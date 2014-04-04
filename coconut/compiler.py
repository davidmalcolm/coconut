#   Copyright 2014 David Malcolm <dmalcolm@redhat.com>
#   Copyright 2014 Red Hat, Inc.
#
#   This is free software: you can redistribute it and/or modify it
#   under the terms of the GNU General Public License as published by
#   the Free Software Foundation, either version 3 of the License, or
#   (at your option) any later version.
#
#   This program is distributed in the hope that it will be useful, but
#   WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#   General Public License for more details.
#
#   You should have received a copy of the GNU General Public License
#   along with this program.  If not, see
#   <http://www.gnu.org/licenses/>.

"""
Compilation of BytecodeCFG to IrCFG

The high-level BytecodeOps are exploded into one or more blocks per
bytecode, along with various other blocks for e.g. exception handling.

Typically even a simple BytecodeCFG typically becomes a fairly complicated
IrCFG.

Stack locations become simple locals, with push/pop activity resolved
now as reads/writes of specific locals (and refcount manipulation).

The "why" local from ceval.c becomes a compile-time variable, affecting
compile-time decisions.
"""

import dis
from io import StringIO
import re
import sys

from coconut.bytecode import BytecodeCFG, BStackEntry, \
    SETUP_LOOP, EXCEPT_HANDLER, SETUP_EXCEPT, SETUP_FINALLY, \
    Py_None
from coconut.ir import IrCFG, IrBlock, Expression, Local, Const, ConstInt, \
    ConstString,  NULL, Call, Local, Global, Assignment, LValue, \
    FieldDereference, ArrayLookup
from coconut.dot import dot_to_png, dot_to_svg
from coconut.optimize import expr_for_python_obj

class UnimplementedBytecode(Exception):
    def __init__(self, op):
        self.op = op
    def __str__(self):
        return '%s' % self.op

def make_safe_varname(text):
    safechars = 'abcdefghijklmnopqrstuvwxyz'
    safechars += safechars.upper()
    safechars += '0123456789_'
    result = ''
    for ch in text:
        if ch in safechars:
            result += ch
        else:
            result += '_'
    return result

# We convert the "enum why_code why" local into a code-generation variable:
WHY_NOT =       0x0001 # No error
WHY_EXCEPTION = 0x0002 # Exception occurred
WHY_RERAISE =   0x0004 # Exception re-raised by 'finally'
WHY_RETURN =    0x0008 # 'return' statement
WHY_BREAK =     0x0010 # 'break' statement
WHY_CONTINUE =  0x0020 # 'continue' statement
WHY_YIELD =     0x0040 # 'yield' operator
WHY_SILENCED =  0x0080 #  Exception silenced by 'with'

# From code.h:
CO_GENERATOR    = 0x0020

class Type:
    pass

class PyObjectPtr(Type):
    pass

class CoConst(Local):
    # a local PyObject* reference to an entry in the co_consts table
    def __init__(self, co_consts, idx):
        self.idx = idx
        self.co_const = co_consts[idx]
        name = make_safe_varname('const%i_%s' % (idx, self.co_const))
        Local.__init__(self, 'PyObject *', name)

class CoName(Local):
    # a local PyObject* reference to an entry in the co_names table
    def __init__(self, co_names, idx):
        self.idx = idx
        self.co_name = co_names[idx]
        name = make_safe_varname('name%i_%s' % (idx, self.co_name))
        Local.__init__(self, 'PyObject *', name)

class Compiler:
    def __init__(self):
        # Config
        self.support_tracing = False
        self.dump_stack_activity = False
        self.verify = True

        self.ircfg = IrCFG()
        self.locals = []
        self.stack = []
        self.f = self.ircfg.add_param('PyFrameObject *', 'f')
        self.throwflag = self.ircfg.add_param('int', 'throwflag')
        # Error status -- nonzero if error:
        self.err = self.ircfg.add_local('int', 'err')
        # Result object -- NULL if error:
        self.x = self.ircfg.add_local('PyObject *', 'x')
        # Temporary objects popped off stack:
        self.v = self.ircfg.add_local('PyObject *', 'v')
        self.w = self.ircfg.add_local('PyObject *', 'w')
        self.u = self.ircfg.add_local('PyObject *', 'u')
        self.t = self.ircfg.add_local('PyObject *', 't')
        self.retval = self.ircfg.add_local('PyObject *', 'retval')
        self.tstate = self.ircfg.add_local('PyThreadState *', 'tstate')
        self.co = self.ircfg.add_local('PyCodeObject *', 'co')
        self.names = self.ircfg.add_local('PyObject *', 'names')
        self.consts = self.ircfg.add_local('PyObject *', 'consts')

        # Some pre-canned expressions:
        self.f_localsplus = FieldDereference(self.f, "f_localsplus")

    def compile(self, co):
        if 0:
            dis.dis(co)

        # generators don't work yet
        if co.co_flags & CO_GENERATOR:
            raise NotImplementedError("Generators aren't yet supported")

        # We have an underlying BytecodeCFG, where the operations are bytecode
        # operations, formed into basic blocks:
        self.bcfg = BytecodeCFG(co)
        bcfg = self.bcfg

        # Now construct a IrCFG, initially with at least one basic-block
        # per bytecode operation, and probably many more.
        for addr in sorted(bcfg.addr_to_op):
            self.ircfg.add_block_at(self.get_bytecode_label(addr))


        self.curcblock = self.ircfg.add_block('entry')

        # fastlocals:
        for i in range(len(co.co_varnames)):
            local = self.ircfg.add_local('PyObject *',
                                        'local%i_%s' % (i, co.co_varnames[i]))
            self.locals.append(local)

        # FIXME: what about args?

        # Have explicit locals for each stack location:
        for i in range(co.co_stacksize):
            self.stack.append(self.ircfg.add_local('PyObject *', 'stack%i' % i))

        # Add some top-level comments summarizing the bytecode:
        s = sys.stdout
        try:
            with StringIO() as sys.stdout:
                dis.dis(co)
                comment = sys.stdout.getvalue()
                self.curcblock.add_comment(comment)
        finally:
            sys.stdout = s
        comment = ''
        for addr in sorted(bcfg.addr_to_block.keys()):
            block = bcfg.addr_to_block[addr]
            for op in block.ops:
                if op.addr in bcfg.linestarts:
                    linenum = bcfg.linestarts[op.addr]
                    comment += ('%s:%d: %s\n'
                                % (co.co_filename, linenum,
                                   bcfg.sourcelines[linenum - 1].rstrip()))
                comment += '%s\n' % op
        self.curcblock.add_comment(comment)

        # In ceval.c, this is initialized at the point of declaration
        # We need to do it ASAP; it gets used almost immediately:
        self.curcblock.add_call(self.tstate, 'PyThreadState_GET', ())

        '''
        self.curcblock.writeln()
        self.curcblock.add_comment('push frame')
        recursive_call, otherwise = \
            self.curcblock.add_conditional(Expression('Py_EnterRecursiveCall("")'),
                                           '!=',
                                           ConstInt(0),
                                           likely=False,
                                           true_label='Py_EnterRecursiveCall_failed',
                                           false_label='Py_EnterRecursiveCall_succeeded')
        recursive_call.add_return(NULL())

        self.curcblock = otherwise
        '''

        # TODO:
        #  if (Py_EnterRecursiveCall(""))
        #    return NULL;

        # tstate->frame = f;
        self.curcblock.add_assignment(
            FieldDereference(self.tstate, 'frame'),
            self.f)

        self.curcblock.writeln()
        self.curcblock.add_comment('Initialize the inlined locals from the PyFrameObject\'s copy')
        for i, local in enumerate(self.locals):
            # "local = f->f_localsplus[%i]"
            self.curcblock.add_assignment(
                local,
                ArrayLookup(self.f_localsplus, ConstInt(i)))
            # FIXME assume the initial arguments are non-NULL, somehow
        self.curcblock.writeln()

        # Code-block tracing hooks
        ''''
        use_tracing, otherwise = \
            self.curcblock.add_conditional(Expression('tstate->use_tracing'),
                                           '!=',
                                           ConstInt(0),
                                           likely=False,
                                           true_label='use_tracing',
                                           false_label='without_use_tracing')
        use_tracing.add_call(None, 'MAYBE_BLOCK_TRACING', () )
        # FIXME: the above can fail in two ways, with "goto exit_eval_frame;"
        use_tracing.add_jump(otherwise.addr)

        self.curcblock = otherwise
        '''

        self.curcblock.writeln()
        self.curcblock.add_assignment(self.retval, NULL())
        self.curcblock.add_assignment(self.co, FieldDereference(self.f, 'f_code'))
        self.curcblock.add_assignment(self.names, FieldDereference(self.co, 'co_names'))
        self.curcblock.add_assignment(self.consts, FieldDereference(self.co, 'co_consts'))

        self.curcblock.add_assignment(self.err, ConstInt(0))
        self.curcblock.add_assignment(self.x, Const('Py_None')) # Not a reference, just anything non-NULL
        self.curcblock.add_assignment(self.w,  NULL())

        '''
        throwblock, nothrowblock = \
            self.curcblock.add_conditional(self.throwflag, '!=', ConstInt(0),
                                           true_label='throwflag_is_set',
                                           false_label='throwflag_is_not_set')

        throwblock.add_comment('support for generator.throw()')
        ctxt = OpcodeContext(self, None, co, [], 0,
                             throwblock,
                             WHY_EXCEPTION)
        ctxt.break_to_on_error() # it's actually a "goto onerror;"

        self.curcblock = nothrowblock
        '''

        # Assume that co_names and co_consts doesn't change.
        # Add optimized lookups for them:
        self.curcblock.writeln()
        self.curcblock.add_comment('Fast access to names/consts:')
        self.fast_names = []
        self.fast_consts = []
        def setup_fast_refs(arr, cls, tuplevar, co_var):
            for i in range(len(co_var)):
                fast = cls(co_var, i)
                arr.append(fast)
                self.ircfg.locals.append(fast)

                expr = expr_for_python_obj(co_var[i])
                if expr:
                    # Avoid looking up the const if it's a singleton,
                    # potentially exposing type-information to later
                    # optimizations:
                    self.curcblock.add_assignment(arr[i], expr)
                else:
                    self.curcblock.add_call(arr[i],
                                            'PyTuple_GET_ITEM',
                                            (tuplevar, ConstInt(i)))
                # FIXME: INCREF/DECREF pairs
        setup_fast_refs(self.fast_names, CoName,
                        self.names, co.co_names)
        setup_fast_refs(self.fast_consts, CoConst,
                        self.consts, co.co_consts)

        self.curcblock.writeln()
        self.curcblock.add_comment('beginning of unrolled bytecode')

        # FIXME: computed jump to (f->f_lasti + 1)
        self.curcblock.add_jump(self.get_bytecode_label(0))

        for addr in sorted(bcfg.addr_to_block.keys()):
            block = bcfg.addr_to_block[addr]
            for op in block.ops:
                self.compile_bytecode(co, bcfg, op)

        if self.verify:
            self.ircfg.verify()

    def get_bytecode_label(self, offset):
        op = self.bcfg.addr_to_op[offset]
        return 'bytecode_offset_%i_%s' % (offset, op.opcodename())

    def compile_bytecode(self, co, bcfg, op):
        self.curcblock = self.ircfg.addr_to_block[self.get_bytecode_label(op.addr)]
        self.curcblock.add_comment(self.get_bytecode_label(op.addr))

        if op.addr in bcfg.linestarts:
            linenum = bcfg.linestarts[op.addr]
            self.curcblock.add_comment('%s:%d: %s'
                                       % (co.co_filename, linenum,
                                          bcfg.sourcelines[linenum - 1].rstrip()))
        self.curcblock.add_comment('offset %i: %s %s'
            % (op.addr, op.opcodename(), op.get_note()))
        self.curcblock.add_comment('values on stack: %s'
                                   % op.vheight)
        self.curcblock.add_comment('bstack: %s' % op.bstack)

        if self.dump_stack_activity:
            if op.vheight:
                # Try to improve readability of generated sources by
                # inserting a dummy function call, documenting in its args
                # the current state of the value stack.
                # Const-propagation etc ought to update this, and we can
                # eventually strip it out (hopefully it won't prevent too
                # many other optimizations)
                self.curcblock.add_call(None,
                                        'STACK_HAS_%i_VALUES' % op.vheight,
                                        tuple(self.stack_at_depth(offset)
                                              for offset in range(op.vheight)))
            # Similarly for locals:
            for local in self.locals:
                self.curcblock.add_call(None,
                                        'LOCAL_%s_HAS_VALUE' % local.name,
                                        (local,) )

        self.curcblock.add_assignment(FieldDereference(self.f,
                                                       'f_lasti'),
                                      ConstInt(op.addr))

        # fast_next_opcode has line-by-line tracing support
        # Since we know which opcodes change the line number, we can
        # trace only at these locations:
        # Note that this doesn't support modifications to
        # f->f_stacktop or f->f_lasti
        if self.support_tracing and op.addr in bcfg.linestarts:
            linenum = bcfg.linestarts[op.addr]
            # FIXME: ceval.c's _Py_TracingPossible needs to be made extern for this
            # to work:
            tracing_possible, no_tracing = \
                self.curcblock.add_conditional(Global('int', '_Py_TracingPossible'),
                                               '!=',
                                               ConstInt(0),
                                               likely=False,
                                               true_label='_Py_TracingPossible_set',
                                               false_label='_Py_TracingPossible_not_set')

            tracing_possible.add_call(self.err, 'MAYBE_TRACE_LINE', (ConstInt(linenum),))
            # (FIXME: implement MAYBE_TRACE_LINE)
            trace_exception, trace_ok = \
                tracing_possible.add_conditional(self.err, '!=', ConstInt(0),
                                                 true_label='MAYBE_TRACE_LINE_raised_exception',
                                                 false_label='MAYBE_TRACE_LINE_succeeded')

            trace_exception.add_comment('trace function raised an exception')
            ctxt = OpcodeContext(self, op, co, op.bstack, op.vheight,
                                 trace_exception,
                                 WHY_NOT)
            ctxt.break_to_on_error() # it's actually a "goto onerror;"

            trace_ok.add_jump(no_tracing.addr)

            self.curcblock = no_tracing
            self.curcblock.add_comment('op.bstack:%r' % op.bstack)

        if hasattr(op, 'ceval'):
            ctxt = OpcodeContext(self, op, co, op.bstack, op.vheight,
                                 self.curcblock,
                                 WHY_NOT)
            op.ceval(ctxt)
        else:
            raise UnimplementedBytecode(op)

    def LOCAL(self, idx):
        return self.locals[idx]

    def stack_at_depth(self, offset):
        if 1:
            return self.stack[offset]
        else:
            # this can be useful for debugging stack depth issues:
            return LValue('stack_at_depth[%i]' % offset)

class OpcodeContext:
    def __init__(self, compiler, opcode, co, bstack, vheight, curcblock, why):
        #assert vheight is not None, (opcode.addr)
        self.compiler = compiler
        self.opcode = opcode
        self.co = co
        if bstack:
            self.bstack = bstack[:]
        else:
            self.bstack = []
        self.vheight = vheight
        self.curcblock = curcblock
        self.why = why

    def writeln(self, line=None):
        self.curcblock.add_comment('writeln: %s' % line) # FIXME: remove this eventually

    def add_comment(self, text):
        self.curcblock.add_comment(text)

    def add_local(self, type_, name, init=None):
        return self.curcblock.add_local(type_, name, init)

    def assign(self, lhs, rhs):
        self.curcblock.add_assignment(lhs, rhs)

    def Py_INCREF(self, arg):
        self.curcblock.add_call(None, 'Py_INCREF', (arg,))

    def Py_DECREF(self, arg):
        self.curcblock.add_call(None, 'Py_DECREF', (arg,))

    def Py_XDECREF(self, arg):
        self.curcblock.add_call(None, 'Py_XDECREF', (arg,))

    def add_stack_comment(self, op, oldvheight, newvheight):
        if 1:
            self.add_comment('  %s; stack depth was %i now %i'
                             % (op, oldvheight, newvheight))


    def INSTR_OFFSET(self):
        return self.opcode.get_next_addr()

    def PUSH(self, arg):
        self.add_stack_comment('PUSH()', self.vheight, self.vheight + 1)
        self.vheight += 1
        self.assign(self.TOP(),
                    arg)

    def POP(self, lhs=None):
        top = self.TOP()
        if lhs:
            self.assign(lhs, top)
        self.add_stack_comment('POP()', self.vheight, self.vheight - 1)
        self.vheight -= 1
        return top

    def STACK_LEVEL(self):
        return self.vheight

    def EMPTY(self):
        return self.STACK_LEVEL() == 0

    def TOP(self):
        return self.STACK_OFFSET(-1)

    def SECOND(self):
        return self.STACK_OFFSET(-2)

    def THIRD(self):
        return self.STACK_OFFSET(-3)

    def STACK_OFFSET(self, offset):
        return self.compiler.stack_at_depth(self.vheight + offset)

    def SET_TOP(self, value):
        self.assign(self.TOP(), value)

    def SET_SECOND(self, value):
        self.assign(self.STACK_OFFSET(-2), value)

    def SET_THIRD(self, value):
        self.assign(self.STACK_OFFSET(-3), value)

    def STACKADJ(self, offset):
        self.add_stack_comment('STACKADJ(%i)' % offset,
                               self.vheight, self.vheight + offset)
        self.vheight += offset

    def JUMPTO(self, arg):
        self.add_comment('JUMPTO')
        self.curcblock.add_jump(self.compiler.get_bytecode_label(arg))

    def JUMPBY(self, arg):
        self.add_comment('JUMPBY')
        self.curcblock.add_jump(self.compiler.get_bytecode_label(self.opcode.get_next_addr() + arg))

    def block_setup(self, op, type_, handler, level):
        self.add_comment('block_setup: %s %s %s %s' % (op, type_, handler, level))
        self.bstack.append(BStackEntry(op))

    def add_jump(self, ctxt):
        self.curcblock.add_jump(ctxt.curcblock.addr)

    def add_conditional(self, lhs, expr, rhs, likely=None,
                        true_label='true',
                        false_label='false'):
        if self.opcode:
            prefix = self.compiler.get_bytecode_label(self.opcode.addr)
            true_label='%s_%s' % (prefix, true_label)
            false_label='%s_%s' % (prefix, false_label)
        true_block, false_block = \
            self.curcblock.add_conditional(lhs, expr, rhs, likely,
                                           true_label=true_label,
                                           false_label=false_label)
        # FIXME: need to wire up true_block and false_block
        return (OpcodeContext(self.compiler, self.opcode, self.co,
                              self.bstack, self.vheight,
                              true_block, self.why),
                OpcodeContext(self.compiler, self.opcode, self.co,
                              self.bstack, self.vheight,
                              false_block, self.why))

    def add_call(self, lhs, fnname, args):
        self.curcblock.add_call(lhs, fnname, args)

    def add_GETITEM(self, lhs, tuplename, idx):
        # From ceval.c's:
        #ifndef Py_DEBUG
        #define GETITEM(v, i) PyTuple_GET_ITEM((PyTupleObject *)(v), (i))
        #else
        #define GETITEM(v, i) PyTuple_GetItem((v), (i))
        #endif
        assert isinstance(tuplename, str)
        assert isinstance(idx, int)

        # Use the prelooked-up locals for this, so that we can resolve
        # directly to a specific local, to help future optimization:
        arr = getattr(self.compiler, 'fast_%s' % tuplename)
        rhs = arr[idx]
        self.curcblock.add_assignment(lhs, rhs)

    def add_return(self, expr):
        self.curcblock.add_return(expr)

    def add_block(self, name='anon'):
        return OpcodeContext(self.compiler, self.opcode, self.co,
                             self.bstack, self.vheight,
                             self.compiler.ircfg.add_block(name),
                             self.why)
    def pop_block(self):
        b = self.bstack.pop()
        return b

    def DISPATCH(self):
        self.FAST_DISPATCH() # FIXME: allow Ctrl-C ?

    def FAST_DISPATCH(self):
        self.curcblock.add_jump(
            self.compiler.get_bytecode_label(self.opcode.get_next_addr()))

    def UNWIND_BLOCK(self, b):
        # while (STACK_LEVEL() > (b)->b_level) { \
        #     PyObject *v = POP(); \
        #     Py_XDECREF(v); \
        # }
        self.add_comment('UNWIND_BLOCK()')
        while self.STACK_LEVEL() > b.get_vstack_height():
            v = self.add_local('PyObject *', 'v')
            v = self.POP()
            self.Py_XDECREF(v)

    def set_why(self, value):
        assert isinstance(value, str)
        self.why = eval(value)
        self.add_comment('WHY = %s' % value)

    def break_to_on_error(self):
        self.add_comment('unrolled instance of on_error')
        ctxt = self
        if ctxt.why == WHY_NOT:
            # if (err == 0 && x != NULL) {
            true_ctxt, false_ctxt = \
                ctxt.add_conditional(self.compiler.err, '==', ConstInt(0),
                                     true_label='zero_err',
                                     false_label='non_zero_err')
            true_ctxt2, false_ctxt2 = \
                true_ctxt.add_conditional(self.compiler.x, '!=', NULL(),
                                          true_label='non_null_x',
                                          false_label='null_x')
            # (We leave out the #ifdef CHECKEXC stuff)
            true_ctxt2.add_comment('Normal, fast path')
            true_ctxt2.DISPATCH()
            false_ctxt.add_jump(false_ctxt2)
            false_ctxt2.set_why('WHY_EXCEPTION')
            false_ctxt2.assign(self.compiler.x, Py_None)
            false_ctxt2.assign(self.compiler.err, ConstInt(0))
            ctxt = false_ctxt2

        if ctxt.why == WHY_EXCEPTION or ctxt.why == WHY_RERAISE:
            ctxt.add_comment('Double-check exception status')
            true_ctxt, false_ctxt = \
                ctxt.add_conditional(Call('PyErr_Occurred', ()), '==', ConstInt(0),
                                     true_label='PyErr_Occurred_false',
                                     false_label='PyErr_Occurred_true')
            true_ctxt.add_call(
                None, 'PyErr_SetString',
                (Global('PyObject *', 'PyExc_SystemError'),
                 ConstString("error return without exception set")))
            true_ctxt.set_why('WHY_EXCEPTION')
            true_ctxt.add_jump(false_ctxt)
            ctxt = false_ctxt

        if ctxt.why == WHY_EXCEPTION:
            ctxt.add_comment('Log traceback info if this is a real exception')
            ctxt.add_call(None, 'PyTraceBack_Here', (self.compiler.f, ))
            ctxt.writeln('if (tstate->c_tracefunc != NULL)')
            ctxt.writeln('    call_exc_trace(tstate->c_tracefunc,')
            ctxt.writeln('                   tstate->c_traceobj, f);')
            ctxt.writeln('}')

        if ctxt.why== WHY_RERAISE:
            ctxt.add_comment('For the rest, treat WHY_RERAISE as WHY_EXCEPTION')
            ctxt.set_why('WHY_EXCEPTION')

        ctxt.add_comment('Unwind stacks if a (pseudo) exception occurred')
        ctxt.goto_fast_block_end()

    def SETLOCAL(self, i, value):
        self.add_comment('SETLOCAL(%i)' % i)
        tmp = self.add_local('PyObject *', 'tmp', self.LOCAL(i))
        self.assign(self.LOCAL(i), value)
        self.Py_XDECREF(tmp)

        # Also write the value back into fastlocals within the frame
        # (with the same refcounting handling):
        f_localsplus_item = ArrayLookup(self.compiler.f_localsplus,
                                        ConstInt(i))
        self.assign(tmp, f_localsplus_item)
        self.assign(f_localsplus_item, value)
        self.Py_INCREF(value)
        self.Py_XDECREF(tmp)

    def GETLOCAL(self, i):
        return self.LOCAL(i)

    def LOCAL(self, i):
        return self.compiler.LOCAL(i)

    def store_stack(self):
        # for use by YIELD_FROM and YIELD_VALUE
        self.assign(FieldDereference(self.compiler.f, 'f_stack_top'),
                    ArrayLookup(FieldDereference(self.compiler.f, 'f_valuestack'),
                                ConstInt(self.vheight)))
        for i in range(self.vheight):
            self.assign(LValue('f->f_valuestack[%i]' % i),
                        self.compiler.stack_at_depth(i))
            self.Py_INCREF(self.compiler.stack_at_depth(i))
            # FIXME: should we also DECREF whatever's already there?

    def goto_fast_block_end(self):
        self.add_comment('unrolled instance of fast_block_end')
        # FIXME: the JUMPTOs here don't work: we need to update nexti instead
        # and only do the jump on DISPATCH
        while self.why != WHY_NOT and self.bstack:
            self.add_comment('Peek at the current block.')
            tryblock = self.bstack[-1]
            self.add_comment('  current PyTryBlock: %s' % tryblock)
            self.add_comment('  current PyTryBlock: %s' % type(tryblock))
            assert self.why != WHY_YIELD
            if isinstance(tryblock.op, SETUP_LOOP) and self.why == WHY_CONTINUE:
                self.set_why(WHY_NOT)
                self.JUMPTO(PyLong_AS_LONG(retval)) # FIXME!
                self.Py_DECREF(retval)
                break # should this halt code generation instead?
            self.add_comment('Now we have to pop the block.')
            b = self.bstack.pop()
            if isinstance(tryblock.op, EXCEPT_HANDLER):
                self.writeln('                UNWIND_EXCEPT_HANDLER(b);') # FIXME
                continue
            self.UNWIND_BLOCK(tryblock)
            if isinstance(tryblock.op, SETUP_LOOP) and self.why == WHY_BREAK:
                self.set_why('WHY_NOT')
                self.JUMPTO(tryblock.get_b_handler())
                # we would break out of the block unwind loop here, but we
                # don't need to do any further work beyond the jump, so simply
                # return to avoid generating a bogus jump in the DISPATCH below
                return
            if self.why == WHY_EXCEPTION and isinstance(tryblock.op, (SETUP_EXCEPT, SETUP_FINALLY)):
                exc = self.add_local('PyObject *', 'exc')
                val = self.add_local('PyObject *', 'val')
                tb = self.add_local('PyObject *', 'tb')
                handler = tryblock.b_handler
                self.add_comment('Beware, this invalidates all b->b_* fields')
                self.block_setup(ExceptHandler(), -1, self.STACK_LEVEL())
                self.PUSH(Expression('tstate->exc_traceback'))
                self.PUSH(Expression('tstate->exc_value'))
                self.writeln('                if (tstate->exc_type != NULL) {')
                self.writeln('                    PUSH(tstate->exc_type);')
                self.writeln('                }')
                self.writeln('                else {')
                self.writeln('                    Py_INCREF(Py_None);')
                self.writeln('                    PUSH(Py_None);')
                self.writeln('                }')
                self.writeln('                PyErr_Fetch(&exc, &val, &tb);')
                self.add_comment('Make the raw exception data')
                self.add_comment('available to the handler,')
                self.add_comment('so a program can emulate the')
                self.add_comment('Python main loop.')
                self.writeln('                PyErr_NormalizeException(')
                self.writeln('                    &exc, &val, &tb);')
                self.writeln('                PyException_SetTraceback(val, tb);')
                self.writeln('                Py_INCREF(exc);')
                self.writeln('                tstate->exc_type = exc;')
                self.writeln('                Py_INCREF(val);')
                self.writeln('                tstate->exc_value = val;')
                self.writeln('                tstate->exc_traceback = tb;')
                self.writeln('                if (tb == NULL)')
                self.writeln('                    tb = Py_None;')
                self.writeln('                Py_INCREF(tb);')
                self.writeln('                PUSH(tb);')
                self.writeln('                PUSH(val);')
                self.writeln('                PUSH(exc);')
                self.set_why('WHY_NOT')
                self.JUMP_TO(handler)
                break

            if isinstance(tryblock, SETUP_FINALLY):
                if self.why & (WHY_RETURN | WHY_CONTINUE):
                    self.PUSH(retval)
                self.writeln('                PUSH(PyLong_FromLong((long)why));')
                self.set_why('WHY_NOT')
                self.JUMPTO(b.b_handler) # FIXME
                break # should this halt code generation instead?

        self.add_comment('done unwinding stack')

        self.add_comment('End the loop if we still have an error (or return)')
        self.writeln()
        if self.why != WHY_NOT:
            self.end_of_main_loop()
        else:
            self.DISPATCH()

    def end_of_main_loop(self):
        self.add_comment('end of main loop')
        assert self.why != WHY_YIELD
        self.add_comment('Pop remaining stack entries')
        while not self.EMPTY():
            self.POP(self.compiler.v)
            self.Py_XDECREF(self.compiler.v)

        if self.why != WHY_RETURN:
            self.assign(self.compiler.retval, NULL())

        self.fast_yield()

    def fast_yield(self):
        '''
        if self.co.co_flags & CO_GENERATOR and (self.why == WHY_YIELD or self.why == WHY_RETURN):
            # FIXME:
            self.add_comment('The purpose of this block is to put aside the generator\'s exception')
            self.add_comment('state and restore that of the calling frame. If the current')
            self.add_comment('exception state is from the caller, we clear the exception values')
            self.add_comment('on the generator frame, so they are not swapped back in latter. The')
            self.add_comment('origin of the current exception state is determined by checking for')
            self.add_comment('except handler blocks, which we must be in iff a new exception')
            self.add_comment('state came into existence in this frame. (An uncaught exception')
            self.add_comment('would have why == WHY_EXCEPTION, and we wouldn\'t be here).')
            self.writeln('int i;')
            self.writeln('for (i = 0; i < f->f_iblock; i++)')
            self.writeln('    if (f->f_blockstack[i].b_type == EXCEPT_HANDLER)')
            self.writeln('        break;')
            self.writeln('if (i == f->f_iblock)')
            self.writeln('    /* We did not create this exception. */')
            self.writeln('    restore_and_clear_exc_state(tstate, f);')
            self.writeln('else')
            self.writeln('    swap_exc_state(tstate, f);')

        ctxt = self
        use_tracing_ctxt, after_tracing_ctxt = \
            ctxt.add_conditional(Expression('tstate->use_tracing'), '!=', ConstInt(0), likely=False,
                                 true_label='use_tracing',
                                 false_label='without_use_tracing')
        has_c_tracefunc_ctxt, false_ctxt2 = \
            use_tracing_ctxt.add_conditional(Expression('tstate->c_tracefunc'), '!=', ConstInt(0),
                                             true_label='has_c_tracefunc',
                                             false_label='no_c_tracefunc')
        if ctxt.why == WHY_RETURN or ctxt.why == WHY_YIELD:
            has_c_tracefunc_ctxt.writeln('                if (call_trace(tstate->c_tracefunc,')
            has_c_tracefunc_ctxt.writeln('                               tstate->c_traceobj, f,')
            has_c_tracefunc_ctxt.writeln('                               PyTrace_RETURN, retval)) {')
            has_c_tracefunc_ctxt.writeln('                    Py_XDECREF(retval);')
            has_c_tracefunc_ctxt.writeln('                    retval = NULL;')
            has_c_tracefunc_ctxt.why = WHY_EXCEPTION # beware!
            has_c_tracefunc_ctxt.writeln('                }')
        elif ctxt.why == WHY_EXCEPTION:
            has_c_tracefunc_ctxt.add_call(None, 'call_trace_protected',
                                          (Expression('tstate->c_tracefunc'),
                                           Expression('tstate->c_traceobj'),
                                           Expression('f'),
                                           Expression('PyTrace_RETURN'),
                                           NULL()))
        has_c_tracefunc_ctxt.add_jump(false_ctxt2)
        false_ctxt2.why = has_c_tracefunc_ctxt.why # see "beware!" above

        has_c_profilefunc_ctxt, false_ctxt3 = \
            false_ctxt2.add_conditional(Expression('tstate->c_profilefunc'), '!=', ConstInt(0),
                                        true_label='has_c_profilefunc',
                                        false_label='no_c_profilefunc')
        if has_c_profilefunc_ctxt.why == WHY_EXCEPTION:
            has_c_profilefunc_ctxt.add_call(None, 'call_trace_protected',
                                            (Expression('tstate->c_profilefunc'),
                                             Expression('tstate->c_profileobj'),
                                             Expression('f'),
                                             Expression('PyTrace_RETURN'),
                                             NULL()))
        else:
            has_c_profilefunc_ctxt.writeln('            if (call_trace(tstate->c_profilefunc,')
            has_c_profilefunc_ctxt.writeln('                                tstate->c_profileobj, f,')
            has_c_profilefunc_ctxt.writeln('                                PyTrace_RETURN, retval)) {')
            has_c_profilefunc_ctxt.writeln('                Py_XDECREF(retval);')
            has_c_profilefunc_ctxt.writeln('                retval = NULL;')
            has_c_profilefunc_ctxt.set_why('WHY_EXCEPTION')
        has_c_profilefunc_ctxt.add_jump(after_tracing_ctxt)
        false_ctxt3.add_jump(after_tracing_ctxt)

        after_tracing_ctxt.add_comment('pop frame')
        after_tracing_ctxt.exit_eval_frame()
        '''
        self.exit_eval_frame()

    def exit_eval_frame(self):
        self.writeln('exit_eval_frame:')
        #self.add_call(None, 'Py_LeaveRecursiveCall', ())
        #self.assign(LValue('tstate->frame'), Expression('f->f_back'))
        self.add_return(self.compiler.retval)