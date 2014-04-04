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

from collections import namedtuple
import dis
import opcode
from pprint import pprint

from coconut.cfg import CFG, Block, Edge, Op
from coconut.dot import to_html, _dot_column
from coconut.ir import \
    NULL, Expression, ConstInt, ConstString, Global, \
    Call, FieldDereference, UnaryExpr, EnumValue

# Globals
Py_None = Global('PyObject *', 'Py_None')
PyExc_ValueError = Global('PyObject *', 'PyExc_ValueError')

# Constants
# From object.h: Rich comparison opcodes:
Py_LT = 0
Py_LE = 1
Py_EQ = 2
Py_NE = 3
Py_GT = 4
Py_GE = 5

# From opcode.h's enum cmp_op:
PyCmp_LT=Py_LT
PyCmp_LE=Py_LE
PyCmp_EQ=Py_EQ
PyCmp_NE=Py_NE
PyCmp_GT=Py_GT
PyCmp_GE=Py_GE
PyCmp_IN, PyCmp_NOT_IN, PyCmp_IS, PyCmp_IS_NOT, \
    PyCmp_EXC_MATCH, PyCmp_BAD = range(PyCmp_GE + 1,
                                       PyCmp_GE + 6 + 1)

enum_cmp_op = {
    PyCmp_LT : "PyCmp_LT",
    PyCmp_LE : "PyCmp_LE",
    PyCmp_EQ : "PyCmp_EQ",
    PyCmp_NE : "PyCmp_NE",
    PyCmp_GT : "PyCmp_GT",
    PyCmp_GE : "PyCmp_GE",
    PyCmp_IN : "PyCmp_IN",
    PyCmp_NOT_IN : "PyCmp_NOT_IN",
    PyCmp_IS : "PyCmp_IS",
    PyCmp_IS_NOT : "PyCmp_IS_NOT",
    PyCmp_EXC_MATCH : "PyCmp_EXC_MATCH",
    PyCmp_BAD : "PyCmp_BAD",
}

NAME_ERROR_MSG = "name '%.200s' is not defined"
GLOBAL_NAME_ERROR_MSG = "global name '%.200s' is not defined"
UNBOUNDLOCAL_ERROR_MSG = "local variable '%.200s' referenced before assignment"
UNBOUNDFREE_ERROR_MSG = ("free variable '%.200s' referenced before assignment"
                         " in enclosing scope")

class NotEvaluatable(Exception):
    pass

def eval_cmp_op(lhs, rhs, op):
    if op == "PyCmp_LT":
        return lhs < rhs
    elif op == "PyCmp_LE":
        return lhs <= rhs
    elif op == "PyCmp_EQ":
        return lhs == rhs
    elif op == "PyCmp_LE":
        return lhs <= rhs
    elif op == "PyCmp_NE":
        return lhs != rhs
    elif op == "PyCmp_GT":
        return lhs > rhs
    elif op == "PyCmp_GE":
        return lhs >= rhs
    elif op == "PyCmp_IN":
        return lhs in rhs
    elif op == "PyCmp_NOT_IN":
        return lhs not in rhs
    else:
        raise NotEvaluatable()

# Base classes:

#
# Classes relating to bytecode analysis
#

class BytecodeCFG(CFG):
    '''Control Flow Graph, from analysis of a CPython bytecode function'''
    #__slots__ = ('co',   # the Python code object (a PyCodeObject, f.__code__)
    #             'sourcelines', # list of strings: the source code
    #             )
    def __init__(self, co):
        CFG.__init__(self)
        self.co = co
        with open(co.co_filename, 'r') as source:
            self.sourcelines = source.readlines()
        self.bytecode = co.co_code # bytes
        self.linestarts = dict(dis.findlinestarts(co))

        # Locate the basic blocks used by jump targets:
        self.labels = dis.findlabels(self.bytecode)
        for idx in self.labels:
            self.add_block_at(idx)
        if 0 not in self.labels:
            self.add_block_at(0)

        self.addr_to_op = {} # from addr to BytecodeOp

        # Carve up bytecode into the underlying operations:
        n = len(self.bytecode)
        i = 0
        while i < n:
            opstart = i

            #if opstart in self.addr_to_block:
            #    curblock = self.addr_to_block[opstart]

            # Carve out one BytecodeOp:
            oplen = 1
            opcode = self.bytecode[i]
            i = i+1
            if opcode == dis.EXTENDED_ARG:
                oplen += 2
                i += 2
                opcode = self.bytecode[i]
            if opcode >= dis.HAVE_ARGUMENT:
                oplen += 2
                i += 2
            opbytes = self.bytecode[i-oplen:i]

            op = BytecodeOp.make(self, opstart, opbytes)
            self.addr_to_op[opstart] = op

            # print(op)

        # Locate the branching operations: each basic block should have only
        # one exit-point, so we may need to introduce additional basic blocks:
        for opstart in self.addr_to_op:
            op = self.addr_to_op[opstart]
            effects = op.get_effects()
            if len(effects) > 1:
                # end of basic block:
                for effect in effects:
                    self._ensure_starts_basic_block(effect.nextaddr)

            # Ensure that "dangling" instructions (e.g. JUMP_ABSOLUTE) have
            # their bytecode carved out into separate blocks:
            if op.is_jump():
                self._ensure_starts_basic_block(op.get_next_addr())

        # Associate operations and basic blocks:
        curblock = None
        for opstart in sorted(self.addr_to_op):
            op = self.addr_to_op[opstart]
            if opstart in self.addr_to_block:
                curblock = self.addr_to_block[opstart]
            assert curblock is not None
            op.block = curblock
            curblock.ops.append(op)

        # print(sorted(self.addr_to_block.keys()))

        # Calculate all of the edges:
        for blockstart in self.addr_to_block:
            # print(blockstart)
            block = self.addr_to_block[blockstart]
            # print(block)
            lastop = block.ops[-1]
            # print('lastop: %s' % lastop)
            for effect in lastop.get_effects():
                e = BytecodeEdge(block,
                                 self.addr_to_block[effect.nextaddr],
                                 effect)
                # print(e)
                self.add_edge(e)

        # Calculate the stack depths:
        self.addr_to_block[0]._recursive_calc_stack_heights([], 0)

        # Debug print:
        if 0:
            for blockstart in sorted(self.addr_to_block):
                print(blockstart)
                block = self.addr_to_block[blockstart]
                print(block)
                for op in block.ops:
                    print(op)

    def _ensure_starts_basic_block(self, addr):
        if addr not in self.addr_to_block:
            self.add_block_at(addr)

    def make_block(self, addr):
        return BytecodeBlock(self, addr)

count = 0

class BStackEntry:
    # Support for "PyFrame_Block*"
    def __init__(self, op):
        self.op = op

    def __str__(self):
        return '%s at %s (to %s)' % (self.op.opcodename(),
                                     self.op.addr,
                                     self.get_b_handler())

    def __repr__(self):
        return 'BStackEntry(op=%r)' % self.op.addr

    def get_vstack_height(self):
        return self.op.vheight

    def get_b_handler(self):
        return self.op.get_next_addr() + self.op.arg

class BytecodeEdge(Edge):
    pass

class BytecodeBlock(Block):
    __slots__ = ('bstack', # state of block stack on entry
                 'vheight', # height of value stack on entry
                 )

    def __init__(self, cfg, addr):
        Block.__init__(self, cfg, addr)
        self.bstack = None
        self.vheight = None

    def __str__(self):
        return ('BytecodeBlock(addr=%i, bstack=%r, vheight=%r)'
                % (self.addr, self.bstack, self.vheight))

    def _recursive_calc_stack_heights(self, bstack, vheight):
        # print('_recursive_calc_stack_heights: %s (%s, %s)' % (self, bstack, vheight))
        if self.bstack is not None:
            # Ensure that all predecessor nodes have the same exit depths (or are
            # unknown):

            if (bstack != self.bstack):
                print("WARNING: %s != %s"
                      % (bstack, self.bstack))
            if (vheight != self.vheight):
                print("WARNING: %s != %s"
                      % (vheight, self.vheight))
            return

        self.bstack = bstack
        self.vheight = vheight
        for op in self.ops:
            op.bstack = bstack
            op.vheight = vheight
            # Calc effect of this op on stack (for next op):
            effects = op.get_effects()
            if len(effects) == 1:
                bstack, vheight = effects[0].calc_result(bstack, vheight)

        # Recursively visit successors:
        for e in self.succ_edges:
            succ = e.dst
            if 0:
                print('  successor of %s: %s' %(self, succ))

            ebstack, evheight = e.effect.calc_result(self.ops[-1].bstack,
                                                     self.ops[-1].vheight)
            succ._recursive_calc_stack_heights(ebstack,
                                               evheight)

    def to_dot_label(self):
        result = '<table border="0" cellspacing="0">\n'
        result += '<tr>'
        result += _dot_column('Block stack: starts at %s' % self.bstack,
                              colspan=8)
        result += '</tr>\n'
        result += '<tr>'
        result += _dot_column('Value stack: starts at %s' % self.vheight,
                              colspan=8)
        result += '</tr>\n'

        result += '<tr>'
        result += _dot_column('Line')
        result += _dot_column('Addr')
        result += _dot_column('Bytes')
        result += _dot_column('Operation')
        result += _dot_column('Argument', colspan=2)
        result += _dot_column('Block Stack')
        result += _dot_column('V-Height')
        result += '</tr>\n'
        for op in self.ops:
            if op.addr in self.cfg.linestarts:
                linenum = self.cfg.linestarts[op.addr]
                src = self.cfg.sourcelines[linenum - 1]
                result += '<tr>'
                result += _dot_column(linenum)
                result += _dot_column(src,
                                      colspan=5)
                result += '</tr>\n'
                #result += self.cfg.sourcelines[linenum - 1] + '\n'

            result += '<tr>'
            result += _dot_column('')
            result += '<td port="addr%i">%s</td>' % (op.addr, op.addr)
            result += _dot_column(' '.join(['0x%02x' % b for b in op.opbytes]))
            result += _dot_column(dis.opname[op.opcode])
            if op.arg is not None:
                result += _dot_column(op.arg)
            else:
                result += _dot_column('')
            result += _dot_column(op.get_note())
            result += _dot_column(','.join([str(bse) for bse in op.bstack]) if op.bstack else '')

            if op.vheight is not None:
                new_vheights = [op.vheight + effect.vstackdelta for effect in op.get_effects()]
            else:
                new_vheights = None

            result += _dot_column('%s -> %s' % (op.vheight, new_vheights))

            result += '</tr>\n'
        result += '</table>\n'
        return result


class BytecodeEffect(namedtuple('BytecodeEffect',
                                ('bstackdelta', 'vstackdelta', 'nextaddr', 'label'))):
    '''
    An operation can have one of more effects on the stack (e.g. POP_JUMP_IF_FALSE)
    bstackdelta: a BStackEntry (gain), -1 (loss), or 0 (unaffected)
    vstackdelta : gain (or loss) of stack depth via this action
    nextaddr : the addr of the next operation to be executed
    label: debug label to help identify what happened
    '''

    def calc_result(self, bstack, vheight):
        # Calculate effect on bstack and bheight

        #print('calc_result: %s %s\n(%s, %s)'
        #      % (self.bstackdelta, self.vstackdelta,
        #         bstack, vheight))

        if isinstance(self.bstackdelta, BStackEntry):
            # block push:
            bstack = bstack[:]
            bstack.append(self.bstackdelta)
        elif self.bstackdelta == -1:
            # block pop:
            vheight = bstack[-1].get_vstack_height()
            bstack = bstack[0:-1]
        else:
            # value push/pop:
            bstack = bstack[:]
            vheight += self.vstackdelta

        #print('-> (%s, %s)'
        #      % (bstack, vheight))

        return bstack, vheight

class UnknownOpcode(ValueError):
    pass

class BytecodeOp(Op):
    __slots__ = ('addr',    # "address" of start of bytecode (index within co_code)
                 'opbytes', # the underlying bytes
                 'opcode',  # the opcode
                 'arg',     # the const argument (expanding any extended args)
                 'bstack',  # state of block stack at start
                 'vheight', # height of value stack at start
                 )

    @classmethod
    def make(cls, cfg, addr, opbytes):
        """
        Construct a BytecodeOp of the appropriate subclass
        """
        if opbytes[0] == dis.EXTENDED_ARG:
            opcode = opbytes[3]
        else:
            opcode = opbytes[0]
        opcodename = dis.opname[opcode]
        subclass = globals()[opcodename]
        return subclass(cfg, addr, opbytes)

    def __init__(self, cfg, addr, opbytes):
        super().__init__(cfg, None) # for now
        self.addr = addr
        self.opbytes = opbytes

        if self.opbytes[0] == dis.EXTENDED_ARG:
            self.opcode = self.opbytes[3]
            extarg = (self.opbytes[1] + self.opbytes[2]*256) * 65536
            self.arg = self.opbytes[4] + self.opbytes[5]*256 + extarg
        else:
            self.opcode = self.opbytes[0]
            if self.opcode >= dis.HAVE_ARGUMENT:
                self.arg = self.opbytes[1] + self.opbytes[2]*256
            else:
                self.arg = None

        self.bstack = None
        self.vheight = None

    def opcodename(self):
        return dis.opname[self.opcode]

    def get_next_addr(self):
        return self.addr + len(self.opbytes)

    def is_jump(self):
        return self.opcode in opcode.hasjrel or self.opcode in opcode.hasjabs

    def _nextop(self, delta, label=''):
        return BytecodeEffect(bstackdelta=0,
                              vstackdelta=delta,
                              nextaddr=self.get_next_addr(),
                              label=label)

    def _get_exception_effect(self, delta):
        return BytecodeEffect(bstackdelta=-1, # FIXME
                              vstackdelta=delta,
                              nextaddr=0, # FIXME
                              label='exception')

    def _nextop_or_exc(self, delta):
        return [BytecodeEffect(bstackdelta=0,
                               vstackdelta=delta,
                               nextaddr=self.get_next_addr(),
                               label=''),
                # FIXME: also handle exceptions
                #self._get_exception_effect(delta)
                ]

    def _get_CALL_args_effects(self, extrapops=0):
        num_positional = self.arg & 0xff
        num_keyword = self.arg >> 8

        # popped function and pushed result cancel each other
        delta = -((num_keyword * 2) + num_positional + extrapops)
        return [BytecodeEffect(bstackdelta=0,
                               vstackdelta=delta,
                               nextaddr=self.get_next_addr(),
                               label=''),
                # FIXME: also handle exceptions
                #self._get_exception_effect(delta)
                ]


    def get_effects(self):
        #class BytecodeEffect(namedtuple('BytecodeEffect', ('vstackdelta', 'nextaddr', 'label'))):

        # FIXME: aim here is to track the possible stack effects of each opcode, and deal with the way
        # that it can vary depending on which branch we take
        # (Hope to be able to mark all of edges with meaningful debug naems also)

        opcodename = self.opcodename()
        if opcodename == 'STOP_CODE':
            return []
        elif opcodename == 'NOP':
            return [self._nextop(0)]
        elif opcodename == 'POP_TOP':
            return [self._nextop(-1)]
        elif opcodename == 'ROT_TWO':
            return [self._nextop(0)]
        elif opcodename == 'ROT_THREE':
            return [self._nextop(0)]
        elif opcodename == 'DUP_TOP':
            return [self._nextop(1)]
        elif opcodename == 'DUP_TOP_TWO':
            return [self._nextop(2)]
        elif opcodename.startswith('UNARY_') or opcodename == 'GET_ITER':
            return self._nextop_or_exc(0)
        elif opcodename.startswith('BINARY_'):
            return self._nextop_or_exc(-1)
        elif opcodename.startswith('INPLACE_'):
            return self._nextop_or_exc(-1)
        elif opcodename == 'STORE_SUBSCR':
            return self._nextop_or_exc(-3)
        elif opcodename == 'DELETE_SUBSCR':
            return self._nextop_or_exc(-2)
        elif opcodename == 'PRINT_EXPR':
            return self._nextop_or_exc(-1)
        elif opcodename == 'BREAK_LOOP':
            return [self._nextop(0, label='break')]
        elif opcodename == 'CONTINUE_LOOP':
            return [self._absjump(label='continue')]
        elif opcodename in {'SET_ADD', 'LIST_APPEND', 'MAP_ADD'}:
            return self._nextop_or_exc(-1)
        elif opcodename == 'RETURN_VALUE':
            return [] # FIXME
        elif opcodename == 'YIELD_VALUE':
            return [] # FIXME
        elif opcodename == 'IMPORT_STAR':
            return self._nextop_or_exc(-1)
        elif opcodename == 'POP_BLOCK':
            return [BytecodeEffect(bstackdelta=-1,
                                   vstackdelta=0,
                                   nextaddr=self.get_next_addr(),
                                   label='')]
        elif opcodename == 'POP_EXCEPT':
            return [self._nextop(0)] # FIXME
        elif opcodename == 'END_FINALLY':
            return [self._nextop(0)] # FIXME
        elif opcodename == 'LOAD_BUILD_CLASS':
            return self._nextop_or_exc(1)
        elif opcodename == 'SETUP_WITH':
            return [self._nextop(0)] # FIXME
        elif opcodename == 'WITH_CLEANUP':
            return [self._nextop(0)] # FIXME
        elif opcodename == 'STORE_LOCALS':
            return [self._nextop(1)] # FIXME

        # HAVE_ARGUMENTS:
        elif opcodename == 'STORE_NAME':
            return [self._nextop(1)]
        elif opcodename == 'DELETE_NAME':
            return self._nextop_or_exc(0)
        elif opcodename == 'UNPACK_SEQUENCE':
            return self._nextop_or_exc(self.arg-1)
        #elif opcodename == 'UNPACK_EX':
        elif opcodename == 'STORE_ATTR':
            return self._nextop_or_exc(-2)
        elif opcodename == 'DELETE_ATTR':
            return self._nextop_or_exc(-1)
        elif opcodename == 'STORE_GLOBAL':
            return self._nextop_or_exc(-1)
        elif opcodename == 'DELETE_GLOBAL':
            return self._nextop_or_exc(0)
        elif opcodename == 'LOAD_CONST':
            return [self._nextop(1)]
        elif opcodename == 'LOAD_NAME':
            return self._nextop_or_exc(1)
        elif opcodename in {'BUILD_TUPLE', 'BUILD_LIST', 'BUILD_SET'}:
            return self._nextop_or_exc(1-self.arg)
        elif opcodename == 'BUILD_MAP':
            return self._nextop_or_exc(1)
        elif opcodename == 'LOAD_ATTR':
            return self._nextop_or_exc(0)
        elif opcodename == 'COMPARE_OP':
            return self._nextop_or_exc(-1)
        elif opcodename == 'IMPORT_NAME':
            return self._nextop_or_exc(-1)
        elif opcodename == 'IMPORT_FROM':
            return self._nextop_or_exc(1)

        elif opcodename == 'JUMP_FORWARD':
            target = self.get_next_addr() + self.arg
            return [BytecodeEffect(bstackdelta=0,
                                   vstackdelta=0,
                                   nextaddr=target,
                                   label='')]
        elif opcodename == 'POP_JUMP_IF_TRUE':
            return [BytecodeEffect(bstackdelta=0,
                                   vstackdelta=-1,
                                   nextaddr=self.arg,
                                   label='true'),
                    BytecodeEffect(bstackdelta=0,
                                   vstackdelta=-1,
                                   nextaddr=self.get_next_addr(),
                                   label='false')]
        elif opcodename == 'POP_JUMP_IF_FALSE':
            return [BytecodeEffect(bstackdelta=0,
                                   vstackdelta=-1,
                                   nextaddr=self.arg,
                                   label='false'),
                    BytecodeEffect(bstackdelta=0,
                                   vstackdelta=-1,
                                   nextaddr=self.get_next_addr(),
                                   label='true')]
        elif opcodename == 'JUMP_IF_TRUE_OR_POP':
            return [BytecodeEffect(bstackdelta=0,
                                   vstackdelta=0,
                                   nextaddr=self.arg,
                                   label='true'),
                    BytecodeEffect(vstackdelta=-1,
                                   nextaddr=self.get_next_addr(),
                                   label='false')]
        elif opcodename == 'JUMP_IF_FALSE_OR_POP':
            return [BytecodeEffect(bstackdelta=0,
                                   vstackdelta=0,
                                   nextaddr=self.arg,
                                   label='false'),
                    BytecodeEffect(bstackdelta=0,
                                   vstackdelta=-1,
                                   nextaddr=self.get_next_addr(),
                                   label='true')]
        elif opcodename == 'JUMP_ABSOLUTE':
            return [BytecodeEffect(bstackdelta=0,
                                   vstackdelta=0,
                                   nextaddr=self.arg,
                                   label='')]

        elif opcodename == 'FOR_ITER':
            return [BytecodeEffect(bstackdelta=0,
                                   vstackdelta=1,
                                   nextaddr=self.get_next_addr(),
                                   label='next'),
                    BytecodeEffect(bstackdelta=0,
                                   vstackdelta=-1,
                                   nextaddr=self.get_next_addr() + self.arg,
                                   label='end')]

        elif opcodename == 'LOAD_GLOBAL':
            return self._nextop_or_exc(1)

        elif opcodename in {'SETUP_LOOP', 'SETUP_EXCEPT', 'SETUP_FINALLY'}:
            return [BytecodeEffect(bstackdelta=BStackEntry(self),
                                   vstackdelta=0,
                                   nextaddr=self.get_next_addr(),
                                   label='')]

        elif opcodename == 'STORE_MAP':
            return self._nextop_or_exc(-2)

        elif opcodename == 'LOAD_FAST':
            return self._nextop_or_exc(1)

        elif opcodename == 'STORE_FAST':
            return [self._nextop(-1)] # no exceptions

        elif opcodename == 'DELETE_FAST':
            return [self._nextop(0)] # no exceptions

        # elif opcodename == 'LOAD_CLOSURE(self, i)
        # elif opcodename == 'LOAD_DEREF(self, i)
        # elif opcodename == 'STORE_DEREF(self, i)
        # elif opcodename == 'DELETE_DEREF(self, i)

        elif opcodename == 'SET_LINENO':
            return [self._nextop(0)] # no exceptions

        elif opcodename == 'RAISE_VARARGS':
            pass # FIXME

        elif opcodename == 'CALL_FUNCTION':
            return self._get_CALL_args_effects()

        elif opcodename == 'MAKE_FUNCTION':
            return self._nextop_or_exc(-self.arg) # no exceptions

        # elif opcodename == 'MAKE_CLOSURE(self, argc)
        elif opcodename == 'BUILD_SLICE':
            if self.arg == 3:
                return self._nextop_or_exc(-2)
            else:
                return self._nextop_or_exc(-1)

        elif opcodename == 'EXTENDED_ARG':
            assert False
        # Shouldn't reach here; we've already processed those out

        elif opcodename == 'CALL_FUNCTION_VAR':
            return self._get_CALL_args_effects(1)

        elif opcodename == 'CALL_FUNCTION_KW':
            return self._get_CALL_args_effects(1)

        elif opcodename == 'CALL_FUNCTION_VAR_KW':
            return self._get_CALL_args_effects(2)

        raise UnknownOpcode(opcodename)

    def get_next_ops(self):
        '''Get a list of (addr, label) pairs of the next code that could be executed
        The length will be 1 for most opcodes (next instruction), but could be 2 for branching
        instructions, and 0 for RETURN_VALUE etc'''

        opcodename = self.opcodename()

        if opcodename == 'RETURN_VALUE':
            return []

        # The simple case:
        nextidx = self.addr + len(self.opbytes)

        jumpidx = None
        if self.opcode in opcode.hasjrel:
            jumpidx = self.addr + self.arg + len(self.opbytes)
        elif self.opcode in opcode.hasjabs:
            jumpidx = self.arg

        # Unconditional jumps:
        if opcodename in {'JUMP_FORWARD', 'JUMP_ABSOLUTE'}:
            return [(jumpidx, '')]

        # Conditional jumps:
        if jumpidx is not None:
            nextlabel = ''
            jumplabel = ''
            if opcodename == 'FOR_ITER':
                nextlabel = 'next'
                jumplabel = 'end'

            return [(nextidx, nextlabel), (jumpidx, jumplabel)]

        return [(nextidx, '')]

    def __str__(self):
        result = ''
        if self.addr in self.cfg.linestarts:
            linenum = self.cfg.linestarts[self.addr]
            if self.addr > 0:
                result += '\n'
            result += "%3d " % linenum
            result += self.cfg.sourcelines[linenum - 1] + '\n'

        lasti = -1

        if self.addr == lasti: result += '--> '
        else: result += '    '
        if self.addr in self.cfg.labels: result += '>> '
        else: result += '   '
        result += repr(self.addr).rjust(4) + ' '

        result += '->%s' % repr(self.get_next_ops()).ljust(12)

        # Print bytes:
        byterepr = ''
        for b in self.opbytes:
            byterepr += repr(b).rjust(4) + ' '
        result += byterepr.ljust(20) + ' '

        # Print disassembly:
        result += dis.opname[self.opcode].ljust(20) + ' '
        if self.arg is not None:
            result += repr(self.arg).rjust(5) + ' '

        result += self.get_note()

        result += str(self.get_effects())

        return result

    def get_note(self):
        if self.opcode in opcode.hasconst:
            return '(' + repr(self.cfg.co.co_consts[self.arg]) + ') '
        elif self.opcode in opcode.hasname:
            return '(' + self.cfg.co.co_names[self.arg] + ') '
        elif self.opcode in opcode.hasjrel:
            return '(to ' + repr(self.addr + self.arg + len(self.opbytes)) + ') '
        elif self.opcode in opcode.haslocal:
            return '(' + self.cfg.co.co_varnames[self.arg] + ') '
        elif self.opcode in opcode.hascompare:
            return '(' + opcode.cmp_op[self.arg] + ') '
        elif self.opcode in opcode.hasfree:
            if free is None:
                free = self.cfg.co.co_cellvars + self.cfg.co.co_freevars
            return '(' + free[self.arg] + ') '
        return ''

    def get_source_line(self):
        """
        Get the source code line for this op (with the trailing newline)
        Can only be called on ops that start a line.
        """
        linenum = self.cfg.linestarts[self.addr]
        return self.cfg.sourcelines[linenum - 1]

############################################################################
# Helper functions for implementing opcodes
############################################################################
def impl_simple_unary_op(ctxt, fnname):
    # This pattern is shared by most of the UNARY_ ops
    # (though not UNARY_NOT)
    #TARGET(UNARY_POSITIVE)
    #        v = TOP();
    #        x = PyNumber_Positive(v);
    #        Py_DECREF(v);
    #        SET_TOP(x);
    #        if (x != NULL) DISPATCH();
    #        break;
    v = ctxt.compiler.v
    x = ctxt.compiler.x
    # Gen code:
    ctxt.assign(v, ctxt.TOP())
    ctxt.add_call(x, fnname, (v,))
    ctxt.Py_DECREF(v)
    ctxt.SET_TOP(x)
    true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
    true_ctxt.DISPATCH()
    false_ctxt.break_to_on_error()

def impl_simple_binary_op(ctxt, fnname, *extraargs):
    # This pattern is shared by most of the BINARY_ ops
    # (though not BINARY_ADD).  BINARY_POWER has an extraarg
    #TARGET(BINARY_foo)
    #    w = POP();
    #    v = TOP();
    #    x = fnname(v, w [, EXTRA_ARGS]);
    #    Py_DECREF(v);
    #    Py_DECREF(w);
    #    SET_TOP(x);
    #    if (x != NULL) DISPATCH();
    #    break;
    w = ctxt.compiler.w
    v = ctxt.compiler.v
    x = ctxt.compiler.x
    # Gen code:
    ctxt.POP(w)
    ctxt.assign(v, ctxt.TOP())
    ctxt.add_call(x, fnname, tuple([v, w] + list(extraargs)))
    ctxt.Py_DECREF(v)
    ctxt.Py_DECREF(w)
    ctxt.SET_TOP(x)
    true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
    true_ctxt.DISPATCH()
    false_ctxt.break_to_on_error()


def impl_simple_INPLACE_op(ctxt, fnname, *extraargs):
    # This pattern is shared by most of the INPLACE_ ops
    # (though not INPLACE_ADD); INPLACE_POWER has an extra arg
    #    TARGET(INPLACE_foo)
    #        w = POP();
    #        v = TOP();
    #        x = fnname(v, w [, EXTRA_ARGS]);
    #        Py_DECREF(v);
    #        Py_DECREF(w);
    #        SET_TOP(x);
    #        if (x != NULL) DISPATCH();
    #        break;
    w = ctxt.compiler.w
    v = ctxt.compiler.v
    x = ctxt.compiler.x
    # Gen code:
    ctxt.POP(w)
    ctxt.assign(v, ctxt.TOP())
    ctxt.add_call(x, fnname, tuple([v, w] + list(extraargs)))
    ctxt.Py_DECREF(v)
    ctxt.Py_DECREF(w)
    ctxt.SET_TOP(x)
    true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
    true_ctxt.DISPATCH()
    false_ctxt.break_to_on_error()

############################################################################
# Classes for the specific opcodes
############################################################################
# These are in the same order as the switch() statement in ceval.c (rather
# than that in opcode.h)
############################################################################

class NOP(BytecodeOp):
    def ceval(self, ctxt):
        ctxt.FAST_DISPATCH()

class LOAD_FAST(BytecodeOp):
    def ceval(self, ctxt):
        x = ctxt.compiler.x
        co = ctxt.compiler.co
        # Based on:
        #    x = GETLOCAL(oparg);
        #    if (x != NULL) {
        #        Py_INCREF(x);
        #        PUSH(x);
        #        FAST_DISPATCH();
        #    }
        #    format_exc_check_arg(PyExc_UnboundLocalError,
        #        UNBOUNDLOCAL_ERROR_MSG,
        #        PyTuple_GetItem(co->co_varnames, oparg));
        #    break;
        ctxt.assign(x, ctxt.GETLOCAL(self.arg))
        true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
        true_ctxt.Py_INCREF(x)
        true_ctxt.PUSH(x)
        true_ctxt.FAST_DISPATCH()
        false_ctxt.add_call(None,
                            'format_exc_check_arg',
                            (Global('PyObject *', 'PyExc_UnboundLocalError'),
                             ConstString(UNBOUNDLOCAL_ERROR_MSG),
                             Call('PyTuple_GetItem',
                                  (FieldDereference(co, 'co_varnames'),
                                   ConstInt(self.arg)))))
        false_ctxt.break_to_on_error()

class LOAD_CONST(BytecodeOp):
    def ceval(self, ctxt):
        x = ctxt.compiler.x
        #TARGET(LOAD_CONST)
        #    x = GETITEM(consts, oparg);
        #    Py_INCREF(x);
        #    PUSH(x);
        #    FAST_DISPATCH();
        ctxt.add_GETITEM(x, 'consts', self.arg)
        ctxt.Py_INCREF(x)
        ctxt.PUSH(x)
        ctxt.FAST_DISPATCH()

class STORE_FAST(BytecodeOp):
    def ceval(self, ctxt):
        #TARGET(STORE_FAST)
        #    v = POP();
        #    SETLOCAL(oparg, v);
        #    FAST_DISPATCH();
        v = ctxt.compiler.v
        ctxt.POP(v)
        ctxt.SETLOCAL(self.arg, v)
        ctxt.FAST_DISPATCH()

class POP_TOP(BytecodeOp):
    def ceval(self, ctxt):
        v = ctxt.compiler.v
        ctxt.POP(v)
        ctxt.Py_DECREF(v)
        ctxt.FAST_DISPATCH()

class ROT_TWO(BytecodeOp):
    def ceval(self, ctxt):
        v = ctxt.compiler.v
        w = ctxt.compiler.w
        #TARGET(ROT_TWO)
        #    v = TOP();
        #    w = SECOND();
        #    SET_TOP(w);
        #    SET_SECOND(v);
        #    FAST_DISPATCH();
        ctxt.assign(v, ctxt.TOP())
        ctxt.assign(w, ctxt.SECOND())
        ctxt.SET_TOP(w)
        ctxt.SET_SECOND(v)
        ctxt.FAST_DISPATCH()

class ROT_THREE(BytecodeOp):
    def ceval(self, ctxt):
        v = ctxt.compiler.v
        w = ctxt.compiler.w
        x = ctxt.compiler.x
        #TARGET(ROT_THREE)
        #    v = TOP();
        #    w = SECOND();
        #    x = THIRD();
        #    SET_TOP(w);
        #    SET_SECOND(x);
        #    SET_THIRD(v);
        #    FAST_DISPATCH();
        ctxt.assign(v, ctxt.TOP())
        ctxt.assign(w, ctxt.SECOND())
        ctxt.assign(x, ctxt.THIRD())
        ctxt.SET_TOP(w)
        ctxt.SET_SECOND(x)
        ctxt.SET_THIRD(v)
        ctxt.FAST_DISPATCH()

class DUP_TOP(BytecodeOp):
    pass
class DUP_TOP_TWO(BytecodeOp):
    def ceval(self, ctxt):
        x = ctxt.compiler.x
        w = ctxt.compiler.w
        #TARGET(DUP_TOP_TWO)
        #    x = TOP();
        #    Py_INCREF(x);
        #    w = SECOND();
        #    Py_INCREF(w);
        #    STACKADJ(2);
        #    SET_TOP(x);
        #    SET_SECOND(w);
        #    FAST_DISPATCH();
        ctxt.assign(x, ctxt.TOP())
        ctxt.Py_INCREF(x);
        ctxt.assign(w, ctxt.SECOND())
        ctxt.Py_INCREF(w)
        ctxt.STACKADJ(2)
        ctxt.SET_TOP(x)
        ctxt.SET_SECOND(w)
        ctxt.FAST_DISPATCH()

class UNARY_POSITIVE(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_unary_op(ctxt, 'PyNumber_Positive')

class UNARY_NEGATIVE(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_unary_op(ctxt, 'PyNumber_Negative')

class UNARY_NOT(BytecodeOp):
    pass

class UNARY_INVERT(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_unary_op(ctxt, 'PyNumber_Invert')

class BINARY_POWER(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_Power',
                              Py_None)

class BINARY_MULTIPLY(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_Multiply')

class BINARY_TRUE_DIVIDE(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_TrueDivide')

class BINARY_FLOOR_DIVIDE(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_FloorDivide')

class BINARY_MODULO(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_Remainder')

class BINARY_ADD(BytecodeOp):
    def ceval(self, ctxt):
        # For now, don't implement the PyUnicode optimization
        # from ceval.c   Hopefully our other optimizations will
        # allow a PyUnicode_Append
        impl_simple_binary_op(ctxt, 'PyNumber_Add')

class BINARY_SUBTRACT(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_Subtract')
class BINARY_SUBSCR(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyObject_GetItem')
class BINARY_LSHIFT(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_Lshift')
class BINARY_RSHIFT(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_Rshift')
class BINARY_AND(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_And')
class BINARY_XOR(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_Xor')
class BINARY_OR(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_Or')

class LIST_APPEND(BytecodeOp):
    pass

class SET_ADD(BytecodeOp):
    pass

class INPLACE_POWER(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_INPLACE_op(ctxt, 'PyNumber_InPlacePower', Py_None)
class INPLACE_MULTIPLY(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_INPLACE_op(ctxt, 'PyNumber_InPlaceMultiply')
class INPLACE_TRUE_DIVIDE(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_INPLACE_op(ctxt, 'PyNumber_InPlaceTrueDivide')
class INPLACE_FLOOR_DIVIDE(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_INPLACE_op(ctxt, 'PyNumber_InPlaceFloorDivide')
class INPLACE_MODULO(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_INPLACE_op(ctxt, 'PyNumber_InPlaceRemainder')
class INPLACE_ADD(BytecodeOp):
    def ceval(self, ctxt):
        # FIXME: for now we don't have the PyUnicode optimization that
        # ceval.c has
        impl_simple_INPLACE_op(ctxt, 'PyNumber_InPlaceAdd')
class INPLACE_SUBTRACT(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_INPLACE_op(ctxt, 'PyNumber_InPlaceSubtract')
class INPLACE_LSHIFT(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_InPlaceLshift')
class INPLACE_RSHIFT(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_InPlaceRshift')
class INPLACE_AND(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_InPlaceAnd')
class INPLACE_XOR(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_InPlaceXor')
class INPLACE_OR(BytecodeOp):
    def ceval(self, ctxt):
        impl_simple_binary_op(ctxt, 'PyNumber_InPlaceOr')

class STORE_SUBSCR(BytecodeOp):
    def ceval(self, ctxt):
        w = ctxt.compiler.w
        v = ctxt.compiler.v
        u = ctxt.compiler.u
        err = ctxt.compiler.err
        #TARGET(STORE_SUBSCR)
        #    w = TOP();
        #    v = SECOND();
        #    u = THIRD();
        #    STACKADJ(-3);
        #    /* v[w] = u */
        #    err = PyObject_SetItem(v, w, u);
        #    Py_DECREF(u);
        #    Py_DECREF(v);
        #    Py_DECREF(w);
        #    if (err == 0) DISPATCH();
        #    break;
        ctxt.assign(w, ctxt.TOP())
        ctxt.assign(v, ctxt.SECOND())
        ctxt.assign(u, ctxt.THIRD())
        ctxt.STACKADJ(-3);
        ctxt.add_comment('v[w] = u')
        ctxt.add_call(err, 'PyObject_SetItem', (v, w, u))
        ctxt.Py_DECREF(u)
        ctxt.Py_DECREF(v)
        ctxt.Py_DECREF(w)
        true_ctxt, false_ctxt = ctxt.add_conditional(err, '==', ConstInt(0), likely=True)
        true_ctxt.DISPATCH()
        false_ctxt.break_to_on_error()

class DELETE_SUBSCR(BytecodeOp):
    pass

class PRINT_EXPR(BytecodeOp):
    pass

# (CASE_TOO_BIG occurs in the switch statement here)

class RAISE_VARARGS(BytecodeOp):
    def ceval(self, ctxt):
        # TARGET(RAISE_VARARGS)
        #     v = w = NULL;
        #     switch (oparg) {
        #     case 2:
        #         v = POP(); /* cause */
        #     case 1:
        #         w = POP(); /* exc */
        #     case 0: /* Fallthrough */
        #         why = do_raise(w, v);
        #         break;
        #     default:
        #         PyErr_SetString(PyExc_SystemError,
        #                    "bad RAISE_VARARGS oparg");
        #         why = WHY_EXCEPTION;
        #         break;
        #     }
        #     break;
        # This is the do_raise() inlined, with stack values
        # assumed to be non-NULL, and the references to v, w
        # replaced with new locals
        #   w -> exc
        #   v -> cause
        ctxt.assign(v, NULL())
        ctxt.assign(w, NULL())
        if self.arg == 2:
            ctxt.POP(cause)
            ctxt.POP(exc)
            do_raise(exc, cause)
            ctxt.break_to_on_error()
        elif self.arg == 1:
            ctxt.POP(exc)
            do_raise(exc, NULL())
            ctxt.break_to_on_error()
        elif self.arg == 0:
            do_raise(NULL(), NULL()) # reraise
            ctxt.break_to_on_error()
        else:
            raise UnrollingError('bad RAISE_VARARGS oparg: %i' % self.arg)

class STORE_LOCALS(BytecodeOp):
    pass

class RETURN_VALUE(BytecodeOp):
    def ceval(self, ctxt):
        #TARGET(RETURN_VALUE)
        #    retval = POP();
        #    why = WHY_RETURN;
        #    goto fast_block_end;
        ctxt.POP(ctxt.compiler.retval)
        ctxt.set_why('WHY_RETURN')
        ctxt.goto_fast_block_end()

class YIELD_FROM(BytecodeOp):
    pass

class YIELD_VALUE(BytecodeOp):
    def ceval(self, ctxt):
        retval = ctxt.compiler.retval
        f = ctxt.compiler.f
        #TARGET(YIELD_VALUE)
        #    retval = POP();
        #    f->f_stacktop = stack_pointer;
        #    why = WHY_YIELD;
        #    goto fast_yield;
        ctxt.POP(retval)
        ctxt.store_stack()
        ctxt.set_why('WHY_YIELD')
        ctxt.fast_yield()

class POP_EXCEPT(BytecodeOp):
    pass

class POP_BLOCK(BytecodeOp):
    # TARGET(POP_BLOCK)
    #       {
    #           PyTryBlock *b = PyFrame_BlockPop(f);
    #           UNWIND_BLOCK(b);
    #       }
    #       DISPATCH();
    def ceval(self, ctxt):
        b = ctxt.pop_block()
        ctxt.UNWIND_BLOCK(b)
        ctxt.DISPATCH()

class END_FINALLY(BytecodeOp):
    pass

class LOAD_BUILD_CLASS(BytecodeOp):
    pass

class STORE_NAME(BytecodeOp):
    pass

class DELETE_NAME(BytecodeOp):
    pass

def unpack_iterable(ctxt, v, argcnt, argcntafter, offset):
    # add an inline copy of unpack_iterable, unrolled for specific values of
    # argcnt/argcntafter and stack depth
    # return a pair of context representing "return 1;", "return 0;" outcomes

    def impl_goto_error(ctxt, i):
        # Equivalent to "goto Error;"
        # Each clause gets its own unrolled copy, since i and sp are compile-time
        # rather than run-time
        while i > 0:
            ctxt.Py_DECREF(ctxt.STACK_OFFSET(0))
            i -= 1
            ctxt.vheight += 1
        ctxt.Py_XDECREF(it)
        ctxt.add_jump(return_0)

    it = ctxt.add_local('PyObject *', 'it')
    w = ctxt.add_local('PyObject *', 'w')

    # we mimic ceval.c's unpack_iterable call by moving the stack pointer up
    # to the height at which all values have been unpacked:
    ctxt.STACKADJ(offset)

    return_1 = ctxt.add_block('unpack_iterable_inlined_return_1')
    return_1.add_comment('effectively a "return 1;" from inlined unpack_iterable()')

    return_0 = ctxt.add_block('unpack_iterable_inlined_return_0')
    return_0.add_comment('effectively a "return 0;" from inlined unpack_iterable()')
    return_0.STACKADJ(-offset) # back at the old level

    ctxt.add_call(it, 'PyObject_GetIter', (v,))
    error_ctxt, non_null_ctxt = \
        ctxt.add_conditional(it, '==', NULL(), likely=False,
                             true_label='PyObject_GetIter_failed',
                             false_label='PyObject_GetIter_succeeded')

    impl_goto_error(error_ctxt, 0)

    ctxt = non_null_ctxt
    # Unroll the loop over argcnt within non_null_ctxt:
    for i in range(argcnt):
        ctxt.add_call(w, 'PyIter_Next', (it, ))
        is_null_ctxt, ctxt = \
            ctxt.add_conditional(w, '==', NULL(),
                                 true_label='call_%i_to_PyIter_Next_returned_NULL' % i,
                                 false_label='call_%i_to_PyIter_Next_returned_non_NULL' % i)
        # ^^^ note reassignment of ctxt

        # is_null_ctxt:
        is_null_ctxt.add_comment('Iterator done, via error or exhaustion.')
        no_err_occurred, err_occurred = \
            is_null_ctxt.add_conditional(UnaryExpr('!', Call('PyErr_Occurred', ())),
                                         '!=',
                                         ConstInt(0),
                                         true_label='PyErr_Occurred_is_false',
                                         false_label='PyErr_Occurred_is_true')

        # no_err_occurred:
        #   We can precompute the formatted error:
        no_err_occurred.add_call(None, 'PyErr_SetString',  # rather than PyErr_Format
                                 (PyExc_ValueError,
                                  ConstString("need more than %d value%s to unpack"
                                              % (i, "" if i == 1 else "s"))))
        impl_goto_error(no_err_occurred, i)

        # err_occurred:
        impl_goto_error(err_occurred, i)

        # non_null_ctxt: (this time from the 1st conditional above)
        #   handle "*--sp = w;"
        ctxt.STACKADJ(-1)
        ctxt.assign(ctxt.STACK_OFFSET(0), w)

    # non_null_ctxt: (continued)
    assert argcntafter == -1 # FIXME: only supporting UNPACK_SEQUENCE for now
    ctxt.add_comment('We better have exhausted the iterator now.')
    ctxt.add_call(w, 'PyIter_Next', (it, ))
    is_null_ctxt2, non_null_ctxt2 = ctxt.add_conditional(w, '==', NULL())

    # is_null_ctxt2:
    err_occurred2, no_err_occurred2 = \
        is_null_ctxt2.add_conditional(Call('PyErr_Occurred', ()),
                                      '!=', ConstInt(0))

    impl_goto_error(err_occurred2, i)

    no_err_occurred2.Py_DECREF(it)
    no_err_occurred2.add_jump(return_1) # success

    # non_null_ctxt2:
    non_null_ctxt2.Py_DECREF(w)
    non_null_ctxt2.add_call(None, 'PyErr_SetString',  # rather than PyErr_Format
                              (PyExc_ValueError,
                               # precomputed format error:
                               ConstString("too many values to unpack "
                                           "(expected %d)" % argcnt)))
    impl_goto_error(non_null_ctxt2, i)

    # FIXME: only supporting UNPACK_SEQUENCE for now

    return return_1, return_0

class UNPACK_SEQUENCE(BytecodeOp):
    def ceval(self, ctxt):
        w = ctxt.compiler.w
        v = ctxt.compiler.v
        #                    #TARGET(UNPACK_SEQUENCE)
        #                    #    v = POP();
        #                    #    if (PyTuple_CheckExact(v) &&
        # is_tuple_ctxt:     #        PyTuple_GET_SIZE(v) == oparg) {
        # correct_tuple_size:#        PyObject **items = \
        #                    #            ((PyTupleObject *)v)->ob_item;
        #                    #        while (oparg--) {
        #                    #            w = items[oparg];
        #                    #            Py_INCREF(w);
        #                    #            PUSH(w);
        #                    #        }
        #                    #        Py_DECREF(v);
        #                    #        DISPATCH();
        # not_tuple_ctxt:    #    } else if (PyList_CheckExact(v) &&
        # is_list_ctxt:      #               PyList_GET_SIZE(v) == oparg) {
        # correct_list_size: #        PyObject **items = \
        #                    #            ((PyListObject *)v)->ob_item;
        #                    #        while (oparg--) {
        #                    #            w = items[oparg];
        #                    #            Py_INCREF(w);
        #                    #            PUSH(w);
        #                    #        }
        # not_list_ctxt:     #    } else if (unpack_iterable(v, oparg, -1,
        #                    #                               stack_pointer + oparg)) {
        #                    #        STACKADJ(oparg);
        #                    #    } else {
        #                    #        /* unpack_iterable() raised an exception */
        #                    #        why = WHY_EXCEPTION;
        #                    #    }
        #                    #    Py_DECREF(v);
        #                    #    break;
        ctxt.POP(v)
        # FIXME: for now, only support tuples, with no length checking!!!
        is_tuple = ctxt.add_local('int', 'is_tuple')
        ctxt.add_call(is_tuple, 'PyTuple_CheckExact', (v, ))
        is_tuple_ctxt, not_tuple_ctxt = \
            ctxt.add_conditional(is_tuple, '!=', ConstInt(0),
                                 true_label='is_tuple',
                                 false_label='is_not_tuple')

        ctxt = is_tuple_ctxt
        tuple_size = ctxt.add_local('Py_ssize_t', 'tuple_size')
        ctxt.add_call(tuple_size, 'PyTuple_GET_SIZE', (v, ))
        correct_tuple_size, incorrect_tuple_size = \
            ctxt.add_conditional(tuple_size, '==', ConstInt(self.arg),
                                 true_label='correct_tuple_size',
                                 false_label='incorrect_tuple_size')

        ctxt = correct_tuple_size
        oparg = self.arg
        while oparg:
            oparg -= 1
            ctxt.add_call(w, 'PyTuple_GET_ITEM', (v, ConstInt(oparg)))
            ctxt.Py_INCREF(w)
            ctxt.PUSH(w)
        ctxt.Py_DECREF(v)
        ctxt.DISPATCH()

        ctxt = incorrect_tuple_size
        ctxt.add_jump(not_tuple_ctxt)

        ctxt = not_tuple_ctxt
        is_list = ctxt.add_local('int', 'is_list')
        ctxt.add_call(is_list, 'PyList_CheckExact', (v, ))
        is_list_ctxt, not_list_ctxt = \
            ctxt.add_conditional(is_list, '!=', ConstInt(0),
                                 true_label='is_list',
                                 false_label='unpack_iterable')

        ctxt = is_list_ctxt
        list_size = ctxt.add_local('Py_ssize_t', 'list_size')
        ctxt.add_call(list_size, 'PyList_GET_SIZE', (v, ))
        correct_list_size, incorrect_list_size = \
            ctxt.add_conditional(list_size, '==', ConstInt(self.arg),
                                 true_label='correct_list_size',
                                 false_label='incorrect_list_size')

        ctxt = correct_list_size
        oparg = self.arg
        while oparg:
            oparg -= 1
            ctxt.add_call(w, 'PyList_GET_ITEM', (v, ConstInt(oparg)))
            ctxt.Py_INCREF(w)
            ctxt.PUSH(w)
        ctxt.Py_DECREF(v)
        ctxt.break_to_on_error()

        ctxt = incorrect_list_size
        ctxt.add_jump(not_list_ctxt)

        # not_list_ctxt:
        true_ctxt, false_ctxt = \
            unpack_iterable(not_list_ctxt, v, self.arg, -1, self.arg)

        # the STACKADJ on true_ctxt is done for us by unpack_iterable
        true_ctxt.Py_DECREF(v)
        true_ctxt.break_to_on_error()

        false_ctxt.add_comment('unpack_iterable() raised an exception')
        false_ctxt.set_why('WHY_EXCEPTION')
        false_ctxt.Py_DECREF(v)
        false_ctxt.break_to_on_error()

class UNPACK_EX(BytecodeOp):
    pass

class STORE_ATTR(BytecodeOp):
    def ceval(self, ctxt):
        w = ctxt.compiler.w
        v = ctxt.compiler.v
        u = ctxt.compiler.u
        err = ctxt.compiler.err
        #TARGET(STORE_ATTR)
        #    w = GETITEM(names, oparg);
        #    v = TOP();
        #    u = SECOND();
        #    STACKADJ(-2);
        #    err = PyObject_SetAttr(v, w, u); /* v.w = u */
        #    Py_DECREF(v);
        #    Py_DECREF(u);
        #    if (err == 0) DISPATCH();
        #    break;
        ctxt.assign(w, Expression('GETITEM(names, %i)' % self.arg))
        ctxt.assign(v, ctxt.TOP())
        ctxt.assign(u, ctxt.SECOND())
        ctxt.STACKADJ(-2)
        ctxt.add_comment('v.w = u')
        ctxt.add_call(err, 'PyObject_SetAttr', (v, w, u))
        ctxt.Py_DECREF(v)
        ctxt.Py_DECREF(u)
        true_ctxt, false_ctxt = ctxt.add_conditional(err, '==', ConstInt(0), likely=True)
        true_ctxt.DISPATCH()
        false_ctxt.break_to_on_error()

class DELETE_ATTR(BytecodeOp):
    pass
class STORE_GLOBAL(BytecodeOp):
    pass
class DELETE_GLOBAL(BytecodeOp):
    pass
class LOAD_NAME(BytecodeOp):
    pass

class LOAD_GLOBAL(BytecodeOp):
    def ceval(self, ctxt):
        x = ctxt.compiler.x
        w = ctxt.compiler.w
        #TARGET(LOAD_GLOBAL)
        #    w = GETITEM(names, oparg);
        #    if (PyDict_CheckExact(f->f_globals)
        #        && PyDict_CheckExact(f->f_builtins)) {
        #        x = _PyDict_LoadGlobal((PyDictObject *)f->f_globals,
        #                               (PyDictObject *)f->f_builtins,
        #                               w);
        #        if (x == NULL) {
        #            if (!PyErr_Occurred())
        #                format_exc_check_arg(PyExc_NameError,
        #                                     GLOBAL_NAME_ERROR_MSG, w);
        #            break;
        #        }
        #        Py_INCREF(x);
        #    }
        #    else {
        #        /* Slow-path if globals or builtins is not a dict */
        #        x = PyObject_GetItem(f->f_globals, w);
        #        if (x == NULL) {
        #            x = PyObject_GetItem(f->f_builtins, w);
        #            if (x == NULL) {
        #                if (PyErr_ExceptionMatches(PyExc_KeyError))
        #                    format_exc_check_arg(
        #                                PyExc_NameError,
        #                                GLOBAL_NAME_ERROR_MSG, w);
        #                break;
        #            }
        #        }
        #    }
        #    PUSH(x);
        #    DISPATCH();
        ctxt.add_GETITEM(w, 'names', self.arg)
        if 1:
            # Simplify optimization by deferring inlining the impl until
            # later:
            ctxt.add_call(x, 'impl_LOAD_GLOBAL', (ctxt.compiler.f, w, ))
            true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
            true_ctxt.PUSH(x)
            true_ctxt.DISPATCH()
            false_ctxt.break_to_on_error()
        else:
            true_ctxt, false_ctxt = ctxt.add_conditional(
                Expression('PyDict_CheckExact(f->f_globals) && PyDict_CheckExact(f->f_builtins)'),
                '!=', ConstInt(0))
            merge_ctxt = ctxt.add_block()
            true_ctxt.add_call(x, '_PyDict_LoadGlobal',
                               (Expression('(PyDictObject *)f->f_globals'),
                                Expression('(PyDictObject *)f->f_builtins'),
                                w))
            true_ctxt2, false_ctxt2 = true_ctxt.add_conditional(x, '==', NULL())
            true_ctxt2.writeln('        if (!PyErr_Occurred())')
            true_ctxt2.writeln('            format_exc_check_arg(PyExc_NameError,')
            true_ctxt2.writeln('                                 GLOBAL_NAME_ERROR_MSG, w);')
            true_ctxt2.writeln('        break;')
            true_ctxt2.writeln('    }')
            false_ctxt2.Py_INCREF(x)
            false_ctxt2.add_jump(merge_ctxt)
            false_ctxt.add_comment('Slow-path if globals or builtins is not a dict')
            false_ctxt.add_call(x, 'PyObject_GetItem',
                                (Expression('f->f_globals'),
                                 w))
            false_ctxt.writeln('    if (x == NULL) {')
            false_ctxt.add_call(x, 'PyObject_GetItem',
                                (Expression('f->f_builtins'),
                                 w))
            false_ctxt.writeln('        if (x == NULL) {')
            false_ctxt.writeln('            if (PyErr_ExceptionMatches(PyExc_KeyError))')
            false_ctxt.writeln('                format_exc_check_arg(')
            false_ctxt.writeln('                            PyExc_NameError,')
            false_ctxt.writeln('                            GLOBAL_NAME_ERROR_MSG, w);')
            false_ctxt.writeln('            break;')
            false_ctxt.writeln('        }')
            false_ctxt.writeln('    }')
            false_ctxt.add_jump(merge_ctxt)
            merge_ctxt.PUSH(x)
            merge_ctxt.DISPATCH()

class DELETE_FAST(BytecodeOp):
    pass
class DELETE_DEREF(BytecodeOp):
    pass
class LOAD_CLOSURE(BytecodeOp):
    pass
class LOAD_DEREF(BytecodeOp):
    pass
class STORE_DEREF(BytecodeOp):
    pass


class BUILD_TUPLE(BytecodeOp):
    def ceval(self, ctxt):
        x = ctxt.compiler.x
        # TARGET(BUILD_TUPLE)
        #     x = PyTuple_New(oparg);
        #     if (x != NULL) {
        #         for (; --oparg >= 0;) {
        #             w = POP();
        #             PyTuple_SET_ITEM(x, oparg, w);
        #         }
        #         PUSH(x);
        #         DISPATCH();
        #     }
        #     break;
        ctxt.add_call(x, 'PyTuple_New', (ConstInt(self.arg), ))
        true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
        # unroll the loop:
        for i in range(self.arg-1 , -1, -1):
            true_ctxt.add_call(None, 'PyTuple_SET_ITEM',
                               (x, ConstInt(i), true_ctxt.TOP()))
            true_ctxt.STACKADJ(-1)
        true_ctxt.PUSH(x)
        true_ctxt.DISPATCH()
        false_ctxt.break_to_on_error()

class BUILD_LIST(BytecodeOp):
    def ceval(self, ctxt):
        x = ctxt.compiler.x
        #TARGET(BUILD_LIST)
        #    x =  PyList_New(oparg);
        #    if (x != NULL) {
        #        for (; --oparg >= 0;) {
        #            w = POP();
        #            PyList_SET_ITEM(x, oparg, w);
        #        }
        #        PUSH(x);
        #        DISPATCH();
        #    }
        #    break;
        ctxt.add_call(x, 'PyList_New', (ConstInt(self.arg), ))
        true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
        # unroll the loop:
        for i in range(self.arg-1 , -1, -1):
            true_ctxt.add_call(None, 'PyList_SET_ITEM',
                               (x, ConstInt(i), true_ctxt.TOP()))
            true_ctxt.STACKADJ(-1)
        true_ctxt.PUSH(x)
        true_ctxt.DISPATCH()
        false_ctxt.break_to_on_error()

class BUILD_SET(BytecodeOp):
    pass

class BUILD_MAP(BytecodeOp):
    def ceval(self, ctxt):
        x = ctxt.compiler.x
        #TARGET(BUILD_MAP)
        #    x = _PyDict_NewPresized((Py_ssize_t)oparg);
        #    PUSH(x);
        #    if (x != NULL) DISPATCH();
        #    break;
        ctxt.add_call(x, '_PyDict_NewPresized', (ConstInt(self.arg),) )
        ctxt.PUSH(x)
        true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
        true_ctxt.DISPATCH()
        false_ctxt.break_to_on_error()

class STORE_MAP(BytecodeOp):
    def ceval(self, ctxt):
        w = ctxt.compiler.w
        u = ctxt.compiler.u
        v = ctxt.compiler.v
        err = ctxt.compiler.err
        #TARGET(STORE_MAP)
        #    w = TOP();     /* key */
        #    u = SECOND();  /* value */
        #    v = THIRD();   /* dict */
        #    STACKADJ(-2);
        #    assert (PyDict_CheckExact(v));
        #    err = PyDict_SetItem(v, w, u);  /* v[w] = u */
        #    Py_DECREF(u);
        #    Py_DECREF(w);
        #    if (err == 0) DISPATCH();
        #    break;
        ctxt.assign(w, ctxt.TOP())
        ctxt.assign(u, ctxt.SECOND())
        ctxt.assign(v, ctxt.THIRD())
        ctxt.STACKADJ(-2);
        ctxt.writeln('assert (PyDict_CheckExact(v));') # FIXME
        ctxt.add_comment('v[w] = u')
        ctxt.add_call(err, 'PyDict_SetItem', (v, w, u))
        ctxt.Py_DECREF(u)
        ctxt.Py_DECREF(w)
        true_ctxt, false_ctxt = ctxt.add_conditional(err, '==', ConstInt(0))
        true_ctxt.DISPATCH()
        false_ctxt.break_to_on_error()

class MAP_ADD(BytecodeOp):
    pass


class LOAD_ATTR(BytecodeOp):
    def ceval(self, ctxt):
        w = ctxt.compiler.w
        v = ctxt.compiler.v
        x = ctxt.compiler.x
        #TARGET(LOAD_ATTR)
        #    w = GETITEM(names, oparg);
        #    v = TOP();
        #    x = PyObject_GetAttr(v, w);
        #    Py_DECREF(v);
        #    SET_TOP(x);
        #    if (x != NULL) DISPATCH();
        #    break;
        ctxt.assign(w, Expression('GETITEM(names, %i)' % self.arg))
        ctxt.assign(v, ctxt.TOP())
        ctxt.add_call(x, 'PyObject_GetAttr', (v, w))
        ctxt.Py_DECREF(v)
        ctxt.SET_TOP(x)
        true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
        true_ctxt.DISPATCH()
        false_ctxt.break_to_on_error()

class COMPARE_OP(BytecodeOp):
    def ceval(self, ctxt):
        w = ctxt.compiler.w
        v = ctxt.compiler.v
        x = ctxt.compiler.x
        #TARGET(COMPARE_OP)
        #    w = POP();
        #    v = TOP();
        #    x = cmp_outcome(oparg, v, w);
        #    Py_DECREF(v);
        #    Py_DECREF(w);
        #    SET_TOP(x);
        #    if (x == NULL) break;
        #    PREDICT(POP_JUMP_IF_FALSE);
        #    PREDICT(POP_JUMP_IF_TRUE);
        #    DISPATCH();
        ctxt.POP(w)
        ctxt.assign(v, ctxt.TOP())
        merge_ctxt = self.cmp_outcome(ctxt, x, self.arg, v, w)
        merge_ctxt.Py_DECREF(v)
        merge_ctxt.Py_DECREF(w)
        merge_ctxt.SET_TOP(x)
        true_ctxt, false_ctxt = merge_ctxt.add_conditional(x, '==', NULL())
        true_ctxt.break_to_on_error()
        false_ctxt.DISPATCH()

    def cmp_outcome(self, ctxt, x, arg, v, w):
        # This is equivalent to the line:
        #    x = cmp_outcome(oparg, v, w);
        # within COMPARE_OP in ceval.c
        # This unrolls cmp_outcome, assigning the returned value to x
        # (without assigning it to v)
        merge_ctxt = ctxt.add_block()
        next_ctxt = ctxt
        res = ctxt.add_local('int', 'res')
        # ceval.c initializes res to 0, but this isn't necessary
        if arg == PyCmp_IS:
            ctxt.assign(res, Expression('(%s == %s)' % (v.name, w.name))) # FIXME
        elif arg == PyCmp_IS_NOT:
            ctxt.assign(res, Expression('(%s != %s)' % (v.name, w.name))) # FIXME
        elif arg == PyCmp_IN:
            ctxt.add_call(res, 'PySequence_Contains', (w, v))
            true_ctxt, false_ctxt = ctxt.add_conditional(res, '<', ConstInt(0))
            true_ctxt.assign(x, NULL())
            true_ctxt.add_jump(merge_ctxt)
            next_ctxt = false_ctxt
        elif arg == PyCmp_NOT_IN:
            ctxt.add_call(res, 'PySequence_Contains', (w, v))
            true_ctxt, false_ctxt = ctxt.add_conditional(res, '<', ConstInt(0))
            true_ctxt.assign(x, NULL())
            true_ctxt.add_jump(merge_ctxt.addr)
            false_ctxt.assign(res, Expression('!%s' % res)) # FIXME
            next_ctxt = false_ctxt
        elif arg == PyCmp_EXC_MATCH:
            ctxt.writeln('if (PyTuple_Check(w)) {')
            ctxt.writeln('    Py_ssize_t i, length;')
            ctxt.writeln('    length = PyTuple_Size(w);')
            ctxt.writeln('    for (i = 0; i < length; i += 1) {')
            ctxt.writeln('        PyObject *exc = PyTuple_GET_ITEM(w, i);')
            ctxt.writeln('        if (!PyExceptionClass_Check(exc)) {')
            ctxt.writeln('            PyErr_SetString(PyExc_TypeError,')
            ctxt.writeln('                            CANNOT_CATCH_MSG);')
            ctxt.writeln('            return NULL;')
            ctxt.writeln('            }')
            ctxt.writeln('        }')
            ctxt.writeln('    }')
            ctxt.writeln('else {')
            ctxt.writeln('    if (!PyExceptionClass_Check(w)) {')
            ctxt.writeln('        PyErr_SetString(PyExc_TypeError,')
            ctxt.writeln('                        CANNOT_CATCH_MSG);')
            ctxt.writeln('        return NULL;')
            ctxt.writeln('        }')
            ctxt.writeln('    }')
            ctxt.writeln('res = PyErr_GivenExceptionMatches(v, w);')
            ctxt.writeln('break;')
        else:
            # use enum cmp_op when writing out the C, for clarity:
            ctxt.add_call(x, 'PyObject_RichCompare', (v, w, EnumValue(arg, enum_cmp_op[arg])))
            return ctxt
        next_ctxt.assign(x, Expression('%s ? Py_True : Py_False' % res.name)) # FIXME
        next_ctxt.add_call(None, 'Py_INCREF', (x,))
        next_ctxt.add_jump(merge_ctxt)
        return merge_ctxt

class IMPORT_NAME(BytecodeOp):
    pass

class IMPORT_STAR(BytecodeOp):
    pass

class IMPORT_FROM(BytecodeOp):
    pass


class JUMP_FORWARD(BytecodeOp):
    def ceval(self, ctxt):
        # TARGET(JUMP_FORWARD)
        #    JUMPBY(oparg);
        #    FAST_DISPATCH();
        ctxt.JUMPBY(self.arg)
        ctxt.FAST_DISPATCH()

class POP_JUMP_IF_FALSE(BytecodeOp):
    def ceval(self, ctxt):
        w = ctxt.compiler.w
        err = ctxt.compiler.err
        #TARGET(POP_JUMP_IF_FALSE)
        #    w = POP();
        #    if (w == Py_True) {
        #        Py_DECREF(w);
        #        FAST_DISPATCH();
        #    }
        #    if (w == Py_False) {
        #        Py_DECREF(w);
        #        JUMPTO(oparg);
        #        FAST_DISPATCH();
        #    }
        #    err = PyObject_IsTrue(w);
        #    Py_DECREF(w);
        #    if (err > 0)
        #        err = 0;
        #    else if (err == 0)
        #        JUMPTO(oparg);
        #    else
        #        break;
        #    DISPATCH();
        ctxt.POP(w)
        true_ctxt, false_ctxt = ctxt.add_conditional(w, '==', Const('Py_True'))
        true_ctxt.Py_DECREF(w)
        true_ctxt.FAST_DISPATCH()
        true_ctxt2, false_ctxt2 = false_ctxt.add_conditional(w, '==', Const('Py_False'))
        true_ctxt2.Py_DECREF(w)
        true_ctxt2.JUMPTO(self.arg)
        false_ctxt2.add_call(err, 'PyObject_IsTrue', (w,))
        false_ctxt2.Py_DECREF(w)
        true_ctxt3, false_ctxt3 = false_ctxt2.add_conditional(err, '>', ConstInt(0))
        true_ctxt3.assign(err, ConstInt(0)) # redundant in this implementation
        true_ctxt3.DISPATCH()
        true_ctxt4, false_ctxt4 = false_ctxt3.add_conditional(err, '==', ConstInt(0))
        true_ctxt4.JUMPTO(self.arg)
        false_ctxt4.break_to_on_error()

class POP_JUMP_IF_TRUE(BytecodeOp):
    pass
class JUMP_IF_FALSE_OR_POP(BytecodeOp):
    pass
class JUMP_IF_TRUE_OR_POP(BytecodeOp):
    pass

class JUMP_ABSOLUTE(BytecodeOp):
    def ceval(self, ctxt):
        ctxt.JUMPTO(self.arg)
        # FIXME: see FAST_LOOPS in ceval.c

class GET_ITER(BytecodeOp):
    def ceval(self, ctxt):
        #TARGET(GET_ITER)
        #    /* before: [obj]; after [getiter(obj)] */
        #    v = TOP();
        #    x = PyObject_GetIter(v);
        #    Py_DECREF(v);
        #    if (x != NULL) {
        #        SET_TOP(x);
        #        PREDICT(FOR_ITER);
        #        DISPATCH();
        #    }
        #    STACKADJ(-1);
        #    break;
        ctxt.add_comment('before: [obj]; after [getiter(obj)]')
        v = ctxt.compiler.v
        ctxt.assign(v, ctxt.TOP())
        x = ctxt.compiler.x
        ctxt.add_call(x, 'PyObject_GetIter', (v,))
        ctxt.Py_DECREF(v)
        true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
        true_ctxt.SET_TOP(x)
        true_ctxt.DISPATCH()
        false_ctxt.STACKADJ(-1)
        false_ctxt.break_to_on_error()

class FOR_ITER(BytecodeOp):
    def ceval(self, ctxt):
        #TARGET(FOR_ITER)
        #    /* before: [iter]; after: [iter, iter()] *or* [] */
        #    v = TOP();
        #    x = (*v->ob_type->tp_iternext)(v);
        #    if (x != NULL) {
        #        PUSH(x);
        #        PREDICT(STORE_FAST);
        #        PREDICT(UNPACK_SEQUENCE);
        #        DISPATCH();
        #    }
        #    if (PyErr_Occurred()) {
        #        if (!PyErr_ExceptionMatches(
        #                        PyExc_StopIteration))
        #            break;
        #        PyErr_Clear();
        #    }
        #    /* iterator ended normally */
        #    x = v = POP();
        #    Py_DECREF(v);
        #    JUMPBY(oparg);
        #    DISPATCH();
        ctxt.add_comment('before: [iter]; after: [iter, iter()] *or* []')
        v = ctxt.compiler.v
        ctxt.assign(v, ctxt.TOP())
        x = ctxt.compiler.x
        ctxt.add_call(x, 'INVOKE_tp_iternext', (v,)) # FIXME: add macro
        true_ctxt, false_ctxt = \
            ctxt.add_conditional(x, '!=', NULL(), likely=True,
                                 true_label='nonnull_tp_iternext',
                                 false_label='null_tp_iternext')

        true_ctxt.PUSH(x)
        true_ctxt.DISPATCH()

        true_ctxt2, false_ctxt2 = \
            false_ctxt.add_conditional(Call('PyErr_Occurred', ()),
                                       '!=', ConstInt(0),
                                       true_label='PyErr_Occurred',
                                       false_label='not_PyErr_Occurred')

        true_ctxt3, false_ctxt3 = \
            true_ctxt2.add_conditional(Call('PyErr_ExceptionMatches',
                                            (Global('PyObject *', 'PyExc_StopIteration'), )),
                                       '==', ConstInt(0),
                                       true_label='is_StopIteration',
                                       false_label='is_not_StopIteration')
        true_ctxt3.break_to_on_error()
        false_ctxt3.add_call(None, 'PyErr_Clear', ())
        false_ctxt3.add_jump(false_ctxt2)

        false_ctxt2.add_comment('iterator ended normally')
        false_ctxt2.POP(v)
        false_ctxt2.assign(x, v)
        false_ctxt2.Py_DECREF(v)
        false_ctxt2.JUMPBY(self.arg)
        #false_ctxt2.DISPATCH()

class BREAK_LOOP(BytecodeOp):
    def ceval(self, ctxt):
        #TARGET(BREAK_LOOP)
        #    why = WHY_BREAK;
        #    goto fast_block_end;
        ctxt.set_why('WHY_BREAK')
        ctxt.goto_fast_block_end()

class CONTINUE_LOOP(BytecodeOp):
    pass

def impl_setup_finally(op, ctxt):
    # This is shared by SETUP_LOOP, SETUP_EXCEPT and SETUP_FINALLY:
    # with this implementation:
    # _setup_finally:
    #   PyFrame_BlockSetup(f, opcode, INSTR_OFFSET() + oparg,
    #                      STACK_LEVEL());
    #   DISPATCH();
    ctxt.block_setup(op,
                     type_=SETUP_FINALLY,
                     handler=ctxt.INSTR_OFFSET() + op.arg,
                     level=ctxt.STACK_LEVEL())
    ctxt.DISPATCH()

class SETUP_LOOP(BytecodeOp):
    def ceval(self, ctxt):
        impl_setup_finally(self, ctxt)

class SETUP_EXCEPT(BytecodeOp):
    def ceval(self, ctxt):
        impl_setup_finally(self, ctxt)

class SETUP_FINALLY(BytecodeOp):
    def ceval(self, ctxt):
        impl_setup_finally(self, ctxt)

class SETUP_WITH(BytecodeOp):
    pass

class WITH_CLEANUP(BytecodeOp):
    pass

class CALL_FUNCTION(BytecodeOp):
    def ceval(self, ctxt):
        # we implement CALL_FUNCTION as a call to a function of the form
        #   impl_CALL_FUNCTION_na_NUM_POS_ARGS_nk_NUM_KWARGS
        # i.e. with a particular number of positional and keyword args.
        # This makes it easier to specialize these function calls
        # into raw C calls if type-analysis detects that we know
        # which function is being called (especially in absence of kwargs)
        # The functions get autogenerated later on if they're still needed.
        na = self.arg & 0xff
        nk = (self.arg>>8) & 0xff
        n = na + 2 * nk;
        ctxt.add_comment('na=%i, nk=%i' % (na, nk))
        x = ctxt.compiler.x

        kwargs = []
        for i in range(nk):
            kwargs.append(ctxt.POP())
            kwargs.append(ctxt.POP())
        args = []
        for i in range(na):
            args.append(ctxt.POP())
        func = ctxt.POP()
        # positional args are in reverse order:
        callargs = tuple([func] + args[::-1] + kwargs)
        ctxt.add_call(x, 'impl_CALL_FUNCTION_na%i_nk%i' % (na, nk),
                      callargs)
        true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
        true_ctxt.PUSH(x)
        true_ctxt.DISPATCH()
        false_ctxt.break_to_on_error()

class CALL_FUNCTION_VAR(BytecodeOp):
    pass

class CALL_FUNCTION_KW(BytecodeOp):
    pass

class CALL_FUNCTION_VAR_KW(BytecodeOp):
    pass

class MAKE_CLOSURE(BytecodeOp):
    pass

class MAKE_FUNCTION(BytecodeOp):
    pass

class BUILD_SLICE(BytecodeOp):
    def ceval(self, ctxt):
        w = ctxt.compiler.w
        v = ctxt.compiler.v
        u = ctxt.compiler.u
        x = ctxt.compiler.x
        #TARGET(BUILD_SLICE)
        #    if (oparg == 3)
        #        w = POP();
        #    else
        #        w = NULL;
        #    v = POP();
        #    u = TOP();
        #    x = PySlice_New(u, v, w);
        #    Py_DECREF(u);
        #    Py_DECREF(v);
        #    Py_XDECREF(w);
        #    SET_TOP(x);
        #    if (x != NULL) DISPATCH();
        #    break;
        if self.arg == 3:
            ctxt.POP(w)
        else:
            ctxt.assign(w, NULL())
        ctxt.POP(v)
        ctxt.assign(u, ctxt.TOP())
        ctxt.add_call(x, 'PySlice_New', (u, v, w))
        ctxt.Py_DECREF(u)
        ctxt.Py_DECREF(v)
        ctxt.Py_XDECREF(w)
        ctxt.SET_TOP(x)
        true_ctxt, false_ctxt = ctxt.add_conditional(x, '!=', NULL(), likely=True)
        true_ctxt.DISPATCH()
        false_ctxt.break_to_on_error()

class EXCEPT_HANDLER(BytecodeOp):
    pass

############################################################################
# (end of implementations of specific opcodes)
############################################################################
