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

from collections import OrderedDict
from io import StringIO
import sys

from coconut.cfg import CFG, Block, Op, Edge
from coconut.dot import to_html, _dot_column
from coconut.cwriter import CWriter

WRITE_BLOCKS_INLINE = 1

class IrFunction:
    def __init__(self, returntype, fnname, params):
        self.returntype = returntype
        self.fnname = fnname
        # Allow param list to simply contain types,
        # to avoid people having to name them
        for i, param in enumerate(params):
            if isinstance(param, IrType):
                params[i] = Param(param, 'param%i' % i)
            elif not isinstance(param, Param):
                raise ValueError('bad parameter for %s: %s'
                                 % (fnname, param))
        self.params = params

    def __hash__(self):
        return hash(self.fnname)

    def __eq__(self, other):
        return self.fnname == other.fnname

    def __repr__(self):
        return '%s(fnname=%r)' % (self.__class__.__name__, self.fnname)

class IrCFG(CFG, IrFunction):
    def __init__(self, returntype, fnname, params):
        CFG.__init__(self)
        IrFunction.__init__(self, returntype, fnname, params)

        # keep an ordered list of blocks
        self.blocks = []
        self.locals = []
        self.name_to_local = {}

    def add_local(self, type_, name):
        if name in self.name_to_local:
            i = 1
            namei = '%s%03i' % (name, i)
            while namei in self.name_to_local:
                i += 1
                namei = '%s%03i' % (name, i)
            name = namei
        local = Local(type_, name)
        self.locals.append(local)
        self.name_to_local[name] = local
        return local

    def to_c(self):
        s = StringIO()
        w = CWriter(s)
        self.to_writer(w)
        return s.getvalue()

    def to_writer(self, w):
        w.writeln('%s\n' % self.returntype.to_c())
        c_params = ', '.join(param.to_c() for param in self.params)
        w.writeln('%s(%s)' % (self.fnname, c_params))
        w.writeln('{')
        w.indent()
        for local in self.locals:
            w.writeln('%s %s;' % (local.type_.to_c(), local.name))

        # Simplify the generated C source
        # For blocks that have a single entry in a conditional
        # render the block within the conditional (rather than outside it with a goto)
        if WRITE_BLOCKS_INLINE:
            edges_by_dest = self.calc_edges_by_dest()
            # dict mapping from dest_addr to list of [(source Block, source Op]]
            for dest_addr in edges_by_dest:
                srcs = edges_by_dest[dest_addr]
                if len(srcs) == 1:
                    src_block, src_op = srcs[0]
                    if isinstance(src_op, Conditional):
                        w.inline_addrs.add(dest_addr)
            # print('inline_addrs: %r' % w.inline_addrs)
            w.ircfg = self # for use by Conditional.write

        for block in self.blocks:
            if block.addr in w.inline_addrs:
                # we'll render this within the conditional that jumps to it
                continue
            w.writeln('%s:' % block.addr)
            w.writeln('{')
            w.indent()
            if hasattr(self, 'pred_edges_by_block'):
                w.writeln('/* reachable from: %s */' % self.pred_edges_by_block[block])
            for local in block.phis_for_locals:
                phi = block.phis_for_locals[local]
                phi.write(w)
            for op in block.ops:
                op.write(w)
            w.outdent()
            w.writeln('}')
        w.outdent()
        w.writeln('}')

    def add_block(self, addr):
        if addr in self.addr_to_block:
            i = 1
            addri = '%s%03i' % (addr, i)
            while addri in self.addr_to_block:
                i += 1
                addri = '%s%03i' % (addr, i)
            addr = addri
        return self.add_block_at(addr)

    def make_block(self, addr):
        return IrBlock(self, addr)

    def verify(self):
        CFG.verify(self)

        for block in self.blocks:
            # Should be no jumps or conditionals except at the end of a block:
            for op in block.ops[:-2]:
                assert (not isinstance(op, (Jump, Conditional))), \
                    block.addr

            # Final op should be a jump, conditional or return:
            if block.ops:
                if not isinstance(block.ops[-1], (Jump, Conditional, Return)):
                    raise ValueError('block %s is not properly terminated; final op: %r'
                                     % (block, block.ops[-1]))

    def calc_edges(self):
        # get list of (src_block, src_op, dest_addr):
        edges = []
        def add_edge(dest_addr):
            edges.append((block, op, dest_addr))
        for block in self.blocks:
            for op in block.ops:
                if isinstance(op, Conditional):
                    add_edge(op.true_block.addr)
                    add_edge(op.false_block.addr)
                if isinstance(op, Jump):
                    add_edge(op.dest_block.addr)
        return edges

    def calc_edges_by_dest(self):
        # get dict mapping from dest_addr to list of [(source Block, source Op]]
        edges = self.calc_edges()
        edges_by_dest = {}
        for src_block, src_op, dest_addr in edges:
            if dest_addr in edges_by_dest:
                edges_by_dest[dest_addr].append((src_block, src_op))
            else:
                edges_by_dest[dest_addr] = [(src_block, src_op)]
        return edges_by_dest

class IrBlock(Block):
    def __init__(self, cfg, addr):
        Block.__init__(self, cfg, addr)
        self.phis_for_locals = {} # dict from Local/SSAName to Phi

    def __repr__(self):
        return 'Block(addr=%r)' % self.addr

    def real_ops_to_c(self):
        return ''.join(op.to_c()
                       for op in self.get_real_ops())

    def writeln(self):
        self.ops.append(Whitespace(''))

    def add_comment(self, text):
        self.ops.append(Comment(text))

    def add_local(self, type_, name, init):
        local = self.cfg.add_local(type_, 'within_%s_%s' % (self.addr, name))
        if init:
            self.add_assignment(local, init)
        return local

    def add_code(self, code):
        self.ops.append(Code(code))

    def add_assignment(self, lhs, rhs):
        assert isinstance(lhs, Expression)
        assert isinstance(rhs, Expression)
        assignment = Assignment(lhs, rhs)
        self.ops.append(assignment)
        return assignment

    def add_eval(self, expr):
        assert isinstance(expr, Expression)
        eval_ = Eval(expr)
        self.ops.append(eval_)
        return eval_

    def add_conditional(self, expr,
                        likely=None,
                        true_label='true', false_label='false'):
        assert isinstance(expr, Expression)
        true_block = self.cfg.add_block(true_label)
        false_block = self.cfg.add_block(false_label)
        cond = Conditional(expr,
                           true_block, false_block,
                           likely)
        self.ops.append(cond)
        self.cfg.add_edge(Edge(self, true_block))
        self.cfg.add_edge(Edge(self, false_block))
        return true_block, false_block

    def add_call(self, lhs, fn, args):
        assert isinstance(fn, IrFunction)
        call = Call(fn, args)
        if lhs:
            self.add_assignment(lhs, call)
        else:
            self.add_eval(call)
        return call

    def add_conditional_call(self, tmpname, fnname, args, likely=None,
                             true_label='true', false_label='false'):
        #  if (fnname()) { } else {}
        tmp = self.add_local('int', tmpname, None)
        self.add_call(tmp, fnname, args)
        return self.add_conditional(tmp, '!=', ConstInt(0),
                                    likely=likely,
                                    true_label=true_label,
                                    false_label=false_label)

    def add_conditionals(self, conditionals):
        true_block = self
        any_are_false = self.cfg.add_block('any_are_false')
        for lhs, expr, rhs in conditionals:
            true_block, false_block = \
                true_block.add_conditional(lhs, expr, rhs)
            false_block.add_jump(any_are_false.addr)
        return true_block, any_are_false

    def add_deref_call(self, lhs, local, args):
        call = DerefCall(lhs, local, args)
        self.ops.append(call)
        return call

    def add_jump(self, dest_block):
        assert isinstance(dest_block, IrBlock)
        self.ops.append(Jump(dest_block))
        self.cfg.add_edge(Edge(self, dest_block))

    def add_return(self, expr):
        self.ops.append(Return(expr))

    def is_empty(self):
        #print('is_empty(%r)' % self.addr)
        # Is this full of Nops, possibly with a trailing Jump/Conditional?
        for op in self.ops[:-1]:
            if not isinstance(op, Nop):
                return False

        if not self.ops:
            return True
        if isinstance(self.ops[-1], (Nop, Conditional, Jump)):
            return True
        return False

    def to_dot_label(self):
        result = '<table border="0" cellspacing="0">\n'
        result += '<tr>%s</tr>\n' % _dot_column(self.addr)
        for local in self.phis_for_locals:
            phi = self.phis_for_locals[local]
            result += '<tr>%s</tr>\n' % _dot_column(repr(phi))
        for op in self.ops:
            result += '<tr>%s</tr>\n' % _dot_column(repr(op))
        result += '</table>\n'
        return result

    def add_Py_INCREF(self, expr):
        self.add_call(None, 'Py_INCREF', (expr, ))

    def add_Py_DECREF(self, expr):
        self.add_call(None, 'Py_DECREF', (expr, ))

    def get_real_ops(self):
        # Get non-comment ops
        return [op for op in self.ops
                if not (isinstance(op, Comment) or isinstance(op, Whitespace))]

############################################################################
# Types
############################################################################

class IrTypes:
    """
    Container of all types, in registration order
    """
    def __init__(self):
        self.types = OrderedDict()

    def new_type(self, name):
        t = IrType(self, name)
        self._add(t)
        return t

    def new_struct(self, name):
        s = IrStruct(self, name)
        self._add(s)
        return s

    def _add(self, newtype):
        self.types[newtype.name] = newtype

class IrType:
    def __init__(self, types, name):
        self.types = types
        self.name = name
        self._ptr_type = None
        self._const_type = None

    def to_c(self):
        return self.name

    def __repr__(self):
        return '%s(name=%r)' % (self.__class__.__name__, self.name)

    def get_pointer(self):
        if self._ptr_type is None:
            self._ptr_type = IrPointerType(self.types, self)
            self.types._add(self._ptr_type)
        return self._ptr_type

    def get_const(self):
        if self._const_type is None:
            self._const_type = IrConstType(self.types, self)
            self.types._add(self._const_type)
        return self._const_type

class IrStruct(IrType):
    def __init__(self, types, name):
        IrType.__init__(self, types, name)
        self.fields = OrderedDict()

    def setup_fields(self, fieldinfo):
        for type_, name in fieldinfo:
            self.fields[name] = IrField(type_, name)

class IrPointerType(IrType):
    def __init__(self, types, other):
        IrType.__init__(self, types, '%s *' % other.name)
        self.other = other

    def __repr__(self):
        return '%s(other=%r)' % (self.__class__.__name__, self.other)

class IrConstType(IrType):
    def __init__(self, types, other):
        IrType.__init__(self, types, 'const %s' % other.name)
        self.other = other
        self._const_type = self

    def __repr__(self):
        return '%s(other=%r)' % (self.__class__.__name__, self.other)

class IrField:
    def __init__(self, type_, name):
        self.type_ = type_
        self.name = name

############################################################################
# Repository of globals
############################################################################

class IrGlobals:
    def __init__(self, types):
        self.types = types
        self.functions = []

    def new_function(self, returntype, fnname, params):
        fn = IrFunction(returntype, fnname, params)
        self.functions.append(fn)
        return fn

############################################################################
# Expressions
############################################################################

class Expression:
    def __init__(self, type_):
        assert isinstance(type_, IrType)
        self.type_ = type_

    def to_c(self):
        raise NotImplementedError

class Cast(Expression):
    # Generic LValue, containing no references needed by the optimizer
    def __init__(self, expr, newtype):
        Expression.__init__(self, newtype)
        assert isinstance(newtype, IrType)
        self.expr = expr
        self.newtype = newtype

    def __repr__(self):
        return 'Cast(expr=%r, newtype=%r)' % (self.code, self.newtype)

    def to_c(self):
        return '(%s)%s' % (self.newtype.to_c(), self.expr.to_c())

class LValue(Expression):
    # Generic LValue, containing no references needed by the optimizer
    def __init__(self, type_):
        Expression.__init__(self, type_)

class Param(LValue):
    def __init__(self, type_, name):
        assert isinstance(type_, IrType)
        LValue.__init__(self, type_)
        self.type_ = type_
        self.name = name
        self.ssacounter = 0
        self.ssanames = set()

    def __repr__(self):
        return ('Param(type_=%r, name=%r)'
                % (self.type_, self.name))

    def to_c(self):
        return self.name

class Local(LValue):
    def __init__(self, type_, name):
        assert isinstance(type_, IrType)
        LValue.__init__(self, type_)
        self.name = name
        self.ssacounter = 0
        self.ssanames = set()

    def __repr__(self):
        return ('Local(type_=%r, name=%r)'
                % (self.type_, self.name))

    def to_c(self):
        return self.name

class Global(LValue):
    def __init__(self, type_, name):
        assert isinstance(type_, IrType)
        LValue.__init__(self, type_)
        self.name = name

    def __repr__(self):
        return ('Global(type_=%r, name=%r)'
                % (self.type_, self.name))

    def to_c(self):
        return self.name

class SimpleLocal(Expression):
    # like a local, but doesn't participate in SSA; is assumed to
    # have trivial behavior
    def __init__(self, type_, name, is_argument):
        assert isinstance(type_, IrType)
        self.type_ = type_
        self.name = name
        self.is_argument = is_argument

    def __repr__(self):
        return ('SimpleLocal(type_=%r, name=%r, is_argument=%r)'
                % (self.type_, self.name, self.is_argument))

    def to_c(self):
        return self.name

class AddressOf(Expression):
    def __init__(self, lvalue):
        Expression.__init__(self, lvalue.type_.get_pointer())
        self.lvalue = lvalue

    def __repr__(self):
        return 'AddressOf(lvalue=%r)' % self.lvalue

    def to_c(self):
        return '&%s' % self.lvalue.to_c()

class Const(Expression):
    def __init__(self, type_, value):
        Expression.__init__(self, type_)
        self.value = value

    def __repr__(self):
        return 'Const(type_=%r, value=%r)' % (self.type_, self.value)

    def __hash__(self):
        return hash(self.value)

    def __eq__(self, other):
        if isinstance(other, Const):
            return self.value == other.value

    def to_c(self):
        return self.value

class InitialValue(Expression):
    def __init__(self, local):
        self.local = local

    def to_c(self):
        return 'InitialValue(%s)' % self.local

    def __repr__(self):
        return 'InitialValue(%r)' % self.local

class ConstInt(Const):
    def to_c(self):
        return '%i' % self.value

    def __repr__(self):
        return 'ConstInt(%r)' % self.value

    def __eq__(self, other):
        if isinstance(other, ConstInt):
            return self.value == other.value

    def __ne__(self, other):
        if isinstance(other, ConstInt):
            return self.value != other.value
        return True

    def __hash__(self):
        return hash(self.value)

class EnumValue(ConstInt):
    def __init__(self, value, name):
        self.value = value
        self.name = name

    def to_c(self):
        return self.name

class ConstString(Const):
    def __init__(self, value):
        self.value = value

    def to_c(self):
        return '"%s"' % self.value

    def __repr__(self):
        return 'ConstString(%r)' % self.value

class NULL(ConstInt):
    def __init__(self, type_):
        ConstInt.__init__(self, type_, 0)

    def __repr__(self):
        return 'NULL()'

    def to_c(self):
        return 'NULL'

class FieldDereference(Expression):
    def __init__(self, ptr, fieldname):
        self.ptr = ptr
        self.fieldname = fieldname

    def __repr__(self):
        return ('FieldDereference(ptr=%r, fieldname=%r)'
                % (self.ptr, self.fieldname))

    def to_c(self):
        return '%s->%s' % (self.ptr.to_c(), self.fieldname)

class ArrayLookup(Expression):
    def __init__(self, ptr, idx):
        self.ptr = ptr
        self.idx = idx

    def __repr__(self):
        return ('ArrayLookup(ptr=%r, idx=%r)'
                % (self.ptr, self.idx))

    def to_c(self):
        return '%s[%s]' % (self.ptr.to_c(), self.idx.to_c())

class UnaryExpr(Expression):
    def __init__(self, kind, expr):
        assert isinstance(expr, Expression)
        assert kind in ('!', ) # for now
        self.kind = kind
        self.expr = expr

    def to_c(self):
        return '%s%s' % (self.kind, self.expr.to_c())

    def __repr__(self):
        return 'UnaryExpr(kind=%r, expr=%r)' \
            % (self.kind, self.expr)

class BinaryExpr(Expression):
    def __init__(self, type_, lhs, expr, rhs):
        assert isinstance(type_, IrType)
        assert isinstance(lhs, Expression)
        assert expr in ('+', '-', '*', '/') # for now
        assert isinstance(rhs, Expression)
        self.type_ = type_
        self.lhs = lhs
        self.expr = expr
        self.rhs = rhs

    def to_c(self):
        return '%s %s %s' % (self.lhs.to_c(), self.expr, self.rhs.to_c())

    def __repr__(self):
        return 'BinaryExpr(type_=%r, lhs=%r, expr=%r, rhs=%r)' \
            % (self.type_, self.lhs, self.expr, self.rhs)

class Comparison(Expression):
    def __init__(self, lhs, expr, rhs):
        assert isinstance(lhs, Expression)
        assert expr in ('<', '<=', '==', '!=', '>=', '>')
        assert isinstance(rhs, Expression)
        self.lhs = lhs
        self.expr = expr
        self.rhs = rhs

    def to_c(self):
        return '%s %s %s' % (self.lhs.to_c(), self.expr, self.rhs.to_c())

    def __repr__(self):
        return 'Comparison(type_=%r, lhs=%r, expr=%r, rhs=%r)' \
            % (self.type_, self.lhs, self.expr, self.rhs)

class Call(Expression):
    def __init__(self, fn, args):
        assert isinstance(fn, IrFunction)
        assert isinstance(args, tuple)
        for arg in args:
            assert isinstance(arg, Expression)
        self.fn = fn
        self.args = args

    def __repr__(self):
        return 'Call(%r, %r)' % (self.fn, self.args)

    def to_c(self):
        return '%s(%s)' \
            % (self.fn.fnname, ', '.join(arg.to_c()
                                         for arg in self.args))

class DerefCall(Expression):
    def __init__(self, local, args):
        assert isinstance(local, Local)
        for arg in args:
            assert isinstance(arg, Expression)
        self.local = local
        self.args = args

    def __repr__(self):
        return 'DerefCall(%r, %r)' % (self.local, self.args)

    def to_c(self):
        return '(*%s)(%s)' \
            % (self.local.to_c(), ', '.join(arg.to_c() for arg in self.args))

############################################################################
# Operations
############################################################################

class IrOp(Op):
    def visit_exprs(self, visitor):
        self.visit_read_exprs(visitor)
        self.visit_write_exprs(visitor)

    def visit_read_exprs(self, visitor):
        raise NotImplementedError()

    def visit_write_exprs(self, visitor):
        raise NotImplementedError()

    def to_c(self):
        s = StringIO()
        w = CWriter(s)
        self.write(w)
        return s.getvalue()

class Phi(IrOp):
    # "args" is a dict, mapping from Edge to Expression
    def __init__(self, lhs, edge_to_expr):
        self.lhs = lhs
        self.edge_to_expr = edge_to_expr

    def __repr__(self):
        return ('Phi(lhs=%r, edge_to_expr=%s'
                % (self.lhs, self.edge_to_expr))

    def write(self, w):
        def item_to_c(edge, expr):
            return (expr.to_c(),
                    ('/* from %r -> %r */'
                     % (edge.src.addr, edge.dst.addr)))
        rhs = [item_to_c(edge, self.edge_to_expr[edge])
               for edge in self.edge_to_expr]
        lhs = self.lhs.to_c()
        if rhs:
            if len(rhs) > 1:
                header = '%s = PHI(' % lhs
                indent = ' ' * len(header)
                w.writeln('%s%s, %s' % (header, rhs[0][0], rhs[0][1]))
                for r in rhs[1:-2]:
                    w.writeln('%s%s, %s' % (indent, r[0], r[1]))
                w.writeln('%s%s); %s' % (indent, rhs[-1][0], rhs[-1][1]))
            else:
                w.writeln('%s = PHI(%s); %s' % (lhs, rhs[0][0], rhs[0][1]))
        else:
            w.writeln('%s = PHI();' % lhs)
        self.lhs.write_known_properties(w)

    def visit_read_exprs(self, visitor):
        for edge in self.edge_to_expr:
            self.edge_to_expr[edge] = visitor(self.edge_to_expr[edge])

    def visit_write_exprs(self, visitor):
        self.lhs = visitor(self.lhs)

class Nop(IrOp):
    # a no-op
    pass

class Whitespace(Nop):
    # for use in prettifying the generated C code
    def __init__(self, text):
        self.text = text

    def __repr__(self):
        return 'Whitespace(%r)' % self.text

    def write(self, w):
        w.writeln('%s' % self.text)

    def visit_read_exprs(self, visitor):
        pass

    def visit_write_exprs(self, visitor):
        pass

class Comment(Nop):
    def __init__(self, text):
        self.text = text

    def __repr__(self):
        return 'Comment(%r)' % self.text

    def write(self, w):
        if '\n' in self.text:
            w.writeln('/*')
            w.indent()
            for line in self.text.splitlines():
                w.writeln(line)
            w.outdent()
            w.writeln('*/')
        else:
            w.writeln('/* %s */' % self.text)

    def visit_read_exprs(self, visitor):
        pass

    def visit_write_exprs(self, visitor):
        pass

class Assignment(IrOp):
    def __init__(self, lhs, rhs):
        assert isinstance(lhs, Expression)
        assert isinstance(rhs, Expression)
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return 'Assignment(%r, %r)' % (self.lhs, self.rhs)

    def write(self, w):
        w.writeln('%s = %s;' % (self.lhs.to_c(), self.rhs.to_c()))

    def visit_read_exprs(self, visitor):
        self.rhs = visitor(self.rhs)

    def visit_write_exprs(self, visitor):
        self.lhs = visitor(self.lhs)

class Conditional(IrOp):
    def __init__(self, expr, true_block, false_block, likely=None):
        assert isinstance(expr, Expression)
        assert isinstance(true_block, IrBlock)
        assert isinstance(false_block, IrBlock)
        self.expr = expr
        self.true_block = true_block
        self.false_block = false_block
        self.likely = likely

    def __repr__(self):
        return ('Conditional(%r, %r, %r)'
                % (self.expr, self.true_block, self.false_block))

    def write(self, w):
        def write_dest_addr(addr):
            w.indent()
            if addr in w.inline_addrs:
                w.writeln('/* inlined block %s */' % addr)
                block = w.ircfg.addr_to_block[addr]
                for op in block.ops:
                    op.write(w)
            else:
                w.writeln('goto %s;' % addr)
            w.outdent()

        clause = self.expr.to_c(),
        if self.likely is True:
            clause = 'LIKELY(%s)' % clause
        if self.likely is False:
            clause = 'UNLIKELY(%s)' % clause
        w.writeln('if (%s) {' % clause)
        write_dest_addr(self.true_block.addr)
        w.writeln('} else {')
        write_dest_addr(self.false_block.addr)
        w.writeln('}')

    def visit_read_exprs(self, visitor):
        self.lhs = visitor(self.lhs)
        self.rhs = visitor(self.rhs)

    def visit_write_exprs(self, visitor):
        pass

class Eval(IrOp):
    def __init__(self, expr):
        self.expr = expr

    def __repr__(self):
        return 'Eval(%r)' % (self.expr)

    def write(self, w):
        w.writeln('(void)%s;' % self.expr.to_c())

class Jump(IrOp):
    def __init__(self, dest_block):
        assert isinstance(dest_block, IrBlock)
        self.dest_block = dest_block

    def __repr__(self):
        return 'Jump(%r)' % self.dest_block

    def __eq__(self, other):
        if isinstance(other, Jump):
            if self.dest_block == other.dest_block:
                return True

    def write(self, w):
        w.writeln('goto %s;' % self.dest_block.addr)

    def visit_read_exprs(self, visitor):
        pass

    def visit_write_exprs(self, visitor):
        pass

class Return(IrOp):
    def __init__(self, expr):
        self.expr = expr

    def __repr__(self):
        return 'Return(%r)' % self.expr

    def __eq__(self, other):
        if isinstance(other, Return):
            if self.expr == other.expr:
                return True

    def write(self, w):
        if self.expr:
            w.writeln('return %s;' % self.expr.to_c())
        else:
            w.writeln('return;')

    def visit_read_exprs(self, visitor):
        self.expr = visitor(self.expr)

    def visit_write_exprs(self, visitor):
        pass
