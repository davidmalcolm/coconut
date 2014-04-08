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

import gccjit

from coconut.ir import Comment, Assignment, Local, Call, FieldDereference, \
    IrType, IrPointerType, IrStruct, Conditional, Param, ConstInt, Return, \
    BinaryExpr, IrConstType, IrFunction, ConstString, Comparison, Eval, \
    Jump, Whitespace, Global, AddressOf, Dereference, IrArrayType, Cast

class GccJitBackend:
    def __init__(self, types, globals_):
        self.ctxt = gccjit.Context()
        if 0:
            self.ctxt.set_bool_option(
                gccjit.BoolOption.DUMP_INITIAL_GIMPLE, True)
            self.ctxt.set_bool_option(
                gccjit.BoolOption.DUMP_EVERYTHING, True)
            self.ctxt.set_bool_option(
                gccjit.BoolOption.KEEP_INTERMEDIATES, True)

        self.types = types
        self.globals_ = globals_

        self.functions = {}

        # Create types
        self.typedict = {}

        # First pass: create types, leaving structs opaque
        for irtype in types.types.values():
            self.typedict[irtype] = self._make_type(irtype)

        # Second pass: fill in fields of any structs
        self.fielddict = {}
        for irtype in types.types.values():
            if isinstance(irtype, IrStruct):
                gfields = []
                for irfield in irtype.fields.values():
                    gfield = self.ctxt.new_field(self.typedict[irfield.type_],
                                                 irfield.name.encode())
                    gfields.append(gfield)
                    self.fielddict[irfield] = gfield
                self.typedict[irtype].set_fields(gfields)

        # Now create global functions:
        self.fndict = {}
        for fn in self.globals_.functions:
            if isinstance(fn, IrFunction):
                params = []
                for param in fn.params:
                    assert isinstance(param, Param)
                    params.append(self.ctxt.new_param(self.typedict[param.type_],
                                                      param.name.encode()))
                self.fndict[fn] = self.ctxt.new_function(
                    gccjit.FunctionKind.IMPORTED,
                    self.typedict[fn.returntype],
                    fn.fnname.encode(),
                    params)

    def _make_type(self, irtype):
        if 0:
            print('_make_type: %r' % irtype)
        if isinstance(irtype, IrPointerType):
            return self.typedict[irtype.other].get_pointer()
        elif isinstance(irtype, IrConstType):
            return self.typedict[irtype.other].get_const()
        elif isinstance(irtype, IrStruct):
            return self.ctxt.new_struct(irtype.name.encode())
        elif isinstance(irtype, IrArrayType):
            return self.ctxt.new_array_type(
                self.typedict[irtype.element_type],
                irtype.num_elements)
        elif isinstance(irtype, IrType):
            if irtype.name == 'void':
                return self.ctxt.get_type(gccjit.TypeKind.VOID)
            if irtype.name == 'bool':
                return self.ctxt.get_type(gccjit.TypeKind.BOOL)
            if irtype.name == 'char':
                return self.ctxt.get_type(gccjit.TypeKind.CHAR)
            if irtype.name == 'int':
                return self.ctxt.get_type(gccjit.TypeKind.INT)
            if irtype.name == 'Py_ssize_t':
                return self.ctxt.get_type(gccjit.TypeKind.INT) # FIXME
            if irtype.name == 'double':
                return self.ctxt.get_type(gccjit.TypeKind.DOUBLE)

        raise NotImplementedError(irtype)

    def compile(self, irfns):
        self.params = {}
        self.locals = {}
        for irfn in irfns:
            self.fndict[irfn] = self.create_fn_decl(irfn)
        for irfn in irfns:
            self.create_fn_body(irfn)
        return self.ctxt.compile()

    def create_fn_decl(self, irfn):
        params = []
        for irparam in irfn.params:
            gparam = self.ctxt.new_param(self.typedict[irparam.type_],
                                         irparam.name.encode())
            params.append(gparam)
            self.params[irparam] = gparam

        return self.ctxt.new_function(gccjit.FunctionKind.EXPORTED,
                                      self.typedict[irfn.returntype],
                                      irfn.fnname.encode(),
                                      params)
    def create_fn_body(self, ircfg):
        out_fn = self.fndict[ircfg]

        for irlocal in ircfg.locals:
            self.locals[irlocal] = out_fn.new_local(self.typedict[irlocal.type_],
                                                    irlocal.name.encode())

        # Create all blocks:
        blockdict = {}
        for irblock in ircfg.blocks:
            blockdict[irblock] = out_fn.new_block(irblock.addr.encode())

        # Now populate them:
        for irblock in ircfg.blocks:
            gblock = blockdict[irblock]
            for op in irblock.ops:
                if isinstance(op, (Comment, Whitespace)):
                    gblock.add_comment(op.text.encode())
                elif isinstance(op, Assignment):
                    gblock.add_assignment(self.make_lvalue(op.lhs),
                                          self.make_rvalue(op.rhs))
                elif isinstance(op, Conditional):
                    gblock.end_with_conditional(
                        self.make_rvalue(op.expr),
                        blockdict[op.true_block],
                        blockdict[op.false_block])
                elif isinstance(op, Eval):
                    gblock.add_eval(self.make_rvalue(op.expr))
                elif isinstance(op, Jump):
                    gblock.end_with_jump(blockdict[op.dest_block])
                elif isinstance(op, Return):
                    if op.expr is None:
                        gblock.end_with_void_return()
                    else:
                        gblock.end_with_return(self.make_rvalue(op.expr))
                else:
                    raise NotImplementedError(op)

    def make_lvalue(self, expr):
        if isinstance(expr, Local):
            return self.locals[expr]
        elif isinstance(expr, Dereference):
            return self.make_rvalue(expr.ptr).dereference()
        elif isinstance(expr, FieldDereference):
            rvalue = self.make_rvalue(expr.ptr)
            assert isinstance(expr.ptr.type_, IrPointerType)
            irfield = expr.ptr.type_.other.fields[expr.field.name]
            gfield = self.fielddict[irfield]
            return self.make_rvalue(expr.ptr).dereference_field(gfield)
        elif isinstance(expr, Global):
            return self.ctxt.new_global(self.typedict[expr.type_],
                                        expr.name.encode())
        raise NotImplementedError(expr)

    def make_rvalue(self, expr):
        if isinstance(expr, Local):
            return self.locals[expr]
        elif isinstance(expr, Dereference):
            return self.make_rvalue(expr.ptr).dereference()
        elif isinstance(expr, Param):
            return self.params[expr]
        elif isinstance(expr, Call):
            func = self.fndict[expr.fn]
            args = [self.make_rvalue(arg)
                    for arg in expr.args]
            return self.ctxt.new_call(func, args)
        elif isinstance(expr, Cast):
            return self.ctxt.new_cast(self.make_rvalue(expr.expr),
                                      self.typedict[expr.newtype])
        elif isinstance(expr, AddressOf):
            return self.make_lvalue(expr.lvalue).get_address()
        elif isinstance(expr, BinaryExpr):
            opdict = {'+':gccjit.BinaryOp.PLUS,
                      '-':gccjit.BinaryOp.MINUS,
                      '*':gccjit.BinaryOp.MULT,
                      '/':gccjit.BinaryOp.DIVIDE}
            return self.ctxt.new_binary_op(opdict[expr.expr],
                                           self.typedict[expr.type_],
                                           self.make_rvalue(expr.lhs),
                                           self.make_rvalue(expr.rhs))
        elif isinstance(expr, Comparison):
            opdict = {'<':gccjit.Comparison.LT,
                      '<=':gccjit.Comparison.LE,
                      '==':gccjit.Comparison.EQ,
                      '!=':gccjit.Comparison.NE,
                      '>=':gccjit.Comparison.GE,
                      '>':gccjit.Comparison.GT}
            return self.ctxt.new_comparison(
                opdict[expr.expr],
                self.make_rvalue(expr.lhs),
                self.make_rvalue(expr.rhs))
        elif isinstance(expr, ConstInt):
            if isinstance(expr.type_, IrPointerType):
                return self.ctxt.new_rvalue_from_ptr(self.typedict[expr.type_],
                                                     expr.value)
            return self.ctxt.new_rvalue_from_int(self.typedict[expr.type_],
                                                 expr.value)
        elif isinstance(expr, ConstString):
            return self.ctxt.new_string_literal(expr.value.encode())
        elif isinstance(expr, FieldDereference):
            rvalue = self.make_rvalue(expr.ptr)
            assert isinstance(expr.ptr.type_, IrPointerType)
            irfield = expr.ptr.type_.other.fields[expr.field.name]
            gfield = self.fielddict[irfield]
            return self.make_rvalue(expr.ptr).dereference_field(gfield)
        elif isinstance(expr, Global):
            return self.ctxt.new_global(self.typedict[expr.type_],
                                        expr.name.encode())
        raise NotImplementedError(expr)

    def make_function(self, fnname):
        if fnname in self.functions:
            return self.functions[fnname]
        raise NotImplementedError(fnname)
