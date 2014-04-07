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

import dis
import unittest

from coconut.compiler import Compiler
from coconut.dot import dot_to_png, dot_to_svg
from coconut.ir import Assignment, Call, Jump, Eval

def compile_(f):
    # Get the IrCFG for function f
    c = Compiler()
    c.compile(f.__code__)
    return c.ircfg

class CompilationTests(unittest.TestCase):
    # tests of simple compilation (without optimization)

    def assert_is_c(self, op, c):
        self.assertEqual(op.to_c(), c)

    def assert_is_assignment(self, op,
                             lhsname=None, rhsname=None):
        self.assertIsInstance(op, Assignment)
        if lhsname:
            self.assertEqual(op.lhs.name, lhsname)
        if rhsname:
            self.assertEqual(op.rhs.name, rhsname)

    def assert_is_assignment_between_locals(self, op, typename,
                                            lhsname, rhsname):
        self.assert_is_assignment(op, lhsname, rhsname)
        self.assertEqual(op.lhs.type_.name, typename)
        self.assertEqual(op.rhs.type_.name, typename)

    def assert_is_Py_INCREF_of_local(self, op, argname):
        self.assertIsInstance(op, Eval)
        call = op.expr
        self.assertIsInstance(call, Call)
        self.assertEqual(call.fn.fnname, 'Py_INCREF')
        self.assertEqual(len(call.args), 1)
        self.assertEqual(call.args[0].name, argname)

    def assert_is_jump(self, op, dstblock):
        self.assertIsInstance(op, Jump)
        self.assertEqual(op.dest_block, dstblock)

    def test_pass(self):
        def f():
            pass # implicit "return None"

        # We expect this bytecode:
        #   LOAD_CONST 0x0000 (i.e. None)
        #   RETURN_VALUE
        # in a single basic block

        # Verify normal operation:
        self.assertEqual(f(), None)

        # Compile to IrCFG
        ircfg = compile_(f)

        # We should now have an entry block,
        # plus at least one block per bytecode op
        self.assertEqual(len(ircfg.blocks), 5)
        self.assertEqual(len(ircfg.edges), 4)

        #print('ircfg.blocks: %r' % ircfg.blocks)
        #print('ircfg.addr_to_block: %r' % ircfg.addr_to_block)
        b_entry = ircfg.addr_to_block['entry']
        b_Py_EnterRecursiveCall_failed = ircfg.addr_to_block['Py_EnterRecursiveCall_failed']
        b_Py_EnterRecursiveCall_succeeded = ircfg.addr_to_block['Py_EnterRecursiveCall_succeeded']
        b_LOAD_CONST = ircfg.addr_to_block['bytecode_offset_0_LOAD_CONST']
        b_RETURN_VALUE = ircfg.addr_to_block['bytecode_offset_3_RETURN_VALUE']

        # Verify initial setup
        self.assertEqual(b_entry.addr, 'entry')
        self.assertEqual(len(b_entry.pred_edges), 0)
        self.assertEqual(len(b_entry.succ_edges), 2)
        self.assertMultiLineEqual(b_entry.real_ops_to_c(),
                                  ('tstate = PyThreadState_GET();\n'
                                   'if (UNLIKELY(Py_EnterRecursiveCall(""))) {\n'
                                   '    goto Py_EnterRecursiveCall_failed;\n'
                                   '} else {\n'
                                   '    goto Py_EnterRecursiveCall_succeeded;\n'
                                   '}\n'))

        ops = b_Py_EnterRecursiveCall_failed.get_real_ops()
        self.assert_is_c(ops[0], 'return NULL;\n')

        ops = b_Py_EnterRecursiveCall_succeeded.get_real_ops()
        self.assert_is_c(ops[0], 'tstate->frame = f;\n')
        self.assert_is_assignment(ops[1],
                                  lhsname='retval')
        self.assert_is_c(ops[1], 'retval = NULL;\n')
        # We pre-extract locals for each of the various consts,
        # so that LOAD_CONST can be a simple lookup, and various
        # optimizations become possible.
        self.assert_is_c(ops[2], 'co = f->f_code;\n')
        self.assert_is_c(ops[3], 'names = co->co_names;\n')
        self.assert_is_c(ops[4], 'consts = co->co_consts;\n')
        self.assert_is_c(ops[5], 'err = 0;\n')
        self.assert_is_c(ops[6], 'x = Py_None;\n')
        self.assert_is_c(ops[7], 'w = NULL;\n')
        self.assert_is_c(ops[8], 'const0_None = Py_None;\n')
        self.assert_is_jump(ops[9], b_LOAD_CONST)
        self.assert_is_c(ops[9], 'goto bytecode_offset_0_LOAD_CONST;\n')

        # Verify how a LOAD_CONST of None gets unrolled to IR ops,
        # with stack push/pop unrolled to manipulation of locals
        # "stack0", "stack1", etc:
        self.assertEqual(b_LOAD_CONST.addr, 'bytecode_offset_0_LOAD_CONST')
        self.assertEqual(len(b_LOAD_CONST.pred_edges), 1)
        self.assertEqual(len(b_LOAD_CONST.succ_edges), 1)
        ops = b_LOAD_CONST.get_real_ops()
        self.assertEqual(len(ops), 5)

        self.assert_is_c(ops[0], 'f->f_lasti = 0;\n')
        self.assert_is_c(ops[1],
                         'x = const0_None;\n')
        self.assert_is_Py_INCREF_of_local(
            ops[2],
            argname='x')

        self.assert_is_assignment_between_locals(
            ops[3],
            typename='PyObject *', lhsname='stack0', rhsname='x')

        self.assert_is_jump(
            ops[4],
            b_RETURN_VALUE)

        # Likewise for RETURN_VALUE
        self.assertEqual(b_RETURN_VALUE.addr, 'bytecode_offset_3_RETURN_VALUE')
        self.assertEqual(len(b_RETURN_VALUE.pred_edges), 1)
        self.assertEqual(len(b_RETURN_VALUE.succ_edges), 0)
        ops = b_RETURN_VALUE.get_real_ops()
        self.assertEqual(len(ops), 4)
        self.assert_is_c(ops[0], 'f->f_lasti = 3;\n')
        self.assert_is_assignment_between_locals(
            ops[1],
            typename='PyObject *', lhsname='retval', rhsname='stack0')
        self.assert_is_c(ops[2], '(void)Py_LeaveRecursiveCall();\n')
        self.assertEqual(ops[-1].to_c(),
                         'return retval;\n')

        csrc = ircfg.to_c()
        # The generated source ought to embed bytecode in comments:
        self.assertIn('offset 0: LOAD_CONST (None)', csrc)
        self.assertIn('offset 3: RETURN_VALUE', csrc)

    def test_hello_world(self):
        def f():
            return 'hello world'
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        # Ensure that constants get readable names:
        self.assertIn('const1_hello_world', csrc)

    def test_false(self):
        def f():
            return False
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('const1_False = (PyObject *)&_Py_FalseStruct;', csrc)

    def test_true(self):
        def f():
            return True
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('const1_True = (PyObject *)&_Py_TrueStruct;', csrc)

    def test_ROT_TWO(self):
        def f(a, b):
            a, b = b, a
            return a, b
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('ROT_TWO', csrc)
        self.assertIn('v = stack1;', csrc)
        self.assertIn('w = stack0;', csrc)
        self.assertIn('stack1 = w;', csrc)
        self.assertIn('stack0 = v;', csrc)

    def test_ROT_THREE(self):
        def f(a, b, c):
            a, b, c = c, b, a
            return (a, b, c)
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('ROT_THREE', csrc)
        self.assertIn('v = stack2;', csrc)
        self.assertIn('w = stack1;', csrc)
        self.assertIn('x = stack0;', csrc)
        self.assertIn('stack2 = w;', csrc)
        self.assertIn('stack1 = x;', csrc)
        self.assertIn('stack0 = v;', csrc)

    def test_UNARY_POSITIVE(self):
        def f(a):
            return + a
        def verify():
            self.assertEqual(f(3), 3)
            self.assertEqual(f(3.0), 3.0)
        verify()
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('UNARY_POSITIVE', csrc)
        self.assertIn('x = PyNumber_Positive(v);', csrc)

    def test_BINARY_SUBTRACT(self):
        def f(a, b):
            return a - b
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('BINARY_SUBTRACT', csrc)
        self.assertIn('x = PyNumber_Subtract(v, w);', csrc)

    def test_BINARY_POWER(self):
        def f(a, b):
            return a ** b
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('BINARY_POWER', csrc)
        self.assertIn('x = PyNumber_Power(v, w, Py_None);', csrc)

    def test_BINARY_MULTIPLY(self):
        def f(a, b):
            return a * b
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('BINARY_MULTIPLY', csrc)
        self.assertIn('x = PyNumber_Multiply(v, w);', csrc)

    def test_INPLACE_MULTIPLY(self):
        def f(a, b):
            a *= b
            return a
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('INPLACE_MULTIPLY', csrc)
        self.assertIn('x = PyNumber_InPlaceMultiply(v, w);', csrc)

    def test_INPLACE_POWER(self):
        def f(a, b):
            a **= b
            return a
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('INPLACE_POWER', csrc)
        self.assertIn('x = PyNumber_InPlacePower(v, w, Py_None);', csrc)

    def test_BUILD_MAP(self):
        def f(a, b):
            return {a: b}
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('BUILD_MAP', csrc)
        self.assertIn('x = _PyDict_NewPresized(1);', csrc)
        self.assertIn('STORE_MAP', csrc)
        self.assertIn('err = PyDict_SetItem(v, w, u);', csrc)

    def test_UNPACK_SEQUENCE(self):
        def f(seq):
            a, b, c = seq
            return 'a: %r, b: %r, c: %r' % (a, b, c)
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('UNPACK_SEQUENCE', csrc)

    def test_STORE_SUBSCR(self):
        def f(a, b, c):
            a[b] = c
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('STORE_SUBSCR', csrc)
        self.assertIn('err = PyObject_SetItem(v, w, u);', csrc)

    def test_BUILD_SLICE(self):
        def f():
            a = [1, 2, 3]
            return a[:]
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('BUILD_SLICE', csrc)

    def test_empty_loop(self):
        def f():
            for i in range(1000):
                pass
            return i
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('SETUP_LOOP', csrc)
        self.assertIn('FOR_ITER', csrc)
        self.assertIn('POP_BLOCK', csrc)

    def test_break(self):
        def f():
            for i in range(1000):
                break
            return i
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('BREAK_LOOP', csrc)

    def test_yield(self):
        def f():
            yield 42
        with self.assertRaises(NotImplementedError,
                               msg="Generators aren't yet supported"):
            ircfg = compile_(f)

def sample_bytecode_func(a, b, c):
    return 'a: %r, b: %r, c: %r' % (a, b, c)

def sample_bytecode_func_with_default(a, b, c=42):
    return 'a: %r, b: %r, c: %r' % (a, b, c)

# FIXME: should also test for co_kwonlyargcount > 0
# and each of CO_OPTIMIZED | CO_NEWLOCALS | CO_NOFREE

class TestCallFunction(unittest.TestCase):
    # "na0_nk0": 0 positional args, 0 keyword args
    def test_na0_nk0_METH_O_bad_args(self):
        def f():
            # bad call to "abs" which takes one arg: it's a PyCFunction with
            # METH_O, hence this should trigger an exception in that path:
            return abs()
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('CALL_FUNCTION', csrc)
        self.assertIn('impl_CALL_FUNCTION_na0_nk0', csrc)

    # "na1_nk0": 1 positional arg, 0 keyword args

    def test_na1_nk0_generic_callable(self):
        def f(a):
            # "str" is a type, so this call will go through the generic
            # do_call() path, using PyObject_Call:
            return str(a)
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('CALL_FUNCTION', csrc)
        self.assertIn('impl_CALL_FUNCTION_na1_nk0', csrc)

    def test_na1_nk0_PyCFUNCTION_with_METH_O(self):
        def f(a):
            # the "abs" builtin is a PyCFunction with METH_O
            # and hence the call goes through the METH_O path
            # within the generated impl_CALL_FUNCTION_
            return abs(a)
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('CALL_FUNCTION', csrc)
        self.assertIn('impl_CALL_FUNCTION_na1_nk0', csrc)

    # "na2_nk0": 2 positional args, 0 keyword args

    def test_na2_nk0_builtin(self):
        def f(a, b):
            # the "max" builtin is a PyCFunction (with
            # METH_VARARGS | METH_KEYWORDS).
            # This exercises the PyCFunction support within the
            # generated impl_CALL_FUNCTION_
            return max(a, b)
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('CALL_FUNCTION', csrc)
        self.assertIn('impl_CALL_FUNCTION_na2_nk0', csrc)

    # "na3_nk0": 3 positional args, 0 keyword args

    def test_calling_bytecode(self):
        def f(a, b, c):
            # this exercises the fast_function support within
            # the generated impl_CALL_FUNCTION_
            return sample_bytecode_func(a, b, c)
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('CALL_FUNCTION', csrc)
        self.assertIn('impl_CALL_FUNCTION_na3_nk0', csrc)

    def test_calling_bytecode_with_default(self):
        def f(a, b):
            # this exercises the non-NULL argdefs fast_function support
            # within the generated impl_CALL_FUNCTION_
            return sample_bytecode_func_with_default(a, b)
        self.assertEqual(sample_bytecode_func_with_default.__defaults__,
                         (42, ))
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('CALL_FUNCTION', csrc)
        self.assertIn('impl_CALL_FUNCTION_na2_nk0', csrc)

class TestBuiltins(unittest.TestCase):
    def test_locals(self):
        # Verify that locals() works
        def f(a, b):
            b *= 3
            c = 42
            return locals()

        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('CALL_FUNCTION', csrc)
        self.assertIn('impl_CALL_FUNCTION_na0_nk0', csrc)

class TestsOf_COMPARE_OP(unittest.TestCase):

    def test_eq(self):
        def f(a, b):
            return a == b
        ircfg = compile_(f)
        csrc = ircfg.to_c()
        self.assertIn('x = PyObject_RichCompare(v, w, PyCmp_EQ);', csrc)

if __name__ == '__main__':
    unittest.main()
