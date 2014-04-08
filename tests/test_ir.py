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

import ctypes
import unittest

from coconut.backend.libgccjit import GccJitBackend
from coconut.ir import IrCFG, IrTypes, IrGlobals, \
    Param, Call, BinaryExpr, ConstInt, Comparison

def to_gccjit(fns, types_, globals_):
    backend = GccJitBackend(types_, globals_)
    result = backend.compile(fns)
    return result

class IrTests(unittest.TestCase):
    def test_conditional(self):
        # Let's build equivalent of:
        #   int
        #   fn(int x)
        #   {
        #      if (x > 3)
        #          return x * 2;
        #      else
        #          return x - 5;
        #   }
        types = IrTypes()
        int_ = types.new_type('int')
        globals_ = IrGlobals(types)

        x = Param(int_, 'x')
        cfg = IrCFG(int_, 'fn', [x])

        b_entry = cfg.add_block('entry')
        b_on_true, b_on_false = b_entry.add_conditional(
            Comparison(x, '>', ConstInt(int_, 3)))

        b_on_true.add_return(BinaryExpr(int_, x, '*', ConstInt(int_, 2)))

        b_on_false.add_return(BinaryExpr(int_, x, '-', ConstInt(int_, 5)))

        self.assertEqual(len(cfg.blocks), 3)
        self.assertEqual(len(cfg.edges), 2)

        self.assertEqual(len(b_entry.pred_edges), 0)
        self.assertEqual(len(b_entry.succ_edges), 2)
        self.assertEqual(len(b_entry.ops), 1)
        self.assertEqual(b_entry.ops[0].to_c(),
                         'if (x > 3) {\n    goto true;\n} else {\n    goto false;\n}\n')

        self.assertEqual(len(b_on_true.pred_edges), 1)
        self.assertEqual(len(b_on_true.succ_edges), 0)

        self.assertEqual(len(b_on_false.pred_edges), 1)
        self.assertEqual(len(b_on_false.succ_edges), 0)

        csrc = cfg.to_c()
        self.assertIn('return x * 2;', csrc)
        self.assertIn('return x - 5;', csrc)

        result = to_gccjit([cfg], types, globals_)
        result_fn = result.get_code(cfg.fnname.encode())
        self.assertTrue(result_fn)
        int_int_func_type = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_int)
        code = int_int_func_type(result_fn)
        self.assertEqual(code(5), 10)
        self.assertEqual(code(4), 8)
        self.assertEqual(code(3), -2)
        self.assertEqual(code(0), -5)

    def test_calling_function(self):
        # Let's build equivalent of:
        #
        #   extern double sqrt(double x);
        #
        #   double
        #   fn(double x, double y)
        #   {
        #       return sqrt(x*x + y*y);
        #   }

        types = IrTypes()
        globals_ = IrGlobals(types)

        double_ = types.new_type('double')

        sqrt = globals_.new_function(double_, 'sqrt', [Param(double_, 'x')])

        x = Param(double_, 'x')
        y = Param(double_, 'y')
        fn = IrCFG(double_, 'fn', [x, y])

        b_entry = fn.add_block('entry')
        call = Call(
            sqrt,
            (BinaryExpr(
                double_,
                BinaryExpr(double_, x, '*', x),
                '+',
                BinaryExpr(double_, y, '*', y)),))
        self.assertEqual(call.to_c(), 'sqrt(x * x + y * y)')

        b_entry.add_return(call)

        result = to_gccjit([fn], types, globals_)
        result_fn = result.get_code(fn.fnname.encode())
        self.assertTrue(result_fn)
        double_double_double_func_type = ctypes.CFUNCTYPE(
            ctypes.c_double, ctypes.c_double, ctypes.c_double)
        code = double_double_double_func_type(result_fn)
        self.assertEqual(code(3, 4), 5)
        self.assertEqual(code(5, 12), 13)

    def test_helper_function(self):
        # Let's build equivalent of:
        #
        #   extern double sqrt(double x);
        #   static inline double square(double a) { return a * a; }
        #
        #   double
        #   hypot(double x, double y)
        #   {
        #       return sqrt(square(x) + square(y));
        #   }

        types = IrTypes()
        globals_ = IrGlobals(types)

        double_ = types.new_type('double')

        sqrt = globals_.new_function(double_, 'sqrt', [Param(double_, 'x')])

        a = Param(double_, 'a')
        square = IrCFG(double_, 'square', [a])
        b_entry = square.add_block('entry')
        b_entry.add_return(BinaryExpr(double_, a, '*', a))

        x = Param(double_, 'x')
        y = Param(double_, 'y')
        hypot = IrCFG(double_, 'hypot', [x, y])

        b_entry = hypot.add_block('entry')
        call = Call(
            sqrt,
            (BinaryExpr(
                double_,
                Call(square, (x,)),
                '+',
                Call(square, (y,))),))
        self.assertEqual(call.to_c(), 'sqrt(square(x) + square(y))')

        b_entry.add_return(call)

        result = to_gccjit([square, hypot], types, globals_)
        result_fn = result.get_code(hypot.fnname.encode())
        self.assertTrue(result_fn)
        double_double_double_func_type = ctypes.CFUNCTYPE(
            ctypes.c_double, ctypes.c_double, ctypes.c_double)
        code = double_double_double_func_type(result_fn)
        self.assertEqual(code(3, 4), 5)
        self.assertEqual(code(5, 12), 13)

if __name__ == '__main__':
    unittest.main()
