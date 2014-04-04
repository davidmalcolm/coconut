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

import unittest

from coconut.bytecode import BytecodeCFG, BStackEntry, \
    LOAD_CONST, RETURN_VALUE, BINARY_MULTIPLY, LOAD_FAST, POP_JUMP_IF_FALSE, \
    SETUP_EXCEPT, SETUP_FINALLY

class BytecodeTests(unittest.TestCase):
    # tests of bytecode extraction
    def test_empty(self):
        def fn():
            pass
        # We expect this bytecode:
        #   LOAD_CONST 0x0000 (i.e. None)
        #   RETURN_VALUE
        # in a single basic block

        co = fn.__code__
        cfg = BytecodeCFG(co)
        self.assertEqual(len(cfg.blocks), 1)
        self.assertEqual(len(cfg.edges), 0)
        self.assertEqual(len(cfg.bytecode), 4)

        op0 = cfg.addr_to_op[0]
        self.assertIsInstance(op0, LOAD_CONST)
        self.assertEqual(op0.addr, 0)
        self.assertEqual(op0.bstack, [])
        self.assertEqual(op0.vheight, 0)

        op3 = cfg.addr_to_op[3]
        self.assertIsInstance(op3, RETURN_VALUE)
        self.assertEqual(op3.addr, 3)
        self.assertEqual(op3.bstack, [])
        self.assertEqual(op3.vheight, 1)

    def test_multiply(self):
        def fn(a, b, c):
            return a * b * c
        # We expect this bytecode:
        #     0 LOAD_FAST                0 (a)
        #     3 LOAD_FAST                1 (b)
        #     6 BINARY_MULTIPLY
        #     7 LOAD_FAST                2 (c)
        #    10 BINARY_MULTIPLY
        #    11 RETURN_VALUE
        co = fn.__code__
        cfg = BytecodeCFG(co)
        self.assertEqual(len(cfg.blocks), 1)
        self.assertEqual(len(cfg.edges), 0)
        self.assertEqual(len(cfg.bytecode), 12)
        op0 = cfg.addr_to_op[0]
        self.assertIsInstance(op0, LOAD_FAST)
        self.assertEqual(op0.vheight, 0)

        op3 = cfg.addr_to_op[3]
        self.assertIsInstance(op3, LOAD_FAST)
        self.assertEqual(op3.vheight, 1)

        op6 = cfg.addr_to_op[6]
        self.assertIsInstance(op6, BINARY_MULTIPLY)
        self.assertEqual(op6.vheight, 2)

        op7 = cfg.addr_to_op[7]
        self.assertIsInstance(op7, LOAD_FAST)
        self.assertEqual(op7.vheight, 1)

        op10 = cfg.addr_to_op[10]
        self.assertIsInstance(op10, BINARY_MULTIPLY)
        self.assertEqual(op10.vheight, 2)

        op11 = cfg.addr_to_op[11]
        self.assertIsInstance(op11, RETURN_VALUE)
        self.assertEqual(op11.vheight, 1)

    def test_conditional(self):
        def fn(a, b, c):
            if a:
                return b
            else:
                return c
        # We expect this bytecode:
        # 48           0 LOAD_FAST                0 (a)
        #              3 POP_JUMP_IF_FALSE       10
        #
        # 49           6 LOAD_FAST                1 (b)
        #              9 RETURN_VALUE
        #
        # 51     >>   10 LOAD_FAST                2 (c)
        #             13 RETURN_VALUE
        #             14 LOAD_CONST               0 (None)
        #             17 RETURN_VALUE
        co = fn.__code__
        cfg = BytecodeCFG(co)
        self.assertEqual(len(cfg.blocks), 3)
        self.assertEqual(len(cfg.edges), 2)
        self.assertEqual(len(cfg.bytecode), 18)

        op0 = cfg.addr_to_op[0]
        self.assertIsInstance(op0, LOAD_FAST)
        self.assertEqual(op0.vheight, 0)
        self.assertIn(op0.addr, cfg.linestarts)
        self.assertEqual(op0.get_source_line(),
                         "            if a:\n")

        op3 = cfg.addr_to_op[3]
        self.assertIsInstance(op3, POP_JUMP_IF_FALSE)
        self.assertEqual(op3.vheight, 1)
        self.assertNotIn(op3.addr, cfg.linestarts)

        op6 = cfg.addr_to_op[6]
        self.assertIsInstance(op6, LOAD_FAST)
        self.assertEqual(op6.vheight, 0)
        self.assertIn(op6.addr, cfg.linestarts)
        self.assertEqual(op6.get_source_line(),
                         "                return b\n")

        op9 = cfg.addr_to_op[9]
        self.assertIsInstance(op9, RETURN_VALUE)
        self.assertEqual(op9.vheight, 1)

        op10 = cfg.addr_to_op[10]
        self.assertIsInstance(op10, LOAD_FAST)
        self.assertEqual(op10.vheight, 0)

        op13 = cfg.addr_to_op[13]
        self.assertIsInstance(op13, RETURN_VALUE)
        self.assertEqual(op13.vheight, 1)

        # The final two ops in the bytecode aren't reachable:
        op14 = cfg.addr_to_op[14]
        self.assertIsInstance(op14, LOAD_CONST)
        op17 = cfg.addr_to_op[17]
        self.assertIsInstance(op17, RETURN_VALUE)

        e0 = cfg.edges[0]
        self.assertEqual(e0.src.addr, 0)
        self.assertEqual(e0.dst.addr, 10)

        e1 = cfg.edges[1]
        self.assertEqual(e1.src.addr, 0)
        self.assertEqual(e1.dst.addr, 6)

    def test_block_stack(self):
        def fn(x):
            try:
                try:
                    return x
                finally:
                    x += [1]
            finally:
                x += [2]

        self.assertEqual(fn([]), [1, 2])

        # We expect this bytecode:
        # 154           0 SETUP_FINALLY           29 (to 32)
        # 155           3 SETUP_FINALLY            8 (to 14)
        # 156           6 LOAD_FAST                0 (x)
        #               9 RETURN_VALUE
        #              10 POP_BLOCK
        #              11 LOAD_CONST               0 (None)
        # 158     >>   14 LOAD_FAST                0 (x)
        #              17 LOAD_CONST               1 (1)
        #              20 BUILD_LIST               1
        #              23 INPLACE_ADD
        #              24 STORE_FAST               0 (x)
        #              27 END_FINALLY
        #              28 POP_BLOCK
        #              29 LOAD_CONST               0 (None)
        # 160     >>   32 LOAD_FAST                0 (x)
        #              35 LOAD_CONST               2 (2)
        #              38 BUILD_LIST               1
        #              41 INPLACE_ADD
        #              42 STORE_FAST               0 (x)
        #              45 END_FINALLY
        # These last ops are unreachable:
        #              46 LOAD_CONST               0 (None)
        #              49 RETURN_VALUE

        co = fn.__code__
        cfg = BytecodeCFG(co)

        self.assertEqual(len(cfg.blocks), 5)
        self.assertEqual(len(cfg.edges), 4)
        self.assertEqual(len(cfg.bytecode), 50)

        op0 = cfg.addr_to_op[0]
        self.assertIsInstance(op0, SETUP_FINALLY)
        self.assertEqual(op0.vheight, 0)
        self.assertEqual(op0.bstack, [])

        op3 = cfg.addr_to_op[3]
        self.assertIsInstance(op3, SETUP_FINALLY)
        self.assertEqual(op3.vheight, 0)
        self.assertEqual(len(op3.bstack), 1)

        # Verify that the SETUP_EXCEPT at 0 has set up a block stack entry
        # at 3 (for handling a "PyFrame_Block*"):
        self.assertEqual(len(op3.bstack), 1)
        bse_at_3 = op3.bstack[0]
        self.assertIsInstance(bse_at_3, BStackEntry)
        self.assertEqual(str(bse_at_3), 'SETUP_FINALLY at 0 (to 32)')
        self.assertEqual(repr(bse_at_3), 'BStackEntry(op=0)')
        self.assertEqual(bse_at_3.op, op0)
        self.assertEqual(bse_at_3.get_vstack_height(), 0)
        self.assertEqual(bse_at_3.get_b_handler(), 32)

        # Likewise, check that the SETUP_EXCEPT at 3 has pushed another block
        # stack entry at 6:
        op6 = cfg.addr_to_op[6]
        self.assertIsInstance(op6, LOAD_FAST)
        self.assertEqual(len(op6.bstack), 2)
        self.assertEqual(op6.bstack[0], op3.bstack[0])
        bse_at_6 = op6.bstack[1]
        self.assertIsInstance(bse_at_6, BStackEntry)
        self.assertEqual(str(bse_at_6), 'SETUP_FINALLY at 3 (to 14)')
        self.assertEqual(repr(bse_at_6), 'BStackEntry(op=3)')
        self.assertEqual(bse_at_6.op, op3)
        self.assertEqual(bse_at_6.get_vstack_height(), 0)
        self.assertEqual(bse_at_6.get_b_handler(), 14)

    def test_exceptions(self):
        def fn(e):
            try:
                2 / 0
            except ZeroDivisionError(exc):
                print(exc)
        # We expect this bytecode:
        # 153           0 SETUP_EXCEPT            12 (to 15)
        # 154           3 LOAD_CONST               1 (2)
        #               6 LOAD_CONST               2 (0)
        #               9 BINARY_TRUE_DIVIDE
        #              10 POP_TOP
        #              11 POP_BLOCK
        #              12 JUMP_FORWARD            34 (to 49)
        # 155     >>   15 DUP_TOP
        #              16 LOAD_GLOBAL              0 (ZeroDivisionError)
        #              19 LOAD_GLOBAL              1 (exc)
        #              22 CALL_FUNCTION            1 (1 positional, 0 keyword pair)
        #              25 COMPARE_OP              10 (exception match)
        #              28 POP_JUMP_IF_FALSE       48
        #              31 POP_TOP
        #              32 POP_TOP
        #              33 POP_TOP
        # 156          34 LOAD_GLOBAL              2 (print)
        #              37 LOAD_GLOBAL              1 (exc)
        #              40 CALL_FUNCTION            1 (1 positional, 0 keyword pair)
        #              43 POP_TOP
        #              44 POP_EXCEPT
        #              45 JUMP_FORWARD             1 (to 49)
        #         >>   48 END_FINALLY
        #         >>   49 LOAD_CONST               0 (None)
        #              52 RETURN_VALUE
        co = fn.__code__
        cfg = BytecodeCFG(co)
        self.assertEqual(len(cfg.blocks), 6)
        self.assertEqual(len(cfg.edges), 6)
        self.assertEqual(len(cfg.bytecode), 53)

        op0 = cfg.addr_to_op[0]
        self.assertIsInstance(op0, SETUP_EXCEPT)
        self.assertEqual(op0.vheight, 0)
        self.assertEqual(op0.bstack, [])

        op3 = cfg.addr_to_op[3]
        self.assertIsInstance(op3, LOAD_CONST)
        self.assertEqual(op3.vheight, 0)
        self.assertEqual(len(op3.bstack), 1)
        # Verify that the SETUP_EXCEPT has set up a block stack entry
        # (for handling a "PyFrame_Block*"):
        bse = op3.bstack[0]
        self.assertIsInstance(bse, BStackEntry)
        self.assertEqual(str(bse), 'SETUP_EXCEPT at 0 (to 15)')
        self.assertEqual(repr(bse), 'BStackEntry(op=0)')
        self.assertEqual(bse.op, op0)
        self.assertEqual(bse.get_vstack_height(), 0)
        self.assertEqual(bse.get_b_handler(), 15)

if __name__ == '__main__':
    unittest.main()
