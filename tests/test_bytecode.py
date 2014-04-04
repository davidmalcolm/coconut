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

from coconut.bytecode import BytecodeCFG, \
    LOAD_CONST, RETURN_VALUE, BINARY_MULTIPLY, LOAD_FAST, POP_JUMP_IF_FALSE

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

        op3 = cfg.addr_to_op[3]
        self.assertIsInstance(op3, POP_JUMP_IF_FALSE)
        self.assertEqual(op3.vheight, 1)

        op6 = cfg.addr_to_op[6]
        self.assertIsInstance(op6, LOAD_FAST)
        self.assertEqual(op6.vheight, 0)

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

if __name__ == '__main__':
    unittest.main()
