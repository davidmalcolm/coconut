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

from coconut.cfg import CFG, Block, Edge
from coconut.dot import dot_to_png

class TestCFG(CFG):
    def make_block(self, addr):
        return TestBlock(self, addr)

class TestBlock(Block):
    def to_dot_label(self):
        return self.addr

class CFGTests(unittest.TestCase):
    def make_test_cfg(self):
        # This is the example graph from Chapter 9 of "Engineering a
        # Compiler" 2nd Edition
        cfg = TestCFG()
        b0 = cfg.add_block_at(0)
        b1 = cfg.add_block_at(1)
        b2 = cfg.add_block_at(2)
        b3 = cfg.add_block_at(3)
        b4 = cfg.add_block_at(4)
        b5 = cfg.add_block_at(5)
        b6 = cfg.add_block_at(6)
        b7 = cfg.add_block_at(7)
        b8 = cfg.add_block_at(8)
        cfg.add_edge(Edge(b0, b1))
        cfg.add_edge(Edge(b1, b2))
        cfg.add_edge(Edge(b1, b5))
        cfg.add_edge(Edge(b2, b3))
        cfg.add_edge(Edge(b3, b4))
        cfg.add_edge(Edge(b3, b1))
        cfg.add_edge(Edge(b5, b6))
        cfg.add_edge(Edge(b5, b8))
        cfg.add_edge(Edge(b6, b7))
        cfg.add_edge(Edge(b8, b7))
        cfg.add_edge(Edge(b7, b3))
        return cfg

    def test_to_dot(self):
        cfg = self.make_test_cfg()
        dot = cfg.to_dot()
        # dot_to_png(dot, 'bytecode.png')

    def test_edges(self):
        cfg = self.make_test_cfg()
        b0 = cfg.blocks[0]
        b1 = cfg.blocks[1]
        self.assertEqual(len(b0.pred_edges), 0)
        self.assertEqual(len(b0.succ_edges), 1) # to b1
        self.assertEqual(len(b1.succ_edges), 2) # from b0 and b3

    def test_dominance(self):
        cfg = self.make_test_cfg()
        doms = cfg.calc_dominance()
        b0 = cfg.blocks[0]
        b1 = cfg.blocks[1]
        b2 = cfg.blocks[2]
        b3 = cfg.blocks[3]
        b4 = cfg.blocks[4]
        b5 = cfg.blocks[5]
        b6 = cfg.blocks[6]
        b7 = cfg.blocks[7]
        b8 = cfg.blocks[8]
        self.assertEqual(doms[b0], {b0})
        self.assertEqual(doms[b1], {b0, b1})
        self.assertEqual(doms[b2], {b0, b1, b2})
        self.assertEqual(doms[b3], {b0, b1, b3})
        self.assertEqual(doms[b4], {b0, b1, b3, b4})
        self.assertEqual(doms[b5], {b0, b1, b5})
        self.assertEqual(doms[b6], {b0, b1, b5, b6})
        self.assertEqual(doms[b7], {b0, b1, b5, b7})
        self.assertEqual(doms[b8], {b0, b1, b5, b8})

        strict_doms = cfg.calc_strict_doms(doms)
        self.assertEqual(strict_doms[b0], set())
        self.assertEqual(strict_doms[b1], {b0})
        self.assertEqual(strict_doms[b2], {b0, b1})
        self.assertEqual(strict_doms[b3], {b0, b1})
        self.assertEqual(strict_doms[b4], {b0, b1, b3})
        self.assertEqual(strict_doms[b5], {b0, b1})
        self.assertEqual(strict_doms[b6], {b0, b1, b5})
        self.assertEqual(strict_doms[b7], {b0, b1, b5})
        self.assertEqual(strict_doms[b8], {b0, b1, b5})

        idoms = cfg.calc_dominator_tree(doms)
        self.assertEqual(idoms[b0], None)
        self.assertEqual(idoms[b1], b0)
        self.assertEqual(idoms[b2], b1)
        self.assertEqual(idoms[b3], b1)
        self.assertEqual(idoms[b4], b3)
        self.assertEqual(idoms[b5], b1)
        self.assertEqual(idoms[b6], b5)
        self.assertEqual(idoms[b7], b5)
        self.assertEqual(idoms[b8], b5)

        dot = cfg.dominator_tree_to_dot(idoms)
        # dot_to_png(dot, 'dominator-tree.png')

        df = cfg.calc_dominance_frontiers(idoms)
        self.assertEqual(df[b0], set())
        self.assertEqual(df[b1], {b1})
        self.assertEqual(df[b2], {b3})
        self.assertEqual(df[b3], {b1})
        self.assertEqual(df[b4], set())
        self.assertEqual(df[b5], {b3})
        self.assertEqual(df[b6], {b7})
        self.assertEqual(df[b7], {b3})
        self.assertEqual(df[b8], {b7})

if __name__ == '__main__':
    unittest.main()
