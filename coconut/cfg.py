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
import os
from tempfile import NamedTemporaryFile

class CFG:
    '''Control Flow Graph'''
    __slots__ = ('blocks',      # list of Block
                 'edges',       # list of Edge
                 'addr_to_block', # dict, mapping from addr to Block
                 )
    def __init__(self):
        self.blocks = []
        self.edges = []
        self.addr_to_block = OrderedDict() # from addr to Block

    def add_block_at(self, addr):
        b = self.make_block(addr)
        self.blocks.append(b)
        self.addr_to_block[b.addr] = b
        return b

    def make_block(self, addr):
        raise NotImplementedError

    def add_edge(self, e):
        self.edges.append(e)
        e.src.succ_edges.add(e)
        e.dst.pred_edges.add(e)
        return e

    def to_dot(self):
        result = 'digraph {\n'
        #result += '  graph [labeljust="l"]\n'
        result += '  node [shape=record];\n'
        for addr in self.addr_to_block:
            block = self.addr_to_block[addr]
            result += '  block%s [label=<%s>];\n' % (addr, block.to_dot_label())
        for edge in self.edges:
            result += ('  block%s -> block%s [label="%s"];\n'
                       % (edge.src.addr, #edge.src.ops[-1].addr,
                          edge.dst.addr, #edge.dst.addr))
                          edge.effect.label if edge.effect else ''))
        result += '}'

        return result

    def view(self):
        dot = self.to_dot()
        with NamedTemporaryFile(suffix='.dot') as f:
            print(f)
            f.write(bytes(dot, 'utf-8'))
            os.system('xdot %s' % f.name)

    def calc_dominance(self):
        # Calculate the dominators for the blocks,
        # returning a dict, mapping from Block keys to set(block) values
        # Algorithm from Figure 9.1 (p479) of "Engineering a Compiler" (2nd ed)
        from functools import reduce
        all_blocks = frozenset(self.blocks)
        doms = {}
        doms[self.blocks[0]] = set([self.blocks[0]])
        for b in self.blocks[1:]:
            doms[b] = set(all_blocks)
        changed = True
        iterations = 0
        while changed:
            changed = False
            iterations += 1
            if 0:
                print('iteration %i' % iterations)
            for b in self.blocks[1:]:
                # FIXME: this is *slow* for large CFGs; is it O(N^2)
                # due to the b.get_predecessor_edges(), or the set(self.blocks)?
                preds = reduce(lambda x, y: x.intersection(y),
                               [doms[e.src]
                                for e in b.pred_edges],
                               all_blocks)
                temp = set([b]).union(preds)
                if temp != doms[b]:
                    doms[b] = temp
                    changed = True
        return doms

    def calc_strict_doms(self, doms=None):
        if doms is None:
            doms = self.calc_dominance()
        strict_doms = {}
        for b in self.blocks:
            strict_doms[b] = doms[b].copy()
            strict_doms[b].remove(b)
        return strict_doms

    def calc_dominator_tree(self, doms=None):
        # Generate a dict mapping from Block to Block, giving the
        # immediate dominator of each block, with None for Blocks that have
        # no immediate dominator.
        if doms is None:
            doms = self.calc_dominance()
        strict_doms = self.calc_strict_doms(doms)

        result = {}
        for block in self.blocks:
            idoms = strict_doms[block].copy()
            for other in strict_doms[block]:
                idoms -= strict_doms[other]
            # print('idoms: %r' % idoms)
            #assert len(idoms) in {0, 1}
            if idoms:
                result[block] = idoms.pop()
            else:
                result[block] = None
        return result

    def dominator_tree_to_dot(self, idoms):
        result = 'digraph {\n'
        result += '  node [shape=record];\n'
        for addr in self.addr_to_block:
            block = self.addr_to_block[addr]
            result += '  block%i [label=<%s>];\n' % (addr, block.to_dot_label())
        for b in self.blocks:
            if idoms[b]:
                result += ('  block%i -> block%i [label="%s"];\n'
                           % (idoms[b].addr,
                              b.addr,
                              ''))
        result += '}'

        return result


    def calc_dominance_frontiers(self, idoms=None):
        # Calculate the dominance frontier of every block,
        # returning a dict, mapping from Block keys to set(block) values
        # Algorithm from Figure 9.8 (p499) of "Engineering a Compiler" (2nd ed)
        if idoms is None:
            idoms = self.calc_dominator_tree()
        df = {}
        for b in self.blocks:
            df[b] = set()
        for b in self.blocks:
            preds = [e.src for e in b.pred_edges]
            if len(preds) > 1:
                for pred in preds:
                    runner = pred
                    while runner != idoms[b] and runner:
                        # print('runner: %r' % runner)
                        # print(df[runner])
                        df[runner] = df[runner].union({b})
                        runner = idoms[runner]
        return df

class Block:
    '''A basic block within a control flow graph
    Each CFG subclass will have a family of Block, Op and Effect subclasses

    Every block has a unique "address"; for now we'll assume this is always
    the offset from the start of the bytecode (index within co_code)
    '''

    __slots__ = ('cfg',   # the CFG
                 'addr',  # "address" of start of bytecode (index within co_code)
                 'ops',    # list of BytecodeOp
                 'pred_edges', # set of Edge
                 'succ_edges', # set of Edge
                 )

    def __init__(self, cfg, addr):
        self.cfg = cfg
        self.addr = addr
        self.ops = []
        self.pred_edges = set()
        self.succ_edges = set()

    def __repr__(self):
        return '%s(addr=%r)' % (self.__class__.__name__, self.addr)

class Edge:
    '''An edge linking two Blocks in a CFG'''
    __slots__ = ('src',    # Block
                 'dst',    # Block
                 'effect', # Effect, or None
                 )

    def __init__(self, src, dst, effect=None):
        self.src = src
        self.dst = dst
        self.effect = effect

    def __str__(self):
        return ('%s(src=%s, dst=%s, effect=%r)'
                % (self.__class__.__name__,
                   self.src.addr,
                   self.dst.addr,
                   self.effect))

    def __repr__(self):
        return ('%s(src=%r, dst=%r, effect=%r)'
                % (self.__class__.__name__,
                   self.src.addr,
                   self.dst.addr,
                   self.effect))

class Op:
    '''An operation within a basic block'''
    __slots__ = ('cfg',     # the CFG
                 'block',   # the Block
                 )

    def __init__(self, cfg, block):
        self.cfg = cfg
        self.block = block
