Experiments towards a method JIT for CPython 3.*

To run:

   PYTHONPATH=. python3 setup.py test

CPython bytecode for a function is parsed and converted to a
coconut.bytecode.BytecodeCFG, where the blocks consist of those
seen e.g. within Python's peephole.c and the ops are bytecodes.
These ops "know" what their stack depths are.

This is then compiled (by coconut.compiler) into a lower-level
representation, coconut.ir.IrCFG.
The higher-level ops are exploded into one or more blocks per bytecode
op, along with various other blocks for e.g. exception handling:
even a simple BytecodeCFG typically becomes a fairly complicate
IrCFG.

It may be possible to optimize the IrCFG (e.g. type inference,
specialization, etc).

This low-level representation can be turned into C, or, I hope,
injected into a JIT library.

Caveats:
  * under development: lots of FIXMEs in the code
  * generators aren't yet supported

Actually running the built code is a work-in-progress.  The approach
I'm currently following involves a small patch to CPython, see
`cpython.patch` within the coconut source tree.  Approaches that don't
require patching CPython are probably preferable.
