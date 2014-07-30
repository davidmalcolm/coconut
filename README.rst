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

This low-level representation can then be sent via pygccjit into
libgccjit, converting it to a machine code specialization of that
function.

Caveats:
  * under development: lots of FIXMEs in the code
  * generators aren't yet supported

Actually running the built code is a work-in-progress.  The approach
I'm currently following involves a small patch to CPython, see
`cpython.patch` within the coconut source tree.  Approaches that don't
require patching CPython are probably preferable.

It's currently a toy: it only implements a subset of the bytecodes, and
there are plenty of optimizations it doesn't do e.g. type inference,
specialization for given types etc), so the performance isn't an
improvement (AIUI we gain a little from eliminating the stack push/pop
activity in favor of direct access to specific memory regions, but we
lose a little since we're thrashing the instruction cache with new code,
vs a single bytecode dispatch loop plus the relatively compact bytecode
format).

That said, it's already been useful for finding bugs and design issues
with libgccjit (and the Python bindings).

The implementation current attempts to faithfully respect the full
dynamic behaviors of the Python interpreter (even the somewhat
pathological ones e.g. where something you call can manipulate your
stack frame and change the types of variables from under you, or a
tp_dealloc hook could toggle whether of not profiling is enabled from
within a Py_DECREF).  Potentially we could relax that to get speed wins.
