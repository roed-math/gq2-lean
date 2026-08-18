# W254: the finite transpose boundary

W254 assembles the four W253 elementary-dual equations into one finite transpose
homomorphism.  Its kernel is exactly the space of ambient functionals annihilating all four
coordinate rows.

The direct correction exists exactly when every functional in that kernel kills the target.
Failure is equivalent to one kernel functional detecting the target.  Uniform target
vanishing implies `MpcPivShiftH 2 1` through the existing direct successor chain.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  The remaining
mathematics is now one finite transpose-kernel calculation, not a compactness, topology, or
generation problem.
