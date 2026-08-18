# W255: the target-augmented transpose

W255 appends target evaluation to the four-row transpose from W254.  Its kernel always lies
inside the original transpose kernel.  A direct correction exists exactly when those two
kernels are equal; failure is exactly strict kernel containment.

Uniform augmented-kernel equality is equivalent to the W246 correction supply and therefore
implies `MpcPivShiftH 2 1`.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  The remaining
one-handle calculation is now a finite rank test: adjoining the target row must not shrink
the kernel of the four-coordinate transpose.
