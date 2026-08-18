# W247: the direct one-handle finite span

W247 turns the W246 correction equation into an exact finite range problem.  At depth
`k - 1`, the four core correction coordinates are represented by their finite quotient
images.  Every coordinate is killed by `chiM`; the `C` coordinate is additionally killed by
all continuous Z2-valued characters.  Both handle coordinates remain one.

These four finite subgroups form `OneHandleDirectLevelCorrection k`.  The generic even
crossed-derivation construction makes the resulting stage shift a homomorphism into the
central layer `zLayer (DM 2 1) k`.  Exact representatives prove that a W246 group-level
correction exists if and only if the inverse current relator lies in this homomorphism's
range.

Consequently `OneHandleDirectFiniteRangeSupply` is equivalent to the W246 correction supply
and implies `MpcPivShiftH 2 1`.  The remaining mathematical task is now finite spanning of
one explicitly defined four-coordinate map; generation, handles, orientation, and the pivot
row no longer occur in the successor equation.
