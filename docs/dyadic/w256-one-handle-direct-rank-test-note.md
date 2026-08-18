# W256: a finite rank test for the direct one-handle obstruction

W256 turns W255's augmented-kernel criterion into a literal finite nullity test.  The
augmented transpose kernel is contained in the four-coordinate transpose kernel, and both
groups are finite.  Consequently they are equal exactly when their cardinalities agree.

The direct correction exists exactly when those two kernel cardinalities agree.  A dual
detector exists exactly when they differ.  Uniform equality is equivalent to the W246 direct
correction supply and therefore implies `MpcPivShiftH 2 1`.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  No rank equality is
asserted: the remaining one-handle calculation is now the concrete finite task of showing
that adjoining target evaluation does not lower the nullity of the four-row transpose.
