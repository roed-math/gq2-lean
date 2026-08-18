# W257: the image-rank form of the direct one-handle test

W257 applies finite rank-nullity to the common source of the coordinate transpose and its
target-augmented version.  Equality of their kernel cardinalities is equivalent to equality of
their image cardinalities.

Therefore a direct correction exists exactly when adjoining target evaluation does not enlarge
the transpose image.  A dual detector exists exactly when the image cardinalities differ.
Uniform image-rank equality is equivalent to the W246 correction supply and hence implies
`MpcPivShiftH 2 1`.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  The remaining
one-handle task is now an ordinary finite-rank computation for a five-row map versus its
four-row projection; no rank equality is asserted here.
