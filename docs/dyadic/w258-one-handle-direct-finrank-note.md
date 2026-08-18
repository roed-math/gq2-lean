# W258: the direct one-handle finrank test

W258 equips the relevant finite elementary groups with local `ZMod 2` module structures and
defines the finranks of the four-coordinate transpose image and its target-augmented image.
Their cardinalities are exactly two raised to those dimensions.

A direct correction exists exactly when the two finranks agree; a dual detector exists exactly
when they differ.  Uniform finrank equality is equivalent to the W246 correction supply and
therefore implies `MpcPivShiftH 2 1`.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`.  No finrank equality
is asserted.  The remaining one-handle task is the conventional finite-linear statement that
the target row lies in the row span of the four coordinate families at every stage.
