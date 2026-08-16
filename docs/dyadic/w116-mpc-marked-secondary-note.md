# W116: explicit secondary defect for the marked Mpc ladder

The marked successor calculation is now carried one full layer beyond the affine cost formula.

For a depth-`j` marked move, `mpcMkAdvanceHall` records the exact eight Hall factors created at
the next layer.  They consist of the head-tail square error, three head/B commutator errors, the
pivot fourth-power error, and three pivot/D commutator errors.  The module proves that this word
lies in `lambda_(j+2)`.

`mpcMkDefectTop_advance_eq_liftResidual_mul_hall` then decomposes the advanced secondary defect
as the old kill equation lifted one layer times the Hall top class.  All seven public
declarations compile with exactly `propext`, `Classical.choice`, and `Quot.sound`.

This removes the previously opaque affine remainder.  Uniform propagation is now equivalent to
showing this explicit secondary class lies in the frozen successor marked-cost range, or
equivalently that its five obstruction coordinates vanish.
