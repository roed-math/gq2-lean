# W211: the finite balanced-coordinate cokernel

W211 compares the exact constrained coordinate span from W210 with the established
unrestricted raw shift span. Every constrained coordinate shift is an unrestricted raw
shift, so the W210 span maps into the raw span. The converse is not available: a raw
correction forgets the separate handle-kernel conditions on the `A`, `B`, and `D` rows and
the character-neutral condition on the `C` row.

The relative central layer is finite and commutative. The quotient
`OneHandleBalancedCoreCoordinateCokernel` therefore packages the exact remaining finite
obstruction. For each balanced point and finite stage,
`oneHandleBalancedCoreCoordinateObstruction` is the class of the current relator target in
that cokernel. Its vanishing is equivalent to membership in the four-coordinate span.
Uniform vanishing is consequently equivalent to W210's
`OneHandleBalancedCoreCoordinateSpanSupply` and implies `MpcPivShiftH 2 1`.

This locates the remaining gap without strengthening the available raw theorem: raw or
augmented-raw target coverage is necessary context, but does not recover constrained
representatives and hence is not sufficient for the balanced one-handle target.

Every public declaration has exactly the standard axiom set `propext`, `Classical.choice`,
and `Quot.sound`.
