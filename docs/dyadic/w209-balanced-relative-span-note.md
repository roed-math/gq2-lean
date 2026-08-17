# W209: the relative finite span

Every W208 correction coordinate vanishes under handle-forgetting. W209 proves by relator
naturality that its finite shift therefore lies in

`zLayer (DM 2 1) k intersect ker(forgetLevelMap_(k+1))`.

This subgroup is `oneHandleRelativeZLayer k`, definitionally the W206 relative lambda image
at `(k,k+1)`. The finite shift is corestricted to it as
`oneHandleBalancedCoreRelativeShiftHom`.

The current target lies there as well. The balanced marking forgets to the compact marking
obtained from `Psi0`, with both handle rows trivial, so its full relator maps to the compact
defining relation and is one. `oneHandleBalancedCoreRelativeTarget` records the resulting
relative central-layer class.

`target_mem_relativeRange_iff_target_mem_range` proves that this corestriction does not alter
the exact W208 target-specific claim. `OneHandleBalancedCoreRelativeSurjectiveSupply` is
separately exposed as a stronger sufficient finite spanning statement; it is not asserted to
be equivalent to the target-specific supply.

The next mathematical comparison is therefore precise: determine whether the existing raw
or augmented coordinate-span engines remain onto after restricting all four core coordinates
to the relative layer and the `C` coordinate to its exact character-neutral image.

Every declaration has exactly the standard axiom set `propext`, `Classical.choice`, and
`Quot.sound`.
