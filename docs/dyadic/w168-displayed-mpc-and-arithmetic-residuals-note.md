# W168: displayed Mpc closure and exact arithmetic residuals

Wave 168 consumes the uniform Mpc phase supply, removes the last routine
selected-family premise, and rewrites the remaining M0 and odd-L inputs as
explicit arithmetic conditions.

## General displayed Mpc record

`MpcHandleDeterminant` turns `wPmpc_branchFreeSupply_handles` into the full
affine determinant at every honest display and handle count.
`MpcGeneralHandleFamilyClosed` then exports the determinant, corrected
`WordCertificateRN`, tied residual, and `mpcRowResidualRN_of_familySelection_closed`
without an
analytic premise.  The selected theorem retains only an oriented equivalence,
scaling, and the exact transported C-pivot.

`MpcGeneralHandleFamilyCanonical` discharges scaling with the repository's
canonical `mScalingHypothesis`.  Its preferred selected endpoint therefore
retains only the oriented equivalence and the exact positive-level C-pivot.
The same module proves that such a pivot has zero value under the ordinary
mod-two cup used in the M0 branch.  Exact depth at positive level consequently
requires a filtered or divided invariant; ordinary parity cannot detect it.

## Compact-M pivot as arithmetic

`M0FieldPivotCup` identifies `M0FieldPivotUnit` with nonvanishing of the cup of
the transported distinguished D character and the mod-two unramified
character.  This is independent of the chosen oriented presentation.

`M0FieldPivotHilbert` uses Kummer surjectivity and the existing local
cup/Hilbert dictionary to choose field elements `a` and `b` for which the
pivot is equivalent to failure of the quadratic norm equation

```text
b = x^2 - a y^2.
```

The representatives are intentionally noncanonical.  Level zero makes the
unramified character nonzero somewhere on `ker chi`, but does not force its
cup with the distinguished D class to be nonzero.  A canonical symbol-level
producer would additionally need the missing Tate--Kummer--Artin placement
theorem.

## Compatible odd-L ramified packet

`RamifiedCertificateCompatibleAt` preserves the caller's custom `MuN 2`
action and reduces `CompatibleRamifiedDataAt` to exactly two predicates over
compatible ramified finite uses:

1. existence of some residue-trivial lift of the tame involution;
2. an `InvolutionFieldPackage` at the anchored splitting field.

The existential lift is strictly weaker than residue-triviality of the
arbitrary `surjInv` choice used in the earlier convenience constructor.  The
general producers for these two arithmetic predicates remain open: the
landed residue-lift theorem is confined to the absolute `q = 2` tame case,
while the involution-field package is the explicit AX3/AX4 interface.

## Verification

All new declarations elaborate at the default heartbeat limit.  The Mpc
determinant and record declarations use only `propext`, `Classical.choice`,
and `Quot.sound`; canonical scaling adds only the inherited
`peripheralCyclotomicAction`.  The cup/Hilbert and compatible ramified
reductions use only the repository's already-recorded Tate-duality and local
Hilbert-symbol foundations.
