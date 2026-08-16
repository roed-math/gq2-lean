# W165: intrinsic field conditions and handle reductions

Wave 165 sharpens three remaining generic-family fronts without adding any
axioms or hidden existence claims.

## Compact M: the surviving pivot is intrinsic

`M0FieldPivotInvariant` proves that unitness of the canonical `C0` marking is
independent of the chosen oriented equivalence.  The proposition
`M0FieldPivotUnit` therefore packages a genuine field-side condition, and
`m0RowResidualRN_of_familySelection_of_fieldPivot` consumes that condition to
produce the selected corrected residual.  The wave does not assert that the
condition holds: W164's automorphism no-go shows that it cannot be manufactured
by changing the oriented frame.

## Procyclic M: handles are not an obstruction

`MpcGeneralHandleRealization` proves that the level condition makes every
handle coordinate divisible by the scaled `C` pivot.  Existing Eichler moves
then clear all handle coordinates while preserving `chiM`.  With an explicit
`MScalingHypothesis`, `exists_scaled_handle_correction` also normalizes the
pivot; the remaining rank-four corrections are separate.  The module packages
a general-h corrected certificate, realization, canonical marking
surjectivity, and tied branch constructor without claiming that field data
already supplies the certificate.

On the analytic side, `MpcUnramifiedHandleHessian` evaluates the arbitrary
display and arbitrary-h unramified Hessian as the common compact wall-handle
phase plus the single factor-set charge

```text
dat.m ((s ^ E omega2) ^ pp) c0.
```

The formula is independent of `eta`.  `MpcUnramifiedHandleComparison` removes
that charge by a translation in the second head coordinate and returns the
common uncharged comparison.  Its honest remaining input is a scaled
unramified resolved-family row whose pivot acts fixed-point-freely; no
projected boundary transport is asserted in this wave.

Together with W164's ramified formula, arbitrary handle count is no longer an
analytic obstruction.  The next integration seam is to obtain the scaled
fixed-point-free unramified row from the selected action-image boundary and to
assemble the two branches into a uniform determinant supply.

## Odd L: the splitting field is canonical

`RamifiedCertificateAnchoredSplit` chooses the fixed field of the anchored
kernel of a finite quotient.  Krull correspondence proves the exact fixing
subgroup identity and finite dimensionality, so
`ramifiedCertificateOfAnchoredSplit` discharges the splitting field, trivial
`ZMod 2` action, and kernel-identification fields of `RamifiedCertificate`.

Two arithmetic inputs remain explicit for each compatible finite ramified
action: a residue-trivial lift of the tame involution and an
`InvolutionFieldPackage` over the anchored field.  The legacy universal
`ramifiedData` binder ranges over unrelated maps `c` and `rho`; this wave does
not claim such an incompatible packet can be produced.

## Verification

Every public declaration in the five new modules was compiled at the default
heartbeat limit and audited with `#print axioms`.  The mathematical surfaces
use only `propext`, `Classical.choice`, and `Quot.sound`, except for the
expected inherited `peripheralCyclotomicAction` in the selected compact-M
consumer and `tateDualityAt` in the ramified-certificate builder.
