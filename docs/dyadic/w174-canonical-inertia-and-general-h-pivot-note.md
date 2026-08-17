# W174: canonical inertia and the general-h pivot boundary

W174 gives standard mathematical forms to the remaining compact-M, general-h Mpc, and odd
ramified interfaces.  It does not assume any of the new residuals.

## Compact M: the Artin value is exact

`M0FieldPivotArtinExact` proves that, once transported distinguished D is placed on the
filtration-uniformizer Kummer class,

`M0FieldPivotUnit B alpha h <-> M0UniformizerArtinCompatibility B FF`.

Thus the single W172 Artin value is not merely a convenient sufficient hypothesis.  Under the
natural D placement it is exactly the intrinsic pivot.  The remaining M0 arithmetic problem
cannot be weakened within the current cup-form interface.

## General-h Mpc: the missing shear is explicit

`MpcGeneralHandlePivotBoundary` defines `MpcPivShiftH alpha h`, the exact odd-`2B` shear needed
to create the divided C digit for arbitrary rank and handle count.  The completed M6 theorem
proves `MpcPivShiftH 2 0`, recovering the unconditional W173 rank-four consumer.

For general `alpha,h`, an epsilon-true selection still places B at the exact lower level.  Given
`MpcPivShiftH alpha h`, the module constructs the exact C pivot and the selected corrected-RN
residual.  Canonical unit scaling preserves exact-pivot existence, and handle clearing fixes C,
so neither existing correction can manufacture the missing shear.  No lift from the rank-four
automorphism to `DM alpha h` is currently available.

## Odd residue data: canonical absolute inertia

`RamifiedCertificateAbsoluteResidueAction` constructs Mathlib's canonical action of
`Gal(Qbar2/Q2)` on the residue field of the absolute norm-valuation subring.  Its kernel is the
canonical `absoluteInertiaSubgroup`, and the module proves

`g in absoluteInertiaSubgroup <-> IsResidueTrivial bot g`.

The W173 odd-root factorization is therefore equivalent to the standard containment saying that
the preimage of full tame inertia lies in canonical absolute inertia.  This containment, in its
oriented `tameAtParams` form, produces `CompatibleResidueLiftAt`.  AX4 does not presently export
the comparison between its abstract tame quotient and this canonical residue action.

## Odd norm data: unit-spectral reciprocity

`AnchoredTameInertiaSpectralReciprocity` isolates `AnchoredUnitSpectralReciprocity`: for any
finite prescribed quotient, if all reciprocity lifts of units fix its field, then the relative
ramification index is one.  Combined with the full-inertia refinement of the AX4 unit clause, it
produces the exact prescribed relative-unramified residual and the complete equal-norm packet.

The remaining inputs are now two familiar local-CFT comparisons:

1. `qMkQ` kills reciprocity of units, rather than merely its 2-primary projection `nuTq`;
2. unit Artin lifts fixing a finite field imply relative ramification index one.

The repository has no exported valuation-inertia or finite-layer norm-reciprocity theorem that
supplies either statement.

## Verification

All four W174 modules compile at default heartbeat and recursion limits.  Structural declarations
use exactly `propext`, `Classical.choice`, and `Quot.sound`; corrected-RN consumers inherit only
their established field-side foundations.  No `sorry`, new axiom, native decision procedure, or
option override is used.
