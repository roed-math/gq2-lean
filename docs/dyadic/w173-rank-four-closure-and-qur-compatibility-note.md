# W173: rank-four closure and full unramified compatibility

W173 closes the remaining rank-four Mpc selector branch and identifies the two odd ramified
arithmetic atoms at the full unramified quotient rather than its 2-primary shadow.

## Mpc: epsilon-true rank four is closed

`MpcTrueRankFourResidual` corrects a stale conclusion in the W172 reduction.  The predicate
`MpcPivShift 2` is not open: `MpcMk.mpcMk_pivShift` proves it unconditionally using the completed
marked Hall ladder.  Therefore every epsilon-true rank-four selection admits an odd shear, an
adjusted orientation with divided C digit one, and the exact transported C pivot.

The final theorem `mpcRowResidualRN_of_familySelection_true_rankFour` needs only:

1. the selected `.Mpc 2 r true eta` branch equation;
2. the honest rank-four handle-count equation; and
3. nonemptiness of the rank-four oriented-equivalence type.

No pivot, digit, scaling, level, residue, determinant, or display premise survives.  Together
with W171's epsilon-false theorem, both rank-four Mpc signs now have corrected-RN consumers.

## Odd residue data: factorization through `QurQ`

`RamifiedCertificateResidueQurCompatibility` proves

`tame g in inertiaPartQ q <-> qMkQ q (tame g) = 1`.

Consequently the corrected full-inertia residue condition is exactly the assertion that the
odd-root action kills the kernel of `qMkQ ∘ tame`.  Equivalently, that action factors through the
full unramified quotient.  `compatibleResidueLiftAt_of_oddRootActionFactorsThroughQur` then
produces the complete compatible residue-lift packet.

This is the narrow classical compatibility still absent from the current interfaces.  Finite
pro-2 reciprocity cannot prove it because W172's obstruction is already an unramified C3
quotient.

## Odd norm data: the prescribed unramified field

`AnchoredTameInertiaPrescribedUnramified` proves that the prescribed subgroup contains the
pulled-back full tame inertia, so its quotient genuinely factors through `QurQ`.  It also isolates
`TameUnitInertiaRefinement`: reciprocity of every unit must land in that full-inertia kernel.  AX4
currently supplies only `nuTq = 1`, which loses the prime-to-two unramified component.

For the prescribed field F0, the theorem
`anchoredTameInertiaField_relE_eq_one_iff_equalNormValues` identifies

`e(F0/K) = 1`

exactly with the needed spectral equality of value groups.  The compatible-use residual
`AnchoredTameInertiaRelativeUnramifiedDataAt` feeds the W171 relative-odd producer and hence the
full equal-norm packet.  What remains is a relative unit/norm theorem proving this exact
prescribed extension is unramified; group factorization alone does not provide the spectral
statement in the current API.

## Verification

All three new modules and the corrected W172 documentation compile at default heartbeat and
recursion limits.  Structural declarations use exactly `propext`, `Classical.choice`, and
`Quot.sound`; the final Mpc residual inherits only the established canonical-scaling field input.
No `sorry`, new axiom, native decision procedure, or option override is used.
