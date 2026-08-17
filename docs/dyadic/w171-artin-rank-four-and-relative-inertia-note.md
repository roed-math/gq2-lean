# W171: Artin evaluation, rank-four closure, and relative inertia

W171 turns each W170 boundary into either a corrected-RN consumer or a field-theoretic residual
with no remaining presentation or finite-action ambiguity.

## Compact M: direct Artin evaluation of the pivot

`M0FieldPivotArtin` evaluates an arbitrary even-model character class on the field
abelianization and applies this to the mod-two unramified character.  Marked reciprocity sends a
filtration uniformizer to unramified value `-1`, so that character takes the nonzero value modulo
two.

Consequently `m0FieldPivotUnit_of_uniformizerD_of_artin` needs only:

1. placement of the transported distinguished D class on the filtration-uniformizer Kummer
   class; and
2. `ModTwoTateKummerArtinCompatibility B`.

The separate W170 premise identifying the field marking with an unramified Kummer class is no
longer needed.  `m0RowResidualRN_of_familySelection_of_uniformizerD_artin` is the corresponding
family-selected corrected-RN consumer.  The two surviving inputs are genuine local-CFT
placement and Artin compatibility; level zero alone still does not imply them.

## Mpc: the epsilon-false rank-four residual is closed

`MpcFalseRankFourResidual` composes the W170 forced digit with the W169 pivot equivalence and the
canonical-scaling corrected-RN consumer.  The theorem
`mpcRowResidualRN_of_familySelection_false_rankFour` has no explicit level, residue, filtered
digit, pivot, scaling, determinant, or display premise.  Its remaining honest inputs are the
selected `Mpc 2 r false eta` branch equality, the rank-four equation saying its handle count is
zero, and an oriented equivalence.

The `epsilon = true` branch remains different: W170's complete selector-schema counterexample
shows that its divided pivot digit is not determined by the current rows.

## Odd L: reciprocity versus absolute residue action

`RamifiedCertificateResidueReciprocity` strengthens the B13 approximation step to an odd-order
root of unity near every norm-one element.  Existing odd-root separation then proves

`FixesOddRootsOfUnity g <-> IsResidueTrivial bot g`.

This identifies the W170 residue-action premise exactly with the assertion that `ker B.nu_ur`
fixes all odd-order roots of unity.  Oriented tame reciprocity transports that assertion to
`TameInertiaAbsoluteResidueTrivialAt`, and `compatibleResidueLiftAt_of_nuUrKernel` produces the
full compatible residue-lift packet.  The remaining theorem is precisely prime-to-two
cyclotomic/residue compatibility for the unramified character; the current reciprocity bundle
contains no such clause.

## Odd L: absolute oddness is relative oddness

`AnchoredTameInertiaNormIndex` proves that the canonical anchored tame-inertia field contains
`K`.  For odd-degree `K`, the ramification tower and fundamental identities give the exact
equivalence

`Odd e(F0 / Q2) <-> Odd e(F0 / K)`.

The compatible-use form `AnchoredTameInertiaRelativeOddDataAt` preserves the caller's custom
action and quantification.  Its producer
`anchoredInvolutionEqualNormValueGroupsAt_of_relativeOddTameInertia` closes the entire norm-value
packet once this relative ramification index is odd.  Thus no absolute-base bookkeeping remains;
the unresolved statement is the honest relative inertia theorem for the prescribed anchored
field.

## Verification

All four modules compile at default heartbeat and recursion limits.  Structural declarations use
only `propext`, `Classical.choice`, and `Quot.sound`; the M0 pivot theorem inherits the existing
Tate-duality foundation, and the selected M0 and Mpc residuals inherit only their established
field-side inputs.  No `sorry`, new axiom, native decision procedure, or option override is used.
