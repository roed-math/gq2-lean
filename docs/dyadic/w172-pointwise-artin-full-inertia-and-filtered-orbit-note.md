# W172: pointwise Artin values, full inertia, and filtered placement

W172 replaces four broad campaign premises by the exact local statements used by their
consumers.  It also records finite counterexamples to two tempting but false shortcuts.

## Compact M: only one Artin value is needed

`M0FieldPivotArtinValue` isolates `M0UniformizerArtinCompatibility`.  This is the single
equation obtained by evaluating the mod-two unramified character on reciprocity of one
filtration uniformizer.  It is equivalent to the cup value used by the distinguished compact-M
pivot.

Consequently `m0RowResidualRN_of_familySelection_of_uniformizerD_artinValue` closes the
family-selected residual from:

1. placement of the transported distinguished D class on the uniformizer Kummer class; and
2. this one Artin value.

The full pointwise `ModTwoTateKummerArtinCompatibility` packet is sufficient but strictly
stronger than the corrected-RN consumer requires.

## Mpc epsilon-true: exact digit-or-shear criterion

`MpcTrueFilteredPlacement` proves that an epsilon-true rank-four selection places B at exact
level `r - 1`.  Its square already attains the exact level-`r` kernel value, so exact kernel
attainment cannot determine the distinguished C digit.

The remaining placement question is exact.  For any current oriented equivalence, a digit-one
orientation exists if and only if either its current divided C digit is one or its
chi-preserving orbit admits an odd B-shear.  The open pivot shift supplies the latter condition,
but is not assumed.  This replaces an opaque filtered-pivot premise by a falsifiable orbit
statement and explains why the epsilon-false argument does not extend formally.

## Odd residue data: full inertia is smaller than the 2-primary kernel

`RamifiedCertificateResidueFullInertia` corrects the natural reciprocity boundary.  The maps
`nuTq` and `nu_ur` retain only the 2-primary unramified coordinate, so their kernels also contain
prime-to-two unramified elements.  A uniform C3 quotient detects

`sigma * (sigma ^ omega2)^{-1}`

inside `ker nuTq` while killing `inertiaPartQ`.  Hence the full 2-primary kernel cannot be
identified with inertia.

The honest residual `TameFullInertiaAbsoluteResidueTrivialAt` asks residue triviality only for
source elements whose tame image lies in `inertiaPartQ`; this is sufficient for
`CompatibleResidueLiftAt`.  The still narrower `TameTauFixesOddRootsLiftAt` is exactly the
selected tame-tau lift condition.  W171's unramified-kernel predicate remains a valid sufficient
hypothesis, but it is not the standard full-inertia theorem and is no longer the preferred
frontier.

## Odd norm data: the visible relative index

`AnchoredTameInertiaRelativeIndex` computes the prescribed anchored field degree as

`[F0 : K] = [rho.range : <t>]`

and proves that `e(F0/K)` divides this visible range index.  Oddness of that exact index produces
the relative-odd packet and therefore the equal-norm-value-groups conclusion.

Oddness of `orderOf t` alone is insufficient: an explicit order-two identity-map regression has
odd `orderOf t` but even preimage index.  The expected sharper arithmetic statement is that the
prescribed anchored extension is unramified over K.  Proving it requires relative unit/norm
reciprocity for this exact layer, not another subgroup-cardinality argument.

## Verification

All four modules compile at default heartbeat and recursion limits.  Every public declaration
uses only its established foundations; the structural Mpc and odd-data declarations use exactly
`propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, new axiom, native decision
procedure, or option override is used.
