# W361 arbitrary-basis N refinement audit

Date: 2026-09-17. Scope: the three `NBasis*` refinement modules, and independent
read-through and fresh compilation of `FreeProTwoMatrixBasis` and
`NFrameMatrixLift`. The refinement author performed this audit; a separate
agent also independently read and compiled the three refinement modules.
No proof sources were changed for this report.

## Result and verification boundary

PASS: all five complete source files were read and compiled afresh with the
pinned runner at default heartbeat limits. All 58 public axiom prints were
exactly `[propext, Classical.choice, Quot.sound]`; all five commands exited 0
without warnings. These are source-module rechecks against the shared import
cache, not a claim that this audit itself rebuilt the whole dependency graph.
The parent-owned fresh campaign build is separate.

The new refinement is genuinely arbitrary-basis and arbitrary-handle-rank.
There is no supplied derivative-image theorem, diagonal-unit matrix premise,
identity-handle restriction, or reduction to a fixed nilpotency class. The
initial-stage theorem still explicitly requires its initial depth-three
relator defect; neither matrix realization nor the free frame lift silently
asserts that condition.

## 1. Inverse-matrix interpolation inside the actual correction kernel

Let `x_v` be the free generators, `e` an actual continuous free automorphism,
and write

```
A[j,v] = coord_j(e x_v),    B[v,k] = coord_v(e⁻¹ x_k).
```

`freeTwo_basis_inverse_coordinates` (`NBasisRowRefinement.lean:21`) proves
`sum_v B[v,k] A[j,v] = delta(j,k)` by applying the ordinary-character coordinate
formula to `coord_j ∘ e` at `e⁻¹ x_k`. Thus the inverse matrix is supplied by the
actual inverse automorphism; invertibility is not a new hypothesis. Columns
are generator images throughout.

For each non-head slot `i`, `nBasisKernelWitness` is the **finite ordered
product** of the existing actual kernel tuples `K(i,v)` raised to the two-adic
exponents `B[v,k]`. Membership follows from the proved all-`v` kernel theorem,
closedness of the actual correction subgroup, continuity of two-adic powers,
and density of natural powers. The proof does not commute factors in the
noncommutative tuple group. It only adds their images under ordinary
characters. The exact row is

```
coord_l(witness(i,k)_j) = 2^(n+1) delta(j,i) delta(l,k).
```

This includes the former exceptional `v=b` column. Finite row interpolation
then clears every row. The head slot uses scale zero and identity witness
**only after** its rows are supplied as exactly zero. Consequently
`exists_nBasis_allRows_same_kernelCoset` (`:119`) produces `t'` with:

- `t⁻¹*t'` in the actual current-basis correction kernel;
- every free coordinate of every `t'_i` equal to zero;
- the original depth `lambda_(n+2)` retained;
- literal corrected N-relator equality in the quotient by `lambda_(n+4)`.

The last clause uses the actual kernel/relator theorem, not merely a formal
linear derivative or an unproved integration assertion.

## 2. Extra head digit and actual target-relative error

`exists_nBasis_full_relative_correction`
(`NBasisRelativeRefinement.lean:24`) first invokes the proved ordinary-head
lemma. Its load-bearing premise is ordinary-character agreement of the
current relator with the target. Together with the improved error in
`lambda_(n+4)`, the head coefficient `2 + 2^alpha` supplies the extra digit
needed to replace the head correction by an exact character-zero element in
the same class modulo `lambda_(n+3)`.

`NPlaneFilteredSlack` preserves the improved relator congruence under that
replacement. Arbitrary-basis kernel interpolation then clears the remaining
rows. The final proof uses quotient equality to retain the **same actual
target-relative error**, not a relation assumed to vanish in the free group.
Neither the input correction nor the current basis needs a separate
orientation premise in this refinement theorem. Its output is killed by
every continuous ordinary Z₂ character and by the canonical orientation.

## 3. Iteration without an assumed stage supply

`exists_nBasis_exact_stage` (`NBasisExactStages.lean:58`) takes an actual
initial free automorphism `e0`, canonical orientation on its generators,
ordinary relator-row agreement with the canonical relator, and actual initial
error in `lambda_3`. For every `n` it constructs an actual free automorphism
with error in `lambda_(n+3)` and **all exact free coordinate columns of e0**.

The induction calls the already proved `nAmbientStageSupply`, then the new
relative refinement, then the actual free-basis correction theorem. There is
no stage-supply parameter. Exact coordinates transport every ordinary
character and therefore the relator-row premise. Corrections retain all
`(4+2h)^2` integral entries, including the free head coordinate; this is
stronger than retaining ordinary characters only after passing to D_N.
Separately quantified stage witnesses are asserted, not a coherent infinite
sequence; the downstream compactness theorem is responsible for passage to
an exact automorphism.

## 4. Independent matrix and full-frame lift checks

`FreeProTwoMatrixBasis.lean` defines literal ordered coordinate words. For
`A B = 1`, the composition of the associated endomorphisms has identity
coordinates and hence induces the identity in every index-two quotient.
The Frattini criterion gives surjectivity; finite topological generation and
profinite Hopficity give an actual continuous automorphism. It correctly does
**not** identify the endomorphism of `B` with the nonabelian inverse. Identity
columns fix literal generators, while identity rows preserve characters on
every element. The generic statements cover every finite rank, including
rank zero; no relator preservation is claimed.

`NFrameMatrixLift.lean` was independently read in full and freshly checked.
Its coordinate section chooses a representative 0 or 1 for the torsion
coordinate and retains all integral coordinates. The section need not be a
homomorphism: only its finitely many columns define a free homomorphism.
Every index-two free quotient factors through the actual full N frame, so
surjectivity of the supplied frame automorphism gives a genuine free-basis
lift. The projection identity holds on **every free element** and includes
torsion and arbitrary handle mixing.

The frame's distinguished nontrivial torsion element is fixed by every frame
automorphism. Its chosen column is literally the head generator. Preservation
of the actual frame orientation implies the exact `b` row via the proved
injectivity of the `nUnit alpha` exponent map (`alpha >= 2`). The integral
inverse matrix is subsequently extracted from the actual inverse free lift;
it is not assumed to be the independently chosen section of the inverse
frame automorphism. No cup or depth-three assertion is hidden in this file.
Those are separate inputs supplied by `NFrameCupCoordinates` and
`NInitialCupDepth` in the subsequent capstone.

## Reproduction and exact source identity

From `/Users/roed/claude/cla/work/gq2-dyadic-campaign`, each of the five files
below was checked with:

```sh
bash /private/tmp/gq2-w360-lean.sh GQ2/Dyadic/MarkedCore/NAME.lean
```

The runner uses Lean `v4.31.0-rc2`, the shared `main-build-cache` import tree,
the configured dependency caches, `autoImplicit=false`, and
`relaxedAutoImplicit=false`; no heartbeat override is passed. This audit
emitted no new module artifacts and did not modify the historical frozen
verification inventory. Public pin counts are respectively 6, 1, 2, 19, 30.

SHA-256 of the audited source revisions:

```text
b203a6831352fc58f52140691237ab3889f98ee89e0e966dab1c11d7633bd668  NBasisRowRefinement.lean
adfabfd1edd812b4effe4eef6113ccf105cb31ae48967f72caff445ea4fda01f  NBasisRelativeRefinement.lean
f2af482436025794895ced466f033687a939f781db52eeb2da9ed2868c081c89  NBasisExactStages.lean
2b1940ff147d4769bf50b449d4f9aceab58a7cc57ad592708ddc64a5c3c40e10  FreeProTwoMatrixBasis.lean
04bb672bd3fda3e849558487e2d355542e1f5e81386bd2cd00af0b2462174a55  NFrameMatrixLift.lean
```

Handoff: no defect or hidden fixed-handle premise was found in these modules.
The full-frame cup-to-initial-depth theorem, compactness/transfer, and final
stabilizer capstone are separately checked modules and should remain separate
entries in the whole-build verification and theorem-scope audit.
