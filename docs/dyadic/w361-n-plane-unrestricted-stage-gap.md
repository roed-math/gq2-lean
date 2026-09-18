# W361 — the N-stage gap and its ambient-stage resolution

**2026-09-17 18:55 UTC successor update:** the continuation formerly labelled
PROPOSED below is now implemented. Eleven new modules culminate in
`nFullStabilizer_lift_iff` in `NFullStabilizerLift.lean`:
actual full-frame orientation/cup isometries lift, with arbitrary handles and
the full torsion-sensitive all-element square. Initial lambda-three error,
arbitrary inverse-matrix kernel-row interpolation, every higher stage and the
full-coordinate compact limit are all supplied, not assumed. The public Lean
name is `GQ2.Dyadic.MarkedCore.nFullStabilizer_lift_iff`. Read
`w361-claude-code-handoff.md`, `w361-n-full-stabilizer-independent-audit.md`,
and `w361-n-full-stabilizer-scope.md`. Preserve the dated reasoning below as
history; do not reopen these seams or infer a finite Nielsen-list certificate.

Updated 2026-09-17, 16:58 UTC. This research lane is independent of the
completed selected-presentation theorem. The ambient stages, strong scaling,
and full torsion-sensitive core-row lifting are now integrated and individually
checked at default limits. The parent began a new zero-reuse, 1541-module
verification snapshot at 16:45 UTC; this note does not pre-announce its result.
The earlier inventory is retained as history, but its claims that a new general
span proof or a torsion-sensitive core-row bridge is missing are **superseded**.

## Final integrated endpoints

- `MarkedCore/NPlaneAmbientStage.lean:197`,
  `NPlaneAmbientStage.exists_ambient_stage`, is the fourteen-pin ambient
  result first checked as `/private/tmp/NFreeAmbientFamily.lean`.
- `MarkedCore/NPlaneGeneralScaling.lean` proves
  `nPlaneScalingHypothesis_general`, `nCorePlane_gl2_lift_general`, and
  `nStabParam_lift_general` without a supplied stage, scaling, or mixing
  premise. Its exact-row induction uses the integrated all-row kernel and
  relative-refinement modules.
- `Instances/DNAutomorphismCup.lean` supplies actual DN automorphism cup
  invariance, rather than assuming it. Its eight public declarations are
  standard-three.
- `MarkedCore/NStabilizerFullRows.lean:296`,
  `NStabilizerFullRows.nPhiHom_aut_fullFrameMark`, recovers every full
  coordinate from the ordinary action and the one explicit free torsion
  entry. All twenty-four public declarations are standard-three.
- `MarkedCore/NTorsionAdjust.lean` supplies the exact N1 precomposition,
  with seven standard-three declarations.
- `MarkedCore/NStabilizerFullLift.lean:11`,
  `nStabParam_fullFrame_lift_general`, removes that last torsion-entry
  premise. For every `alpha >= 2`, every handle rank, and every admissible
  `P : NStabParam`, it returns an actual continuous automorphism preserving
  orientation and satisfying, for **every** marked generator,

  ```
  nPhiHom ha h (abMk (Psi (dnGen alpha h i))) = fullFrameMark P h i.
  ```

  `fullFrameMark` is literally `P.rows` on the four core generators and
  identity on every handle coordinate, with zero handle torsion. The theorem
  has no residual `htau`, cup, matrix, or stage-supply premise and has exactly
  the standard-three axiom footprint. Its ordinary-character conclusion is
  also retained.

These files were individually compiled warning-free and cached before the
new snapshot freeze. **Arbitrary handle-mixing stabilizers are not claimed
by this endpoint**; that is the proposed continuation below.

## New checked result: actual ambient stages in every rank

`/private/tmp/NFreeAmbientFamily.lean` proves an actual correction step at
every handle rank and every depth at least three. All fourteen public pins
are exactly standard-three; compilation is warning-free at default limits,
and `.olean`/`.ilean` were generated at 16:08 UTC.

Using the notation of the earlier inventory below, its exact final theorem,
`GQ2.Dyadic.MarkedCore.NFreeAmbientAudit.exists_ambient_stage`, is:

```
alpha >= 2, k >= 3,
e : ContinuousMulEquiv F F,
forall i, chi(e(x_i)) = chi(x_i),
r(e o x)*r(x)^(-1) in lambda_k
  imply
exists t : I -> F,
  (forall i, t_i in lambda_(k-1)) and
  r(i -> e(x_i)*t_i)*r(x)^(-1) in lambda_(k+1).
```

There is **no orientation or ordinary-row condition on `t`**. This is an
actual image/preimage and next-stage group-word theorem, not a conditional
image interface or finite-class test. It retains the exact original free
relator as the target.

## The general infrastructure was already present

The decisive existing API is
`StageAbstractionEvenDerivKer.evenDeriv_mem_rawShiftSpan_of_forall_derivKer`.
It is polymorphic in the pro-two carrier and handle rank, and tests an
arbitrary central-layer class. Its supporting
`StageAbstractionEvenRawSpanStep.evenRawAugmentedSpan_of_base_of_step` and
`evenRawAugmentedSpanBaseSupply_of_generates` already prove the uniform
ambient span, including every handle and every non-twisted pure-power tail.

The earlier rejection of rank-three `stageSL1R0/R2` as direct all-rank N
producers was correct. The subsequent inventory was incomplete: the old
even field wrappers' conditional derivation-family and raw-to-bracket
hypotheses do **not** mean their underlying general ambient span is absent.
The free group supplies its coordinate derivation family directly; the
stronger raw-to-neutral bracket upgrade is unnecessary here.

## Checked adapter and non-vacuity audit

1. Existing `EvenFamily.evenFamDerivModelN`, composed with `freeNProjection`
   and `e.symm`, gives the exact Kronecker coordinate crossed maps on the
   **current** free basis. Free hom-extensionality extends the supplied
   generator orientation equations to all elements, proving their exact
   `IsChiShadowDeriv` condition.
2. The criterion packages its marking in `Tuple W`. Set `W.word=1` to
   discharge only the irrelevant container's relation field. The tuple still
   contains the actual current generators, their orientation values, and a
   genuine generation proof. The tested class is independently the actual
   `r(e o x)*r(x)^(-1)`.
3. Lift each finite offset to its natural-number representative in `Z2`,
   apply `evenFam_nRelWord_wordLift`, and reduce. This proves that **both**
   actual relator words vanish under every coordinate crossed map; hence
   their actual target-relative difference vanishes exactly.
4. The error itself is the `derivKer` representative, with its supplied
   depth and zero offset. A `WL(k+1)` homomorphism is never incorrectly
   descended through `Q_(k+1)`.
5. The generic criterion provides actual raw-shift membership. Extract its
   depth-correction representatives, replace the canonical base by the
   family's actual base, and apply `evenRawStageShift_n`. The current error
   is central in the top layer, so the inverse shift cancels it with the
   repository's exact multiplication convention.

The original free relator is **never assumed to die** in a finite quotient.
The dummy word is not a replacement for the actual error or target.

## Relationship to the frozen conditional reduction

`NPlaneUnrestrictedReduction.NUnrestrictedStageSupply` also requests
`chi(t_i)=1` for every orientation-compatible free basis. The new ambient
theorem does not establish that literal old proposition; they must not be
silently identified.

The strong-scaling induction maintains additional, already-proved invariants:
the exact unit-diagonal ordinary matrix of the current free basis, and exact
ordinary-character agreement of its relator with the target. These allow:
actual error -> head extra digit -> same-class character-zero head ->
derivative-kernel clearing of **all** remaining ordinary rows -> exact
orientation preservation -> free-basis persistence -> quotient stages ->
compactness. No additional stage-image premise is needed by this route.

The formerly omitted b-row is not a mathematical obstruction. In independently
checked `/private/tmp/NPlaneKernelBExtension.lean`, the same actual kernel
tuple works at `v=b`: its exceptional head-slot factor is
`([b,g][g,b])^(2^n)=1`, and its last factor is `[b,b]^(2^n)=1`; the remaining
derivative vanishes by the existing mixed-power identity. The parent is
assembling the unconditional strong-scaling endpoint from this fully ambient
route; this timestamp does not pre-announce that endpoint's verification.

## Hypotheses and edge cases

- `alpha >= 2` and `k >= 3` are load-bearing. No alpha-one or degree-two
  extrapolation is asserted; the cubic mixed-square terms are retained.
- `e` is an actual free continuous automorphism, not a finite-level tuple.
- Exact canonical orientation rows are used, not inferred merely from being
  a basis.
- There is no restriction on `h`; zero handles are included.
- Derivative kernels do not imply image membership. Image membership is
  separately obtained from the generic span and crossed separation first.
- The selected-presentation endpoint is unchanged. No arbitrary externally
  fixed full marking is asserted to be preserved by this research result.

## Original MC-N scope versus the newly closed formal consumer

Earlier read-only specification audit, after general scaling but before the
subsequent full-row bridge. Its missing-core-bridge assessment is superseded
by the integrated endpoints above. **Torsion-sensitive abelianization lifting
is an explicit original MC-N requirement**, not merely an optional stronger
nonclaim invented during this audit:

- `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex:732`–735
  asks that every automorphism of `D_P^ab` preserving orientation, the
  torsion relation vector, and the mod-two cup form lift to `D_P`.
- The same packet's MC-M/MC-N completion table, lines 1077–1082, requires
  lifting the Smith–Witt stabilizer **on the abelianization**.
- `docs/dyadic/plan.md:68`–69 and 114–121 repeat that specification.
- `docs/dyadic/mc-design.md:633`–642 writes the intended literal equation
  `forall x, B.e(abMk(Psi x)) = B.e(phi(abMk x))`, and says N is its mirror.

The implemented formal endpoint is genuinely narrower in its stated result:

- `N.lean:908`–936 defines the full `NStabParam`: `tau`, `tauSigma`,
  and `tauX2` are actual `ZMod 2` coordinates, and `P.rows` retains them.
- `N.lean:1863`–1865 defines `P.nuAction` using only `p`, `q`, and `g`.
  The three torsion parameters are absent. `nChar_dnX0` explains why
  every ordinary `Z2`-valued character is blind to these shifts.
- `N.lean:1872`–1887 and `ClearWide.lean:711`–720 ask only for orientation
  preservation and the simultaneous action on **all ordinary characters**.
- The new staged `NPlaneGeneralScaling.nStabParam_lift_general` discharges
  the last scaling binder in exactly that formal result. Its docstring
  correctly says “character-frame action”; it does not assert `P.rows`.

A concrete distinction is obtained by taking `p=q=0`, `g=1`,
`tauSigma=tauX2=0`, and choosing `tau=0` or `tau=1`. Both parameters are
admissible, and their `nuAction` is identical, while their `rows.x1`
torsion entries differ. The ordinary-character conclusion cannot identify
which of these two full abelianization actions the chosen witness has.
In particular, the older `N.lean:1867`–1871 comment identifying the
nu-frame theorem with the full memo obligation is not itself a checked
torsion-sensitive bridge.

This distinction is **not a defect in the completed selected field
presentation**. The marked-core certificate actually consumed by that
theorem requires orientation and one full `Z2` unramified character, as
written in packet lines 711–723 and ledger lines 150–163. Those requirements
do not ask to realize an arbitrarily prescribed torsion shift. The ledger
explicitly distinguishes sufficient marking correction from a larger
free-relator theorem.

Classification at that earlier checkpoint (items 2–3 are now discharged for
`P.rows` with identity handles by `nStabParam_fullFrame_lift_general`):

1. The formal `NPlaneScalingHypothesis` and its ordinary-character
   `NStabParam` consumer are now closed, uniformly in all valid exponents
   and handle ranks, with standard-three proofs.
2. Literal full `P.rows` realization, or a theorem on the induced
   `topAbelianization` map matching the original MC-N wording, is a
   **remaining original-specification bridge** unless another separately
   checked endpoint supplies it. It is not justified merely by the name
   “stabilizer lift.”
3. A plausible small-rank-independent continuation is to identify the
   induced abelianization action, use natural cup preservation to force
   the coupled torsion entries, and tune the remaining free `tau` entry
   with the existing exact N1 transvection `dnTauBEquiv`. At rank four,
   `nStabParam_tauSolve_unique` already supplies the algebraic uniqueness
   of the coupled entries. This is a proposed adapter route, not a proof
   in this audit; the actual cup/abelianization bridge and handle rows
   must be stated and checked.
4. No counterexample to full lifting is asserted. Nor should this
   original-specification difference be relabeled as a missing hypothesis
   of the existing fully marked selected-presentation theorem.

No authoritative plan, packet, or Lean source was changed by this audit.

### Exact reusable route to the torsion-sensitive rows

The follow-up found enough existing interfaces to make the bridge concrete.
The following design was then implemented in `NStabilizerFullRows` and
`NStabilizerFullLift`; it is now kernel-checked for the stated core-row scope.

1. `Instances/EvenModelCupForm.lean:178` gives `dnFrattiniCupForm` at every
   handle rank, and line 201 gives `dnObs_injective`. The directly reusable
   automorphism-invariance proof is already implemented for M in
   `Instances/M0C0PivotAutomorphism.lean:44`–125: transport `PresentedBy`
   through the automorphism, obtain a second injective obstruction map
   `H2 -> ZMod 2`, identify it with the canonical map by
   `LSquare.addMonoidHom_zmodTwo_eq_of_injective`, and compare the two
   explicit cup evaluations. All corresponding N presentation and
   obstruction inputs already exist. This avoids assuming cup preservation
   as an extra hypothesis or constructing a new general cohomology library.
2. `MarkedCore/NFrameExists.lean:232`–273 supplies the actual continuous
   torsion, B, C, D, and handle coordinate characters. Its `nPhiHom_gen`
   at line 553 and `nFrameExists_phiEquiv` identify their joint values with
   the actual abelianization frame. Thus full rows can be read from existing
   coordinates rather than from a separately assumed frame.
3. Suppose `Psi` is the witness of the new ordinary-character theorem and
   let `a_i` be the torsion-character value on `Psi(dnGen_i)`. Apply the
   actual N cup-invariance adapter to the torsion character and the reduced
   ordinary coordinate characters. The explicit all-rank `evenCupForm`
   (`Instances/EvenModelH2.lean:76`) gives:

   ```
   a_0 = 1,
   a_(handle U_j) = a_(handle V_j) = 0  for every j,
   p mod 2 = a_3*(g00 mod 2) + a_2*(g01 mod 2),
   q mod 2 = a_3*(g10 mod 2) + a_2*(g11 mod 2).
   ```

   The first equality uses the B-coordinate, whose pullback is unchanged;
   the handle equalities use the unchanged partner coordinate in each
   hyperbolic pair. No handle-rank case split is involved. The last two
   equations are exactly the existing admissibility couplings, so
   `N.lean:1045`, `nStabParam_tauSolve_unique`, forces
   `a_2=P.tauSigma` and `a_3=P.tauX2`.
4. Only `a_1` remains free. **Precompose** `Psi` with `dnTauBEquiv k`,
   choosing `k mod 2=P.tau-a_1`. Its exact generator formulas
   (`N.lean:583`, `:595`) change only the input `x1` by `x0^k`.
   Since the torsion value on `Psi(x0)` is one, this changes precisely the
   desired torsion entry. It preserves orientation (`:606`) and every
   ordinary character (`:1816`). The resulting automorphism therefore has
   the prescribed `P.rows` on the rank-four core and identity on all handle
   coordinates, including their torsion coordinates.

This route did not require altering the new compactness theorem. The N
automorphism-cup adapter, coordinate-pairing calculations, and final exact-row
packaging are all included in the checked integrated result.
Retaining an explicit mod-two matrix through the free-stage compactness
argument would be another possible route, but is not needed by this design.

There is a further scope distinction: `NStabParam` describes the distinguished
rank-four core with identity handle extension. An arbitrary all-rank
Smith–Witt stabilizer that mixes handles still requires the stated standard
handle-move assembly. Neither the ordinary-frame theorem nor the proved
full-core-row theorem should be advertised as that larger assembly
without its explicit theorem.

## PROPOSED continuation: arbitrary handle-mixing stabilizers

Read-only assessment, not a new theorem or an assertion that the original
all-rank handle-mixing obligation is solved. No Lean source was changed for
this assessment. The proposed target should quantify over an actual
continuous automorphism of `NFrameModel h` preserving orientation and the
full mod-two cup form, rather than silently reusing the rank-four
`NStabParam` type.

### Removing the unit-diagonal hypothesis from correction refinement

Let `F=FreeTwoRank(coreRank h)`, `x` its canonical basis, and `y=e(x)` for an
actual free continuous automorphism. Write

```
A[j,v] = coord_j(e(x_v)),
B[v,k] = coord_v(e^(-1)(x_k)),
d = 2^(n+1).
```

`FreeProTwoCharacterCorrection.freeTwo_character_coordinates` applied to
`coord_j composed with e` at `e^(-1)(x_k)` gives
`sum_v A[j,v]*B[v,k] = delta[j,k]`. The order is **A B**, with these column
conventions; it is not an assumed abelianization identification.

`NPlaneKernelTuple.lean:40`, `nPlaneKernelTuple_character`, already gives
the unrestricted exact current-basis row of each actual witness `K_(i,v)`:
it is zero outside correction slot `i`, and equals `d*A[j,v]` there.
`NPlaneKernelAllRows.lean:92` places it in the actual derivative kernel for
every `v`, including the orientation coordinate `b`, whenever `i != 0`.
`NPlaneCorrectionKernel.lean:120` says this kernel is closed. Therefore the
**finite ordered product**

```
W_(i,k) = product_v zpowZtwo(K_(i,v), B[v,k])
```

remains in that closed subgroup and has exact coordinate row
`d*delta[j,k]` in slot `i`. No commutativity of the ambient tuple group is
needed: the tested characters have commutative targets. No infinite product
or extra convergence argument is needed. For excluded head-slot rows use
the identity witness with scale zero after exact head cleanup.

This gives precisely the hypotheses of
`ProTwoRowCorrection.lean:108`,
`exists_closedSubgroup_rowZero_same_coset_fintype`. Ordinary depth divisibility
then uses scale `d`, without division by a diagonal unit. The existing
`NPlaneFullRelativeRefinement` head cleanup, filtered replacement, and
orientation recovery do not themselves require diagonality; their current
diagonal binder enters through the row-interpolation call. Thus this is a
specific reusable generalization, not another unknown image theorem.

### Initial basis and the genuine initial-depth seam

For a prescribed full abelianization automorphism, choose an integral lift
of its coordinate matrix with torsion-generator column exactly `e_0`.
The unique order-two element must be fixed (`N.nFrameModel_map_t`), so that
choice is compatible with the target. Orientation preservation should force
the B-coordinate row to be exactly `e_1`, using
`N.nUnit_zpowZtwo_injective` and the canonical orientation factorization.
The remaining finite torsion entries can be lifted to `0` or `1` in `Z2`.
The free block's invertibility makes the resulting integral matrix invertible.

Independent variance check: with generator-image **columns**
`A[j,v]=coord_j(e(x_v))`, preservation of the pulled-back character cup form
means `Abar G Abar^T=G`, **not** `Abar^T G Abar=G`. The head block
`G=[[1,1],[1,0]]` is not self-inverse. The actual N1 shear
`A=[[1,1],[0,1]]` satisfies `A G A^T=G`, whereas `A^T G A=I`; the wrong
convention would therefore exclude an already realized automorphism.
With column zero equal to `e_0`, writing `G=E00+J` gives
`Abar J Abar^T=J`, the expected commutator-coefficient equality. The
explicit uniform square/commutator expansion below is still required.
The proposed target remains an actual continuous `NFrameModel h`
automorphism for `alpha >= 2`, preserving orientation and the full mod-two
cup form. No preservation of `nu` is imposed: this stabilizer is intended
to change `nu`. None of this proposed continuation is claimed proved.

Two adapters must actually be proved, not assumed:

1. Realize this arbitrary invertible integral matrix by a free continuous
   automorphism. `freeTwoCoordinateWord` gives generator images with the
   desired columns; a Frattini generation argument and Hopficity should
   promote the universal map. `FreeProTwoBasisCorrection` supplies the
   surrounding proof pattern, but its existing theorem only treats a
   known basis multiplied by depth-two corrections, not arbitrary matrices.
2. Prove that full mod-two cup preservation gives
   `r(y)*r(x)^(-1) in lambda_3`. For `alpha >= 2`, the degree-two relator is
   the head square plus the head commutator and all hyperbolic commutators.
   In `F/lambda_3`, depth-two elements are central of exponent two, so
   uniform square/commutator expansion should identify its transformed
   coefficients with the preserved cup matrix. The existing
   `FreeProTwoUnitPower.nInitialUnitPowerError_mem_three` proves only the
   particular unit-power case. Existing degree-two **spanning** statements
   alone do not justify the required equality. An explicit class-two
   expansion, or a proved separating coefficient model, is the actual
   missing initial-depth interface. This is one uniform degree-two lemma,
   not a request for successively higher nilpotency-class experiments.

Exact head-column agreement also guarantees the full ordinary relator row
matches the original target (`NPlaneOrdinaryHead.nRelWord_ordinary_row`).
Thereafter `NPlaneAmbientStage.exists_ambient_stage` already supplies every
unrestricted correction for every orientation-compatible current basis.
The generalized row refinement above can preserve the arbitrary matrix A
exactly; `exists_freeTwoBasisCorrection` supplies each new genuine basis.

### Exact full-row limit, not the existing plane-only limit

The present `NPlaneCompactness.nPlaneStageSet` records the particular
`nCoreMat T` ordinary action, orientation, Frattini generation, and relator
depth. Its theorem cannot simply be cited for a different full matrix.
A new stage set should instead require exact values
`nPhiHom(abMk(m_i))=prescribedColumn_i` for every generator, including its
torsion coordinate. These are closed conditions by `continuous_nPhiHom`.
The nesting, compact intersection, separated filtration, `nLiftHom`,
surjectivity, and Hopficity proofs then have the same form as
`NPlaneCompactness.lean:64`–153.

The free-stage transfer must retain these full coordinates. Exact integral
free coordinates control every ordinary row;
`FreeProTwoModTwoCharacters.freeTwo_modTwo_character_eq_of_coordinate_modTwo`
controls the torsion character after projection. This is stronger than the
current `NPlaneFreeStageTransfer.nPlaneStageSet_of_free_exact_stage`, which
only exports the plane-stage predicate. Generation can still be transferred
from the actual free automorphism and surjective quotient map.

No counterexample to this proposed extension was found in the bounded
assessment. Nonetheless all three new packages—arbitrary-basis row
interpolation, initial matrix/depth-three realization, and full-row stage
compactness/transfer—remain **unimplemented and unproved as assembled
theorems** in this snapshot. They should not be counted as completed merely
because their individual proof ingredients are largely present.

## Historical inventory (superseded where noted above)

The following was the state before locating and instantiating the general
even criterion. It explains the old proposed restricted-kernel route, but is
not the current remaining-work list.

### Earlier conclusion

No unconditional arbitrary-rank N reachability theorem was found in the
current tree. The new actual derivative, kernel tuples, exact row correction,
and compactness results do not themselves prove that an arbitrary current
relator defect belongs to the derivative image.

There is, however, no additional crossed-derivation hypothesis to obtain for
the actual defect once the current marking has the exact canonical orientation
rows. That fact is now kernel-checked in `NPlaneCrossedDefect.lean`.

## The remaining stage statement, without hidden row restrictions

Use these actual existing objects:

```
I = Fin (coreRank h)
F = FreeTwoRank (coreRank h)
x = freeTwoRankGen (coreRank h)
chi = freeNOrientation alpha h
r(m) = nRelWord alpha m
lambda_j = twoCentralSeries F j
```

A sufficient **unrestricted** stage theorem, still to be proved, is:

```
alpha >= 2, j >= 3,
e : ContinuousMulEquiv F F,
forall z, chi(e z) = chi z,
y_i = e(x_i),
epsilon = r(y) * r(x)^(-1),
epsilon in lambda_j
  imply
exists t : I -> F,
  (forall i, t_i in lambda_(j-1) and chi(t_i)=1) and
  r(i -> y_i*t_i) * r(x)^(-1) in lambda_(j+1).
```

No assertion that the t_i have zero ordinary rows belongs in this theorem.
That is the subsequent relative refinement supplied by derivative-kernel row
correction. Nor does the hypothesis merely assume a tuple generates modulo
some finite level: the displayed e supplies an actual free basis.

Equivalently, at the current depth the unresolved conclusion is an actual
preimage of the inverse error under `nFilteredDerivative`, with correction
entries in the image of `ker chi intersect lambda_(j-1)`. The checked shift
formula then gives the displayed next-stage conclusion. The factor order is
consistent with the repository convention: the error is `r(y)*r(x)^(-1)`;
the derivative is central in the top layer, so its inverse cancels this error.

One may instead prove a stronger standalone image theorem for an arbitrary
`epsilon in ker chi intersect lambda_j` annihilated by every continuous
chi-crossed derivation. This is a mathematical target, not an existing local
theorem or a new axiom in the development.

## Crossed annihilation is now derived, not carried

`MarkedCore/Certificate.lean:nRelWord_nMasterMark` already proves the N-word
identity at every handle rank for every tuple of derivation coordinates.
The new `MarkedCore/NPlaneCrossedDefect.lean` exposes its direct consequence:

```
Phi : F ->* WordLift Z2 Z2Units
(Phi z).g = chi z
chi(y_i) = chi(x_i) for every i
  imply
Phi (r(y)*r(x)^(-1)) = 1.
```

The statement actually holds for all monoid homomorphisms with the displayed
base condition; hence it covers the continuous crossed-derivation lifts in
particular. It needs neither a basis hypothesis nor a filtration hypothesis,
and is valid already for alpha at least one. Both the first-jet and base
coordinates vanish; this is not merely an ordinary-abelianization calculation.
The new module has four public pins, each exactly standard-three, and was
compiled and cached at default limits without warnings.

Being a basis by itself does **not** imply this annihilation: its canonical
orientation rows are used. Conversely, the annihilation just proved does not
by itself produce a derivative preimage without an image/span theorem.

## Existing reachability candidates and their actual scopes

- `Roe/Labute/StageLemma/StageOne.lean:stageSL1R0` and `stageSL1R2` are for
  three-generator tuples in the fixed DR and D0 quotients. Their hypotheses
  include their own orientation-compatible stage sets.
- `StageLemma/Defect.lean:span_free_r0`, `span_free_r2` and their descent
  theorems use the rank-three `freeProTwo` and the specific R0/R2 derivative
  words and tail pairs. They are not polymorphic in the N alphabet or N
  head derivative.
- The older even-stage route has N-labelled wrappers, but
  `StageAbstractionEvenClimbFinal.evenClimbFinal_residualSupplyN` explicitly
  carries a derivation-family supply and a raw-to-bracket upgrade. The
  per-field wrapper preserves these hypotheses. It is not the missing
  unconditional free-N span theorem.
- `NPlaneFilteredDerivative` supplies the actual N shift, all-rank and at
  every depth at least three. `NPlaneFilteredDerivativeLinear` supplies
  multiplicativity on the correction domain. Neither supplies surjectivity.
- `FreeProTwoUnitPower` supplies the genuine initial free automorphism and
  its depth-three error. `FreeNOrientation` identifies ker chi with the exact
  b-coordinate kernel. `NPlaneCrossedDefect` supplies the error's crossed
  annihilation. These are valid inputs to, not replacements for, reachability.
- The mixed-group tuple and its zero derivative control choices **within** a
  derivative fiber. A large kernel, including every required ordinary row,
  does not prove that a specified fiber is nonempty.

## Primary-source match and economical formalization target

Labute's section 4.1, Lemmas 2–4, provides the relevant mathematical pattern:
an orientation-kernel graded span, followed by crossed functionals separating
the remaining pure-power classes. It is this local image argument—not the
unmarked classification conclusion—that should be formalized. The source
does not impose simultaneous vanishing of ordinary rows on its corrections.
[Labute, *Classification of Demushkin Groups*, printed pp. 124–126](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/3045C3866BBC24C718D94C18F8F68E58/S0008414X00054158a.pdf/classification-of-demushkin-groups.pdf).

A suitable next development is a direct actual-quotient N span theorem:
the image of `ker chi intersect lambda_j` is generated by the unrestricted
N derivative image and the classes of `x_v^(2^(j-1))` for `v != b`.
The new exact b-coordinate description supports the orientation-kernel
filtration step. The remaining finite pure-power coefficients must then be
eliminated using genuine coordinate crossed derivations, not ordinary
characters. Existing finite WordLift/digit tools offer reusable infrastructure,
but their rank-three separation proofs are not already a general N theorem.

This is a uniform span/image task, not a request for more nilpotency-class
computations. The actual source files and the statement above keep the gap
visible; none asserts `NPlaneScalingHypothesis`.
