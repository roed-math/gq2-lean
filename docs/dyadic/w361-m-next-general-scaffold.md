# W361: the next general M lifting task

2026-09-17. Targeted read-only source/specification map for the Claude handoff.
No new M theorem, source edit, or claim of MC-M closure is made here. Suggested
constructions below are research tasks, not additional hypotheses to assume.

## Target and existing boundary

The original packet §7, lines 732–735, asks for lifting every automorphism of
the **full** abelianization preserving orientation, the torsion relation and
the mod-two cup form. Its §14 additionally prescribes a finite Nielsen-family
construction. The newly proved `nFullStabilizer_lift_iff` supplies the N
mathematical assertion, but has no M conclusion.

For M, the inspected library already supplies:

| Checked interface | Exact scope |
|---|---|
| `mFrameExists_phiEquiv`, `mPhiHom_gen`, `mPhiHom_word` in `MFrameExists` | Actual all-rank topological abelianization and every coordinate; no assumed frame-existence binder. |
| `mStabilizer_classification` in `M` | Rank-four full-frame classification for `alpha >= 2`, into seven-parameter `MStabParam`. |
| `mNielsen_factorization` in `M` | Finite seven-family factorization **of the frame action**. This alone is not group-level lifting of those factors. |
| `mLambdaEquiv`, `dmTauDEquiv`; `dmRealizesWide_pureM5`, `mMixFamily_coreMix` in `CoreMixM` | Existing actual moves and their stated marking/ordinary-character behavior; inspect their exact conclusions before calling them a prescribed full torsion-sensitive frame action. |
| `mScaleHEquiv`, `chiM_mScaleHEquiv`, `mScaleHEquiv_C_row` in `MScalingHandles` | Actual all-rank orientation-preserving scaling, with the required C-row action on every ordinary Z₂ character. |
| `mScalingHypothesis`, `mMixHypothesis` in `MScalingHandles` | Complete marking-consumer discharge, using the standing `peripheralCyclotomicAction` input. The explicit-`R` variant `mScalingHypothesis_of_peripheral` retains that input as a parameter. |
| `mCoreOrientationCharacteristic_all` in `Instances/MOrientationCharacteristic` | Intrinsic M orientation rigidity is already proved; do not reopen it as a missing premise. |

`MScalingHypothesis` in `CoreMixM` deliberately specifies only the C row,
not all other rows. In particular `mScaleHNewU` is a conjugate of `U^u`:
this scaling construction changes ordinary handle-U rows when `u != 1`.
It cannot simply be relabelled the pure `mFamM3` core action extended by
identity handles. The rank-four B/D conjugators also require their own exact
coordinate analysis if pursuing the finite-family route. Likewise, a theorem
about every ordinary Z₂ character can still miss a torsion entry.

These distinctions do not reopen the completed selected-field theorem: its
required M marking consumers already have producers.

## M is not a text substitution for N

The literal relators and their ordinary rows are:

```text
N: A^(2+2^alpha) [A,B] [C,D] handles
   (2+2^alpha) f(A)
M: A^2 [A,B] C^(2^alpha) [C,D] handles
   2 f(A) + 2^alpha f(C).
```

For M put `m = 2^(alpha-1)`. Its primitive relation vector in the free
integral coordinates is `r = e_A + m e_C`; the relation submodule is `2 Z₂ r`.
The actual frame torsion generator is `t = Abar + m Cbar`, not `Abar`.
`mPhiHom_A` gives `(1,0,-m,0,0)`, whereas `mPhiHom_C` gives `(0,0,1,0,0)`.
The formula `mPhiHom_word` records precisely this change of coordinates.

The orientation is also different: on `(A,B,C,D)` it is
`(1,-1,1,mUnit alpha)`. `mChiModel_ofAdd` and `mChi_row_extract` say that
preserving it fixes B **parity** and the integral D coordinate. It does not
fix the integral B row as on N. Preserve the actual character through the
frame projection, not an invented stronger row condition.

The old M classification matrix stores generator images in **rows**;
`M.lean` uses `Mbarᵀ G Mbar = G`. New free matrix helpers store images in
**columns** and use `Abar G Abarᵀ = G`. `MarkedCore/Variance.lean` is the
existing dictionary. A semantic character-pair cup predicate, like
`NFrameCupIsometry`, is safer at the public boundary.

## A concrete arbitrary-basis route is available to investigate

There is no relation/torsion counterexample to full M lifting in this audit.
Several hard general ingredients already match exactly:

1. **The actual filtered derivative is shared.**
   `StageAbstractionEvenRawSpan.evenRawStageShift_m` and
   `evenRawStageShift_n` both identify the literal shift with
   `evenRawDbarWord`, for `alpha >= 2`, `k >= 3` and corrections of depth
   `k-1`. This is already a quotient-group identity, not only a graded analogy.
   The new N kernel tuples, their closed derivative-kernel subgroup and
   arbitrary-basis diagonal row witnesses can be reused once a small M
   preservation adapter identifies their derivative with this same word.
   `nBasisKernelWitness_mem` and `nBasisKernelWitness_row` already concern
   that actual free-group kernel; their names do not impose an N relator
   equation. Do not claim the N-specific relator conclusion of
   `exists_nBasis_allRows_same_kernelCoset` is itself an M theorem.
2. **The M crossed-model ingredients already exist.** `EvenFamilyConstruct`
   supplies `evenFam_mRelWord_wordLift`, `evenFamDerivModelM`, its `_gen` and
   `_isChiShadow` lemmas. `StageAbstractionEvenKernelAdapted` supplies
   `evenKernel_vM_sub_one_dvd_four` and
   `evenKernel_vM_diagonal_add_one_dvd_four`. They fit the existing
   `evenDeriv_mem_rawShiftSpan_of_forall_derivKer`. An M version of
   `NPlaneAmbientStage` should use the actual free-basis target-relative
   defect and these M models. It must not impose false relator death on the
   free tuple. The constant-one auxiliary `StageWord` only packages that
   tuple; both actual M words must separately die under the crossed maps.
3. **The initial free lift must respect the primitive relation.** Work first
   in the free basis `(T=A*C^m,B,C,D,handles)`, using the explicit inverse
   substitution `A=T*C^(-m)`. A canonical frame lift fixing T then preserves
   `r` exactly in the original integral coordinates. Choosing independent
   0/1 torsion sections for the original A and C columns does *not* by itself
   ensure this exact relation-vector property. Adapt the actual free-basis
   construction in `FreeProTwoMatrixBasis`/`NFrameMatrixLift`, not just its
   final Frattini matrix assertion.
4. **Initial depth-three and cup comparison need an M adapter.** For
   `alpha >= 2`, the change from A to T is trivial mod two, and `C^(2^alpha)`
   dies modulo lambda-three. The chosen lift need not fix A literally, but
   its A image agrees with A modulo lambda-two; in the class-two quotient
   that suffices for equality of their squares. The exact bracket expansion
   and symmetric contraction in `NInitialCupDepth` are reusable. Its final
   N-relator theorem is not directly the M theorem. Existing `dmObs`,
   `dmFrattiniCupForm`, `dmObs_injective` and `dmObs_surjective` provide the
   genuine cup interface and the ingredients for the converse.
5. **Later exact rows and compactness should retain the full frame.** Reuse
   generic free-basis persistence and continuous-character factorization.
   All-ordinary-character-zero corrections also kill any commutative
   pro-two character by `freeTwo_commutative_hom_coordinates`, including the
   actual M orientation. An M full-frame stage transfer and compactness
   wrapper must retain torsion, not merely the selected unramified marking.

This is a source-supported proof plan. The M adapters and their composition
have not been proved by this note, and no claim of a complete M route is made.

## Recommended first bounded Claude task

**Prove the coupled ordinary-head cleanup, then its same-class free-group
representative; do not start by duplicating the entire N campaign.**

Create a new additive M module. For `alpha >= 2`, `d >= 2`, arbitrary marking
`y`, corrections `t`, target, and continuous Z₂ character `f`, assume exact
ordinary agreement `f(mRelWord alpha y) = f(target)`, `t_C ∈ lambda_d`, and
the corrected defect lies in `lambda_(d+2)`. Prove

```text
2^d divides toAdd(f(t_A)).
```

The exact correction row is `2 f(t_A)+2^alpha f(t_C)`. Filtration divisibility
first gives `2^d | f(t_A)+2^(alpha-1) f(t_C)`. Since
`2^(d-1) | f(t_C)` and `alpha >= 2`, the second summand is already divisible
by `2^d`. This supplies the head digit without falsely setting the C row to
zero. With `t_A ∈ lambda_d`, apply
`exists_freeTwo_characterZero_same_twoCentralClass` coordinatewise to obtain
the exact all-character-zero head representative in its current graded class.

Acceptance for this first task: an actual M-word theorem, arbitrary rank and
target, no assumed derivative image, no added orientation/zero-C premise,
default Lean limits and explicit standard-three axiom pins. Then add the
small M derivative-kernel/slack adapter using `evenRawStageShift_m` and reuse
the already proved arbitrary-basis witnesses. Keep the initial primitive
relation-vector lift as a separately named task, not a hidden assumption.

## Guardrails for the handoff

- Do not infer unrestricted canonical-C placement from a full stabilizer
  lift. W341–W344 concern which marked fields the **old candidate word** can
  realize; these no-go results are not counterexamples to automorphism lifting.
  The strict-handle/changed-source alternative remains essential.
- The direct filtered M route may avoid invoking B8, but that is an aim,
  not a proved axiom-footprint result. Existing preferred M scaling already
  uses the explicitly approved peripheral input; do not silently erase it.
- No extrapolation to `alpha=1`: the derivative and mod-two basis-change
  arguments above use `alpha >= 2`.
- Do not confuse a complete mathematical lift with the packet's finite
  Nielsen-family display. The existing frame factorization helps the latter,
  but each asserted group lift still needs its exact full-coordinate equation.
- Preserve the verified 1,541-module snapshot and the subsequent N increment's
  separate verification boundary. This read-only scaffold adds only this note;
  it authorizes no frozen-word edit, new axiom, publication or release.
