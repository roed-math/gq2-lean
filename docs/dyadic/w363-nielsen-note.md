# W363-NIELSEN: the packet's finite Nielsen-generator artifact at the rank-four M core

> **Overtaken by W364-NFACTOR, recorded by W364-HOUSE at `d2056503`.** The
> section "The N side (MC-N)" below reports, as a finding, that the MC-N finite
> list cannot be produced because `nNielsen_factorization` and `nFamN1` through
> `nFamN6` exist nowhere under `GQ2/`. That was true when this note was written.
> W364-NFACTOR built all of them, in
> `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean`: the six families at `:138`
> to `:158`, `nNielsen_factorization` at `:357`, and the MC-N artifact
> `nNielsenFac_finite_list` at `:758`. Read that section as a record of what was
> missing, not of what is. Nothing else in this note is superseded, and the
> N-side bridge it delivered is exactly what W364 consumed.
>
> The same non-existence claim is still live in
> `GQ2/Dyadic/MarkedCore/NNielsenGenerators.lean`'s module docstring, lines
> 14-22, which no lane has been able to edit. See finding H1 of
> `docs/dyadic/w364-house-note.md`.

Lane W363-NIELSEN of the general-K campaign. Base `69b9851c`, branch
`claude/w363-nielsen`. New modules: `GQ2/Dyadic/MarkedCore/MNielsenGenerators.lean`
(70 declarations) and `GQ2/Dyadic/MarkedCore/NNielsenGenerators.lean` (16), all std-3.
No existing module was edited; `GQ2.lean` untouched.

## What the packet asks for

`docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` lines 1077-1082, row
**MC-M** (and **MC-N**, the same criterion at the N core):

> **MC-M** Marked automorphism lifting for the rank-four `M_alpha` core. A finite list of
> orientation-preserving Nielsen generators lifts the Smith-Witt stabilizer on the
> abelianization; composition gives every required marking correction.

Both rows are explicitly **rank-four** (`h = 0`). This note is about `h = 0` and
`alpha >= 2` throughout; see "Handles" below.

## What this lane produced

### The headline

`mNielsenGen_finite_list (ha : 2 <= alpha) (p : MStabParam)`. For every rank-four
stabilizer parameter there exist `k b5 e5 c6 d7 : Z_2` and `beta4 : Z_2^x` such that the
explicit seven-element list

```
mNielsenGenList ha p.gamma k b5 e5 beta4 c6 d7
  = [mNielsenGenM3 p.gamma, mNielsenGenM1 ha k, mNielsenGenM5 b5, mNielsenGenM2 e5,
     mNielsenGenM4 beta4, mNielsenGenM6 c6, mNielsenGenM7 d7]
```

of continuous automorphisms of the actual full M frame `MFrameModel 0` satisfies

1. `length = 7`;
2. every member preserves `mFrameOrientation` and satisfies `MCupFrameCupIsometry`, and
   therefore **lifts**: there is a `Psi : ContinuousMulEquiv (DM alpha 0) (DM alpha 0)` with
   `chiM alpha 0 (Psi x) = chiM alpha 0 x` for all `x` and the exact all-element commuting
   frame square;
3. the composite of the list (leftmost applied first) is the frame action of `p`;
4. the composite of the lifts is a lift of that composite.

`mNielsenGen_param_realized` is (4) with the list projected away: **every classified
rank-four stabilizer parameter is realized by an actual `chiM`-preserving continuous
automorphism of `D_M`**, with the exact frame square.

`mNielsenGen_stabilizer_induced` is the same with the packet's own quantifier. Given the
canonical rank-four frame `mNielsenGenFrame ha` and an orientation character `chi` with the
four pinned generator values, **every** `xi` satisfying `IsMStabilizer` (that is, every
element of the Smith-Witt stabilizer of `D_M^ab`) is induced by an actual `chiM`-preserving
continuous automorphism `Psi` of `D_M`, with the exact square `abMk (Psi x) = xi (abMk x)`.
The step from "every `MStabParam`" to "every stabilizer element" is
`mNielsenGen_frameAction_of_realizes`, which identifies the frame automorphism that
`mStabilizer_classification` classifies with `mNielsenGenMap` at its parameter. It is proved
by hom-extensionality on `MFrameModel 0` (the canonical marks generate it topologically,
`mNielsenGen_frame_hom_ext`) against `MStabParam.Realizes`'s three rows plus the forced
`A`-row `mStabilizer_A_row`.

### The bridge (ticket T1), which was the real work

`M.lean`'s classification `mStabilizer_classification` and factorization
`mNielsen_factorization` speak of `MStabParam.act`, a map on coordinate 4-tuples in the
row convention. Wave 362's `mFullStabilizer_lift_of_frame` wants a
`ContinuousMulEquiv (MFrameModel h) (MFrameModel h)` satisfying

* `forall z, mFrameOrientation ha h (phi z) = mFrameOrientation ha h z`, and
* `MCupFrameCupIsometry ha phi`, which quantifies over **all** continuous mod-two
  characters of the frame.

Both are discharged here for **every** `MStabParam`:

* `mNielsenGen_orientation` is immediate from `mFrameOrientation_preserved_iff`: the
  integral `B` parity survives because `beta` is a unit and the `C` and `D` contributions
  are even, and the integral `D` coordinate is fixed outright.
* `mNielsenGen_cupIsometry` needed new machinery. The repo had **no** producer of
  `MCupFrameCupIsometry` other than `mCupFrameCupIsometry_of_aut` ("it comes from an
  actual core automorphism"), which is exactly what is unavailable for families M4 to M7.
  So the semantic predicate is reduced here to a finite `F2` matrix check:
  - `mNielsenGen_coord_zero` through `mNielsenGen_coord_three` read the four mod-two frame
    coordinates off an arbitrary frame element. The forced `A`-row correction
    `2^(alpha-1)` is invisible mod two once `alpha >= 2`; that is where the binder is used.
  - `mNielsenGen_character_apply` expands an arbitrary continuous mod-two character in
    those coordinates, by pushing the free pro-two coordinate expansion
    `freeTwo_commutative_hom_coordinates` through the surjection
    `mCupFreeFrameProjection`.
  - `mNielsenGen_image_coord_zero/one/two/three` compute the reduced **column-convention**
    matrix of a parameter straight from the semantics, and `mNielsenGen_cup_core` is the
    resulting finite check (`decide` over `ZMod 2`).

  `MarkedCore/Variance.lean` is therefore **not a proof input**: no PROOF here uses the
  row-convention `mFrameMatrix` (it is in the import closure, and `IsMStabilizer` unfolds to it,
  so the earlier wording "nothing here reads it" was literally false; W364-AUDIT2 confirmed the
  substantive claim entry by entry, including the predicted transpose of `mFrameMatrix_of_realizes`),
  so no transposition has to be arranged. The matrix that
  comes out,

  ```
  column of t   (1, 0, 0, 0)
  column of B   (tau, 1, parity B_c, 0)
  column of C   (0, 0, 1, 0)
  column of D   (parity B_c, 0, parity e, 1)
  ```

  is the transpose of `mFrameMatrix_of_realizes`'s, exactly as that dictionary predicts.

### Supporting pieces

* `mNielsenGenMap` carries `MStabParam.act` onto `MFrameModel 0` (the empty handle tail
  rides along untouched); it is multiplicative and continuous.
* Each of `mFamM1` through `mFamM7` has an explicit inverse **inside its own family**
  (negate the parameter, or invert the unit), so `mNielsenGenM1` through `mNielsenGenM7`
  are honest `ContinuousMulEquiv`s and not bare maps.
* `mNielsenGenLifts_trans` / `mNielsenGenLifts_compose`: the composite of lifts is a lift
  of the composite, for a list of any length.
* `mNielsenGen_nRed_eq_parity`: `N.lean`'s ring-hom reduction `nRed` and `M.lean`'s parity
  `mParityZ` are the same map. The two files had been using both without a bridge.

## What this does NOT do, relative to the packet wording

This is the part the owner has to adjudicate.

1. **The lifts are not generator-level constructions.** The packet sentence reads most
   naturally as "there is a finite list of generators, each of which is *exhibited* as an
   automorphism of the core, and composition gives the rest". What is proved here is that
   each of the seven families lifts **by wave 362's `mFullStabilizer_lift_of_frame`**, i.e.
   by the uniform filtered-correction and compactness argument of waves 361/362. No
   generator is lifted by an explicit group-level construction in this file, and none is
   claimed to be. Codex's warning in `docs/dyadic/w361-claude-code-handoff.md` section 3
   ("Do not call the finite-list artifact done") is respected: the compactness proof is
   **not** relabelled as a finite-list proof. What is new is a genuinely different object,
   the finite list itself, plus the fact that each of its members satisfies the two
   hypotheses of the compactness theorem.

   Two of the seven families do have honest independent group-level lifts elsewhere in the
   repo: **M1** is `M.lean`'s `mLambdaEquiv` and **M2** is HM4's `dmTauDEquiv`. **M3** is
   the S2 unit scaling, built in `MarkedCore/MScaling.lean` at handle level zero.
   **M4, M5, M6, M7** are the S3 residue and have no group-level construction anywhere in
   the repo. If the owner reads the packet sentence as demanding generator-level lifts,
   the outstanding work is exactly those four families.
   [W364 correction (packet lane, verified at the Lean): M5 DOES have `mMixFamily_coreMix`
   (`CoreMixM.lean:304`), the pure M5 move at every parameter and every `h`, though stated on
   `Z_2`-valued characters and so not pinning the torsion coordinate; and M3's only route
   (`MScaling`) consumes the standing input B8. The Option-B work list is therefore M4, M6, M7
   outright, M5's torsion pin, an M assembly theorem, and M3 without B8; see
   `w364-proof-packet-amendment-mc.md`.]

2. **The orientation character is an abstract one with pinned generator values.**
   `mNielsenGen_stabilizer_induced` takes `chi` together with `hchiA` to `hchiD`, exactly as
   `mStabilizer_classification` does; it does not construct a descended `chiMab` and prove
   that clause redundant. That is `M.lean`'s own recorded finding 6, inherited here, not a
   new gap.

   (The gap this note flagged at first draft, that "every stabilizer element" was quantified
   as "every `MStabParam`", is **closed**: see `mNielsenGen_frameAction_of_realizes` and
   `mNielsenGen_stabilizer_induced` above.)

3. **The list is a list of seven family *members*, not seven *families*.** The seven
   families are each parameterized by a 2-adic number or unit; what the theorem produces
   for a given `p` is one member of each family. That is what "a finite list of Nielsen
   generators ... composition gives every required marking correction" should mean for a
   pro-2 group (a literally finite generating *set* is impossible: the stabilizer is not
   finitely generated as an abstract group), but it is worth saying out loud.

## Handles (`h > 0`)

They do **not** fall out for free, and the packet does not ask for them in this row.

* The *lifting* half is already general in `h`: `mFullStabilizer_lift_of_frame` and
  `nFullStabilizer_lift` both allow handles to mix arbitrarily.
* The *finite list* half is rank-four because its two inputs are:
  `mStabilizer_classification` and `mNielsen_factorization` are both stated for
  `DM alpha 0` only.
* What would be needed at `h > 0` is a classification of the full-frame stabilizer
  including the handle block -- the handle-mixing generators (`GL` of the `2h`-dimensional
  handle block, plus the core-handle shears) on top of the seven core families. No such
  classification exists in the repo.
* A weaker statement is within easy reach and is *not* claimed here: the seven core
  families, extended by the identity on the handle tail, still preserve orientation and
  cup at every `h`, hence still lift. The coordinate and character machinery in this file
  (`mNielsenGen_coord_*`, `mNielsenGen_character_apply`) is already stated at general `h`;
  only the final `evenCupForm` expansion is specialised to `h = 0`.

## The N side (MC-N)

**The N-side finite list cannot be produced, because the N-side factorization does not
exist in the repo.** This is a finding, not a deferral [W364: superseded the same session by
W364-NFACTOR, which built `nNielsen_factorization` (eight slots) and `nNielsenFac_finite_list`
in `MarkedCore/NNielsenFactorization.lean`; the lifting half delivered below is what it consumes]:

* `N.lean` has `nStabilizer_classification` (`IsNStab alpha R <-> ExistsUnique P,
  P.Admissible /\ P.rows = R`), with parameter type `NStabParam` carrying a full
  `2 x 2` matrix `g` over `Z_2` for the `(sigma, x2)` block.
* There is **no** `nNielsen_factorization` and there are **no** `nFamN1` ... `nFamN6`
  values anywhere in `GQ2/`. The six N families live only in the design memo
  `docs/dyadic/mc-design.md` section 3.4, as a table. The completeness argument sketched
  there ("N2/N3 generate `SL_2(Z_2)`, N4 supplies the determinant") is unformalized, and
  it is strictly more than the M side needed, because the M handle block is absent at
  rank four while the N `(sigma, x2)` block is a genuine `GL_2(Z_2)`.
* The only N-family artifact in the repo is `Variance.lean`'s `nMatOf_famN1_cupIsometry`,
  a single mod-two matrix check for family N1.

What this lane delivered on the N side instead is the **bridge**, which is the half that is
available and is exactly what the missing factorization would consume. Until now there was no
producer of the semantic predicate `NFrameCupIsometry` other than "it comes from an actual core
automorphism", which is precisely what one does not have for a family one is trying to lift.
`GQ2/Dyadic/MarkedCore/NNielsenGenerators.lean` supplies one from finite mod-two matrix data in
N's own column convention:

* `nNielsenGen_coord_zero` through `nNielsenGen_coord_three`: the four mod-two frame coordinates
  of an arbitrary frame element. Unlike M there is no forced `A`-row, so these are the bare
  reductions with no `2^(alpha-1)` correction.
* `nNielsenGen_character_apply`: the character expansion at N.
* `nNielsenGenMat ha phi i j`: the `i`-th mod-two coordinate of the image of the `j`-th
  canonical mark, exactly the shape of `NRows.mat`.
* `nNielsenGen_cup_of_mat`: `A G A^T = G` in that convention gives `NFrameCupIsometry`.
* `nNielsenGen_lift_of_mat`: with the integral `x1` coordinate fixed on the nose (which is
  `nFrameOrientation_preserved_iff`'s concrete form of orientation preservation), the frame
  automorphism lifts to a `chiN`-preserving continuous automorphism of `D_N` with the exact
  square.
* `nNielsenGen_lift_of_rows`: the same with the cup clause stated in `NRows.IsCupIsometry`
  vocabulary, so a consumer holding `nStabilizer_classification`'s clause can feed it directly.

The orientation clause at N is genuinely stronger than at M (the integral `x1` row is fixed,
where at M only the `B` parity is pinned); that asymmetry is the one already recorded in
`MFrameMatrixLift`.

**What the MC-N row still needs**: `nFamN1` through `nFamN6` as `NStabParam` values, and a
completeness theorem factoring an arbitrary admissible `NStabParam` through them. The hard part
is the `(sigma, x2)` block: the memo's argument is "elementary matrices generate `SL_2` over a
local ring, and N4 supplies the determinant", which has no counterpart on the M side and is not
in the repo.

## Verification

Every declaration in both modules prints `[propext, Classical.choice, Quot.sound]` (std-3),
pinned by a `#print axioms` at the end of each file. Checked with

```
bash scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/MNielsenGenerators.lean
bash scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/NNielsenGenerators.lean
```

against the shared cache at base `69b9851c`; no `lake` invocation, no `sorry`, no
`native_decide`, no resource options, no new axiom. Neither module imports the other, and
neither is registered in `GQ2.lean`.
