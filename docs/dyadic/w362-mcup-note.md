# W362-MCUP lane note

> **W363-MCONSOL rename.** `MFullFrameStages`'s five-hypothesis composition
> shape, called `mFullStabilizer_lift` when this note was written, is now
> `mFullStabilizer_lift_of_interfaces`. The plain name `mFullStabilizer_lift`
> now belongs to the unconditional theorem in `MFullStabilizerLift.lean`
> (whose earlier spelling `mFullStabilizer_lift_of_frame` is kept as an alias).
> Read every bare `mFullStabilizer_lift` below as
> `mFullStabilizer_lift_of_interfaces`.


Lane: M full-stabilizer lifting, step 4 of 5 (the initial depth-three and cup
comparison adapter at M). Branch `claude/w362-mcup`, base `6770a87e`.
Route item 4 of `docs/dyadic/w361-m-next-general-scaffold.md`.

Two new modules, no existing module edited, `GQ2.lean` untouched.
Verification of record: `bash scripts/w361_lean_runner.sh` for the first module
and `scripts/mirror.sh sweep` / `gen GQ2.Dyadic.MarkedCore.MInitialCupDepth` /
`check GQ2/Dyadic/MarkedCore/MFrameCupCoordinates.lean` for the second.
Default limits (200000 heartbeats), `autoImplicit=false`, no `sorry`, no
`native_decide`, no new axiom, no resource option. Every one of the 25
declarations is std-3 (`propext`, `Classical.choice`, `Quot.sound`), pinned
in file by `#print axioms`.

`claude/w362-mstages` is merged into this branch, so
`MFrameCupCoordinates.lean` imports the sibling `MFullFrameCompactness.lean`
and reuses its `mStageOneLe` and `mStageProjection` rather than keeping private
copies. There is no import cycle: no MSTAGES module imports either module of
this lane.

## `GQ2/Dyadic/MarkedCore/MInitialCupDepth.lean` (T2) -- 9 declarations

The M word is `A^2 [A,B] C^(2^alpha) [C,D]` times the handles, so it is not a
text substitution of the N word. Two M-specific facts replace the N head
argument, and both use `alpha >= 2`:

- `mCupPow_eq_one` -- every element of the class-two quotient is killed by
  `2 ^ alpha` once `alpha >= 2`, so the actual `C^(2^alpha)` block disappears
  there;
- `mCupSq_eq_of_zLayer`, `mCupSq_levelMk_eq_of_mem_two` -- the surviving head is
  a **square**, and a square in the class-two quotient depends only on the class
  of its base modulo lambda-two.

Consequently the M head hypothesis is the weak one, agreement modulo
lambda-two, not the literal generator fixing the N theorem uses.

The MINIT interface is **discharged, not assumed**:

- `mCupPowHalf_mem_two` -- for `alpha >= 2`, `g ^ (2^(alpha-1))` lies in
  lambda-two (this is the exact sense of "the change from `A` to
  `T = A * C^(2^(alpha-1))` is trivial mod two"; it fails at `alpha = 1`);
- `mCupHead_mem_two_of_fixed_T` -- if a lift fixes `T` literally then its `A`
  image agrees with `A` modulo lambda-two, whatever it does to `C`.

Shape assumed from MINIT, and nothing more: the free-basis tuple `m` with
`m 0 * m 2 ^ 2 ^ (alpha - 1) = m' 0 * m' 2 ^ 2 ^ (alpha - 1)` (fixed `T`), or,
in the weaker primitive form, `m 0 * (m' 0)⁻¹ ∈ twoCentralSeries _ 2`.

Deliverables:

- `mCupRelWord_levelMk_eq_head_mul_tail` -- the exact class-two shape of the M
  relator: head square times the **same** commutator tail the N calculation
  controls;
- `mCupRelWord_level_three_eq` -- actual quotient equality of the two M
  relators;
- `mCupRelWord_error_mem_three` -- actual error membership
  `mRelWord alpha m * (mRelWord alpha m')⁻¹ ∈ twoCentralSeries _ 3`;
- `mCupRelWord_error_mem_three_of_fixed_T` -- the same with the fixed-`T`
  hypothesis in place of the mod-two one.

The commutator tail is **not** reproved. `NInitialCupDepth.freeTail_eq_of_cup`
(bracket expansion plus symmetric contraction) and
`NInitialCupDepth.freeTail_value` are used verbatim, as is
`NInitialCupDepth.reducedRows`. `NInitialCupDepth`'s final N-relator theorem is
not used and is not claimed to be an M theorem.

## `GQ2/Dyadic/MarkedCore/MFrameCupCoordinates.lean` (T1, T3) -- 16 declarations

`MCupFrameCupIsometry` is the semantic character-pair predicate: it quantifies
over **every** continuous mod-two character of the actual full M frame,
torsion coordinate included, and assumes no group lift and no matrix.

Two M-specific points, checked rather than copied:

- the relator obligation of a frame coordinate character is the M one,
  `m 0 ^ 2 * m 2 ^ (2 ^ alpha) = 1`, not the N one; it holds for every mod-two
  coordinate marking including the `C` index `i = 2`, because squares are
  trivial in `Multiplicative (ZMod 2)` and `2 ^ alpha` is even
  (`mCupFrameCoordinate_head_relation`). So all `4 + 2h` mod-two coordinates of
  the M frame genuinely are characters;
- the **variance**. `NInitialCupDepth.reducedRows m i j` is coordinate `i` of the
  image of generator `j`, so the matrix has **columns = images** and the system
  proved is `Abar G Abar^T = G`. `MarkedCore/Variance.lean` is the dictionary:
  `M.lean` stores frame images in rows and therefore writes the same condition
  as `Mbar^T G Mbar = G`. The Gram is literally shared (`mGram_eq_nGram`, and
  `evenCupForm` is the Gram of both rows via
  `obsH2_evenModel_mNatWord_characterCup`), so no M-specific Gram appears.

Deliverables:

- `mCupFrameOfDM`, `mCupFrameCanonicalMark`, `mCupFreeFrameProjection`,
  `mCupFreeFrameProjection_apply` -- the actual frame of the core, its canonical
  columns, and the composite free cover over the sibling `mStageProjection`;
- `mCupFrameModTwoCoordinate`, `_canonicalMark`, `_projection` -- the frame
  mod-two coordinates and their exact pullback to the reduced free coordinates,
  on every free element;
- `MCupFrameCupIsometry.reducedRows_of_projection` (**T1**) -- the semantic
  predicate implies the exact reduced-coordinate cup equations for any free
  tuple projecting to the prescribed frame columns;
- `mCupRelWord_error_mem_three_of_frame`,
  `mCupRelWord_error_mem_three_of_frame_fixedT` -- T1 composed with T2, end to
  end from the semantic predicate to lambda-three error membership;
- `mCupStageError_of_frame` -- the seam with MSTAGES: verbatim
  `MFullFrameStages.mFullStabilizer_lift`'s `herror0`, from verbatim its
  `hframe0` and its `hT` (`mStageTorsionWord` fixation, written out). Checked by
  composing it into `mFullStabilizer_lift` in a scratch theorem that elaborates
  with no residual goal and is std-3. That theorem's orientation hypothesis
  `hchi0` is **not** needed for the depth-three step, so this statement omits it
  and is the stronger one;
- `mCupFrameCupIsometry_of_aut` (**T3**) -- the converse ingredient: any
  continuous automorphism of the actual core `D_M` whose frame action is `phi`
  makes `phi` a cup isometry. Proved through `dmObs` and uniqueness of the
  one-dimensional degree-two obstruction
  (`M0C0PivotAutomorphism.evenCupForm_comp_dm_aut`), with no coordinate
  computation and no matrix.

## The seam with the sibling lanes

`mFullStabilizer_lift` consumes, from this lane, exactly

```text
mRelWord alpha (fun i => e0 (freeTwoRankGen (coreRank h) i)) *
  (mRelWord alpha (freeTwoRankGen (coreRank h)))⁻¹
    ∈ twoCentralSeries (FreeTwoRank (coreRank h)) 3
```

and `mCupStageError_of_frame` produces exactly that, given `e0` fixing
`mStageTorsionWord alpha` and inducing `phi` on the full frame, plus
`MCupFrameCupIsometry ha phi`. The remaining MINIT obligation is therefore to
construct such an `e0` and to supply `MCupFrameCupIsometry ha phi` for the
`phi` being lifted; `mCupFrameCupIsometry_of_aut` supplies the latter in the
converse direction only.

## What remains

- The N file also specializes its coordinate theorem along `nFrameLiftEquiv`
  (`NFrameCupCoordinates.nFrameLiftEquiv_cup`). The M twin needs
  `mFrameLiftEquiv`, which lives in the sibling lane's
  `MarkedCore/MFrameMatrixLift.lean`; the hypothesis
  `hproj : ∀ k, mCupFreeFrameProjection ha h (m k) = phi (mCupFrameCanonicalMark ha h k)`
  is precisely the interface that lane has to supply, and
  `mCupFreeFrameProjection_gen` is the reference instance of it.
- The fixed-`T` hypothesis
  `m 0 * m 2 ^ 2 ^ (alpha - 1) = m' 0 * m' 2 ^ 2 ^ (alpha - 1)`
  is an input here. MINIT owes it for the lift it constructs; this lane proves
  only that it suffices.
- No iff is asserted. T3 is the converse **ingredient**; assembling it with the
  forward direction into `mFullStabilizer_lift_iff` is step 5, not step 4.
- Nothing here is claimed at `alpha = 1`: both `mCupPow_eq_one` and
  `mCupPowHalf_mem_two` fail there.
