# W362-MINIT: the initial free lift at M, respecting the primitive relation

> **W363-MCONSOL rename.** `MFullFrameStages`'s five-hypothesis composition
> shape, called `mFullStabilizer_lift` when this note was written, is now
> `mFullStabilizer_lift_of_interfaces`. The plain name `mFullStabilizer_lift`
> now belongs to the unconditional theorem in `MFullStabilizerLift.lean`
> (whose earlier spelling `mFullStabilizer_lift_of_frame` is kept as an alias).
> Read every bare `mFullStabilizer_lift` below as
> `mFullStabilizer_lift_of_interfaces`.


Lane note, 2026-09-17. Module `GQ2/Dyadic/MarkedCore/MFrameMatrixLift.lean`
(namespace `GQ2.Dyadic.MarkedCore`, prefix `mFrame`), 111 declarations, every
one pinned in the file; all print the std-3 set
`[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, no
`native_decide`, no options, default heartbeats, `autoImplicit=false`.
Route item 3 of `docs/dyadic/w361-m-next-general-scaffold.md`.

Everything is at `2 ≤ alpha`, arbitrary handle count `h`, arbitrary frame
automorphism. Nothing is claimed at `alpha = 1`.

## Status: T1, T2, T3 landed as theorems; MSTAGES shapes supplied

### T2: the fixed-T free lift (`exists_mFrame_freeBasis_lift`)

From any `phi : ContinuousMulEquiv (MFrameModel h) (MFrameModel h)` with
`∀ z, mFrameOrientation hα h (phi z) = mFrameOrientation hα h z` (the actual
`chiM`, transported through `mFrameExists_phiEquiv`; equal to `MFrameApi`'s
`mFrameApiChiModel` by `mFrameOrientation_eq_apiChiModel`), the automorphism
`mFrameLiftEquiv hα h phi` of the free pro-two group has

* literal fixed head: `e (mFrameHead α h) = mFrameHead α h` where
  `mFrameHead α h = A * C^(2^(alpha-1))` (`mFrameLiftEquiv_head`);
* exact relation vector: `∀ j, ∑ i, coord_j (e X_i) * r_i = r_j` with
  `r = mFrameRelVec α = e_A + 2^(alpha-1) e_C` (`mFrameLiftEquiv_relVec`);
* exact frame square through `mPhiHom`:
  `mFrameProjection hα h (e x) = phi (mFrameProjection hα h x)` for every `x`
  (`mFrameLiftEquiv_projection`);
* orientation preserved on every element (`mFrameLiftEquiv_orientation`);
* exact coordinates: every column `i ≠ 0` is the canonical section
  `mFrameCoordinateSection α (phi (proj X_i))` (`= mSurjVec`), and the A column
  is `r - 2^(alpha-1) * (C column)` (`mFrameLiftEquiv_coordinate_gen_of_ne`,
  `mFrameLiftEquiv_coordinate_gen_zero`).

Construction: `mFrameLiftMark` sends `A ↦ T * (word_C)^(-m)` and every other
generator to the coordinate word of the canonical section of its frame image;
surjectivity through index-two quotients via `mCoordHom` and Frattini
(`surjective_of_forall_index_p_quotient_surjective`), then `profinite_hopfian`
and `continuousMulEquivOfBijective`, exactly as `NFrameMatrixLift`. The torsion
generator of the frame is fixed by `nFrameModel_map_t`, which applies verbatim
because `MFrameModel h` and `NFrameModel h` are the same abbreviation.

`mFrameOrientation_preserved_iff`: orientation preservation is exactly
preservation of `mParityZ` of the integral B slot and of the integral D slot
(`mChi_row_extract`), not of the integral B row as on N.

### T1: the basis change and the coordinate dictionary

* `mFrameBasisChange α h`: the actual free automorphism `A ↦ T = A * C^m`, others
  fixed, with explicit inverse `mFrameBasisChangeInvHom` (slot 0 to
  `X_0 * X_2^(-m)`, the inverse substitution `A = T * C^(-m)`), mutually inverse
  by `presPro2_hom_ext` (`mFrameBasisChangeHom_comp_inv`, `_InvHom_comp`).
* `mFrameHeadCoordinate α h j x := coord_j (basisChange.symm x)`, the
  `(T, B, C, D, handles)` coordinates. Dictionary:
  `mFrameHeadCoordinate α h j x = coord_j x - [j = 2] * 2^(alpha-1) * coord_0 x`
  (`mFrameHeadCoordinate_eq`); `mFrameBasisChange_coordinate` is the forward
  direction; `T` has T-coordinates `e_0` (`mFrameHeadCoordinate_head`).
* In T-coordinates the frame projection has the N shape
  (`mFrameProjection_headCoordinate`): torsion slot = T coordinate mod two,
  every other slot copied. In original coordinates it is `mPhiHom_word`'s
  change of coordinates (`mFrameProjection_coordinate`, for arbitrary elements,
  using `mFrameModel_isProP`).
* `mFrameRelVec_fixed_of_head_fixed`: any continuous hom fixing `T` satisfies
  `M r = r` exactly in the original integral coordinates.

The precise negative statement: `mFrameNaiveLiftMatrix hα h phi` is the literal
transcription of the N lift matrix (the canonical section applied to every
column, A and C included, independent torsion digits). Then

* `mFrameNaiveLiftMatrix_relVec`: `N r = (1 + 2^(alpha-1) * digit) r` where
  `digit ∈ {0, 1}` is the torsion coordinate of `phi(Cbar)`; a unit multiple, so
  the submodule `Z_2 r` is preserved but the vector is not;
* `mFrameNaiveLiftMatrix_relVec_iff`: `N r = r ↔ (phi(Cbar)).torsion = 0`;
* `mFrameTorsionShear h`: the frame automorphism `(ε,b,c,d,f) ↦ (ε + parity c,
  b, c, d, f)`, an involution, orientation preserving
  (`mFrameTorsionShear_orientation`), with `(shear(Cbar)).torsion = 1`;
* `mFrameNaiveLiftMatrix_torsionShear_not_relVec`: for it the independent
  sections do NOT fix `r`, while `mFrameLiftEquiv_relVec` does.

Remark (not proved here, not needed): at rank four the cup condition kills the
torsion coordinate of `phi(Cbar)` (`mStabilizer_classification`), so the naive
sections would happen to work under full-stabilizer hypotheses; the fixed-T lift
needs only the orientation.

### T3: the cup-side interface for MCUP

The lift does not fix `A` literally: `A⁻¹ * e(A) = C^m * (e C)^(-m)`.

* `mFrameLiftEquiv_gen_zero_mem_two`: `A⁻¹ * e(A) ∈ twoCentralSeries F 2`
  (both factors are `2^(alpha-1)`-th powers, `mFrame_pow_halfExp_mem_two`);
* `mFrameLiftEquiv_levelMk_two_gen_zero`: equality in the level-two quotient;
* `mFrameLiftEquiv_reduced_gen_zero`: `nRed (coord_j (e A)) = [j = 0]`, the
  reduced A column is the first standard basis vector exactly as for the N lift.

### The MSTAGES interface (coordinator request, after merging `claude/w362-mstages`)

`mFullStabilizer_lift` (`MFullFrameStages.lean`) takes `e0, hT, hchi0, hframe0`
from MINIT. Supplied:

* `mFrameLiftEquiv_torsionWord`: `mStageTorsionWord α (fun i => e0 (gen i)) =
  mStageTorsionWord α gen` (`mFrameHead α h = mStageTorsionWord α gen` by rfl);
* `mFrameLiftEquiv_stageOrientation`: `∀ i, mStageOrientation α h (e0 (gen i)) =
  mStageOrientation α h (gen i)` (via `mStageOrientation_eq_freeOrientation`);
* `mFrameLiftEquiv_stageFrame`: `∀ i, mPhiHom (mStageOneLe hα) h (abMk
  (mStageProjection α h (e0 (gen i)))) = phi (mPhiHom _ h (abMk (dmGen α h i)))`;
* `mStageInitialLift_of_fixedHead_error`: `MStageInitialLift hα h phi` from the
  orientation hypothesis and MCUP's depth-three relator error for this lift;
* `mFullStabilizer_lift_of_fixedHead`: the one-`exact` composition, still
  conditional on MCUP's `herror` and MKERNEL's `MStageStep`.

The module now uses MSTAGES's `mStageProjection` and `mStageOneLe` directly
(no duplicate free projection).

## What remains (not this lane)

* MCUP: the depth-three relator error of `mFrameLiftEquiv hα h phi` from the
  cup hypothesis, consuming `mFrameLiftEquiv_reduced_gen_zero` /
  `mFrameLiftEquiv_gen_zero_mem_two` and the exact columns.
* MKERNEL: `MStageStep α h`.
* Reading the orientation hypothesis off a cup-plus-orientation stabilizer
  predicate, if MCUP states one at the public boundary
  (`mFrameOrientation_eq_apiChiModel`, `mFrameOrientation_preserved_iff` are the
  bridges).

## Verification of record

The module imports `MFullFrameStages`, which is not yet in the shared cache, so
`scripts/w361_lean_runner.sh` cannot see it until the cache advances. Used:

```
scripts/mirror.sh sweep
scripts/mirror.sh gen GQ2.Dyadic.MarkedCore.MHeadCleanup
scripts/mirror.sh gen GQ2.Dyadic.MarkedCore.MFullFrameCompactness
scripts/mirror.sh gen GQ2.Dyadic.MarkedCore.MFullFrameStages
scripts/mirror.sh check GQ2/Dyadic/MarkedCore/MFrameMatrixLift.lean
```

Output: `OK`, 111 `#print axioms` lines, all std-3 or smaller, no warnings.
Before the MSTAGES rewire (commit `3b0a4254`) the module was verified with
`bash scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/MFrameMatrixLift.lean`
against the shared cache alone.
