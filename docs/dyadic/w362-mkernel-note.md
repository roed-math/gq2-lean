# W362-MKERNEL lane note: M derivative-kernel interpolation (arbitrary basis)

Lane of the gq2-lean general-K campaign, M full-stabilizer lifting step 2 of 5.
Branch `claude/w362-mkernel`, base `6770a87e`, Lean 4.31.0-rc2, shared cache.
Verification of record: `bash scripts/w361_lean_runner.sh <File.lean>` for the
first module and `scripts/mirror.sh gen` for the second; no `lake` is run here.

## Ticket

- T1: the M preservation adapter identifying the N kernel tuples' derivative
  with the shared word via `evenRawStageShift_m`, so the closed
  derivative-kernel subgroup and the arbitrary-basis row witnesses apply at
  the M word.
- T2: the M twin of the closed derivative-kernel interpolation of
  `NBasisRowRefinement` for an arbitrary basis (kill every ordinary row at
  depth `d` from a depth-`(d-1)` correction), with an M ambient-stage
  statement using the actual free-basis target-relative defect.
- T3: the named interface consumed by the stage lane (MSTAGES).

## Modules

### `GQ2/Dyadic/MarkedCore/MBasisRowRefinement.lean` (T1, T2 interpolation)

Imports `NBasisRowRefinement` and `StageAbstractionEvenRawSpan`. All in
namespace `GQ2.Dyadic.MarkedCore`, prefix `mBasis`.

| Declaration | Statement |
|---|---|
| `mBasis_nFilteredDerivative_eq_evenRawDbarWord` | `nFilteredDerivative m t = evenRawDbarWord m t` in `Q_(k+1)`, `k >= 3`, depth-`(k-1)` correction. Composite of `nFiltered_nRelWord` (at `alpha = 2`) and `evenRawStageShift_n`. |
| `mBasis_mFiltered_mRelWord` | **T1.** `mRelWord alpha (m*t) = mRelWord alpha m * nFilteredDerivative m t` in `Q_(k+1)`, `alpha >= 2`, `k >= 3`. From `evenRawStageShift_m`. |
| `mBasis_relator_shift` | The same on the actual group, projected by `levelMk G (k+1)`. |
| `mBasis_mem_nPlaneCorrectionKernel_iff_mError` | `t ∈ nPlaneCorrectionKernel k hk m ↔ depth (k-1) ∧ (mRelWord alpha m)⁻¹ * mRelWord alpha (m*t) ∈ lambda_(k+1)`. |
| `mBasis_mRelWord_mul_correctionKernel` | Right multiplication by the closed kernel keeps the M relator value in `Q_(k+1)`. |
| `mBasis_mRelWord_defect_mul_correctionKernel_iff` | The same for the target-relative defect, arbitrary target. |
| `mBasis_mRelWord_correction_level_congr`, `_defect_mem_iff` | Top-layer slack invariance of the M relator (from the committed `mStageWord.zshift`), `alpha >= 1`. |
| `exists_mBasis_allRows_same_kernelCoset` | **T2 interpolation.** Head rows zero, depth `n+2` tuple: an all-row-zero representative in the same `nPlaneCorrectionKernel (n+3)` coset, same depth, same M relator value in `Q_(n+4)`. |

What transfers verbatim at the M word: `nPlaneCorrectionKernel`, its
closedness, `nBasisKernelWitness_mem`, `nBasisKernelWitness_row`, and the
generic finite interpolation `exists_closedSubgroup_rowZero_same_coset_fintype`.
What does not: the relator conclusion of `exists_nBasis_allRows_same_kernelCoset`
(an N equation) is replaced, not reused; the head row `t 0` is not killed by
the kernel (the kernel witnesses exist only at `i ≠ 0`).

### `GQ2/Dyadic/MarkedCore/MPlaneAmbientStage.lean` (T2 ambient stage, T3)

Imports `MBasisRowRefinement` and `NPlaneAmbientStage` (for the constant-one
`oneWord`, `free_finite_gen`, `basis_generates`).

| Declaration | Statement |
|---|---|
| `mBasisProjection`, `_gen` | Free rank-`coreRank h` group onto `DM alpha h`, generator to generator. |
| `mBasisOrientation`, `_gen`, `mBasisProjection_orientation` | `chiM` pulled back along the projection; generator values `vM alpha`. |
| `mBasisOrientation_aut`, `mBasisOrientation_eq_one_of_coordinates` | Generator preservation extends; all coordinates zero forces orientation one. |
| `mBasisCoordinateDeriv`, `_gen`, `_base`, `_defect` | The `evenFamDerivModelM` crossed maps on an arbitrary basis; `chiM`-shadowed; both actual M words die separately (`mBasis_finite_mRelWord_eq_one`). |
| `mBasisTuple`, `mBasisFamily` | The constant-one-word tuple and its derivation family at the `vM` table. |
| `mBasis_defect_mem_rawSpan` | The actual free-basis target-relative M defect in `lambda_k` lies in the raw shift span (`evenKernel_vM_*` inputs). |
| `mBasis_exists_ambient_stage` | **T2 ambient stage.** Orientation-compatible basis, defect in `lambda_k` (`k >= 3`): a depth-`(k-1)` correction with defect in `lambda_(k+1)`. Uses `evenRawStageShift_m`. |
| `MBasisAmbientStageSupply`, `mBasisAmbientStageSupply` | The same in the stage indexing `n+3 -> n+4`; proved. |
| `MBasisHeadCleanupSupply` | **Named input (not proved here).** The coupled M ordinary-head cleanup owned by the MHeadCleanup lane, stated with the weakest hypotheses this file needs. |
| `exists_mBasis_allRows_relative_correction` | Kernel interpolation packaged with the literal target-relative defect and the orientation conclusion. |
| `MBasisStageStep` | **T3 interface.** Orientation-compatible basis, exact ordinary agreement, defect in `lambda_(n+3)`: a depth-`(n+2)` correction with orientation one, every ordinary character one (coordinate matrix retained), defect in `lambda_(n+4)`. |
| `mBasisStageStep_of_headCleanup` | `MBasisHeadCleanupSupply alpha h -> MBasisStageStep alpha h`, `alpha >= 2`. |

## Status

Opened 2026-09-17. `MBasisRowRefinement.lean` verified by the runner of
record: exit 0, 9 pins, all `[propext, Classical.choice, Quot.sound]`, no
warnings. `MPlaneAmbientStage.lean` now imports the landed `MHeadCleanup`
(merged from `claude/w362-mhead`), so the one-step interface `MBasisStageStep`
is proved unconditionally; its verification goes through the mirror harness
once the shared cache rebuild that was running when the lane opened finishes.

## Log

- Commit 1: lane note opened.
- Commit 2: both modules drafted (unverified).
- Commit 3: head-cleanup input weakened to the all-coordinate depth form.
- Merge: `claude/w362-mhead` (landed head cleanup) merged in.
- Commit 4: `MPlaneAmbientStage` consumes `mHead_exists_freeTwo_characterZero_same_class`;
  `mBasisHeadCleanupSupply` and `mBasisStageStep` are theorems.
- Commit 5: `MBasisRowRefinement.lean` verified (9 pins, std-3).
