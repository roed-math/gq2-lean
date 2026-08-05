/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteVariableStageOne

/-!
# Variable-rank stage two: the kernel-adapted supply and the all-stage residual theorem

`GammaLSylowPreimageFieldLabuteVariableStageOne` upgraded a kernel-adapted raw kill to the
sharp actual-defect supply of a single stage.  This file packages the remaining per-field
obligation as one Prop, `SqKernelAdaptedDefectSupply`: at every level `k ≥ 3` and every exact
stage tuple, some depth-`k-1` correction kills the current improved-word defect while leaving
every hyperbolic handle row trivial at the next finite precision.  At `h = 0` there are no
handle rows, so the interface degenerates to raw Labute reachability, and the bottom-field
oracle satisfies it unconditionally.

For odd-degree fields the supply yields the full capstone premise: surjectivity of the
descended cyclotomic character (odd-degree marked reciprocity) feeds the fresh-digit flip, and
the transgression chain of the stage regression converts the sharp supply into the
primitive-residual formulation consumed by
`nonempty_orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing`
(`oddDegreeGalKSq_allStagePrimitiveResidualVanishing`).
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **The kernel-adapted raw supply.**  At every stage of the given field and handle count,
one depth correction kills the current literal improved-word defect and keeps all handle rows
trivial at the next finite precision.  This is the single remaining arithmetic obligation of
the forward presentation capstone; its core-row refinements are theorems. -/
def SqKernelAdaptedDefectSupply (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] (h : ℕ) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
    ∃ c : Fin (SqCore.sqRank h) → levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      (∀ i, c i ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1)) ∧
      SqCyclotomicStageTuple.stageShift
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c =
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ ∧
      (∀ j : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
        (SqCyclotomicStageTuple.stageModified
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c
          (SqCore.sqHandleIdxU j)) = 1) ∧
      (∀ j : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
        (SqCyclotomicStageTuple.stageModified
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c
          (SqCore.sqHandleIdxV j)) = 1)

/-- At handle count zero the kernel-adapted supply is exactly all-stage raw Labute
reachability: there are no handle rows to constrain. -/
theorem sqKernelAdaptedDefectSupply_of_rank_zero_raw
    (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (Hraw : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K 0 k,
      SqCyclotomicStageTuple.sqRawDefectReachable
        (maxProPQuotient 2 (GalK K)) 0 k T.generators) :
    SqKernelAdaptedDefectSupply K 0 := by
  intro k hk T
  obtain ⟨c, hdepth, hkill⟩ := Hraw k hk T
  exact ⟨c, hdepth, hkill, fun j ↦ j.elim0, fun j ↦ j.elim0⟩

/-- The kernel-adapted supply strengthens raw all-stage Labute reachability only through its
handle-row clauses: forgetting them recovers the raw statement at every rank. -/
theorem SqKernelAdaptedDefectSupply.toRaw {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] {h : ℕ}
    (H : SqKernelAdaptedDefectSupply K h)
    (k : ℕ) (hk : 3 ≤ k) (T : SqCyclotomicStageTuple K h k) :
    SqCyclotomicStageTuple.sqRawDefectReachable
      (maxProPQuotient 2 (GalK K)) h k T.generators := by
  obtain ⟨c, hdepth, hkill, -, -⟩ := H k hk T
  exact ⟨c, hdepth, hkill⟩

/-- **Per-stage primitive-residual vanishing from the kernel-adapted supply.**  Given
surjectivity of the descended cyclotomic character, each supplied stage upgrades through the
sharp correction to a base point with vanishing primitive residual. -/
theorem stageResidual_exists_primitiveVanishing_of_kernelAdaptedSupply
    {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] {h : ℕ}
    (hsurj : Function.Surjective (chiCycKTwo (K := K)))
    (Hsupply : SqKernelAdaptedDefectSupply K h)
    (k : ℕ) (hk : 3 ≤ k) (T : SqCyclotomicStageTuple K h k) :
    ∃ W : SqCyclotomicStageTuple.SharpAdmissibleCorrection T (by omega),
      SqCyclotomicStageTuple.SharpCyclotomicInflationPrimitiveResidualVanishing T hk W
        (maxProTwoGalK_isTopologicallyFinGen K) := by
  obtain ⟨c, hdepth, hkill, hhU, hhV⟩ := Hsupply k hk T
  exact SqCyclotomicStageTuple.stageResidual_exists_primitiveVanishing_of_actualDefectSupply
    (maxProTwoGalK_isTopologicallyFinGen K)
    (SqCyclotomicStageTuple.stageResidual_nonempty_actualDefectSupply_of_kernelAdaptedKill
      hk hsurj c hdepth hkill hhU hhV)

/-- **The all-stage residual theorem for odd-degree fields.**  Odd-degree marked reciprocity
makes the descended cyclotomic character surjective, so the kernel-adapted supply delivers the
complete `∀ k ≥ 3` premise of the forward presentation capstone. -/
theorem oddDegreeGalKSq_allStagePrimitiveResidualVanishing
    {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] {h : ℕ}
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hsupply : SqKernelAdaptedDefectSupply K h) :
    ∀ (k : ℕ) (hk : 3 ≤ k) (T : SqCyclotomicStageTuple K h k),
      ∃ W : SqCyclotomicStageTuple.SharpAdmissibleCorrection T (by omega),
        SqCyclotomicStageTuple.SharpCyclotomicInflationPrimitiveResidualVanishing T hk W
          (maxProTwoGalK_isTopologicallyFinGen K) :=
  fun k hk T ↦ stageResidual_exists_primitiveVanishing_of_kernelAdaptedSupply
    (chiCycKTwo_surjective_of_odd_finrank K (markedRecipAt K) hodd) Hsupply k hk T

/-! ## The rank-one calibration -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The bottom field satisfies the kernel-adapted supply unconditionally: its stages are raw
defect-reachable and there are no handles. -/
theorem sqKernelAdaptedDefectSupply_bot :
    SqKernelAdaptedDefectSupply (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 :=
  sqKernelAdaptedDefectSupply_of_rank_zero_raw _ fun k hk T ↦
    (sqCyclotomicStageTuple_bot_all_defectReachable k hk T).toRaw

#print axioms sqKernelAdaptedDefectSupply_of_rank_zero_raw
#print axioms SqKernelAdaptedDefectSupply.toRaw
#print axioms stageResidual_exists_primitiveVanishing_of_kernelAdaptedSupply
#print axioms oddDegreeGalKSq_allStagePrimitiveResidualVanishing
#print axioms sqKernelAdaptedDefectSupply_bot

end

end GQ2.Dyadic.LSquare
