/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStage
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCoreRankOne
import GQ2.Roe.Labute.StageLemma.StageTwo

/-!
# Rank-one regression for the variable-rank Labute stage

The already-proved oriented classification of `G_Q2(2)` transports the literal improved
square marking to every lower two-central quotient.  In particular, the general campaign's
level-three base premise is a theorem when `h = 0`; the `Q_2` case is not an additional input
to the variable-rank induction.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Every lower two-central level of the bottom field has an exact oriented square marking,
obtained from the proved oriented `Q_2` equivalence. -/
theorem sqCyclotomicStageTuple_bot_nonempty (k : ℕ) :
    Nonempty (SqCyclotomicStageTuple
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k) := by
  obtain ⟨e⟩ := orientedSqZeroEquivGalKBot
  exact ⟨SqCyclotomicStageTuple.ofOrientedEquiv e⟩

/-- Regression theorem at the exact base level consumed by the general stage induction. -/
theorem sqCyclotomicStageTuple_bot_three_nonempty :
    Nonempty (SqCyclotomicStageTuple
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 3) :=
  sqCyclotomicStageTuple_bot_nonempty 3

/-- Strongest noncircular correction regression currently available at `Q_2`: at every
level, the exact oriented stage transported from the already-proved global classification has
its actual defect reachable by an admissible correction. -/
theorem sqCyclotomicStageTuple_bot_defectReachable (k : ℕ) :
    ∃ T : SqCyclotomicStageTuple
        (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k,
      T.DefectReachable := by
  obtain ⟨e⟩ := orientedSqZeroEquivGalKBot
  exact ⟨SqCyclotomicStageTuple.ofOrientedEquiv e,
    SqCyclotomicStageTuple.ofOrientedEquiv_defectReachable e⟩

/-- The preceding correction regression at the base level used by stage induction. -/
theorem sqCyclotomicStageTuple_bot_three_defectReachable :
    ∃ T : SqCyclotomicStageTuple
        (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 3,
      T.DefectReachable :=
  sqCyclotomicStageTuple_bot_defectReachable 3

/-! ## Exact comparison with the rank-three stage calculation -/

/-- `stageSL1R2` is exactly raw actual-defect reachability for the literal improved square
word at `h = 0`.  Thus the rank-three crossed-derivation/span calculation itself aligns with
the new presentation; what it does not provide is the separate exact-fibre strictification
required by `AdmissibleCorrection`. -/
theorem stageSL1R2_sqRawDefectReachable (k : ℕ) (hk : 3 ≤ k)
    {T : Fin 3 → levelQuot (D0 : Type) k} (hT : T ∈ sPR2 k) :
    SqCyclotomicStageTuple.sqRawDefectReachable (D0 : Type) 0 k T := by
  obtain ⟨w, hw, hshift⟩ := stageSL1R2 k hk hT
  refine ⟨w, hw, ?_⟩
  calc
    SqCyclotomicStageTuple.stageShift (h := 0) (k := k)
        (fun i : Fin 3 ↦ canonLift (D0 : Type) k (T i)) w =
        dbarWordR2 (canonLift (D0 : Type) k (T 0))
          (canonLift (D0 : Type) k (T 1))
          (canonLift (D0 : Type) k (T 2)) w := by
      exact SqCyclotomicStageTuple.stageShift_zero_eq_dbarWordR2
        k hk _ w hw
    _ = (defectR2 k T)⁻¹ := hshift
    _ = (sqStageDefect (D0 : Type) 0 k T)⁻¹ := by
      rw [sqStageDefect, SqCore.sqRelWord_zero, SqCore.sqWord_eq_drWord]
      rfl

/-- The existing rank-three `SL1` and `SL2` calculations compose to a single correction
of the original canonical lift.  That correction has the depth required by the general
stage interface, kills the literal improved-word defect, and leaves a tuple satisfying the
full next-level finite-precision presentation conditions. -/
theorem stageSL12R2_truncatedCorrection (k : ℕ) (hk : 3 ≤ k)
    {T : Fin 3 → levelQuot (D0 : Type) k} (hT : T ∈ sPR2 k) :
    ∃ correction : Fin 3 → levelQuot (D0 : Type) (k + 1),
      (∀ i, correction i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) ∧
      SqCyclotomicStageTuple.stageShift (h := 0)
          (fun i : Fin 3 ↦ canonLift (D0 : Type) k (T i)) correction =
        (sqStageDefect (D0 : Type) 0 k T)⁻¹ ∧
      SqCyclotomicStageTuple.stageModified (G := (D0 : Type)) (h := 0) (k := k)
          (fun i : Fin 3 ↦ canonLift (D0 : Type) k (T i)) correction ∈ sPR2 (k + 1) := by
  obtain ⟨w, hw, hd⟩ := stageSL1R2 k hk hT
  let T₁ : Fin 3 → levelQuot (D0 : Type) k :=
    fun i ↦ T i * GQ2.Roe.Labute.levelProj (D0 : Type) k (w i)
  have hT₁ : T₁ ∈ sPR2 k := by
    exact sPR2_mul_mem k hk hT fun i ↦ levelProj_mem_lambdaImage (D0 : Type) (hw i)
  have hδ₁ : defectR2 k T₁ = 1 := by
    dsimp only [T₁]
    rw [defectR2_mul k hk hw, hd, mul_inv_cancel]
  obtain ⟨w', hw', _hker, hnext⟩ := stageSL2R2 k hk hT₁ hδ₁
  let base : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ canonLift (D0 : Type) k (T i)
  let next : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ canonLift (D0 : Type) k (T₁ i) * w' i
  let correction : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ (base i)⁻¹ * next i
  have hmodified : SqCyclotomicStageTuple.stageModified
      (G := (D0 : Type)) (h := 0) (k := k) base correction = next := by
    funext i
    dsimp only [SqCyclotomicStageTuple.stageModified, correction]
    group
  have hdepth : ∀ i, correction i ∈
      lambdaImage (D0 : Type) (k - 1) (k + 1) := by
    intro i
    apply SqCyclotomicStageTuple.mem_lambdaImage_succ_of_levelProj_mem (by omega)
    have hwproj : GQ2.Roe.Labute.levelProj (D0 : Type) k (w i) ∈
        lambdaImage (D0 : Type) (k - 1) k :=
      levelProj_mem_lambdaImage (D0 : Type) (hw i)
    have hw'proj : GQ2.Roe.Labute.levelProj (D0 : Type) k (w' i) ∈
        lambdaImage (D0 : Type) (k - 1) k :=
      levelProj_mem_lambdaImage (D0 : Type) (hw' i)
    have hprod := Subgroup.mul_mem _ hwproj hw'proj
    simpa only [correction, base, next, map_mul, map_inv, levelProj_canonLift,
      T₁, mul_assoc, inv_mul_cancel_left] using hprod
  refine ⟨correction, hdepth, ?_, ?_⟩
  · have hnextrel : SqCore.sqRelWord (h := 0) next = 1 := by
      rw [SqCore.sqRelWord_zero, SqCore.sqWord_eq_drWord]
      exact hnext.1.1
    rw [SqCyclotomicStageTuple.stageShift, hmodified, hnextrel, mul_one]
    rfl
  · rw [hmodified]
    exact hnext

#print axioms sqCyclotomicStageTuple_bot_nonempty
#print axioms sqCyclotomicStageTuple_bot_three_nonempty
#print axioms sqCyclotomicStageTuple_bot_defectReachable
#print axioms sqCyclotomicStageTuple_bot_three_defectReachable
#print axioms stageSL1R2_sqRawDefectReachable
#print axioms stageSL12R2_truncatedCorrection

end

end GQ2.Dyadic.LSquare
