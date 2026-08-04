/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStage
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCoreRankOne
import GQ2.Roe.Labute.StageLemma.StageOne

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

#print axioms sqCyclotomicStageTuple_bot_nonempty
#print axioms sqCyclotomicStageTuple_bot_three_nonempty
#print axioms sqCyclotomicStageTuple_bot_defectReachable
#print axioms sqCyclotomicStageTuple_bot_three_defectReachable
#print axioms stageSL1R2_sqRawDefectReachable

end

end GQ2.Dyadic.LSquare
