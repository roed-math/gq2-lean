/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStage
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCoreRankOne

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

#print axioms sqCyclotomicStageTuple_bot_nonempty
#print axioms sqCyclotomicStageTuple_bot_three_nonempty
#print axioms sqCyclotomicStageTuple_bot_defectReachable
#print axioms sqCyclotomicStageTuple_bot_three_defectReachable

end

end GQ2.Dyadic.LSquare
