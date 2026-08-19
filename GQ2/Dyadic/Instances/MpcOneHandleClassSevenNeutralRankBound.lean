/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralCoordinateBound

/-!
# Rank bounds for the class-seven neutral target

W290 bounds the standard neutral target by a two-dimensional `F₂` space.  Therefore both
the neutral-image transpose and every target-augmented transpose have rank at most two.
In particular, rank two for the unaugmented neutral image forces every augmentation to have
the same rank and closes the full W6 correctability criterion from W289.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralRankBound

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralConnecting
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTargetRank
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralCoordinateBound
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev NeutralSource := Additive OneHandleCompactConnectingKernel
private abbrev NeutralTarget := Additive OneHandleC7StandardNeutralityCokernel
private abbrev NeutralDual := NeutralSource →+ ZMod 2

theorem neutralImageTransposeRank_le_two :
    oneHandleCompactNeutralImageTransposeRank ≤ 2 := by
  letI : Finite oneHandleCompactNeutralImageTranspose.range :=
    Finite.of_surjective _
      oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective
  have hcardRange : Nat.card oneHandleCompactNeutralImageTranspose.range ≤
      Nat.card (ElemDual NeutralTarget) :=
    Nat.card_le_card_of_surjective
      oneHandleCompactNeutralImageTranspose.rangeRestrict
      oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective
  have hcardDual : Nat.card (ElemDual NeutralTarget) =
      Nat.card NeutralTarget :=
    card_elemDual oneHandleC7StandardNeutralityCokernel_add_self
  have hcard : 2 ^ oneHandleCompactNeutralImageTransposeRank ≤ 2 ^ 2 := by
    rw [← neutralImageTranspose_rangeCard_eq_pow_rank]
    norm_num
    exact hcardRange.trans (hcardDual.le.trans
      natCard_oneHandleC7StandardNeutralityCokernel_le_four)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem neutralTargetAugmentedTransposeRank_le_two
    (x : OneHandleC7StandardNeutralityCokernel) :
    oneHandleCompactNeutralTargetAugmentedTransposeRank x ≤ 2 := by
  letI : Finite (oneHandleCompactNeutralTargetAugmentedTranspose x).range :=
    Finite.of_surjective _
      (oneHandleCompactNeutralTargetAugmentedTranspose x).rangeRestrict_surjective
  have hcardRange :
      Nat.card (oneHandleCompactNeutralTargetAugmentedTranspose x).range ≤
        Nat.card (ElemDual NeutralTarget) :=
    Nat.card_le_card_of_surjective
      (oneHandleCompactNeutralTargetAugmentedTranspose x).rangeRestrict
      (oneHandleCompactNeutralTargetAugmentedTranspose x).rangeRestrict_surjective
  have hcardDual : Nat.card (ElemDual NeutralTarget) =
      Nat.card NeutralTarget :=
    card_elemDual oneHandleC7StandardNeutralityCokernel_add_self
  have hcard :
      2 ^ oneHandleCompactNeutralTargetAugmentedTransposeRank x ≤ 2 ^ 2 := by
    rw [← neutralTargetAugmentedTranspose_rangeCard_eq_pow_rank]
    norm_num
    exact hcardRange.trans (hcardDual.le.trans
      natCard_oneHandleC7StandardNeutralityCokernel_le_four)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem neutralImageTransposeRank_eq_zero_or_one_or_two :
    oneHandleCompactNeutralImageTransposeRank = 0 ∨
      oneHandleCompactNeutralImageTransposeRank = 1 ∨
      oneHandleCompactNeutralImageTransposeRank = 2 := by
  have h := neutralImageTransposeRank_le_two
  omega

theorem oneHandleW6Correctable_of_neutralImageTransposeRank_eq_two
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E)
    (hrank : oneHandleCompactNeutralImageTransposeRank = 2) :
    OneHandleW6Correctable := by
  rw [oneHandleW6Correctable_iff_neutralTarget_finrank_eq E D hD]
  apply le_antisymm
  · rw [hrank]
    exact neutralTargetAugmentedTransposeRank_le_two _
  · exact neutralImageTransposeRank_le_augmentedRank _

#print axioms neutralImageTransposeRank_le_two
#print axioms neutralTargetAugmentedTransposeRank_le_two
#print axioms neutralImageTransposeRank_eq_zero_or_one_or_two
#print axioms oneHandleW6Correctable_of_neutralImageTransposeRank_eq_two

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralRankBound
