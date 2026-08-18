/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRank

/-!
# The class-seven ordinary-relative rank jump

W271 appends one scalar target-evaluation row to the four ordinary-relative rows.  Projection
from the augmented image onto the coordinate image is surjective, while the augmented image
embeds in the coordinate image times `ZMod 2`.  Hence the augmented rank is either unchanged
or exactly one larger.

The zero-jump case is ordinary relative coverage.  The one-jump case is its exact negation.
This dichotomy still does not decide which case holds for the selected class-seven target,
and it does not address the separate neutral-`C` quotient.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRankJump

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRank
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev RelativeSource :=
  Additive (oneHandleRelativeLambdaImage 5 7)

private abbrev RelativeTransposeTarget :=
  (RelativeSource →+ ZMod 2) ×
    (RelativeSource →+ ZMod 2) ×
      (RelativeSource →+ ZMod 2) × (RelativeSource →+ ZMod 2)

private noncomputable def relativeRangeProjection
    (E : OneHandleC7RelativeLift) :
    (oneHandleC7StandardRelativeAugmentedTranspose E).range →
      oneHandleC7StandardRelativeCoordinateTranspose.range := fun y =>
  ⟨y.1.1, by
    rcases y.2 with ⟨ell, h⟩
    exact ⟨ell, congrArg Prod.fst h⟩⟩

private theorem relativeRangeProjection_surjective
    (E : OneHandleC7RelativeLift) :
    Function.Surjective (relativeRangeProjection E) := by
  rintro ⟨y, ell, rfl⟩
  refine ⟨⟨oneHandleC7StandardRelativeAugmentedTranspose E ell,
    ⟨ell, rfl⟩⟩, ?_⟩
  rfl

private noncomputable def relativeRangeEmbedding
    (E : OneHandleC7RelativeLift) :
    (oneHandleC7StandardRelativeAugmentedTranspose E).range →
      oneHandleC7StandardRelativeCoordinateTranspose.range × ZMod 2 := fun y =>
  (relativeRangeProjection E y, y.1.2)

private theorem relativeRangeEmbedding_injective
    (E : OneHandleC7RelativeLift) :
    Function.Injective (relativeRangeEmbedding E) := by
  intro x y hxy
  change (relativeRangeProjection E x, x.1.2) =
    (relativeRangeProjection E y, y.1.2) at hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z => z.1.1) hxy
  · exact congrArg (fun z => z.2) hxy

theorem standardRelativeCoordinateRank_le_augmentedRank
    (E : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeCoordinateTransposeRank ≤
      oneHandleC7StandardRelativeAugmentedTransposeRank E := by
  letI : Finite (oneHandleC7StandardRelativeAugmentedTranspose E).range :=
    Finite.of_surjective _
      (oneHandleC7StandardRelativeAugmentedTranspose E).rangeRestrict_surjective
  have hcard :
      Nat.card oneHandleC7StandardRelativeCoordinateTranspose.range ≤
        Nat.card (oneHandleC7StandardRelativeAugmentedTranspose E).range :=
    Nat.card_le_card_of_surjective _
      (relativeRangeProjection_surjective E)
  rw [standardRelativeCoordinateTranspose_rangeCard_eq_pow_rank,
    standardRelativeAugmentedTranspose_rangeCard_eq_pow_rank] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem standardRelativeAugmentedRank_le_coordinateRank_add_one
    (E : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeAugmentedTransposeRank E ≤
      oneHandleC7StandardRelativeCoordinateTransposeRank + 1 := by
  letI : Finite oneHandleC7StandardRelativeCoordinateTranspose.range :=
    Finite.of_surjective _
      oneHandleC7StandardRelativeCoordinateTranspose.rangeRestrict_surjective
  have hcard :
      Nat.card (oneHandleC7StandardRelativeAugmentedTranspose E).range ≤
        Nat.card
          (oneHandleC7StandardRelativeCoordinateTranspose.range × ZMod 2) :=
    Nat.card_le_card_of_injective _ (relativeRangeEmbedding_injective E)
  rw [Nat.card_prod, Nat.card_zmod,
    standardRelativeCoordinateTranspose_rangeCard_eq_pow_rank,
    standardRelativeAugmentedTranspose_rangeCard_eq_pow_rank, ← pow_succ] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem standardRelativeAugmentedRank_eq_or_eq_add_one
    (E : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeAugmentedTransposeRank E =
        oneHandleC7StandardRelativeCoordinateTransposeRank ∨
      oneHandleC7StandardRelativeAugmentedTransposeRank E =
        oneHandleC7StandardRelativeCoordinateTransposeRank + 1 := by
  have hlo := standardRelativeCoordinateRank_le_augmentedRank E
  have hhi := standardRelativeAugmentedRank_le_coordinateRank_add_one E
  omega

def OneHandleC7StandardRelativeTargetDetected
    (E : OneHandleC7RelativeLift) : Prop :=
  ∃ ell : ElemDual (Additive (oneHandleRelativeZLayer 6)),
    oneHandleC7StandardRelativeCoordinateTranspose ell = 0 ∧
      ell (Additive.ofMul (oneHandleC7RelativeTarget E)) ≠ 0

theorem standardRelativeTargetDetected_iff_not_mem_relaxed
    (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeTargetDetected E ↔
      oneHandleC7RelativeTarget E ∉
        oneHandleStandardRelativeRelaxedCoordinateSpan := by
  rw [← standardRelativeTargetTransposeVanishing_iff_target_mem_relaxed]
  simp only [OneHandleC7StandardRelativeTargetDetected,
    OneHandleC7StandardRelativeTargetTransposeVanishing]
  push Not
  rfl

theorem standardRelativeTarget_not_mem_relaxed_iff_rank_add_one
    (E : OneHandleC7RelativeLift) :
    oneHandleC7RelativeTarget E ∉
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      oneHandleC7StandardRelativeAugmentedTransposeRank E =
        oneHandleC7StandardRelativeCoordinateTransposeRank + 1 := by
  rw [not_iff_not.mpr (standardRelativeTarget_mem_relaxed_iff_finrank_eq E)]
  rcases standardRelativeAugmentedRank_eq_or_eq_add_one E with h | h
  · simp [h]
  · simp [h]

theorem standardRelativeTarget_mem_relaxed_iff_rankJump_zero
    (E : OneHandleC7RelativeLift) :
    oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      oneHandleC7StandardRelativeAugmentedTransposeRank E -
        oneHandleC7StandardRelativeCoordinateTransposeRank = 0 := by
  rw [standardRelativeTarget_mem_relaxed_iff_finrank_eq]
  have hle := standardRelativeCoordinateRank_le_augmentedRank E
  omega

theorem standardRelativeTarget_not_mem_relaxed_iff_rankJump_one
    (E : OneHandleC7RelativeLift) :
    oneHandleC7RelativeTarget E ∉
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      oneHandleC7StandardRelativeAugmentedTransposeRank E -
        oneHandleC7StandardRelativeCoordinateTransposeRank = 1 := by
  rw [standardRelativeTarget_not_mem_relaxed_iff_rank_add_one]
  have hle := standardRelativeCoordinateRank_le_augmentedRank E
  omega

theorem standardRelativeTargetDetected_iff_rankJump_one
    (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeTargetDetected E ↔
      oneHandleC7StandardRelativeAugmentedTransposeRank E -
        oneHandleC7StandardRelativeCoordinateTransposeRank = 1 := by
  rw [standardRelativeTargetDetected_iff_not_mem_relaxed,
    standardRelativeTarget_not_mem_relaxed_iff_rankJump_one]

#print axioms standardRelativeCoordinateRank_le_augmentedRank
#print axioms standardRelativeAugmentedRank_le_coordinateRank_add_one
#print axioms standardRelativeAugmentedRank_eq_or_eq_add_one
#print axioms standardRelativeTargetDetected_iff_not_mem_relaxed
#print axioms standardRelativeTarget_not_mem_relaxed_iff_rank_add_one
#print axioms standardRelativeTarget_mem_relaxed_iff_rankJump_zero
#print axioms standardRelativeTarget_not_mem_relaxed_iff_rankJump_one
#print axioms standardRelativeTargetDetected_iff_rankJump_one

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRankJump
