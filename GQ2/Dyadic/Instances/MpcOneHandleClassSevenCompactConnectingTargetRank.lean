/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingTarget

/-!
# Rank jump for the compact connecting target

W283 reduced ordinary class-seven solvability to equality of the augmented and unaugmented
connecting-target transpose kernels.  This module converts that equality to an exact F2-rank
test.  Since augmentation appends one scalar target-evaluation row, its rank is either unchanged
or exactly one larger.

Rank equality is ordinary relative solvability.  A one-bit rank jump is its exact negation and
is equivalent to the existence of a character annihilating the connecting image while detecting
the reference obstruction.  The rank is not computed here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingTargetRank

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenFinitePacket
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingTarget
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev ConnectingSource :=
  Additive OneHandleCompactKernelCorrection

private abbrev ConnectingTarget :=
  Additive OneHandleC7StandardRelativeCokernel

private abbrev ConnectingDual := ConnectingSource →+ ZMod 2

private theorem zmodTwo_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_smul (R := ZMod 2), show (2 : ZMod 2) = 0 by decide,
    zero_smul]

private theorem connectingDual_add_self (v : ConnectingDual) : v + v = 0 := by
  ext D
  exact zmodTwo_add_self _

private theorem connectingAugmentedTarget_add_self
    (v : ConnectingDual × ZMod 2) : v + v = 0 := by
  apply Prod.ext
  · exact connectingDual_add_self v.1
  · exact zmodTwo_add_self v.2

noncomputable def oneHandleCompactConnectingImageTransposeRank : ℕ := by
  letI : Module (ZMod 2) ConnectingDual :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact connectingDual_add_self v)
  exact Module.finrank (ZMod 2)
    (AddSubgroup.toZModSubmodule 2
      oneHandleCompactConnectingImageTranspose.range)

noncomputable def oneHandleCompactConnectingTargetAugmentedTransposeRank
    (E : OneHandleC7RelativeLift) : ℕ := by
  letI : Module (ZMod 2) (ConnectingDual × ZMod 2) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact connectingAugmentedTarget_add_self v)
  exact Module.finrank (ZMod 2)
    (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactConnectingTargetAugmentedTranspose E).range)

theorem connectingImageTranspose_rangeCard_eq_pow_rank :
    Nat.card oneHandleCompactConnectingImageTranspose.range =
      2 ^ oneHandleCompactConnectingImageTransposeRank := by
  letI : Module (ZMod 2) ConnectingDual :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact connectingDual_add_self v)
  letI : Finite oneHandleCompactConnectingImageTranspose.range :=
    Finite.of_surjective _
      oneHandleCompactConnectingImageTranspose.rangeRestrict_surjective
  letI : Finite (AddSubgroup.toZModSubmodule 2
      oneHandleCompactConnectingImageTranspose.range) :=
    inferInstanceAs (Finite oneHandleCompactConnectingImageTranspose.range)
  letI : Fintype (AddSubgroup.toZModSubmodule 2
      oneHandleCompactConnectingImageTranspose.range) :=
    Fintype.ofFinite _
  letI : FiniteDimensional (ZMod 2) (AddSubgroup.toZModSubmodule 2
      oneHandleCompactConnectingImageTranspose.range) :=
    Module.Finite.of_finite
  change Nat.card (AddSubgroup.toZModSubmodule 2
      oneHandleCompactConnectingImageTranspose.range) = _
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rfl

theorem connectingTargetAugmentedTranspose_rangeCard_eq_pow_rank
    (E : OneHandleC7RelativeLift) :
    Nat.card (oneHandleCompactConnectingTargetAugmentedTranspose E).range =
      2 ^ oneHandleCompactConnectingTargetAugmentedTransposeRank E := by
  letI : Module (ZMod 2) (ConnectingDual × ZMod 2) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact connectingAugmentedTarget_add_self v)
  letI : Finite
      (oneHandleCompactConnectingTargetAugmentedTranspose E).range :=
    Finite.of_surjective _
      (oneHandleCompactConnectingTargetAugmentedTranspose E).rangeRestrict_surjective
  letI : Finite (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactConnectingTargetAugmentedTranspose E).range) :=
    inferInstanceAs (Finite
      (oneHandleCompactConnectingTargetAugmentedTranspose E).range)
  letI : Fintype (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactConnectingTargetAugmentedTranspose E).range) :=
    Fintype.ofFinite _
  letI : FiniteDimensional (ZMod 2) (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactConnectingTargetAugmentedTranspose E).range) :=
    Module.Finite.of_finite
  change Nat.card (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactConnectingTargetAugmentedTranspose E).range) = _
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rfl

private theorem rangeCard_mul_kernelCard
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Finite A]
    (f : A →+ B) :
    Nat.card f.range * Nat.card f.ker = Nat.card A := by
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker).symm

private theorem rangeCard_eq_iff_kernelCard_eq
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Finite A] (f : A →+ B) (g : A →+ C) :
    Nat.card f.range = Nat.card g.range ↔
      Nat.card f.ker = Nat.card g.ker := by
  letI : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  letI : Finite g.range :=
    Finite.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hf := rangeCard_mul_kernelCard f
  have hg := rangeCard_mul_kernelCard g
  constructor
  · intro hrange
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := f.range))
    calc
      Nat.card f.range * Nat.card f.ker = Nat.card A := hf
      _ = Nat.card g.range * Nat.card g.ker := hg.symm
      _ = Nat.card f.range * Nat.card g.ker := by rw [hrange]
  · intro hker
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.ker))
    calc
      Nat.card f.range * Nat.card f.ker = Nat.card A := hf
      _ = Nat.card g.range * Nat.card g.ker := hg.symm
      _ = Nat.card g.range * Nat.card f.ker := by rw [hker]

theorem ordinaryRelativeSolvable_iff_connectingTarget_rangeCard_eq
    (E : OneHandleC7RelativeLift) :
    OneHandleW6OrdinaryRelativeSolvable ↔
      Nat.card
          (oneHandleCompactConnectingTargetAugmentedTranspose E).range =
        Nat.card oneHandleCompactConnectingImageTranspose.range := by
  rw [ordinaryRelativeSolvable_iff_connectingTarget_ker_eq]
  have hcard := rangeCard_eq_iff_kernelCard_eq
    (oneHandleCompactConnectingTargetAugmentedTranspose E)
    oneHandleCompactConnectingImageTranspose
  rw [hcard]
  constructor
  · intro h
    rw [h]
  · intro hcard
    exact AddSubgroup.eq_of_le_of_card_ge
      (connectingTargetAugmented_ker_le_imageTranspose_ker E)
      (le_of_eq hcard.symm)

theorem ordinaryRelativeSolvable_iff_connectingTarget_finrank_eq
    (E : OneHandleC7RelativeLift) :
    OneHandleW6OrdinaryRelativeSolvable ↔
      oneHandleCompactConnectingTargetAugmentedTransposeRank E =
        oneHandleCompactConnectingImageTransposeRank := by
  rw [ordinaryRelativeSolvable_iff_connectingTarget_rangeCard_eq,
    connectingTargetAugmentedTranspose_rangeCard_eq_pow_rank,
    connectingImageTranspose_rangeCard_eq_pow_rank]
  exact (Nat.pow_right_injective (a := 2) (by omega)).eq_iff

private noncomputable def connectingTargetRangeProjection
    (E : OneHandleC7RelativeLift) :
    (oneHandleCompactConnectingTargetAugmentedTranspose E).range →
      oneHandleCompactConnectingImageTranspose.range := fun y =>
  ⟨y.1.1, by
    rcases y.2 with ⟨ell, h⟩
    exact ⟨ell, congrArg Prod.fst h⟩⟩

private theorem connectingTargetRangeProjection_surjective
    (E : OneHandleC7RelativeLift) :
    Function.Surjective (connectingTargetRangeProjection E) := by
  rintro ⟨y, ell, rfl⟩
  refine ⟨⟨oneHandleCompactConnectingTargetAugmentedTranspose E ell,
    ⟨ell, rfl⟩⟩, ?_⟩
  rfl

private noncomputable def connectingTargetRangeEmbedding
    (E : OneHandleC7RelativeLift) :
    (oneHandleCompactConnectingTargetAugmentedTranspose E).range →
      oneHandleCompactConnectingImageTranspose.range × ZMod 2 := fun y =>
  (connectingTargetRangeProjection E y, y.1.2)

private theorem connectingTargetRangeEmbedding_injective
    (E : OneHandleC7RelativeLift) :
    Function.Injective (connectingTargetRangeEmbedding E) := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z ↦ z.1.1) hxy
  · exact congrArg (fun z ↦ z.2) hxy

theorem connectingImageTransposeRank_le_augmentedRank
    (E : OneHandleC7RelativeLift) :
    oneHandleCompactConnectingImageTransposeRank ≤
      oneHandleCompactConnectingTargetAugmentedTransposeRank E := by
  letI : Finite
      (oneHandleCompactConnectingTargetAugmentedTranspose E).range :=
    Finite.of_surjective _
      (oneHandleCompactConnectingTargetAugmentedTranspose E).rangeRestrict_surjective
  have hcard : Nat.card oneHandleCompactConnectingImageTranspose.range ≤
      Nat.card
        (oneHandleCompactConnectingTargetAugmentedTranspose E).range :=
    Nat.card_le_card_of_surjective _
      (connectingTargetRangeProjection_surjective E)
  rw [connectingImageTranspose_rangeCard_eq_pow_rank,
    connectingTargetAugmentedTranspose_rangeCard_eq_pow_rank] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem connectingTargetAugmentedRank_le_imageRank_add_one
    (E : OneHandleC7RelativeLift) :
    oneHandleCompactConnectingTargetAugmentedTransposeRank E ≤
      oneHandleCompactConnectingImageTransposeRank + 1 := by
  letI : Finite oneHandleCompactConnectingImageTranspose.range :=
    Finite.of_surjective _
      oneHandleCompactConnectingImageTranspose.rangeRestrict_surjective
  have hcard : Nat.card
      (oneHandleCompactConnectingTargetAugmentedTranspose E).range ≤
        Nat.card
          (oneHandleCompactConnectingImageTranspose.range × ZMod 2) :=
    Nat.card_le_card_of_injective _
      (connectingTargetRangeEmbedding_injective E)
  rw [Nat.card_prod, Nat.card_zmod,
    connectingImageTranspose_rangeCard_eq_pow_rank,
    connectingTargetAugmentedTranspose_rangeCard_eq_pow_rank, ← pow_succ] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem connectingTargetAugmentedRank_eq_or_eq_add_one
    (E : OneHandleC7RelativeLift) :
    oneHandleCompactConnectingTargetAugmentedTransposeRank E =
        oneHandleCompactConnectingImageTransposeRank ∨
      oneHandleCompactConnectingTargetAugmentedTransposeRank E =
        oneHandleCompactConnectingImageTransposeRank + 1 := by
  have hlo := connectingImageTransposeRank_le_augmentedRank E
  have hhi := connectingTargetAugmentedRank_le_imageRank_add_one E
  omega

def OneHandleCompactConnectingTargetDetected
    (E : OneHandleC7RelativeLift) : Prop :=
  ∃ ell : ElemDual ConnectingTarget,
    oneHandleCompactConnectingImageTranspose ell = 0 ∧
      oneHandleCompactConnectingTargetEvaluation E ell ≠ 0

theorem connectingTargetDetected_iff_not_solvable
    (E : OneHandleC7RelativeLift) :
    OneHandleCompactConnectingTargetDetected E ↔
      ¬ OneHandleW6OrdinaryRelativeSolvable := by
  rw [ordinaryRelativeSolvable_iff_obstruction_mem_connectingValues,
    obstruction_mem_connectingValues_iff_transposeVanishing]
  simp only [OneHandleCompactConnectingTargetDetected,
    OneHandleCompactConnectingTargetTransposeVanishing]
  push Not
  rfl

theorem not_ordinaryRelativeSolvable_iff_connectingTarget_rank_add_one
    (E : OneHandleC7RelativeLift) :
    ¬ OneHandleW6OrdinaryRelativeSolvable ↔
      oneHandleCompactConnectingTargetAugmentedTransposeRank E =
        oneHandleCompactConnectingImageTransposeRank + 1 := by
  rw [not_iff_not.mpr
    (ordinaryRelativeSolvable_iff_connectingTarget_finrank_eq E)]
  rcases connectingTargetAugmentedRank_eq_or_eq_add_one E with h | h
  · simp [h]
  · simp [h]

theorem connectingTargetDetected_iff_rankJump_one
    (E : OneHandleC7RelativeLift) :
    OneHandleCompactConnectingTargetDetected E ↔
      oneHandleCompactConnectingTargetAugmentedTransposeRank E -
        oneHandleCompactConnectingImageTransposeRank = 1 := by
  rw [connectingTargetDetected_iff_not_solvable E,
    not_ordinaryRelativeSolvable_iff_connectingTarget_rank_add_one E]
  have hle := connectingImageTransposeRank_le_augmentedRank E
  omega

#print axioms oneHandleCompactConnectingImageTransposeRank
#print axioms oneHandleCompactConnectingTargetAugmentedTransposeRank
#print axioms ordinaryRelativeSolvable_iff_connectingTarget_finrank_eq
#print axioms connectingTargetAugmentedRank_eq_or_eq_add_one
#print axioms OneHandleCompactConnectingTargetDetected
#print axioms connectingTargetDetected_iff_not_solvable
#print axioms not_ordinaryRelativeSolvable_iff_connectingTarget_rank_add_one
#print axioms connectingTargetDetected_iff_rankJump_one

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingTargetRank
