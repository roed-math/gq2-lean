/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTarget

/-!
# Rank jump for the class-seven neutral connecting target

W288 reduced full W6 correctability to equality of augmented and unaugmented neutral-target
transpose kernels. This module converts that equality to an exact `F₂`-rank test.

Appending target evaluation changes the transpose rank by either zero or one. Rank equality is
full W6 correctability, while a one-bit jump is equivalent to a character annihilating the
neutral connecting image and detecting the chosen obstruction. The rank is not computed here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTargetRank

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralConnecting
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTarget
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev NeutralSource := Additive OneHandleCompactConnectingKernel
private abbrev NeutralTarget := Additive OneHandleC7StandardNeutralityCokernel
private abbrev NeutralDual := NeutralSource →+ ZMod 2

private theorem zmodTwo_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_smul (R := ZMod 2), show (2 : ZMod 2) = 0 by decide,
    zero_smul]

private theorem neutralDual_add_self (v : NeutralDual) : v + v = 0 := by
  ext K
  exact zmodTwo_add_self _

private theorem neutralAugmentedTarget_add_self
    (v : NeutralDual × ZMod 2) : v + v = 0 := by
  apply Prod.ext
  · exact neutralDual_add_self v.1
  · exact zmodTwo_add_self v.2

theorem neutralImageTranspose_rangeCard_eq_pow_rank :
    Nat.card oneHandleCompactNeutralImageTranspose.range =
      2 ^ oneHandleCompactNeutralImageTransposeRank := by
  letI : Module (ZMod 2) NeutralDual :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact neutralDual_add_self v)
  letI : Finite oneHandleCompactNeutralImageTranspose.range :=
    Finite.of_surjective _
      oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective
  letI : Finite (AddSubgroup.toZModSubmodule 2
      oneHandleCompactNeutralImageTranspose.range) :=
    inferInstanceAs (Finite oneHandleCompactNeutralImageTranspose.range)
  letI : FiniteDimensional (ZMod 2) (AddSubgroup.toZModSubmodule 2
      oneHandleCompactNeutralImageTranspose.range) :=
    Module.Finite.of_finite
  change Nat.card (AddSubgroup.toZModSubmodule 2
      oneHandleCompactNeutralImageTranspose.range) =
    2 ^ Module.finrank (ZMod 2) (AddSubgroup.toZModSubmodule 2
      oneHandleCompactNeutralImageTranspose.range)
  have h := Module.natCard_eq_pow_finrank
    (K := ZMod 2) (V := AddSubgroup.toZModSubmodule 2
      oneHandleCompactNeutralImageTranspose.range)
  simpa [ZMod.card] using h

theorem neutralTargetAugmentedTranspose_rangeCard_eq_pow_rank
    (x : OneHandleC7StandardNeutralityCokernel) :
    Nat.card (oneHandleCompactNeutralTargetAugmentedTranspose x).range =
      2 ^ oneHandleCompactNeutralTargetAugmentedTransposeRank x := by
  letI : Module (ZMod 2) (NeutralDual × ZMod 2) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact neutralAugmentedTarget_add_self v)
  letI : Finite
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range :=
    Finite.of_surjective _
      (oneHandleCompactNeutralTargetAugmentedTranspose x).rangeRestrict_surjective
  letI : Finite (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range) :=
    inferInstanceAs (Finite
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range)
  letI : FiniteDimensional (ZMod 2) (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range) :=
    Module.Finite.of_finite
  change Nat.card (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range) =
    2 ^ Module.finrank (ZMod 2) (AddSubgroup.toZModSubmodule 2
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range)
  have h := Module.natCard_eq_pow_finrank
    (K := ZMod 2) (V := AddSubgroup.toZModSubmodule 2
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range)
  simpa [ZMod.card] using h

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

theorem neutralTargetTransposeVanishing_iff_rangeCard_eq
    (x : OneHandleC7StandardNeutralityCokernel) :
    OneHandleCompactNeutralTargetTransposeVanishing x ↔
      Nat.card (oneHandleCompactNeutralTargetAugmentedTranspose x).range =
        Nat.card oneHandleCompactNeutralImageTranspose.range := by
  rw [neutralTargetTransposeVanishing_iff_ker_eq]
  have hcard := rangeCard_eq_iff_kernelCard_eq
    (oneHandleCompactNeutralTargetAugmentedTranspose x)
    oneHandleCompactNeutralImageTranspose
  rw [hcard]
  constructor
  · intro h
    rw [h]
  · intro hcard
    exact AddSubgroup.eq_of_le_of_card_ge
      (neutralTargetAugmented_ker_le_imageTranspose_ker x)
      (le_of_eq hcard.symm)

theorem neutralTargetTransposeVanishing_iff_finrank_eq
    (x : OneHandleC7StandardNeutralityCokernel) :
    OneHandleCompactNeutralTargetTransposeVanishing x ↔
      oneHandleCompactNeutralTargetAugmentedTransposeRank x =
        oneHandleCompactNeutralImageTransposeRank := by
  rw [neutralTargetTransposeVanishing_iff_rangeCard_eq,
    neutralTargetAugmentedTranspose_rangeCard_eq_pow_rank,
    neutralImageTranspose_rangeCard_eq_pow_rank]
  exact (Nat.pow_right_injective (a := 2) (by omega)).eq_iff

theorem oneHandleW6Correctable_iff_neutralTarget_finrank_eq
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E) :
    OneHandleW6Correctable ↔
      oneHandleCompactNeutralTargetAugmentedTransposeRank
          (oneHandleC7StandardNeutralityObstruction
            (compactKernelCorrectionLift E D)
            (compactKernelCorrectionLift_relaxed E D hD)) =
        oneHandleCompactNeutralImageTransposeRank := by
  rw [oneHandleW6Correctable_iff_neutrality_mem_connectingValues E D hD,
    mem_compactNeutralConnectingValues_iff_transposeVanishing,
    neutralTargetTransposeVanishing_iff_finrank_eq]

private noncomputable def neutralTargetRangeProjection
    (x : OneHandleC7StandardNeutralityCokernel) :
    (oneHandleCompactNeutralTargetAugmentedTranspose x).range →
      oneHandleCompactNeutralImageTranspose.range := fun y =>
  ⟨y.1.1, by
    rcases y.2 with ⟨ell, h⟩
    exact ⟨ell, congrArg Prod.fst h⟩⟩

private theorem neutralTargetRangeProjection_surjective
    (x : OneHandleC7StandardNeutralityCokernel) :
    Function.Surjective (neutralTargetRangeProjection x) := by
  rintro ⟨y, ell, rfl⟩
  refine ⟨⟨oneHandleCompactNeutralTargetAugmentedTranspose x ell,
    ⟨ell, rfl⟩⟩, ?_⟩
  rfl

private noncomputable def neutralTargetRangeEmbedding
    (x : OneHandleC7StandardNeutralityCokernel) :
    (oneHandleCompactNeutralTargetAugmentedTranspose x).range →
      oneHandleCompactNeutralImageTranspose.range × ZMod 2 := fun y =>
  (neutralTargetRangeProjection x y, y.1.2)

private theorem neutralTargetRangeEmbedding_injective
    (x : OneHandleC7StandardNeutralityCokernel) :
    Function.Injective (neutralTargetRangeEmbedding x) := by
  intro y z hyz
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun a ↦ a.1.1) hyz
  · exact congrArg (fun a ↦ a.2) hyz

theorem neutralImageTransposeRank_le_augmentedRank
    (x : OneHandleC7StandardNeutralityCokernel) :
    oneHandleCompactNeutralImageTransposeRank ≤
      oneHandleCompactNeutralTargetAugmentedTransposeRank x := by
  letI : Finite
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range :=
    Finite.of_surjective _
      (oneHandleCompactNeutralTargetAugmentedTranspose x).rangeRestrict_surjective
  have hcard : Nat.card oneHandleCompactNeutralImageTranspose.range ≤
      Nat.card (oneHandleCompactNeutralTargetAugmentedTranspose x).range :=
    Nat.card_le_card_of_surjective _
      (neutralTargetRangeProjection_surjective x)
  rw [neutralImageTranspose_rangeCard_eq_pow_rank,
    neutralTargetAugmentedTranspose_rangeCard_eq_pow_rank] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem neutralTargetAugmentedRank_le_imageRank_add_one
    (x : OneHandleC7StandardNeutralityCokernel) :
    oneHandleCompactNeutralTargetAugmentedTransposeRank x ≤
      oneHandleCompactNeutralImageTransposeRank + 1 := by
  letI : Finite oneHandleCompactNeutralImageTranspose.range :=
    Finite.of_surjective _
      oneHandleCompactNeutralImageTranspose.rangeRestrict_surjective
  have hcard : Nat.card
      (oneHandleCompactNeutralTargetAugmentedTranspose x).range ≤
        Nat.card (oneHandleCompactNeutralImageTranspose.range × ZMod 2) :=
    Nat.card_le_card_of_injective _
      (neutralTargetRangeEmbedding_injective x)
  rw [Nat.card_prod, Nat.card_zmod,
    neutralImageTranspose_rangeCard_eq_pow_rank,
    neutralTargetAugmentedTranspose_rangeCard_eq_pow_rank, ← pow_succ] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem neutralTargetAugmentedRank_eq_or_eq_add_one
    (x : OneHandleC7StandardNeutralityCokernel) :
    oneHandleCompactNeutralTargetAugmentedTransposeRank x =
        oneHandleCompactNeutralImageTransposeRank ∨
      oneHandleCompactNeutralTargetAugmentedTransposeRank x =
        oneHandleCompactNeutralImageTransposeRank + 1 := by
  have hlo := neutralImageTransposeRank_le_augmentedRank x
  have hhi := neutralTargetAugmentedRank_le_imageRank_add_one x
  omega

def OneHandleCompactNeutralTargetDetected
    (x : OneHandleC7StandardNeutralityCokernel) : Prop :=
  ∃ ell : ElemDual NeutralTarget,
    oneHandleCompactNeutralImageTranspose ell = 0 ∧
      oneHandleCompactNeutralTargetEvaluation x ell ≠ 0

theorem neutralTargetDetected_iff_not_mem
    (x : OneHandleC7StandardNeutralityCokernel) :
    OneHandleCompactNeutralTargetDetected x ↔
      x ∉ compactNeutralConnectingValues := by
  rw [mem_compactNeutralConnectingValues_iff_transposeVanishing]
  simp only [OneHandleCompactNeutralTargetDetected,
    OneHandleCompactNeutralTargetTransposeVanishing]
  push Not
  rfl

theorem neutralTargetDetected_iff_rankJump_one
    (x : OneHandleC7StandardNeutralityCokernel) :
    OneHandleCompactNeutralTargetDetected x ↔
      oneHandleCompactNeutralTargetAugmentedTransposeRank x -
        oneHandleCompactNeutralImageTransposeRank = 1 := by
  rw [neutralTargetDetected_iff_not_mem,
    mem_compactNeutralConnectingValues_iff_transposeVanishing,
    neutralTargetTransposeVanishing_iff_finrank_eq]
  have hlo := neutralImageTransposeRank_le_augmentedRank x
  rcases neutralTargetAugmentedRank_eq_or_eq_add_one x with h | h
  · simp [h]
  · simp [h]

#print axioms neutralTargetTransposeVanishing_iff_finrank_eq
#print axioms oneHandleW6Correctable_iff_neutralTarget_finrank_eq
#print axioms neutralTargetAugmentedRank_eq_or_eq_add_one
#print axioms OneHandleCompactNeutralTargetDetected
#print axioms neutralTargetDetected_iff_not_mem
#print axioms neutralTargetDetected_iff_rankJump_one

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTargetRank
