/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2

/-!
# Rank test for the ordinary class-seven relative target

W270 packages the four ordinary-relative rows in one elementary transpose.  This file appends
target evaluation as a fifth row.  Ordinary relative coverage is exactly equality of the two
kernels, equivalently equality of their image cardinalities or their `ZMod 2` finranks.  The
augmented rank can only equal the coordinate rank or exceed it by one.

This is a finite rank test for the first W269 obstruction.  It does not decide the rank, and it
does not address the separate neutral-`C` quotient.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRank

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev RelativeSource :=
  Additive (oneHandleRelativeLambdaImage 5 7)

private abbrev RelativeTransposeTarget :=
  (RelativeSource →+ ZMod 2) ×
    (RelativeSource →+ ZMod 2) ×
      (RelativeSource →+ ZMod 2) × (RelativeSource →+ ZMod 2)

noncomputable def oneHandleC7StandardRelativeTargetEvaluation
    (E : OneHandleC7RelativeLift) :
    ElemDual (Additive (oneHandleRelativeZLayer 6)) →+ ZMod 2 where
  toFun ell := ell (Additive.ofMul (oneHandleC7RelativeTarget E))
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def oneHandleC7StandardRelativeAugmentedTranspose
    (E : OneHandleC7RelativeLift) :
    ElemDual (Additive (oneHandleRelativeZLayer 6)) →+
      RelativeTransposeTarget × ZMod 2 where
  toFun ell :=
    (oneHandleC7StandardRelativeCoordinateTranspose ell,
      oneHandleC7StandardRelativeTargetEvaluation E ell)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem standardRelativeAugmentedTranspose_ker_le_coordinateTranspose_ker
    (E : OneHandleC7RelativeLift) :
    (oneHandleC7StandardRelativeAugmentedTranspose E).ker ≤
      oneHandleC7StandardRelativeCoordinateTranspose.ker := by
  intro ell hell
  have hzero := AddMonoidHom.mem_ker.mp hell
  exact AddMonoidHom.mem_ker.mpr (congrArg Prod.fst hzero)

theorem standardRelativeTargetTransposeVanishing_iff_ker_eq
    (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeTargetTransposeVanishing E ↔
      (oneHandleC7StandardRelativeAugmentedTranspose E).ker =
        oneHandleC7StandardRelativeCoordinateTranspose.ker := by
  constructor
  · intro Hvan
    apply le_antisymm
    · exact standardRelativeAugmentedTranspose_ker_le_coordinateTranspose_ker E
    · intro ell hell
      have hT := AddMonoidHom.mem_ker.mp hell
      apply AddMonoidHom.mem_ker.mpr
      apply Prod.ext
      · exact hT
      · exact Hvan ell hT
  · intro hker ell hT
    have hell : ell ∈ oneHandleC7StandardRelativeCoordinateTranspose.ker :=
      AddMonoidHom.mem_ker.mpr hT
    rw [← hker] at hell
    exact congrArg Prod.snd (AddMonoidHom.mem_ker.mp hell)

theorem standardRelativeTarget_mem_relaxed_iff_augmented_ker_eq
    (E : OneHandleC7RelativeLift) :
    oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      (oneHandleC7StandardRelativeAugmentedTranspose E).ker =
        oneHandleC7StandardRelativeCoordinateTranspose.ker := by
  rw [← standardRelativeTargetTransposeVanishing_iff_target_mem_relaxed,
    standardRelativeTargetTransposeVanishing_iff_ker_eq]

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

theorem standardRelativeTarget_mem_relaxed_iff_rangeCard_eq
    (E : OneHandleC7RelativeLift) :
    oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      Nat.card (oneHandleC7StandardRelativeAugmentedTranspose E).range =
        Nat.card oneHandleC7StandardRelativeCoordinateTranspose.range := by
  rw [standardRelativeTarget_mem_relaxed_iff_augmented_ker_eq]
  have hcard := rangeCard_eq_iff_kernelCard_eq
    (oneHandleC7StandardRelativeAugmentedTranspose E)
    oneHandleC7StandardRelativeCoordinateTranspose
  rw [hcard]
  constructor
  · intro h
    rw [h]
  · intro hcard
    exact AddSubgroup.eq_of_le_of_card_ge
      (standardRelativeAugmentedTranspose_ker_le_coordinateTranspose_ker E)
      (le_of_eq hcard.symm)

private theorem zmodTwo_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_smul (R := ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

private theorem relativeTransposeTarget_add_self
    (v : RelativeTransposeTarget) : v + v = 0 := by
  apply Prod.ext
  · ext x
    exact zmodTwo_add_self _
  · apply Prod.ext
    · ext x
      exact zmodTwo_add_self _
    · apply Prod.ext
      · ext x
        exact zmodTwo_add_self _
      · ext x
        exact zmodTwo_add_self _

private theorem relativeAugmentedTarget_add_self
    (v : RelativeTransposeTarget × ZMod 2) : v + v = 0 := by
  apply Prod.ext
  · exact relativeTransposeTarget_add_self v.1
  · exact zmodTwo_add_self _

noncomputable def oneHandleC7StandardRelativeCoordinateTransposeRank : ℕ := by
  letI : Module (ZMod 2) RelativeTransposeTarget :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact relativeTransposeTarget_add_self v)
  exact Module.finrank (ZMod 2)
    (AddSubgroup.toZModSubmodule 2
      oneHandleC7StandardRelativeCoordinateTranspose.range)

noncomputable def oneHandleC7StandardRelativeAugmentedTransposeRank
    (E : OneHandleC7RelativeLift) : ℕ := by
  letI : Module (ZMod 2) (RelativeTransposeTarget × ZMod 2) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact relativeAugmentedTarget_add_self v)
  exact Module.finrank (ZMod 2)
    (AddSubgroup.toZModSubmodule 2
      (oneHandleC7StandardRelativeAugmentedTranspose E).range)

theorem standardRelativeCoordinateTranspose_rangeCard_eq_pow_rank :
    Nat.card oneHandleC7StandardRelativeCoordinateTranspose.range =
      2 ^ oneHandleC7StandardRelativeCoordinateTransposeRank := by
  letI : Module (ZMod 2) RelativeTransposeTarget :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact relativeTransposeTarget_add_self v)
  letI : Finite oneHandleC7StandardRelativeCoordinateTranspose.range :=
    Finite.of_surjective _
      oneHandleC7StandardRelativeCoordinateTranspose.rangeRestrict_surjective
  letI : Finite (AddSubgroup.toZModSubmodule 2
      oneHandleC7StandardRelativeCoordinateTranspose.range) :=
    inferInstanceAs
      (Finite oneHandleC7StandardRelativeCoordinateTranspose.range)
  letI : Fintype (AddSubgroup.toZModSubmodule 2
      oneHandleC7StandardRelativeCoordinateTranspose.range) :=
    Fintype.ofFinite _
  letI : FiniteDimensional (ZMod 2) (AddSubgroup.toZModSubmodule 2
      oneHandleC7StandardRelativeCoordinateTranspose.range) :=
    Module.Finite.of_finite
  change Nat.card (AddSubgroup.toZModSubmodule 2
      oneHandleC7StandardRelativeCoordinateTranspose.range) = _
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rfl

theorem standardRelativeAugmentedTranspose_rangeCard_eq_pow_rank
    (E : OneHandleC7RelativeLift) :
    Nat.card (oneHandleC7StandardRelativeAugmentedTranspose E).range =
      2 ^ oneHandleC7StandardRelativeAugmentedTransposeRank E := by
  letI : Module (ZMod 2) (RelativeTransposeTarget × ZMod 2) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact relativeAugmentedTarget_add_self v)
  letI : Finite (oneHandleC7StandardRelativeAugmentedTranspose E).range :=
    Finite.of_surjective _
      (oneHandleC7StandardRelativeAugmentedTranspose E).rangeRestrict_surjective
  letI : Finite (AddSubgroup.toZModSubmodule 2
      (oneHandleC7StandardRelativeAugmentedTranspose E).range) :=
    inferInstanceAs
      (Finite (oneHandleC7StandardRelativeAugmentedTranspose E).range)
  letI : Fintype (AddSubgroup.toZModSubmodule 2
      (oneHandleC7StandardRelativeAugmentedTranspose E).range) :=
    Fintype.ofFinite _
  letI : FiniteDimensional (ZMod 2) (AddSubgroup.toZModSubmodule 2
      (oneHandleC7StandardRelativeAugmentedTranspose E).range) :=
    Module.Finite.of_finite
  change Nat.card (AddSubgroup.toZModSubmodule 2
      (oneHandleC7StandardRelativeAugmentedTranspose E).range) = _
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rfl

theorem standardRelativeTarget_mem_relaxed_iff_finrank_eq
    (E : OneHandleC7RelativeLift) :
    oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      oneHandleC7StandardRelativeAugmentedTransposeRank E =
        oneHandleC7StandardRelativeCoordinateTransposeRank := by
  rw [standardRelativeTarget_mem_relaxed_iff_rangeCard_eq,
    standardRelativeAugmentedTranspose_rangeCard_eq_pow_rank,
    standardRelativeCoordinateTranspose_rangeCard_eq_pow_rank]
  exact (Nat.pow_right_injective (a := 2) (by omega)).eq_iff

#print axioms oneHandleC7StandardRelativeTargetEvaluation
#print axioms oneHandleC7StandardRelativeAugmentedTranspose
#print axioms standardRelativeTargetTransposeVanishing_iff_ker_eq
#print axioms standardRelativeTarget_mem_relaxed_iff_rangeCard_eq
#print axioms oneHandleC7StandardRelativeCoordinateTransposeRank
#print axioms oneHandleC7StandardRelativeAugmentedTransposeRank
#print axioms standardRelativeTarget_mem_relaxed_iff_finrank_eq

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRank
