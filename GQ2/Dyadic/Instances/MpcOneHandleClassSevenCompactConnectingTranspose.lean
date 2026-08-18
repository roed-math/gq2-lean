/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingCriterion
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRank

/-!
# The F2 transpose of the compact connecting homomorphism

W279 reduced triviality of the compact connecting homomorphism to a finite range inclusion.
This module dualizes that inclusion.  The compact-kernel transpose evaluates every ambient
F2-character on all compact-kernel shifts, while the augmented transpose pairs it with the four
ordinary relative coordinate rows.

The connecting homomorphism is trivial exactly when the augmented and ordinary transpose
kernels agree.  This is an exact finite kernel criterion; no equality or rank computation is
asserted here.
-/
namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingTranspose

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRank
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingCriterion
open GQ2.FoxH
open scoped IsMulCommutative

private abbrev RelativeSource :=
  Additive (oneHandleRelativeLambdaImage 5 7)

private abbrev RelativeTransposeTarget :=
  (RelativeSource →+ ZMod 2) ×
    (RelativeSource →+ ZMod 2) ×
      (RelativeSource →+ ZMod 2) × (RelativeSource →+ ZMod 2)

private abbrev CompactKernelDual :=
  Additive OneHandleCompactKernelCorrection →+ ZMod 2

noncomputable def oneHandleCompactKernelTranspose :
    ElemDual (Additive (oneHandleRelativeZLayer 6)) →+
      CompactKernelDual where
  toFun ell :=
    (ell : Additive (oneHandleRelativeZLayer 6) →+ ZMod 2).comp
      compactKernelRelativeShiftHom.toAdditive
  map_zero' := rfl
  map_add' _ _ := rfl

def OneHandleCompactKernelTransposeVanishing : Prop :=
  ∀ ell : ElemDual (Additive (oneHandleRelativeZLayer 6)),
    oneHandleC7StandardRelativeCoordinateTranspose ell = 0 →
      oneHandleCompactKernelTranspose ell = 0

private def oneHandleCompactQuotientAdd :
    Additive (oneHandleRelativeZLayer 6) →+
      Additive OneHandleC7StandardRelativeCokernel :=
  (QuotientGroup.mk'
    oneHandleStandardRelativeRelaxedCoordinateSpan).toAdditive

theorem compactKernelCovered_iff_transposeVanishing :
    OneHandleCompactKernelCovered ↔
      OneHandleCompactKernelTransposeVanishing := by
  constructor
  · intro hcover ell hell
    have hrows : OneHandleC7StandardRelativeRowsAnnihilate ell :=
      (standardRelativeCoordinateTranspose_eq_zero_iff_rowsAnnihilate ell).mp hell
    have hann : OneHandleC7StandardRelativeSpanAnnihilates ell :=
      (standardRelativeRowsAnnihilate_iff_spanAnnihilates ell).mp hrows
    apply AddMonoidHom.ext
    intro D
    exact hann _ (hcover D)
  · intro hvan D
    by_contra hmem
    have hobs : QuotientGroup.mk'
        oneHandleStandardRelativeRelaxedCoordinateSpan
          (compactKernelRelativeShiftHom D) ≠ 1 := by
      intro hzero
      exact hmem ((QuotientGroup.eq_one_iff _).mp hzero)
    have hadd : Additive.ofMul
        (QuotientGroup.mk'
          oneHandleStandardRelativeRelaxedCoordinateSpan
            (compactKernelRelativeShiftHom D)) ≠ 0 := by
      simpa using hobs
    obtain ⟨qell, hqell⟩ := elemDual_separates
      oneHandleC7StandardRelativeCokernel_add_self hadd
    let ell : ElemDual (Additive (oneHandleRelativeZLayer 6)) :=
      ((qell : Additive OneHandleC7StandardRelativeCokernel →+ ZMod 2).comp
        oneHandleCompactQuotientAdd :
          ElemDual (Additive (oneHandleRelativeZLayer 6)))
    have hann : OneHandleC7StandardRelativeSpanAnnihilates ell := by
      intro z hz
      change qell (Additive.ofMul
        (QuotientGroup.mk'
          oneHandleStandardRelativeRelaxedCoordinateSpan z)) = 0
      have hq : QuotientGroup.mk'
          oneHandleStandardRelativeRelaxedCoordinateSpan z = 1 :=
        (QuotientGroup.eq_one_iff z).mpr hz
      rw [hq]
      exact map_zero qell
    have hrows : OneHandleC7StandardRelativeRowsAnnihilate ell :=
      (standardRelativeRowsAnnihilate_iff_spanAnnihilates ell).mpr hann
    have hell : oneHandleC7StandardRelativeCoordinateTranspose ell = 0 :=
      (standardRelativeCoordinateTranspose_eq_zero_iff_rowsAnnihilate ell).mpr hrows
    have hzero := congrArg
      (fun f : CompactKernelDual ↦ f (Additive.ofMul D)) (hvan ell hell)
    exact hqell hzero

noncomputable def oneHandleCompactAugmentedTranspose :
    ElemDual (Additive (oneHandleRelativeZLayer 6)) →+
      RelativeTransposeTarget × CompactKernelDual where
  toFun ell :=
    (oneHandleC7StandardRelativeCoordinateTranspose ell,
      oneHandleCompactKernelTranspose ell)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem compactAugmentedTranspose_ker_le_coordinateTranspose_ker :
    oneHandleCompactAugmentedTranspose.ker ≤
      oneHandleC7StandardRelativeCoordinateTranspose.ker := by
  intro ell hell
  have hzero :
      (oneHandleC7StandardRelativeCoordinateTranspose ell,
        oneHandleCompactKernelTranspose ell) = 0 :=
    AddMonoidHom.mem_ker.mp hell
  exact AddMonoidHom.mem_ker.mpr
    (congrArg Prod.fst hzero)

theorem compactKernelTransposeVanishing_iff_ker_eq :
    OneHandleCompactKernelTransposeVanishing ↔
      oneHandleCompactAugmentedTranspose.ker =
        oneHandleC7StandardRelativeCoordinateTranspose.ker := by
  constructor
  · intro hvan
    apply le_antisymm
    · exact compactAugmentedTranspose_ker_le_coordinateTranspose_ker
    · intro ell hell
      have hcoord := AddMonoidHom.mem_ker.mp hell
      apply AddMonoidHom.mem_ker.mpr
      apply Prod.ext
      · exact hcoord
      · exact hvan ell hcoord
  · intro hker ell hcoord
    have hell : ell ∈ oneHandleC7StandardRelativeCoordinateTranspose.ker :=
      AddMonoidHom.mem_ker.mpr hcoord
    rw [← hker] at hell
    exact congrArg Prod.snd (AddMonoidHom.mem_ker.mp hell)

theorem compactConnectingTrivial_iff_transpose_ker_eq :
    OneHandleCompactConnectingTrivial ↔
      oneHandleCompactAugmentedTranspose.ker =
        oneHandleC7StandardRelativeCoordinateTranspose.ker := by
  rw [compactConnectingTrivial_iff_kernelCovered,
    compactKernelCovered_iff_transposeVanishing,
    compactKernelTransposeVanishing_iff_ker_eq]

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

theorem compactConnectingTrivial_iff_transpose_rangeCard_eq :
    OneHandleCompactConnectingTrivial ↔
      Nat.card oneHandleCompactAugmentedTranspose.range =
        Nat.card oneHandleC7StandardRelativeCoordinateTranspose.range := by
  rw [compactConnectingTrivial_iff_transpose_ker_eq]
  have hcard := rangeCard_eq_iff_kernelCard_eq
    oneHandleCompactAugmentedTranspose
    oneHandleC7StandardRelativeCoordinateTranspose
  rw [hcard]
  constructor
  · intro h
    rw [h]
  · intro hcard
    exact AddSubgroup.eq_of_le_of_card_ge
      compactAugmentedTranspose_ker_le_coordinateTranspose_ker
      (le_of_eq hcard.symm)

private theorem zmodTwo_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_smul (R := ZMod 2), show (2 : ZMod 2) = 0 by decide,
    zero_smul]

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

private theorem compactKernelDual_add_self
    (v : CompactKernelDual) : v + v = 0 := by
  ext D
  exact zmodTwo_add_self _

private theorem compactAugmentedTarget_add_self
    (v : RelativeTransposeTarget × CompactKernelDual) : v + v = 0 := by
  apply Prod.ext
  · exact relativeTransposeTarget_add_self v.1
  · exact compactKernelDual_add_self v.2

noncomputable def oneHandleCompactAugmentedTransposeRank : ℕ := by
  letI : Module (ZMod 2) (RelativeTransposeTarget × CompactKernelDual) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact compactAugmentedTarget_add_self v)
  exact Module.finrank (ZMod 2)
    (AddSubgroup.toZModSubmodule 2
      oneHandleCompactAugmentedTranspose.range)

theorem compactAugmentedTranspose_rangeCard_eq_pow_rank :
    Nat.card oneHandleCompactAugmentedTranspose.range =
      2 ^ oneHandleCompactAugmentedTransposeRank := by
  letI : Module (ZMod 2) (RelativeTransposeTarget × CompactKernelDual) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact compactAugmentedTarget_add_self v)
  letI : Finite oneHandleCompactAugmentedTranspose.range :=
    Finite.of_surjective _
      oneHandleCompactAugmentedTranspose.rangeRestrict_surjective
  letI : Finite (AddSubgroup.toZModSubmodule 2
      oneHandleCompactAugmentedTranspose.range) :=
    inferInstanceAs (Finite oneHandleCompactAugmentedTranspose.range)
  letI : Fintype (AddSubgroup.toZModSubmodule 2
      oneHandleCompactAugmentedTranspose.range) :=
    Fintype.ofFinite _
  letI : FiniteDimensional (ZMod 2) (AddSubgroup.toZModSubmodule 2
      oneHandleCompactAugmentedTranspose.range) :=
    Module.Finite.of_finite
  change Nat.card (AddSubgroup.toZModSubmodule 2
      oneHandleCompactAugmentedTranspose.range) = _
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rfl

theorem compactConnectingTrivial_iff_transpose_finrank_eq :
    OneHandleCompactConnectingTrivial ↔
      oneHandleCompactAugmentedTransposeRank =
        oneHandleC7StandardRelativeCoordinateTransposeRank := by
  rw [compactConnectingTrivial_iff_transpose_rangeCard_eq,
    compactAugmentedTranspose_rangeCard_eq_pow_rank,
    standardRelativeCoordinateTranspose_rangeCard_eq_pow_rank]
  exact (Nat.pow_right_injective (a := 2) (by omega)).eq_iff

#print axioms oneHandleCompactKernelTranspose
#print axioms OneHandleCompactKernelTransposeVanishing
#print axioms compactKernelCovered_iff_transposeVanishing
#print axioms oneHandleCompactAugmentedTranspose
#print axioms compactKernelTransposeVanishing_iff_ker_eq
#print axioms compactConnectingTrivial_iff_transpose_ker_eq
#print axioms compactConnectingTrivial_iff_transpose_rangeCard_eq
#print axioms oneHandleCompactAugmentedTransposeRank
#print axioms compactConnectingTrivial_iff_transpose_finrank_eq

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingTranspose
