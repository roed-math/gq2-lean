/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
import GQ2.Devissage.ElemDualPack

/-!
# Elementary-dual form of the ordinary class-seven relative obstruction

W269 splits the constrained correction problem into ordinary relative coverage and the
remaining neutral-`C` condition.  The first quotient is elementary abelian.  This file pulls
its dual test back to the relative central layer and then expands span annihilation into the
four literal standard rows.

Thus ordinary relative coverage is equivalent to one finite transpose condition: every
`ZMod 2` functional which kills the square/bracket `A` row and the three bracket rows also
kills the selected W268 target.  No vanishing statement is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCoordinates
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

theorem oneHandleC7StandardRelativeCokernel_sq
    (x : OneHandleC7StandardRelativeCokernel) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | _ z =>
    have hz : z ^ 2 = 1 := Subtype.ext (zLayer_sq H z.2.1)
    change (QuotientGroup.mk'
      oneHandleStandardRelativeRelaxedCoordinateSpan z) ^ 2 = 1
    rw [← map_pow, hz, map_one]

theorem oneHandleC7StandardRelativeCokernel_add_self
    (x : Additive OneHandleC7StandardRelativeCokernel) : x + x = 0 := by
  apply Additive.toMul.injective
  simpa [pow_two] using oneHandleC7StandardRelativeCokernel_sq x.toMul

def OneHandleC7StandardRelativeF2Vanishing
    (E : OneHandleC7RelativeLift) : Prop :=
  ∀ ell : ElemDual (Additive OneHandleC7StandardRelativeCokernel),
    ell (Additive.ofMul (oneHandleC7StandardRelativeObstruction E)) = 0

theorem standardRelativeF2Vanishing_iff_obstruction_eq_one
    (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeF2Vanishing E ↔
      oneHandleC7StandardRelativeObstruction E = 1 := by
  constructor
  · intro h
    by_contra hne
    have ha : Additive.ofMul
        (oneHandleC7StandardRelativeObstruction E) ≠ 0 := by
      simpa using hne
    obtain ⟨ell, hell⟩ := elemDual_separates
      oneHandleC7StandardRelativeCokernel_add_self ha
    exact hell (h ell)
  · intro h ell
    rw [h]
    exact map_zero ell

theorem standardRelativeF2Vanishing_iff_target_mem_relaxed
    (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeF2Vanishing E ↔
      oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan := by
  rw [standardRelativeF2Vanishing_iff_obstruction_eq_one,
    standardRelativeObstruction_eq_one_iff]

def OneHandleC7StandardRelativeSpanAnnihilates
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6))) : Prop :=
  ∀ z : oneHandleRelativeZLayer 6,
    z ∈ oneHandleStandardRelativeRelaxedCoordinateSpan →
      ell (Additive.ofMul z) = 0

def OneHandleC7StandardRelativeAmbientF2Vanishing
    (E : OneHandleC7RelativeLift) : Prop :=
  ∀ ell : ElemDual (Additive (oneHandleRelativeZLayer 6)),
    OneHandleC7StandardRelativeSpanAnnihilates ell →
      ell (Additive.ofMul (oneHandleC7RelativeTarget E)) = 0

private def oneHandleC7StandardRelativeQuotientAdd :
    Additive (oneHandleRelativeZLayer 6) →+
      Additive OneHandleC7StandardRelativeCokernel :=
  (QuotientGroup.mk'
    oneHandleStandardRelativeRelaxedCoordinateSpan).toAdditive

theorem standardRelativeAmbientF2Vanishing_iff_target_mem_relaxed
    (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeAmbientF2Vanishing E ↔
      oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan := by
  constructor
  · intro Hvan
    by_contra hmem
    have hobs : oneHandleC7StandardRelativeObstruction E ≠ 1 := by
      intro hzero
      exact hmem ((standardRelativeObstruction_eq_one_iff E).mp hzero)
    have hadd : Additive.ofMul
        (oneHandleC7StandardRelativeObstruction E) ≠ 0 := by
      simpa using hobs
    obtain ⟨qell, hqell⟩ := elemDual_separates
      oneHandleC7StandardRelativeCokernel_add_self hadd
    let ell : ElemDual (Additive (oneHandleRelativeZLayer 6)) :=
      ((qell : Additive OneHandleC7StandardRelativeCokernel →+ ZMod 2).comp
        oneHandleC7StandardRelativeQuotientAdd :
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
    exact hqell (Hvan ell hann)
  · intro hmem ell hann
    exact hann _ hmem

noncomputable def oneHandleStandardRelativeShiftCRelaxed :
    oneHandleRelativeLambdaImage 5 7 →* oneHandleRelativeZLayer 6 :=
  oneHandleBalancedCoreRelativeShiftCRelaxed
    oneHandleStandardBalancedPoint 6 (by omega)

@[simp] theorem oneHandleStandardRelativeShiftCRelaxed_apply
    (x : oneHandleRelativeLambdaImage 5 7) :
    (oneHandleStandardRelativeShiftCRelaxed x).1 =
      commP x.1 (levelMk H 7 (dmD 2 1)) := by
  exact oneHandleBalancedCoreRelativeShiftCRelaxed_apply
    oneHandleStandardBalancedPoint 6 (by omega) x

theorem oneHandleStandardRelativeRelaxedCoordinateSpan_eq_rows :
    oneHandleStandardRelativeRelaxedCoordinateSpan =
      ((oneHandleStandardRelativeShiftA.range ⊔
        oneHandleStandardRelativeShiftB.range) ⊔
      (oneHandleStandardRelativeShiftCRelaxed.range ⊔
        oneHandleStandardRelativeShiftD.range)) := by
  rfl

def OneHandleC7StandardRelativeRowsAnnihilate
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6))) : Prop :=
  (∀ x : oneHandleRelativeLambdaImage 5 7,
      ell (Additive.ofMul (oneHandleStandardRelativeShiftA x)) = 0) ∧
  (∀ x : oneHandleRelativeLambdaImage 5 7,
      ell (Additive.ofMul (oneHandleStandardRelativeShiftB x)) = 0) ∧
  (∀ x : oneHandleRelativeLambdaImage 5 7,
      ell (Additive.ofMul (oneHandleStandardRelativeShiftCRelaxed x)) = 0) ∧
  (∀ x : oneHandleRelativeLambdaImage 5 7,
      ell (Additive.ofMul (oneHandleStandardRelativeShiftD x)) = 0)

private def oneHandleC7StandardRelativeF2Kernel
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6))) :
    Subgroup (oneHandleRelativeZLayer 6) :=
  ell.ker.toSubgroup'

private theorem mem_oneHandleC7StandardRelativeF2Kernel_iff
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6)))
    (z : oneHandleRelativeZLayer 6) :
    z ∈ oneHandleC7StandardRelativeF2Kernel ell ↔
      ell (Additive.ofMul z) = 0 := by
  rfl

theorem standardRelativeRowsAnnihilate_iff_spanAnnihilates
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6))) :
    OneHandleC7StandardRelativeRowsAnnihilate ell ↔
      OneHandleC7StandardRelativeSpanAnnihilates ell := by
  constructor
  · rintro ⟨hA, hB, hC, hD⟩ z hz
    have hspan : oneHandleStandardRelativeRelaxedCoordinateSpan ≤
        oneHandleC7StandardRelativeF2Kernel ell := by
      rw [oneHandleStandardRelativeRelaxedCoordinateSpan_eq_rows]
      apply sup_le
      · apply sup_le
        · rintro y ⟨x, rfl⟩
          exact (mem_oneHandleC7StandardRelativeF2Kernel_iff ell _).mpr (hA x)
        · rintro y ⟨x, rfl⟩
          exact (mem_oneHandleC7StandardRelativeF2Kernel_iff ell _).mpr (hB x)
      · apply sup_le
        · rintro y ⟨x, rfl⟩
          exact (mem_oneHandleC7StandardRelativeF2Kernel_iff ell _).mpr (hC x)
        · rintro y ⟨x, rfl⟩
          exact (mem_oneHandleC7StandardRelativeF2Kernel_iff ell _).mpr (hD x)
    exact (mem_oneHandleC7StandardRelativeF2Kernel_iff ell z).mp (hspan hz)
  · intro hann
    refine ⟨fun x ↦ hann _ ?_, fun x ↦ hann _ ?_,
      fun x ↦ hann _ ?_, fun x ↦ hann _ ?_⟩
    · rw [oneHandleStandardRelativeRelaxedCoordinateSpan_eq_rows]
      exact (show oneHandleStandardRelativeShiftA.range ≤ _ from
        le_trans le_sup_left le_sup_left) ⟨x, rfl⟩
    · rw [oneHandleStandardRelativeRelaxedCoordinateSpan_eq_rows]
      exact (show oneHandleStandardRelativeShiftB.range ≤ _ from
        le_trans le_sup_right le_sup_left) ⟨x, rfl⟩
    · rw [oneHandleStandardRelativeRelaxedCoordinateSpan_eq_rows]
      exact (show oneHandleStandardRelativeShiftCRelaxed.range ≤ _ from
        le_trans le_sup_left le_sup_right) ⟨x, rfl⟩
    · rw [oneHandleStandardRelativeRelaxedCoordinateSpan_eq_rows]
      exact (show oneHandleStandardRelativeShiftD.range ≤ _ from
        le_trans le_sup_right le_sup_right) ⟨x, rfl⟩

def OneHandleC7StandardRelativeCoordinateF2Vanishing
    (E : OneHandleC7RelativeLift) : Prop :=
  ∀ ell : ElemDual (Additive (oneHandleRelativeZLayer 6)),
    OneHandleC7StandardRelativeRowsAnnihilate ell →
      ell (Additive.ofMul (oneHandleC7RelativeTarget E)) = 0

theorem standardRelativeCoordinateF2Vanishing_iff_target_mem_relaxed
    (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeCoordinateF2Vanishing E ↔
      oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan := by
  rw [← standardRelativeAmbientF2Vanishing_iff_target_mem_relaxed]
  constructor <;> intro H ell hell
  · exact H ell
      ((standardRelativeRowsAnnihilate_iff_spanAnnihilates ell).mpr hell)
  · exact H ell
      ((standardRelativeRowsAnnihilate_iff_spanAnnihilates ell).mp hell)

private abbrev RelativeSource :=
  Additive (oneHandleRelativeLambdaImage 5 7)

private abbrev StandardRelativeTransposeTarget :=
  (RelativeSource →+ ZMod 2) ×
    (RelativeSource →+ ZMod 2) ×
      (RelativeSource →+ ZMod 2) × (RelativeSource →+ ZMod 2)

noncomputable def oneHandleC7StandardRelativeCoordinateTranspose :
    ElemDual (Additive (oneHandleRelativeZLayer 6)) →+
      StandardRelativeTransposeTarget where
  toFun ell :=
    ((ell : Additive (oneHandleRelativeZLayer 6) →+ ZMod 2).comp
        oneHandleStandardRelativeShiftA.toAdditive,
      (ell : Additive (oneHandleRelativeZLayer 6) →+ ZMod 2).comp
        oneHandleStandardRelativeShiftB.toAdditive,
      (ell : Additive (oneHandleRelativeZLayer 6) →+ ZMod 2).comp
        oneHandleStandardRelativeShiftCRelaxed.toAdditive,
      (ell : Additive (oneHandleRelativeZLayer 6) →+ ZMod 2).comp
        oneHandleStandardRelativeShiftD.toAdditive)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem oneHandleC7StandardRelativeCoordinateTranspose_apply_A
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6)))
    (x : oneHandleRelativeLambdaImage 5 7) :
    (oneHandleC7StandardRelativeCoordinateTranspose ell).1
        (Additive.ofMul x) =
      ell (Additive.ofMul (oneHandleStandardRelativeShiftA x)) := rfl

@[simp] theorem oneHandleC7StandardRelativeCoordinateTranspose_apply_B
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6)))
    (x : oneHandleRelativeLambdaImage 5 7) :
    (oneHandleC7StandardRelativeCoordinateTranspose ell).2.1
        (Additive.ofMul x) =
      ell (Additive.ofMul (oneHandleStandardRelativeShiftB x)) := rfl

@[simp] theorem oneHandleC7StandardRelativeCoordinateTranspose_apply_C
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6)))
    (x : oneHandleRelativeLambdaImage 5 7) :
    (oneHandleC7StandardRelativeCoordinateTranspose ell).2.2.1
        (Additive.ofMul x) =
      ell (Additive.ofMul (oneHandleStandardRelativeShiftCRelaxed x)) := rfl

@[simp] theorem oneHandleC7StandardRelativeCoordinateTranspose_apply_D
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6)))
    (x : oneHandleRelativeLambdaImage 5 7) :
    (oneHandleC7StandardRelativeCoordinateTranspose ell).2.2.2
        (Additive.ofMul x) =
      ell (Additive.ofMul (oneHandleStandardRelativeShiftD x)) := rfl

theorem standardRelativeCoordinateTranspose_eq_zero_iff_rowsAnnihilate
    (ell : ElemDual (Additive (oneHandleRelativeZLayer 6))) :
    oneHandleC7StandardRelativeCoordinateTranspose ell = 0 ↔
      OneHandleC7StandardRelativeRowsAnnihilate ell := by
  constructor
  · intro h
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
    · have hx := congrArg
          (fun q : StandardRelativeTransposeTarget ↦ q.1 (Additive.ofMul x)) h
      simpa using hx
    · have hx := congrArg
          (fun q : StandardRelativeTransposeTarget ↦ q.2.1 (Additive.ofMul x)) h
      simpa using hx
    · have hx := congrArg
          (fun q : StandardRelativeTransposeTarget ↦ q.2.2.1 (Additive.ofMul x)) h
      simpa using hx
    · have hx := congrArg
          (fun q : StandardRelativeTransposeTarget ↦ q.2.2.2 (Additive.ofMul x)) h
      simpa using hx
  · rintro ⟨hA, hB, hC, hD⟩
    apply Prod.ext
    · ext x
      exact hA x
    · apply Prod.ext
      · ext x
        exact hB x
      · apply Prod.ext
        · ext x
          exact hC x
        · ext x
          exact hD x

def OneHandleC7StandardRelativeTargetTransposeVanishing
    (E : OneHandleC7RelativeLift) : Prop :=
  ∀ ell : ElemDual (Additive (oneHandleRelativeZLayer 6)),
    oneHandleC7StandardRelativeCoordinateTranspose ell = 0 →
      ell (Additive.ofMul (oneHandleC7RelativeTarget E)) = 0

theorem standardRelativeTargetTransposeVanishing_iff_target_mem_relaxed
    (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeTargetTransposeVanishing E ↔
      oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan := by
  rw [← standardRelativeCoordinateF2Vanishing_iff_target_mem_relaxed]
  constructor <;> intro H ell hell
  · exact H ell
      ((standardRelativeCoordinateTranspose_eq_zero_iff_rowsAnnihilate ell).mpr hell)
  · exact H ell
      ((standardRelativeCoordinateTranspose_eq_zero_iff_rowsAnnihilate ell).mp hell)

theorem relativeCorrectable_iff_coordinateF2_and_neutrality
    (E : OneHandleC7RelativeLift) :
    OneHandleC7RelativeCorrectable E ↔
      OneHandleC7StandardRelativeCoordinateF2Vanishing E ∧
      ∀ hrel : oneHandleC7RelativeTarget E ∈
          oneHandleStandardRelativeRelaxedCoordinateSpan,
        oneHandleC7StandardNeutralityObstruction E hrel = 1 := by
  rw [relativeCorrectable_iff_relaxed_and_neutrality]
  constructor
  · rintro ⟨hrel, hneutral⟩
    exact ⟨(standardRelativeCoordinateF2Vanishing_iff_target_mem_relaxed E).mpr hrel,
      fun hrel' ↦ by simpa only [Subsingleton.elim hrel' hrel] using hneutral⟩
  · rintro ⟨hF2, hneutral⟩
    let hrel :=
      (standardRelativeCoordinateF2Vanishing_iff_target_mem_relaxed E).mp hF2
    exact ⟨hrel, hneutral hrel⟩

#print axioms oneHandleC7StandardRelativeCokernel_sq
#print axioms oneHandleC7StandardRelativeCokernel_add_self
#print axioms standardRelativeF2Vanishing_iff_obstruction_eq_one
#print axioms standardRelativeAmbientF2Vanishing_iff_target_mem_relaxed
#print axioms oneHandleStandardRelativeShiftCRelaxed
#print axioms oneHandleStandardRelativeShiftCRelaxed_apply
#print axioms standardRelativeRowsAnnihilate_iff_spanAnnihilates
#print axioms standardRelativeCoordinateF2Vanishing_iff_target_mem_relaxed
#print axioms oneHandleC7StandardRelativeCoordinateTranspose
#print axioms standardRelativeCoordinateTranspose_eq_zero_iff_rowsAnnihilate
#print axioms standardRelativeTargetTransposeVanishing_iff_target_mem_relaxed
#print axioms relativeCorrectable_iff_coordinateF2_and_neutrality

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2
