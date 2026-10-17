/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSixTarget
import GQ2.Dyadic.Instances.MpcC6WeightedTraceFinal

/-!
# Lifting the compact class-six correction to one handle

This module applies the checked compact class-six factors verbatim to the explicit one-handle
class-five marking.  The factors remain legal: they have depth four, preserve the handle
letters and cyclotomic row, and have zero distinguished pivot row.  After forgetting the
handle, the modified marking is exactly the compact class-six marking certified by the
weighted trace calculation.

Consequently its class-six relator has trivial compact image.  The only possible failure is
the explicit element `oneHandleC6Residual`, which lies simultaneously in the depth-five
central layer and in the kernel of handle-forgetting.  The candidate is a genuine class-six
correction exactly when this residual is one.  No vanishing of the relative residual is
asserted here; the result removes every compact contribution and isolates the precise new
handle obstruction.
-/


namespace GQ2.Dyadic.Instances.MpcOneHandleClassSixCompactLift

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad
open GQ2.Dyadic.Instances.MpcMk
open GQ2.Dyadic.Instances.MpcMkC6
open GQ2.Dyadic.Instances.MpcC6WeightedTraceFinal
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleClassFourSeed
open GQ2.Dyadic.Instances.MpcOneHandleClassFiveSeed
open GQ2.Dyadic.Instances.MpcOneHandleClassSixTarget
open GQ2.Roe.Labute

private abbrev H := DM 2 1
private abbrev A : H := dmA 2 1
private abbrev B : H := dmB 2 1
private abbrev C : H := dmC 2 1
private abbrev D : H := dmD 2 1

def oneHandleC6Us : H :=
  commP (commP B D) A ^ 2 * commP (B ^ 2) A ^ 2 *
    commP (commP B C) B ^ 2 * commP (commP (commP B D) B) A *
    commP (commP (commP B C) B) B * commP (commP (commP B D) B) B *
    commP (commP (commP B D) D) B

def oneHandleC6Ut : H :=
  B ^ 8 * commP (commP B C) B ^ 2 * commP (commP B D) B ^ 2 *
    commP (commP (commP B C) B) B * commP (commP (commP B D) D) B

def oneHandleC6Um : H :=
  commP (commP B D) B ^ 2 * commP (commP (commP B D) B) B

def oneHandleC6Un : H :=
  commP B C ^ 4 * commP (commP B C) B ^ 2 *
    commP (commP B C) C ^ 2 * commP (commP (commP B C) C) B

def oneHandleC6Factors : Fin (coreRank 1) → H :=
  fullMark oneHandleC6Us oneHandleC6Ut oneHandleC6Um oneHandleC6Un
    (fun _ ↦ 1) (fun _ ↦ 1)

private theorem comm_three (x y z : H) :
    commP (commP x y) z ∈ twoCentralSeries H 3 :=
  cfour_commP_mem_three (cfour_commP_mem_two x y) z

private theorem sq_comm_three_four (x y z : H) :
    commP (commP x y) z ^ 2 ∈ twoCentralSeries H 4 :=
  sq_mem_twoCentralSeries_succ _ (comm_three x y z)

private theorem comm_four (x y z w : H) :
    commP (commP (commP x y) z) w ∈ twoCentralSeries H 4 :=
  cfour_commP_mem_four (comm_three x y z) w

private theorem sq_comm_sq_four (x y : H) :
    commP (x ^ 2) y ^ 2 ∈ twoCentralSeries H 4 := by
  apply sq_mem_twoCentralSeries_succ
  apply cfour_commP_mem_three
  exact sq_mem_twoCentralSeries_succ _
    (show x ∈ twoCentralSeries H 1 by simp)

private theorem comm_pow_four_mem_four (x y : H) :
    commP x y ^ 4 ∈ twoCentralSeries H 4 := by
  have h3 : commP x y ^ 2 ∈ twoCentralSeries H 3 :=
    sq_mem_twoCentralSeries_succ _ (cfour_commP_mem_two x y)
  have h4 : (commP x y ^ 2) ^ 2 ∈ twoCentralSeries H 4 :=
    sq_mem_twoCentralSeries_succ _ h3
  convert h4 using 1
  norm_num [← pow_mul]

theorem oneHandleC6Us_mem : oneHandleC6Us ∈ twoCentralSeries H 4 := by
  simp only [oneHandleC6Us]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (sq_comm_three_four B D A) (sq_comm_sq_four B A))
      (sq_comm_three_four B C B)) (comm_four B D B A))
      (comm_four B C B B)) (comm_four B D B B)) (comm_four B D D B)

theorem oneHandleC6Ut_mem : oneHandleC6Ut ∈ twoCentralSeries H 4 := by
  simp only [oneHandleC6Ut]
  have hB8 : B ^ 8 ∈ twoCentralSeries H 4 := by
    convert pow_two_pow_mem_twoCentralSeries_succ (G := H) B 3 using 1
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ hB8 (sq_comm_three_four B C B))
      (sq_comm_three_four B D B)) (comm_four B C B B)) (comm_four B D D B)

theorem oneHandleC6Um_mem : oneHandleC6Um ∈ twoCentralSeries H 4 := by
  simp only [oneHandleC6Um]
  exact Subgroup.mul_mem _ (sq_comm_three_four B D B) (comm_four B D B B)

theorem oneHandleC6Un_mem : oneHandleC6Un ∈ twoCentralSeries H 4 := by
  simp only [oneHandleC6Un]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (comm_pow_four_mem_four B C) (sq_comm_three_four B C B))
      (sq_comm_three_four B C C)) (comm_four B C C B)

theorem oneHandleC6Factors_depth (i : Fin (coreRank 1)) :
    oneHandleC6Factors i ∈ twoCentralSeries H 4 := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simpa [oneHandleC6Factors] using oneHandleC6Us_mem
  · simpa [oneHandleC6Factors] using oneHandleC6Ut_mem
  · simpa [oneHandleC6Factors] using oneHandleC6Um_mem
  · simpa [oneHandleC6Factors] using oneHandleC6Un_mem
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleC6Factors, mHandleIdx_coordU, mHandleIdx_coordV]

private theorem chi_commP (x y : H) : chiM 2 1 (commP x y) = 1 := by
  exact map_commP_eq_one (chiM 2 1).toMonoidHom x y

theorem oneHandleC6Factors_chi (i : Fin (coreRank 1)) :
    chiM 2 1 (oneHandleC6Factors i) = 1 := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [oneHandleC6Factors, oneHandleC6Us, chi_commP]
  · have hB8 : chiM 2 1 (B ^ 8) = 1 := by
      rw [map_pow, chiM_dmB, show (8 : ℕ) = 2 * 4 by omega,
        pow_mul, neg_one_sq, one_pow]
    simp [oneHandleC6Factors, oneHandleC6Ut, chi_commP, hB8]
  · simp [oneHandleC6Factors, oneHandleC6Um, chi_commP]
  · simp [oneHandleC6Factors, oneHandleC6Un, chi_commP]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleC6Factors, mHandleIdx_coordU, mHandleIdx_coordV]

theorem oneHandleC6Factors_row
    (f : ContinuousMonoidHom H (Multiplicative ℤ_[2])) :
    toAdd (f (oneHandleC6Factors 2)) = 0 := by
  have h1 := map_commP_eq_one f.toMonoidHom (commP B D) B
  have h2 := map_commP_eq_one f.toMonoidHom (commP (commP B D) B) B
  simp only [oneHandleC6Factors, fullMark_two, oneHandleC6Um,
    map_mul, map_pow]
  change toAdd (f.toMonoidHom (commP (commP B D) B) ^ 2 *
    f.toMonoidHom (commP (commP (commP B D) B) B)) = 0
  rw [h1, h2, one_pow, one_mul, toAdd_one]

def OneHandleC6CertificateKill : Prop :=
  oneHandleDirectRelatorShift oneHandleW5Mark oneHandleC6Factors 5 =
    (levelMk H 6 (mRelWord 2 oneHandleW5Mark))⁻¹

def oneHandleW5Correction_of_certificate
    (h : OneHandleC6CertificateKill) :
    OneHandleDirectCorrection oneHandleW5Mark 5 where
  factors := oneHandleC6Factors
  depth := oneHandleC6Factors_depth
  handleU j := by simp [oneHandleC6Factors]
  handleV j := by simp [oneHandleC6Factors]
  chi := oneHandleC6Factors_chi
  row := oneHandleC6Factors_row
  kills := h

theorem dmForgetHandles_oneHandleC6Us :
    dmForgetHandles 2 1 oneHandleC6Us = mpcMkC6Us := by
  simp [oneHandleC6Us, mpcMkC6Us, map_mul, map_pow, commP,
    dmForgetHandles_dmA, dmForgetHandles_dmB, dmForgetHandles_dmC,
    dmForgetHandles_dmD]

theorem dmForgetHandles_oneHandleC6Ut :
    dmForgetHandles 2 1 oneHandleC6Ut = mpcMkC6Ut := by
  simp [oneHandleC6Ut, mpcMkC6Ut, map_mul, map_pow, commP,
    dmForgetHandles_dmB, dmForgetHandles_dmC, dmForgetHandles_dmD]

theorem dmForgetHandles_oneHandleC6Um :
    dmForgetHandles 2 1 oneHandleC6Um = mpcMkC6Um := by
  simp [oneHandleC6Um, mpcMkC6Um, map_mul, map_pow, commP,
    dmForgetHandles_dmB, dmForgetHandles_dmD]

theorem dmForgetHandles_oneHandleC6Un :
    dmForgetHandles 2 1 oneHandleC6Un = mpcMkC6Un := by
  simp [oneHandleC6Un, mpcMkC6Un, map_mul, map_pow, commP,
    dmForgetHandles_dmB, dmForgetHandles_dmC]

def compactW5Mark : Fin (coreRank 1) → (DM 2 0 : Type) :=
  fullMark (mpcWordLetA mpcFvW5.1) (mpcWordLetB mpcFvW5.2.1)
    (mpcWordLetC mpcFvW5.2.2.1) (mpcWordLetD mpcFvW5.2.2.2)
    (fun _ ↦ 1) (fun _ ↦ 1)

def compactC6Factors : Fin (coreRank 1) → (DM 2 0 : Type) :=
  fullMark mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un
    (fun _ ↦ 1) (fun _ ↦ 1)

def compactC6Mark : Fin (coreRank 1) → (DM 2 0 : Type) :=
  fun i ↦ compactW5Mark i * compactC6Factors i

theorem dmForgetHandles_oneHandleW5Mark (i : Fin (coreRank 1)) :
    dmForgetHandles 2 1 (oneHandleW5Mark i) = compactW5Mark i := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [oneHandleW5Mark, oneHandleDirectModify, oneHandleW4Mark,
      oneHandleW5Factors, compactW5Mark, mpcFvW5, mpcBldW, mpcWordLetA,
      oneHandleW4, commP]
  · simp [oneHandleW5Mark, oneHandleDirectModify, oneHandleW4Mark,
      oneHandleW5Factors, oneHandleW5Ut, compactW5Mark, mpcFvW5,
      mpcBldW, mpcFvUt, mpcWordLetB, oneHandleW4, commP]
    group
  · simp [oneHandleW5Mark, oneHandleDirectModify, oneHandleW4Mark,
      oneHandleW5Factors, compactW5Mark, mpcFvW5, mpcWordLetC]
  · simp [oneHandleW5Mark, oneHandleDirectModify, oneHandleW4Mark,
      oneHandleW5Factors, oneHandleW5Un, compactW5Mark, mpcFvW5,
      mpcFvUn, mpcWordLetD, commP]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleW5Mark, oneHandleDirectModify, oneHandleW4Mark,
        oneHandleW5Factors, compactW5Mark, mHandleIdx_coordU,
        mHandleIdx_coordV]

theorem dmForgetHandles_oneHandleC6Factors (i : Fin (coreRank 1)) :
    dmForgetHandles 2 1 (oneHandleC6Factors i) = compactC6Factors i := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simpa [oneHandleC6Factors, compactC6Factors] using
      dmForgetHandles_oneHandleC6Us
  · simpa [oneHandleC6Factors, compactC6Factors] using
      dmForgetHandles_oneHandleC6Ut
  · simpa [oneHandleC6Factors, compactC6Factors] using
      dmForgetHandles_oneHandleC6Um
  · simpa [oneHandleC6Factors, compactC6Factors] using
      dmForgetHandles_oneHandleC6Un
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleC6Factors, compactC6Factors, mHandleIdx_coordU,
        mHandleIdx_coordV]

theorem dmForgetHandles_oneHandleC6Mark (i : Fin (coreRank 1)) :
    dmForgetHandles 2 1
        (oneHandleDirectModify oneHandleW5Mark oneHandleC6Factors i) =
      compactC6Mark i := by
  rw [oneHandleDirectModify, map_mul, dmForgetHandles_oneHandleW5Mark,
    dmForgetHandles_oneHandleC6Factors]
  rfl

def compactC6Tuple :
    (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type) :=
  (mpcFvW5.1 * mpcMkC6Us, mpcFvW5.2.1 * mpcMkC6Ut,
    mpcFvW5.2.2.1 * mpcMkC6Um, mpcFvW5.2.2.2 * mpcMkC6Un)

theorem compactC6Tuple_mem : compactC6Tuple ∈ mpcWordSet 6 := by
  have hm := mpcMk_fullMove_ladMove (j := 4) (by omega) mpcMkC6_fullMove
  have hkill :
      mpcLadDefect mpcFvW5 *
          mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2
            mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un ∈
        twoCentralSeries (DM 2 0 : Type) 6 :=
    (lim_mem_twoCentralSeries_iff_levelMk 6 _).mpr mpcMkC6_certificateKill
  exact mpcBld_step mpcFv_w5_mem mpcMkC6Us mpcMkC6Ut mpcMkC6Um
    mpcMkC6Un hm.1.1 hm.1.2 hm.2.1.1 hm.2.1.2 hm.2.2.1.1
    hm.2.2.1.2 hm.2.2.2.1 hm.2.2.2.2 hkill

theorem compactC6Mark_relator :
    mRelWord 2 compactC6Mark = mpcLadDefect compactC6Tuple := by
  simp [compactC6Mark, compactW5Mark, compactC6Factors,
    compactC6Tuple, mRelWord, handleWord_one, mpcLadDefect,
    mpcWordLetA, mpcWordLetB, mpcWordLetC, mpcWordLetD]
  group

theorem dmForgetHandles_oneHandleC6Relator :
    dmForgetHandles 2 1
        (mRelWord 2
          (oneHandleDirectModify oneHandleW5Mark oneHandleC6Factors)) =
      mRelWord 2 compactC6Mark := by
  rw [map_mRelWord]
  congr 1
  funext i
  exact dmForgetHandles_oneHandleC6Mark i

theorem dmForgetHandles_oneHandleC6Relator_mem :
    dmForgetHandles 2 1
        (mRelWord 2
          (oneHandleDirectModify oneHandleW5Mark oneHandleC6Factors)) ∈
      twoCentralSeries (DM 2 0 : Type) 6 := by
  rw [dmForgetHandles_oneHandleC6Relator, compactC6Mark_relator]
  exact compactC6Tuple_mem.2.2.2.2

noncomputable def dmForgetHandlesLevelSix :
    levelQuot H 6 →* levelQuot (DM 2 0 : Type) 6 :=
  QuotientGroup.map (twoCentralSeries H 6)
    (twoCentralSeries (DM 2 0 : Type) 6)
    (dmForgetHandles 2 1).toMonoidHom (by
      intro x hx
      exact map_twoCentralSeries_le (dmForgetHandles 2 1).toMonoidHom
        (dmForgetHandles 2 1).continuous_toFun 6 ⟨x, hx, rfl⟩)

@[simp] theorem dmForgetHandlesLevelSix_levelMk (x : H) :
    dmForgetHandlesLevelSix (levelMk H 6 x) =
      levelMk (DM 2 0 : Type) 6 (dmForgetHandles 2 1 x) := by
  rfl

def oneHandleC6Residual : levelQuot H 6 :=
  levelMk H 6
    (mRelWord 2
      (oneHandleDirectModify oneHandleW5Mark oneHandleC6Factors))

theorem oneHandleC6Residual_forget_eq_one :
    dmForgetHandlesLevelSix oneHandleC6Residual = 1 := by
  rw [oneHandleC6Residual, dmForgetHandlesLevelSix_levelMk]
  apply (lim_mem_twoCentralSeries_iff_levelMk 6 _).mp
  exact dmForgetHandles_oneHandleC6Relator_mem

theorem oneHandleC6Residual_mem_ker :
    oneHandleC6Residual ∈ dmForgetHandlesLevelSix.ker :=
  oneHandleC6Residual_forget_eq_one

theorem oneHandleC6Residual_mem_zLayer : oneHandleC6Residual ∈ zLayer H 5 := by
  have hdepth : ∀ i, levelMk H 6 (oneHandleC6Factors i) ∈
      lambdaImage H 4 6 := fun i ↦
    ⟨oneHandleC6Factors i, oneHandleC6Factors_depth i, rfl⟩
  have hshift :
      oneHandleDirectRelatorShift oneHandleW5Mark oneHandleC6Factors 5 ∈
        zLayer H 5 := by
    rw [oneHandleDirectRelatorShift,
      evenRawStageShift_m (G := H) (by omega) (by omega) 1 5 (by omega)
        (fun i ↦ levelMk H 6 (oneHandleW5Mark i))
        (fun i ↦ levelMk H 6 (oneHandleC6Factors i)) hdepth]
    exact evenRawDbarWord_mem_zLayer 1 5 (by omega) _ _ hdepth
  have horig : levelMk H 6 (mRelWord 2 oneHandleW5Mark) ∈ zLayer H 5 :=
    ⟨mRelWord 2 oneHandleW5Mark, oneHandleW5Mark_mem.2.2.2.2, rfl⟩
  rw [oneHandleDirectRelatorShift_eq] at hshift
  change (levelMk H 6 (mRelWord 2 oneHandleW5Mark))⁻¹ *
      oneHandleC6Residual ∈ zLayer H 5 at hshift
  have hprod := Subgroup.mul_mem _ horig hshift
  have heq :
      levelMk H 6 (mRelWord 2 oneHandleW5Mark) *
          ((levelMk H 6 (mRelWord 2 oneHandleW5Mark))⁻¹ *
            oneHandleC6Residual) =
        oneHandleC6Residual := by
    group
  rw [heq] at hprod
  exact hprod

def oneHandleC6RelativeLayer : Subgroup (levelQuot H 6) :=
  zLayer H 5 ⊓ dmForgetHandlesLevelSix.ker

theorem oneHandleC6Residual_mem_relativeLayer :
    oneHandleC6Residual ∈ oneHandleC6RelativeLayer :=
  ⟨oneHandleC6Residual_mem_zLayer, oneHandleC6Residual_mem_ker⟩

theorem oneHandleC6CertificateKill_iff_residual_eq_one :
    OneHandleC6CertificateKill ↔ oneHandleC6Residual = 1 := by
  rw [OneHandleC6CertificateKill, oneHandleDirectRelatorShift_eq]
  change (levelMk H 6 (mRelWord 2 oneHandleW5Mark))⁻¹ *
      oneHandleC6Residual =
        (levelMk H 6 (mRelWord 2 oneHandleW5Mark))⁻¹ ↔ _
  constructor
  · intro h
    exact mul_left_cancel (by simpa only [mul_one] using h)
  · intro h
    rw [h, mul_one]

theorem oneHandleW5Correctable_of_C6Residual_eq_one
    (h : oneHandleC6Residual = 1) : OneHandleW5Correctable :=
  ⟨oneHandleW5Correction_of_certificate
    (oneHandleC6CertificateKill_iff_residual_eq_one.mpr h)⟩

theorem oneHandleDirectSet_six_nonempty_of_C6Residual_eq_one
    (h : oneHandleC6Residual = 1) : (oneHandleDirectSet 6).Nonempty :=
  oneHandleDirectSet_six_nonempty_of_W5Correctable
    (oneHandleW5Correctable_of_C6Residual_eq_one h)

#print axioms oneHandleC6Factors_depth
#print axioms oneHandleC6Factors_chi
#print axioms oneHandleC6Factors_row
#print axioms dmForgetHandles_oneHandleC6Relator_mem
#print axioms oneHandleC6Residual_mem_relativeLayer
#print axioms oneHandleC6CertificateKill_iff_residual_eq_one
#print axioms oneHandleW5Correctable_of_C6Residual_eq_one
#print axioms oneHandleDirectSet_six_nonempty_of_C6Residual_eq_one

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSixCompactLift

