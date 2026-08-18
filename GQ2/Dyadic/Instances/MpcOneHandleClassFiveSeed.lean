/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectRankRecurrence
import GQ2.Dyadic.Instances.MpcFive

/-!
# The explicit class-five seed at one handle

The compact class-five correction survives in `D_M(2,1)`: put `B⁴` in the `B` slot and
`B⁴[B²,D]` in the `D` slot, leaving both handle slots fixed.  A direct calculation in the
class-five quotient shows that its shift is exactly the defect of the class-four marking.  The
defect is a product of three central involutions, hence is its own inverse, so the correction
kills the relator.

This gives an explicit point in the fifth direct set.  Equivalently, the fourth-rung augmented
and coordinate transpose ranks agree and the four target-row coefficients exist.  This closes
the first direct recurrence step; it does not assert the later steps.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassFiveSeed

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad
open GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcOneHandleClassFourSeed
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank
open GQ2.Dyadic.Instances.MpcOneHandleDirectRowCoefficients
open GQ2.Roe.Labute

private abbrev H := DM 2 1

private theorem zcomm {z : levelQuot H 5} (hz : z ∈ zLayer H 4)
    (x : levelQuot H 5) : z * x = x * z :=
  (zLayer_commute hz x).eq

private theorem zinv_self {z : levelQuot H 5} (hz : z ∈ zLayer H 4) :
    z⁻¹ = z := by
  have hsq : z * z = 1 := by
    rw [← pow_two]
    exact zLayer_sq _ hz
  calc
    z⁻¹ = z⁻¹ * (z * z) := by rw [hsq, mul_one]
    _ = z := by group

private theorem swap {Q : Type*} [Group Q] (x y : Q) :
    commP x y = (commP y x)⁻¹ := by
  simp only [commP]
  group

private theorem cmove {Q : Type*} [Group Q] {z : Q}
    (hz : ∀ x : Q, z * x = x * z) (x y : Q) :
    x * z * y = x * y * z := by
  rw [mul_assoc, hz, ← mul_assoc]

private theorem cmoveL {Q : Type*} [Group Q] {z : Q}
    (hz : ∀ x : Q, z * x = x * z) (x y : Q) :
    x * y * z = x * z * y :=
  (cmove hz x y).symm

private theorem kill3 {Q : Type*} [Group Q] {a b c : Q}
    (ha : ∀ x : Q, a * x = x * a) (hb : ∀ x : Q, b * x = x * b)
    (ea : a * a = 1) (eb : b * b = 1) (ec : c * c = 1) :
    a * b * c * (a * (b * c)) = 1 := by
  calc
    a * b * c * (a * (b * c)) = a * b * c * a * b * c := by group
    _ = a * b * a * c * b * c := by rw [cmoveL ha (a * b) c]
    _ = a * a * b * c * b * c := by rw [cmoveL ha a b]
    _ = a * a * b * b * c * c := by rw [cmoveL hb (a * a * b) c]
    _ = 1 := by rw [ea, one_mul, eb, one_mul, ec]

private theorem witnessKill {Q : Type*} [Group Q]
    {x y zc dc f gc jc : Q}
    (hz : ∀ u : Q, zc * u = u * zc)
    (hd : ∀ u : Q, dc * u = u * dc)
    (hg : ∀ u : Q, gc * u = u * gc)
    (hzz : zc * zc = 1) (hxf : x * f = f * x) :
    x * y * (zc * dc) * (y⁻¹ * f) * (zc * gc) *
        (x⁻¹ * f⁻¹ * jc) = dc * gc * jc := by
  have hcomm : x * f * x⁻¹ * f⁻¹ = 1 := by rw [hxf]; group
  calc
    x * y * (zc * dc) * (y⁻¹ * f) * (zc * gc) *
        (x⁻¹ * f⁻¹ * jc) =
      x * y * zc * dc * y⁻¹ * f * zc * gc * x⁻¹ * f⁻¹ * jc := by group
    _ = x * zc * y * dc * y⁻¹ * f * zc * gc * x⁻¹ * f⁻¹ * jc := by
      rw [cmoveL hz x y]
    _ = x * zc * dc * y * y⁻¹ * f * zc * gc * x⁻¹ * f⁻¹ * jc := by
      rw [cmoveL hd (x * zc) y]
    _ = x * zc * dc * f * zc * gc * x⁻¹ * f⁻¹ * jc := by group
    _ = x * zc * dc * zc * f * gc * x⁻¹ * f⁻¹ * jc := by
      rw [cmoveL hz (x * zc * dc) f]
    _ = x * zc * dc * zc * gc * f * x⁻¹ * f⁻¹ * jc := by
      rw [cmoveL hg (x * zc * dc * zc) f]
    _ = x * zc * zc * dc * gc * f * x⁻¹ * f⁻¹ * jc := by
      rw [cmove hd (x * zc) zc]
    _ = x * dc * gc * f * x⁻¹ * f⁻¹ * jc := by
      rw [mul_assoc x zc zc, hzz, mul_one]
    _ = dc * x * gc * f * x⁻¹ * f⁻¹ * jc := by rw [← hd x]
    _ = dc * gc * x * f * x⁻¹ * f⁻¹ * jc := by rw [cmoveL hg dc x]
    _ = dc * gc * (x * f * x⁻¹ * f⁻¹) * jc := by group
    _ = dc * gc * jc := by rw [hcomm, mul_one]

def oneHandleW5Ut : H := dmB 2 1 ^ 4

def oneHandleW5Un : H :=
  dmB 2 1 ^ 4 * commP (dmB 2 1 ^ 2) (dmD 2 1)

def oneHandleW5Factors : Fin (coreRank 1) → H :=
  fullMark 1 oneHandleW5Ut 1 oneHandleW5Un (fun _ ↦ 1) (fun _ ↦ 1)

def oneHandleW5Defect : levelQuot H 5 :=
  levelMk H 5
    (commP (dmB 2 1 ^ 4) (dmA 2 1) *
      commP (dmC 2 1) (dmB 2 1 ^ 2) ^ 2 *
      commP (commP (dmB 2 1 ^ 2) (dmD 2 1)) (dmC 2 1))

theorem oneHandleW4Mark_defect_five :
    levelMk H 5 (mRelWord 2 oneHandleW4Mark) =
      levelMk H 5
        (commP (dmB 2 1 ^ 4) (dmA 2 1) *
          commP (dmC 2 1) (dmB 2 1 ^ 2) ^ 2 *
          commP (commP (dmB 2 1 ^ 2) (dmD 2 1)) (dmC 2 1)) := by
  let p := levelMk H 5 (dmA 2 1)
  let q := levelMk H 5 (dmB 2 1)
  let r := levelMk H 5 (dmC 2 1)
  let w := levelMk H 5 (dmD 2 1)
  let u := levelMk H 5 (dmGen 2 1 (handleIdxU (0 : Fin 1)))
  let v := levelMk H 5 (dmGen 2 1 (handleIdxV (0 : Fin 1)))
  let beta := commP w q
  have hbeta : beta ∈ lambdaImage H 2 5 := mpcFv_commP_mem_two w q
  have hz : (q ^ 4)⁻¹ ∈ lambdaImage H 3 5 :=
    Subgroup.inv_mem _ (cfive_pow_four_mem_lambdaThree q)
  have hword := mpcFv_mWord_five (G := H)
    (p := p) (q := q) (r := r) (w := w)
    (σ := beta) (τ := beta) (μ := 1) (ν := 1) (z := (q ^ 4)⁻¹)
    hbeta hbeta (one_mem _) (one_mem _) hz
  have hbase : mWord 2 p q r w * commP u v = 1 := by
    have h := congrArg (levelMk H 5) (dm_relation 2 1)
    rw [map_one, map_mRelWord, mRelWord, handleWord_one] at h
    exact h
  change levelMk H 5 (mRelWord 2 oneHandleW4Mark) = _
  simp only [oneHandleW4Mark, mRelWord, standardHandleMark_zero,
    standardHandleMark_one, standardHandleMark_two,
    standardHandleMark_three, standardHandleMark_handleU,
    standardHandleMark_handleV, handleWord, List.finRange, map_mul,
    map_pow, oneHandleW4]
  change mWord 2 (p * (q ^ 4)⁻¹ * beta) (q * beta)
      (q ^ 2 * r) w * commP u v =
        commP (q ^ 4) p * commP r (q ^ 2) ^ 2 *
          commP (commP (q ^ 2) w) r
  simp only [mul_one] at hword
  rw [hword]
  simp only [mpcFv_z_sq, mpcFv_z_commP, mpcFv_pow_four_commP_self,
    cfour_comm_one, cfour_one_comm, one_pow, one_mul, mul_one]
  have hq2 : q ^ 2 ∈ lambdaImage H 2 5 := mpcLad_five_sq_mem_two _
  have hq4 : q ^ 4 ∈ lambdaImage H 3 5 :=
    cfive_pow_four_mem_lambdaThree _
  have hW : commP w q ∈ lambdaImage H 2 5 := mpcFv_commP_mem_two _ _
  have hpq : commP p q ∈ lambdaImage H 2 5 := mpcFv_commP_mem_two _ _
  have hWsq : commP w q ^ 2 ∈ lambdaImage H 3 5 :=
    mpcFv_sq_mem_three hW
  have hWq : commP (commP w q) q ∈ lambdaImage H 3 5 :=
    mpcFv_commP_mem_three_left hW _
  have hK : commP (commP p q) (commP w q) *
      commP (commP p q) (commP w q) = 1 := by
    rw [← pow_two]
    exact zLayer_sq _ (mpcFv_commP_mem_zLayer_two hpq hW)
  have hY : commP p (commP w q) = (commP (commP w q) p)⁻¹ := swap _ _
  have hH : commP q w ^ 2 = (commP w q ^ 2)⁻¹ := by
    rw [swap q w, inv_pow]
  have hI : commP (commP q w) q = (commP (commP w q) q)⁻¹ := by
    rw [swap q w, mpcFv_commP_inv_left_two hW]
  have hcorr :
      beta ^ 2 * commP beta p *
          (q ^ 8 * commP (q ^ 4) p) *
          (commP p beta * commP beta q *
            (commP beta beta * commP (commP p q) beta *
              commP (commP p q) beta)) *
          (q ^ 8 * (commP r (q ^ 2) ^ 2)) *
          (commP q w ^ 2 * commP (commP q w) q *
            commP (commP (q ^ 2) w) r) =
        commP (q ^ 4) p * commP r (q ^ 2) ^ 2 *
          commP (commP (q ^ 2) w) r := by
    simp only [beta, mpcFv_commP_self, one_mul]
    rw [hK, mul_one, hY, hH, hI]
    exact witnessKill
      (x := beta ^ 2) (y := commP beta p) (zc := q ^ 8)
      (dc := commP (q ^ 4) p) (f := commP beta q)
      (gc := commP r (q ^ 2) ^ 2)
      (jc := commP (commP (q ^ 2) w) r)
      (zcomm (cfive_pow_eight_mem_zLayer q))
      (zcomm (mpcFv_commP_mem_zLayer_left hq4 _))
      (zcomm (mpcFv_sq_mem_zLayer (mpcFv_commP_mem_three_right _ hq2)))
      (by rw [← pow_two]; exact zLayer_sq _ (cfive_pow_eight_mem_zLayer q))
      (mpcFv_lycomm (mpcFv_three_le_two hWq) hWsq)
  rw [hcorr]
  have hsurv : commP (q ^ 4) p * commP r (q ^ 2) ^ 2 *
      commP (commP (q ^ 2) w) r ∈ zLayer H 4 := by
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (mpcFv_commP_mem_zLayer_left hq4 _)
        (mpcFv_sq_mem_zLayer (mpcFv_commP_mem_three_right _ hq2)))
      (mpcFv_commP_mem_zLayer_left
        (mpcFv_commP_mem_three_left hq2 _) _)
  rw [mul_assoc, zcomm hsurv (commP u v), ← mul_assoc, hbase, one_mul]

theorem oneHandleW5_b2_mem_two :
    dmB 2 1 ^ 2 ∈ twoCentralSeries H 2 :=
  sq_mem_twoCentralSeries_succ _ (Subgroup.mem_top _)

theorem oneHandleW5Ut_mem_three :
    oneHandleW5Ut ∈ twoCentralSeries H 3 := by
  have h : oneHandleW5Ut = (dmB 2 1 ^ 2) ^ 2 := by
    rw [oneHandleW5Ut, ← pow_mul]
  rw [h]
  exact sq_mem_twoCentralSeries_succ _ oneHandleW5_b2_mem_two

theorem oneHandleW5Un_mem_three :
    oneHandleW5Un ∈ twoCentralSeries H 3 := by
  exact Subgroup.mul_mem _ oneHandleW5Ut_mem_three
    (cfour_commP_mem_three oneHandleW5_b2_mem_two _)

theorem oneHandleW5Factors_depth (i : Fin (coreRank 1)) :
    oneHandleW5Factors i ∈ twoCentralSeries H 3 := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [oneHandleW5Factors]
  · simpa [oneHandleW5Factors] using oneHandleW5Ut_mem_three
  · simp [oneHandleW5Factors]
  · simpa [oneHandleW5Factors] using oneHandleW5Un_mem_three
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleW5Factors, mHandleIdx_coordU, mHandleIdx_coordV]

theorem oneHandleW5Factors_chi (i : Fin (coreRank 1)) :
    chiM 2 1 (oneHandleW5Factors i) = 1 := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [oneHandleW5Factors]
  · rw [oneHandleW5Factors, fullMark_one, oneHandleW5Ut, map_pow,
      chiM_dmB, show (4 : ℕ) = 2 * 2 by omega, pow_mul, neg_one_sq,
      one_pow]
  · simp [oneHandleW5Factors]
  · rw [oneHandleW5Factors, fullMark_three, oneHandleW5Un, map_mul,
      map_pow, chiM_dmB,
      show (4 : ℕ) = 2 * 2 by omega, pow_mul, neg_one_sq, one_pow,
      one_mul]
    simp only [commP, map_mul, map_inv]
    rw [mul_assoc ((chiM 2 1) (dmB 2 1 ^ 2))⁻¹
        ((chiM 2 1) (dmD 2 1))⁻¹,
      mul_comm ((chiM 2 1) (dmD 2 1))⁻¹
        ((chiM 2 1) (dmB 2 1 ^ 2)),
      ← mul_assoc ((chiM 2 1) (dmB 2 1 ^ 2))⁻¹]
    group
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleW5Factors, mHandleIdx_coordU, mHandleIdx_coordV]

theorem oneHandleW5_shift_eq_defect :
    oneHandleDirectRelatorShift oneHandleW4Mark oneHandleW5Factors 4 =
      levelMk H 5
        (commP (dmB 2 1 ^ 4) (dmA 2 1) *
          commP (dmC 2 1) (dmB 2 1 ^ 2) ^ 2 *
          commP (commP (dmB 2 1 ^ 2) (dmD 2 1)) (dmC 2 1)) := by
  have hdepth : ∀ i, levelMk H 5 (oneHandleW5Factors i) ∈
      lambdaImage H 3 5 := fun i ↦
    ⟨oneHandleW5Factors i, oneHandleW5Factors_depth i, rfl⟩
  rw [oneHandleDirectRelatorShift,
    evenRawStageShift_m (G := H) (by omega) (by omega) 1 4 (by omega)
      (fun i ↦ levelMk H 5 (oneHandleW4Mark i))
      (fun i ↦ levelMk H 5 (oneHandleW5Factors i)) hdepth]
  simp [evenRawDbarWord, evenRawCoreDbarWord, evenRawHandleDbarWord,
    oneHandleW5Factors, oneHandleW5Ut, oneHandleW5Un,
    oneHandleW4Mark, oneHandleW4, cfour_one_comm]
  let p := levelMk H 5 (dmA 2 1)
  let q := levelMk H 5 (dmB 2 1)
  let r := levelMk H 5 (dmC 2 1)
  let w := levelMk H 5 (dmD 2 1)
  let beta := commP w q
  let br := commP (q ^ 2) w
  change commP (q ^ 4) (p * (q ^ 4)⁻¹ * beta) *
      commP (q ^ 4 * br) (q ^ 2 * r) =
    commP (q ^ 4) p * commP r (q ^ 2) ^ 2 * commP br r
  have hq2 : q ^ 2 ∈ lambdaImage H 2 5 := mpcLad_five_sq_mem_two q
  have hq4 : q ^ 4 ∈ lambdaImage H 3 5 :=
    cfive_pow_four_mem_lambdaThree q
  have hbeta : beta ∈ lambdaImage H 2 5 :=
    mpcFv_commP_mem_two w q
  have hbr : br ∈ lambdaImage H 3 5 :=
    mpcFv_commP_mem_three_left hq2 w
  have hfirst : commP (q ^ 4) (p * (q ^ 4)⁻¹ * beta) =
      commP (q ^ 4) p := by
    rw [cfour_commP_mul_right, mpcFv_vanish' hbeta hq4, one_mul,
      mpcFv_commP_zLayer_left
        (mpcFv_commP_mem_zLayer_left hq4 (p * (q ^ 4)⁻¹)) beta,
      mul_one, cfour_commP_mul_right,
      mpcFv_vanish33 hq4 (Subgroup.inv_mem _ hq4), one_mul,
      mpcFv_commP_zLayer_left
        (mpcFv_commP_mem_zLayer_left hq4 p) (q ^ 4)⁻¹,
      mul_one]
  have hpow : commP r (q ^ 4) = commP r (q ^ 2) ^ 2 := by
    have e : q ^ 4 = q ^ 2 * q ^ 2 := by rw [← pow_add]
    rw [e, cfour_commP_mul_right,
      mpcFv_vanish' hq2 (mpcFv_commP_mem_three_right r hq2),
      mul_one, ← pow_two]
  have hsecond : commP (q ^ 4 * br) (q ^ 2 * r) =
      commP r (q ^ 2) ^ 2 * commP br r := by
    have hun : q ^ 4 * br ∈ lambdaImage H 3 5 :=
      Subgroup.mul_mem _ hq4 hbr
    rw [cfour_commP_mul_right, mpcFv_vanish' hq2 hun,
      cfour_one_comm]
    simp only [mul_one]
    rw [mpcFv_commP_left_add hq4 r, swap (q ^ 4) r,
      zinv_self (mpcFv_commP_mem_zLayer_right r hq4), hpow]
  rw [hfirst, hsecond, mul_assoc]

theorem oneHandleW4Mark_defect_five_eq :
    levelMk H 5 (mRelWord 2 oneHandleW4Mark) = oneHandleW5Defect := by
  simpa only [oneHandleW5Defect] using oneHandleW4Mark_defect_five

theorem oneHandleW5_shift_eq :
    oneHandleDirectRelatorShift oneHandleW4Mark oneHandleW5Factors 4 =
      oneHandleW5Defect := by
  simpa only [oneHandleW5Defect] using oneHandleW5_shift_eq_defect

theorem oneHandleW5Defect_inv : oneHandleW5Defect⁻¹ = oneHandleW5Defect := by
  let p := levelMk H 5 (dmA 2 1)
  let q := levelMk H 5 (dmB 2 1)
  let r := levelMk H 5 (dmC 2 1)
  let w := levelMk H 5 (dmD 2 1)
  let a := commP (q ^ 4) p
  let b := commP r (q ^ 2) ^ 2
  let c := commP (commP (q ^ 2) w) r
  rw [oneHandleW5Defect]
  simp only [map_mul, map_pow, Marking.map_commP]
  change (a * b * c)⁻¹ = a * b * c
  have hq2 : q ^ 2 ∈ lambdaImage H 2 5 := mpcLad_five_sq_mem_two q
  have ha : a ∈ zLayer H 4 :=
    mpcFv_commP_mem_zLayer_left (cfive_pow_four_mem_lambdaThree q) p
  have hb : b ∈ zLayer H 4 :=
    mpcFv_sq_mem_zLayer (mpcFv_commP_mem_three_right r hq2)
  have hc : c ∈ zLayer H 4 :=
    mpcFv_commP_mem_zLayer_left
      (mpcFv_commP_mem_three_left hq2 w) r
  have hdd : (a * b * c) * (a * b * c) = 1 := by
    calc
      (a * b * c) * (a * b * c) = a * b * c * (a * (b * c)) := by
        group
      _ = 1 := kill3 (zcomm ha) (zcomm hb)
        (by simpa only [pow_two] using zLayer_sq _ ha)
        (by simpa only [pow_two] using zLayer_sq _ hb)
        (by simpa only [pow_two] using zLayer_sq _ hc)
  exact inv_eq_of_mul_eq_one_right hdd

theorem oneHandleW5_relator_mem_five :
    mRelWord 2 (oneHandleDirectModify oneHandleW4Mark oneHandleW5Factors) ∈
      twoCentralSeries H 5 := by
  apply (lim_mem_twoCentralSeries_iff_levelMk 5 _).mpr
  have hshift := oneHandleW5_shift_eq
  rw [oneHandleDirectRelatorShift_eq, oneHandleW4Mark_defect_five_eq,
    oneHandleW5Defect_inv] at hshift
  apply mul_left_cancel (a := oneHandleW5Defect)
  simpa only [mul_one] using hshift

theorem oneHandleW4Mark_mem_direct_four :
    oneHandleW4Mark ∈ oneHandleDirectSet 4 :=
  ⟨oneHandleW4Mark_modTwoIndep, oneHandleW4Mark_handles,
    oneHandleW4Mark_chi, oneHandleW4Mark_C_row,
    oneHandleW4Mark_relator_mem_four⟩

def oneHandleW4Correction : OneHandleDirectCorrection oneHandleW4Mark 4 where
  factors := oneHandleW5Factors
  depth i := by simpa using oneHandleW5Factors_depth i
  handleU j := by simp [oneHandleW5Factors]
  handleV j := by simp [oneHandleW5Factors]
  chi := oneHandleW5Factors_chi
  row f := by simp [oneHandleW5Factors]
  kills := by
    rw [oneHandleW5_shift_eq, oneHandleW4Mark_defect_five_eq]
    exact oneHandleW5Defect_inv.symm

theorem oneHandleW5Mark_mem_direct_five :
    oneHandleDirectModify oneHandleW4Mark oneHandleW5Factors ∈
      oneHandleDirectSet 5 :=
  oneHandleW4Correction.toSuccessor (by omega)
    oneHandleW4Mark_mem_direct_four

theorem oneHandleDirectSet_five_nonempty :
    (oneHandleDirectSet 5).Nonempty :=
  ⟨oneHandleDirectModify oneHandleW4Mark oneHandleW5Factors,
    oneHandleW5Mark_mem_direct_five⟩

theorem oneHandleW4Mark_augmentedTranspose_finrank_eq :
    oneHandleDirectAugmentedTransposeRank (by omega)
        oneHandleW4Mark_mem_direct_four =
      oneHandleDirectCoordinateTransposeRank oneHandleW4Mark 4 (by omega) :=
  (nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
    (by omega) oneHandleW4Mark_mem_direct_four).mp ⟨oneHandleW4Correction⟩

theorem oneHandleW4Mark_targetRowCoefficients :
    OneHandleDirectTargetRowCoefficients (by omega)
      oneHandleW4Mark_mem_direct_four :=
  (targetRowCoefficients_iff_nonempty_directCorrection
    (by omega) oneHandleW4Mark_mem_direct_four).mpr ⟨oneHandleW4Correction⟩

#print axioms oneHandleW4Mark_defect_five
#print axioms oneHandleW5_shift_eq_defect
#print axioms oneHandleW5Defect_inv
#print axioms oneHandleW5_relator_mem_five
#print axioms oneHandleW4Correction
#print axioms oneHandleW5Mark_mem_direct_five
#print axioms oneHandleDirectSet_five_nonempty
#print axioms oneHandleW4Mark_augmentedTranspose_finrank_eq
#print axioms oneHandleW4Mark_targetRowCoefficients

end
end GQ2.Dyadic.Instances.MpcOneHandleClassFiveSeed
