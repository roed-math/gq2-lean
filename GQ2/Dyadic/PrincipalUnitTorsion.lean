/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import Mathlib.Algebra.Group.Torsion
import GQ2.TeichmullerLift
import GQ2.UnitFiltrationTop

/-!
# Torsion-freeness of sufficiently deep dyadic principal units

For a finite dyadic field with absolute ramification index `e`, the principal-unit subgroup
`U^(e+1)` is torsion-free.  The proof avoids a `2`-adic logarithm (which is not currently
available in Mathlib):

* an odd-order root of unity distinct from `1` has distance exactly `1` from `1`, by the
  odd-root separation theorem in `GQ2.TeichmullerLift`;
* an even-order root has a power of exact order `2`, hence equal to `-1`; taking powers cannot
  increase its distance from `1`, so its original distance is at least `‖2‖`.

Thus the open ball `‖x - 1‖ < ‖2‖` contains no nontrivial root of unity.  Since
`‖π‖^(e+1) < ‖π‖^e = ‖2‖`, the claimed principal-unit result follows.

This is a genuine arithmetic input toward the `demushkinQ = 2` calculation.  It does not by
itself show that the pro-2 completion of `U^(e+1)` is torsion-free: that stronger assertion
still needs a logarithm/power-map structure theorem or an equivalent completion theorem.
-/

namespace GQ2.Dyadic

open Finset GQ2.TeichmullerLift

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

private lemma norm_eq_one_of_isOfFinOrder {x : ℚbar2} (hx : IsOfFinOrder x) : ‖x‖ = 1 := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg x) hn).mp
  rw [← norm_pow, pow_orderOf_eq_one, norm_one]

/-- **Root-of-unity isolation at `1`.**  In `ℚ̄₂`, the open ball of radius `‖2‖` around
`1` contains no nontrivial finite-order element. -/
theorem rootOfUnity_eq_one_of_norm_sub_one_lt_norm_two {x : ℚbar2}
    (hx : IsOfFinOrder x) (hsmall : ‖x - 1‖ < ‖(2 : ℚbar2)‖) : x = 1 := by
  by_contra hxne
  have hnpos : 0 < orderOf x := hx.orderOf_pos
  have hxpow : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  have hxnorm : ‖x‖ = 1 := norm_eq_one_of_isOfFinOrder hx
  rcases (orderOf x).even_or_odd with heven | hodd
  · let y : ℚbar2 := x ^ (orderOf x / 2)
    have hyord : orderOf y = 2 := by
      exact orderOf_pow_orderOf_div hnpos.ne' heven.two_dvd
    have hy2 : y ^ 2 = 1 := by
      simpa only [hyord] using pow_orderOf_eq_one y
    have hyne : y ≠ 1 := by
      intro hy
      have : orderOf y = 1 := orderOf_eq_one_iff.mpr hy
      omega
    have hyneg : y = -1 := (sq_eq_one_iff.mp hy2).resolve_left hyne
    have hcontract : ‖1 ^ (orderOf x / 2) - x ^ (orderOf x / 2)‖ ≤ ‖1 - x‖ :=
      norm_pow_sub_pow_le_norm_sub (K := ℚbar2) norm_one.le hxnorm.le _
    have htwo_le : ‖(2 : ℚbar2)‖ ≤ ‖x - 1‖ := by
      calc
        ‖(2 : ℚbar2)‖ = ‖1 - (-1 : ℚbar2)‖ := by
          congr 1
          ring
        _ = ‖1 - y‖ := by rw [hyneg]
        _ = ‖1 ^ (orderOf x / 2) - x ^ (orderOf x / 2)‖ := by simp [y]
        _ ≤ ‖1 - x‖ := hcontract
        _ = ‖x - 1‖ := norm_sub_rev _ _
    exact (not_lt_of_ge htwo_le) hsmall
  · have hdist : ‖1 - x‖ = 1 :=
      norm_one_sub_eq_one_of_pow_eq_one hodd hxpow hxne
    have hlt : ‖x - 1‖ < 1 := hsmall.trans norm_two_lt_one
    rw [norm_sub_rev, hdist] at hlt
    exact (lt_irrefl 1 hlt).elim

variable {K : IntermediateField ℚ_[2] ℚbar2}

/-- An element of `U^(e+1)` has distance strictly less than `‖2‖` from `1`. -/
theorem norm_sub_one_lt_norm_two_of_mem_depthUnits_succ_e
    (FF : DyadicUnitFiltration K)
    (u : ↥(depthUnits K FF.π (FF.e + 1))) :
    ‖(((u.1 : (↥K)ˣ) : ↥K) : ℚbar2) - 1‖ < ‖(2 : ℚbar2)‖ := by
  have hu := ((mem_depthUnits K FF.π (FF.e + 1) u.1).mp u.2).2
  refine hu.trans_lt ?_
  rw [pow_succ, ← FF.he]
  calc
    ‖(2 : ℚbar2)‖ * ‖FF.π‖ < ‖(2 : ℚbar2)‖ * 1 :=
      mul_lt_mul_of_pos_left FF.hπ_lt
        (norm_pos_iff.mpr (show (2 : ℚbar2) ≠ 0 by norm_num))
    _ = ‖(2 : ℚbar2)‖ := mul_one _

/-- **Deep principal units have no nontrivial torsion.** -/
theorem depthUnit_eq_one_of_isOfFinOrder
    (FF : DyadicUnitFiltration K)
    (u : ↥(depthUnits K FF.π (FF.e + 1))) (hu : IsOfFinOrder u) : u = 1 := by
  have huQ : IsOfFinOrder ((((u.1 : (↥K)ˣ) : ↥K) : ℚbar2)) := by
    rw [isOfFinOrder_iff_pow_eq_one] at hu ⊢
    obtain ⟨n, hn, hpow⟩ := hu
    refine ⟨n, hn, ?_⟩
    have hpowUnits : (u.1 : (↥K)ˣ) ^ n = 1 := congrArg Subtype.val hpow
    have hpowK : ((u.1 : (↥K)ˣ) : ↥K) ^ n = 1 := congrArg Units.val hpowUnits
    simpa using congrArg (fun z : ↥K => (z : ℚbar2)) hpowK
  have huOne : (((u.1 : (↥K)ˣ) : ↥K) : ℚbar2) = 1 :=
    rootOfUnity_eq_one_of_norm_sub_one_lt_norm_two huQ
      (norm_sub_one_lt_norm_two_of_mem_depthUnits_succ_e FF u)
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact huOne

/-- **`U^(e+1)` is multiplicatively torsion-free.**  Equivalently, every positive power map on
this sufficiently deep principal-unit group is injective. -/
theorem isMulTorsionFree_depthUnits_succ_e (FF : DyadicUnitFiltration K) :
    IsMulTorsionFree ↥(depthUnits K FF.π (FF.e + 1)) := by
  apply IsMulTorsionFree.of_not_isOfFinOrder
  intro u hune hufin
  exact hune (depthUnit_eq_one_of_isOfFinOrder FF u hufin)

/-- Positive power maps are injective on `U^(e+1)`. -/
theorem depthUnits_succ_e_pow_injective (FF : DyadicUnitFiltration K)
    {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun u : ↥(depthUnits K FF.π (FF.e + 1)) => u ^ n) := by
  letI := isMulTorsionFree_depthUnits_succ_e FF
  exact pow_left_injective hn

/-- The deep principal units lie in the norm-one unit group. -/
theorem depthUnits_succ_e_le_normUnits (FF : DyadicUnitFiltration K) :
    depthUnits K FF.π (FF.e + 1) ≤ normUnits K :=
  fun _ hu => hu.1

/-- The same deep group, viewed inside the norm-one units, is torsion-free. -/
theorem isMulTorsionFree_depthUnitsSubgroupOfNormUnits_succ_e
    (FF : DyadicUnitFiltration K) :
    IsMulTorsionFree
      ↥((depthUnits K FF.π (FF.e + 1)).subgroupOf (normUnits K)) := by
  letI := isMulTorsionFree_depthUnits_succ_e FF
  let e := Subgroup.subgroupOfEquivOfLe (depthUnits_succ_e_le_normUnits FF)
  exact e.injective.isMulTorsionFree e.toMonoidHom

/-- Reduction modulo `U^(e+1)` is injective on finite-order norm-one units.  Thus all actual
torsion in `O_Kˣ` is already detected at this finite depth; the remaining completion problem is
to prove that passing to the pro-2 completion introduces no new torsion in the deep factor. -/
theorem quotientMk_depthUnits_succ_e_injective_on_isOfFinOrder
    (FF : DyadicUnitFiltration K) {u v : ↥(normUnits K)}
    (hu : IsOfFinOrder u) (hv : IsOfFinOrder v)
    (hquot : QuotientGroup.mk'
        ((depthUnits K FF.π (FF.e + 1)).subgroupOf (normUnits K)) u =
      QuotientGroup.mk'
        ((depthUnits K FF.π (FF.e + 1)).subgroupOf (normUnits K)) v) :
    u = v := by
  let N := (depthUnits K FF.π (FF.e + 1)).subgroupOf (normUnits K)
  letI : IsMulTorsionFree ↥N :=
    isMulTorsionFree_depthUnitsSubgroupOfNormUnits_succ_e FF
  have hmem : u⁻¹ * v ∈ N := QuotientGroup.eq.mp hquot
  let z : ↥N := ⟨u⁻¹ * v, hmem⟩
  have hz : IsOfFinOrder z :=
    (N.subtype_injective.isOfFinOrder_iff (x := z)).mp (hu.inv.mul hv)
  have hz1 : z = 1 := by
    by_contra hzne
    exact (not_isOfFinOrder_of_isMulTorsionFree hzne) hz
  have : u⁻¹ * v = 1 := congrArg Subtype.val hz1
  exact inv_mul_eq_one.mp this

end

end GQ2.Dyadic
