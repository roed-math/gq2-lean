/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.AnchoredTameInertiaPrescribedUnramified

/-!
# Anchored involution norm matching over arbitrary finite bases

The previous absolute-index argument required odd absolute degree of the base field. This
module replaces it with the relative tower argument: `e(L/K)` is odd, while `e(L/k)` divides
both `e(L/K)` and two. Thus `e(L/k)=1`, regardless of `e(K/Q₂)`.

The endpoint takes the existing prescribed tame-inertia unramified packet and supplies the
full compatible anchored involution equal-norm-value packet. No odd-degree, presentation-family,
handle-count, or local reciprocity hypothesis is added.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Relative ramification is multiplicative in an embedded finite-field tower. -/
theorem relE_mul_tower {K F L : IntermediateField ℚ_[2] ℚ̄₂}
    (FK : DyadicUnitFiltration K) (FF : DyadicUnitFiltration F)
    (FL : DyadicUnitFiltration L) (hKF : K ≤ F) (hFL : F ≤ L) :
    GaloisCosetNorm.relE FK FL (hKF.trans hFL) =
      GaloisCosetNorm.relE FF FL hFL * GaloisCosetNorm.relE FK FF hKF := by
  apply mul_right_cancel₀ (show (FK.e : ℤ) ≠ 0 by
    exact_mod_cast (Nat.ne_zero_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one FK.he_pos)))
  rw [← GaloisCosetNorm.e_eq_relE_mul FK FL,
    mul_assoc, ← GaloisCosetNorm.e_eq_relE_mul FK FF,
    ← GaloisCosetNorm.e_eq_relE_mul FF FL]

/-- An involution tower is unramified when the splitting field has odd ramification relative
to any common base. Unlike the absolute-index adapter, this allows arbitrarily ramified bases. -/
theorem hunram_of_odd_relative_eF0
    {K k L F₀ : IntermediateField ℚ_[2] ℚ̄₂}
    (FK : DyadicUnitFiltration K) (Fk : DyadicUnitFiltration k)
    (FL : DyadicUnitFiltration L) (F₀F : DyadicUnitFiltration F₀)
    (hKk : K ≤ k) (hkL : k ≤ L) (hKF₀ : K ≤ F₀) (hF₀L : F₀ ≤ L)
    (hm2 : GaloisCosetNorm.relE Fk FL hkL ∣ 2)
    {r : ℕ} (hrodd : Odd r)
    (hdvd : GaloisCosetNorm.relE F₀F FL hF₀L ∣ (r : ℤ))
    (hodd : Odd (GaloisCosetNorm.relE FK F₀F hKF₀)) :
    ∀ x : ℚ̄₂, x ≠ 0 → x ∈ L →
      ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖ := by
  have hrel₀ : Odd (GaloisCosetNorm.relE F₀F FL hF₀L) := by
    obtain ⟨c, hc⟩ := hdvd
    exact (Int.odd_mul.mp (hc ▸ (by exact_mod_cast hrodd : Odd (r : ℤ)))).1
  have hrelL : Odd (GaloisCosetNorm.relE FK FL (hKk.trans hkL)) := by
    rw [relE_mul_tower FK F₀F FL hKF₀ hF₀L]
    exact hrel₀.mul hodd
  rw [relE_mul_tower FK Fk FL hKk hkL] at hrelL
  have hm_odd := (Int.odd_mul.mp hrelL).1
  have hm1 : GaloisCosetNorm.relE Fk FL hkL = 1 := by
    have hle : GaloisCosetNorm.relE Fk FL hkL ≤ 2 := Int.le_of_dvd (by norm_num) hm2
    have hge := GaloisCosetNorm.relE_pos Fk FL hkL
    have := Int.odd_iff.mp hm_odd
    omega
  have hπ := GaloisCosetNorm.relE_spec Fk FL hkL
  rw [hm1, zpow_one] at hπ
  exact UnramifiedNorm.hunram_of_uniformizer_norm_eq Fk FL hπ.symm

variable {C : Type} [Group C] [TopologicalSpace C]

/-- Every anchored involution field over `G_K` contains `K`. -/
theorem baseField_le_anchoredInvolutionField
    (K : IntermediateField ℚ_[2] ℚ̄₂)
    (rho : ContinuousMonoidHom ↑(GalKsub K) C) (g : ↑(GalKsub K)) :
    K ≤ anchoredInvolutionField (GalKsub K) rho g := by
  intro x hx
  rw [anchoredInvolutionField, IntermediateField.mem_fixedField_iff]
  intro y hy
  obtain ⟨a, ha, rfl⟩ := hy
  have hx' : x ∈ IntermediateField.fixedField K.fixingSubgroup :=
    (InfiniteGalois.fixedField_fixingSubgroup K).symm ▸ hx
  exact hx' a

variable [DiscreteTopology C] [Finite C]

/-- Odd relative ramification of the anchored tame-inertia field suffices for all canonical
involution towers over an arbitrary finite base field. -/
theorem anchoredInvolutionEqualNormValueGroups_of_relativeOddTameInertia_general
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (FK : DyadicUnitFiltration K) (rho : ContinuousMonoidHom ↑(GalKsub K) C)
    (t : C) (ht : t ∈ rho.toMonoidHom.range) (htodd : Odd (orderOf t))
    (Hodd : AnchoredTameInertiaRelativeOddData K FK rho t) :
    AnchoredInvolutionEqualNormValueGroups (GalKsub K) rho := by
  classical
  let U := GalKsub K
  have hU : IsOpen (U : Set AbsGalQ2) := isOpen_fixingSubgroup K
  obtain ⟨F₀F, hF₀odd⟩ := Hodd
  letI : FiniteDimensional ℚ_[2] (anchoredSplitField U rho) :=
    anchoredSplitField_finiteDimensional U hU rho
  letI : FiniteDimensional ℚ_[2] (anchoredTameInertiaField U rho t) :=
    anchoredTameInertiaField_finiteDimensional U hU rho t
  let FL : DyadicUnitFiltration (anchoredSplitField U rho) :=
    dyadicUnitFiltration (anchoredSplitField U rho)
  have hF₀L := anchoredTameInertiaField_le_anchoredSplitField U rho t
  have hidx₀ :=
    anchoredSplitField_subgroupOf_anchoredTameInertiaField_index U hU rho t ht
  haveI hfin₀ : Finite (↑((anchoredTameInertiaField U rho t).fixingSubgroup) ⧸
      ((anchoredSplitField U rho).fixingSubgroup).subgroupOf
        (anchoredTameInertiaField U rho t).fixingSubgroup) := by
    refine (Nat.card_ne_zero.mp ?_).2
    show ((anchoredSplitField U rho).fixingSubgroup.subgroupOf
      (anchoredTameInertiaField U rho t).fixingSubgroup).index ≠ 0
    rw [hidx₀]
    exact (orderOf_pos t).ne'
  have hdiv₀ : GaloisCosetNorm.relE F₀F FL hF₀L ∣ (orderOf t : ℤ) := by
    have hdiv := UnramifiedBridge.relE_dvd_of_index F₀F FL hF₀L
    rwa [show Nat.card (↑((anchoredTameInertiaField U rho t).fixingSubgroup) ⧸
        ((anchoredSplitField U rho).fixingSubgroup).subgroupOf
          (anchoredTameInertiaField U rho t).fixingSubgroup) = orderOf t from hidx₀] at hdiv
  intro g hgN hg2
  letI : FiniteDimensional ℚ_[2] (anchoredInvolutionField U rho g) :=
    anchoredInvolutionField_finiteDimensional U hU rho g
  let Fk : DyadicUnitFiltration (anchoredInvolutionField U rho g) :=
    dyadicUnitFiltration (anchoredInvolutionField U rho g)
  have hkL := anchoredInvolutionField_le_anchoredSplitField U rho g
  have hidx := anchoredSplitField_subgroupOf_anchoredInvolutionField_index U hU rho g hgN hg2
  have hm2 : GaloisCosetNorm.relE Fk FL hkL ∣ 2 :=
    UnramifiedBridge.relE_dvd_two Fk FL hkL hidx
  have hunram := hunram_of_odd_relative_eF0 FK Fk FL F₀F
    (baseField_le_anchoredInvolutionField K rho g) hkL
    (baseField_le_anchoredTameInertiaField K rho t) hF₀L hm2 htodd hdiv₀ hF₀odd
  obtain ⟨d, δ, hδ2, hδL, hδk, hadj⟩ :=
    anchoredInvolutionField_exists_sqrt_generator U hU rho g hgN hg2
  refine ⟨d, δ, hδ2, hδL, hδk, hadj, ?_⟩
  intro y hy0 hyrepr
  obtain ⟨a, b, hy⟩ := hyrepr
  have hyL : y ∈ anchoredSplitField U rho := by
    rw [hy]
    exact (anchoredSplitField U rho).add_mem (hkL a.2)
      ((anchoredSplitField U rho).mul_mem (hkL b.2) hδL)
  obtain ⟨z, hz0, hzk, hnorm⟩ := hunram y hy0 hyL
  exact ⟨⟨z, hzk⟩, fun hz ↦ hz0 (congrArg Subtype.val hz), hnorm⟩

/-- The compatible-use relative oddness adapter with no base-degree restriction. -/
theorem anchoredInvolutionEqualNormValueGroupsAt_of_relativeOddTameInertia_general
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (htame : Function.Surjective tame)
    (Hodd : AnchoredTameInertiaRelativeOddDataAt P K FK tame) :
    AnchoredInvolutionEqualNormValueGroupsAt P (GalKsub K) tame := by
  intro D _ _ _ _ V _ _ c rho hfac hram
  have ht : c (tqTau P.qK) ∈ rho.toMonoidHom.range := by
    obtain ⟨g, hg⟩ := htame (tqTau P.qK)
    refine ⟨g, ?_⟩
    change rho g = c (tqTau P.qK)
    rw [hfac, hg]
  have hq0 : P.qK ≠ 0 := P.qK_pos.ne'
  have hqe : Even P.qK := by
    rw [P.qK_eq]
    obtain ⟨f, hf⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt P.f_pos)
    rw [hf, pow_succ]
    exact even_two.mul_left _
  have htodd : Odd (orderOf (c (tqTau P.qK))) :=
    tqTau_odd_order_map hq0 hqe c.toMonoidHom
  exact anchoredInvolutionEqualNormValueGroups_of_relativeOddTameInertia_general K FK rho
    (c (tqTau P.qK)) ht htodd (Hodd V c rho hfac hram)

/-- Prescribed tame-inertia fields unramified over the base supply the full involution norm
packet in every finite degree, including all even presentation families. -/
theorem anchoredInvolutionEqualNormValueGroupsAt_of_prescribedTameUnramified_general
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (htame : Function.Surjective tame)
    (Hunram : AnchoredTameInertiaRelativeUnramifiedDataAt P K FK tame) :
    AnchoredInvolutionEqualNormValueGroupsAt P (GalKsub K) tame :=
  anchoredInvolutionEqualNormValueGroupsAt_of_relativeOddTameInertia_general P K FK tame htame
    (anchoredTameInertiaRelativeOddDataAt_of_relativeUnramified P K FK tame Hunram)

#print axioms relE_mul_tower
#print axioms hunram_of_odd_relative_eF0
#print axioms baseField_le_anchoredInvolutionField
#print axioms anchoredInvolutionEqualNormValueGroups_of_relativeOddTameInertia_general
#print axioms anchoredInvolutionEqualNormValueGroupsAt_of_relativeOddTameInertia_general
#print axioms anchoredInvolutionEqualNormValueGroupsAt_of_prescribedTameUnramified_general
end
end GQ2.Dyadic

