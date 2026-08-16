/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.AnchoredInvolutionFieldNorm

/-!
# The odd-inertia reduction for anchored involution norm data

The canonical involution tower of `AnchoredInvolutionFieldNorm` has equal norm value groups once
the canonical tame-inertia field has odd absolute ramification index.  This module proves all
other steps: openness and Krull recovery for that field, its inclusion in the anchored splitting
field, the tame-inertia quotient count, the odd relative-index leg, and the final quadratic norm
matching.

The remaining predicate `AnchoredTameInertiaOddDataAt` is deliberately quantified only over the
compatible ramified uses of the determinant consumer and retains the caller's action.  It asks
for a filtration of one explicit canonical field whose ramification index is odd.

This is also the exact present API boundary.  The base `AbsGalQ2` theorem
`UnramifiedBridge.odd_e_inertiaField` proves the analogous oddness using
`UnitNormIndex.card_unitImage_eq_e`, local reciprocity over `ℚ₂`, and tame orientation.  No
general-`K` relative unit-image cardinality theorem is exposed by `MarkedRecip` or
`OrientedTameQuotientK`; `MarkedRecip` also deliberately omits finite-layer norm reciprocity.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The anchored image of the preimage of the cyclic tame-inertia subgroup. -/
def anchoredTameInertiaSubgroup (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) (t : C) : Subgroup GalQ2 :=
  ((Subgroup.zpowers t).comap rho.toMonoidHom).map (subtypeAnc U).toMonoidHom

/-- The canonical anchored tame-inertia field associated to `rho` and `t`. -/
def anchoredTameInertiaField (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) (t : C) : IntermediateField ℚ_[2] ℚ̄₂ :=
  IntermediateField.fixedField (anchoredTameInertiaSubgroup U rho t)

omit [Finite C] in
private theorem anchoredTameInertiaSubgroup_isOpen (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) (t : C) :
    IsOpen ((anchoredTameInertiaSubgroup U rho t : Subgroup GalQ2) : Set GalQ2) := by
  have hpre : IsOpen ((((Subgroup.zpowers t).comap rho.toMonoidHom : Subgroup ↑U) : Set ↑U)) :=
    (isOpen_discrete ((Subgroup.zpowers t : Subgroup C) : Set C)).preimage rho.continuous_toFun
  rw [anchoredTameInertiaSubgroup, Subgroup.coe_map]
  change IsOpen ((fun x : ↑U ↦ (x : AbsGalQ2)) ''
    ((((Subgroup.zpowers t).comap rho.toMonoidHom : Subgroup ↑U) : Set ↑U)))
  exact hU.isOpenMap_subtype_val _ hpre

omit [Finite C] in
/-- Krull correspondence recovers the anchored tame-inertia subgroup. -/
theorem fixingSubgroup_anchoredTameInertiaField (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) (t : C) :
    (anchoredTameInertiaField U rho t).fixingSubgroup =
      anchoredTameInertiaSubgroup U rho t := by
  unfold anchoredTameInertiaField
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨_, Subgroup.isClosed_of_isOpen _ (anchoredTameInertiaSubgroup_isOpen U hU rho t)⟩

omit [Finite C] in
/-- The canonical anchored tame-inertia field is finite over `ℚ₂`. -/
theorem anchoredTameInertiaField_finiteDimensional (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) (rho : ContinuousMonoidHom ↑U C) (t : C) :
    FiniteDimensional ℚ_[2] (anchoredTameInertiaField U rho t) := by
  rw [← InfiniteGalois.isOpen_iff_finite (anchoredTameInertiaField U rho t),
    fixingSubgroup_anchoredTameInertiaField U hU rho t]
  exact anchoredTameInertiaSubgroup_isOpen U hU rho t

omit [DiscreteTopology C] [Finite C] in
/-- The tame-inertia field lies below the anchored splitting field. -/
theorem anchoredTameInertiaField_le_anchoredSplitField (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) (t : C) :
    anchoredTameInertiaField U rho t ≤ anchoredSplitField U rho := by
  intro x hx
  rw [anchoredTameInertiaField, IntermediateField.mem_fixedField_iff] at hx
  rw [anchoredSplitField, IntermediateField.mem_fixedField_iff]
  intro y hy
  rw [ancSubgroup_kerAnc] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  apply hx
  refine ⟨n, ?_, rfl⟩
  change rho.toMonoidHom n ∈ Subgroup.zpowers t
  rw [MonoidHom.mem_ker.mp hn]
  exact one_mem _

omit [DiscreteTopology C] [Finite C] in
private theorem preimage_subgroupOf_index (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) (t : C)
    (ht : t ∈ rho.toMonoidHom.range) :
    ((rho.toMonoidHom.ker : Subgroup ↑U).subgroupOf
      ((Subgroup.zpowers t).comap rho.toMonoidHom)).index = orderOf t := by
  let T₀ : Subgroup ↑U := (Subgroup.zpowers t).comap rho.toMonoidHom
  let rho' : ↑T₀ →* ↑(Subgroup.zpowers t) :=
    { toFun := fun x ↦ ⟨rho x.1, x.2⟩
      map_one' := Subtype.ext (map_one rho)
      map_mul' := fun a b ↦ Subtype.ext (map_mul rho a.1 b.1) }
  have hsurj : Function.Surjective rho' := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := (Subgroup.mem_zpowers_iff).mp hy
    obtain ⟨g, hg⟩ := ht
    refine ⟨⟨g ^ m, ?_⟩, Subtype.ext ?_⟩
    · change rho.toMonoidHom (g ^ m) ∈ Subgroup.zpowers t
      rw [map_zpow, hg]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) m
    · exact map_zpow rho g m |>.trans (congrArg (fun z ↦ z ^ m) hg)
  have hker : rho'.ker =
      (rho.toMonoidHom.ker : Subgroup ↑U).subgroupOf T₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
  calc
    ((rho.toMonoidHom.ker : Subgroup ↑U).subgroupOf
        ((Subgroup.zpowers t).comap rho.toMonoidHom)).index
        = rho'.ker.index := by rw [hker]
    _ = Nat.card (↑T₀ ⧸ rho'.ker) := rfl
    _ = Nat.card ↑(Subgroup.zpowers t) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective rho' hsurj).toEquiv
    _ = orderOf t := Nat.card_zpowers t

omit [Finite C] in
/-- The anchored splitting subgroup has tame-inertia index `orderOf t`. -/
theorem anchoredSplitField_subgroupOf_anchoredTameInertiaField_index
    (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2))
    (rho : ContinuousMonoidHom ↑U C) (t : C) (ht : t ∈ rho.toMonoidHom.range) :
    (((anchoredSplitField U rho).fixingSubgroup).subgroupOf
      (anchoredTameInertiaField U rho t).fixingSubgroup).index = orderOf t := by
  rw [fixingSubgroup_anchoredSplitField U hU rho,
    fixingSubgroup_anchoredTameInertiaField U hU rho t, ancSubgroup_kerAnc]
  change ((rho.toMonoidHom.ker : Subgroup ↑U).map (subtypeAnc U).toMonoidHom).relIndex
    (((Subgroup.zpowers t).comap rho.toMonoidHom).map (subtypeAnc U).toMonoidHom) = orderOf t
  rw [Subgroup.relIndex_map_map_of_injective _ _ (subtypeAnc_injective U)]
  exact preimage_subgroupOf_index U rho t ht

/-- Odd absolute ramification of the canonical tame-inertia field is the exact remaining input
to the existing `UnramifiedBridge.hunram_of_odd_eF0` assembly. -/
def AnchoredTameInertiaOddData (U : Subgroup AbsGalQ2)
    (rho : ContinuousMonoidHom ↑U C) (t : C) : Prop :=
  ∃ F₀F : DyadicUnitFiltration (anchoredTameInertiaField U rho t), Odd F₀F.e

/-- Odd anchored tame inertia supplies equal norm value groups in every canonical involution
tower. -/
theorem anchoredInvolutionEqualNormValueGroups_of_oddTameInertia
    (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2))
    (rho : ContinuousMonoidHom ↑U C) (t : C) (ht : t ∈ rho.toMonoidHom.range)
    (htodd : Odd (orderOf t)) (Hodd : AnchoredTameInertiaOddData U rho t) :
    AnchoredInvolutionEqualNormValueGroups U rho := by
  classical
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
  have hunram := UnramifiedBridge.hunram_of_odd_eF0
    Fk FL F₀F hkL hF₀L hm2 htodd hdiv₀ hF₀odd
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

/-- The odd-inertia premise with exactly the compatible ramified-use quantification and custom
action of `AnchoredInvolutionEqualNormValueGroupsAt`. -/
def AnchoredTameInertiaOddDataAt (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (V : Type) [AddCommGroup V] [DistribMulAction D V]
    (c : ContinuousMonoidHom (Tq P.qK) D) (rho : ContinuousMonoidHom ↑U D),
    (∀ g : ↑U, rho g = c (tame g)) →
      (∃ v : V, c (tqTau P.qK) • v ≠ v) →
        AnchoredTameInertiaOddData U rho (c (tqTau P.qK))

/-- Odd ramification of the canonical tame-inertia field produces the full compatible-use
equal-norm-value-groups packet. -/
theorem anchoredInvolutionEqualNormValueGroupsAt_of_oddTameInertia
    (P : FieldParameters) (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2))
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) (htame : Function.Surjective tame)
    (Hodd : AnchoredTameInertiaOddDataAt P U tame) :
    AnchoredInvolutionEqualNormValueGroupsAt P U tame := by
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
  exact anchoredInvolutionEqualNormValueGroups_of_oddTameInertia U hU rho
    (c (tqTau P.qK)) ht htodd (Hodd V c rho hfac hram)

#print axioms anchoredTameInertiaSubgroup
#print axioms anchoredTameInertiaField
#print axioms fixingSubgroup_anchoredTameInertiaField
#print axioms anchoredTameInertiaField_finiteDimensional
#print axioms anchoredTameInertiaField_le_anchoredSplitField
#print axioms anchoredSplitField_subgroupOf_anchoredTameInertiaField_index
#print axioms AnchoredTameInertiaOddData
#print axioms anchoredInvolutionEqualNormValueGroups_of_oddTameInertia
#print axioms AnchoredTameInertiaOddDataAt
#print axioms anchoredInvolutionEqualNormValueGroupsAt_of_oddTameInertia

end
end GQ2.Dyadic
