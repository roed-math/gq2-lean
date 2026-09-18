/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateOddCyclotomicRamification
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueBaseChange
import GQ2.Dyadic.Instances.RamifiedCertificateRelativeFrobeniusUnitSplit

/-!
# Reciprocity units and canonical residue inertia

Finite-layer norm reciprocity already controls the image of the units: its cardinality is the
ramification index. Thus an actual unramified abelian layer is fixed by reciprocity units,
independently of any choice of full Frobenius coordinate.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 SpectralLocalField
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Base reciprocity units are trivial on any actual unramified finite abelian layer. -/
theorem restrictAb_recip_unit_eq_one_of_ramification_one
    (R : LocalReciprocity) (L : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ s t : L ≃ₐ[ℚ_[2]] L, s * t = t * s)
    (FF : DyadicUnitFiltration L) (he : FF.e = 1) (u : ℤ_[2]ˣ) :
    restrictAb L hab (R.recip (unitEmbed u)) = 1 := by
  let phi := ((restrictAb L hab).comp R.recip).comp unitEmbed
  have hc : Nat.card phi.range = 1 :=
    (UnitNormIndex.card_unitImage_eq_e R L hab FF).trans he
  haveI : Subsingleton phi.range := (Nat.card_eq_one_iff_unique.mp hc).1
  have h : (⟨phi u, ⟨u, rfl⟩⟩ : phi.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

/-- A lift of reciprocity of a base unit fixes every element of an unramified abelian layer. -/
theorem recip_unit_lift_fixes_of_ramification_one
    (R : LocalReciprocity) (L : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ s t : L ≃ₐ[ℚ_[2]] L, s * t = t * s)
    (FF : DyadicUnitFiltration L) (he : FF.e = 1)
    (u : ℤ_[2]ˣ) (g : AbsGalQ2) (hg : toAb g = R.recip (unitEmbed u))
    (x : ℚ̄₂) (hx : x ∈ L) : (show Kummer.GaloisGroup ℚ_[2] from g) x = x := by
  have hr : restrictHom L g = 1 := by
    rw [← restrictAb_toAb L hab g, hg]
    exact restrictAb_recip_unit_eq_one_of_ramification_one R L hab FF he u
  exact (AlgEquiv.restrictNormal_eq_one_iff L
    (show Kummer.GaloisGroup ℚ_[2] from g)).mp hr x hx

/-- Full finite-layer norm reciprocity forces every base reciprocity unit to fix odd roots.
No signed Frobenius normalization is used. -/
theorem fixesOddRootsOfUnity_recip_unit
    (R : LocalReciprocity) (u : ℤ_[2]ˣ) (g : AbsGalQ2)
    (hg : toAb g = R.recip (unitEmbed u)) : FixesOddRootsOfUnity g := by
  intro m ζ hm hζ
  have hd : Odd (orderOf ζ) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hζ)
  letI : NeZero (orderOf ζ) := ⟨hd.pos.ne'⟩
  let L : IntermediateField ℚ_[2] ℚ̄₂ := IntermediateField.adjoin ℚ_[2] {ζ}
  letI : IsCyclotomicExtension {orderOf ζ} ℚ_[2] L :=
    (IsPrimitiveRoot.orderOf ζ).intermediateField_adjoin_isCyclotomicExtension (K := ℚ_[2])
  letI : FiniteDimensional ℚ_[2] L :=
    IsCyclotomicExtension.finiteDimensional {orderOf ζ} ℚ_[2] L
  letI : IsGalois ℚ_[2] L := IsCyclotomicExtension.isGalois {orderOf ζ} ℚ_[2] L
  letI : IsMulCommutative (L ≃ₐ[ℚ_[2]] L) :=
    IsCyclotomicExtension.isMulCommutative {orderOf ζ} ℚ_[2] L
  let x : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ_[2] ζ⟩
  have hx : x ^ orderOf ζ = 1 := Subtype.ext (pow_orderOf_eq_one ζ)
  have hprim : IsPrimitiveRoot x (orderOf ζ) := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact IsPrimitiveRoot.orderOf ζ
  have hgen : Algebra.adjoin ℚ_[2] ({x} : Set L) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hprim
  let FF := dyadicUnitFiltration L
  have he : FF.e = 1 := filtration_e_eq_one_of_odd_root L FF
    (orderOf ζ) hd x hx hgen
  exact recip_unit_lift_fixes_of_ramification_one R L
    (fun s t ↦ IsMulCommutative.is_comm.comm s t)
    FF he u g hg ζ x.property

/-- Canonical absolute inertia contains every lift of base reciprocity of a unit. -/
theorem recip_unit_lift_mem_absoluteInertia
    (R : LocalReciprocity) (u : ℤ_[2]ˣ) (g : AbsGalQ2)
    (hg : toAb g = R.recip (unitEmbed u)) : g ∈ absoluteInertiaSubgroup := by
  change (show Kummer.GaloisGroup ℚ_[2] from g) ∈ absoluteInertiaSubgroup
  rw [mem_absoluteInertiaSubgroup_iff_isResidueTrivial_bot]
  exact (fixesOddRootsOfUnity_iff_isResidueTrivial_bot g).mp
    (fixesOddRootsOfUnity_recip_unit R u g hg)

/-- The unit-to-actual-inertia theorem over every finite dyadic field follows from base norm
reciprocity and the marked norm-compatibility clause. -/
theorem absoluteResidueUnitInertia_of_norm_reciprocity
    {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) :
    AbsoluteResidueUnitInertia B := by
  intro u g hu hg
  have hv : v2 (normUnitsK K u) = 0 := by
    rw [v2_normUnitsK_eq_f_mul_dyadicValuation FF u,
      dyadicValuation_eq_zero_of_norm_eq_one u hu, mul_zero]
  obtain ⟨u₀, hu₀⟩ := UnitNormIndex.mem_unitEmbed_range_of_v2_eq_zero hv
  apply recip_unit_lift_mem_absoluteInertia R u₀ (subtypeAnc (GalKsub K) g)
  calc
    toAb (subtypeAnc (GalKsub K) g) = inclAbK K (toAbK K g) :=
      (inclAbK_toAbK K g).symm
    _ = inclAbK K (B.recip u) := congrArg (inclAbK K) hg
    _ = R.recip (normUnitsK K u) := B.norm_compat u
    _ = R.recip (unitEmbed u₀) := congrArg R.recip hu₀.symm

/-- The canonical full residue coordinate kills all marked reciprocity units, without a
Frobenius value premise. -/
theorem absoluteResidueUnitReciprocity_of_norm_reciprocity
    {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) :
    AbsoluteResidueUnitReciprocity B :=
  absoluteResidueUnitInertia_iff_reciprocity.mp
    (absoluteResidueUnitInertia_of_norm_reciprocity B FF)

#print axioms restrictAb_recip_unit_eq_one_of_ramification_one
#print axioms recip_unit_lift_fixes_of_ramification_one
#print axioms fixesOddRootsOfUnity_recip_unit
#print axioms recip_unit_lift_mem_absoluteInertia
#print axioms absoluteResidueUnitInertia_of_norm_reciprocity
#print axioms absoluteResidueUnitReciprocity_of_norm_reciprocity

end
end GQ2.Dyadic
