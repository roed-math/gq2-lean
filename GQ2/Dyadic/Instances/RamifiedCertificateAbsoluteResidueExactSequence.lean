/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueAlgebraicClosure
import Mathlib.FieldTheory.KrullTopology

/-!
# The canonical absolute residue action and its topological exactness

The residue action of `Gal(AlgebraicClosure ℚ_[2]/ℚ_[2])` was originally constructed only as a
ring automorphism of the absolute norm-residue field.  This module proves that it fixes the base
residue field, bundles it as a homomorphism into the base-linear Galois group, identifies its
kernel with `absoluteInertiaSubgroup`, and proves continuity for the two Krull topologies.

Continuity is proved directly.  A finite intermediate residue field has finitely many elements;
choose integral representatives of all of them, adjoin those representatives to `ℚ_[2]`, and use
the fixing subgroup of that finite extension as an open neighborhood in the absolute Galois
group.  Compactness then shows that the residue-action image is closed.  The topological first
isomorphism theorem is made explicit as
`absoluteInertiaQuotientEquivResidueRange`.

The module also isolates the exact remaining field-theoretic seam: surjectivity is equivalent to
lifting the restriction of every residue automorphism to every finite normal intermediate
residue field.  No existing local-reciprocity declaration currently supplies this finite-level
residue-Frobenius lifting statement.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
local notation "k₀" => IsLocalRing.ResidueField BaseInteger
local notation "k̄₂" => IsLocalRing.ResidueField absoluteNormInteger

local instance : Algebra BaseInteger absoluteNormInteger := absoluteNormIntegerAlgebra
local instance : IsLocalHom (algebraMap BaseInteger absoluteNormInteger) :=
  absoluteNormInteger_algebraMap_isLocalHom
local instance : Algebra k₀ k̄₂ := absoluteResidueFieldAlgebra
local instance : Algebra.IsAlgebraic k₀ k̄₂ := absoluteResidueField_isAlgebraic
local instance : Finite k₀ := baseResidueField_finite
local instance : Fintype k₀ := Fintype.ofFinite k₀
local instance : IsAlgClosed k̄₂ := absoluteResidueField_isAlgClosed

/-- Normality of the algebraically closed absolute residue extension. -/
theorem absoluteResidueField_normal : Normal k₀ k̄₂ :=
  normal_iff.mpr fun x =>
    ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩

local instance : Normal k₀ k̄₂ := absoluteResidueField_normal

/-- Every absolute residue automorphism induced from the absolute Galois group fixes the base
residue field. -/
theorem absoluteResidueAction_commutes_base
    (g : Kummer.GaloisGroup ℚ_[2]) (a : k₀) :
    absoluteResidueAction g (algebraMap k₀ k̄₂ a) = algebraMap k₀ k̄₂ a := by
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  change absoluteResidueAction g
      (IsLocalRing.residue absoluteNormInteger
        (algebraMap BaseInteger absoluteNormInteger b)) =
    IsLocalRing.residue absoluteNormInteger
      (algebraMap BaseInteger absoluteNormInteger b)
  rw [absoluteResidueAction_residue]
  congr 1
  apply Subtype.ext
  change g (algebraMap ℚ_[2] ℚ̄₂ (b : ℚ_[2])) = algebraMap ℚ_[2] ℚ̄₂ (b : ℚ_[2])
  exact g.commutes _

/-- The canonical absolute residue action, regarded as base-linear automorphisms of the absolute
residue field. -/
def absoluteResidueAlgAction :
    Kummer.GaloisGroup ℚ_[2] →* Gal(k̄₂/k₀) where
  toFun g :=
    { absoluteResidueAction g with
      commutes' := absoluteResidueAction_commutes_base g }
  map_one' := by
    apply AlgEquiv.ext
    intro x
    change absoluteResidueAction 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    change absoluteResidueAction (g * h) x =
      absoluteResidueAction g (absoluteResidueAction h x)
    rw [map_mul]
    rfl

@[simp]
theorem absoluteResidueAlgAction_apply
    (g : Kummer.GaloisGroup ℚ_[2]) (x : k̄₂) :
    absoluteResidueAlgAction g x = absoluteResidueAction g x := rfl

/-- The kernel of the base-linear residue action is exactly absolute inertia. -/
theorem absoluteResidueAlgAction_ker :
    absoluteResidueAlgAction.ker = absoluteInertiaSubgroup := by
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    apply RingEquiv.ext
    intro x
    exact DFunLike.congr_fun h x
  · intro h
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun h x

/-- The base-linear absolute residue action is continuous for the two Krull topologies. -/
theorem absoluteResidueAlgAction_continuous : Continuous absoluteResidueAlgAction := by
  apply continuous_of_continuousAt_one absoluteResidueAlgAction
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hEfin, hEs⟩ := hs
  letI : FiniteDimensional k₀ E := hEfin
  letI : Finite E := Module.finite_of_finite k₀
  let lift (e : E) : absoluteNormInteger :=
    Classical.choose (IsLocalRing.residue_surjective (e : k̄₂))
  have lift_spec (e : E) :
      IsLocalRing.residue absoluteNormInteger (lift e) = (e : k̄₂) :=
    Classical.choose_spec (IsLocalRing.residue_surjective (e : k̄₂))
  let L : IntermediateField ℚ_[2] ℚ̄₂ :=
    IntermediateField.adjoin ℚ_[2] (Set.range fun e : E => (lift e : ℚ̄₂))
  letI : FiniteDimensional ℚ_[2] L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  rw [mem_nhds_iff]
  refine ⟨(L.fixingSubgroup : Set (Kummer.GaloisGroup ℚ_[2])), ?_,
    IntermediateField.fixingSubgroup_isOpen L, L.fixingSubgroup.one_mem⟩
  intro g hg
  apply hEs
  change absoluteResidueAlgAction g ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro e he
  let ee : E := ⟨e, he⟩
  change absoluteResidueAlgAction g (ee : k̄₂) = (ee : k̄₂)
  change absoluteResidueAction g (ee : k̄₂) = (ee : k̄₂)
  rw [← lift_spec ee, absoluteResidueAction_residue]
  congr 1
  apply Subtype.ext
  apply (IntermediateField.mem_fixingSubgroup_iff L g).mp hg
  apply IntermediateField.subset_adjoin
  exact Set.mem_range_self ee

/-- The canonical residue action bundled as a continuous homomorphism of Krull-topological
Galois groups. -/
def absoluteResidueAlgActionContinuous :
    Kummer.GaloisGroup ℚ_[2] →ₜ* Gal(k̄₂/k₀) :=
  ⟨absoluteResidueAlgAction, absoluteResidueAlgAction_continuous⟩

/-- The image of the canonical absolute residue action is closed.  Thus density, equivalently
finite-level residue automorphism lifting, is the only remaining ingredient for surjectivity. -/
theorem absoluteResidueAlgAction_range_isClosed :
    IsClosed (Set.range absoluteResidueAlgAction) :=
  (isCompact_range absoluteResidueAlgAction_continuous).isClosed

/-- The topological first isomorphism theorem for the canonical absolute residue action.  The
quotient by its exact kernel is canonically the closed image, with the quotient and subspace Krull
topologies. -/
noncomputable def absoluteResidueQuotientEquivRange :
    (Kummer.GaloisGroup ℚ_[2] ⧸ absoluteResidueAlgAction.ker) ≃ₜ*
      absoluteResidueAlgAction.range := by
  let e := QuotientGroup.quotientKerEquivRange absoluteResidueAlgAction
  have he_cont : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk absoluteResidueAlgAction.ker).continuous_iff.mpr
    change Continuous absoluteResidueAlgAction.rangeRestrict
    exact absoluteResidueAlgAction_continuous.subtype_mk _
  have he_home : IsHomeomorph e :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨he_cont, e.bijective⟩
  have he_inv_cont : Continuous e.symm :=
    (Equiv.isHomeomorph_iff e.toEquiv).mp he_home |>.2
  exact
    { e with
      continuous_toFun := he_cont
      continuous_invFun := he_inv_cont }

/-- Topological exactness stated with the intrinsic absolute inertia subgroup. -/
noncomputable def absoluteInertiaQuotientEquivResidueRange :
    (Kummer.GaloisGroup ℚ_[2] ⧸ absoluteInertiaSubgroup) ≃ₜ*
      absoluteResidueAlgAction.range := by
  let e : (Kummer.GaloisGroup ℚ_[2] ⧸ absoluteInertiaSubgroup) ≃*
      absoluteResidueAlgAction.range :=
    (QuotientGroup.quotientMulEquivOfEq absoluteResidueAlgAction_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange absoluteResidueAlgAction)
  have he_cont : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk absoluteInertiaSubgroup).continuous_iff.mpr
    change Continuous absoluteResidueAlgAction.rangeRestrict
    exact absoluteResidueAlgAction_continuous.subtype_mk _
  have he_home : IsHomeomorph e :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨he_cont, e.bijective⟩
  have he_inv_cont : Continuous e.symm :=
    (Equiv.isHomeomorph_iff e.toEquiv).mp he_home |>.2
  exact
    { e with
      continuous_toFun := he_cont
      continuous_invFun := he_inv_cont }

@[simp]
theorem absoluteInertiaQuotientEquivResidueRange_mk
    (g : Kummer.GaloisGroup ℚ_[2]) :
    absoluteInertiaQuotientEquivResidueRange (QuotientGroup.mk g) =
      absoluteResidueAlgAction.rangeRestrict g := rfl

/-- Finite-level residue automorphism lifting implies surjectivity of the canonical absolute
residue action.  The proof uses the normal finite-intermediate-field basis of the Krull topology,
then upgrades density to surjectivity using compactness of the source and Hausdorffness of the
target. -/
theorem absoluteResidueAlgAction_surjective_of_finite_lifts
    (h_lift : ∀ (E : IntermediateField k₀ k̄₂),
      FiniteDimensional k₀ E → Normal k₀ E → ∀ σ : Gal(k̄₂/k₀),
        ∃ g : Kummer.GaloisGroup ℚ_[2], ∀ x : E,
          absoluteResidueAlgAction g (x : k̄₂) = σ (x : k̄₂)) :
    Function.Surjective absoluteResidueAlgAction := by
  have hdense : DenseRange absoluteResidueAlgAction := by
    intro σ
    rw [mem_closure_iff_nhds_one]
    intro U hU
    rw [krullTopology_mem_nhds_one_iff_of_normal] at hU
    obtain ⟨E, hEfin, hEnormal, hEU⟩ := hU
    letI : FiniteDimensional k₀ E := hEfin
    letI : Normal k₀ E := hEnormal
    obtain ⟨g, hg⟩ := h_lift E hEfin hEnormal σ
    refine ⟨absoluteResidueAlgAction g, ⟨g, rfl⟩, hEU ?_⟩
    apply (IntermediateField.mem_fixingSubgroup_iff E _).mpr
    intro x hx
    have hx' : σ.symm x ∈ E := by
      rw [← (IntermediateField.normal_iff_forall_map_eq'.mp hEnormal σ.symm)]
      exact (E.map_mem_map σ.symm.toAlgHom).mpr hx
    have hagree := hg ⟨σ.symm x, hx'⟩
    change absoluteResidueAlgAction g (σ.symm x) = x
    simpa using hagree
  rw [← Set.range_eq_univ]
  apply Set.eq_univ_of_forall
  intro σ
  rw [← absoluteResidueAlgAction_range_isClosed.closure_eq]
  exact hdense σ

/-- Surjectivity of the absolute residue action is equivalent to lifting the restriction of every
residue automorphism to every finite normal intermediate residue field. -/
theorem absoluteResidueAlgAction_surjective_iff_finite_lifts :
    Function.Surjective absoluteResidueAlgAction ↔
      ∀ (E : IntermediateField k₀ k̄₂),
        FiniteDimensional k₀ E → Normal k₀ E → ∀ σ : Gal(k̄₂/k₀),
          ∃ g : Kummer.GaloisGroup ℚ_[2], ∀ x : E,
            absoluteResidueAlgAction g (x : k̄₂) = σ (x : k̄₂) := by
  constructor
  · intro hsurj E _ _ σ
    obtain ⟨g, rfl⟩ := hsurj σ
    exact ⟨g, fun _ => rfl⟩
  · exact absoluteResidueAlgAction_surjective_of_finite_lifts

#print axioms absoluteResidueField_normal
#print axioms absoluteResidueAction_commutes_base
#print axioms absoluteResidueAlgAction
#print axioms absoluteResidueAlgAction_ker
#print axioms absoluteResidueAlgAction_continuous
#print axioms absoluteResidueAlgActionContinuous
#print axioms absoluteResidueAlgAction_range_isClosed
#print axioms absoluteResidueQuotientEquivRange
#print axioms absoluteInertiaQuotientEquivResidueRange
#print axioms absoluteInertiaQuotientEquivResidueRange_mk
#print axioms absoluteResidueAlgAction_surjective_of_finite_lifts
#print axioms absoluteResidueAlgAction_surjective_iff_finite_lifts

end

end GQ2.Dyadic
