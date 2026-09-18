/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueZhat
import GQ2.UnitNormIndex

/-!
# Finite residue actions for odd cyclotomic ramification

This module constructs the actual finite Galois action on the residue field of the norm
valuation ring. It is base-linear and agrees with reduction of the field action. The subsequent
odd-cyclotomic ramification argument can therefore use odd-root separation to prove faithfulness.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 SpectralLocalField
open scoped NNReal Pointwise
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
local notation "k₀" => IsLocalRing.ResidueField BaseInteger

section FiniteResidue
variable (L : IntermediateField ℚ_[2] ℚ̄₂)
  [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]

omit [FiniteDimensional ℚ_[2] L] in
/-- A dyadic Galois automorphism preserves the inherited absolute norm. -/
theorem finiteGalois_norm_eq (g : L ≃ₐ[ℚ_[2]] L) (x : L) : ‖g x‖ = ‖x‖ := by
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := ℚ_[2]) (K₁ := L) (E := ℚ̄₂) g
  have hx : s (x : ℚ̄₂) = (g x : ℚ̄₂) := by
    rw [← AlgEquiv.restrictNormalHom_apply L s x, hs]
  change ‖(g x : ℚ̄₂)‖ = ‖(x : ℚ̄₂)‖
  rw [← hx]
  exact norm_galois s (x : ℚ̄₂)

/-- The full finite Galois group preserves the norm valuation ring. -/
theorem finiteGalois_mem_normInteger_decomposition (g : L ≃ₐ[ℚ_[2]] L) :
    g ∈ (NormedField.valuation (K := L)).valuationSubring.decompositionSubgroup ℚ_[2] := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  change ‖g⁻¹ x‖₊ ≤ 1 ↔ ‖x‖₊ ≤ 1
  rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simp only [NNReal.coe_one, coe_nnnorm, finiteGalois_norm_eq]

def finiteGaloisNormDecomposition : (L ≃ₐ[ℚ_[2]] L) →*
    (NormedField.valuation (K := L)).valuationSubring.decompositionSubgroup ℚ_[2] where
  toFun g := ⟨g, finiteGalois_mem_normInteger_decomposition L g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

abbrev finiteNormInteger := (NormedField.valuation (K := L)).valuationSubring

def finiteGaloisResidueAction : (L ≃ₐ[ℚ_[2]] L) →*
    RingAut (IsLocalRing.ResidueField (finiteNormInteger L)) :=
  (MulSemiringAction.toRingAut
    ((NormedField.valuation (K := L)).valuationSubring.decompositionSubgroup ℚ_[2])
    (IsLocalRing.ResidueField (finiteNormInteger L))).comp (finiteGaloisNormDecomposition L)

theorem finiteGaloisResidueAction_residue (g : L ≃ₐ[ℚ_[2]] L) (x : finiteNormInteger L) :
    finiteGaloisResidueAction L g (IsLocalRing.residue (finiteNormInteger L) x) =
      IsLocalRing.residue (finiteNormInteger L) (finiteGaloisNormDecomposition L g • x) :=
  (IsLocalRing.ResidueField.residue_smul
    ((NormedField.valuation (K := L)).valuationSubring.decompositionSubgroup ℚ_[2])
    (finiteGaloisNormDecomposition L g) x).symm

local instance : (NormedField.valuation (K := ℚ_[2])).HasExtension
    (NormedField.valuation (K := L)) := normValuation_hasExtension L
local instance : Algebra BaseInteger (finiteNormInteger L) :=
  Valuation.HasExtension.instAlgebra_valuationSubring
    (NormedField.valuation (K := ℚ_[2])) (NormedField.valuation (K := L))
local instance : IsLocalHom (algebraMap BaseInteger (finiteNormInteger L)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger

theorem finiteGaloisResidueAction_commutes_base (g : L ≃ₐ[ℚ_[2]] L) (a : k₀) :
    finiteGaloisResidueAction L g
        (algebraMap k₀ (IsLocalRing.ResidueField (finiteNormInteger L)) a) =
      algebraMap k₀ (IsLocalRing.ResidueField (finiteNormInteger L)) a := by
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  change finiteGaloisResidueAction L g
      (IsLocalRing.residue (finiteNormInteger L) (algebraMap BaseInteger (finiteNormInteger L) b)) =
    IsLocalRing.residue (finiteNormInteger L) (algebraMap BaseInteger (finiteNormInteger L) b)
  rw [finiteGaloisResidueAction_residue]
  congr 1
  apply Subtype.ext
  change g (algebraMap ℚ_[2] L (b : ℚ_[2])) = algebraMap ℚ_[2] L (b : ℚ_[2])
  exact g.commutes _

def finiteGaloisResidueAlgAction : (L ≃ₐ[ℚ_[2]] L) →*
    Gal(IsLocalRing.ResidueField (finiteNormInteger L)/k₀) where
  toFun g :=
    { finiteGaloisResidueAction L g with
      commutes' := finiteGaloisResidueAction_commutes_base L g }
  map_one' := by
    ext x
    change finiteGaloisResidueAction L 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change finiteGaloisResidueAction L (g * h) x =
      finiteGaloisResidueAction L g (finiteGaloisResidueAction L h x)
    rw [map_mul]
    rfl

end FiniteResidue

#print axioms finiteGalois_norm_eq
#print axioms finiteGalois_mem_normInteger_decomposition
#print axioms finiteGaloisNormDecomposition
#print axioms finiteGaloisResidueAction
#print axioms finiteGaloisResidueAction_residue
#print axioms finiteGaloisResidueAction_commutes_base
#print axioms finiteGaloisResidueAlgAction

end
end GQ2.Dyadic
