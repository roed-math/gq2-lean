/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateQurZhatFrobeniusComparison
import GQ2.Dyadic.RamificationInertiaBridge
import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite-level Frobenius in the absolute residue field

This module supplies the first field-theoretic part of the Frobenius coordinate left open by
`AbsoluteUnramifiedFrobeniusCoordinate`.  The norm valuation on `AlgebraicClosure ℚ_[2]`
extends the base norm valuation.  Hence its residue field is canonically an algebra over the
two-element base residue field.

Every element of the absolute residue field comes from a finite residue extension.  Indeed, lift
the residue class to an integral algebraic `2`-adic number, adjoin that lift to `ℚ_[2]`, and use
`SpectralLocalField.integer_finite` for the resulting finite intermediate field.  It follows that
the absolute residue field is algebraic over the base residue field.

At every such finite level, Mathlib's finite-field theorem applies: the Galois group is exhausted
by the powers of Frobenius, and this Frobenius is the square map because the base residue field has
cardinality two.

The remaining input is now sharply separated from this finite-level algebra:

* prove that the absolute residue field is algebraically closed; and
* prove the standard residue exact sequence: the absolute residue action is onto the automorphism
  group of that algebraic closure and induces the quotient topology; then identify this profinite
  Galois group continuously with `Zhat`, normalized so that square Frobenius maps to
  `Zhat.ofInt 1`.

Mathlib currently has neither the algebraic-closedness theorem for a valuation residue field nor
this infinite residue-Galois exact sequence/equivalence with `Zhat`.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
local notation "k₀" => IsLocalRing.ResidueField BaseInteger
local notation "k̄₂" => IsLocalRing.ResidueField absoluteNormInteger

/-! ## The canonical absolute residue-field extension -/

/-- The norm valuation on the algebraic closure extends the norm valuation on `ℚ_[2]`. -/
theorem absoluteNormValuation_hasExtension :
    (NormedField.valuation (K := ℚ_[2])).HasExtension
      (NormedField.valuation (K := ℚ̄₂)) := by
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  simp only [Valuation.comap_apply, NormedField.valuation_apply]
  have hnorm : ‖(algebraMap ℚ_[2] ℚ̄₂ x : ℚ̄₂)‖₊ = ‖x‖₊ :=
    nnnorm_algebraMap' ℚ̄₂ x
  rw [hnorm]

local instance absoluteNormValuationHasExtension :
    (NormedField.valuation (K := ℚ_[2])).HasExtension
      (NormedField.valuation (K := ℚ̄₂)) :=
  absoluteNormValuation_hasExtension

/-- The canonical algebra of the absolute norm-integer ring over the base norm-integer ring. -/
@[reducible] noncomputable def absoluteNormIntegerAlgebra :
    Algebra BaseInteger absoluteNormInteger :=
  Valuation.HasExtension.instAlgebra_valuationSubring
    (NormedField.valuation (K := ℚ_[2])) (NormedField.valuation (K := ℚ̄₂))

local instance : Algebra BaseInteger absoluteNormInteger := absoluteNormIntegerAlgebra

/-- The norm-integer inclusion is a local homomorphism. -/
theorem absoluteNormInteger_algebraMap_isLocalHom :
    IsLocalHom (algebraMap BaseInteger absoluteNormInteger) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger

local instance : IsLocalHom (algebraMap BaseInteger absoluteNormInteger) :=
  absoluteNormInteger_algebraMap_isLocalHom

/-- The induced algebra of the absolute residue field over the base residue field. -/
@[reducible] noncomputable def absoluteResidueFieldAlgebra : Algebra k₀ k̄₂ := inferInstance

local instance : Algebra k₀ k̄₂ := absoluteResidueFieldAlgebra

/-- The two-element base residue field is finite. -/
theorem baseResidueField_finite : Finite k₀ :=
  Finite.of_injective baseIntegerResidueEquivZMod baseIntegerResidueEquivZMod.injective

local instance : Finite k₀ := baseResidueField_finite
local instance : Fintype k₀ := Fintype.ofFinite k₀

/-- The base residue field used by the valuation extension has cardinality two. -/
theorem baseResidueField_fintype_card : Fintype.card k₀ = 2 := by
  rw [← Nat.card_eq_fintype_card, baseInteger_residue_card]

/-- The inherited norm valuation on a finite intermediate field extends further to the algebraic
closure. -/
theorem intermediateNormValuation_to_absolute_hasExtension
    (K : IntermediateField ℚ_[2] ℚ̄₂) :
    (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := ℚ̄₂)) := by
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  simp only [Valuation.comap_apply, NormedField.valuation_apply]
  have hnorm : ‖(algebraMap K ℚ̄₂ x : ℚ̄₂)‖₊ = ‖x‖₊ := rfl
  rw [hnorm]

/-! ## Algebraicity by finite residue levels -/

/-- Every element of the absolute residue field lies in a finite residue extension of the base;
in particular the absolute residue field is algebraic over the two-element base residue field. -/
theorem absoluteResidueField_isAlgebraic : Algebra.IsAlgebraic k₀ k̄₂ := by
  constructor
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  let y : ℚ̄₂ := x
  have hyint : IsIntegral ℚ_[2] y := Algebra.IsIntegral.isIntegral y
  let K : IntermediateField ℚ_[2] ℚ̄₂ := IntermediateField.adjoin ℚ_[2] {y}
  letI : FiniteDimensional ℚ_[2] K := IntermediateField.adjoin.finiteDimensional hyint
  letI : (NormedField.valuation (K := ℚ_[2])).HasExtension
      (NormedField.valuation (K := K)) := normValuation_hasExtension K
  letI : Algebra BaseInteger (ExtensionInteger K) :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      (NormedField.valuation (K := ℚ_[2])) (NormedField.valuation (K := K))
  letI : IsLocalHom (algebraMap BaseInteger (ExtensionInteger K)) :=
    Valuation.HasExtension.instIsLocalHomValuationInteger
  letI : Module.Finite BaseInteger (ExtensionInteger K) := integer_finite K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := ℚ̄₂)) :=
    intermediateNormValuation_to_absolute_hasExtension K
  letI : Algebra (ExtensionInteger K) absoluteNormInteger :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      (NormedField.valuation (K := K)) (NormedField.valuation (K := ℚ̄₂))
  letI : IsLocalHom (algebraMap (ExtensionInteger K) absoluteNormInteger) :=
    Valuation.HasExtension.instIsLocalHomValuationInteger
  letI : IsScalarTower BaseInteger (ExtensionInteger K) absoluteNormInteger :=
    .of_algebraMap_eq fun r => by apply Subtype.ext; rfl
  let xK : ExtensionInteger K := ⟨⟨y,
    IntermediateField.mem_adjoin_simple_self ℚ_[2] y⟩, x.property⟩
  have hfin : IsIntegral k₀ (IsLocalRing.residue (ExtensionInteger K) xK) :=
    IsIntegral.of_finite k₀ _
  have hmap : algebraMap (IsLocalRing.ResidueField (ExtensionInteger K)) k̄₂
      (IsLocalRing.residue (ExtensionInteger K) xK) =
        IsLocalRing.residue absoluteNormInteger x := by
    rfl
  rw [← hmap]
  exact (hfin.map (IsScalarTower.toAlgHom k₀
    (IsLocalRing.ResidueField (ExtensionInteger K)) k̄₂)).isAlgebraic

/-! ## The exact finite-level Frobenius theorem -/

/-- On the residue field of every finite intermediate extension, powers of Frobenius exhaust the
finite Galois group. -/
theorem finiteResidue_frobeniusPowers_bijective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] :
    letI := normValuation_hasExtension K
    letI : Algebra BaseInteger (ExtensionInteger K) :=
      Valuation.HasExtension.instAlgebra_valuationSubring
        (NormedField.valuation (K := ℚ_[2])) (NormedField.valuation (K := K))
    letI : IsLocalHom (algebraMap BaseInteger (ExtensionInteger K)) :=
      Valuation.HasExtension.instIsLocalHomValuationInteger
    letI : Module.Finite BaseInteger (ExtensionInteger K) := integer_finite K
    Function.Bijective (fun n : Fin (Module.finrank k₀
        (IsLocalRing.ResidueField (ExtensionInteger K))) =>
      FiniteField.frobeniusAlgEquivOfAlgebraic k₀
        (IsLocalRing.ResidueField (ExtensionInteger K)) ^ n.1) := by
  letI := normValuation_hasExtension K
  letI : Algebra BaseInteger (ExtensionInteger K) :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      (NormedField.valuation (K := ℚ_[2])) (NormedField.valuation (K := K))
  letI : IsLocalHom (algebraMap BaseInteger (ExtensionInteger K)) :=
    Valuation.HasExtension.instIsLocalHomValuationInteger
  letI : Module.Finite BaseInteger (ExtensionInteger K) := integer_finite K
  letI : Finite (IsLocalRing.ResidueField (ExtensionInteger K)) :=
    IsLocalRing.ResidueField.finite_of_finite (R := BaseInteger)
      (S := ExtensionInteger K) inferInstance
  exact FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k₀
    (IsLocalRing.ResidueField (ExtensionInteger K))

/-- The finite-level Frobenius above is concretely the square map. -/
theorem finiteResidue_frobenius_apply
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (x : IsLocalRing.ResidueField (ExtensionInteger K)) :
    letI := normValuation_hasExtension K
    letI : Algebra BaseInteger (ExtensionInteger K) :=
      Valuation.HasExtension.instAlgebra_valuationSubring
        (NormedField.valuation (K := ℚ_[2])) (NormedField.valuation (K := K))
    letI : IsLocalHom (algebraMap BaseInteger (ExtensionInteger K)) :=
      Valuation.HasExtension.instIsLocalHomValuationInteger
    letI : Module.Finite BaseInteger (ExtensionInteger K) := integer_finite K
    FiniteField.frobeniusAlgEquivOfAlgebraic k₀
      (IsLocalRing.ResidueField (ExtensionInteger K)) x = x ^ 2 := by
  letI := normValuation_hasExtension K
  letI : Algebra BaseInteger (ExtensionInteger K) :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      (NormedField.valuation (K := ℚ_[2])) (NormedField.valuation (K := K))
  letI : IsLocalHom (algebraMap BaseInteger (ExtensionInteger K)) :=
    Valuation.HasExtension.instIsLocalHomValuationInteger
  letI : Module.Finite BaseInteger (ExtensionInteger K) := integer_finite K
  letI : Finite (IsLocalRing.ResidueField (ExtensionInteger K)) :=
    IsLocalRing.ResidueField.finite_of_finite (R := BaseInteger)
      (S := ExtensionInteger K) inferInstance
  rw [show FiniteField.frobeniusAlgEquivOfAlgebraic k₀
      (IsLocalRing.ResidueField (ExtensionInteger K)) x =
        x ^ Fintype.card k₀ from rfl,
    baseResidueField_fintype_card]

#print axioms absoluteNormValuation_hasExtension
#print axioms absoluteNormInteger_algebraMap_isLocalHom
#print axioms baseResidueField_fintype_card
#print axioms intermediateNormValuation_to_absolute_hasExtension
#print axioms absoluteResidueField_isAlgebraic
#print axioms finiteResidue_frobeniusPowers_bijective
#print axioms finiteResidue_frobenius_apply

end


end GQ2.Dyadic
