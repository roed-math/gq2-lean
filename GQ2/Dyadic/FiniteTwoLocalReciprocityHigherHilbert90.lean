/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.FiniteTwoLocalReciprocityHigherKummerExact
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Finite-factorization Hilbert 90 for higher Kummer theory

Mathlib proves multiplicative Hilbert 90 for a finite Galois extension.  This file packages the
precise descent datum needed to apply it to a cocycle on the absolute Galois group, then restricts
the resulting interface to the finite-valued `MuN n` cocycles used by higher Kummer theory.

There is deliberately no assertion of Hilbert 90 for arbitrary p-adically continuous maps into
`Qbar_2^x`: such maps need not have finite image.  The only remaining field-correspondence seam is
`MuNFiniteHilbert90FactorizationSupply`, which asks that a `MuN n`-valued continuous cocycle be
inflated from some finite Galois layer.
-/

namespace GQ2.Dyadic

open ContCoh
open scoped Classical

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]

set_option synthInstance.maxHeartbeats 200000 in
/-- Explicit data saying that a multiplicative cocycle on `G_K` is inflated from a cocycle on
one finite Galois layer of `ℚ̄₂/K`. -/
structure FiniteHilbert90Factorization
    (K : IntermediateField ℚ_[2] ℚbar2)
    (f : ↥(K.fixingSubgroup) → ℚbar2ˣ) where
  L : IntermediateField (↥K) ℚbar2
  [finiteDimensional : FiniteDimensional (↥K) L]
  [normal : Normal (↥K) L]
  cocycle : (L ≃ₐ[↥K] L) → Lˣ
  isMulCocycle : groupCohomology.IsMulCocycle₁ cocycle
  inflate : ∀ g : ↥(K.fixingSubgroup),
    Units.map L.val
      (cocycle (AlgEquiv.restrictNormalHom L (IntermediateField.fixingSubgroupEquiv K g))) = f g

namespace FiniteHilbert90Factorization

variable {f : ↥(K.fixingSubgroup) → ℚbar2ˣ}

/-- Restriction of an element of `G_K` to the chosen finite normal layer. -/
noncomputable def restriction (F : FiniteHilbert90Factorization K f) :
    ↥(K.fixingSubgroup) →* (F.L ≃ₐ[↥K] F.L) := by
  letI := F.normal
  exact (AlgEquiv.restrictNormalHom F.L).comp
    (IntermediateField.fixingSubgroupEquiv K).toMonoidHom

/-- Inclusion of the finite layer into `ℚ̄₂`, on units. -/
noncomputable def inclusionUnits (F : FiniteHilbert90Factorization K f) : F.Lˣ →* ℚbar2ˣ :=
  Units.map F.L.val

@[simp] theorem inclusionUnits_cocycle (F : FiniteHilbert90Factorization K f)
    (g : ↥(K.fixingSubgroup)) :
    F.inclusionUnits (F.cocycle (F.restriction g)) = f g := by
  letI := F.normal
  simpa [restriction, inclusionUnits] using F.inflate g

set_option synthInstance.maxHeartbeats 200000 in
/-- Restriction and inclusion respect the Galois action. -/
theorem inclusionUnits_smul (F : FiniteHilbert90Factorization K f)
    (g : ↥(K.fixingSubgroup)) (b : F.Lˣ) :
    F.inclusionUnits (F.restriction g • b) = g • F.inclusionUnits b := by
  letI := F.normal
  apply Units.ext
  simp only [restriction, MonoidHom.comp_apply]
  change ((AlgEquiv.restrictNormalHom F.L (IntermediateField.fixingSubgroupEquiv K g))
    (b : F.L) : ℚbar2) = g.1 (b : ℚbar2)
  rw [AlgEquiv.restrictNormalHom_apply]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- Finite-extension Hilbert 90, embedded back into `ℚ̄₂`, trivializes an explicitly
factored cocycle on `G_K`. -/
theorem exists_coboundary (F : FiniteHilbert90Factorization K f) :
    ∃ beta : ℚbar2ˣ, ∀ g : ↥(K.fixingSubgroup),
      f g = (g • beta) * beta⁻¹ := by
  letI := F.finiteDimensional
  letI := F.normal
  obtain ⟨b, hb⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      F.cocycle F.isMulCocycle
  refine ⟨F.inclusionUnits b, fun g => ?_⟩
  calc
    f g = F.inclusionUnits (F.cocycle (F.restriction g)) :=
      (F.inclusionUnits_cocycle g).symm
    _ = F.inclusionUnits ((F.restriction g • b) / b) := by rw [hb]
    _ = F.inclusionUnits (F.restriction g • b) * (F.inclusionUnits b)⁻¹ := by
      rw [map_div, div_eq_mul_inv]
    _ = (g • F.inclusionUnits b) * (F.inclusionUnits b)⁻¹ := by
      rw [F.inclusionUnits_smul]

end FiniteHilbert90Factorization

/-- The multiplicative `ℚ̄₂ˣ`-valued cocycle underlying a `MuN n`-valued additive
cocycle. -/
def muNCocycleUnits {n : ℕ} [NeZero n]
    (z : Z1 ↥(K.fixingSubgroup) (MuN n)) : ↥(K.fixingSubgroup) → ℚbar2ˣ :=
  fun g ↦ (z.1 g).toMul.1

/-- The underlying units-valued cocycle is continuous because `MuN n` is discrete. -/
theorem continuous_muNCocycleUnits {n : ℕ} [NeZero n]
    (z : Z1 ↥(K.fixingSubgroup) (MuN n)) : Continuous (muNCocycleUnits z) := by
  have hcoe : Continuous (fun x : MuN n => x.toMul.1) := continuous_of_discreteTopology
  change Continuous (fun g => (z.1 g).toMul.1)
  exact hcoe.comp (mem_Z1_iff.mp z.2).1

/-- The additive `Z1` identity becomes the usual multiplicative crossed-homomorphism law after
coercion from roots of unity to `ℚ̄₂ˣ`. -/
theorem muNCocycleUnits_mul {n : ℕ} [NeZero n]
    (z : Z1 ↥(K.fixingSubgroup) (MuN n)) (g h : ↥(K.fixingSubgroup)) :
    muNCocycleUnits z (g * h) =
      muNCocycleUnits z g * (g • muNCocycleUnits z h) := by
  have hz := (mem_Z1_iff.mp z.2).2 g h
  have hu := congrArg (fun x : MuN n => x.toMul.1) hz
  change muNCocycleUnits z (g * h) =
    muNCocycleUnits z g * (g • muNCocycleUnits z h) at hu
  exact hu

/-- Every value of the coerced cocycle still has `n`-th power one. -/
theorem muNCocycleUnits_pow {n : ℕ} [NeZero n]
    (z : Z1 ↥(K.fixingSubgroup) (MuN n)) (g : ↥(K.fixingSubgroup)) :
    muNCocycleUnits z g ^ n = 1 := by
  exact (mem_rootsOfUnity n ((z.1 g).toMul : ℚbar2ˣ)).mp (z.1 g).toMul.2

/-- The true remaining field-correspondence input: every `MuN n`-valued continuous cocycle
factors through one finite normal Galois layer. -/
def MuNFiniteHilbert90FactorizationSupply
    (K : IntermediateField ℚ_[2] ℚbar2) (n : ℕ) [NeZero n] : Prop :=
  ∀ z : Z1 ↥(K.fixingSubgroup) (MuN n),
    Nonempty (FiniteHilbert90Factorization K (muNCocycleUnits z))

/-- A finite-factorization supply, together with Mathlib's finite Galois Hilbert 90, proves the
narrow `MuNContinuousHilbert90` statement required by higher Kummer surjectivity. -/
theorem muNContinuousHilbert90_of_finiteFactorizationSupply
    {n : ℕ} [NeZero n] (S : MuNFiniteHilbert90FactorizationSupply K n) :
    MuNContinuousHilbert90 K n := by
  intro z
  obtain ⟨beta, hbeta⟩ := (Classical.choice (S z)).exists_coboundary
  exact ⟨beta, fun g => by simpa [muNCocycleUnits] using hbeta g⟩

#print axioms FiniteHilbert90Factorization.exists_coboundary
#print axioms continuous_muNCocycleUnits
#print axioms muNCocycleUnits_mul
#print axioms muNCocycleUnits_pow
#print axioms muNContinuousHilbert90_of_finiteFactorizationSupply

end
end GQ2.Dyadic
