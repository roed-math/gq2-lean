/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueFiniteFrobenius
import Mathlib.Algebra.Polynomial.Lifts

/-!
# The absolute norm-residue field is an algebraic closure of the base residue field

`RamifiedCertificateAbsoluteResidueFiniteFrobenius` proves that the residue field of the norm
valuation ring in `AlgebraicClosure ℚ_[2]` is algebraic over the two-element base residue field.
This module proves the complementary algebraic-closedness statement directly.

Given a monic irreducible polynomial over the absolute residue field, lift it coefficientwise
through the surjective residue map to a monic polynomial over `absoluteNormInteger`.  Its image in
`AlgebraicClosure ℚ_[2]` has a root.  Because it is monic, that root is integral over the
valuation ring.  Valuation subrings are integrally closed and have their ambient field as fraction
field, so the root comes from `absoluteNormInteger`; reducing it gives a root of the original
polynomial.

Consequently the absolute residue field is an algebraic closure of the two-element base residue
field.  Mathlib's finite-field Frobenius is therefore globally defined here, and is concretely the
square map.

The remaining field-side seam for `AbsoluteUnramifiedFrobeniusCoordinate` is no longer a residue
field classification theorem.  It is the standard topological residue exact sequence: prove that
`absoluteResidueAction` lands in and surjects onto the base-linear automorphism group, that its
kernel quotient carries the correct profinite topology, and that this automorphism group is
continuously `Zhat`, with square Frobenius sent to `Zhat.ofInt 1`.  The oriented-tame comparison
then additionally requires the W177 Frobenius commuting square.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField
open Polynomial

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
local notation "k₀" => IsLocalRing.ResidueField BaseInteger
local notation "k̄₂" => IsLocalRing.ResidueField absoluteNormInteger

local instance : Algebra BaseInteger absoluteNormInteger := absoluteNormIntegerAlgebra
local instance : IsLocalHom (algebraMap BaseInteger absoluteNormInteger) :=
  absoluteNormInteger_algebraMap_isLocalHom
local instance : Algebra k₀ k̄₂ := absoluteResidueFieldAlgebra

/-! ## Algebraic closedness -/

/-- The residue field of the norm valuation ring in `AlgebraicClosure ℚ_[2]` is algebraically
closed. -/
theorem absoluteResidueField_isAlgClosed : IsAlgClosed k̄₂ := by
  apply IsAlgClosed.of_exists_root
  intro p hpmonic hpirr
  obtain ⟨q, hqmap, hqdeg, hqmonic⟩ :=
    lifts_and_degree_eq_and_monic
      (f := IsLocalRing.residue absoluteNormInteger)
      (mem_lifts_of_surjective IsLocalRing.residue_surjective p) hpmonic
  let Q : ℚ̄₂[X] := q.map (algebraMap absoluteNormInteger ℚ̄₂)
  have hQmonic : Q.Monic := hqmonic.map _
  have hQdeg : Q.degree ≠ 0 := by
    unfold Q
    rw [hqmonic.degree_map, hqdeg]
    exact (degree_pos_of_irreducible hpirr).ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root Q hQdeg
  have hyint : IsIntegral absoluteNormInteger y := by
    refine ⟨q, hqmonic, ?_⟩
    simpa [aeval_def, Q, IsRoot.def] using hy
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hyint
  refine ⟨IsLocalRing.residue absoluteNormInteger x, ?_⟩
  have hqx : q.eval x = 0 := by
    apply Subtype.ext
    change algebraMap absoluteNormInteger ℚ̄₂ (q.eval x) = 0
    rw [← eval_map_apply, hx]
    exact hy
  rw [← hqmap, eval_map_apply, hqx, map_zero]

/-! ## Algebraic-closure and Frobenius consequences -/

/-- The absolute norm-residue field is an algebraic closure of the two-element base residue
field. -/
theorem absoluteResidueField_isAlgClosure : IsAlgClosure k₀ k̄₂ where
  isAlgClosed := absoluteResidueField_isAlgClosed
  isAlgebraic := absoluteResidueField_isAlgebraic

local instance : Finite k₀ := baseResidueField_finite
local instance : Fintype k₀ := Fintype.ofFinite k₀
local instance : Algebra.IsAlgebraic k₀ k̄₂ := absoluteResidueField_isAlgebraic
local instance : IsAlgClosure k₀ k̄₂ := absoluteResidueField_isAlgClosure

/-- A noncanonical identification of the absolute norm-residue field with Mathlib's algebraic
closure of its two-element base residue field. -/
def absoluteResidueFieldEquivAlgebraicClosure :
    k̄₂ ≃ₐ[k₀] AlgebraicClosure k₀ :=
  IsAlgClosure.equiv k₀ k̄₂ (AlgebraicClosure k₀)

/-- The canonical square Frobenius on the absolute residue field. -/
def absoluteResidueFrobenius : Gal(k̄₂/k₀) :=
  FiniteField.frobeniusAlgEquivOfAlgebraic k₀ k̄₂

@[simp]
theorem absoluteResidueFrobenius_apply (x : k̄₂) :
    absoluteResidueFrobenius x = x ^ 2 := by
  change x ^ Fintype.card k₀ = x ^ 2
  rw [baseResidueField_fintype_card]

#print axioms absoluteResidueField_isAlgClosed
#print axioms absoluteResidueField_isAlgClosure
#print axioms absoluteResidueFieldEquivAlgebraicClosure
#print axioms absoluteResidueFrobenius
#print axioms absoluteResidueFrobenius_apply

end


end GQ2.Dyadic
