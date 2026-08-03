/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import Mathlib.NumberTheory.LocalField.Basic
import GQ2.Dyadic.ResidueNormBridge

/-!
# The spectral residue field as a Mathlib local-field residue field

The dyadic development realizes a finite extension of `ℚ₂` as an intermediate field of
`AlgebraicClosure ℚ₂`, with its inherited spectral norm.  Mathlib's new local-field API instead
starts from a `ValuativeRel`.  This file gives a named, non-instance bridge between those two
descriptions, and identifies the intrinsic residue field used by `UnitFiltrationCounts` with the
residue field of the resulting valuation ring.

The bridge is deliberately named rather than installed globally: Mathlib is in the middle of a
transition from `Valued` to `ValuativeRel`, and a global instance here would overlap any future
canonical instance for finite extensions.

The final section isolates why `Ideal.sum_ramification_inertia_eq_finrank` does not yet prove the
fundamental identity in this repository.  It needs a finite flat algebra of valuation rings,
together with identifications of its ring-theoretic ramification and inertia degrees.  Mathlib's
current local-field API supplies the individual DVRs and finite residue fields, but no extension
layer producing those facts for a finite extension.
-/

namespace GQ2.Dyadic.SpectralLocalField

open IsUltrametricDist
open scoped NNReal NormedField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

variable (K : IntermediateField ℚ_[2] ℚ̄₂)

/-- The valuative relation represented by the inherited spectral norm on `K`. -/
@[implicit_reducible]
def valuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

/-- The inherited norm topology is the topology of `valuativeRel K`. -/
theorem isValuativeTopology :
    letI : ValuativeRel K := valuativeRel K
    IsValuativeTopology K := by
  letI : ValuativeRel K := valuativeRel K
  letI : (NormedField.valuation (K := K)).Compatible :=
    Valuation.Compatible.ofValuation _
  apply IsValuativeTopology.of_zero
  intro s
  have hbridge :=
    (NormedField.valuation (K := K)).exists_setOf_restrict_le_iff (0 : K) s
  simp only [sub_zero] at hbridge
  rw [← hbridge]
  exact Valued.mem_nhds_zero

variable [FiniteDimensional ℚ_[2] K]

/-- A finite intermediate field, equipped with the valuative relation represented by its
inherited spectral norm, is a nonarchimedean local field in Mathlib's new API. -/
theorem isNonarchimedeanLocalField :
    letI : ValuativeRel K := valuativeRel K
    IsNonarchimedeanLocalField K := by
  letI : ValuativeRel K := valuativeRel K
  letI : (NormedField.valuation (K := K)).Compatible :=
    Valuation.Compatible.ofValuation _
  letI : IsValuativeTopology K := isValuativeTopology K
  have hnormTwo : ‖(2 : K)‖ < 1 := by
    change ‖(2 : ℚ̄₂)‖ < 1
    exact GQ2.norm_two_lt_one
  have hvaluationNontrivial :
      (NormedField.valuation (K := K)).IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨2, by norm_num, ?_⟩
    simpa [NormedField.valuation_apply, ← NNReal.coe_lt_coe] using hnormTwo
  letI : ValuativeRel.IsNontrivial K :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := K))).mpr hvaluationNontrivial
  letI : ProperSpace K := FiniteDimensional.proper ℚ_[2] K
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

/-! ## Identification of the two valuation rings -/

/-- The spectral-norm unit ball used by `UnitFiltrationCounts` is the valuation ring attached to
the norm-valued-field instance.  The equivalence is the identity on underlying field elements. -/
def oSubEquivNormInteger :
    GQ2.UnitFiltrationCounts.Osub K ≃+*
      (NormedField.valuation (K := K)).integer where
  toFun x := ⟨x, by simpa [Valuation.mem_integer_iff, ← NNReal.coe_le_coe] using x.2⟩
  invFun x := ⟨x, by simpa [Valuation.mem_integer_iff, ← NNReal.coe_le_coe] using x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Under the canonical norm-valued-field instance, `Valued.integer K` is definitionally the
integer ring of `NormedField.valuation`.  This declaration fixes the instance explicitly and so
is stable in the presence of other valued-field instances. -/
theorem valuedInteger_eq_normInteger :
    letI : Valued K ℝ≥0 := NormedField.toValued
    Valued.integer K = (NormedField.valuation (K := K)).integer := by
  rfl

/-- `oSubEquivNormInteger` in Mathlib's `Valued.integer` spelling. -/
def oSubEquivValuedInteger :
    letI : Valued K ℝ≥0 := NormedField.toValued
    GQ2.UnitFiltrationCounts.Osub K ≃+* Valued.integer K := by
  letI : Valued K ℝ≥0 := NormedField.toValued
  exact oSubEquivNormInteger K

@[simp]
theorem oSubEquivNormInteger_apply
    (x : GQ2.UnitFiltrationCounts.Osub K) :
    ((oSubEquivNormInteger K x :
      (NormedField.valuation (K := K)).integer) : K) = x := rfl

@[simp]
theorem oSubEquivNormInteger_symm_apply
    (x : (NormedField.valuation (K := K)).integer) :
    ((oSubEquivNormInteger K).symm x : K) = x := rfl

/-- Under the valuation-ring equivalence, the intrinsic open unit ball is exactly Mathlib's
maximal ideal of the norm valuation ring. -/
theorem map_maxIdeal_eq :
    Ideal.map (oSubEquivNormInteger K).toRingHom
        (GQ2.UnitFiltrationCounts.maxIdeal K) =
      IsLocalRing.maximalIdeal ((NormedField.valuation (K := K)).integer) := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective (oSubEquivNormInteger K).toRingHom
    (oSubEquivNormInteger K).surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change ‖(x : K)‖₊ < 1
    exact_mod_cast hx
  · intro hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hy
    refine ⟨(oSubEquivNormInteger K).symm y, ?_, (oSubEquivNormInteger K).apply_symm_apply y⟩
    change ‖(y : K)‖ < 1
    exact_mod_cast hy

/-- The intrinsic residue field of `UnitFiltrationCounts` is Mathlib's residue field of the norm
valuation ring. -/
def residueFieldEquivNormInteger :
    GQ2.UnitFiltrationCounts.ResidueField K ≃+*
      IsLocalRing.ResidueField ((NormedField.valuation (K := K)).integer) :=
  Ideal.quotientEquiv
    (GQ2.UnitFiltrationCounts.maxIdeal K)
    (IsLocalRing.maximalIdeal ((NormedField.valuation (K := K)).integer))
    (oSubEquivNormInteger K) (map_maxIdeal_eq K).symm

/-- Cardinality form of `residueFieldEquivNormInteger`. -/
theorem residueField_card_eq_normInteger_residueField_card :
    Nat.card (GQ2.UnitFiltrationCounts.ResidueField K) =
      Nat.card (IsLocalRing.ResidueField
        ((NormedField.valuation (K := K)).integer)) :=
  Nat.card_congr (residueFieldEquivNormInteger K).toEquiv

/-- The filtration exponent `FF.f` is the exponent of the cardinality of Mathlib's valuation-ring
residue field.  Thus the residue-field half of the prospective ramification/inertia comparison is
already completely identified; the missing work is extension-level, not a mismatch of residue
field models. -/
theorem normInteger_residueField_card_eq_pow_f (FF : GQ2.DyadicUnitFiltration K) :
    Nat.card (IsLocalRing.ResidueField
        ((NormedField.valuation (K := K)).integer)) = 2 ^ FF.f := by
  rw [← residueField_card_eq_normInteger_residueField_card K]
  exact GQ2.UnitFiltrationCounts.residueField_card_eq_pow_f K FF

end

end GQ2.Dyadic.SpectralLocalField
