/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.FieldBranchSelector
import GQ2.Dyadic.Instances.Fields

/-!
# The residue-degree/norm bridge for ramified quadratic fields

For the odd-valuation quadratic family `K = ℚ₂(√a)`, the value group is visibly ramified:
`√a` has a norm which no element of `ℚ₂` has.  Combining that observation with the general
norm identity `e · v₂(N π) = [K : ℚ₂]` proves `e = 2` and `v₂(N π) = 1`.  The independently
proved unit-filtration computation `q_K = 2` gives `f = 1`, hence the exact bridge

`FF.f = (UnitNormIndex.normValPi K FF).toNat`.

This closes the arithmetic bridge for the four literal ramified rows `√-2`, `√2`, `√10`, and
`√-10`.  It does not assert the still-missing fundamental identity for an arbitrary finite
dyadic field.
-/

namespace GQ2.Dyadic.Fields

open IntermediateField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

variable {a : ℚ_[2]}

/-- An odd-valuation quadratic extension has absolute ramification index two. -/
theorem quadField_e_eq_two (hodd : Odd a.valuation) (ha : ¬ IsSquare a)
    (FF : DyadicUnitFiltration (quadField a)) : FF.e = 2 := by
  letI : Algebra.IsQuadraticExtension ℚ_[2] (quadField a) :=
    { finrank_eq_two' := finrank_quadField ha }
  let FQ : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] ℚ̄₂) :=
    GQ2.dyadicUnitFiltration' ⊥
  have hmul := GQ2.UnitNormIndex.e_mul_normValPi (quadField a) FF
  rw [finrank_quadField ha] at hmul
  have hnormPos := GQ2.UnitNormIndex.normValPi_pos (quadField a) FF
  have hePos : (1 : ℤ) ≤ FF.e := by exact_mod_cast FF.he_pos
  have heLe : FF.e ≤ 2 := by
    have hdvd : (FF.e : ℤ) ∣ 2 := ⟨GQ2.UnitNormIndex.normValPi (quadField a) FF, hmul.symm⟩
    have : (FF.e : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
    exact_mod_cast this
  have heCases : FF.e = 1 ∨ FF.e = 2 := by omega
  rcases heCases with heOne | heTwo
  · exfalso
    have hFQe : FQ.e = 1 := bot_e_eq_one FQ
    have hπ : ‖FF.π‖ = ‖FQ.π‖ :=
      GQ2.UnramifiedNorm.uniformizer_norm_eq_of_e_eq FQ FF (by rw [heOne, hFQe])
    have hunram := GQ2.UnramifiedNorm.hunram_of_uniformizer_norm_eq FQ FF hπ
    have ha0 : a ≠ 0 := ne_zero_of_odd_valuation hodd
    have hs0 : sqrtIn a ≠ 0 := by
      intro hs
      apply ha0
      apply (algebraMap ℚ_[2] ℚ̄₂).injective
      calc
        algebraMap ℚ_[2] ℚ̄₂ a = sqrtIn a ^ 2 := (sqrtIn_sq a).symm
        _ = 0 := by rw [hs]; norm_num
        _ = algebraMap ℚ_[2] ℚ̄₂ 0 := (map_zero _).symm
    obtain ⟨y, hy0, hybot, hnorm⟩ :=
      hunram (sqrtIn a) hs0 (sqrtIn_mem_quadField a)
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hybot
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hy0
      rw [← hc, hc0, map_zero]
    exact (norm_ne_norm_mul_sqrtIn hodd hc0 (one_ne_zero : (1 : ℚ_[2]) ≠ 0))
      (by simpa [← hc] using hnorm.symm)
  · exact heTwo

/-- The exact residue-degree/norm compatibility for every odd-valuation quadratic field. -/
theorem residueDegree_eq_normValPiToNat_quadField
    (hodd : Odd a.valuation) (ha : ¬ IsSquare a)
    (FF : DyadicUnitFiltration (quadField a)) :
    FF.f = (GQ2.UnitNormIndex.normValPi (quadField a) FF).toNat := by
  letI : Algebra.IsQuadraticExtension ℚ_[2] (quadField a) :=
    { finrank_eq_two' := finrank_quadField ha }
  have he := quadField_e_eq_two hodd ha FF
  have hnorm := GQ2.UnitNormIndex.e_mul_normValPi (quadField a) FF
  rw [he, finrank_quadField ha] at hnorm
  have hnormEq : GQ2.UnitNormIndex.normValPi (quadField a) FF = 1 := by
    omega
  have hq := qOf_quadField hodd ha FF
  rw [qOf_eq] at hq
  have hf : FF.f = 1 := by
    apply Nat.pow_right_injective (le_refl 2)
    simpa using hq
  rw [hf, hnormEq]
  rfl

/-- The numerical selector package for an odd-valuation quadratic field, with no externally
supplied degree or residue-degree binder. -/
def finiteDyadicParameters_quadField
    (hodd : Odd a.valuation) (ha : ¬ IsSquare a)
    (FF : DyadicUnitFiltration (quadField a)) :
    FiniteDyadicParameters (quadField a) FF := by
  letI : Algebra.IsQuadraticExtension ℚ_[2] (quadField a) :=
    { finrank_eq_two' := finrank_quadField ha }
  exact FiniteDyadicParameters.ofNormValPi FF
    (residueDegree_eq_normValPiToNat_quadField hodd ha FF)

end

end GQ2.Dyadic.Fields
