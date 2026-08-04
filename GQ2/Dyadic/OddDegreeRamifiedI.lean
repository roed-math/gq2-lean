/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.RamifiedI
import GQ2.Dyadic.FieldBranchSelector
import GQ2.UnitNormIndex

/-!
# Odd degree forces ramification of `K(i)/K`

The repository represents unramifiedness of a quadratic extension by the literal
`HasEqualNormValueGroups` predicate.  This file proves directly, without importing a separate
ramification theory, that an odd-degree finite extension `K/ℚ₂` cannot have equal norm value
groups after adjoining a square root of `-1`.

The key witness is `1 + i`, whose norm has square `‖2‖`.  If its norm occurred in `K`, the
field norm down to `ℚ₂` would force an even integer to equal `[K : ℚ₂]`.
-/

namespace GQ2.Dyadic

noncomputable section

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The absolute value of the algebraic norm from an arbitrary finite dyadic field is the
`[K : ℚ₂]`-th power of the spectral absolute value.  Unlike
`UnitNormIndex.norm_val`, this version does not require `K/ℚ₂` to be Galois: the algebraic
norm is expanded over all embeddings of `K` into `ℚ̄₂`, and each embedding extends to an
automorphism of the algebraic closure. -/
theorem norm_algebra_eq_norm_pow_finrank
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] (x : K) :
    ‖(Algebra.norm ℚ_[2] x : ℚ_[2])‖ =
      ‖(x : ℚ̄₂)‖ ^ Module.finrank ℚ_[2] K := by
  classical
  have hconj : ∀ σ : K →ₐ[ℚ_[2]] ℚ̄₂, ‖σ x‖ = ‖(x : ℚ̄₂)‖ := by
    intro σ
    let g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂ :=
      AlgEquiv.ofBijective (σ.liftNormal ℚ̄₂)
        (AlgHom.normal_bijective ℚ_[2] ℚ̄₂ ℚ̄₂ _)
    have hcomm : g (algebraMap K ℚ̄₂ x) = σ x := by
      simpa [g] using σ.liftNormal_commutes ℚ̄₂ x
    rw [← hcomm, ← AlgEquiv.smul_def]
    exact norm_galois g (algebraMap K ℚ̄₂ x)
  have hprod : algebraMap ℚ_[2] ℚ̄₂ (Algebra.norm ℚ_[2] x) =
      ∏ σ : K →ₐ[ℚ_[2]] ℚ̄₂, σ x :=
    Algebra.norm_eq_prod_embeddings ℚ_[2] ℚ̄₂ x
  rw [← norm_algebraMap' (𝕜' := ℚ̄₂) (Algebra.norm ℚ_[2] x), hprod, norm_prod]
  calc
    ∏ σ : K →ₐ[ℚ_[2]] ℚ̄₂, ‖σ x‖ =
        ∏ _σ : K →ₐ[ℚ_[2]] ℚ̄₂, ‖(x : ℚ̄₂)‖ :=
      Finset.prod_congr rfl (fun σ _ ↦ hconj σ)
    _ = ‖(x : ℚ̄₂)‖ ^ Module.finrank ℚ_[2] K := by
      rw [Finset.prod_const, Finset.card_univ, AlgHom.card]

/-- If `[K : ℚ₂]` is odd, adjoining any square root of `-1` fails the repository's literal
equal-norm-value-groups criterion. -/
theorem not_hasEqualNormValueGroups_sqrt_neg_one_of_odd_finrank
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (hodd : Odd (Module.finrank ℚ_[2] K)) (δi : ℚ̄₂) (hδi : δi ^ 2 = -1) :
    ¬ HasEqualNormValueGroups K δi := by
  intro hunram
  let z : ℚ̄₂ := 1 + δi
  have hδnorm : ‖δi‖ = 1 := by
    have hsquare : ‖δi‖ ^ 2 = 1 := by
      rw [← norm_pow, hδi, norm_neg, norm_one]
    nlinarith [norm_nonneg δi]
  have hzsq : z ^ 2 = 2 * δi := by
    dsimp [z]
    calc
      (1 + δi) ^ 2 = 1 + 2 * δi + δi ^ 2 := by ring
      _ = 2 * δi := by rw [hδi]; ring
  have hz0 : z ≠ 0 := by
    intro hz
    have hδ : δi = -1 := by
      dsimp [z] at hz
      linear_combination hz
    rw [hδ] at hδi
    norm_num at hδi
  have hznormsq : ‖z‖ ^ 2 = ‖(2 : ℚ_[2])‖ := by
    calc
      ‖z‖ ^ 2 = ‖z ^ 2‖ := (norm_pow z 2).symm
      _ = ‖(2 : ℚ̄₂) * δi‖ := by rw [hzsq]
      _ = ‖(2 : ℚ̄₂)‖ * ‖δi‖ := norm_mul _ _
      _ = ‖(2 : ℚ_[2])‖ := by
        rw [hδnorm, mul_one,
          show (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 from (map_ofNat _ 2).symm,
          norm_algebraMap']
  obtain ⟨w, hw0, hwnorm⟩ := hunram z hz0 ⟨1, 1, by simp [z]⟩
  have hwnormsq : ‖(w : ℚ̄₂)‖ ^ 2 = ‖(2 : ℚ_[2])‖ := by
    rw [← hwnorm]
    exact hznormsq
  have hnormpow : ‖(Algebra.norm ℚ_[2] w : ℚ_[2])‖ ^ 2 =
      ‖(2 : ℚ_[2])‖ ^ Module.finrank ℚ_[2] K := by
    rw [norm_algebra_eq_norm_pow_finrank K w]
    calc
      (‖(w : ℚ̄₂)‖ ^ Module.finrank ℚ_[2] K) ^ 2 =
          ‖(w : ℚ̄₂)‖ ^ (Module.finrank ℚ_[2] K * 2) :=
        (pow_mul _ _ _).symm
      _ = ‖(w : ℚ̄₂)‖ ^ (2 * Module.finrank ℚ_[2] K) := by
        rw [Nat.mul_comm]
      _ = (‖(w : ℚ̄₂)‖ ^ 2) ^ Module.finrank ℚ_[2] K := pow_mul _ _ _
      _ = ‖(2 : ℚ_[2])‖ ^ Module.finrank ℚ_[2] K := by rw [hwnormsq]
  have hN0 : (Algebra.norm ℚ_[2] w : ℚ_[2]) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr (by simpa using hw0)
  rw [Padic.norm_eq_zpow_neg_valuation hN0, UnitNormIndex.norm_two,
    ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul] at hnormpow
  have hexp := zpow_right_injective₀
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hnormpow
  obtain ⟨k, hk⟩ := hodd
  omega

/-- Every finite odd-degree dyadic field canonically supplies the campaign's `RamifiedIData`.
The square root is chosen in the fixed algebraic closure; the ramification field is proved by
the preceding norm-value calculation. -/
noncomputable def ramifiedIData_of_odd_finrank
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (hodd : Odd (Module.finrank ℚ_[2] K)) : RamifiedIData K := by
  let hex := IsAlgClosed.exists_pow_nat_eq (-1 : ℚ̄₂) (n := 2) (by norm_num)
  let δi := Classical.choose hex
  have hδi : δi ^ 2 = -1 := Classical.choose_spec hex
  exact ⟨δi, hδi,
    not_hasEqualNormValueGroups_sqrt_neg_one_of_odd_finrank hodd δi hδi⟩

#print axioms norm_algebra_eq_norm_pow_finrank
#print axioms not_hasEqualNormValueGroups_sqrt_neg_one_of_odd_finrank
#print axioms ramifiedIData_of_odd_finrank

end


end GQ2.Dyadic
