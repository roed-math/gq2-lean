/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameShadowWord
import GQ2.Dyadic.Word.Hessian

/-!
# Extraspecial unramified shadow comparison

The determinant phase lives in the kappa-zero central extension, not merely
in the polarized Heisenberg pairing. Here the shadow and splice equalities
are proved in that full extension, preserving the quadratic diagonal and the
equivariant factor-set correction. The tau graph value is required to be one,
and every wild graph value must have trivial lower group coordinate.

The exponent-four bound is essential and is discharged by the proved
extraspecial power theorem. No assertion of a source determinant certificate
or of a boundary equivalence is made here.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH GQ2.SectionSix Count

/-- A word shadow is invisible if its generator substitution is literally the identity. -/
theorem evalZ_tameShadow_of_tau_one_of_wild_pow
    {n : ℕ} {G : Type*} [Group G]
    (p : Generator n → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (htau : p .tau=1) (hwild : ∀ i, p (.wild i) ^ E omega2 = p (.wild i))
    (R : PWord (Generator n)) :
    PWord.evalZ p E E₂ (tameShadow R) = PWord.evalZ p E E₂ R := by
  rw [tameShadow, PWord.evalZ_subst]
  congr 1
  funext g
  cases g with
  | sigma => rfl
  | tau => exact htau.symm
  | wild i => simp [tameShadowSubst, htau, hwild]

/-- The class one modulo four fixes an element of exponent dividing four. -/
theorem pow_eq_self_of_pow_four_eq_one
    {G : Type*} [Group G] (p : G) (hp : p^4=1) {e : ℕ} (he : e%4=1) : p^e=p := by
  have heq : e=4*(e/4)+1 := by omega
  rw [heq, pow_add, pow_mul, hp, one_pow, pow_one, one_mul]

/-- Unramified normal shadows preserve the full extraspecial evaluation. -/
theorem hessEvalZ_tameShadow_unramified
    {n : ℕ} {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (mu : Generator n → SemiProd C V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hV₂ : ∀ v : V, v+v=0) (htau : mu .tau=1)
    (hwild : ∀ i, (mu (.wild i)).2=1)
    {e : ℕ} (hE : E omega2=(e:ℤ)) (he : e%4=1)
    (R : PWord (Generator n)) :
    hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ (tameShadow R) =
      hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ R := by
  apply evalZ_tameShadow_of_tau_one_of_wild_pow
  · apply WordCoh.CentExt.ext
    · exact htau
    · rfl
  · intro i
    rw [hE, zpow_natCast]
    apply pow_eq_self_of_pow_four_eq_one _ _ he
    have H := kappa0_pow_eq_one_of_snd_pow dat hdat hV₂
      (WordCoh.lift mu (kappa0Cocycle dat hdat) (.wild i))
      (n := 1) (by simpa using hwild i)
    simpa using H

/-- An unramified normal splice retains the structural word's entire quadratic value. -/
theorem hessEvalZ_tameSplice_unramified
    {n : ℕ} {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (mu : Generator n → SemiProd C V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hV₂ : ∀ v : V, v+v=0) (htau : mu .tau=1)
    (hwild : ∀ i, (mu (.wild i)).2=1)
    {e : ℕ} (hE : E omega2=(e:ℤ)) (he : e%4=1)
    (R H : PWord (Generator n)) :
    hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ (tameSplice R H) =
      hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ R := by
  rw [tameSplice, hessEvalZ_mul, hessEvalZ_mul, hessEvalZ_inv,
    hessEvalZ_tameShadow_unramified dat hdat mu E E₂ hV₂ htau hwild hE he R,
    hessEvalZ_tameShadow_unramified dat hdat mu E E₂ hV₂ htau hwild hE he H,
    mul_inv_cancel_right]

#print axioms evalZ_tameShadow_of_tau_one_of_wild_pow
#print axioms pow_eq_self_of_pow_four_eq_one
#print axioms hessEvalZ_tameShadow_unramified
#print axioms hessEvalZ_tameSplice_unramified

end
end GQ2.Dyadic
