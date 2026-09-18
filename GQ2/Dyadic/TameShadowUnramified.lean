/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameShadowWord
import GQ2.Dyadic.HeisActionCongruence
import GQ2.Dyadic.Certificates.M0

/-!
# Unramified invariance of tame shadows and splices

When tau and all wild bases act trivially, and the two cochains vanish at tau,
the averaging shadow preserves every first and second Heisenberg coordinate.
The omega resolver class one modulo four is essential: it fixes both first jets
and kills the binomial central term. No condition is imposed on sigma's action
or on either sigma offset.

Consequently a tame splice has exactly R's jets and central charge on these
cochains, for arbitrary words R and H. This is a word-level comparison, not yet
an assertion of the source certificate or of Stokes duality for R.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH

variable {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- A trivial-action lift is unchanged through second order at the honest omega class. -/
theorem heisActionEq_pow_of_mod_four
    (p : HeisLift A C) (hA₂ : ∀ a : A, a+a=0)
    (hp : ∀ a : A, p.g • a = a) {e : ℕ} (he : e % 4 = 1) :
    HeisActionEq (p ^ e) p := by
  rw [heisPow_of_trivial p hp e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Certificates.MCompact.nsmul_self_of_odd hA₂ (odd_of_mod_four_eq_one he) p.a
  · exact Certificates.MCompact.nsmul_self_of_odd ElemDual.add_self_eq_zero
      (odd_of_mod_four_eq_one he) p.l
  · change e • p.z + (e.choose 2) • p.l p.a = p.z
    rw [nsmul_zmod2_odd (odd_of_mod_four_eq_one he),
      nsmul_zmod2_even (choose_two_even_of_mod_four he), add_zero]
  · intro a
    change (p.g ^ e) • a = p.g • a
    rw [hp]
    exact mem_trivAct.mp (pow_mem (mem_trivAct.mpr hp) e) a

/-- Generator-level shadow invariance with zero tau offsets. -/
theorem heisEvalZ_tameShadowSubst_unramified
    {n : ℕ} (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (n+1)) (a : A), t.x i • a = a)
    (htau : ∀ a : A, t.τ • a = a)
    (hxτ : x .tau = 0) (hyτ : y .tau = 0)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (g : Generator n) :
    HeisActionEq (heisEvalZ ⇑t x y E E₂ (tameShadowSubst g)) (heisGen ⇑t x y g) := by
  have hT : HeisActionEq (heisGen ⇑t x y .tau) 1 :=
    ⟨hxτ, hyτ, rfl, fun a ↦ (htau a).trans (one_smul C a).symm⟩
  cases g with
  | sigma => exact HeisActionEq.refl _
  | tau => exact hT.symm
  | wild i =>
      change HeisActionEq
        (((heisGen ⇑t x y (.wild i)) * (heisGen ⇑t x y .tau)) ^ (E omega2) *
          ((heisGen ⇑t x y .tau) ^ (E omega2))⁻¹) (heisGen ⇑t x y (.wild i))
      rw [hE, zpow_natCast, zpow_natCast]
      have H := (((HeisActionEq.refl (heisGen ⇑t x y (.wild i))).mul hT).pow e).mul
        (hT.pow e).inv
      have H' : HeisActionEq
          (((heisGen ⇑t x y (.wild i)) * (heisGen ⇑t x y .tau)) ^ e *
            ((heisGen ⇑t x y .tau) ^ e)⁻¹) ((heisGen ⇑t x y (.wild i)) ^ e) := by
        simpa only [mul_one, one_pow, inv_one] using H
      exact H'.trans (heisActionEq_pow_of_mod_four _ hA₂ (hwild i) he)

/-- The averaging shadow preserves unramified jets and charge for any word. -/
theorem heisEvalZ_tameShadow_unramified
    {n : ℕ} (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (n+1)) (a : A), t.x i • a = a)
    (htau : ∀ a : A, t.τ • a = a)
    (hxτ : x .tau = 0) (hyτ : y .tau = 0)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (R : PWord (Generator n)) :
    HeisActionEq (heisEvalZ ⇑t x y E E₂ (tameShadow R))
      (heisEvalZ ⇑t x y E E₂ R) := by
  change HeisActionEq
    (PWord.evalZ (heisGen ⇑t x y) E E₂ (PWord.subst tameShadowSubst R))
    (PWord.evalZ (heisGen ⇑t x y) E E₂ R)
  rw [PWord.evalZ_subst]
  exact HeisActionEq.evalZ _ _ E E₂
    (heisEvalZ_tameShadowSubst_unramified t x y E E₂ hA₂ hwild htau hxτ hyτ hE he) R

/-- The two H factors cancel through second order in the unramified branch. -/
theorem heisEvalZ_tameSplice_unramified
    {n : ℕ} (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (n+1)) (a : A), t.x i • a = a)
    (htau : ∀ a : A, t.τ • a = a)
    (hxτ : x .tau = 0) (hyτ : y .tau = 0)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (R H : PWord (Generator n)) :
    HeisActionEq (heisEvalZ ⇑t x y E E₂ (tameSplice R H))
      (heisEvalZ ⇑t x y E E₂ R) := by
  have hR := heisEvalZ_tameShadow_unramified t x y E E₂ hA₂ hwild htau hxτ hyτ hE he R
  have hH := heisEvalZ_tameShadow_unramified t x y E E₂ hA₂ hwild htau hxτ hyτ hE he H
  have hh := (hR.mul (HeisActionEq.refl (heisEvalZ ⇑t x y E E₂ H))).mul hH.inv
  simpa only [tameSplice, heisEvalZ_mul, heisEvalZ_inv, mul_inv_cancel_right] using hh

#print axioms heisActionEq_pow_of_mod_four
#print axioms heisEvalZ_tameShadowSubst_unramified
#print axioms heisEvalZ_tameShadow_unramified
#print axioms heisEvalZ_tameSplice_unramified

end
end GQ2.Dyadic

