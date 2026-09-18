/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameShadowUnramified

/-!
# The literal tau column of an unramified tame splice

On a cochain supported only at tau, every tame-shadow jet vanishes. The base action is
still that of the original word. If the actual spliced relator dies, the remaining prefix
action is trivial, so the splice has exactly its compact template's tau column. This is a
full first-jet computation, not an inference from equality of kernels.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH

variable {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- Tau-only offsets disappear from each shadow generator, including its central charge. -/
theorem heisEvalZ_tameShadowSubst_tauOnly
    {n : ℕ} (t : Marking n C) (a : A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA2 : ∀ b : A, b+b=0)
    (hwild : ∀ (i : Fin (n+1)) (b : A), t.x i • b=b)
    (htau : ∀ b : A, t.τ • b=b)
    {e : ℕ} (hE : E omega2=(e : ℤ)) (he : e%4=1)
    (g : Generator n) :
    HeisActionEq
      (heisEvalZ ⇑t (Pi.single .tau a) 0 E E₂ (tameShadowSubst g))
      (heisPure (A := A) (t g)) := by
  cases g with
  | sigma =>
      change HeisActionEq (heisGen ⇑t (Pi.single .tau a) 0 .sigma) (heisPure t.σ)
      have hh : heisGen ⇑t (Pi.single .tau a) 0 .sigma = heisPure t.σ := by
        simp [heisGen, heisPure]
      rw [hh]
      exact HeisActionEq.refl _
  | tau =>
      exact ⟨rfl, rfl, rfl, fun b => (one_smul C b).trans (htau b).symm⟩
  | wild i =>
      let X := heisGen ⇑t (Pi.single .tau a) 0 (.wild i)
      let T := heisGen ⇑t (Pi.single .tau a) 0 .tau
      have hXT : ∀ b : A, (X*T).g • b=b := by
        intro b
        change (t.x i*t.τ) • b=b
        rw [mul_smul, htau, hwild]
      have hT : ∀ b : A, T.g • b=b := htau
      have hpow := (heisActionEq_pow_of_mod_four (X*T) hA2 hXT he).mul
        (heisActionEq_pow_of_mod_four T hA2 hT he).inv
      change HeisActionEq ((X*T)^(E omega2) * (T^(E omega2))⁻¹) _
      rw [hE, zpow_natCast, zpow_natCast]
      have hX : X = heisPure (t.x i) := by
        simp [X, heisPure]
      simpa only [mul_inv_cancel_right, hX, Marking.x] using hpow

/-- The entire shadow has zero tau-only jets and the original word's base action. -/
theorem heisEvalZ_tameShadow_tauOnly
    {n : ℕ} (t : Marking n C) (a : A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA2 : ∀ b : A, b+b=0)
    (hwild : ∀ (i : Fin (n+1)) (b : A), t.x i • b=b)
    (htau : ∀ b : A, t.τ • b=b)
    {e : ℕ} (hE : E omega2=(e : ℤ)) (he : e%4=1)
    (R : PWord (Generator n)) :
    HeisActionEq
      (heisEvalZ ⇑t (Pi.single .tau a) 0 E E₂ (tameShadow R))
      (heisPure (A := A) (PWord.evalZ ⇑t E E₂ R)) := by
  change HeisActionEq
    (PWord.evalZ (heisGen ⇑t (Pi.single .tau a) 0) E E₂
      (PWord.subst tameShadowSubst R)) _
  rw [PWord.evalZ_subst]
  have H := HeisActionEq.evalZ _ (fun g => heisPure (A := A) (t g)) E E₂
    (heisEvalZ_tameShadowSubst_tauOnly t a E E₂ hA2 hwild htau hE he) R
  rw [← PWord.map_evalZ (heisPure (A := A)) ⇑t E E₂ R] at H
  exact H

/-- The actual spliced word has precisely the template's tau column. Only the actual
changed relator is required to die; neither raw word is assumed to die. -/
theorem heisEvalZ_tameSplice_tauOnly
    {n : ℕ} (t : Marking n C) (a : A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA2 : ∀ b : A, b+b=0)
    (hwild : ∀ (i : Fin (n+1)) (b : A), t.x i • b=b)
    (htau : ∀ b : A, t.τ • b=b)
    {e : ℕ} (hE : E omega2=(e : ℤ)) (he : e%4=1)
    (R H : PWord (Generator n))
    (hr : PWord.evalZ ⇑t E E₂ (tameSplice R H)=1) :
    (heisEvalZ ⇑t (Pi.single .tau a) 0 E E₂ (tameSplice R H)).a =
      (heisEvalZ ⇑t (Pi.single .tau a) 0 E E₂ H).a := by
  let p := heisEvalZ ⇑t (Pi.single .tau a) 0 E E₂ (tameShadow R)
  let b := heisEvalZ ⇑t (Pi.single .tau a) 0 E E₂ H
  let c := heisEvalZ ⇑t (Pi.single .tau a) 0 E E₂ (tameShadow H)
  have hp := heisEvalZ_tameShadow_tauOnly t a E E₂ hA2 hwild htau hE he R
  have hc := heisEvalZ_tameShadow_tauOnly t a E E₂ hA2 hwild htau hE he H
  have hp0 : p.a=0 := hp.1
  have hc0 : c.a=0 := hc.1
  have hact : ∀ v : A, c.g • v = b.g • v := by
    intro v
    exact (hc.2.2.2 v).trans (by rw [heisPure_g, ← heisEvalZ_g ⇑t (Pi.single .tau a) 0 E E₂ H])
  have hbase : (p*b*c⁻¹).g=1 := by
    change (heisEvalZ ⇑t (Pi.single .tau a) 0 E E₂ (tameSplice R H)).g=1
    rw [heisEvalZ_g, hr]
  have hpa : ∀ v : A, p.g • v=v := by
    intro v
    have hv := congrArg (fun g : C => g • v) hbase
    simp only [HeisLift.mul_g, HeisLift.inv_g, mul_smul, one_smul] at hv
    rw [← hact, smul_inv_smul] at hv
    exact hv
  change (p*b*c⁻¹).a=b.a
  simp only [HeisLift.mul_a, HeisLift.inv_a, hp0, hc0, smul_zero, neg_zero,
    add_zero, zero_add, hpa]

#print axioms heisEvalZ_tameShadowSubst_tauOnly
#print axioms heisEvalZ_tameShadow_tauOnly
#print axioms heisEvalZ_tameSplice_tauOnly

end
end GQ2.Dyadic
