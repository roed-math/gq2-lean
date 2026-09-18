/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaNormalKernelTransport
import GQ2.Dyadic.TameShadowUnramified
import GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize

/-!
# The complete unramified normalization, correction, and splice comparison

All Heisenberg coordinates agree on sigma=tau=0. Only trivial ACTION of the
resolved sigma powers is needed here; this statement does not descend a quadratic
factor set. The kernel theorem uses actual relator death on both sides.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH Count Certificates
open Instances.GammaRCorePresentationNuNormalize

variable {n : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- Wild normalization is invisible on sigma-normal Heisenberg cochains. -/
theorem heisEvalZ_wildShearBackward_sigma_normal
    (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (k : Fin (n+1) → ℤ_[2])
    (hx : x .sigma=0) (hy : y .sigma=0)
    (hs : ∀ (i : Fin (n+1)) (a : A), t.σ ^ E (padicOmega2 (k i)) • a=a)
    (R : PWord (Generator n)) :
    HeisActionEq
      (heisEvalZ ⇑t x y E E₂ (PWord.subst (wildShearNielsen k).backward R))
      (heisEvalZ ⇑t x y E E₂ R) := by
  change HeisActionEq (PWord.evalZ (heisGen ⇑t x y) E E₂ _) _
  rw [PWord.evalZ_subst]
  apply HeisActionEq.evalZ
  intro g
  cases g with
  | sigma => exact HeisActionEq.refl _
  | tau => exact HeisActionEq.refl _
  | wild i =>
      change HeisActionEq (heisGen ⇑t x y (.wild i) *
        heisGen ⇑t x y .sigma ^ E (padicOmega2 (k i))) (heisGen ⇑t x y (.wild i))
      have hp : heisGen ⇑t x y .sigma=heisPure t.σ := by
        apply HeisLift.ext <;> simp [heisGen, hx, hy, heisPure]
      rw [hp, ← map_zpow]
      have hh : HeisActionEq (heisPure (A := A) (t.σ ^ E (padicOmega2 (k i)))) 1 :=
        ⟨rfl, rfl, rfl, fun a ↦ (hs i a).trans (one_smul C a).symm⟩
      simpa only [mul_one] using (HeisActionEq.refl (heisGen ⇑t x y (.wild i))).mul hh

/-- Arbitrary tame correction is invisible on tau-normal Heisenberg cochains. -/
theorem heisEvalZ_tauCorrection_tau_normal
    (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hx : x .tau=0) (hy : y .tau=0) (htau : ∀ a : A, t.τ • a=a)
    (z : Zhat) (R : PWord (Generator n)) :
    HeisActionEq (heisEvalZ ⇑t x y E E₂ (.mul R (.inv (.profPow (.gen .tau) z))))
      (heisEvalZ ⇑t x y E E₂ R) := by
  have hh : HeisActionEq (heisGen ⇑t x y .tau) 1 :=
    ⟨hx, hy, rfl, fun a ↦ (htau a).trans (one_smul C a).symm⟩
  have H := (HeisActionEq.refl (heisEvalZ ⇑t x y E E₂ R)).mul (hh.zpow (E z)).inv
  simpa only [heisEvalZ_mul, heisEvalZ_inv, heisEvalZ_profPow, heisEvalZ_gen,
    heisGen, one_zpow, inv_one, mul_one] using H

/-- The entire source construction preserves normalized Heisenberg coordinates. -/
theorem heisEvalZ_normalizedCorrectedSplice_unramified
    (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (k : Fin (n+1) → ℤ_[2])
    (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (n+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hxσ : x .sigma=0) (hyσ : y .sigma=0) (hxτ : x .tau=0) (hyτ : y .tau=0)
    (hs : ∀ (i : Fin (n+1)) (a : A), t.σ ^ E (padicOmega2 (k i)) • a=a)
    {e : ℕ} (hE : E omega2=(e : ℤ)) (he : e%4=1)
    (z : Zhat) (R H : PWord (Generator n)) :
    HeisActionEq (heisEvalZ ⇑t x y E E₂ (tameSplice
      (.mul (PWord.subst (wildShearNielsen k).backward R)
        (.inv (.profPow (.gen .tau) z))) H)) (heisEvalZ ⇑t x y E E₂ R) :=
  (heisEvalZ_tameSplice_unramified t x y E E₂ hA₂ hwild htau hxτ hyτ hE he _ H).trans
    ((heisEvalZ_tauCorrection_tau_normal t x y E E₂ hxτ hyτ htau z _).trans
      (heisEvalZ_wildShearBackward_sigma_normal t x y E E₂ k hxσ hyσ hs R))

/-- The changed source and raw source have exactly the same unramified cocycles. -/
theorem kernel_iff_normalizedCorrectedSplice_unramified_of_square
    [Finite A] {q : ℕ}
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (k : Fin (n+1) → ℤ_[2])
    (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (n+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a) (hq : Even q)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hs : ∀ (i : Fin (n+1)) (a : A), t.σ ^ E (padicOmega2 (k i)) • a=a)
    {e : ℕ} (hE : E omega2=(e : ℤ)) (he : e%4=1)
    (z : Zhat) (R H : PWord (Generator n))
    (hsq : ∀ a : A, heisD1 ⇑t (fun l ↦ heisToFree E E₂ (gammaFam n q R l))
      (heisD0 ⇑t a)=0)
    (hr' : ∀ l, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam n q
      (tameSplice (.mul (PWord.subst (wildShearNielsen k).backward R)
        (.inv (.profPow (.gen .tau) z))) H) l))=1)
    (x : Generator n → A) :
    heisD1 ⇑t (fun l ↦ heisToFree E E₂ (gammaFam n q
      (tameSplice (.mul (PWord.subst (wildShearNielsen k).backward R)
        (.inv (.profPow (.gen .tau) z))) H) l)) x=0 ↔
      heisD1 ⇑t (fun l ↦ heisToFree E E₂ (gammaFam n q R l)) x=0 := by
  apply heisD1_gammaFam_kernel_iff_of_sigma_tau_normal_of_square t E E₂ hA₂ htau hq hsigma
    _ R (heisD1_comp_heisD0 ⇑t _ hr') hsq
  intro y hyσ hyτ
  exact (heisEvalZ_normalizedCorrectedSplice_unramified t y 0 E E₂ k hA₂ hwild htau
    hyσ rfl hyτ rfl hs hE he z R H).1

#print axioms heisEvalZ_wildShearBackward_sigma_normal
#print axioms heisEvalZ_tauCorrection_tau_normal
#print axioms heisEvalZ_normalizedCorrectedSplice_unramified
#print axioms kernel_iff_normalizedCorrectedSplice_unramified_of_square

end
end GQ2.Dyadic
