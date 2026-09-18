/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameShadowHessian
import GQ2.Dyadic.HessianPinnedResolverTransport
import GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize

/-!
# Normalized-head and tame-correction invariance of the quadratic phase

These equalities hold in the full factor-set central extension. The head offset
is zero, its resolved 2-primary powers are one, and the complete tame lift is one.
No action-image replacement or unproved vanishing of a central charge is used.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.SectionSix Count
open Instances.GammaRCorePresentationNuNormalize

theorem evalZ_wildShearBackward_of_head_powers_one
    {n : ℕ} {G : Type*} [Group G] (p : Generator n → G)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (k : Fin (n+1) → ℤ_[2])
    (hs : ∀ i, p .sigma ^ E (padicOmega2 (k i))=1)
    (R : PWord (Generator n)) :
    PWord.evalZ p E E₂ (PWord.subst (wildShearNielsen k).backward R) =
      PWord.evalZ p E E₂ R := by
  rw [PWord.evalZ_subst]
  congr 1
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      change p (.wild i)*p .sigma ^ E (padicOmega2 (k i))=p (.wild i)
      rw [hs, mul_one]

theorem hessEvalZ_wildShearBackward_of_sigma_normal
    {n : ℕ} {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (mu : Generator n → SemiProd C V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (k : Fin (n+1) → ℤ_[2]) (hsigma : (mu .sigma).1=0)
    (hs : ∀ i, (mu .sigma).2 ^ E (padicOmega2 (k i))=1)
    (R : PWord (Generator n)) :
    hessEvalZ mu (kappa0Cocycle dat hdat) E E₂
      (PWord.subst (wildShearNielsen k).backward R) =
      hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ R := by
  apply evalZ_wildShearBackward_of_head_powers_one
  intro i
  have hp : WordCoh.lift mu (kappa0Cocycle dat hdat) .sigma =
      hessLineHom dat hdat (mu .sigma).2 := by
    apply WordCoh.CentExt.ext
    · exact Prod.ext hsigma rfl
    · rfl
  rw [hp, ← map_zpow, hs, map_one]

theorem hessEvalZ_tauCorrection_of_tau_one
    {n : ℕ} {L : Type} [Group L]
    (mu : Generator n → L) (c : WordCoh.TwoCocycle L)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (htau : mu .tau=1) (z : Zhat) (R : PWord (Generator n)) :
    hessEvalZ mu c E E₂ (.mul R (.inv (.profPow (.gen .tau) z))) =
      hessEvalZ mu c E E₂ R := by
  have ht : WordCoh.lift mu c .tau=1 := by
    apply WordCoh.CentExt.ext
    · exact htau
    · rfl
  change PWord.evalZ (WordCoh.lift mu c) E E₂ _=PWord.evalZ (WordCoh.lift mu c) E E₂ R
  simp only [PWord.evalZ_mul, PWord.evalZ_inv, PWord.evalZ_profPow, PWord.evalZ_gen,
    ht, one_zpow, inv_one, mul_one]

theorem zpow_resolved_padicOmega2_eq_one
    {C : Type} [Group C] [Finite C] [TopologicalSpace C] [DiscreteTopology C]
    (s : C) (E : Zhat → ℤ) (hs : powOmega2 s=1)
    (hres : ∀ z : ℤ_[2], s ^ E (padicOmega2 z)=s ^ᶻ padicOmega2 z) (z : ℤ_[2]) :
    s ^ E (padicOmega2 z)=1 := by
  rw [hres, zpowHat_padicOmega2, padicOmega2Exp, mul_comm, pow_mul]
  change powOmega2 s ^ _=1
  rw [hs, one_pow]

/-- Odd projected heads have trivial resolved 2-primary powers at the original graph level. -/
theorem zpow_padicOmega2_pinned_eq_one_of_surjective_of_odd
    {L0 C : Type} [Group L0] [Finite L0] [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    (phi : L0 →* C) (hphi : Function.Surjective phi)
    (s : C) (hs : Odd (orderOf s)) (z : ℤ_[2]) :
    s ^ omegaPinnedLevelZhatResolver (4*Monoid.exponent L0) (padicOmega2 z)=1 := by
  apply zpow_resolved_padicOmega2_eq_one s _ (powOmega2_eq_one_of_odd hs)
  intro a
  exact omegaPinnedLevelZhatResolver_spec (fourMulExponent_ne_zero_and_even L0).1
    (fun p ↦ ((Monoid.order_dvd_exponent p).trans (MonoidHom.exponent_dvd hphi)).trans
      ⟨4, by ring⟩) (padicOmega2 a) s

#print axioms evalZ_wildShearBackward_of_head_powers_one
#print axioms hessEvalZ_wildShearBackward_of_sigma_normal
#print axioms hessEvalZ_tauCorrection_of_tau_one
#print axioms zpow_resolved_padicOmega2_eq_one
#print axioms zpow_padicOmega2_pinned_eq_one_of_surjective_of_odd

end
end GQ2.Dyadic
