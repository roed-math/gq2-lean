/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairPhase
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
import GQ2.Dyadic.TameHessianNormalization

/-!
# The normalized, corrected pair-splice quadratic phase

On a tame-normal unramified cochain, the shadow splice, tame correction and wild
shear disappear in the full central extension. The raw pair calculation then
supplies the compact wall phase in every handle rank.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairSplicePhase
noncomputable section
open GQ2 GQ2.SectionSix GQ2.Dyadic Count MarkedCore Certificates
open Instances.EvenMHeadHandlePairPhase Instances.EvenMHeadHandlePairSpliceSupply
open Instances.EvenMHeadHandlePairNormalize Instances.EvenMHeadHandlePairSource
open Instances.GammaRCorePresentationNuNormalize
open Instances.WordPhaseModel Instances.WordPhase

theorem hessEvalZ_headHandlePairSplice_normal
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v+v=0) {alpha h q : ℕ}
    (halpha : 1 ≤ alpha) (hα : 2 ≤ alpha) (hq0 : q≠0) (hq : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (s : C) (p : (V×V) × (Fin h → V×V))
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {e : ℕ}
    (hE : E omega2=(e : ℤ)) (he : e%4=1)
    (hs : ∀ z : ℤ_[2], s ^ E (padicOmega2 z)=1) :
    hessEvalZ (Certificates.hessMark s 1
      (fun i : Fin (2+2*h+1) ↦ wPmCompactPhaseNormal h p (.wild i)))
      (kappa0Cocycle dat hdat) E E₂
      (headHandlePairSpliceW alpha h q halpha hq0 hq j nuP) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (wPhCompactWallHandlePhase q0 h p) := by
  unfold headHandlePairSpliceW
  rw [hessEvalZ_tameSplice_unramified dat hdat _ E E₂ hV2 rfl (fun _ ↦ rfl) hE he]
  unfold headHandlePairPrimeCorrectedW tamePrimeToTwoCorrectedWord
  rw [hessEvalZ_tauCorrection_of_tau_one _ _ E E₂ rfl]
  unfold headHandlePairNormalizedW
  rw [hessEvalZ_wildShearBackward_of_sigma_normal dat hdat _ E E₂ _ rfl (fun i ↦ hs _)]
  exact hessEvalZ_headHandlePair_normal dat hdat hV2 hα j s p E E₂ hE he

theorem hessRelZ_headHandlePairSplice_normal
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v+v=0) {alpha h q : ℕ}
    (halpha : 1 ≤ alpha) (hα : 2 ≤ alpha) (hq0 : q≠0) (hq : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (s : C) (p : (V×V) × (Fin h → V×V))
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {e : ℕ}
    (hE : E omega2=(e : ℤ)) (he : e%4=1)
    (hs : ∀ z : ℤ_[2], s ^ E (padicOmega2 z)=1) :
    hessRelZ (Certificates.hessMark s 1
      (fun i : Fin (2+2*h+1) ↦ wPmCompactPhaseNormal h p (.wild i)))
      (kappa0Cocycle dat hdat) E E₂
      (headHandlePairSpliceW alpha h q halpha hq0 hq j nuP) =
      wPhCompactWallHandlePhase q0 h p := by
  rw [hessRelZ, hessEvalZ_headHandlePairSplice_normal dat hdat hV2 halpha hα hq0 hq j nuP
    s p E E₂ hE he hs, WordCoh.CentExt.incl_fib]

#print axioms hessEvalZ_headHandlePairSplice_normal
#print axioms hessRelZ_headHandlePairSplice_normal
end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairSplicePhase

