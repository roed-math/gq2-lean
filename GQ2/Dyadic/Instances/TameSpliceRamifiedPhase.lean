/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameShadowHessianRamified
import GQ2.Dyadic.HessianPinnedResolverTransport
import GQ2.Dyadic.Instances.TameSpliceRamifiedSupply
import GQ2.Dyadic.Instances.WordPhaseCompactMHandleComparison
import GQ2.Dyadic.Instances.GammaRUniformProjectedPhaseSeam

/-!
# Ramified extraspecial phase for an arbitrary structural tame splice

The calculation uses the actual projected head and the full factor-set central
extension. A surjective original graph target supplies every pinned exponent;
no unresolved power, diagonal charge, or source equivalence is assumed.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.SectionEight GQ2.SectionSix
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open Count Words Certificates LSquare
open Instances.WordPhase Instances.WordPhaseModel Instances.WordPhaseSeam
open Instances.WordPhaseCompactMHandleData Instances.WordPhaseCompactMData
open Certificates.MProcyclic

theorem hessRelZ_tameSplice_mCompact_ramified_pinned
    {L0 C V : Type} [Group L0] [Finite L0] [Group C] [Finite C]
    [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (phi : L0 →* SemiProd C V) (hphi : Function.Surjective phi)
    (hV2 : ∀ v : V, v+v=0) {alpha h q : ℕ} (hq0 : q≠0) (hqe : Even q)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u•v=v → v=0)
    (R : PWord (Generator (2+2*h))) (hspecR : TameSpec.TameSpecializes (2+2*h) q R)
    (hendR : IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4*Monoid.exponent L0))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent L0)) (gammaFam (2+2*h) q R k)))
    (p : (V×V) × (Fin h → V×V)) :
    hessRelZ (Certificates.hessMark s u
      (fun i : Fin (2+2*h+1) ↦ wPmCompactPhaseNormal h p (.wild i)))
      (kappa0Cocycle dat hdat)
      (omegaPinnedLevelZhatResolver (4*Monoid.exponent L0))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent L0))
      (tameSplice R (Words.MCompact.mCompactW alpha h)) =
      wPcMRamifiedHandlePhase q0 h p := by
  letI : Finite (SemiProd C V) := inferInstanceAs (Finite (V×C))
  let E := omegaPinnedLevelZhatResolver (4*Monoid.exponent L0)
  let E₂ := omegaPinnedLevelZtwoResolver (4*Monoid.exponent L0)
  have hendH : IsStokesEndpoint (fun k ↦ heisToFree E E₂
      (gammaFam (2+2*h) q (Words.MCompact.mCompactW alpha h) k)) := by
    change IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4*Monoid.exponent L0))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent L0))
      (gammaFam (2+2*h) q (Words.MCompact.mCompactW alpha h) k))
    rw [mCompact_pinned_family_eq_level]
    exact Certificates.MCompact.mCompact_isStokesEndpoint hqe
      (odd_omega2Exp (fourMulExponent_ne_zero_and_even L0).1
        (fourMulExponent_ne_zero_and_even L0).2)
  have H := hessEvalZ_tameSplice_ramified dat hdat
    (Certificates.hessMark s u
      (fun i : Fin (2+2*h+1) ↦ wPmCompactPhaseNormal h p (.wild i))) E E₂
    R (Words.MCompact.mCompactW alpha h)
    (omegaPinnedLevelZhatResolver_wordLift_of_surjective phi hphi)
    (fun _ ↦ rfl) hVu (fun v ↦ by change powOmega2 u • v=v; rw [powOmega2_eq_one_of_odd hu, one_smul])
    hendR hendH hspecR (tameSpecializes_mCompact hq0 hqe alpha h)
    (fun a ↦ resolvedAt_omegaPinnedLevelResolvers_centExt_of_surjective phi hphi
      (kappa0Cocycle dat hdat) _ R)
    (fun a ↦ resolvedAt_omegaPinnedLevelResolvers_centExt_of_surjective phi hphi
      (kappa0Cocycle dat hdat) _ (Words.MCompact.mCompactW alpha h))
  change (hessEvalZ _ _ E E₂ _).fib = _
  rw [H]
  exact wPcM_hessRelZ_eq_ramifiedHandlePhase dat hdat hV2 s u hu hVu p E E₂
    (omegaPinnedLevelZhatResolver_centExt_of_surjective phi hphi _)

#print axioms hessRelZ_tameSplice_mCompact_ramified_pinned

end
end GQ2.Dyadic

