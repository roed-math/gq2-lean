/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.SourceBoundaryReplacementRN
import GQ2.Dyadic.SourceTransportRN

/-!
# Transporting a corrected analytic core independently of its boundary

`SourceDataRN.transport` moves an entire corrected source across a continuous source-group
equivalence.  The even-M mobile-normal-form problem needs a weaker operation: move exact
lifting, Stokes duality, scalar counts, and finite generation first, then install a genuinely
new tame/pro-2 boundary on the transported group.

`SourceAnalyticCoreRN.transportGamma` supplies exactly that operation.  The proof is the
boundary-independent part of corrected source transport and is uniform in the degree, word,
pro-2 target, and marking.

`FlexibleModelSourceRN.ofTransportedAnalyticBoundary` is the direct consumer.  It changes the
candidate word/source group and boundary simultaneously.  The construction also makes the
next invariance test possible: when the transported source is still equivalent to the standard
even-M candidate group, its boundary can be pulled back and compared with W341.
-/

namespace GQ2.Dyadic.Instances.SourceBoundaryReplacementRN

noncomputable section

open GQ2 GQ2.SectionEight GQ2.Dyadic
open GQ2.Dyadic.SourceTransport
open GQ2.Dyadic.Instances.SourceBoundaryReplacementRN
open GQ2.Dyadic.Instances.FieldFamilyFlexibleModelAssembly
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

/-- Transport a boundary-independent corrected analytic core across an arbitrary continuous
equivalence of source groups. -/
noncomputable def SourceAnalyticCoreRN.transportGamma
    {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (A : SourceAnalyticCoreRN n q P hP nuP SN) {Gamma' : ProfiniteGrp}
    (e : ContinuousMulEquiv Gamma' A.Γ)
    (smul' : DistribMulAction Gamma' (ZMod 2))
    (hcont' : letI := smul'; ContinuousSMul Gamma' (ZMod 2))
    (htriv' : letI := smul'; ∀ (gamma : Gamma') (m : ZMod 2), gamma • m = m) :
    SourceAnalyticCoreRN n q P hP nuP SN where
  Γ := Gamma'
  smulZmod2 := smul'
  contSMulZmod2 := hcont'
  htriv := htriv'
  tfg := IsTopologicallyFinGen.of_surjective
    (e.symm : ContinuousMonoidHom A.Γ Gamma').toMonoidHom
    (e.symm : ContinuousMonoidHom A.Γ Gamma').continuous_toFun
    e.symm.surjective A.tfg
  exactLifting :=
    ⟨fun RF b₁ F rho₁ => by
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨rho, rfl⟩ := (boundaryLiftsKEquiv e b F RF.TC).surjective rho₁
        exact (Nat.card_congr (liftsOverKEquiv e RF b F rho)).symm.trans
          (A.exactLifting.1 RF b F rho),
      fun Dd hnd rho₁ hrho₁ => by
        obtain ⟨rho, rfl⟩ := (precompEquiv e _).surjective rho₁
        have hrho : Function.Surjective rho := fun y => by
          obtain ⟨a, ha⟩ := hrho₁ y
          exact ⟨e a, ha⟩
        rw [(Nat.card_congr (Equiv.subtypeEquiv (mLiftsEquiv e Dd rho)
            fun f => (mLiftsEquiv_central e Dd rho f).symm)).symm,
          (Nat.card_congr (mLiftsEquiv e Dd rho)).symm]
        exact A.exactLifting.2.1 Dd hnd rho hrho,
      fun hE2 hRK hR2 b₁ F => by
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        simp only [exactImageCountK_comp, mBK_comp]
        exact A.exactLifting.2.2 hE2 hRK hR2 b F⟩
  stokes :=
    ⟨fun b₁ F En l h rho₁ => by
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨rho, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective rho₁
        exact (Nat.card_congr
          (tCocycleEquiv e (rhoPrimeK _ b F (En.radData l h) rfl rho))).symm.trans
          (A.stokes.1 b F En l h rho),
      fun b₁ F En l h Dsc rho₁ c₁ hc => by
        letI := A.smulZmod2
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨rho, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective rho₁
        obtain ⟨c, rfl⟩ := (vCocycleEquiv e (En.descData l h)
          (rhoPrimeK _ b F (En.radData l h) rfl rho)).surjective c₁
        refine (tLiftable_comp (descSigma_spec En l h Dsc) e _ c).mpr
          (A.stokes.2.1 b F En l h Dsc rho c fun chi => ?_)
        exact (betaChi_comp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
          htriv' A.htriv e _ chi c).symm.trans (hc chi),
      fun b₁ F En l h Dsc rho₁ chi hchi => by
        letI := A.smulZmod2
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨rho, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective rho₁
        obtain ⟨c, hcne⟩ := A.stokes.2.2.1 b F En l h Dsc rho chi hchi
        refine ⟨vCocycleEquiv e (En.descData l h) _ c, fun heq => hcne ?_⟩
        have h1 := betaChi_comp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
          htriv' A.htriv e (rhoPrimeK _ b F (En.radData l h) rfl rho) chi c
        have h2 := betaChi_comp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
          htriv' A.htriv e (rhoPrimeK _ b F (En.radData l h) rfl rho) chi 0
        exact h1.symm.trans (heq.trans h2),
      fun b₁ F En l h hsimple hVne hnt rho₁ => by
        obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
        obtain ⟨rho, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective rho₁
        exact (Nat.card_congr (vCocycleEquiv e (En.descData l h)
          (rhoPrimeK _ b F (En.radData l h) rfl rho))).symm.trans
          (A.stokes.2.2.2 b F En l h hsimple hVne hnt rho)⟩
  scalar :=
    ⟨(Nat.card_congr (precompEquiv e (Multiplicative (ZMod 2)))).symm.trans A.scalar.1,
      by
        letI := A.smulZmod2
        exact (card_H2_comp htriv' A.htriv e).trans A.scalar.2⟩

/-- Simultaneously change the candidate word/source group and install a boundary on the
transported analytic core. -/
noncomputable def FlexibleModelSourceRN.ofTransportedAnalyticBoundary
    {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (A : SourceAnalyticCoreRN n q P hP nuP SN)
    (e : ContinuousMulEquiv (GammaR n q R) A.Γ)
    (D : SourceAnalyticBoundaryRN
      (A.transportGamma e (scalarActionZmodTwo (GammaR n q R))
        (scalarActionZmodTwo_continuousSMul (GammaR n q R))
        (scalarActionZmodTwo_triv (GammaR n q R))))
    (hnuP : Function.Surjective nuP)
    (hwild : IsProP 2 D.tame.toMonoidHom.ker) :
    FlexibleModelSourceRN n q R P hP nuP SN :=
  FlexibleModelSourceRN.ofAnalyticBoundary
    (A.transportGamma e (scalarActionZmodTwo (GammaR n q R))
      (scalarActionZmodTwo_continuousSMul (GammaR n q R))
      (scalarActionZmodTwo_triv (GammaR n q R)))
    D (ContinuousMulEquiv.refl _) hnuP hwild

#print axioms SourceAnalyticCoreRN.transportGamma
#print axioms FlexibleModelSourceRN.ofTransportedAnalyticBoundary

end

end GQ2.Dyadic.Instances.SourceBoundaryReplacementRN
