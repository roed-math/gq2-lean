/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramifiedComparison
import GQ2.Dyadic.Instances.TameSpliceRamifiedComparison
import GQ2.Dyadic.Instances.WordPhaseHeadProfiles
import GQ2.Dyadic.Instances.GammaRUniformDeterminant

/-!
# Complete boundary and determinant certificates for the changed pair source

Every boundary lift has an actual faithful head projection. Its unramified or
ramified profile supplies the corresponding proved source-to-phase comparison,
and both give the same compact wall-handle Gauss sum. The result applies to
arbitrary compatible core boundary maps with canonical tame generator images.

The final constructors combine this determinant with uniform Stokes and the
normalized pair core. Their only additional core-row input is the promoted
handle's unit value; no phase, determinant, or class-specific data is assumed.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceBoundary
noncomputable section
open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.WordPhase GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseBoundaryMarking GQ2.Dyadic.Instances.WordPhaseHeadProfiles
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
open GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramifiedComparison
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSplice
open GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize
open GQ2.Dyadic.LSquare GQ2.QuadraticFp2

variable {alpha h q : ℕ} (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
  (hq0 : q≠0) (hqe : Even q) (j : Fin h)
  (nuDM : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
local notation "W" => headHandlePairSpliceW alpha h q halpha hq0 hqe j nuDM
local notation "Γ" => GammaR (2+2*h) q W
include halpha2

theorem headHandlePairSplice_boundaryComparison
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e^2=1) (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom Γ (Tq q)) (pro2 : ContinuousMonoidHom Γ P)
    (compat : ∀ g, nuTq q (tame g)=nuP (pro2 g))
    (htameSigma : tame (gammaGen (2+2*h) q W .sigma)=tqSigma q)
    (htameTau : tame (gammaGen (2+2*h) q W .tau)=tqTau q)
    (htameWild : ∀ i, tame (gammaGen (2+2*h) q W (.wild i))=1)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v≠0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g•v≠v)
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l≠(SectionNine.blockFrame T Blk hE2).zeroDR) :
    ∀ rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
      (SectionNine.blockFrame T Blk hE2).TC,
      let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
      let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
        (sourceBoundaryMapK tame pro2 compat) F
        ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho
      letI := scalarActionZmodTwo (Γ : Type)
      letI : Fintype DD.Vmod := Fintype.ofFinite _
      Nonempty (SourceWordPhaseComparison DD rhoM (scalarActionZmodTwo_triv _)
        ((DD.Vmod×DD.Vmod) × (Fin h → DD.Vmod×DD.Vmod))
        (wPhCompactWallHandlePhase DD.qbar h)) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  classical
  let b := sourceBoundaryMapK tame pro2 compat
  let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
  intro rho
  let DD := En.descData l hl
  have hl' : l.1≠Blk.frattiniK := fun heq ↦ hl (Subtype.ext heq)
  let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F (En.radData l hl) rfl rho
  letI : TopologicalSpace DD.C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  letI : DiscreteTopology DD.C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  letI : TopologicalSpace DD.Vmod := ⊥
  letI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction (SectionNine.blockFrame T Blk hE2).YC DD.Vmod := blockActV Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
  letI : DistribMulAction (Γ : Type) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (Γ : Type) (ZMod 2) := scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction (Γ : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
  haveI : ContinuousSMul (Γ : Type) DD.Vmod := by
    constructor
    have hfac : (fun p : (Γ : Type) × DD.Vmod ↦ p.1•p.2) =
        (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1•p.2) ∘
          (fun p ↦ (rho.1.1 p.1,p.2)) := by funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ g : (Γ : Type), rho0 DD rhoM g=rho.1.1 g :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀ (g : (Γ : Type)) (v : DD.Vmod), g•v=rho0 DD rhoM g•v := by
    intro g v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c•v) (hround g).symm
  have hmark := projectedHead_marking T Blk hE2 hq0 hqe F tame pro2 compat l hl rho
    (gammaGen (2+2*h) q W) htameSigma htameTau htameWild
  have hsigmaHead : SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen (2+2*h) q W .sigma))=hvSigmaK T Blk F := hmark.1
  have htauHead : SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen (2+2*h) q W .tau))=hvTauK T Blk F := hmark.2.1
  have hwildHead : ∀ i, SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen (2+2*h) q W (.wild i)))=1 := hmark.2.2
  have hwildTwo : IsWildTwo (wildAlphabet (2+2*h))
      (fun i ↦ Count.rho0Continuous DD rhoM (gammaGen (2+2*h) q W i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoM)
      (rho0Continuous_surjective DD rhoM
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hblockPiCH : Function.Surjective (SectionNine.blockPiCH T Blk) := by
    intro c
    obtain ⟨y, hy⟩ := T.piY_surjective c
    exact ⟨QuotientGroup.mk' Blk.K y, hy⟩
  have hblockProj : Function.Surjective (SectionNine.blockProjF T Blk) :=
    (QuotientGroup.mk'_surjective _).comp hblockPiCH
  have hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc•v=SectionNine.blockProjF T Blk cc•v :=
    SectionNine.blockProjF_compat T Blk
  have hsemi : Function.Surjective (semiProdProjHom (C' := DD.C0) (V := DD.Vmod)
      (SectionNine.blockProjF T Blk) hpi) := by
    intro z
    obtain ⟨c,hc⟩ := hblockProj z.2
    exact ⟨(z.1,c),Prod.ext rfl hc⟩
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  by_cases hunram : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
      F.alpha (tqTau q)•v=v
  · have htauOne : SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2+2*h) q W .tau))=1 :=
      htauHead.trans (head_cyclic_of_unramified T Blk F hunram).1
    have hsigmaFpf : ∀ v : DD.Vmod,
        rho0 DD rhoM (gammaGen (2+2*h) q W .sigma)•v=v → v=0 := by
      intro v hv
      apply head_sigma_fixedPointFree T Blk hE2 hq0 hqe F hnt hunram v
      rw [hpi, hsigmaHead] at hv
      exact hv
    have hsigmaOmega : powOmega2 (SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2+2*h) q W .sigma)))=1 := by
      rw [hsigmaHead]
      exact head_sigma_omega_eq_one T Blk hE2 hq0 hqe F hVne hunram
    exact ⟨headHandlePairSplice_unramifiedComparison halpha halpha2 hq0 hqe j nuDM rhoM
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hsemi
      hcompat hwildTwo htauOne hwildHead hsigmaFpf hsigmaOmega⟩
  · have hram : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha (tqTau q)•v≠v := by simpa only [not_forall] using hunram
    have hprof := head_tau_ramified_profile T Blk hq0 hqe F hram
    have htauOdd : Odd (orderOf (SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2+2*h) q W .tau)))) := by
      rw [htauHead]
      exact hprof.1
    have htauFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2+2*h) q W .tau))•v=v → v=0 := by
      intro v hv
      rw [htauHead] at hv
      exact hprof.2.2 v hv
    unfold headHandlePairSpliceW at *
    exact ⟨phaseComparison_tameSplice_mCompact_ramified
      (uniformStokesSupply_headHandlePairSplice halpha halpha2 hq0 hqe j nuDM)
      (headHandlePairPrimeCorrectedW_specializes alpha h q halpha hq0 hqe j nuDM)
      hq0 hqe (fun _ hN hNtwo ↦ headHandlePairPrime_pinned_endpoint halpha hq0 hqe j nuDM hN hNtwo)
      rhoM hcompat hwildTwo (blockDatHVK T Blk hq0 hqe F l hl')
      (blockDatHV_specK T Blk hq0 hqe F l hl') (SectionNine.blockProjF T Blk) hpi
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hsemi hwildHead htauOdd htauFpf⟩

theorem headHandlePairSplice_branchFreeSupply
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom Γ (Tq q)) (pro2 : ContinuousMonoidHom Γ P)
    (compat : ∀ g, nuTq q (tame g)=nuP (pro2 g))
    (htameSigma : tame (gammaGen (2+2*h) q W .sigma)=tqSigma q)
    (htameTau : tame (gammaGen (2+2*h) q W .tau)=tqTau q)
    (htameWild : ∀ i, tame (gammaGen (2+2*h) q W (.wild i))=1) :
    wPhBranchFreeSupply (2+2*h) nuP tame pro2 compat := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0' hqe' F
    hsimple hVne hnt m hm hcard l hl rho
  let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  refine ⟨(DD.Vmod×DD.Vmod) × (Fin h → DD.Vmod×DD.Vmod), inferInstance,
    wPhCompactWallHandlePhase DD.qbar h, ?_, ?_⟩
  · exact headHandlePairSplice_boundaryComparison halpha halpha2 hq0 hqe j nuDM
      T Blk hE2 F tame pro2 compat htameSigma htameTau htameWild hVne hnt l hl rho
  · have hcard' : Fintype.card DD.Vmod=2^(2*m) := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    exact (wPh_compactWallHandlePhase_gaussSum_standardRam DD.hquad DD.hns hcard' h).trans
      (congrArg (fun n ↦ (standardNumerics n).gaussRam m) (by omega : 2*h+2=2+2*h))

theorem headHandlePairSplice_determinant
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom Γ (Tq q)) (pro2 : ContinuousMonoidHom Γ P)
    (compat : ∀ g, nuTq q (tame g)=nuP (pro2 g))
    (htameSigma : tame (gammaGen (2+2*h) q W .sigma)=tqSigma q)
    (htameTau : tame (gammaGen (2+2*h) q W .tau)=tqTau q)
    (htameWild : ∀ i, tame (gammaGen (2+2*h) q W (.wild i))=1) :
    AffineDeterminantCertificate Γ (2+2*h) q P nuP (standardNumerics (2+2*h))
      tame pro2 compat (scalarActionZmodTwo _) :=
  (uniformStokesSupply_headHandlePairSplice halpha halpha2 hq0 hqe j nuDM).determinant_of_branchFree
    (by exact even_two.add (even_two.mul_right h)) nuP tame pro2 compat
    (headHandlePairSplice_branchFreeSupply halpha halpha2 hq0 hqe j nuDM nuP tame pro2 compat
      htameSigma htameTau htameWild)

def headHandlePairSplice_flexibleCertificateLeaves
    (hU : nuDM (dmGen alpha h (handleIdxU j))=ztwoOne) :
    Instances.FieldFamilyFlexibleCertificate.FlexibleCertificateLeavesRN (2+2*h) q W
      (DM alpha h) (isProP_DM alpha h) nuDM (standardNumerics (2+2*h)) hq0 hqe := by
  let S := uniformStokesSupply_headHandlePairSplice halpha halpha2 hq0 hqe j nuDM
  let C := flexibleCore_headHandlePairSplice halpha hq0 hqe j nuDM hU
  let hs := headHandlePairSpliceW_specializes halpha hq0 hqe j nuDM
  apply S.certificateLeaves_of_branchFree (by exact even_two.add (even_two.mul_right h))
    hs (isProP_DM alpha h) C hq0 hqe
  apply headHandlePairSplice_branchFreeSupply halpha halpha2 hq0 hqe j nuDM nuDM
  · exact TameSpec.tameOfSpec_gammaGen hs .sigma
  · exact TameSpec.tameOfSpec_gammaGen hs .tau
  · intro i
    exact TameSpec.tameOfSpec_gammaGen hs (.wild i)

def headHandlePairSplice_wordCertificate
    (hU : nuDM (dmGen alpha h (handleIdxU j))=ztwoOne) :
    WordCertificateRN (2+2*h) q W (DM alpha h) (isProP_DM alpha h) nuDM
      (standardNumerics (2+2*h)) :=
  Instances.FieldFamilyFlexibleCertificate.wordCertificateRN_of_flexibleLeaves
    (headHandlePairSplice_flexibleCertificateLeaves halpha halpha2 hq0 hqe j nuDM hU)

#print axioms headHandlePairSplice_boundaryComparison
#print axioms headHandlePairSplice_branchFreeSupply
#print axioms headHandlePairSplice_determinant
#print axioms headHandlePairSplice_flexibleCertificateLeaves
#print axioms headHandlePairSplice_wordCertificate
end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceBoundary

