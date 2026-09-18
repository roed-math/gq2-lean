/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceBoundary
import GQ2.Dyadic.Instances.MpcMobileSpliceBoundary
import GQ2.Dyadic.Instances.TameSpliceHessianCertificates

/-!
# Original pair/mobile Hessian records at every actual boundary lift

The established boundary descent and head-profile proofs are retained, but the
conclusion now keeps the original Hessian record, including its linear change of
coordinates and full affine-phase field. No new sector, matrix, phase, or Gauss
premise is added. Both changed source words and the original boundary maps remain
literal in the result types, uniformly in every source parameter and handle rank.
-/

namespace GQ2.Dyadic.Instances.TameSpliceBoundaryHessianCertificates
noncomputable section
open GQ2.Dyadic.Instances.WordPhaseCompactCertificates
open GQ2.Dyadic.Instances.TameSpliceHessianCertificates
section Pair

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

theorem pairBoundaryHessian
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
      Nonempty (SourceCompactHessian DD rhoM (scalarActionZmodTwo_triv _) h) := by
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
    exact ⟨pairUnramifiedHessian halpha halpha2 hq0 hqe j nuDM rhoM
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
    exact ⟨tameSpliceRamifiedHessian
      (uniformStokesSupply_headHandlePairSplice halpha halpha2 hq0 hqe j nuDM)
      (headHandlePairPrimeCorrectedW_specializes alpha h q halpha hq0 hqe j nuDM)
      hq0 hqe (fun _ hN hNtwo ↦ headHandlePairPrime_pinned_endpoint halpha hq0 hqe j nuDM hN hNtwo)
      rhoM hcompat hwildTwo (blockDatHVK T Blk hq0 hqe F l hl')
      (blockDatHV_specK T Blk hq0 hqe F l hl') (SectionNine.blockProjF T Blk) hpi
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hsemi hwildHead htauOdd htauFpf⟩

end Pair
section Mobile

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.WordPhase GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.MpcMobileNuSource GQ2.Dyadic.Instances.MpcMobileSpliceSupply
open GQ2.Dyadic.Instances.MpcMobileUnramifiedComparison
open GQ2.Dyadic.Instances.WordPhaseBoundaryMarking
open GQ2.Dyadic.Instances.WordPhaseHeadProfiles
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.LSquare GQ2.QuadraticFp2

section Source
variable {alpha r p h q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
  (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
  (nuM : ContinuousMonoidHom (DM alpha h : Type) Ztwo)

local notation "W" => tameSplice
  (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuM) (MCompact.mCompactW alpha h)
local notation "Γ" => GammaR (2 + 2 * h) q W

include halpha2

/-- Every nontrivial simple boundary has the same wall-and-handle phase, including honest
ramified heads. No source normal form or phase identity is left as an input. -/
theorem mobileBoundaryHessian
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom Γ (Tq q)) (pro2 : ContinuousMonoidHom Γ P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 + 2 * h) q W .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 + 2 * h) q W .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1), tame (gammaGen (2 + 2 * h) q W (.wild i)) = 1)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR) :
    ∀ rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
        (SectionNine.blockFrame T Blk hE2).TC,
      let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
      let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
        (sourceBoundaryMapK tame pro2 compat) F
        ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho
      letI := scalarActionZmodTwo (Γ : Type)
      letI : Fintype DD.Vmod := Fintype.ofFinite _
      Nonempty (SourceCompactHessian DD rhoM (scalarActionZmodTwo_triv _) h) := by
  classical
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  set b := sourceBoundaryMapK tame pro2 compat with hb
  set En := blockEnrichmentDK T Blk hE2 hq0 hqe F with hEn
  intro rho
  set DD := En.descData l hl with hDD
  have hl' : l.1 ≠ Blk.frattiniK := fun heq ↦ hl (Subtype.ext heq)
  set rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F (En.radData l hl) rfl rho
    with hrhoM
  letI : TopologicalSpace DD.C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology DD.C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction (SectionNine.blockFrame T Blk hE2).YC DD.Vmod := blockActV Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
  letI : DistribMulAction (Γ : Type) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (Γ : Type) (ZMod 2) := scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction (Γ : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
  haveI : ContinuousSMul (Γ : Type) DD.Vmod := by
    constructor
    have hfac : (fun z : (Γ : Type) × DD.Vmod ↦ z.1 • z.2) =
        (fun z : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ z.1 • z.2) ∘
          (fun z ↦ (rho.1.1 z.1, z.2)) := by funext z; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ g : (Γ : Type), rho0 DD rhoM g = rho.1.1 g :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀ (g : (Γ : Type)) (v : DD.Vmod), g • v = rho0 DD rhoM g • v := by
    intro g v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v) (hround g).symm
  obtain ⟨hsigmaHead, htauHead, hwildHead⟩ := projectedHead_marking T Blk hE2 hq0 hqe F
    tame pro2 compat l hl rho (gammaGen (2 + 2 * h) q W) htameSigma htameTau htameWild
  change SectionNine.blockProjF T Blk (rho0 DD rhoM
    (gammaGen (2 + 2 * h) q W .sigma)) = hvSigmaK T Blk F at hsigmaHead
  change SectionNine.blockProjF T Blk (rho0 DD rhoM
    (gammaGen (2 + 2 * h) q W .tau)) = hvTauK T Blk F at htauHead
  change ∀ i, SectionNine.blockProjF T Blk (rho0 DD rhoM
    (gammaGen (2 + 2 * h) q W (.wild i))) = 1 at hwildHead
  have hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rhoM (gammaGen (2 + 2 * h) q W i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoM)
      (rho0Continuous_surjective DD rhoM
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hblockPiCH : Function.Surjective (SectionNine.blockPiCH T Blk) := by
    intro c
    obtain ⟨y, hy⟩ := T.piY_surjective c
    refine ⟨QuotientGroup.mk' Blk.K y, ?_⟩
    change T.piY y = c
    exact hy
  have hblockProj : Function.Surjective (SectionNine.blockProjF T Blk) :=
    (QuotientGroup.mk'_surjective _).comp hblockPiCH
  have hpi : ∀ (cc : DD.C0) (v : DD.Vmod),
      cc • v = SectionNine.blockProjF T Blk cc • v :=
    fun cc v ↦ SectionNine.blockProjF_compat T Blk cc v
  have hsemi : Function.Surjective (semiProdProjHom (C' := DD.C0) (V := DD.Vmod)
      (SectionNine.blockProjF T Blk) hpi) := by
    intro z
    obtain ⟨c, hc⟩ := hblockProj z.2
    exact ⟨(z.1, c), Prod.ext rfl hc⟩
  by_cases hunram : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
      F.alpha (tqTau q) • v = v
  · have htauOne : SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 + 2 * h) q W .tau)) = 1 :=
      htauHead.trans (head_cyclic_of_unramified T Blk F hunram).1
    have hsigma2 : powOmega2 (SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 + 2 * h) q W .sigma))) = 1 := by
      rw [hsigmaHead]
      exact head_sigma_omega_eq_one T Blk hE2 hq0 hqe F hVne hunram
    have hsigmaFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 + 2 * h) q W .sigma)) • v = v → v = 0 := by
      rw [hsigmaHead]
      exact head_sigma_fixedPointFree T Blk hE2 hq0 hqe F hnt hunram
    exact nonempty_mobileUnramifiedHessian hq0 hqe eta halpha halpha2 nuM rhoM
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hsemi
      hcompat hwildTwo htauOne hwildHead hsigma2 hsigmaFpf
  · have hram : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha (tqTau q) • v ≠ v := not_forall.mp hunram
    obtain ⟨hodd, _, hfpf⟩ := head_tau_ramified_profile T Blk hq0 hqe F hram
    have htauOdd : Odd (orderOf (SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 + 2 * h) q W .tau)))) := by
      rw [htauHead]
      exact hodd
    have htauFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 + 2 * h) q W .tau)) • v = v → v = 0 := by
      rw [htauHead]
      exact hfpf
    exact ⟨tameSpliceRamifiedHessian
      (mpcMobileTameSplice_uniformStokesSupply hq0 hqe eta halpha halpha2 nuM)
      (mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuM) hq0 hqe
      (fun _ hN hNtwo ↦ mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuM hN hNtwo)
      rhoM hcompat hwildTwo
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hsemi
      hwildHead htauOdd htauFpf⟩

end Source
end Mobile
#print axioms pairBoundaryHessian
#print axioms mobileBoundaryHessian
end
end GQ2.Dyadic.Instances.TameSpliceBoundaryHessianCertificates
