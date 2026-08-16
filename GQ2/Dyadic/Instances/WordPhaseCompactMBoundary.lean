/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactMUnramifiedBoundary
import GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedComparison

/-!
# Branch-free handle-free compact-M boundary data

This file joins the unramified and honest ramified handle-free compact-M comparisons at their
common `plusFormD` endpoint.  In the ramified branch it derives projected tame oddness and
fixed-point-freeness, the source `powOmega2` action needed by the Fox row, and the surjectivity
of the faithful-head semidirect projection directly from the block data.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactMBoundary

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseCompactMData
open GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedData
open GQ2.Dyadic.LSquare

/-- Every handle-free compact-M boundary lift reaches the common plus-form endpoint. -/
theorem wPcMComparison_boundary
    {alpha q : Nat} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (MCompact.gamma alpha 0 q) (Tq q))
    (pro2 : ContinuousMonoidHom (MCompact.gamma alpha 0 q) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau) = tqTau q)
    (htameWild : ∀ i : Fin 3,
      tame (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i)) = 1)
    (halpha : 2 ≤ alpha)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
        W = ⊥ ∨ W = ⊤)
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
      letI := scalarActionZmodTwo ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type)
      letI : Fintype DD.Vmod := Fintype.ofFinite _
      letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
      Nonempty (SourceWordPhaseComparison DD rhoM (scalarActionZmodTwo_triv _)
        (DD.Vmod × DD.Vmod) (plusFormD DD.qbar DD.qbar)) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  classical
  by_cases hunram : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
      F.alpha (tqTau q) • v = v
  · exact wPcMComparison_boundary_unramifiedP1 T Blk hE2 hq0 hqe F tame pro2 compat
      htameSigma htameTau htameWild halpha hsimple hVne hnt hunram l hl
  · have hram : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha (tqTau q) • v ≠ v := by
      simpa only [not_forall] using hunram
    set b := sourceBoundaryMapK tame pro2 compat with hb
    set En := blockEnrichmentDK T Blk hE2 hq0 hqe F with hEn
    intro rho
    set DD := En.descData l hl with hDD
    have hl' : l.1 ≠ Blk.frattiniK := fun heq ↦ hl (Subtype.ext heq)
    set rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F
      (En.radData l hl) rfl rho with hrhoM
    letI : TopologicalSpace DD.C0 :=
      (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
    haveI : DiscreteTopology DD.C0 :=
      (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
    letI : TopologicalSpace DD.Vmod := ⊥
    haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
    letI actYC : DistribMulAction
        (SectionNine.blockFrame T Blk hE2).YC DD.Vmod := blockActV Blk
    letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
    letI : DistribMulAction ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    letI : DistribMulAction ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type) DD.Vmod :=
      DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
    haveI : ContinuousSMul ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type) DD.Vmod := by
      constructor
      have hfac :
          (fun p : ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type) × DD.Vmod ↦ p.1 • p.2) =
            (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
              (fun p ↦ (rho.1.1 p.1, p.2)) := by
        funext p
        rfl
      rw [hfac]
      exact continuous_of_discreteTopology.comp
        ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
    have hround : ∀ gamma : ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type),
        rho0 DD rhoM gamma = rho.1.1 gamma :=
      rho0_descData_rhoPrimeK b F En l hl rho
    have hcompat : ∀ (g : ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type))
        (v : DD.Vmod), g • v = rho0 DD rhoM g • v := by
      intro g v
      exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v) (hround g).symm
    have hheadFac : ∀ gamma : ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type),
        SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) =
          headTameSurjK T Blk F (tame gamma) := by
      intro gamma
      rw [hround gamma]
      exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
        (boundaryLift_headK T Blk hE2 b F rho gamma)
    have htauHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) = hvTauK T Blk F := by
      rw [hheadFac, htameTau]
      rfl
    have hwildHead : ∀ i : Fin 3, SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i))) = 1 := by
      intro i
      rw [hheadFac, htameWild i]
      show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
      rw [map_one, map_one]
    have hwildTwo : IsWildTwo (wildAlphabet 2)
        (fun i ↦ Count.rho0Continuous DD rhoM
          (gammaGen 2 q (MCompact.mCompactW alpha 0) i)) :=
      isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoM)
        (rho0Continuous_surjective DD rhoM
          (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
            (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
    have hrelHV : (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F =
        hvTauK T Blk F ^ q := hv_relK T Blk F
    haveI hnormHV : (Subgroup.zpowers (hvTauK T Blk F)).Normal :=
      tame_zpowers_normal_pow (hv_genK T Blk F) hrelHV
    have hoddHV : Odd (orderOf (hvTauK T Blk F)) :=
      tame_odd_order_pow (orderOf_pos (hvSigmaK T Blk F)).ne' hq0 hqe hrelHV
    have htauHeadFpf : ∀ v : DD.Vmod, hvTauK T Blk F • v = v → v = 0 := by
      intro v hv
      exact tau_fixed_eq_zero_of_zpowers_normal (hvTauK T Blk F) hnormHV
        (SectionNine.hv_simple T Blk) hram v hv
    have hoddProjected : Odd (orderOf (SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)))) := by
      rw [htauHead]
      exact hoddHV
    have htauProjectedFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v = v → v = 0 := by
      intro v hv
      apply htauHeadFpf v
      rwa [htauHead] at hv
    have hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rhoM
        (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v = v := by
      intro v
      have hstep : powOmega2 (rho0 DD rhoM
          (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v =
          SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
            (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau))) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      rw [hstep, powOmega2_map (SectionNine.blockProjF T Blk), htauHead,
        powOmega2_eq_one_of_odd hoddHV, one_smul]
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
    have hsemi : Function.Surjective
        (semiProdProjHom (C' := DD.C0) (V := DD.Vmod)
          (SectionNine.blockProjF T Blk)
          hpi) := by
      intro z
      obtain ⟨c, hc⟩ := hblockProj z.2
      exact ⟨(z.1, c), Prod.ext rfl hc⟩
    refine ⟨?_⟩
    simpa only [rhoM, b, En] using
      (WordPhaseCompactMRamifiedComparison.wPcMComparison_ramifiedHead rhoM
        (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
        (SectionNine.blockProjF T Blk) hpi
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hsemi hcompat (Vmod_exp2 DD) hwildTwo
        hq0 hqe halpha hwildHead hoddProjected htauProjectedFpf hTodd)

/-- The branch-free determinant supply for the handle-free compact-M word. -/
theorem wPcM_branchFreeSupply
    {alpha q : Nat} {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (MCompact.gamma alpha 0 q) (Tq q))
    (pro2 : ContinuousMonoidHom (MCompact.gamma alpha 0 q) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau) = tqTau q)
    (htameWild : ∀ i : Fin 3,
      tame (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i)) = 1)
    (halpha : 2 ≤ alpha) :
    wPhBranchFreeSupply 2 nuP tame pro2 compat := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F
    hsimple hVne hnt m hm hcard l hl rho
  set DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl with hDD
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
  refine ⟨DD.Vmod × DD.Vmod, inferInstance, plusFormD DD.qbar DD.qbar, ?_, ?_⟩
  · simpa only [DD] using
      (wPcMComparison_boundary T Blk hE2 hq0 hqe F tame pro2 compat
        htameSigma htameTau htameWild halpha hsimple hVne hnt l hl rho)
  · have hcard' : Nat.card DD.Vmod = 2 ^ (2 * m) := by
      simpa [DD, blockEnrichmentDK, blockEnrichmentK,
        RecursionFrame.Enrichment.descData, SectionNine.blockFrame,
        blockFrameImpl] using hcard
    rw [gaussSum_plusFormD DD.hquad DD.hquad DD.hns,
      ← Nat.card_eq_fintype_card, hcard']
    rfl

/-! ## Axiom audit -/

#print axioms wPcMComparison_boundary
#print axioms wPcM_branchFreeSupply

end

end GQ2.Dyadic.Instances.WordPhaseCompactMBoundary
