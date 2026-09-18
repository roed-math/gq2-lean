/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.LHessianCertificates
import GQ2.Dyadic.Instances.GammaLSourceArfGeneral
import GQ2.Dyadic.Instances.WordPhaseHeadProfiles

/-!
# Branch-free original L Hessian records at actual boundary lifts

At q=2^f with f odd, the completed arithmetic source-Arf producer and the
word-independent head profiles discharge every branch premise. The original
record keeps the actual projected graph operator. Its sign is negative exactly
in the unramified sector; the two sectors are not assigned a common sign.
No new Arf, phase, matrix or sector assumption is introduced.
-/

namespace GQ2.Dyadic.Instances.LBoundaryHessianCertificates
noncomputable section
open GQ2 GQ2.SectionEight GQ2.SectionSix
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic Count Certificates Words Words.LSq LSquare
open Instances.WordPhaseOddCertificates Instances.WordPhaseCompactCertificates
open Instances.LHessianCertificates
open Instances.WordPhaseBoundaryMarking Instances.WordPhaseHeadProfiles

/-- A full original Hessian certificate for every actual simple nontrivial L
boundary lift. The literal sign identifies the ramification sector, while every
head and source-Arf premise is discharged internally. -/
theorem lBoundaryHessian
    {h q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e^2=1) (hq0 : q≠0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g, nuTq q (tame g)=nuP (pro2 g))
    (htameSigma : tame (gammaGen (2*h+1) q (lSqW h) .sigma)=tqSigma q)
    (htameTau : tame (gammaGen (2*h+1) q (lSqW h) .tau)=tqTau q)
    (htameWild : ∀ i, tame (gammaGen (2*h+1) q (lSqW h) (.wild i))=1)
    {f : ℕ} (hfodd : Odd f) (hqf : q=2^f)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g•w ∈ W) → W=⊥ ∨ W=⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v≠0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g•v≠v)
    (m : ℕ) (hm : 1≤m)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod=2^(2*m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l≠(SectionNine.blockFrame T Blk hE2).zeroDR)
    (rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
      (SectionNine.blockFrame T Blk hE2).TC) :
    letI := blockPS_commGroup Blk
    letI := SectionNine.headAct T Blk
    letI := SectionNine.hvAct T Blk
    let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
    letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
    let rhoL := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
      (sourceBoundaryMapK tame pro2 compat) F
      ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho
    letI := scalarActionZmodTwo ((gamma h q : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
      (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
    letI := sourceQuotientModule DD rhoL
    ∃ certificate : SourceOddHessian DD rhoL (scalarActionZmodTwo_triv _)
      (headOperator (DD := DD) rhoL (SectionNine.blockProjF T Blk))
      (headOperator_twoPower (DD := DD) rhoL (SectionNine.blockProjF T Blk)) h,
      (certificate.affinePhase.baseSign=-1 ↔
        ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q)•v=v) ∧
      (certificate.affinePhase.baseSign=1 ↔
        ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q)•v≠v) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  classical
  let b := sourceBoundaryMapK tame pro2 compat
  let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
  let DD := En.descData l hl
  have hl' : l.1≠Blk.frattiniK := fun heq ↦ hl (Subtype.ext heq)
  let rhoL := rhoPrimeK (SectionNine.blockFrame T Blk hE2) b F (En.radData l hl) rfl rho
  letI : TopologicalSpace DD.C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  letI : DiscreteTopology DD.C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  letI : TopologicalSpace DD.Vmod := ⊥
  letI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction (SectionNine.blockFrame T Blk hE2).YC DD.Vmod := blockActV Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
  letI : DistribMulAction ((gamma h q : ProfiniteGrp) : Type) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul ((gamma h q : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let theta := Count.rho0Continuous DD rhoL
  letI : DistribMulAction ((gamma h q : ProfiniteGrp) : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod theta.toMonoidHom
  haveI : ContinuousSMul ((gamma h q : ProfiniteGrp) : Type) DD.Vmod := by
    constructor
    have hfac : (fun p : ((gamma h q : Type)) × DD.Vmod ↦ p.1•p.2) =
        (fun p : DD.C0 × DD.Vmod ↦ p.1•p.2) ∘ (fun p ↦ (theta p.1,p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod), g•v=rho0 DD rhoL g•v :=
    fun _ _ ↦ rfl
  have hround : ∀ g : (gamma h q : Type), rho0 DD rhoL g=rho.1.1 g :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hsimpleGamma : IsSimpleModTwo (gamma h q : Type) DD.Vmod := by
    obtain ⟨v,hv⟩ := hVne
    refine ⟨nontrivial_of_ne v 0 hv, ?_⟩
    intro W hW
    have hsimpleDD : ∀ W : AddSubgroup DD.Vmod,
        (∀ c : DD.C0, ∀ w ∈ W, c•w ∈ W) → W=⊥ ∨ W=⊤ := hsimple
    apply hsimpleDD W
    intro c w hw
    obtain ⟨g,hg⟩ := rho.1.2 c
    have H := hW g w hw
    rw [hcompat, hround, hg] at H
    exact H
  have hmark := projectedHead_marking T Blk hE2 hq0 hqe F tame pro2 compat l hl rho
    (gammaGen (2*h+1) q (lSqW h)) htameSigma htameTau htameWild
  have hsigmaHead : SectionNine.blockProjF T Blk
      (rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) .sigma))=hvSigmaK T Blk F := hmark.1
  have htauHead : SectionNine.blockProjF T Blk
      (rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) .tau))=hvTauK T Blk F := hmark.2.1
  have hwildHead : ∀ i, SectionNine.blockProjF T Blk
      (rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) (.wild i)))=1 := hmark.2.2
  have hwildTwo : IsWildTwo (wildAlphabet (2*h+1))
      (fun i ↦ Count.rho0Continuous DD rhoL (gammaGen (2*h+1) q (lSqW h) i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoL)
      (rho0Continuous_surjective DD rhoL
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc•v=SectionNine.blockProjF T Blk cc•v :=
    SectionNine.blockProjF_compat T Blk
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule
    (fun v => (two_nsmul v).trans (Vmod_exp2 DD v))
  letI := sourceQuotientModule DD rhoL
  let base : FactorSet (SectionNine.HVq T Blk) DD.Vmod :=
    blockDatHVK T Blk hq0 hqe F l hl'
  have hbase : IsEquivariantFactorSet DD.qbar base :=
    blockDatHV_specK T Blk hq0 hqe F l hl'
  have hf : ∀ a b : DD.Vmod, DD.dat.f a b=base.f a b := fun _ _ ↦ rfl
  have hmu : ∀ (cc : DD.C0) (v : DD.Vmod),
      DD.dat.m cc v=base.m (SectionNine.blockProjF T Blk cc) v := fun _ _ ↦ rfl
  by_cases hunram : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q)•v=v
  · have htauOne : SectionNine.blockProjF T Blk
        (rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) .tau))=1 :=
      htauHead.trans (head_cyclic_of_unramified T Blk F hunram).1
    have hsigmaFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk
        (rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) .sigma))•v=v → v=0 := by
      intro v hv
      apply head_sigma_fixedPointFree T Blk hE2 hq0 hqe F hnt hunram v
      rwa [hsigmaHead] at hv
    let G : LUnramifiedHeadData rhoL (SectionNine.blockProjF T Blk) :=
      { tau_head := htauOne, wild_head := hwildHead,
        sigma_fixedPointFree := hsigmaFpf, wildTwo := hwildTwo }
    refine ⟨unramifiedHessian (DD := DD) rhoL base hbase
      (SectionNine.blockProjF T Blk) hpi hf hmu
      hcompat hsimpleGamma hqe m hm hcard G, ?_⟩
    have hsign := unramifiedHessian_baseSign (DD := DD) rhoL base hbase
      (SectionNine.blockProjF T Blk) hpi hf hmu
      hcompat hsimpleGamma hqe m hm hcard G
    refine ⟨⟨fun _ => hunram, fun _ => hsign⟩, ?_⟩
    constructor
    · intro H
      rw [hsign] at H
      norm_num at H
    · rintro ⟨v,hv⟩
      exact (hv (hunram v)).elim
  · have hram : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q)•v≠v :=
      not_forall.mp hunram
    have hprof := head_tau_ramified_profile T Blk hq0 hqe F hram
    have htauFpf : ∀ v : DD.Vmod,
        rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) .tau)•v=v → v=0 := by
      intro v hv
      apply hprof.2.2 v
      rwa [hpi, htauHead] at hv
    have htauOmega : ∀ v : DD.Vmod,
        powOmega2 (rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) .tau))•v=v := by
      intro v
      let pi : DD.C0 →* SectionNine.HVq T Blk := SectionNine.blockProjF T Blk
      have hp : pi (powOmega2 (rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) .tau)))=1 := by
        rw [powOmega2_map pi]
        change powOmega2 (SectionNine.blockProjF T Blk
          (rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) .tau)))=1
        rw [htauHead, hprof.2.1]
      calc
        _ = pi (powOmega2 (rho0 DD rhoL (gammaGen (2*h+1) q (lSqW h) .tau)))•v := hpi _ _
        _ = v := by rw [hp, one_smul]
    let G : LRamifiedHeadData rhoL (SectionNine.blockProjF T Blk) :=
      { wild_head := hwildHead, tau_fixedPointFree := htauFpf, tau_oddPart_fixed := htauOmega }
    let S := lRamifiedSourceArf_blockK T Blk hE2 hq0 hqe F tame pro2 compat
      htameSigma htameTau htameWild hfodd hqf m hcard l hl hram rho
    refine ⟨ramifiedHessian (DD := DD) rhoL base hbase
      (SectionNine.blockProjF T Blk) hpi hf hmu
      hcompat hqe m hcard G S, ?_⟩
    have hsign := ramifiedHessian_baseSign (DD := DD) rhoL base hbase
      (SectionNine.blockProjF T Blk) hpi hf hmu hcompat hqe m hcard G S
    refine ⟨?_, ⟨fun _ => hram, fun _ => hsign⟩⟩
    constructor
    · intro H
      rw [hsign] at H
      norm_num at H
    · exact fun H => (hunram H).elim

#print axioms lBoundaryHessian

end
end GQ2.Dyadic.Instances.LBoundaryHessianCertificates
