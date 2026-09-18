/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.CompactNHessianCertificates
import GQ2.Dyadic.Instances.WordPhaseHeadProfiles

/-!
# Branch-free original compact-N Hessian records at actual boundary lifts

The same compact normal target occurs in both head sectors. The public
word-independent boundary marking and head profiles discharge every head premise
of the actual source Hessian producers. The original record retains the actual
source quotient, linear coordinate map and inverse, literal diagonal, quadratic
and nonsingular target, and affine-phase certificate.

The minimal block already supplies simplicity to the head-profile lemmas, so only
the old nontrivial-action premise is needed explicitly. No new phase, sector,
fixed-point-free, dimension, or cardinality assumption is introduced; no old API
or source word is changed. Handle rank is arbitrary, including zero.
-/

namespace GQ2.Dyadic.Instances.CompactNBoundaryHessianCertificates
noncomputable section
open GQ2 GQ2.SectionEight GQ2.SectionSix
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic Count Certificates Words LSquare
open Instances.WordPhase Instances.WordPhaseModel
open Instances.CompactNHessianCertificates Instances.WordPhaseCompactCertificates
open Instances.WordPhaseBoundaryMarking Instances.WordPhaseHeadProfiles

/-- A full original compact-N Hessian record at every actual nontrivial simple
boundary lift. Head sectors and all phase premises are discharged internally. -/
theorem compactNBoundaryHessian
    {alpha h q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e^2=1) (hq0 : q≠0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (NCompact.gamma alpha h q) (Tq q))
    (pro2 : ContinuousMonoidHom (NCompact.gamma alpha h q) P)
    (compat : ∀ g, nuTq q (tame g)=nuP (pro2 g))
    (htameSigma : tame (gammaGen (2+2*h) q (nCompactW alpha h) .sigma)=tqSigma q)
    (htameTau : tame (gammaGen (2+2*h) q (nCompactW alpha h) .tau)=tqTau q)
    (htameWild : ∀ i, tame (gammaGen (2+2*h) q (nCompactW alpha h) (.wild i))=1)
    (halpha : 2 ≤ alpha)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g•v≠v)
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l≠(SectionNine.blockFrame T Blk hE2).zeroDR)
    (rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
      (SectionNine.blockFrame T Blk hE2).TC) :
    let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
    let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
      (sourceBoundaryMapK tame pro2 compat) F
      ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho
    letI := scalarActionZmodTwo ((NCompact.gamma alpha h q : ProfiniteGrp) : Type)
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
  letI : DistribMulAction ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
  haveI : ContinuousSMul ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((NCompact.gamma alpha h q : ProfiniteGrp) : Type) × DD.Vmod ↦ p.1•p.2) =
        (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1•p.2) ∘
          (fun p ↦ (rho.1.1 p.1,p.2)) := by funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ g : ((NCompact.gamma alpha h q : ProfiniteGrp) : Type),
      rho0 DD rhoM g=rho.1.1 g :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀ (g : ((NCompact.gamma alpha h q : ProfiniteGrp) : Type))
      (v : DD.Vmod), g•v=rho0 DD rhoM g•v := by
    intro g v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c•v) (hround g).symm
  have hmark := projectedHead_marking T Blk hE2 hq0 hqe F tame pro2 compat l hl rho
    (gammaGen (2+2*h) q (nCompactW alpha h)) htameSigma htameTau htameWild
  have hsigmaHead : SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen (2+2*h) q (nCompactW alpha h) .sigma))=hvSigmaK T Blk F :=
    hmark.1
  have htauHead : SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen (2+2*h) q (nCompactW alpha h) .tau))=hvTauK T Blk F :=
    hmark.2.1
  have hwildHead : ∀ i, SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen (2+2*h) q (nCompactW alpha h) (.wild i)))=1 := hmark.2.2
  have hwildTwo : IsWildTwo (wildAlphabet (2+2*h))
      (fun i ↦ Count.rho0Continuous DD rhoM (gammaGen (2+2*h) q (nCompactW alpha h) i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoM)
      (rho0Continuous_surjective DD rhoM
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc•v=SectionNine.blockProjF T Blk cc•v :=
    SectionNine.blockProjF_compat T Blk
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  by_cases hunram : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
      F.alpha (tqTau q)•v=v
  · have htauOne : SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2+2*h) q (nCompactW alpha h) .tau))=1 :=
      htauHead.trans (head_cyclic_of_unramified T Blk F hunram).1
    have hsigmaFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2+2*h) q (nCompactW alpha h) .sigma))•v=v → v=0 := by
      intro v hv
      apply head_sigma_fixedPointFree T Blk hE2 hq0 hqe F hnt hunram v
      rwa [hsigmaHead] at hv
    exact ⟨compactNUnramifiedHessian rhoM
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      hcompat (Vmod_exp2 DD) hwildTwo hq0 hqe halpha hwildHead htauOne hsigmaFpf⟩
  · have hram : ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha (tqTau q)•v≠v := by simpa only [not_forall] using hunram
    have hprof := head_tau_ramified_profile T Blk hq0 hqe F hram
    have htauFpf : ∀ v : DD.Vmod,
        rho0 DD rhoM (gammaGen (2+2*h) q (nCompactW alpha h) .tau)•v=v → v=0 := by
      intro v hv
      apply hprof.2.2 v
      rwa [hpi, htauHead] at hv
    have htauOmega : ∀ v : DD.Vmod, powOmega2
        (rho0 DD rhoM (gammaGen (2+2*h) q (nCompactW alpha h) .tau))•v=v := by
      intro v
      have hstep : powOmega2 (rho0 DD rhoM
          (gammaGen (2+2*h) q (nCompactW alpha h) .tau))•v =
          SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
            (gammaGen (2+2*h) q (nCompactW alpha h) .tau)))•v :=
        SectionNine.blockProjF_compat T Blk _ v
      rw [hstep, powOmega2_map (SectionNine.blockProjF T Blk), htauHead,
        hprof.2.1, one_smul]
    exact ⟨compactNRamifiedHessian rhoM
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      hcompat (Vmod_exp2 DD) hwildTwo hq0 hqe halpha hwildHead htauFpf htauOmega⟩

#print axioms compactNBoundaryHessian

end
end GQ2.Dyadic.Instances.CompactNBoundaryHessianCertificates
