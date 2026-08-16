/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcWordPhaseData
import GQ2.Dyadic.Instances.WordPhaseCompactMUnramifiedBoundary
import GQ2.Dyadic.Instances.MpcCandidateFinal

/-!
# The branch-free procyclic-M determinant for sqrt(10)

The handle-free procyclic-M word has the common split hyperbolic phase in both the unramified
and ramified simple-module branches. This supplies the generic affine determinant bridge and,
for the canonical `sqrt(10)` core, closes the corrected RN candidate endpoint.
-/

namespace GQ2.Dyadic.Instances.MpcSqrtTenDeterminant

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.MpcWordPhaseData
open GQ2.Dyadic.Instances.WordPhaseCompactMData
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Instances.MpcCandidateStokes
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.TameSpec
open GQ2.Dyadic.Fields
open GQ2.Dyadic.LSquare

theorem wPmpc_sqrtTen_cardH2 (q : ℕ) (hqe : Even q) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    Nat.card
      (H2 ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2)) = 2 := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  have hsimp : UniformHsimp 2 1 0 0 q .one :=
    RecordBlocks.recBl_mpc_uniformPushedHsimp
      (alpha := 2) (r := 1) (pp := 0) (h := 0) (q := q)
      (by omega) hqe MpcDisplayFor.one
  exact cardH2_of_uniformPushed
    (alpha := 2) (r := 1) (pp := 0) (h := 0) (q := q) (d := EtaDisplay.one)
    hsimp (by omega) (by omega) hqe

theorem wPmpc_QZero_sqrtTen_of_projectedHeadMark
    {q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hqe : Even q) (c : VCocycle DD rho)
    (htauHead : pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)) = 1)
    (hwildHead : ∀ i : Fin 3, pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i))) = 1)
    (hsigma2Head : ∀ v : DD.Vmod,
      (pi (rho0 DD rho (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma)) ^
        (omega2Exp
          (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ)) • v = v)
    (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen 2 q (mpcW 2 1 0 .one 0) i)) =
      wPmCompactPhaseNormal 0 p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = plusFormD DD.qbar DD.qbar p.1 := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  exact wPmpc_QZero_eq_plusFormD_pp_zero_of_projectedHeadMark rho
    base hbase pi hpi hf hm (by omega) hqe (wPmpc_sqrtTen_cardH2 q hqe)
    c htauHead hwildHead
    hsigma2Head p hc

theorem wPmpc_QZero_sqrtTen_of_ramifiedProjectedHeadMark
    {q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hqe : Even q) (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin 3, pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)) • v = v → v = 0)
    (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen 2 q (mpcW 2 1 0 .one 0) i)) =
      wPmCompactPhaseNormal 0 p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = plusFormD DD.qbar DD.qbar p.1 := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  exact wPmpc_QZero_eq_plusFormD_pp_zero_of_ramifiedProjectedHeadMark rho
    base hbase pi hpi hf hm hphi hqe (wPmpc_sqrtTen_cardH2 q hqe) c
    hwildHead htauHeadOdd htauHeadFpf p hc

theorem wPmpcComparison_boundary_unramified
    {q : Nat} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (displayedGamma 2 1 0 0 q .one) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma 2 1 0 0 q .one) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau) = tqTau q)
    (htameWild : ∀ i : Fin 3,
      tame (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i)) = 1)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
    (hunram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v = v)
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR) :
    ∀ rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
        (SectionNine.blockFrame T Blk hE2).TC,
      let DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
      let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
        (sourceBoundaryMapK tame pro2 compat) F
        ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho
      letI := scalarActionZmodTwo ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type)
      letI : Fintype DD.Vmod := Fintype.ofFinite _
      letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
      Nonempty (SourceWordPhaseComparison DD rhoM (scalarActionZmodTwo_triv _)
        (DD.Vmod × DD.Vmod) (plusFormD DD.qbar DD.qbar)) := by
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
  letI : DistribMulAction ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) DD.Vmod := by
    constructor
    have hfac :
        (fun p :
          ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) × DD.Vmod ↦ p.1 • p.2) =
          (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
            (fun p ↦ (rho.1.1 p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ gamma : ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type),
      rho0 DD rhoM gamma = rho.1.1 gamma :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀ (g : ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rhoM g • v := by
    intro g v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v) (hround g).symm
  have hsimpleGamma : IsSimpleModTwo
      ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨nontrivial_of_ne v 0 hv, ?_⟩
    intro W hW
    apply hsimple W
    intro c w hw
    obtain ⟨g, rfl⟩ := rho.1.2 c
    exact hW g w hw
  have hheadFac : ∀ gamma : ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type),
      SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) =
        headTameSurjK T Blk F (tame gamma) := by
    intro gamma
    rw [hround gamma]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F rho gamma)
  have hsigmaHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma)) = hvSigmaK T Blk F := by
    rw [hheadFac, htameSigma]
    rfl
  have htauHeadOne : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)) = 1 := by
    rw [hheadFac, htameTau]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha (tqTau q)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hunram
  have hwildHead : ∀ i : Fin 3, SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i))) = 1 := by
    intro i
    rw [hheadFac, htameWild i]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
    rw [map_one, map_one]
  have hwildTwo : IsWildTwo (wildAlphabet 2)
      (fun i ↦ Count.rho0Continuous DD rhoM
        (gammaGen 2 q (mpcW 2 1 0 .one 0) i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoM)
      (rho0Continuous_surjective DD rhoM
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hsurjrho : Function.Surjective
      (fun gamma :
        ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) ↦ rho0 DD rhoM gamma) :=
    fun y ↦ by
    obtain ⟨gamma, hgamma⟩ := rho.1.2 y
    exact ⟨gamma, (hround gamma).trans hgamma⟩
  have hfix : ∀ v : DD.Vmod,
      (∀ gamma : ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type),
        rho0 DD rhoM gamma • v = v) → v = 0 :=
    hfix_of_simple_nt hsurjrho hsimple hnt
  have hzp : ∀ x : SectionNine.HVq T Blk,
      x ∈ Subgroup.zpowers (hvSigmaK T Blk F) := by
    have hle : Subgroup.closure {hvSigmaK T Blk F, hvTauK T Blk F} ≤
        Subgroup.zpowers (hvSigmaK T Blk F) := by
      rw [Subgroup.closure_le, Set.pair_subset_iff]
      refine ⟨Subgroup.mem_zpowers _, ?_⟩
      have htauOne : hvTauK T Blk F = 1 := by
        show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha (tqTau q)) = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hunram
      rw [htauOne]
      exact Subgroup.one_mem _
    rw [hv_genK T Blk F] at hle
    exact fun x ↦ hle (Subgroup.mem_top x)
  have hsigmaFpf : ∀ v : DD.Vmod, rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma) • v = v → v = 0 := by
    intro v hv
    have hv' : hvSigmaK T Blk F • v = v := by
      have hstep : rho0 DD rhoM
          (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma)) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      rwa [hstep, hsigmaHead] at hv
    refine hfix v fun gamma ↦ ?_
    have hstep : rho0 DD rhoM gamma • v =
        SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) • v :=
      SectionNine.blockProjF_compat T Blk _ v
    rw [hstep]
    have hmem : hvSigmaK T Blk F ∈ MulAction.stabilizer (SectionNine.HVq T Blk) v :=
      MulAction.mem_stabilizer_iff.mpr hv'
    exact (Subgroup.zpowers_le.mpr hmem)
      (hzp (SectionNine.blockProjF T Blk (rho0 DD rhoM gamma)))
  have htauAct : ∀ v : DD.Vmod, rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau) • v = v := by
    intro v
    calc
      rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      _ = 1 • v := congrArg (fun cc ↦ cc • v) htauHeadOne
      _ = v := one_smul _ _
  have hwildAct : ∀ (i : Fin 3) (v : DD.Vmod), rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i)) • v = v := by
    intro i v
    calc
      rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i)) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i))) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      _ = 1 • v := congrArg (fun cc ↦ cc • v) (hwildHead i)
      _ = v := one_smul _ _
  have hsigma2HV : ∀ v : DD.Vmod, powOmega2 (hvSigmaK T Blk F) • v = v := by
    have hsimpleHV : IsSimpleModTwo (SectionNine.HVq T Blk) DD.Vmod := by
      refine ⟨hsimpleGamma.1, ?_⟩
      intro W hW
      apply hsimpleGamma.2 W
      intro gamma v hv
      have hstep : rho0 DD rhoM gamma • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      rw [hcompat gamma v, hstep]
      exact hW _ v hv
    apply pow2_smul_trivial_of_stable (Vmod_exp2 DD) hsimpleHV
      (powOmega2 (hvSigmaK T Blk F)) (isPGroup_zpowers_powOmega2 _)
    intro a v hv
    have hc : powOmega2 (hvSigmaK T Blk F) * a =
        a * powOmega2 (hvSigmaK T Blk F) :=
      comm_of_cyclic (hvSigmaK T Blk F) hzp _ _
    calc
      powOmega2 (hvSigmaK T Blk F) • (a • v) =
          (powOmega2 (hvSigmaK T Blk F) * a) • v := (mul_smul _ _ _).symm
      _ = (a * powOmega2 (hvSigmaK T Blk F)) • v := by rw [hc]
      _ = a • (powOmega2 (hvSigmaK T Blk F) • v) := mul_smul _ _ _
      _ = a • v := congrArg (a • ·) hv
  have hsigma2 : ∀ v : DD.Vmod, powOmega2 (rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma)) • v = v := by
    intro v
    have hstep : powOmega2 (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma)) • v =
        SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
          (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma))) • v :=
      SectionNine.blockProjF_compat T Blk _ v
    rw [hstep, powOmega2_map (SectionNine.blockProjF T Blk), hsigmaHead]
    exact hsigma2HV v
  have hsigma2Head : ∀ v : DD.Vmod,
      (SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma)) ^
          (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : Int)) • v = v :=
    WordPhaseCompactMData.wPcM_resolver_smul_of_powOmega2 (SectionNine.blockProjF T Blk)
      (SectionNine.blockProjF_compat T Blk) _ hsigma2
  have hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rhoM),
      (fun i ↦ c.c (gammaGen 2 q (mpcW 2 1 0 .one 0) i)) =
        wPmCompactPhaseNormal 0 p →
      QZero DD rhoM c = plusFormD DD.qbar DD.qbar p.1 := by
    intro p c hc
    exact wPmpc_QZero_sqrtTen_of_projectedHeadMark rhoM
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) (SectionNine.blockProjF_compat T Blk)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hqe c htauHeadOne
      hwildHead hsigma2Head p hc
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
  let C := wPmpcComparison_unramified_of_headPhase rhoM (scalarActionZmodTwo_triv _)
    hcompat (Vmod_exp2 DD) hwildTwo (by omega) hqe htauAct hwildAct hsigmaFpf hsigma2 hphase
  refine ⟨{
    phaseEquiv := C.phaseEquiv.trans
      (Equiv.prodUnique (DD.Vmod × DD.Vmod) (Fin 0 → DD.Vmod × DD.Vmod))
    phase_eq := fun x ↦ ?_ }⟩
  rw [C.phase_eq]
  simp [plusFormD]

theorem wPmpcComparison_boundary
    {q : Nat} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (displayedGamma 2 1 0 0 q .one) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma 2 1 0 0 q .one) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau) = tqTau q)
    (htameWild : ∀ i : Fin 3,
      tame (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i)) = 1)
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
      letI := scalarActionZmodTwo ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type)
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
  · exact wPmpcComparison_boundary_unramified T Blk hE2 hq0 hqe F tame pro2 compat
      htameSigma htameTau htameWild hsimple hVne hnt hunram l hl
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
    letI : DistribMulAction ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    letI : DistribMulAction ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) DD.Vmod :=
      DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
    haveI : ContinuousSMul ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) DD.Vmod := by
      constructor
      have hfac :
          (fun p :
            ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type) × DD.Vmod ↦ p.1 • p.2) =
            (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
              (fun p ↦ (rho.1.1 p.1, p.2)) := by
        funext p
        rfl
      rw [hfac]
      exact continuous_of_discreteTopology.comp
        ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
    have hround : ∀ gamma : ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type),
        rho0 DD rhoM gamma = rho.1.1 gamma :=
      rho0_descData_rhoPrimeK b F En l hl rho
    have hcompat : ∀ (g : ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type))
        (v : DD.Vmod), g • v = rho0 DD rhoM g • v := by
      intro g v
      exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v) (hround g).symm
    have hheadFac : ∀ gamma : ((displayedGamma 2 1 0 0 q .one : ProfiniteGrp) : Type),
        SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) =
          headTameSurjK T Blk F (tame gamma) := by
      intro gamma
      rw [hround gamma]
      exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
        (boundaryLift_headK T Blk hE2 b F rho gamma)
    have htauHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)) = hvTauK T Blk F := by
      rw [hheadFac, htameTau]
      rfl
    have hwildHead : ∀ i : Fin 3, SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i))) = 1 := by
      intro i
      rw [hheadFac, htameWild i]
      show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
      rw [map_one, map_one]
    have hwildTwo : IsWildTwo (wildAlphabet 2)
        (fun i ↦ Count.rho0Continuous DD rhoM
          (gammaGen 2 q (mpcW 2 1 0 .one 0) i)) :=
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
        (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)))) := by
      rw [htauHead]
      exact hoddHV
    have htauProjectedFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)) • v = v → v = 0 := by
      intro v hv
      apply htauHeadFpf v
      rwa [htauHead] at hv
    have hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)) • v = v := by
      intro v
      have hstep : powOmega2 (rho0 DD rhoM
          (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau)) • v =
          SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
            (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau))) • v :=
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
    have hwildAct : ∀ (i : Fin 3) (v : DD.Vmod), rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i)) • v = v := by
      intro i v
      calc
        rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i)) • v =
            SectionNine.blockProjF T Blk (rho0 DD rhoM
              (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i))) • v := hpi _ v
        _ = 1 • v := congrArg (fun cc ↦ cc • v) (hwildHead i)
        _ = v := one_smul _ _
    have htauFpf : ∀ v : DD.Vmod, rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau) • v = v → v = 0 := by
      intro v hv
      apply htauProjectedFpf v
      exact (hpi _ v).symm.trans hv
    have hphase : ∀
        (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
        (c : VCocycle DD rhoM),
        (fun i ↦ c.c (gammaGen 2 q (mpcW 2 1 0 .one 0) i)) =
          wPmCompactPhaseNormal 0 p →
        QZero DD rhoM c = plusFormD DD.qbar DD.qbar p.1 := by
      intro p c hc
      exact wPmpc_QZero_sqrtTen_of_ramifiedProjectedHeadMark rhoM
        (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
        (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        hsemi hqe c hwildHead hoddProjected htauProjectedFpf p hc
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
    let C := wPmpcComparison_ramified_of_headPhase rhoM (scalarActionZmodTwo_triv _)
      hcompat (Vmod_exp2 DD) hwildTwo hqe hwildAct htauFpf hTodd hphase
    refine ⟨{
      phaseEquiv := C.phaseEquiv.trans
        (Equiv.prodUnique (DD.Vmod × DD.Vmod) (Fin 0 → DD.Vmod × DD.Vmod))
      phase_eq := fun x ↦ ?_ }⟩
    rw [C.phase_eq]
    simp [plusFormD]

/-- The branch-free word-phase supply for the handle-free procyclic-M sqrt(10) word. -/
theorem wPmpc_branchFreeSupply
    {q : Nat} {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (displayedGamma 2 1 0 0 q .one) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma 2 1 0 0 q .one) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .sigma) = tqSigma q)
    (htameTau : tame
      (gammaGen 2 q (mpcW 2 1 0 .one 0) .tau) = tqTau q)
    (htameWild : ∀ i : Fin 3,
      tame (gammaGen 2 q (mpcW 2 1 0 .one 0) (.wild i)) = 1) :
    wPhBranchFreeSupply 2 nuP tame pro2 compat := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F
    hsimple hVne hnt m hm hcard l hl rho
  set DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl with hDD
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
  refine ⟨DD.Vmod × DD.Vmod, inferInstance, plusFormD DD.qbar DD.qbar, ?_, ?_⟩
  · simpa only [DD] using
      (wPmpcComparison_boundary T Blk hE2 hq0 hqe F tame pro2 compat
        htameSigma htameTau htameWild hsimple hVne hnt l hl rho)
  · have hcard' : Nat.card DD.Vmod = 2 ^ (2 * m) := by
      simpa [DD, blockEnrichmentDK, blockEnrichmentK,
        RecursionFrame.Enrichment.descData, SectionNine.blockFrame,
        blockFrameImpl] using hcard
    rw [gaussSum_plusFormD DD.hquad DD.hquad DD.hns,
      ← Nat.card_eq_fintype_card, hcard']
    rfl

/-- The canonical procyclic-M core realizes the sqrt(10) branch-free supply. -/
theorem wPmpc_sqrtTen_branchFreeSupply
    (q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    wPhBranchFreeSupply 2
      (MProcyclicCore.mpcNu 2 1 0 (by omega))
      (TameSpec.tameOfSpec 2 q (mpcW 2 1 0 .one 0)
        (MProcyclicCore.mpcTameSpecializes 2 1 0 q (by omega) hq0 hqe))
      (MProcyclicCore.mpcPro2 2 1 0 q (by omega) hq0 hqe)
      (MProcyclicCore.mpcCompat 2 1 0 q (by omega) hq0 hqe
        (MProcyclicCore.mpcTameSpecializes 2 1 0 q (by omega) hq0 hqe)
        (MProcyclicCore.mpcNu 2 1 0 (by omega))
        (MProcyclicCore.mpcNu_sigma 2 1 0 (by omega))
        (MProcyclicCore.mpcNu_wild 2 1 0 (by omega))) := by
  apply wPmpc_branchFreeSupply
  · exact TameSpec.tameOfSpec_gammaGen _ .sigma
  · exact TameSpec.tameOfSpec_gammaGen _ .tau
  · intro i
    exact TameSpec.tameOfSpec_gammaGen _ (.wild i)

/-- Canonical-parameter spelling of the sqrt(10) branch-free supply. -/
theorem wPmpc_sqrtTen_branchFreeSupply_canonical
    (q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    wPhBranchFreeSupply 2
      (mpcNu 2 1 (p false 1) (by omega))
      (TameSpec.tameOfSpec 2 q (mpcW 2 1 (p false 1) .one 0)
        (mpcTameSpecializes 2 1 (p false 1) q (by omega) hq0 hqe))
      (mpcPro2 2 1 (p false 1) q (by omega) hq0 hqe)
      (mpcCompat 2 1 (p false 1) q (by omega) hq0 hqe
        (mpcTameSpecializes 2 1 (p false 1) q (by omega) hq0 hqe)
        (mpcNu 2 1 (p false 1) (by omega))
        (mpcNu_sigma 2 1 (p false 1) (by omega))
        (mpcNu_wild 2 1 (p false 1) (by omega))) := by
  apply wPmpc_branchFreeSupply
  · exact TameSpec.tameOfSpec_gammaGen _ .sigma
  · exact TameSpec.tameOfSpec_gammaGen _ .tau
  · intro i
    exact TameSpec.tameOfSpec_gammaGen _ (.wild i)

/-- A branch-free word-phase supply discharges both affine determinant clauses for any
handle-free procyclic-M word. -/
theorem mpcAffineDeterminantCertificate_of_branchFree
    {alpha r pp q : ℕ} (hα : 2 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom
      (GammaR 2 q (mpcW alpha r pp .one 0)) (Tq q))
    (pro2 : ContinuousMonoidHom (GammaR 2 q (mpcW alpha r pp .one 0)) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (S : wPhBranchFreeSupply 2 nuP tame pro2 compat) :
    AffineDeterminantCertificate (GammaR 2 q (mpcW alpha r pp .one 0)) 2 q P nuP
      (standardNumerics 2) tame pro2 compat (scalarActionZmodTwo _) := by
  letI := scalarActionZmodTwo
    (((GammaR 2 q (mpcW alpha r pp .one 0) : ProfiniteGrp) : Type))
  haveI := scalarActionZmodTwo_continuousSMul
    (((GammaR 2 q (mpcW alpha r pp .one 0) : ProfiniteGrp) : Type))
  have hsimp : UniformHsimp alpha r pp 0 q .one :=
    RecordBlocks.recBl_mpc_uniformPushedHsimp hα hqe MpcDisplayFor.one
  constructor
  · exact fun T Blk _ _ _ hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl _ ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0' hqe' F
      apply gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [mpcCand_hZcard hsimp
          (by omega) hqe (sourceBoundaryMapK tame pro2 compat) F En l hl
          hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · rw [wPh_gauss_targets_eq 0 m]
        exact S T Blk hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl
  · exact fun T Blk _ _ _ hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl _ ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0' hqe' F
      apply gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [mpcCand_hZcard hsimp
          (by omega) hqe (sourceBoundaryMapK tame pro2 compat) F En l hl
          hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact S T Blk hE2 hq0' hqe' F hsimple hVne hnt m hm hcard l hl

/-- The branch-free phase comparison gives the affine determinant certificate for sqrt(10). -/
theorem mpcSqrtTen_affineDeterminantCertificate
    (q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    AffineDeterminantCertificate
      (GammaR 2 q (mpcW 2 1 (p false 1) .one 0)) 2 q (DM 2 0)
      (mpcNu 2 1 (p false 1) (by omega)) (standardNumerics 2)
      (TameSpec.tameOfSpec 2 q (mpcW 2 1 (p false 1) .one 0)
        (mpcTameSpecializes 2 1 (p false 1) q (by omega) hq0 hqe))
      (mpcPro2 2 1 (p false 1) q (by omega) hq0 hqe)
      (mpcCompat 2 1 (p false 1) q (by omega) hq0 hqe
        (mpcTameSpecializes 2 1 (p false 1) q (by omega) hq0 hqe)
        (mpcNu 2 1 (p false 1) (by omega))
        (mpcNu_sigma 2 1 (p false 1) (by omega))
        (mpcNu_wild 2 1 (p false 1) (by omega)))
      (scalarActionZmodTwo _) := by
  apply mpcAffineDeterminantCertificate_of_branchFree
    (alpha := 2) (r := 1) (pp := p false 1) (q := q)
    (le_refl 2) hqe
  exact wPmpc_sqrtTen_branchFreeSupply_canonical q hq0 hqe

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity}

/-- The corrected sqrt(10) candidate is unconditionally the expected Galois group. -/
theorem mpcSqrtTen_candidate_equiv_galKRN
    [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen)
    {FF : DyadicUnitFiltration KSqrtTen}
    (F : GenAsmFieldInputs KSqrtTen B FF
      (SelectedPresentation.Mpc 2 1 false .one 0).degree) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.Mpc 2 1 false .one 0).degree
        (qOf KSqrtTen FF) (SelectedPresentation.Mpc 2 1 false .one 0).word :
        ProfiniteGrp) : Type) (GalK KSqrtTen)) := by
  apply MpcCandidateFinal.mpc_candidate_equiv_galKRN_sqrtTen B F
  exact mpcSqrtTen_affineDeterminantCertificate
    (qOf KSqrtTen FF) (qOf_ne_zero KSqrtTen FF) (even_qOf KSqrtTen FF)

/-! ## Axiom audit -/

#print axioms wPmpc_QZero_sqrtTen_of_projectedHeadMark
#print axioms wPmpc_QZero_sqrtTen_of_ramifiedProjectedHeadMark
#print axioms wPmpcComparison_boundary
#print axioms wPmpc_sqrtTen_branchFreeSupply_canonical
#print axioms mpcAffineDeterminantCertificate_of_branchFree
#print axioms mpcSqrtTen_affineDeterminantCertificate
#print axioms mpcSqrtTen_candidate_equiv_galKRN

end
end GQ2.Dyadic.Instances.MpcSqrtTenDeterminant
