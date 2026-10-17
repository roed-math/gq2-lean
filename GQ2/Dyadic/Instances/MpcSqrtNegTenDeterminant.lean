/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcSqrtNegTenWordPhaseData
import GQ2.Dyadic.Instances.MpcSqrtTenDeterminant

/-!
# The branch-free procyclic-M determinant for sqrt(-10)

The pp-one unramified factor-set charge is absorbed by a second-slot translation, while the
ramified branch already has the split plus-form phase. Together these comparisons give an
unconditional affine determinant certificate. The field endpoint retains exactly the independent
canonical-marking premise `MpcPivShift 2`.
-/

namespace GQ2.Dyadic.Instances.MpcSqrtNegTenDeterminant

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.MpcWordPhaseData
open GQ2.Dyadic.Instances.MpcSqrtNegTenWordPhaseData
open GQ2.Dyadic.Instances.MpcSqrtTenDeterminant
open GQ2.Dyadic.Instances.PlusFormLinearShift
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.Instances.MpcCandidateStokes
open GQ2.Dyadic.Instances.MpcPiv
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.MProcyclicUnram
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.TameSpec
open GQ2.Dyadic.Fields
open GQ2.Dyadic.LSquare

theorem wPmpcComparison_boundary_unramified_pp_one
    {q : Nat} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (displayedGamma 2 1 1 0 q .one) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma 2 1 1 0 q .one) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau) = tqTau q)
    (htameWild : ∀ i : Fin 3,
      tame (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i)) = 1)
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
      letI := scalarActionZmodTwo ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type)
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
  letI : DistribMulAction ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) DD.Vmod := by
    constructor
    have hfac :
        (fun p :
          ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) × DD.Vmod ↦ p.1 • p.2) =
          (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
            (fun p ↦ (rho.1.1 p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ gamma : ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type),
      rho0 DD rhoM gamma = rho.1.1 gamma :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀ (g : ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rhoM g • v := by
    intro g v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v) (hround g).symm
  have hsimpleGamma : IsSimpleModTwo
      ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨nontrivial_of_ne v 0 hv, ?_⟩
    intro W hW
    apply hsimple W
    intro c w hw
    obtain ⟨g, rfl⟩ := rho.1.2 c
    exact hW g w hw
  have hheadFac : ∀ gamma : ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type),
      SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) =
        headTameSurjK T Blk F (tame gamma) := by
    intro gamma
    rw [hround gamma]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F rho gamma)
  have hsigmaHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)) = hvSigmaK T Blk F := by
    rw [hheadFac, htameSigma]
    rfl
  have htauHeadOne : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)) = 1 := by
    rw [hheadFac, htameTau]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha (tqTau q)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hunram
  have hwildHead : ∀ i : Fin 3, SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i))) = 1 := by
    intro i
    rw [hheadFac, htameWild i]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
    rw [map_one, map_one]
  have hwildTwo : IsWildTwo (wildAlphabet 2)
      (fun i ↦ Count.rho0Continuous DD rhoM
        (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoM)
      (rho0Continuous_surjective DD rhoM
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hsurjrho : Function.Surjective
      (fun gamma :
        ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) ↦ rho0 DD rhoM gamma) :=
    fun y ↦ by
    obtain ⟨gamma, hgamma⟩ := rho.1.2 y
    exact ⟨gamma, (hround gamma).trans hgamma⟩
  have hfix : ∀ v : DD.Vmod,
      (∀ gamma : ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type),
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
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma) • v = v → v = 0 := by
    intro v hv
    have hv' : hvSigmaK T Blk F • v = v := by
      have hstep : rho0 DD rhoM
          (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)) • v :=
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
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau) • v = v := by
    intro v
    calc
      rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      _ = 1 • v := congrArg (fun cc ↦ cc • v) htauHeadOne
      _ = v := one_smul _ _
  have hwildAct : ∀ (i : Fin 3) (v : DD.Vmod), rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i)) • v = v := by
    intro i v
    calc
      rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i)) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i))) • v :=
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
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)) • v = v := by
    intro v
    have hstep : powOmega2 (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)) • v =
        SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
          (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma))) • v :=
      SectionNine.blockProjF_compat T Blk _ v
    rw [hstep]
    refine (congrArg (· • v) (powOmega2_map (SectionNine.blockProjF T Blk) _)).trans ?_
    rw [hsigmaHead]
    exact hsigma2HV v
  have hsigma2Head : ∀ v : DD.Vmod,
      (SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)) ^
          (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : Int)) • v = v :=
    WordPhaseCompactMData.wPcM_resolver_smul_of_powOmega2 (SectionNine.blockProjF T Blk)
      (SectionNine.blockProjF_compat T Blk) _ hsigma2
  let base : FactorSet (SectionNine.HVq T Blk) DD.Vmod :=
    blockDatHVK T Blk hq0 hqe F l hl'
  have hbase : IsEquivariantFactorSet DD.qbar base :=
    blockDatHV_specK T Blk hq0 hqe F l hl'
  let g : SectionNine.HVq T Blk := SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma)) ^
    (omega2Exp
      (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : ℤ)
  have hg : ∀ v : DD.Vmod, g • v = v := by
    simpa only [g] using hsigma2Head
  have hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rhoM),
      (fun i ↦ c.c (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) =
        wPmCompactPhaseNormal 0 p →
      QZero DD rhoM c = plusFormD DD.qbar DD.qbar p.1 + base.m g p.1.1 := by
    intro p c hc
    have hqzero := wPmpc_QZero_eq_plusFormD_charge_of_projectedHeadMark rhoM
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) (SectionNine.blockProjF_compat T Blk)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hqe (wPmpc_sqrtNegTen_cardH2 q hqe)
      c htauHeadOne hwildHead hsigma2Head p hc
    exact hqzero
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
  let C0 := wPmpcComparison_unramified_of_headPhase_charge rhoM
    base g (scalarActionZmodTwo_triv _)
    hcompat (Vmod_exp2 DD) hwildTwo (by omega) hqe htauAct hwildAct hsigmaFpf hsigma2 hphase
  let C : SourceWordPhaseComparison DD rhoM (scalarActionZmodTwo_triv _)
      (DD.Vmod × DD.Vmod)
      (fun p ↦ plusFormD DD.qbar DD.qbar p +
        base.m g p.1) := {
    phaseEquiv := C0.phaseEquiv.trans
      (Equiv.prodUnique (DD.Vmod × DD.Vmod) (Fin 0 → DD.Vmod × DD.Vmod))
    phase_eq := fun x ↦ by
      rw [C0.phase_eq]
      rfl }
  letI actHV : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
  exact SourceWordPhaseComparison.remove_factorSetCharge base hbase
    DD.hquad DD.hns g hg C


theorem wPmpcComparison_boundary_pp_one
    {q : Nat} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (displayedGamma 2 1 1 0 q .one) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma 2 1 1 0 q .one) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau) = tqTau q)
    (htameWild : ∀ i : Fin 3,
      tame (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i)) = 1)
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
      letI := scalarActionZmodTwo ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type)
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
  · exact wPmpcComparison_boundary_unramified_pp_one T Blk hE2 hq0 hqe F tame pro2 compat
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
    letI : DistribMulAction ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    letI : DistribMulAction ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) DD.Vmod :=
      DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
    haveI : ContinuousSMul ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) DD.Vmod := by
      constructor
      have hfac :
          (fun p :
            ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type) × DD.Vmod ↦ p.1 • p.2) =
            (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
              (fun p ↦ (rho.1.1 p.1, p.2)) := by
        funext p
        rfl
      rw [hfac]
      exact continuous_of_discreteTopology.comp
        ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
    have hround : ∀ gamma : ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type),
        rho0 DD rhoM gamma = rho.1.1 gamma :=
      rho0_descData_rhoPrimeK b F En l hl rho
    have hcompat : ∀ (g : ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type))
        (v : DD.Vmod), g • v = rho0 DD rhoM g • v := by
      intro g v
      exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v) (hround g).symm
    have hheadFac : ∀ gamma : ((displayedGamma 2 1 1 0 q .one : ProfiniteGrp) : Type),
        SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) =
          headTameSurjK T Blk F (tame gamma) := by
      intro gamma
      rw [hround gamma]
      exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
        (boundaryLift_headK T Blk hE2 b F rho gamma)
    have htauHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)) = hvTauK T Blk F := by
      rw [hheadFac, htameTau]
      rfl
    have hwildHead : ∀ i : Fin 3, SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i))) = 1 := by
      intro i
      rw [hheadFac, htameWild i]
      show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
      rw [map_one, map_one]
    have hwildTwo : IsWildTwo (wildAlphabet 2)
        (fun i ↦ Count.rho0Continuous DD rhoM
          (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) :=
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
        (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)))) := by
      rw [htauHead]
      exact hoddHV
    have htauProjectedFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)) • v = v → v = 0 := by
      intro v hv
      apply htauHeadFpf v
      rwa [htauHead] at hv
    have hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)) • v = v := by
      intro v
      have hstep : powOmega2 (rho0 DD rhoM
          (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau)) • v =
          SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
            (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau))) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      rw [hstep]
      refine (congrArg (· • v) (powOmega2_map (SectionNine.blockProjF T Blk) _)).trans ?_
      rw [htauHead, powOmega2_eq_one_of_odd hoddHV, one_smul]
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
        (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i)) • v = v := by
      intro i v
      calc
        rho0 DD rhoM (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i)) • v =
            SectionNine.blockProjF T Blk (rho0 DD rhoM
              (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i))) • v := hpi _ v
        _ = 1 • v := congrArg (fun cc ↦ cc • v) (hwildHead i)
        _ = v := one_smul _ _
    have htauFpf : ∀ v : DD.Vmod, rho0 DD rhoM
        (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau) • v = v → v = 0 := by
      intro v hv
      apply htauProjectedFpf v
      exact (hpi _ v).symm.trans hv
    have hphase : ∀
        (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
        (c : VCocycle DD rhoM),
        (fun i ↦ c.c (gammaGen 2 q (mpcW 2 1 1 .one 0) i)) =
          wPmCompactPhaseNormal 0 p →
        QZero DD rhoM c = plusFormD DD.qbar DD.qbar p.1 := by
      intro p c hc
      exact wPmpc_QZero_eq_plusFormD_pp_one_of_ramifiedProjectedHeadMark rhoM
        (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
        (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        hsemi hqe (wPmpc_sqrtNegTen_cardH2 q hqe) c
        hwildHead hoddProjected htauProjectedFpf p hc
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
    let C := wPmpcComparison_ramified_pp_one_of_headPhase rhoM (scalarActionZmodTwo_triv _)
      hcompat (Vmod_exp2 DD) hwildTwo hqe hwildAct htauFpf hTodd hphase
    refine ⟨{
      phaseEquiv := C.phaseEquiv.trans
        (Equiv.prodUnique (DD.Vmod × DD.Vmod) (Fin 0 → DD.Vmod × DD.Vmod))
      phase_eq := fun x ↦ ?_ }⟩
    rw [C.phase_eq]
    simp [plusFormD]

theorem wPmpc_branchFreeSupply_pp_one
    {q : Nat} {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (displayedGamma 2 1 1 0 q .one) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma 2 1 1 0 q .one) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .sigma) = tqSigma q)
    (htameTau : tame
      (gammaGen 2 q (mpcW 2 1 1 .one 0) .tau) = tqTau q)
    (htameWild : ∀ i : Fin 3,
      tame (gammaGen 2 q (mpcW 2 1 1 .one 0) (.wild i)) = 1) :
    wPhBranchFreeSupply 2 nuP tame pro2 compat := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F
    hsimple hVne hnt m hm hcard l hl rho
  set DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl with hDD
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
  refine ⟨DD.Vmod × DD.Vmod, inferInstance, plusFormD DD.qbar DD.qbar, ?_, ?_⟩
  · simpa only [DD] using
      (wPmpcComparison_boundary_pp_one T Blk hE2 hq0 hqe F tame pro2 compat
        htameSigma htameTau htameWild hsimple hVne hnt l hl rho)
  · have hcard' : Nat.card DD.Vmod = 2 ^ (2 * m) := by
      simpa [DD, blockEnrichmentDK, blockEnrichmentK,
        RecursionFrame.Enrichment.descData, SectionNine.blockFrame,
        blockFrameImpl] using hcard
    rw [gaussSum_plusFormD DD.hquad DD.hquad DD.hns,
      ← Nat.card_eq_fintype_card, hcard']
    rfl

theorem wPmpc_sqrtNegTen_branchFreeSupply_canonical
    (q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    wPhBranchFreeSupply 2
      (mpcNu 2 1 (p true 1) (by omega))
      (TameSpec.tameOfSpec 2 q (mpcW 2 1 (p true 1) .one 0)
        (mpcTameSpecializes 2 1 (p true 1) q (by omega) hq0 hqe))
      (mpcPro2 2 1 (p true 1) q (by omega) hq0 hqe)
      (mpcCompat 2 1 (p true 1) q (by omega) hq0 hqe
        (mpcTameSpecializes 2 1 (p true 1) q (by omega) hq0 hqe)
        (mpcNu 2 1 (p true 1) (by omega))
        (mpcNu_sigma 2 1 (p true 1) (by omega))
        (mpcNu_wild 2 1 (p true 1) (by omega))) := by
  apply wPmpc_branchFreeSupply_pp_one
  · exact TameSpec.tameOfSpec_gammaGen _ .sigma
  · exact TameSpec.tameOfSpec_gammaGen _ .tau
  · intro i
    exact TameSpec.tameOfSpec_gammaGen _ (.wild i)

theorem mpcSqrtNegTen_affineDeterminantCertificate
    (q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    AffineDeterminantCertificate
      (GammaR 2 q (mpcW 2 1 (p true 1) .one 0)) 2 q (DM 2 0)
      (mpcNu 2 1 (p true 1) (by omega)) (standardNumerics 2)
      (TameSpec.tameOfSpec 2 q (mpcW 2 1 (p true 1) .one 0)
        (mpcTameSpecializes 2 1 (p true 1) q (by omega) hq0 hqe))
      (mpcPro2 2 1 (p true 1) q (by omega) hq0 hqe)
      (mpcCompat 2 1 (p true 1) q (by omega) hq0 hqe
        (mpcTameSpecializes 2 1 (p true 1) q (by omega) hq0 hqe)
        (mpcNu 2 1 (p true 1) (by omega))
        (mpcNu_sigma 2 1 (p true 1) (by omega))
        (mpcNu_wild 2 1 (p true 1) (by omega)))
      (scalarActionZmodTwo _) := by
  apply mpcAffineDeterminantCertificate_of_branchFree
    (alpha := 2) (r := 1) (pp := p true 1) (q := q)
    (le_refl 2) hqe
  exact wPmpc_sqrtNegTen_branchFreeSupply_canonical q hq0 hqe

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity}

theorem mpcSqrtNegTen_candidate_equiv_galKRN
    [T2Space (GalK KSqrtNegTen)] (hshift : MpcPivShift 2)
    (B : MarkedRecip R KSqrtNegTen) {FF : DyadicUnitFiltration KSqrtNegTen}
    (F : GenAsmFieldInputs KSqrtNegTen B FF
      (SelectedPresentation.Mpc 2 1 true .one 0).degree) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.Mpc 2 1 true .one 0).degree
        (qOf KSqrtNegTen FF) (SelectedPresentation.Mpc 2 1 true .one 0).word :
        ProfiniteGrp) : Type) (GalK KSqrtNegTen)) := by
  apply MpcCandidateFinal.mpc_candidate_equiv_galKRN_sqrtNegTen hshift B F
  exact mpcSqrtNegTen_affineDeterminantCertificate
    (qOf KSqrtNegTen FF) (qOf_ne_zero KSqrtNegTen FF) (even_qOf KSqrtNegTen FF)

/-! ## Axiom audit -/

#print axioms wPmpcComparison_boundary_unramified_pp_one
#print axioms wPmpcComparison_boundary_pp_one
#print axioms wPmpc_branchFreeSupply_pp_one
#print axioms wPmpc_sqrtNegTen_branchFreeSupply_canonical
#print axioms mpcSqrtNegTen_affineDeterminantCertificate
#print axioms mpcSqrtNegTen_candidate_equiv_galKRN

end

end GQ2.Dyadic.Instances.MpcSqrtNegTenDeterminant
