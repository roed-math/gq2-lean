/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcRamifiedProjectedComparison
import GQ2.Dyadic.Instances.RecordBlocks

/-!
# Procyclic-M boundary supply with handles

This file closes the arbitrary-h procyclic-M analytic lane. It derives the unramified and
honest ramified boundary comparisons from the common projected-head APIs, evaluates the common
wall-handle phase, and packages the result as a branch-free word-phase supply.
-/

namespace GQ2.Dyadic.Instances.MpcHandleBoundary

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Words.Mpc GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.MpcRamifiedProjectedComparison
open GQ2.Dyadic.Instances.MpcUnramifiedProjectedComparison
open GQ2.Dyadic.Instances.RecordBlocks
open GQ2.Dyadic.LSquare
open GQ2.QuadraticFp2

/-- The scalar second cohomology of every valid displayed Mpc row has cardinality two. -/
theorem wPmpc_cardH2_handles
    {alpha r pp h q : ℕ} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q) :
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type)
    Nat.card (H2
      ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) (ZMod 2)) = 2 := by
  have hsimp : UniformHsimp alpha r pp h q d.display :=
    recBl_mpc_uniformPushedHsimp (eta := eta) halpha hqe d
  exact cardH2_of_uniformPushed
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) (d := d.display)
    hsimp (by omega) hr hqe

private theorem odd_orderOf_of_powOmega2_eq_one
    {C : Type} [Group C] [Finite C] (s : C)
    (hs : powOmega2 s = 1) : Odd (orderOf s) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hn : orderOf s ≠ 0 := by
    rw [ne_eq, orderOf_eq_zero_iff, not_not]
    exact isOfFinOrder_of_finite s
  have ha : (orderOf s).factorization 2 ≠ 0 :=
    (Nat.prime_two.factorization_pos_of_dvd hn heven.two_dvd).ne'
  have hdvd : orderOf s ∣ omega2Exp (orderOf s) :=
    orderOf_dvd_of_pow_eq_one (by simpa [powOmega2] using hs)
  have hevenExp : Even (omega2Exp (orderOf s)) :=
    even_iff_two_dvd.mpr (heven.two_dvd.trans hdvd)
  have hmod := (omega2Exp_modEq_one hn ha).of_dvd (dvd_pow_self 2 ha)
  have hoddExp : Odd (omega2Exp (orderOf s)) := by
    rw [Nat.odd_iff]
    exact hmod
  exact (Nat.not_even_iff_odd.mpr hoddExp) hevenExp

/-- Every unramified procyclic-`M` boundary lift reaches the common compact phase. -/
theorem wPmpcComparison_boundary_unramified_handles
    {alpha r pp h q : Nat} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (displayedGamma alpha r pp h q d.display) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma alpha r pp h q d.display) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1),
      tame (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) (.wild i)) = 1)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
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
      letI := scalarActionZmodTwo ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type)
      letI : Fintype DD.Vmod := Fintype.ofFinite _
      letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
        inferInstance
      Nonempty (SourceWordPhaseComparison DD rhoM (scalarActionZmodTwo_triv _)
        ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
        (wPhCompactWallHandlePhase DD.qbar h)) := by
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
  letI : DistribMulAction
      ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction
      ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
  haveI : ContinuousSMul
      ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) DD.Vmod := by
    constructor
    have hfac :
        (fun p :
          ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) × DD.Vmod ↦
            p.1 • p.2) =
          (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
            (fun p ↦ (rho.1.1 p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ gamma : ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type),
      rho0 DD rhoM gamma = rho.1.1 gamma :=
    rho0_descData_rhoPrimeK b F En l hl rho
  have hcompat : ∀ (g : ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rhoM g • v := by
    intro g v
    exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v) (hround g).symm
  have hsimpleGamma : IsSimpleModTwo
      ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨nontrivial_of_ne v 0 hv, ?_⟩
    intro W hW
    apply hsimple W
    intro c w hw
    obtain ⟨g, rfl⟩ := rho.1.2 c
    exact hW g w hw
  have hheadFac : ∀ gamma : ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type),
      SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) =
        headTameSurjK T Blk F (tame gamma) := by
    intro gamma
    rw [hround gamma]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F rho gamma)
  have hsigmaHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma)) = hvSigmaK T Blk F := by
    rw [hheadFac, htameSigma]
    rfl
  have htauHeadOne : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau)) = 1 := by
    rw [hheadFac, htameTau]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha (tqTau q)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hunram
  have hwildHead : ∀ i : Fin (2 + 2 * h + 1), SectionNine.blockProjF T Blk
      (rho0 DD rhoM (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) (.wild i))) = 1 := by
    intro i
    rw [hheadFac, htameWild i]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
    rw [map_one, map_one]
  have hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rhoM
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) i)) :=
    isWildTwo_of_gammaGen (Count.rho0Continuous DD rhoM)
      (rho0Continuous_surjective DD rhoM
        (rhoPrimeK_surjective (SectionNine.blockFrame T Blk hE2) b F
          (En.radData l hl) rfl rho)) (fun _ ↦ rfl)
  have hsurjrho : Function.Surjective
      (fun gamma :
        ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) ↦
          rho0 DD rhoM gamma) :=
    fun y ↦ by
    obtain ⟨gamma, hgamma⟩ := rho.1.2 y
    exact ⟨gamma, (hround gamma).trans hgamma⟩
  have hfix : ∀ v : DD.Vmod,
      (∀ gamma : ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type),
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
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma) • v = v → v = 0 := by
    intro v hv
    have hv' : hvSigmaK T Blk F • v = v := by
      have hstep : rho0 DD rhoM
          (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma)) • v :=
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
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau) • v = v := by
    intro v
    calc
      rho0 DD rhoM (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau)) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      _ = 1 • v := congrArg (fun cc ↦ cc • v) htauHeadOne
      _ = v := one_smul _ _
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod), rho0 DD rhoM
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) (.wild i)) • v = v := by
    intro i v
    calc
      rho0 DD rhoM (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) (.wild i)) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) (.wild i))) • v :=
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
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma)) • v = v := by
    intro v
    have hstep : powOmega2 (rho0 DD rhoM
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma)) • v =
        SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
          (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma))) • v :=
      SectionNine.blockProjF_compat T Blk _ v
    rw [hstep, powOmega2_map (SectionNine.blockProjF T Blk), hsigmaHead]
    exact hsigma2HV v
  have hsigmaOmegaOne : powOmega2 (hvSigmaK T Blk F) = 1 :=
    SectionNine.hvAct_faithful T Blk _ hsigma2HV
  have hsigmaHeadOdd : Odd (orderOf (SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma)))) := by
    rw [hsigmaHead]
    exact odd_orderOf_of_powOmega2_eq_one _ hsigmaOmegaOne
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
        (SectionNine.blockProjF T Blk) hpi) := by
    intro z
    obtain ⟨c, hc⟩ := hblockProj z.2
    exact ⟨(z.1, c), Prod.ext rfl hc⟩
  have hcardH2 := wPmpc_cardH2_handles
    (alpha := alpha) (r := r) (pp := pp) (h := h) d halpha hr hqe
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  simpa only [rhoM, b, En] using
    (exists_comparison_unramified_of_projectedHead_handles rhoM
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) hpi (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      hsemi hcompat (Vmod_exp2 DD) hwildTwo d.represents halpha hqe hcardH2
      htauHeadOne hwildHead hsigmaHeadOdd (by
        intro v hv
        apply hsigmaFpf v
        rw [hpi]
        exact hv) DD.hquad DD.hns)

/-- Every arbitrary-h procyclic-M boundary lift reaches the common wall-handle endpoint. -/
theorem wPmpcComparison_boundary_handles
    {alpha r pp h q : Nat} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (displayedGamma alpha r pp h q d.display) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma alpha r pp h q d.display) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1),
      tame (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) (.wild i)) = 1)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
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
      letI := scalarActionZmodTwo ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type)
      letI : Fintype DD.Vmod := Fintype.ofFinite _
      letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
        inferInstance
      Nonempty (SourceWordPhaseComparison DD rhoM (scalarActionZmodTwo_triv _)
        ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
        (wPhCompactWallHandlePhase DD.qbar h)) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  classical
  by_cases hunram : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
      F.alpha (tqTau q) • v = v
  · exact wPmpcComparison_boundary_unramified_handles d T Blk hE2 hq0 hqe F tame pro2 compat
      htameSigma htameTau htameWild halpha hr hsimple hVne hnt hunram l hl
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
    letI : DistribMulAction
        ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    letI : DistribMulAction
        ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) DD.Vmod :=
      DistribMulAction.compHom DD.Vmod rho.1.1.toMonoidHom
    haveI : ContinuousSMul
        ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) DD.Vmod := by
      constructor
      have hfac :
          (fun p :
            ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type) × DD.Vmod ↦
              p.1 • p.2) =
            (fun p : (SectionNine.blockFrame T Blk hE2).YC × DD.Vmod ↦ p.1 • p.2) ∘
              (fun p ↦ (rho.1.1 p.1, p.2)) := by
        funext p
        rfl
      rw [hfac]
      exact continuous_of_discreteTopology.comp
        ((rho.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
    have hround : ∀ gamma : ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type),
        rho0 DD rhoM gamma = rho.1.1 gamma :=
      rho0_descData_rhoPrimeK b F En l hl rho
    have hcompat : ∀ (g : ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type))
        (v : DD.Vmod), g • v = rho0 DD rhoM g • v := by
      intro g v
      exact congrArg (fun c : (SectionNine.blockFrame T Blk hE2).YC ↦ c • v) (hround g).symm
    have hheadFac : ∀ gamma : ((displayedGamma alpha r pp h q d.display : ProfiniteGrp) : Type),
        SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) =
          headTameSurjK T Blk F (tame gamma) := by
      intro gamma
      rw [hround gamma]
      exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
        (boundaryLift_headK T Blk hE2 b F rho gamma)
    have htauHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau)) = hvTauK T Blk F := by
      rw [hheadFac, htameTau]
      rfl
    have hwildHead : ∀ i : Fin (2 + 2 * h + 1), SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) (.wild i))) = 1 := by
      intro i
      rw [hheadFac, htameWild i]
      show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
      rw [map_one, map_one]
    have hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
        (fun i ↦ Count.rho0Continuous DD rhoM
          (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) i)) :=
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
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau)))) := by
      rw [htauHead]
      exact hoddHV
    have htauProjectedFpf : ∀ v : DD.Vmod, SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau)) • v = v → v = 0 := by
      intro v hv
      apply htauHeadFpf v
      rwa [htauHead] at hv
    have hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rhoM
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau)) • v = v := by
      intro v
      have hstep : powOmega2 (rho0 DD rhoM
          (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau)) • v =
          SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
            (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau))) • v :=
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
    have hcardH2 := wPmpc_cardH2_handles
      (alpha := alpha) (r := r) (pp := pp) (h := h) d halpha hr hqe
    simpa only [rhoM, b, En] using
      (exists_comparison_ramified_of_projectedHead_handles rhoM
        (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
        (SectionNine.blockProjF T Blk) hpi
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hsemi hcompat (Vmod_exp2 DD) hwildTwo
        halpha hqe hcardH2 hwildHead hoddProjected htauProjectedFpf)

/-- The common compact wall-handle endpoint has the standard even-degree Gauss sum. -/
theorem wPmpc_compactWallHandlePhase_gaussSum
    {V : Type} [AddCommGroup V] [Fintype V] {q0 : V → ZMod 2}
    (hquad : IsQuadraticFp2 q0) (hns : Nonsingular q0) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    QuadraticFp2.gaussSum (wPhCompactWallHandlePhase q0 h) =
      (standardNumerics (2 * h + 2)).gaussRam m :=
  wPh_compactWallHandlePhase_gaussSum_standardRam hquad hns hcard h

/-- The arbitrary-h procyclic-M word has a branch-free word-phase supply. -/
theorem wPmpc_branchFreeSupply_handles
    {alpha r pp h q : Nat} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (displayedGamma alpha r pp h q d.display) (Tq q))
    (pro2 : ContinuousMonoidHom (displayedGamma alpha r pp h q d.display) P)
    (compat : ∀ g, nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .sigma) = tqSigma q)
    (htameTau : tame
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 + 2 * h + 1), tame
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp d.display h) (.wild i)) = 1)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) :
    wPhBranchFreeSupply (2 * h + 2) nuP tame pro2 compat := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F
    hsimple hVne hnt m hm hcard l hl rho
  set DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  refine ⟨(DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod), inferInstance,
    wPhCompactWallHandlePhase DD.qbar h, ?_, ?_⟩
  · simpa only [DD] using
      (wPmpcComparison_boundary_handles d T Blk hE2 hq0 hqe F tame pro2 compat
        htameSigma htameTau htameWild halpha hr hsimple hVne hnt l hl rho)
  · apply wPmpc_compactWallHandlePhase_gaussSum DD.hquad DD.hns
    rw [← Nat.card_eq_fintype_card]
    simpa [DD, blockEnrichmentDK, blockEnrichmentK,
      RecursionFrame.Enrichment.descData, SectionNine.blockFrame,
      blockFrameImpl] using hcard
/-! ## Axiom audit -/

#print axioms wPmpc_cardH2_handles
#print axioms wPmpcComparison_boundary_unramified_handles
#print axioms wPmpcComparison_boundary_handles
#print axioms wPmpc_compactWallHandlePhase_gaussSum
#print axioms wPmpc_branchFreeSupply_handles

end

end GQ2.Dyadic.Instances.MpcHandleBoundary
