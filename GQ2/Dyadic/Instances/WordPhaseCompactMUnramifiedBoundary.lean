/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactMData
import GQ2.Dyadic.Instances.GammaLDeterminantRamifiedData

/-!
# Compact-M unramified boundary data

This file puts the compact-`M`, `h = 0`, `P = 1` comparison at an arbitrary unramified
boundary lift.  The tame head is cyclic on `sigma`; simplicity makes `sigma` fixed-point-free
and makes its two-primary part act trivially.  The latter fact is transported to the exact
resolver used by the compact Hessian trace.

The honest ramified branch is deliberately not covered here.  Its newer second-order row does
not assume the `sigma` two-primary action is trivial, while the older `P = 0` Hessian assembler
does.  Closing that analytic gap is a separate theorem.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactMData

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.LSquare

/-! ## Resolver transport -/

/-- Transport `powOmega2`-triviality through a head quotient at the exact compact trace
resolver. -/
theorem wPcM_resolver_smul_of_powOmega2
    {C Cbar V : Type} [Group C] [Finite C] [Group Cbar] [AddCommGroup V] [Finite V]
    [DistribMulAction C V] [DistribMulAction Cbar V]
    (pi : C →* Cbar) (hpi : ∀ (c : C) (v : V), c • v = pi c • v) (s : C)
    (hsigma2 : ∀ v : V, powOmega2 s • v = v) :
    ∀ v : V,
      (pi s ^ (omega2Exp
        (4 * Monoid.exponent (SectionSix.SemiProd C V)) : Int)) • v = v := by
  let L := SectionSix.SemiProd C V
  letI : Finite L := inferInstanceAs (Finite (V × C))
  let N := 4 * Monoid.exponent L
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
  have hsExp : s ^ Monoid.exponent L = 1 := by
    let p : L := (0, s)
    have hp : p ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one p
    calc
      s ^ Monoid.exponent L = sdSnd (p ^ Monoid.exponent L) :=
        (map_pow sdSnd p _).symm
      _ = 1 := by rw [hp]; exact map_one sdSnd
  have hsN : s ^ N = 1 := by
    rw [show N = Monoid.exponent L * 4 by simp [N, Nat.mul_comm], pow_mul, hsExp, one_pow]
  have hresolved : s ^ omega2Exp N = powOmega2 s :=
    powOmega2_pow_eq _ (orderOf_dvd_of_pow_eq_one hsN) hN
  intro v
  calc
    (pi s ^ (omega2Exp N : Int)) • v = pi (s ^ (omega2Exp N : Int)) • v := by
      rw [map_zpow]
    _ = (s ^ (omega2Exp N : Int)) • v := (hpi _ _).symm
    _ = powOmega2 s • v := by rw [zpow_natCast, hresolved]
    _ = v := hsigma2 v

/-! ## The unramified boundary lift -/

/-- Every unramified compact-`M` boundary lift has the `P = 1` source-to-word comparison. -/
theorem wPcMComparison_boundary_unramifiedP1
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
  have hsimpleGamma : IsSimpleModTwo
      ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type) DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨nontrivial_of_ne v 0 hv, ?_⟩
    intro W hW
    apply hsimple W
    intro c w hw
    obtain ⟨g, rfl⟩ := rho.1.2 c
    exact hW g w hw
  have hheadFac : ∀ gamma : ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type),
      SectionNine.blockProjF T Blk (rho0 DD rhoM gamma) =
        headTameSurjK T Blk F (tame gamma) := by
    intro gamma
    rw [hround gamma]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 b F rho gamma)
  have hsigmaHead : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma)) = hvSigmaK T Blk F := by
    rw [hheadFac, htameSigma]
    rfl
  have htauHeadOne : SectionNine.blockProjF T Blk (rho0 DD rhoM
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) = 1 := by
    rw [hheadFac, htameTau]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha (tqTau q)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hunram
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
  have hsurjrho : Function.Surjective
      (fun gamma : ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type) ↦ rho0 DD rhoM gamma) :=
    fun y ↦ by
    obtain ⟨gamma, hgamma⟩ := rho.1.2 y
    exact ⟨gamma, (hround gamma).trans hgamma⟩
  have hfix : ∀ v : DD.Vmod,
      (∀ gamma : ((MCompact.gamma alpha 0 q : ProfiniteGrp) : Type),
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
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma) • v = v → v = 0 := by
    intro v hv
    have hv' : hvSigmaK T Blk F • v = v := by
      have hstep : rho0 DD rhoM
          (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma)) • v :=
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
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau) • v = v := by
    intro v
    calc
      rho0 DD rhoM (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v :=
        SectionNine.blockProjF_compat T Blk _ v
      _ = 1 • v := congrArg (fun cc ↦ cc • v) htauHeadOne
      _ = v := one_smul _ _
  have hwildAct : ∀ (i : Fin 3) (v : DD.Vmod), rho0 DD rhoM
      (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i)) • v = v := by
    intro i v
    calc
      rho0 DD rhoM (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i)) • v =
          SectionNine.blockProjF T Blk (rho0 DD rhoM
            (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i))) • v :=
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
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma)) • v = v := by
    intro v
    have hstep : powOmega2 (rho0 DD rhoM
        (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma)) • v =
        SectionNine.blockProjF T Blk (powOmega2 (rho0 DD rhoM
          (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma))) • v :=
      SectionNine.blockProjF_compat T Blk _ v
    refine hstep.trans ?_
    refine (congrArg (· • v) ((powOmega2_map (SectionNine.blockProjF T Blk) _).trans
      (congrArg powOmega2 hsigmaHead))).trans ?_
    exact hsigma2HV v
  have hsigma2Head : ∀ v : DD.Vmod,
      (SectionNine.blockProjF T Blk (rho0 DD rhoM
        (gammaGen 2 q (MCompact.mCompactW alpha 0) .sigma)) ^
          (omega2Exp
            (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)) : Int)) • v = v :=
    wPcM_resolver_smul_of_powOmega2 (SectionNine.blockProjF T Blk)
      (SectionNine.blockProjF_compat T Blk) _ hsigma2
  have hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rhoM),
      (fun i ↦ c.c (gammaGen 2 q (MCompact.mCompactW alpha 0) i)) =
        wPmCompactPhaseNormal 0 p →
      QZero DD rhoM c = wPhCompactWallHandlePhase DD.qbar 0 p := by
    intro p c hc
    exact wPcM_QZero_eq_compactWallPhase_P1_of_headMark rhoM
      (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
      (SectionNine.blockProjF T Blk) (SectionNine.blockProjF_compat T Blk)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hqe hq0 halpha c htauHeadOne hwildHead
      hsigma2Head p hc
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
  let C := wPcMComparison_unramifiedP1_of_headPhase rhoM (scalarActionZmodTwo_triv _)
    hcompat (Vmod_exp2 DD) hwildTwo hqe htauAct hwildAct hsigmaFpf hsigma2 hphase
  refine ⟨{
    phaseEquiv := C.phaseEquiv.trans
      (Equiv.prodUnique (DD.Vmod × DD.Vmod) (Fin 0 → DD.Vmod × DD.Vmod))
    phase_eq := fun x ↦ ?_ }⟩
  rw [C.phase_eq]
  simp [wPhCompactWallHandlePhase, plusFormD]

/-! ## Axiom audit -/

#print axioms wPcM_resolver_smul_of_powOmega2
#print axioms wPcMComparison_boundary_unramifiedP1

end

end GQ2.Dyadic.Instances.WordPhaseCompactMData
