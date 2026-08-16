/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcCandidateScalar
import GQ2.Dyadic.Count.LocalDuality

/-!
# Full Stokes certificate for the corrected procyclic-N candidate

The selected procyclic-N residue is already an unconditional `UniformHsimp` once an honest
`NpcDisplayFor` package is fixed.  This file translates that word-side residue into the four
count clauses of `StokesDualityCertificate` and packages the result at the displayed and
semantic arbitrary-unit carriers.  There is deliberately no frozen tied Npc row.
-/

namespace GQ2.Dyadic.Instances.NpcCandidateStokes

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Instances
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.CardH2GammaA
open GQ2.Dyadic.NProcyclic GQ2.Dyadic.NProcyclicUnram

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

variable {alpha r h q : ℕ} {d : EtaData}

/-- The T-cocycle count for a displayed procyclic-N candidate. -/
theorem npcCand_tcocycle (hsimp : UniformHsimp alpha r h q d)
    (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (TCocycle (En.radData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) =
      (standardNumerics (2 * h + 2)).tMult
          (Nat.card (Additive ↥(En.radData l hl).T)) *
        Nat.card (fixedPts (RF.YB ⧸ (En.radData l hl).M)
          (ElemDual (Additive ↥(En.radData l hl).T))) := by
  let D := En.radData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI : TopologicalSpace (Additive ↥D.T) := ⊥
  haveI : DiscreteTopology (Additive ↥D.T) := ⟨rfl⟩
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type)) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma alpha r h q d : Type)) (Additive ↥D.T) := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r h q d : Type)) × Additive ↥D.T => p.1 • p.2) =
          (fun p : (RF.YB ⧸ D.M) × Additive ↥D.T => p.1 • p.2) ∘
            (fun p : ((displayedGamma alpha r h q d : Type)) × Additive ↥D.T =>
              (rho p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  have hb := resolvesAt_and_endpoint_uniformHeis
    (C := RF.YB ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D)
    (alpha := alpha) (r := r) (h := h) (q := q) hα hqe d
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (RF.YB ⧸ D.M)))
      (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact Count.tcocycle_cardN rho (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (npcW alpha r h d)) hres
    (radT_add_self D)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ => rfl))
    (rhoPrimeK_surjective RF b F D rfl ρ) (nCompact_degree h)
    (hsimp (RF.YB ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D)) hb.2

/-- The T-dual separation clause for a displayed procyclic-N candidate. -/
theorem npcCand_hsep (hsimp : UniformHsimp alpha r h q d)
    (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l hl))
    (ρ : BoundaryLiftsK b F RF.TC)
    (c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    (hvan : letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
      ∀ chi : ↥(TCharC (En.radData l hl)),
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c = 0) :
    TLiftable (descSigma_spec En l hl Dsc) c := by
  let D := En.radData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  have hb := resolvesAt_and_endpoint_uniformHeis
    (C := RF.YB ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D)
    (alpha := alpha) (r := r) (h := h) (q := q) hα hqe d
  have hres2 : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (RF.YB ⧸ D.M)))
      (WordLift (ZMod 2) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisScal_injective
  have hresT : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent (RF.YB ⧸ D.M)))
      (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact Count.hsep_field_goal_marking b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (scalarActionZmodTwo _) (scalarActionZmodTwo_triv _)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (npcW alpha r h d))
    (fun _ => rfl)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ => rfl))
    hres2 hresT (hsimp (RF.YB ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D))
    hb.2 c hvan

/-- Right separation for the descent module of a displayed procyclic-N candidate. -/
theorem npcCand_hrsep (hsimp : UniformHsimp alpha r h q d)
    (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC) :
    letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
    letI : TopologicalSpace (En.descData l hl).Vmod := ⊥
    haveI : DiscreteTopology (En.descData l hl).Vmod := ⟨rfl⟩
    letI : DistribMulAction ((displayedGamma alpha r h q d : Type))
        (En.descData l hl).Vmod :=
      DistribMulAction.compHom (En.descData l hl).Vmod
        (rho0 (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    letI : TopologicalSpace (ElemDual (En.descData l hl).Vmod) := ⊥
    haveI : DiscreteTopology (ElemDual (En.descData l hl).Vmod) := ⟨rfl⟩
    IsRightSeparating ((displayedGamma alpha r h q d : Type))
      (En.descData l hl).Vmod := by
  let D := En.radData l hl
  let DD := En.descData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
  haveI := scalarActionZmodTwo_continuousSMul
    ((displayedGamma alpha r h q d : Type))
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type)) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod (rho0 DD rho)
  letI : TopologicalSpace (ElemDual DD.Vmod) := ⊥
  haveI : DiscreteTopology (ElemDual DD.Vmod) := ⟨rfl⟩
  letI : TopologicalSpace DD.C0 := ⊥
  haveI : DiscreteTopology DD.C0 := ⟨rfl⟩
  letI := scalarActionZmodTwo DD.C0
  let theta := Count.rho0Continuous DD rho
  have hcompat : ∀ (g : ((displayedGamma alpha r h q d : Type))) (a : DD.Vmod),
      g • a = theta g • a := fun _ _ => rfl
  haveI : ContinuousSMul ((displayedGamma alpha r h q d : Type))
      (ElemDual DD.Vmod) := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r h q d : Type)) × ElemDual DD.Vmod =>
          p.1 • p.2) =
          (fun p : DD.C0 × ElemDual DD.Vmod => p.1 • p.2) ∘
            (fun p : ((displayedGamma alpha r h q d : Type)) × ElemDual DD.Vmod =>
              (theta p.1, p.2)) := by
      funext p
      exact elemDual_compat theta hcompat p.1 p.2
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_uniformHeis
    (C := DD.C0) (A := DD.Vmod) (Vmod_exp2 DD)
    (alpha := alpha) (r := r) (h := h) (q := q) hα hqe d
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent DD.C0))
      (WordLift (ZMod 2) DD.C0) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) DD.C0)
        (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisScal_injective
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent DD.C0))
      (WordLift DD.Vmod DD.C0) := by
    let incl : ContinuousMonoidHom (WordLift DD.Vmod DD.C0)
        (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent DD.C0))
      (WordLift (ElemDual DD.Vmod) DD.C0) := by
    let incl : ContinuousMonoidHom (WordLift (ElemDual DD.Vmod) DD.C0)
        (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisDual, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisDual_injective
  have hsurj : Function.Surjective theta := by
    intro c0
    obtain ⟨bb, hbb⟩ := DD.hpiC0 c0
    obtain ⟨g, hg⟩ :=
      rhoPrimeK_surjective RF b F D rfl ρ (QuotientGroup.mk bb)
    exact ⟨g, (rho0_apply_of_rep DD rho g bb hg.symm).trans hbb⟩
  have hwild := isWildTwo_of_gammaGen theta hsurj (fun _ => rfl)
  have hd := hsimp DD.C0 theta DD.Vmod (Vmod_exp2 DD)
  have hsd : IsSelfDualN (2 * h + 2)
      (fun g => theta (gammaGen (2 + 2 * h) q (npcW alpha r h d) g))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent DD.C0)) DD.Vmod :=
    Count.isSelfDualN_of_stokesDuality (nCompact_degree h) hd
      (lower_rel theta (fun _ => rfl)
        (isAdmissibleMarkedPresentation_gammaR
          (2 + 2 * h) q (npcW alpha r h d)) hresP) hb.2
  exact Count.isRightSeparating_of_selfDualN theta hcompat (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (npcW alpha r h d)) hwild
    hresS hresP hresD hb.1 hsd hb.2 (Vmod_exp2 DD)

/-- The nonzero-character obstruction clause for a displayed procyclic-N candidate. -/
theorem npcCand_hpartial (hsimp : UniformHsimp alpha r h q d)
    (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l hl))
    (ρ : BoundaryLiftsK b F RF.TC) (chi : ↥(TCharC (En.radData l hl)))
    (hchi : chi ≠ 0) :
    letI := scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))
    ∃ c : VCocycle (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl ρ),
      betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c ≠
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi
          (0 : VCocycle (En.descData l hl)
            (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) :=
  Count.hpartial_field_goal b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _)
    (cardH2_of_uniformPushed hsimp hα hqe)
    (npcCand_hrsep hsimp hα hqe b F En l hl ρ) chi hchi

/-- The simple nontrivial V-cocycle count for a displayed procyclic-N candidate. -/
theorem npcCand_hZcard (hsimp : UniformHsimp alpha r h q d)
    (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR)
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (VCocycle (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) =
      Nat.card En.Vmod *
        (standardNumerics (2 * h + 2)).h1Mult (Nat.card En.Vmod) := by
  let D := En.radData l hl
  let DD := En.descData l hl
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction RF.YC DD.Vmod :=
    (inferInstance : DistribMulAction RF.YC En.Vmod)
  letI : DistribMulAction ((displayedGamma alpha r h q d : Type)) DD.Vmod :=
    DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  haveI : ContinuousSMul ((displayedGamma alpha r h q d : Type)) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((displayedGamma alpha r h q d : Type)) × DD.Vmod => p.1 • p.2) =
          (fun p : RF.YC × DD.Vmod => p.1 • p.2) ∘
            (fun p : ((displayedGamma alpha r h q d : Type)) × DD.Vmod =>
              (ρ.1.1 p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI := scalarActionZmodTwo RF.YC
  have hb := resolvesAt_and_endpoint_uniformHeis
    (C := RF.YC) (A := DD.Vmod) (Vmod_exp2 DD)
    (alpha := alpha) (r := r) (h := h) (q := q) hα hqe d
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent RF.YC))
      (WordLift DD.Vmod RF.YC) := by
    let incl : ContinuousMonoidHom (WordLift DD.Vmod RF.YC)
        (HeisLift DD.Vmod RF.YC) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hsimple' : IsSimpleModTwo RF.YC DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    exact ⟨nontrivial_of_ne v 0 hv, hsimple⟩
  exact Count.hZcardN ρ.1.1
    (fun g v => congrArg (fun c : RF.YC => c • v)
      (rho0_descData_rhoPrimeK b F En l hl ρ g))
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR
      (2 + 2 * h) q (npcW alpha r h d)) hres
    (Vmod_exp2 DD)
    (isWildTwo_of_gammaGen ρ.1.1 ρ.1.2 (fun _ => rfl)) ρ.1.2
    (nCompact_degree h)
    (hsimp RF.YC ρ.1.1 DD.Vmod (Vmod_exp2 DD)) hb.2 hsimple' hnt

/-- The full Stokes certificate for a displayed procyclic-N candidate, from its uniform
pushed residue. -/
theorem npcCand_stokes_of_uniformPushed
    (hsimp : UniformHsimp alpha r h q d)
    (hα : 1 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (displayedGamma alpha r h q d) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2))
      (scalarActionZmodTwo ((displayedGamma alpha r h q d : Type))) :=
  ⟨fun b F En l hl ρ => npcCand_tcocycle hsimp hα hqe b F En l hl ρ,
   fun b F En l hl Dsc ρ c hvan =>
    npcCand_hsep hsimp hα hqe b F En l hl Dsc ρ c hvan,
   fun b F En l hl Dsc ρ chi hchi =>
    npcCand_hpartial hsimp hα hqe b F En l hl Dsc ρ chi hchi,
   fun b F En l hl hsimple hVne hnt ρ =>
    npcCand_hZcard hsimp hα hqe b F En l hl hsimple hVne hnt ρ⟩

/-- The displayed Stokes certificate supplied by every honest procyclic-N display package. -/
theorem npcCand_stokes_displayed {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (hα : 2 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (displayedGamma alpha r h q d.data)
      (2 * h + 2) q P nuP (standardNumerics (2 * h + 2))
      (scalarActionZmodTwo
        ((displayedGamma alpha r h q d.data : Type))) := by
  obtain ⟨z, hz⟩ := d.exists_toPadic_eq_one_add_two_mul
  exact npcCand_stokes_of_uniformPushed
    (uniformPushedHsimp hα hqe z hz) (by omega) hqe

/-- The semantic arbitrary-unit Stokes certificate for every valid selected procyclic-N
display. -/
theorem npcCand_stokes {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta)
    (hα : 2 ≤ alpha) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (gamma alpha r h q eta)
      (2 * h + 2) q P nuP (standardNumerics (2 * h + 2))
      (scalarActionZmodTwo
        ((gamma alpha r h q eta : Type))) := by
  rw [gamma_eq_display alpha r h q d]
  exact npcCand_stokes_displayed d hα hqe

#print axioms npcCand_tcocycle
#print axioms npcCand_hsep
#print axioms npcCand_hrsep
#print axioms npcCand_hpartial
#print axioms npcCand_hZcard
#print axioms npcCand_stokes_of_uniformPushed
#print axioms npcCand_stokes_displayed
#print axioms npcCand_stokes

end

end GQ2.Dyadic.Instances.NpcCandidateStokes
