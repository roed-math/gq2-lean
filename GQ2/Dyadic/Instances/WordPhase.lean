/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Instances.RecordBlocks
import GQ2.Dyadic.Instances.N0M0CompactBranches

/-!
# The word-phase supply at the compact rows  (dyadic campaign, lane W86-PHASE)

W85-BLOCKS put two things at the compact-`M` candidate: the four Stokes conjuncts, discharged
outright, and the determinant certificate, reduced to `recBlWordPhaseSupply`.  It left two
items for this lane, and this module works both.

* **§1 and §2, the `N` twins.**  The compact-`N` row gets the same two treatments.  Everything
  the `M` transcription used has an `N` counterpart, so §1 and §2 are transcriptions of
  `RecordBlocks` §3 and §4 with `nCompactFam` for `mCompactFam`, `NCompact.uniformPushedHsimp`
  for `MCompact.uniformPushedHsimp` and `Count.resolvesAt_and_endpoint_nCompactFam_uniformHeis`
  for the `M` resolver.  One binder genuinely differs and is carried honestly: the `N` uniform
  resolver takes `1 ≤ α` and the `M` one does not, so every `N` conjunct carries `1 ≤ α`.  At
  `2 ≤ α`, where the rows sit, it is free.

* **§3, the word-phase supply itself.**  `recBlWordPhaseSupply` and its `N` twin are the
  even-degree analogue of what `LSquare.affineDeterminantCertificate_of_wordPhaseSupply`
  consumes on the odd side, and the tame binder bakes the word in, so no instantiation of the
  `L` supply can serve.  §3 records what the even-degree wall analysis needs and where the tree
  stops short of it.

The degree transports `recBl_stokes_standard_congr` and `recBl_determinant_standard_congr` are
reused from `RecordBlocks`; they are word-agnostic and were already stated at general `Gam`.

Sections are added as the lane lands them; the axiom pins at the end carry the honest split.
-/

namespace GQ2.Dyadic.Instances.WordPhase

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Instances
open GQ2.Dyadic.Instances.RecordBlocks

/-! ## §1 The Stokes conjuncts at the compact-`N` candidate (ticket T1)

W85-BLOCKS §3 named this "the obvious first W86 item" and said all three inputs exist.  They do,
and the transcription goes through with one honest difference.

| what the `M` proof uses | `N` counterpart | same shape? |
| --- | --- | --- |
| `Count.resolvesAt_and_endpoint_mCompactFam_uniformHeis` | `…_nCompactFam_uniformHeis` | **no**: the `N` one takes `1 ≤ α` |
| `MCompact.degree` | `NCompact.degree` | yes, identical statement |
| `MCompact.uniformPushedHsimp` | `NCompact.uniformPushedHsimp` | yes, both unconditional at `2 ≤ α`, `Even q` |
| `MCompact.cardH2_of_uniformPushed` | `NCompact.cardH2_of_uniformPushed` | yes, `1 ≤ α`, `q ≠ 0`, `Even q` |
| `MCompact.datumRho_surjective` | `NCompact.datumRho_surjective` | the `N` one needs **less**: no `1 ≤ α` |
| `isAdmissibleMarkedPresentation_gammaR` | same, word-generic | yes |

So the four conjuncts below carry `1 ≤ α` where the `M` twins carry it only on `hpartial`.  The
extra binder comes from the resolver, not from the row, and `2 ≤ α` discharges it. -/

section NStokes

open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.NCompact
open GQ2.Dyadic.Certificates GQ2.CardH2GammaA TameSpec

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

variable {α h q : ℕ}

/-- **Conjunct 1 at the compact-`N` candidate**: the `T`-cocycle count at every recursion frame.
Transcription of `LSquare.tcocycle_of_uniformPushed`. -/
theorem wPh_nCand_tcocycle (hsimp : UniformPushedHsimp α h q) (hα : 1 ≤ α) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
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
  letI : DistribMulAction ((gamma α h q : Type)) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((gamma α h q : Type)) (Additive ↥D.T) := by
    constructor
    have hfac :
        (fun p : ((gamma α h q : Type)) × Additive ↥D.T => p.1 • p.2) =
          (fun p : (RF.YB ⧸ D.M) × Additive ↥D.T => p.1 • p.2) ∘
            (fun p : ((gamma α h q : Type)) × Additive ↥D.T => (rho p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  have hb := Count.resolvesAt_and_endpoint_nCompactFam_uniformHeis
    (C := RF.YB ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D) (α := α) (h := h) (q := q) hα hqe
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (RF.YB ⧸ D.M))))
      (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact Count.tcocycle_cardN rho (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) hres
    (radT_add_self D)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ => rfl))
    (rhoPrimeK_surjective RF b F D rfl ρ) (NCompact.degree h)
    (hsimp (RF.YB ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D)) hb.2

/-- **Conjunct 2 at the compact-`N` candidate**: the `(T^∨)^C` separation clause, via the
word-side marking route.  Transcription of `LSquare.hsep_of_uniformPushed`. -/
theorem wPh_nCand_hsep (hsimp : UniformPushedHsimp α h q) (hα : 1 ≤ α) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l hl))
    (ρ : BoundaryLiftsK b F RF.TC)
    (c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    (hvan : letI := scalarActionZmodTwo ((gamma α h q : Type))
      ∀ chi : ↥(TCharC (En.radData l hl)),
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c = 0) :
    TLiftable (descSigma_spec En l hl Dsc) c := by
  let D := En.radData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  have hb := Count.resolvesAt_and_endpoint_nCompactFam_uniformHeis
    (C := RF.YB ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D) (α := α) (h := h) (q := q) hα hqe
  have hres2 : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (RF.YB ⧸ D.M))))
      (WordLift (ZMod 2) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisScal_injective
  have hresT : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent (RF.YB ⧸ D.M))))
      (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact Count.hsep_field_goal_marking b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (scalarActionZmodTwo _) (scalarActionZmodTwo_triv _)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) (fun _ => rfl)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ => rfl))
    hres2 hresT (hsimp (RF.YB ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D))
    hb.2 c hvan

/-- Right separation for the descent module at the compact-`N` candidate: the fork feeding
conjunct 3.  Transcription of `LSquare.hrsep_of_uniformPushed`. -/
theorem wPh_nCand_hrsep (hsimp : UniformPushedHsimp α h q) (hα : 1 ≤ α) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    letI : TopologicalSpace (En.descData l hl).Vmod := ⊥
    haveI : DiscreteTopology (En.descData l hl).Vmod := ⟨rfl⟩
    letI : DistribMulAction ((gamma α h q : Type)) (En.descData l hl).Vmod :=
      DistribMulAction.compHom (En.descData l hl).Vmod
        (rho0 (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    letI : TopologicalSpace (ElemDual (En.descData l hl).Vmod) := ⊥
    haveI : DiscreteTopology (ElemDual (En.descData l hl).Vmod) := ⟨rfl⟩
    IsRightSeparating ((gamma α h q : Type)) (En.descData l hl).Vmod := by
  let D := En.radData l hl
  let DD := En.descData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction ((gamma α h q : Type)) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod (rho0 DD rho)
  letI : TopologicalSpace (ElemDual DD.Vmod) := ⊥
  haveI : DiscreteTopology (ElemDual DD.Vmod) := ⟨rfl⟩
  letI : TopologicalSpace DD.C0 := ⊥
  haveI : DiscreteTopology DD.C0 := ⟨rfl⟩
  letI := scalarActionZmodTwo DD.C0
  let theta := Count.rho0Continuous DD rho
  have hcompat : ∀ (g : ((gamma α h q : Type))) (a : DD.Vmod), g • a = theta g • a :=
    fun _ _ => rfl
  haveI : ContinuousSMul ((gamma α h q : Type)) (ElemDual DD.Vmod) := by
    constructor
    have hfac :
        (fun p : ((gamma α h q : Type)) × ElemDual DD.Vmod => p.1 • p.2) =
          (fun p : DD.C0 × ElemDual DD.Vmod => p.1 • p.2) ∘
            (fun p : ((gamma α h q : Type)) × ElemDual DD.Vmod => (theta p.1, p.2)) := by
      funext p
      exact elemDual_compat theta hcompat p.1 p.2
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := Count.resolvesAt_and_endpoint_nCompactFam_uniformHeis
    (C := DD.C0) (A := DD.Vmod) (Vmod_exp2 DD) (α := α) (h := h) (q := q) hα hqe
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift (ZMod 2) DD.C0) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) DD.C0) (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisScal_injective
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift DD.Vmod DD.C0) := by
    let incl : ContinuousMonoidHom (WordLift DD.Vmod DD.C0) (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift (ElemDual DD.Vmod) DD.C0) := by
    let incl : ContinuousMonoidHom
        (WordLift (ElemDual DD.Vmod) DD.C0) (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisDual, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisDual_injective
  have hsurj : Function.Surjective theta :=
    LSquare.rho0Continuous_surjective DD rho (rhoPrimeK_surjective RF b F D rfl ρ)
  have hwild := isWildTwo_of_gammaGen theta hsurj (fun _ => rfl)
  have hd := hsimp DD.C0 theta DD.Vmod (Vmod_exp2 DD)
  have hsd : IsSelfDualN (2 * h + 2)
      (fun g => theta (gammaGen (2 + 2 * h) q (nCompactW α h) g))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent DD.C0))) DD.Vmod :=
    Count.isSelfDualN_of_stokesDuality (NCompact.degree h) hd
      (lower_rel theta (fun _ => rfl)
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) hresP) hb.2
  exact Count.isRightSeparating_of_selfDualN theta hcompat (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) hwild
    hresS hresP hresD hb.1 hsd hb.2 (Vmod_exp2 DD)

/-- **Conjunct 3 at the compact-`N` candidate**: the nonzero-character obstruction.
Transcription of `LSquare.hpartial_of_uniformPushed`; `1 ≤ α` and `q ≠ 0` enter here, through
`MCompact.cardH2_of_uniformPushed`. -/
theorem wPh_nCand_hpartial (hsimp : UniformPushedHsimp α h q) (hα : 1 ≤ α) (hq0 : q ≠ 0)
    (hqe : Even q) {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l hl))
    (ρ : BoundaryLiftsK b F RF.TC) (chi : ↥(TCharC (En.radData l hl)))
    (hchi : chi ≠ 0) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    ∃ c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ),
      betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c ≠
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi
          (0 : VCocycle (En.descData l hl)
            (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) :=
  Count.hpartial_field_goal b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (cardH2_of_uniformPushed hsimp hα hq0 hqe)
    (wPh_nCand_hrsep hsimp hα hqe b F En l hl ρ) chi hchi

/-- **Conjunct 4 at the compact-`N` candidate**: the simple nontrivial `V`-cocycle count.
Transcription of `LSquare.hZcard_of_uniformPushed`.  This one is also what the determinant
bridge needs for its finiteness step, so §4 consumes it too. -/
theorem wPh_nCand_hZcard (hsimp : UniformPushedHsimp α h q) (hα : 1 ≤ α) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
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
  letI : DistribMulAction ((gamma α h q : Type)) DD.Vmod :=
    DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  haveI : ContinuousSMul ((gamma α h q : Type)) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((gamma α h q : Type)) × DD.Vmod => p.1 • p.2) =
          (fun p : RF.YC × DD.Vmod => p.1 • p.2) ∘
            (fun p : ((gamma α h q : Type)) × DD.Vmod => (ρ.1.1 p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI := scalarActionZmodTwo RF.YC
  have hb := Count.resolvesAt_and_endpoint_nCompactFam_uniformHeis
    (C := RF.YC) (A := DD.Vmod) (Vmod_exp2 DD) (α := α) (h := h) (q := q) hα hqe
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent RF.YC)))
      (WordLift DD.Vmod RF.YC) := by
    let incl : ContinuousMonoidHom (WordLift DD.Vmod RF.YC) (HeisLift DD.Vmod RF.YC) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hsimple' : IsSimpleModTwo RF.YC DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    exact ⟨nontrivial_of_ne v 0 hv, hsimple⟩
  exact Count.hZcardN ρ.1.1
    (fun g v => congrArg (fun c : RF.YC => c • v)
      (rho0_descData_rhoPrimeK b F En l hl ρ g))
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (nCompactW α h)) hres
    (Vmod_exp2 DD) (isWildTwo_of_gammaGen ρ.1.1 ρ.1.2 (fun _ => rfl)) ρ.1.2
    (NCompact.degree h) (hsimp RF.YC ρ.1.1 DD.Vmod (Vmod_exp2 DD)) hb.2 hsimple' hnt

/-- **The Stokes certificate at the compact-`N` candidate, from the uniform residue.**  The `M`
twin of `LSquare.stokesDualityCertificate_of_uniformPushed`, at the count lane's degree
spelling. -/
theorem wPh_nCand_stokes_of_uniformPushed (hsimp : UniformPushedHsimp α h q) (hα : 1 ≤ α)
    (hq0 : q ≠ 0) (hqe : Even q) {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2))
      (scalarActionZmodTwo ((gamma α h q : Type))) :=
  ⟨fun b F En l hl ρ => wPh_nCand_tcocycle hsimp hα hqe b F En l hl ρ,
   fun b F En l hl Dsc ρ c hvan => wPh_nCand_hsep hsimp hα hqe b F En l hl Dsc ρ c hvan,
   fun b F En l hl Dsc ρ chi hchi =>
    wPh_nCand_hpartial hsimp hα hq0 hqe b F En l hl Dsc ρ chi hchi,
   fun b F En l hl hsimple hVne hnt ρ =>
    wPh_nCand_hZcard hsimp hα hqe b F En l hl hsimple hVne hnt ρ⟩

/-- **The `M0` row's `stokes` clause is a theorem, unconditionally at `2 ≤ α`**, at the degree
spelling the row records use.  This is the clause W84-CLAUSES left open, and it closes with no
new hypothesis: `MCompact.uniformPushedHsimp` is already unconditional at `2 ≤ α`. -/
theorem wPh_nCand_stokes (hα : 2 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (GammaR (2 + 2 * h) q (nCompactW α h)) (2 + 2 * h) q P nuP
      (standardNumerics (2 + 2 * h))
      (scalarActionZmodTwo ((GammaR (2 + 2 * h) q (nCompactW α h) : Type))) :=
  recBl_stokes_standard_congr (by omega)
    (wPh_nCand_stokes_of_uniformPushed (uniformPushedHsimp hα hqe) (by omega) hq0 hqe)

end NStokes

end GQ2.Dyadic.Instances.WordPhase
