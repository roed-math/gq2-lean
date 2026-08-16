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
Transcription of `RecordBlocks.recBl_mCand_tcocycle`, itself the `M` twin of
`LSquare.tcocycle_of_uniformPushed`.  `1 ≤ α` is new here: the `N` uniform resolver takes it. -/
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
word-side marking route.  Transcription of `RecordBlocks.recBl_mCand_hsep`.  `1 ≤ α` is new
here, from the `N` uniform resolver. -/
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
conjunct 3.  Transcription of `RecordBlocks.recBl_mCand_hrsep`.  `1 ≤ α` is new here, from the
`N` uniform resolver. -/
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
Transcription of `RecordBlocks.recBl_mCand_hpartial`; `1 ≤ α` and `q ≠ 0` enter here through
`NCompact.cardH2_of_uniformPushed`, exactly as on the `M` side. -/
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
Transcription of `RecordBlocks.recBl_mCand_hZcard`.  This one is also what the determinant
bridge needs for its finiteness step, so §2 consumes it too.  `1 ≤ α` is new here, from the `N`
uniform resolver. -/
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

/-- **The Stokes certificate at the compact-`N` candidate, from the uniform residue.**  The `N`
twin of `RecordBlocks.recBl_mCand_stokes_of_uniformPushed`, at the count lane's degree
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

/-- **The `N0` row's `stokes` clause is a theorem, unconditionally at `2 ≤ α`**, at the degree
spelling the row records use.  W85-BLOCKS' per-clause table marks this cell "not attempted here";
it closes with no new hypothesis, because `NCompact.uniformPushedHsimp` is unconditional at
`2 ≤ α` and `2 ≤ α` also discharges the resolver's `1 ≤ α`. -/
theorem wPh_nCand_stokes (hα : 2 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (GammaR (2 + 2 * h) q (nCompactW α h)) (2 + 2 * h) q P nuP
      (standardNumerics (2 + 2 * h))
      (scalarActionZmodTwo ((GammaR (2 + 2 * h) q (nCompactW α h) : Type))) :=
  recBl_stokes_standard_congr (by omega)
    (wPh_nCand_stokes_of_uniformPushed (uniformPushedHsimp hα hqe) (by omega) hq0 hqe)

end NStokes

/-! ## §2 The determinant reduction at the compact-`N` candidate (ticket T1)

The same transcription, of `RecordBlocks` §4.  The trap it names holds verbatim here: the
`G_K`-side clone `affineDeterminant_galK` discharges both Gauss-`Z` clauses internally through
`gaussZResidueDK_{unramified,ramified}`, each of which takes a `TateDualityG` produced only by
`FieldData.tateDualityGalK` and hence gated on an open finite-index embedding into the absolute
Galois group, which is what this campaign is trying to prove.  **No declaration in this module
takes a `TateDualityG`, a `LocalEulerChar` or a `RamifiedCertificate`**, and the words do not
occur in this file outside this paragraph.  The route used is `gaussZResidueK_of_wordPhase`,
which takes no duality at all.

What lands is the reduction, not the supply: after §2 the `N0` row's `determinant` clause
follows from `wPhWordPhaseSupplyN`.  §3 says what that supply would cost. -/

section NDeterminant

open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.NCompact
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2

variable {α h q : ℕ}

set_option linter.unusedVariables false in
/-- **The compact-`N` word-phase supply**: the `N` twin of `RecordBlocks.recBlWordPhaseSupply`,
itself the even-degree analogue of `LSquare.DeterminantWordPhaseSupply`.  Binder for binder the two clauses of
`AffineDeterminantCertificate`, with the already-summed `GaussZResidueK` conclusion replaced by
a word-phase model whose Gauss sum has the required value.  Stated as a conjunction rather than
a structure because both clauses are `Prop`. -/
def wPhWordPhaseSupplyN {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma α h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma α h q) P)
    (compat : ∀ g : (gamma α h q : Type), nuTq q (tame g) = nuP (pro2 g)) : Prop :=
  (letI := scalarActionZmodTwo ((gamma α h q : Type))
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
      (F : BoundaryFrameK q P H E)
      (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
          W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hunram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v = v),
      LSquare.WordPhaseResidueK (sourceBoundaryMapK tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl
        (scalarActionZmodTwo_triv _)
        ((standardNumerics (2 * h + 2)).gaussUnram m))
  ∧ (letI := scalarActionZmodTwo ((gamma α h q : Type))
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
      (F : BoundaryFrameK q P H E)
      (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
          W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v ≠ v),
      LSquare.WordPhaseResidueK (sourceBoundaryMapK tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl
        (scalarActionZmodTwo_triv _)
        ((standardNumerics (2 * h + 2)).gaussRam m))

/-- **The determinant certificate at the compact-`N` candidate, from a word-phase supply.**  The
`N` twin of `RecordBlocks.recBl_mCand_determinant_of_wordPhaseSupply`.  §1's
`wPh_nCand_hZcard` supplies the finiteness of the cocycle group (the `L` proof calls
`hZcard_of_uniformPushed`, which had no `M` counterpart until §3); simplicity and nontriviality
kill the fixed vectors through the generic `hfix_of_simple_nt`; the phase is the only input left.
`2 ≤ α` enters through `NCompact.uniformPushedHsimp`, and also discharges the `1 ≤ α` the `N`
resolver adds. -/
theorem wPh_nCand_determinant_of_wordPhaseSupply (hα : 2 ≤ α) {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma α h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma α h q) P)
    (compat : ∀ g : (gamma α h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (S : wPhWordPhaseSupplyN nuP tame pro2 compat) :
    AffineDeterminantCertificate (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) tame pro2 compat
      (scalarActionZmodTwo ((gamma α h q : Type))) := by
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
  constructor
  · exact fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hunram ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      apply LSquare.gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [wPh_nCand_hZcard (uniformPushedHsimp hα hqe) (by omega) hqe
          (sourceBoundaryMapK tame pro2 compat) F En l hl hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact S.1 T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hunram
  · exact fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hram ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      apply LSquare.gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [wPh_nCand_hZcard (uniformPushedHsimp hα hqe) (by omega) hqe
          (sourceBoundaryMapK tame pro2 compat) F En l hl hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact S.2 T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hram

end NDeterminant


/-! ## §3 The row: `ℚ₂(√−2)` on `N0 2 0`

`RowClauses` §3 states the acceptance shape at `ℚ₂(√5)` and `RecordBlocks` §5 restates it with
the two discharged binders removed.  This section does the same at the pilot row, which is the
`N0 2 0` row `RowClauses` §4 says gets "the identical treatment" but never instantiated.

| `N0 2 0` obligation | before this lane | after |
| --- | --- | --- |
| `cand` `exactLifting` at `Γ_R` | `askCStageVanishing` at `Γ_R` (`rowCl_nCand_exactLifting_iff`) | unchanged |
| `cand` `scalar` at `Γ_R` | discharged (`rowCl_nCand_scalar`) | discharged |
| `cand` `stokes` at `Γ_R` | **open**, never attempted | **discharged**, §1, no new hypothesis |
| `cand` `determinant` at `Γ_R` | **open**, no supplier anywhere | `wPhWordPhaseSupplyN`, §2 |
| `ASK` `exactLifting` at `G_K` | `askCStageVanishing` at `G_K` | unchanged |
| `ASK` `stokes` at `G_K` | discharged | discharged |

So after §1 and §2 the pilot row costs exactly what the `ℚ₂(√5)` row costs: **one word-phase
supply and two instances of one coefficient `Prop`**. -/

section SqrtNegTwoRow

open GQ2.Dyadic.Instances.CanonicalRecords GQ2.Dyadic.Fields
open GQ2.Dyadic.NCompact GQ2.Dyadic.Words TameSpec MarkedCore
open GQ2.Dyadic.SelectedCoreLeavesRN

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `[ℚ₂(√−2) : ℚ₂]` is the pilot row's degree.  The `N` twin of `rowCl_hdeg_sqrtFive`. -/
theorem wPh_hdeg_sqrtNegTwo :
    Module.finrank ℚ_[2] KSqrtNegTwo = (SelectedPresentation.N0 2 0).degree := by
  rw [finrank_KSqrtNegTwo]; rfl

/-- **The `ℚ₂(√−2)` row's residual after this lane.**  Compare `canRec_rowResidual_sqrtNegTwo`,
whose `cand` binder is the whole `CAND` certificate: here the `stokes` and `scalar` clauses are
gone outright, the `exactLifting` clause is the coefficient `Prop`, and the `determinant` clause
is the word-phase supply of §2. -/
theorem wPh_rowResidual_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) {FF : DyadicUnitFiltration KSqrtNegTwo}
    (F : GenAsmFieldInputs KSqrtNegTwo B FF (SelectedPresentation.N0 2 0).degree)
    (Sdet : wPhWordPhaseSupplyN (α := 2) (h := 0) (q := qOf KSqrtNegTwo FF)
      (nNuZtwo 2 0)
      (tameOfSpec (2 + 2 * 0) (qOf KSqrtNegTwo FF) (nCompactW 2 0)
        (genCertNTameSpecializes 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
          (even_qOf KSqrtNegTwo FF)))
      (genCertNPro2 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
        (even_qOf KSqrtNegTwo FF))
      (genCertNCompat 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
        (even_qOf KSqrtNegTwo FF)
        (genCertNTameSpecializes 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
          (even_qOf KSqrtNegTwo FF))
        (nNuZtwo 2 0) (nNuZtwo_sigma 2 0) (nNuZtwo_wild 2 0)))
    (hvanCand : askCStageVanishing (GammaR (2 + 2 * 0) (qOf KSqrtNegTwo FF) (nCompactW 2 0))
      (qOf KSqrtNegTwo FF) (DN 2 0) (nNuZtwo 2 0))
    (hvanK : askCStageVanishing (galKProfinite KSqrtNegTwo) (qOf KSqrtNegTwo FF)
      (genAsmCore (.N0 2 0)) (nNuZtwo 2 0)) :
    ∃ G : GenAsmBranch KSqrtNegTwo B, G.pres = .N0 2 0 ∧ Nonempty (GenAsmRowResidual G F.T) :=
  canRec_rowResidual_N0_of_analytic 2 0 (canRec_branch_sqrtNegTwo B) F
    ((RowClauses.rowCl_nCand_exactLifting_iff (le_refl 2) (qOf_ne_zero KSqrtNegTwo FF)
      (even_qOf KSqrtNegTwo FF)).mpr hvanCand)
    (wPh_nCand_stokes (le_refl 2) (qOf_ne_zero KSqrtNegTwo FF) (even_qOf KSqrtNegTwo FF))
    (RowClauses.rowCl_nCand_scalar (le_refl 2) (qOf_ne_zero KSqrtNegTwo FF)
      (even_qOf KSqrtNegTwo FF))
    (recBl_determinant_standard_congr (by omega)
      (wPh_nCand_determinant_of_wordPhaseSupply (le_refl 2) _ _ _ _ Sdet))
    (askC_exactLiftingSemantics_galK wPh_hdeg_sqrtNegTwo hvanK)
    (askC_stokes_galK wPh_hdeg_sqrtNegTwo)

/-- **The acceptance statement at `ℚ₂(√−2)`.**  The candidate group over the `N0 2 0` word at
`q_K` presents `G_{ℚ₂(√−2)}`, given one word-phase supply and the coefficient `Prop` at each of
the row's two carriers.  The `N` twin of `RecordBlocks.recBl_candidate_equiv_galK_sqrtFive`. -/
theorem wPh_candidate_equiv_galK_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) {FF : DyadicUnitFiltration KSqrtNegTwo}
    (F : GenAsmFieldInputs KSqrtNegTwo B FF (SelectedPresentation.N0 2 0).degree)
    (Sdet : wPhWordPhaseSupplyN (α := 2) (h := 0) (q := qOf KSqrtNegTwo FF)
      (nNuZtwo 2 0)
      (tameOfSpec (2 + 2 * 0) (qOf KSqrtNegTwo FF) (nCompactW 2 0)
        (genCertNTameSpecializes 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
          (even_qOf KSqrtNegTwo FF)))
      (genCertNPro2 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
        (even_qOf KSqrtNegTwo FF))
      (genCertNCompat 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
        (even_qOf KSqrtNegTwo FF)
        (genCertNTameSpecializes 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
          (even_qOf KSqrtNegTwo FF))
        (nNuZtwo 2 0) (nNuZtwo_sigma 2 0) (nNuZtwo_wild 2 0)))
    (hvanCand : askCStageVanishing (GammaR (2 + 2 * 0) (qOf KSqrtNegTwo FF) (nCompactW 2 0))
      (qOf KSqrtNegTwo FF) (DN 2 0) (nNuZtwo 2 0))
    (hvanK : askCStageVanishing (galKProfinite KSqrtNegTwo) (qOf KSqrtNegTwo FF)
      (genAsmCore (.N0 2 0)) (nNuZtwo 2 0)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.N0 2 0).degree (qOf KSqrtNegTwo FF)
        (SelectedPresentation.N0 2 0).word : ProfiniteGrp) : Type) (GalK KSqrtNegTwo)) :=
  RowClauses.rowCl_equiv_of_rowResidual F
    (wPh_rowResidual_sqrtNegTwo B F Sdet hvanCand hvanK)

end SqrtNegTwoRow


/-! ## §4 The even-degree wall-handle phase (ticket T2)

W85-BLOCKS left the supply itself open with a precise diagnosis: the `L` producers
`wordPhaseResidueK_{unramified,ramified}_lSq` run through
`lSqWallHandlePhase_gaussSum_standard{Unram,Ram}`, "which exist only at odd degree `2h + 1`";
the compact word "offers only the unsigned magnitude", and "there are no even-degree sign
pins".  This section builds the missing pins, and in doing so **corrects the shape of the
ticket**.

### The correction: at even degree there is one value, not two

`standardNumerics n` has `gaussUnram m = (-1)^n · 2^(n·m)` and `gaussRam m = 2^(n·m)`.  On the
odd rows these differ in sign, which is why the `L` supply is two computations with two
different targets and why `GammaLUnramifiedPhase` has to compute an Arf invariant (`arf q = 1`
on the unramified branch) to get the minus sign.  **At even degree they are the same integer**
(`wPh_gaussUnram_eq_gaussRam_of_even`).  So W85-BLOCKS §5's "two even-degree wall-handle phase
computations" is one computation consumed twice, and the branch hypotheses `hunram` and `hram`
of `recBlWordPhaseSupply` are not needed to state the target.

### The pin: the even endpoint value is a theorem

The even-degree endpoint normal form is a `plusFormD` head and `h` hyperbolic handle planes,
on `(V × V) × (Fin h → V × V)` rather than the odd rows' `V × (Fin h → V × V)`.  Its Gauss sum
is `Certificates.nCompact_handle_form_gaussSum`, which is form-theoretic (its proof is
`gaussSum_plusFormD` plus `gaussSum_pi_sum`; it takes no word and no handle datum), so it serves
both compact rows.  At `Fintype.card V = 2 ^ (2 * m)` it lands exactly on
`(standardNumerics (2 * h + 2)).gaussRam m`.

The sign is `+1` for a structural reason, not a computation: the head is `plusFormD q q`, whose
second slot is a full polar character sum, so the head is split and its Arf invariant is `0` on
**both** branches.  There is no even-degree analogue of `arf_eq_one_of_zeroCount_sub`, and none
is needed.  This is what makes `gaussUnram = gaussRam` true on the nose at even degree rather
than by accident.

The sign collapse `(-1)^(2h+2) = 1` that W85-BLOCKS §5 named as missing (`Even.neg_one_pow`
"never used anywhere under `GQ2/`") is `wPh_neg_one_pow_even` below. -/

section EvenPhase

open GQ2.QuadraticFp2 GQ2.Dyadic.Certificates

/-- The sign collapse W85-BLOCKS §5 named as absent from the tree. -/
theorem wPh_neg_one_pow_even {n : ℕ} (hn : Even n) : (-1 : ℤ) ^ n = 1 :=
  hn.neg_one_pow

/-- **At even degree the two Gauss targets coincide.**  This is the structural correction to
W85-BLOCKS §5: the even-degree supply carries one value, not two, and the unramified branch
needs no Arf computation. -/
theorem wPh_gaussUnram_eq_gaussRam_of_even {n : ℕ} (hn : Even n) (m : ℕ) :
    (standardNumerics n).gaussUnram m = (standardNumerics n).gaussRam m := by
  show (-1 : ℤ) ^ n * 2 ^ (n * m) = 2 ^ (n * m)
  rw [wPh_neg_one_pow_even hn, one_mul]

/-- The compact rows' degree is even. -/
theorem wPh_even_two_mul_add_two (h : ℕ) : Even (2 * h + 2) := ⟨h + 1, by ring⟩

/-- The two Gauss targets at the compact rows' degree, in the spelling the count lane
produces. -/
theorem wPh_gauss_targets_eq (h m : ℕ) :
    (standardNumerics (2 * h + 2)).gaussUnram m
      = (standardNumerics (2 * h + 2)).gaussRam m :=
  wPh_gaussUnram_eq_gaussRam_of_even (wPh_even_two_mul_add_two h) m

/-- **The even-degree wall-handle phase**: a `plusFormD` head and `h` hyperbolic handle planes.
The even twin of `LSquare.lSqWallHandlePhase`, whose head is a Wall doubling `qDouble q U` on a
single copy of `V`.  The even head takes two copies and carries no Wall operator, which is the
whole reason the even sign is unconditional. -/
def wPhCompactWallHandlePhase {V : Type} [AddCommGroup V] (q : V → ZMod 2) (h : ℕ) :
    (V × V) × (Fin h → V × V) → ZMod 2 :=
  fun p ↦ plusFormD q q p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2

/-- **The even-degree endpoint value, ramified spelling.**  The even twin of
`LSquare.lSqWallHandlePhase_gaussSum_standardRam`.  No Arf hypothesis and no Wall operator
appear, unlike both odd-degree twins. -/
theorem wPh_compactWallHandlePhase_gaussSum_standardRam
    {V : Type} [AddCommGroup V] [Fintype V] {q : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    gaussSum (wPhCompactWallHandlePhase q h)
      = (standardNumerics (2 * h + 2)).gaussRam m := by
  have hb := nCompact_handle_form_gaussSum (V := V) (q := q) hq hns hcard h
  show gaussSum (fun p : (V × V) × (Fin h → V × V) =>
    plusFormD q q p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2) = _
  rw [hb]
  show (2 : ℤ) ^ (2 * m * (h + 1)) = 2 ^ ((2 * h + 2) * m)
  congr 1
  ring

/-- **The even-degree endpoint value, unramified spelling.**  The even twin of
`LSquare.lSqWallHandlePhase_gaussSum_standardUnram`.  Same form, same value: at even degree the
unramified target is the ramified one. -/
theorem wPh_compactWallHandlePhase_gaussSum_standardUnram
    {V : Type} [AddCommGroup V] [Fintype V] {q : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m)) (h : ℕ) :
    gaussSum (wPhCompactWallHandlePhase q h)
      = (standardNumerics (2 * h + 2)).gaussUnram m :=
  (wPh_compactWallHandlePhase_gaussSum_standardRam hq hns hcard h).trans
    (wPh_gauss_targets_eq h m).symm

end EvenPhase


/-! ## §5 The reduction: the even supply is branch-free and word-generic

§4 says the two clauses of `recBlWordPhaseSupply` have the same target.  This section draws the
consequence: the supply follows from a **single** statement with the branch hypothesis deleted,
and that statement mentions the word only through `tame`, `pro2` and `compat`, so it is shared
by every even-degree row rather than being re-stated per word.

That is the honest measure of what W85-BLOCKS §5's residual costs after this lane:

| | odd (`L`) row | even compact rows, before | even compact rows, after |
| --- | --- | --- | --- |
| clauses to supply | 2 (different targets) | 2 (assumed different) | **1** |
| branch hypothesis used | yes (`hunram` forces `arf = 1`) | assumed yes | **no** |
| endpoint value | `lSqWallHandlePhase_gaussSum_standard*` | **absent** | `wPh_compactWallHandlePhase_gaussSum_standard*` (§4) |
| endpoint form | Wall head + `h` planes | absent | `wPhCompactWallHandlePhase` (§4) |
| phase comparison | `sourceWordPhaseComparison_of_lSqUnramifiedHead` | absent | **absent** (§6) |

`wPhBranchFreeSupply` is stated at an arbitrary `Gam : ProfiniteGrp` and an arbitrary degree
`n`, because nothing in it is word-specific once the tame data is fixed: the `L` supply's
apparent word-dependence, which W85-BLOCKS §5 correctly identified as blocking any reuse of
`DeterminantWordPhaseSupply`, lives entirely in the *types* of `tame` and `pro2`, and those are
this definition's parameters. -/

section BranchFree

open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2

set_option linter.unusedVariables false in
/-- **The branch-free word-phase supply**, at an arbitrary carrier and degree.  Compare
`RecordBlocks.recBlWordPhaseSupply`, which is this statement twice, once with `hunram` and the
`gaussUnram` target and once with `hram` and the `gaussRam` target.  At even degree the two
targets agree (§4), so the branch hypotheses carry no information and one clause serves. -/
def wPhBranchFreeSupply {Gam : ProfiniteGrp} {q : ℕ} (n : ℕ) {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom Gam (Tq q))
    (pro2 : ContinuousMonoidHom Gam P)
    (compat : ∀ g : (Gam : Type), nuTq q (tame g) = nuP (pro2 g)) : Prop :=
  letI := scalarActionZmodTwo ((Gam : Type))
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR),
    LSquare.WordPhaseResidueK (sourceBoundaryMapK tame pro2 compat) F
      (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl
      (scalarActionZmodTwo_triv _)
      ((standardNumerics n).gaussRam m)

variable {α h q : ℕ}

/-- **The compact-`M` supply follows from the branch-free one.**  Both clauses of
`RecordBlocks.recBlWordPhaseSupply` are the single branch-free clause, the unramified one after
rewriting its target by §4's `wPh_gauss_targets_eq`. -/
theorem wPh_recBlWordPhaseSupply_of_branchFree {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (MCompact.gamma α h q) (Tq q))
    (pro2 : ContinuousMonoidHom (MCompact.gamma α h q) P)
    (compat : ∀ g : (MCompact.gamma α h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (S : wPhBranchFreeSupply (2 * h + 2) nuP tame pro2 compat) :
    RecordBlocks.recBlWordPhaseSupply nuP tame pro2 compat :=
  ⟨fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl _ ↦ by
    rw [wPh_gauss_targets_eq h m]
    exact S T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl,
   fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl _ ↦
    S T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl⟩

/-- **The compact-`N` supply follows from the same branch-free one.**  The `N` twin of the
previous theorem, at the same statement: `wPhBranchFreeSupply` does not mention the word. -/
theorem wPh_wordPhaseSupplyN_of_branchFree {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (NCompact.gamma α h q) (Tq q))
    (pro2 : ContinuousMonoidHom (NCompact.gamma α h q) P)
    (compat : ∀ g : (NCompact.gamma α h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (S : wPhBranchFreeSupply (2 * h + 2) nuP tame pro2 compat) :
    wPhWordPhaseSupplyN nuP tame pro2 compat :=
  ⟨fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl _ ↦ by
    rw [wPh_gauss_targets_eq h m]
    exact S T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl,
   fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl _ ↦
    S T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl⟩

end BranchFree

/-! ## §6 What is left: the phase comparison, named

After §5 the whole even-degree determinant residual is `wPhBranchFreeSupply`.  This section
strips it to its irreducible core.  `WordPhaseResidueK` asks, per boundary lift, for three
things: a finite model type `W`, a form `Q` on it, and a `SourceWordPhaseComparison` matching
`QZeroBar` with `Q`, together with the value of `gaussSum Q`.  §4 supplies the last three of
those outright once `W` and `Q` are taken to be the even endpoint: `DescData` already carries
`hquad` and `hns` for `qbar`, and the supply's own `hcard` is the remaining input.  So the only
thing still owed is **the comparison itself**, and `wPhCompactPhaseModel` is exactly that.

### Why this one is genuinely even-degree work

On the odd row the comparison is `sourceWordPhaseComparison_of_lSqUnramifiedHead`, assembled
from three ingredients, and each of the three is word-specific:

* `lSqPhaseNormal h`, the normal cochain coordinates, built from `lSqRamifiedNormal`;
* `heisD1_lSqPhaseNormal_eq_zero_unramified`, that those coordinates are `d¹`-closed;
* `lSqFam_unramified_phaseNormalForm`, that every `d¹`-closed cochain is uniquely one of them
  modulo `d⁰`.

None of the three has a compact-word counterpart anywhere in the tree; `grep` for
`phaseNormalForm` and `PhaseNormal` returns `lSq` hits only.  The generic assembler
`sourceWordPhaseComparison_of_lSqHeadNormalForm` that consumes them is itself stated at
`LSquare.gamma h q`, `lSqW h` and `lSqFam h q e`, so it cannot be instantiated at a compact word
either, for the same reason W85-BLOCKS §5 gives for `DeterminantWordPhaseSupply`: the word is in
the types.

What §4 changes is the *shape* of the target, and it changes it in the direction that makes the
missing normal form easier rather than harder.  The odd comparison must produce a model with a
Wall head `qDouble q U`, carrying the operator `U = smulAddEquiv (s ^ ω₂(...))⁻¹` built from the
`sigma`-image, and the unramified branch then has to prove `arf = 1` for that head.  The even
model has no operator and no Arf condition: its head is `plusFormD qbar qbar` on two coordinates.
So the even-degree normal form to be built is the statement that the compact word's `d¹`-closed
cochains are, modulo `d⁰`, two free head coordinates and `h` handle pairs, with no branch split.

That is one named object, and it is the whole distance between this lane's endpoint and a
determinant certificate for the compact rows. -/

section PhaseModel

open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2 GQ2.Dyadic.LSquare

set_option linter.unusedVariables false in
/-- **The one thing still owed**: a source-to-word phase comparison against the even endpoint
form of §4, at every boundary lift of a compact-word carrier.  No Gauss value appears: §4 already
computed it, and `DescData.hquad`/`.hns` already supply that computation's hypotheses. -/
def wPhCompactPhaseModel {Gam : ProfiniteGrp} {q : ℕ} (h : ℕ) {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom Gam (Tq q))
    (pro2 : ContinuousMonoidHom Gam P)
    (compat : ∀ g : (Gam : Type), nuTq q (tame g) = nuP (pro2 g)) : Prop :=
  letI := scalarActionZmodTwo ((Gam : Type))
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
      (SectionNine.blockFrame T Blk hE2).TC),
    letI : Fintype ((blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl).Vmod :=
      Fintype.ofFinite _
    Nonempty (SourceWordPhaseComparison
      ((blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl)
      (rhoPrimeK (SectionNine.blockFrame T Blk hE2)
        (sourceBoundaryMapK tame pro2 compat) F
        ((blockEnrichmentDK T Blk hE2 hq0 hqe F).radData l hl) rfl rho)
      (scalarActionZmodTwo_triv _)
      ((((blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl).Vmod ×
          ((blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl).Vmod) ×
        (Fin h → ((blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl).Vmod ×
          ((blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl).Vmod))
      (wPhCompactWallHandlePhase
        ((blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl).qbar h))

/-- **The branch-free supply from the phase comparison alone.**  Everything except the
comparison is discharged here: the model type and form are §4's even endpoint, its Gauss value
is `wPh_compactWallHandlePhase_gaussSum_standardRam`, and that value's two hypotheses are the
`DescData` fields `hquad` and `hns`. -/
theorem wPh_branchFree_of_phaseModel {Gam : ProfiniteGrp} {q : ℕ} (h : ℕ) {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom Gam (Tq q))
    (pro2 : ContinuousMonoidHom Gam P)
    (compat : ∀ g : (Gam : Type), nuTq q (tame g) = nuP (pro2 g))
    (M : wPhCompactPhaseModel h nuP tame pro2 compat) :
    wPhBranchFreeSupply (2 * h + 2) nuP tame pro2 compat := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl
    rho
  set DD := (blockEnrichmentDK T Blk hE2 hq0 hqe F).descData l hl with hDD
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  refine ⟨(DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod), inferInstance,
    wPhCompactWallHandlePhase DD.qbar h, M T Blk hE2 hq0 hqe F l hl rho, ?_⟩
  exact wPh_compactWallHandlePhase_gaussSum_standardRam DD.hquad DD.hns
    ((Nat.card_eq_fintype_card (α := DD.Vmod)).symm.trans hcard) h

end PhaseModel

/-! ## §7 The two rows at the branch-free binder

§5 lets both acceptance statements be restated over `wPhBranchFreeSupply` instead of over their
own per-word supplies.  That is the sharpest form of the two rows this lane can state: one
`Prop`, shared by both, plus the two instances of the coefficient `Prop` that W84-CLAUSES and
W85-BLOCKS leave standing and that this lane does not touch. -/

section BranchFreeRows

open GQ2.Dyadic.Instances.CanonicalRecords GQ2.Dyadic.FieldBranchId GQ2.Dyadic.Fields
open GQ2.Dyadic.FieldSqrtFive GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.Words TameSpec MarkedCore
open GQ2.Dyadic.SelectedCoreLeavesRN

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **`ℚ₂(√5)` over the branch-free supply.**  `RecordBlocks.recBl_candidate_equiv_galK_sqrtFive`
with its `recBlWordPhaseSupply` binder replaced by §5's. -/
theorem wPh_candidate_equiv_galK_sqrtFive_branchFree [T2Space (GalK KSqrtFive)]
    (B : MarkedRecip R KSqrtFive) {FF : DyadicUnitFiltration KSqrtFive}
    (F : GenAsmFieldInputs KSqrtFive B FF (SelectedPresentation.M0 2 0).degree)
    (Sdet : wPhBranchFreeSupply (2 * 0 + 2) (q := qOf KSqrtFive FF)
      (fieldId_mNuZtwo 2 0 (by omega))
      (tameOfSpec (2 + 2 * 0) (qOf KSqrtFive FF) (Words.MCompact.mCompactW 2 0)
        (mTameSpecializes 2 0 (qOf KSqrtFive FF) (qOf_ne_zero KSqrtFive FF)
          (even_qOf KSqrtFive FF)))
      (mPro2 2 0 (qOf KSqrtFive FF) (by omega) (qOf_ne_zero KSqrtFive FF)
        (even_qOf KSqrtFive FF))
      (mCompat 2 0 (qOf KSqrtFive FF) (by omega) (qOf_ne_zero KSqrtFive FF)
        (even_qOf KSqrtFive FF)
        (mTameSpecializes 2 0 (qOf KSqrtFive FF) (qOf_ne_zero KSqrtFive FF)
          (even_qOf KSqrtFive FF))
        (fieldId_mNuZtwo 2 0 (by omega)) (canRec_mNuZtwo_sigma 2 0 (by omega))
        (canRec_mNuZtwo_wild 2 0 (by omega))))
    (hvanCand : askCStageVanishing
      (GammaR (2 + 2 * 0) (qOf KSqrtFive FF) (Words.MCompact.mCompactW 2 0))
      (qOf KSqrtFive FF) (DM 2 0) (fieldId_mNuZtwo 2 0 (by omega)))
    (hvanK : askCStageVanishing (galKProfinite KSqrtFive) (qOf KSqrtFive FF)
      (genAsmCore (.M0 2 0)) (fieldId_mNuZtwo 2 0 (by omega))) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.M0 2 0).degree (qOf KSqrtFive FF)
        (SelectedPresentation.M0 2 0).word : ProfiniteGrp) : Type) (GalK KSqrtFive)) :=
  RecordBlocks.recBl_candidate_equiv_galK_sqrtFive B F
    (wPh_recBlWordPhaseSupply_of_branchFree _ _ _ _ Sdet) hvanCand hvanK

/-- **`ℚ₂(√−2)` over the same branch-free supply.**  §3 with its `wPhWordPhaseSupplyN` binder
replaced by §5's, which is literally the same statement as the one the `√5` row now takes. -/
theorem wPh_candidate_equiv_galK_sqrtNegTwo_branchFree [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) {FF : DyadicUnitFiltration KSqrtNegTwo}
    (F : GenAsmFieldInputs KSqrtNegTwo B FF (SelectedPresentation.N0 2 0).degree)
    (Sdet : wPhBranchFreeSupply (2 * 0 + 2) (q := qOf KSqrtNegTwo FF)
      (nNuZtwo 2 0)
      (tameOfSpec (2 + 2 * 0) (qOf KSqrtNegTwo FF) (nCompactW 2 0)
        (genCertNTameSpecializes 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
          (even_qOf KSqrtNegTwo FF)))
      (genCertNPro2 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
        (even_qOf KSqrtNegTwo FF))
      (genCertNCompat 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
        (even_qOf KSqrtNegTwo FF)
        (genCertNTameSpecializes 2 0 (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
          (even_qOf KSqrtNegTwo FF))
        (nNuZtwo 2 0) (nNuZtwo_sigma 2 0) (nNuZtwo_wild 2 0)))
    (hvanCand : askCStageVanishing (GammaR (2 + 2 * 0) (qOf KSqrtNegTwo FF) (nCompactW 2 0))
      (qOf KSqrtNegTwo FF) (DN 2 0) (nNuZtwo 2 0))
    (hvanK : askCStageVanishing (galKProfinite KSqrtNegTwo) (qOf KSqrtNegTwo FF)
      (genAsmCore (.N0 2 0)) (nNuZtwo 2 0)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.N0 2 0).degree (qOf KSqrtNegTwo FF)
        (SelectedPresentation.N0 2 0).word : ProfiniteGrp) : Type) (GalK KSqrtNegTwo)) :=
  wPh_candidate_equiv_galK_sqrtNegTwo B F
    (wPh_wordPhaseSupplyN_of_branchFree _ _ _ _ Sdet) hvanCand hvanK

end BranchFreeRows

/-! ## Axiom audit

26 declarations, `#print axioms` on each, recorded in the file.

* **22 std-3** (`propext`, `Classical.choice`, `Quot.sound`), and `wPh_even_two_mul_add_two`
  pins `propext` alone: everything this lane proves, including all of §1, §2, §4, §5 and §6.
  In particular **the whole even-degree phase layer is std-3**, and so is the reduction of both
  compact supplies to one branch-free statement.
* **4 with campaign axioms**, all of them row statements: the three `ℚ₂(√−2)` ones
  (`wPh_rowResidual_sqrtNegTwo`, `wPh_candidate_equiv_galK_sqrtNegTwo`,
  `wPh_candidate_equiv_galK_sqrtNegTwo_branchFree`) carry std-3 plus
  `{tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated,
  absGalQ2_localEulerCharacteristic, hilbertSymbol_normCriterion_finiteDyadic,
  relativeStiefelWhitney_dyadic}`, and `wPh_candidate_equiv_galK_sqrtFive_branchFree` carries
  that set **plus `peripheralCyclotomicAction`**.  All of it comes through the general theorem
  and the rows' arithmetic inputs; §5's reduction adds nothing.

**Where the five-versus-six comes from.**  The `√5` set is checked against
`RecordBlocks.recBl_candidate_equiv_galK_sqrtFive`: identical, so restating the determinant
binder over `wPhBranchFreeSupply` is axiom-neutral.  The pilot row's acceptance statement costs
five campaign axioms where the `M0 2 0` row costs six.  This is **not** a discovery of this
lane: `CanonicalRecords.lean`'s own pin prose already records that `canRec_branch_sqrtNegTwo`
carries the four-axiom even-route endpoint set and "that set plus `peripheralCyclotomicAction`"
sits on the other three branch data.  What §3 and §7 add is only that the gap survives all the
way to the row conclusion, which had not been instantiated before. -/

section AxiomPins

#print axioms wPh_nCand_tcocycle
#print axioms wPh_nCand_hsep
#print axioms wPh_nCand_hrsep
#print axioms wPh_nCand_hpartial
#print axioms wPh_nCand_hZcard
#print axioms wPh_nCand_stokes_of_uniformPushed
#print axioms wPh_nCand_stokes
#print axioms wPhWordPhaseSupplyN
#print axioms wPh_nCand_determinant_of_wordPhaseSupply
#print axioms wPh_hdeg_sqrtNegTwo
#print axioms wPh_rowResidual_sqrtNegTwo
#print axioms wPh_candidate_equiv_galK_sqrtNegTwo
#print axioms wPh_neg_one_pow_even
#print axioms wPh_gaussUnram_eq_gaussRam_of_even
#print axioms wPh_even_two_mul_add_two
#print axioms wPh_gauss_targets_eq
#print axioms wPhCompactWallHandlePhase
#print axioms wPh_compactWallHandlePhase_gaussSum_standardRam
#print axioms wPh_compactWallHandlePhase_gaussSum_standardUnram
#print axioms wPhBranchFreeSupply
#print axioms wPh_recBlWordPhaseSupply_of_branchFree
#print axioms wPh_wordPhaseSupplyN_of_branchFree
#print axioms wPhCompactPhaseModel
#print axioms wPh_branchFree_of_phaseModel
#print axioms wPh_candidate_equiv_galK_sqrtFive_branchFree
#print axioms wPh_candidate_equiv_galK_sqrtNegTwo_branchFree

end AxiomPins

end GQ2.Dyadic.Instances.WordPhase
