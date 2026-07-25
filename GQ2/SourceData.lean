/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Prop89Close
import GQ2.GaussZ.GammaAD

/-!
# The pluggable source interface: `SourceData`  (the SourceData refactor, R30)

The two-source assembly (`thm_4_2`, `prop_8_9`, `prop_8_9_of`) pins its candidate slot to
`Γ_A` through the `BoundaryMaps` A-side fields and the `_gammaA` supply lemmas.  This file
extracts that slot into a single structure `SourceData`, so that a second presented source
(the note's `Γ_R`) can be plugged in beside `G_ℚ₂` with **zero further refactoring**: R32
builds `sourceR : SourceData` and instantiates `thm_4_2_of_sources` (`GQ2/ThmFourTwo.lean`).

## Contents

* `sourceBoundaryMap` — the eq. (27) bundling `b_Γ : Γ → ∂bd` of a tame/pro-2 pair (the
  `BoundaryMaps.bA` construction, factored out so structure fields can name it).
* `SourceData` — the source group `Γ` (bundled `ProfiniteGrp`, the R31a carrier decision),
  its four marked generators, the boundary fields of eq. (27)/Prop 3.10/Prop 3.14 **including
  the promoted `ker_pro2`** (the recon's 12 + 1), and the seven supply-obligation families
  (the recon's (ii) list = R31's worklist), each in the exact ∀-shape of its `_gammaA`
  witness so the `Γ_A` instance is the untouched lemma.
* `BoundaryMaps.sourceA` — the `Γ_A` instance: `BoundaryMaps` A-fields + `_gammaA` lemmas.
* `terminal_count_eq_of_sources` — the §9.1 terminal count over an abstract source
  (`SectionNine.terminal_count_eq`'s two-source assembly, replayed through the
  source-generic bridges `boundaryLifts_equiv_qlifts`/`qlifts_equiv_commonLifts`).
* `gaussZ_obtain_blockD_of_sources` — the shared-`G0` obtain over an abstract source
  (`SectionNine.gaussZ_obtain_blockD` replayed: `m` and the head dichotomy are
  source-independent; the source contributes exactly the two dichotomy leaves
  `gaussZ_unramified`/`gaussZ_ramified` at the **externally given** `G0 = ∓2^m`).
* `prop_8_9_of_sources` — `SectionEight.prop_8_9_of_source` at a bundled `SourceData`.

## Import discipline

This file must stay **plain-import** (non-`module`): it imports the §8 stack
(`Prop89Close` and below), which is plain-import, and `module`-style files cannot import
plain files (the R31a pitfall; precedent: `GQ2/Roe/Prop23.lean`, `GQ2/Roe/Supply.lean`).

Axioms: **none introduced** — every statement here is assembled from proved material; the
axiom footprints of the consumers are unchanged (the R30 regression gate).
-/

namespace GQ2

open SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

/-- **The boundary map `b_Γ : Γ → ∂bd` of eq. (27)**, bundled from a tame/pro-2 pair with
the Prop 3.14 ν-compatibility — the `BoundaryMaps.bA` construction, factored out so that
`SourceData` fields can refer to the map determined by the structure's own fields.
Definitionally equal to `B.bA` at `(B.tameA, B.pro2A, B.compatA)`. -/
noncomputable def sourceBoundaryMap {Γ : ProfiniteGrp} (tame : ContinuousMonoidHom Γ Ttame)
    (pro2 : ContinuousMonoidHom Γ PiBd)
    (compat : ∀ g : Γ, nuT (tame g) = nuTwo (pro2 g)) :
    ContinuousMonoidHom Γ ↥boundarySubgroup :=
  ⟨(tame.toMonoidHom.prod pro2.toMonoidHom).codRestrict boundarySubgroup
      fun g => compat g,
    (tame.continuous_toFun.prodMk pro2.continuous_toFun).subtype_mk _⟩

-- The named hypothesis binders in the obligation fields are interface documentation for
-- R31/R32 (they mirror the `_gammaA` lemma signatures); the unused-variable linter would
-- flag them, so it is scoped off for this one declaration.
set_option linter.unusedVariables false in
/-- **The pluggable source** (the SourceData refactor): everything the two-source assembly
consumes about the candidate slot.  Data fields = the eq. (27) boundary interface of a
presented source (Prop 3.10 / Prop 3.14, pinned by generator values as for `Γ_A`), with
`ker_pro2` **promoted to a field** (the recon's 12 + 1; `Γ_A` derives it as
`SectionNine.ker_pro2A`, `Γ_R` from its max-pro-2 identification).  Prop fields = the seven
supply-obligation families, each in the exact ∀-shape of its `_gammaA` witness, so
`BoundaryMaps.sourceA` is assembled from the untouched lemmas and `sourceR` from R31's.  -/
structure SourceData where
  /-- The source group, as a bundled profinite group (the R31a carrier decision: all
  topology/group instances flow from `ProfiniteGrp`). -/
  Γ : ProfiniteGrp
  /-- The marked generator `σ` of the source presentation. -/
  sigma : Γ
  /-- The marked generator `τ`. -/
  tau : Γ
  /-- The marked generator `x₀`. -/
  x0 : Γ
  /-- The marked generator `x₁`. -/
  x1 : Γ
  /-- The tame quotient map (eq. (27), tame component; Prop 3.2/Prop 3.14). -/
  tame : ContinuousMonoidHom Γ Ttame
  /-- The maximal pro-2 quotient map (eq. (27), pro-2 component; Prop 3.10). -/
  pro2 : ContinuousMonoidHom Γ PiBd
  /-- Prop 3.14's ν-compatibility: `ν_t ∘ tame = ν₂ ∘ pro2` (what lands `b_Γ` in `∂bd`). -/
  compat : ∀ g : Γ, nuT (tame g) = nuTwo (pro2 g)
  /-- Generator pinning (Prop 3.14's proof): `tame σ = σ`. -/
  tame_sigma : tame sigma = tameSigma
  /-- Generator pinning: `tame τ = τ`. -/
  tame_tau : tame tau = tameTau
  /-- Generator pinning: `tame x₀ = 1`. -/
  tame_x0 : tame x0 = 1
  /-- Generator pinning: `tame x₁ = 1`. -/
  tame_x1 : tame x1 = 1
  /-- Generator pinning (Prop 3.10): `pro2 σ = σ`. -/
  pro2_sigma : pro2 sigma = piSigma
  /-- Generator pinning: `pro2 τ = 1`. -/
  pro2_tau : pro2 tau = 1
  /-- Generator pinning: `pro2 x₀ = x₀`. -/
  pro2_x0 : pro2 x0 = piX0
  /-- Generator pinning: `pro2 x₁ = x₁`. -/
  pro2_x1 : pro2 x1 = piX1
  /-- Eq. (27): joint surjectivity of `b_Γ : Γ ↠ ∂bd`. -/
  surj : Function.Surjective
    (fun g : Γ => (⟨(tame g, pro2 g), compat g⟩ : ↥boundarySubgroup))
  /-- **The promoted field** (recon 12 + 1): `pro2` is *the* maximal pro-2 quotient map —
  its kernel is the pro-2 kernel of the maximal pro-p quotient API.  (`Γ_A`:
  `SectionNine.ker_pro2A`; consumed by the §9.1 terminal identification.) -/
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 Γ
  /-- The ambient `ZMod 2`-scalar action of the source (trivial, by `htriv` below) — the
  instance the (140)/Gauss-`Z` layers are stated at (`Γ_A`: the global instance of
  `GQ2/RStage/GammaA.lean`). -/
  smulZmod2 : DistribMulAction ↥Γ (ZMod 2)
  /-- Continuity of the ambient scalar action. -/
  contSMulZmod2 : letI := smulZmod2; ContinuousSMul ↥Γ (ZMod 2)
  /-- The ambient scalar action is trivial (`Γ_A`: `RStageGammaA.htriv_gammaA`). -/
  htriv : letI := smulZmod2; ∀ (γ : ↥Γ) (m : ZMod 2), γ • m = m
  /-- **(ii.1) topological finite generation** (`Γ_A`:
  `gammaA_topologicallyFinitelyGenerated`; `Γ_R`:
  `gammaR_topologicallyFinitelyGenerated`, R31a). -/
  tfg : ∃ s : Finset (Γ : Type),
    (Subgroup.closure (s : Set (Γ : Type))).topologicalClosure = ⊤
  /-- **(ii.2) Lemma 8.2**: `#Hom_cont(Γ, 𝔽₂) = 8` (`Γ_A`: `lemma_8_2_gammaA`; `Γ_R`:
  `lemma_8_2_R`, R31a). -/
  hom8 : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8
  /-- **(ii.5, leaf) `#H²(Γ, 𝔽₂) = 2`** at the ambient (trivial) action (`Γ_A`:
  `CardH2GammaA.card_H2_gammaA`). -/
  cardH2 : letI := smulZmod2; Nat.card (H2 Γ (ZMod 2)) = 2
  /-- **(ii.3) the `M`-stage multiplicity** (props 5.15/5.16): `#LiftsOver(ρ) = |M_B|²`
  over every lower boundary lift (`Γ_A`: `RecursionFrame.liftsOver_card_gammaA`). -/
  liftsOver_card : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (ρ : BoundaryLifts b F RF.TC),
    Nat.card (RF.LiftsOver b F ρ) = (Nat.card ↥RF.MB) ^ 2
  /-- **(ii.4) Lemma 8.6 (half-torsor count)** ⟦lem-radicaledge⟧: with a nonzero radical
  edge, exactly half of the `M`-lifts of a lower epimorphism satisfy the central relation
  (`Γ_A`: `lemma_8_6_gammaA`). -/
  lem86 : ∀ {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg), D.NoDescent →
    ∀ (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)), Function.Surjective ρ →
      2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ)
  /-- **(ii.5, assembled) the (136) stage at the block frame** (`Γ_A`:
  `CardH2GammaA.stageR136_gammaA`, built from `cardH2` through the generic
  `stageR136`-builders). -/
  stageR136 : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E),
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCount b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * ((blockFrameImpl T Blk hE2).mB b F l : ℤ)
            - exactImageCount b F (blockFrameImpl T Blk hE2).TB)
  /-- **(ii.6) the `T`-cocycle count** in the `muZero` closed form (`Γ_A`:
  `Phase140GammaA.tcocycle_card_gammaA`). -/
  tcocycle_card : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC),
    Nat.card (TCocycle (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = Nat.card (Additive ↥(En.radData l h).T) ^ 2
        * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
            (ElemDual (Additive ↥(En.radData l h).T)))
  /-- **(ii.6) the `(T^∨)^C`-separation**: a `V`-coordinate whose `χ`-obstructions all
  vanish is `T`-liftable (`Γ_A`: `Phase140GammaA.hsep_gammaA`). -/
  hsep : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLifts b F RF.TC)
    (c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)),
    (∀ χ : ↥(TCharC (En.radData l h)),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
      TLiftable (descSigma_spec En l h Dsc) c
  /-- **(ii.6) nondegeneracy of the obstruction pairing in the character** (`Γ_A`:
  `Phase140GammaA.hpartial_gammaA`). -/
  hpartial : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLifts b F RF.TC)
    (χ : ↥(TCharC (En.radData l h))), χ ≠ 0 →
    ∃ c : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
        ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
  /-- **(ii.6) the `V`-cocycle count** `#Z¹_{Γ,ρ'}(V) = #V²` under the simple nontrivial
  `Y_C`-action (`Γ_A`: `Phase140GammaA.hZcard_gammaA`). -/
  hZcard : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∀ W : AddSubgroup En.Vmod, (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ v : En.Vmod, v ≠ 0) →
    (∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v) →
    ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (VCocycle (En.descData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
        = Nat.card En.Vmod * Nat.card En.Vmod
  /-- **(ii.7) the Gauss-`Z` residue, unramified head** (the (83)-evaluation at the
  **externally given** `G0 = −2^m` — the recon's shared-`G0` seam): at the head-inflated
  enrichment, with the head dichotomy `F.alpha τ`-trivial (`Γ_A`:
  `SectionNine.gaussZResidueD_gammaA_unramified`). -/
  gaussZ_unramified : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (F : BoundaryFrame H E)
    (hsimple : ∀ W : AddSubgroup (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hunram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha tameTau • v = v),
    letI := smulZmod2
    GaussZResidue (sourceBoundaryMap tame pro2 compat) F
      (SectionNine.blockEnrichmentD T Blk hE2 F) l h (-(2 ^ m : ℤ))
  /-- **(ii.7) the Gauss-`Z` residue, ramified head** (`G0 = +2^m`; `Γ_A`:
  `SectionNine.gaussZResidueD_gammaA_ramified`). -/
  gaussZ_ramified : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (F : BoundaryFrame H E)
    (hsimple : ∀ W : AddSubgroup (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha tameTau • v ≠ v),
    letI := smulZmod2
    GaussZResidue (sourceBoundaryMap tame pro2 compat) F
      (SectionNine.blockEnrichmentD T Blk hE2 F) l h (2 ^ m : ℤ)

namespace SourceData

variable (S : SourceData)

/-- The source's boundary map `b_Γ : Γ → ∂bd` (eq. (27)); at `sourceA` this is
definitionally `B.bA`. -/
noncomputable def b : ContinuousMonoidHom S.Γ ↥boundarySubgroup :=
  sourceBoundaryMap S.tame S.pro2 S.compat

@[simp] theorem b_apply_coe (g : S.Γ) : (S.b g : Ttame × PiBd) = (S.tame g, S.pro2 g) :=
  rfl

theorem b_surjective : Function.Surjective S.b := S.surj

/-- Surjectivity of the source's pro-2 coordinate, derived from the joint surjectivity
`surj` (the `terminal_count_eq` `hpro2A_surj` derivation, source-generic). -/
theorem pro2_surjective : Function.Surjective S.pro2 := fun p => by
  obtain ⟨t, ht⟩ := SectionThree.nuT_surjective (nuTwo p)
  obtain ⟨g, hg⟩ := S.surj ⟨(t, p), ht⟩
  exact ⟨g, congrArg (fun x : ↥boundarySubgroup => x.val.2) hg⟩

end SourceData

/-- **The `Γ_A` instance of the source interface**: the `BoundaryMaps` A-side fields and
the untouched `_gammaA` supply lemmas, assembled.  (`ker_pro2` is `SectionNine.ker_pro2A`,
the derivation from the generator values + `prop_3_10_gammaA`; the scalar action is the
global trivial instance of `GQ2/RStage/GammaA.lean`.) -/
noncomputable def BoundaryMaps.sourceA (B : BoundaryMaps) : SourceData where
  Γ := GammaA
  sigma := quotientMk NA univMarking.σ
  tau := quotientMk NA univMarking.τ
  x0 := quotientMk NA univMarking.x₀
  x1 := quotientMk NA univMarking.x₁
  tame := B.tameA
  pro2 := B.pro2A
  compat := B.compatA
  tame_sigma := B.tameA_sigma
  tame_tau := B.tameA_tau
  tame_x0 := B.tameA_x0
  tame_x1 := B.tameA_x1
  pro2_sigma := B.pro2A_sigma
  pro2_tau := B.pro2A_tau
  pro2_x0 := B.pro2A_x0
  pro2_x1 := B.pro2A_x1
  surj := B.surjA
  ker_pro2 := SectionNine.ker_pro2A B
  smulZmod2 := inferInstance
  contSMulZmod2 := inferInstance
  htriv := RStageGammaA.htriv_gammaA
  tfg := gammaA_topologicallyFinitelyGenerated
  hom8 := lemma_8_2_gammaA
  cardH2 := CardH2GammaA.card_H2_gammaA
  liftsOver_card := fun RF b F ρ => RF.liftsOver_card_gammaA b F ρ
  lem86 := fun D hedge ρ hρ => lemma_8_6_gammaA D hedge ρ hρ
  stageR136 := fun hE2 hRK hR2 b F => CardH2GammaA.stageR136_gammaA hE2 hRK hR2 b F
  tcocycle_card := fun b F En l h ρ => Phase140GammaA.tcocycle_card_gammaA b F En l h ρ
  hsep := fun b F En l h Dsc ρ c hc => Phase140GammaA.hsep_gammaA b F En l h Dsc ρ c hc
  hpartial := fun b F En l h Dsc ρ χ hχ =>
    Phase140GammaA.hpartial_gammaA b F En l h Dsc ρ χ hχ
  hZcard := fun b F En l h hsimple hVne hnt ρ =>
    Phase140GammaA.hZcard_gammaA b F En l h hsimple hVne hnt ρ
  gaussZ_unramified := fun T Blk =>
    SectionNine.gaussZResidueD_gammaA_unramified T Blk (B := B)
  gaussZ_ramified := fun T Blk =>
    SectionNine.gaussZResidueD_gammaA_ramified T Blk (B := B)

/-- The load-bearing definitional identity of the flip: `sourceA`'s boundary map **is**
`B.bA` (by `rfl`), so re-deriving the `Γ_A` capstones from the `_of_sources` forms changes
no statement. -/
@[simp] theorem BoundaryMaps.sourceA_b (B : BoundaryMaps) : B.sourceA.b = B.bA := rfl

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- **The §9.1 terminal count over an abstract source** (the SourceData refactor):
`SectionNine.terminal_count_eq` with the candidate slot abstracted — the source enters only
through `b`, `pro2`, `surj` and the promoted `ker_pro2`, via the source-generic bridges
`boundaryLifts_equiv_qlifts` / `qlifts_equiv_commonLifts` at the (source-independent)
Lemma 9.2 splitting datum. -/
theorem terminal_count_eq_of_sources (S : SourceData) (B : BoundaryMaps)
    (F : BoundaryFrame H E) [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (hstack : SectionSeven.IsScalarStack T.LY) :
    exactImageCount S.b F T = exactImageCount B.bF F T := by
  obtain ⟨M, hMn, hModd, hMtwo⟩ := SectionNine.head_two_nilpotent F
  obtain ⟨Ntil, hNn, hNodd, hNQ2, hNL, _hNcomm, hmapM, hNLsup⟩ :=
    SectionNine.lemma_9_2_core T.piY T.piY_surjective T.LY T.ker_piY T.isPGroup_two hstack
      M hModd hMtwo
  set D : SectionNine.L92 H Y := ⟨T.piY, T.piY_surjective, T.LY, T.ker_piY, M, hMn, hModd,
    Ntil, hNn, hNodd, hNL, hmapM, hNLsup, hNQ2⟩ with hD
  have hDpi : D.piY = T.piY := by rw [hD]
  have hbS : Function.Surjective S.b := S.b_surjective
  have hbF : Function.Surjective B.bF := fun x => by
    obtain ⟨g, hg⟩ := B.surjF x
    exact ⟨g, Subtype.ext (by rw [B.bF_apply_coe]; exact congrArg Subtype.val hg)⟩
  have hbpro2S : ∀ g, (S.b g).val.2 = S.pro2 g := fun g => by rw [S.b_apply_coe]
  have hbpro2F : ∀ g, (B.bF g).val.2 = B.pro2F g := fun g => by rw [B.bF_apply_coe]
  show Nat.card (BoundaryLifts S.b F T) = Nat.card (BoundaryLifts B.bF F T)
  calc Nat.card (BoundaryLifts S.b F T)
      = Nat.card (SectionNine.QLifts F T hE2 D S.b) :=
        SectionNine.boundaryLifts_equiv_qlifts F T hE2 D hDpi S.b hbS
    _ = Nat.card (SectionNine.CommonLifts F T hE2 D) :=
        SectionNine.qlifts_equiv_commonLifts F T hE2 D S.b hbS S.pro2 S.pro2_surjective
          hbpro2S S.ker_pro2
    _ = Nat.card (SectionNine.QLifts F T hE2 D B.bF) :=
        (SectionNine.qlifts_equiv_commonLifts F T hE2 D B.bF hbF B.pro2F
          B.pro2F_surjective hbpro2F B.ker_pro2F).symm
    _ = Nat.card (BoundaryLifts B.bF F T) :=
        (SectionNine.boundaryLifts_equiv_qlifts F T hE2 D hDpi B.bF hbF).symm

/-- **The shared-`G0` obtain over an abstract source** (the SourceData refactor, the
recon's external-`G0` seam): `SectionNine.gaussZ_obtain_blockD` replayed — the exponent `m`
(from the nonsingular form, source-independent) and the head dichotomy (on
`F.alpha τ`, source-independent) are decided once, and each source contributes exactly its
dichotomy leaf at the resulting `G0 = ∓2^m`: the abstract slot through
`gaussZ_unramified`/`gaussZ_ramified`, the `G_ℚ₂` slot through the proved local twins. -/
theorem gaussZ_obtain_blockD_of_sources {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    [IsTopologicalGroup AbsGalQ2]
    (hE2 : ∀ e : E, e ^ 2 = 1) (S : SourceData) (B : BoundaryMaps)
    (F : BoundaryFrame H E) (R : LocalReciprocity) (horient : TameUnitOrientation R B.tameF)
    (hsimple : ∀ W : AddSubgroup (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod), g • v ≠ v) :
    letI := S.smulZmod2
    ∃ G0 : ℤ,
      (∀ (l : (SectionNine.blockFrame T Blk hE2).DR)
        (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR),
        GaussZResidue S.b F (SectionNine.blockEnrichmentD T Blk hE2 F) l h G0) ∧
      (∀ (l : (SectionNine.blockFrame T Blk hE2).DR)
        (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR),
        GaussZResidue B.bF F (SectionNine.blockEnrichmentD T Blk hE2 F) l h G0) := by
  classical
  letI := blockPS_commGroup Blk
  letI := SectionNine.headAct T Blk
  by_cases hex : ∃ l : (SectionNine.blockFrame T Blk hE2).DR,
      l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR
  · obtain ⟨l₀, hl₀⟩ := hex
    have hl₀' : l₀.1 ≠ Blk.frattiniK := fun heq => hl₀ (Subtype.ext heq)
    -- `m` from the nonsingular form on `V` (A-4.6b), `l`-free through `#V`
    obtain ⟨m, hm, hcard⟩ := exists_one_le_card_eq_two_pow_of_nonsingular
      (blockQbar T Blk F.alpha F.alpha_surjective l₀ hl₀')
      (blockHquad T Blk F.alpha F.alpha_surjective l₀ hl₀')
      (blockHns T Blk F.alpha F.alpha_surjective l₀ hl₀')
      (SectionNine.blockPS_exp2 T Blk) hVne
    -- the ρ/source-uniform head dichotomy
    by_cases hd : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P),
        F.alpha tameTau • v = v
    · exact ⟨-(2 ^ m : ℤ),
        fun l h => S.gaussZ_unramified T Blk hE2 F hsimple hVne hnt m hm hcard l h hd,
        fun l h => SectionNine.gaussZResidueD_local_unramified T Blk hE2 B F
          (tateDuality 2) hsimple hVne hnt m hm hcard l h hd⟩
    · push Not at hd
      exact ⟨(2 ^ m : ℤ),
        fun l h => S.gaussZ_ramified T Blk hE2 F hsimple hVne hnt m hm hcard l h hd,
        fun l h => SectionNine.gaussZResidueD_local_ramified T Blk hE2 B F
          (tateDuality 2) R horient hsimple hVne hnt m hm hcard l h hd⟩
  · push Not at hex
    exact ⟨0, fun l h => absurd (hex l) h, fun l h => absurd (hex l) h⟩

/-- **Proposition 8.9 over a bundled source** (the SourceData refactor): the recon's
"`prop_8_9` runs over a `SourceData` instance" form — `SectionEight.prop_8_9_of_source` fed
from the structure's fields.  R32 consumes this at `sourceR`; the `Γ_A` capstone
`SectionEight.prop_8_9` is (equivalently) the same statement at `B.sourceA`, re-derived in
`GQ2/Prop89Close.lean` directly from the unbundled form. -/
theorem prop_8_9_of_sources (S : SourceData) (B : BoundaryMaps) {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (En : (blockFrameImpl T Blk hE2).Enrichment) (F : BoundaryFrame H E)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    [IsTopologicalGroup AbsGalQ2]
    (hfgF : ∃ s : Finset AbsGalQ2,
      (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (hheadS : Function.Surjective (fun γ : S.Γ => (F.frameMap (S.b γ)).1))
    (hheadF : Function.Surjective (fun γ : AbsGalQ2 => (F.frameMap (B.bF γ)).1))
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : (blockFrameImpl T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : (blockFrameImpl T Blk hE2).YC) (v : En.Vmod), g • v ≠ v)
    (G0 : ℤ)
    (hGaussZS : letI := S.smulZmod2;
      ∀ (l : (blockFrameImpl T Blk hE2).DR)
        (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR), GaussZResidue S.b F En l h G0)
    (hGaussZF : ∀ (l : (blockFrameImpl T Blk hE2).DR)
      (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR), GaussZResidue B.bF F En l h G0) :
    ∃ (μ : ℕ) (G0' : ℤ) (DT : Type) (_ : Fintype DT)
      (phase : (l : (blockFrameImpl T Blk hE2).DR) →
        l ≠ (blockFrameImpl T Blk hE2).zeroDR → DT →
          CentralCover (blockFrameImpl T Blk hE2).YC),
      0 < Nat.card DT ∧
        ClosedRecursion (blockFrameImpl T Blk hE2) S.b F μ G0' DT phase ∧
          ClosedRecursion (blockFrameImpl T Blk hE2) B.bF F μ G0' DT phase := by
  letI := S.smulZmod2
  letI := S.contSMulZmod2
  exact prop_8_9_of_source B T Blk hE2 En F S.b S.htriv S.tfg S.hom8 S.cardH2
    (fun hRK hR2 => S.stageR136 hE2 hRK hR2 S.b F)
    (fun D hedge ρ hρ => S.lem86 D hedge ρ hρ)
    (S.liftsOver_card _ S.b F)
    (fun l h ρ => S.tcocycle_card S.b F En l h ρ)
    (fun l h Dsc ρ c hc => S.hsep S.b F En l h Dsc ρ c hc)
    (fun l h Dsc ρ χ hχ => S.hpartial S.b F En l h Dsc ρ χ hχ)
    (fun l h ρ => S.hZcard S.b F En l h hsimple hVne hnt ρ)
    hfgF hheadS hheadF hsimple hVne hnt G0 hGaussZS hGaussZF

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (27) = ⟦eq-boundarymap⟧
  * Lemma 8.2 = ⟦lem-scalarcount⟧
  * Lemma 8.6 = ⟦lem-radicaledge⟧
  * Lemma 9.2 = ⟦lem-oddsplit⟧
  * Prop 3.10 = ⟦prop-pro2⟧
  * Prop 3.14 = ⟦prop-compatiblemarking⟧
  * Proposition 8.9 = ⟦thm-closedrecursion⟧ (= theorem 8.17 in current tex)
-/
