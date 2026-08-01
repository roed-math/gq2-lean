/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Numerics
import GQ2.Dyadic.Recursion.Prop89Close
import GQ2.Dyadic.Recursion.BlockHeadDat
import GQ2.MStageCount
import GQ2.RStage.Local
import GQ2.Phase140.Local
import GQ2.GaussZ.FinalD
import GQ2.Roe.Main

/-!
# The two-sided degree-`n` source record: `SourceDataN`  (dyadic campaign, ticket SD2)

Boundary-abstracted, numerically parameterized clone of `GQ2.SourceData`
(`GQ2/SourceData.lean:75-268`), per SD1 memo §1.2/§2/§8, atop the SD-R1–3 spine clone
`GQ2/Dyadic/Recursion/`.  This is the record both sides of packet Thm 11.1
(`thm:source-abstract`) instantiate; SD3's `thm_source_generic` quantifies over two of them.

## Field-by-field delta versus the frozen model  (memo §1.2)

* **dropped** — the 4 marked generators + 8 pinning fields (`SourceData.lean:80-108`; memo Q2,
  adopted): consumed nowhere, and rank never enters structurally (MC1 §(ix)).  The
  marked-generator documentation lives in the instantiations, which have honest generators.
  No `SourceMarking` companion is defined here: with the pro-2 slot abstract there are no
  canonical marked points of `P` to pin against (`piSigma`/`piX0`/`piX1` are `ℚ₂`-slot data),
  so the companion would need marked `P`-points as extra data no consumer wants — not
  "trivially cheap", hence skipped per the Q2 fallback's own condition.
* **retyped** — `tame` lands in F3's `Tq q` (`GQ2/Dyadic/TameQuotientK.lean:257`), `pro2` in
  the abstract marked pro-2 slot `P` (memo Q4), the boundary is `boundarySubgroupQ q nuP`
  (`GQ2/Dyadic/TameBoundary.lean`), and every obligation family re-targets the SD-R clone
  types (`BoundaryFrameK`, `BoundaryLiftsK`, `LiftsOverK`, `rhoPrimeK`, `mBK`,
  `exactImageCountK`, `GaussZResidueK`, `blockEnrichmentDK`); the head-dichotomy element is
  `tqTau q`.
* **revalued** — the five numeric leaves read `SN : SourceNumerics n`
  (`GQ2/Dyadic/Recursion/Numerics.lean`, landed by SD-R1; this file is its designated
  consumer): `homCard = SN.homScalar` (model: `hom8 = 8`),
  `liftsOver_card = SN.mMult #M_B` (model: `#M_B ^ 2`),
  `tcocycle_card = SN.tMult #T * #fixedPts` (model: `#T ^ 2 * …`),
  `hZcard = #V * SN.h1Mult #V` (model: `#V * #V` — the SD-R3 shape rule: the **outer** `#V`
  is `#B¹` and stays literal, the **inner** factor is the one that moves, memo §1.3),
  `gaussZ_* = SN.gaussUnram m` / `SN.gaussRam m` (model: `∓2^m`).
* **unchanged** — everything else, verbatim: `compat`/`surj`/`ker_pro2` (retargeted types
  only), the scalar-action triple, `tfg` (a record field per FG1 Route D), `cardH2 = 2`
  (degree-independent), `lem86`, `stageR136`, `hsep`, `hpartial`.  There is **no
  `eulerChar` field** (LG1 ruling: derived, never an input).

## The `n = 1` story  (all definitional except the two documented value bridges)

The instances `sourceA_N`/`sourceR_N`/`sourceF_N` reproduce `BoundaryMaps.sourceA`
(`GQ2/SourceData.lean:297`), `sourceR` (`GQ2/Roe/Main.lean`), and — new at `n = 1`, the
two-sided flip's genuinely new object — the `G_ℚ₂` record, from the verified `*_local` leaf
pack (memo §3.1/§3.3).  Probes verified in-session at the SD-R3 head:

* `boundarySubgroupQ 2 nuTwo = boundarySubgroup := rfl` (P1) and `tqTau 2 = tameTau := rfl`,
  so the boundary interface fields of the old records are accepted **without transport**;
* `blockEnrichmentDK T Blk hE2 hq0 hqe F = blockEnrichmentD T Blk hE2 F.toBoundaryFrame
  := rfl` — the choice chain (`prop_7_4K`/`mForm`/κ⁰ existentials) is definitionally the
  model's at `q = 2` because every `∃`-spec is boundary-free, so `Exists.choose` agrees by
  proof irrelevance;
* `GaussZResidueK … = GaussZResidue …` and `mBK … = ….mB …` are `rfl` at `q = 2`
  (with `rhoPrimeK_eq`/`liftsOverK_eq`/`exactImageCountK_eq` from the spine);
* the only non-`rfl` seams are the two `standardNumerics 1` value bridges of memo §1.4
  (`pow_one` is not `rfl`): `hZcard` composes with `standardNumerics_one_h1Mult`, and
  `gaussZ_*` rewrite by `standardNumerics_one_gaussUnram`/`_gaussRam` — each ≤ 2 lines,
  exactly the memo §8 acceptance budget.

`sourceF_N` carries the `(R, horient)` reciprocity binders and the
`[CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]` instance binders — precisely
the binders memo §3.1 removes from the two-sided statement and moves into the
`S₂`-instantiation.  This is the `n = 1` case of what the ASK ticket does at general `K`
(memo §3.3's supply map: B10-K for the tame side, the marked-core certificate for the pro-2
side, LG5's `local_gauss_K` for the Gauss leaves).

## Import discipline

Plain-import (memo §5): sits with `GQ2/Roe/Main.lean` as a leaf over the plain §8/§9 stack
and the plain `Recursion/` clone tree; the `module`-style F3 suppliers arrive through the
clone imports.  `SourceNumerics`/`standardNumerics` are **re-exported by import** here (the
`GQ2.Dyadic.Recursion.Numerics` line): SD3/ASK reach them through this file.

Axioms: **no new axioms; none of the nine obligations as axioms.**  Print check performed
per declaration (measured, not budgeted): the factory/record/API layer and `sourceA_N` +
`sourceA_N_b` print exactly std-3 — **equal to `BoundaryMaps.sourceA`'s own print**;
`sourceR_N` + `sourceR_N_b` print std-3 ∪ {B3c `dyadicOrientation`, B5 `localReciprocity`,
B8 `peripheralCyclotomicAction`} — **equal to the frozen `sourceR`'s own print** (B-Lab
stays the `hBLab` binder, never an axiom); `sourceF_N` + `sourceF_N_b` print
std-3 ∪ {B1, B6, B7, B9, B11a} — **equal to the frozen `thm_4_2` capstone's own print**,
i.e. packaging the B-side as a record costs not one axiom beyond the capstone it serves.
No frozen file is touched, so the capstone prints themselves cannot move.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

/-! ## The boundary-map factory  (eq. (27) at the `K`-boundary) -/

/-- **The boundary map `b_Γ : Γ → ∂` of eq. (27) at the `K`-boundary**, bundled from a
tame/pro-2 pair with the ν-compatibility.  Clone of `GQ2.sourceBoundaryMap`
(`GQ2/SourceData.lean:56`) at `boundarySubgroupQ q nuP`; at `q = 2`, `P := PiBd`,
`nuP := nuTwo` it **is** the model's construction (`sourceBoundaryMapK_two` below), which is
what makes `sourceA_N.b = B.bA` and `(sourceR_N hBLab).b = (sourceR hBLab).b` hold by
`rfl`. -/
noncomputable def sourceBoundaryMapK {q : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} {Γ : ProfiniteGrp}
    (tame : ContinuousMonoidHom Γ (Tq q)) (pro2 : ContinuousMonoidHom Γ P)
    (compat : ∀ g : Γ, nuTq q (tame g) = nuP (pro2 g)) :
    ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP) :=
  ⟨(tame.toMonoidHom.prod pro2.toMonoidHom).codRestrict (boundarySubgroupQ q nuP)
      fun g => compat g,
    (tame.continuous_toFun.prodMk pro2.continuous_toFun).subtype_mk _⟩

/-- The factory at `q = 2` on a `ℚ₂`-typed pair **is** `GQ2.sourceBoundaryMap` — `rfl`
(probe P1b at the construction level). -/
theorem sourceBoundaryMapK_two {Γ : ProfiniteGrp} (tame : ContinuousMonoidHom Γ Ttame)
    (pro2 : ContinuousMonoidHom Γ PiBd)
    (compat : ∀ g : Γ, nuT (tame g) = nuTwo (pro2 g)) :
    sourceBoundaryMapK (q := 2) (nuP := nuTwo) tame pro2 compat
      = GQ2.sourceBoundaryMap tame pro2 compat := rfl

/-- **`ν_{t,q} : T_q ↠ Z₂` is surjective**: its range is closed (continuous image of a
compact group) and contains the topological generator `ν_{t,q}(σ_q) = 1`.  The general-`q`
sibling of `GQ2.SectionThree.nuT_surjective` (`GQ2/Prop32.lean:525`), by the same one-liner;
it feeds `SourceDataN.pro2_surjective` exactly as the model's feeds
`SourceData.pro2_surjective`. -/
theorem nuTq_surjective (q : ℕ) : Function.Surjective (nuTq q) :=
  SectionThree.surjective_of_mem_range_topGen (nuTq q) SectionThree.topGen_ztwo
    ⟨tqSigma q, nuTq_tqSigma q⟩

/-! ## The record -/

-- The named hypothesis binders in the obligation fields are interface documentation for the
-- instantiating lanes (they mirror the supply-lemma signatures); the unused-variable linter
-- would flag them, so it is scoped off for this one declaration (the model's discipline,
-- `GQ2/SourceData.lean:67`).
set_option linter.unusedVariables false in
/-- **The two-sided degree-`n` pluggable source** (SD1 memo §1.2): everything the
parameterized recursion consumes about one source, at the `K`-boundary
`boundarySubgroupQ q nuP` of the abstract marked pro-2 slot `(P, hP, nuP)` (memo Q4), with
the five moving numeric leaves valued in the shared `SN : SourceNumerics n` (memo Q3/Q5).

Both sources of a comparison share one `SN`, so no equality side conditions between the two
sources' numerics ever arise (memo §3.2).  Data fields = the eq. (27) boundary interface
with `ker_pro2` promoted, exactly as in the model; Prop fields = the seven supply-obligation
families in the exact `∀`-shapes of the SD-R clone consumers
(`closedRecursionK_of_source`, `GQ2/Dyadic/Recursion/Prop89Close.lean:208`, and SD3's
terminal/Gauss lanes), so instantiation is by the untouched supply lemmas. -/
structure SourceDataN (n q : ℕ) (P : ProfiniteGrp) (hP : IsProP 2 P)
    (nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n) where
  /-- The source group, as a bundled profinite group (the R31a carrier decision, kept —
  memo §3.4). -/
  Γ : ProfiniteGrp
  /-- The tame quotient map (eq. (27), tame component), into F3's general tame group. -/
  tame : ContinuousMonoidHom Γ (Tq q)
  /-- The maximal pro-2 quotient map (eq. (27), pro-2 component), into the abstract slot. -/
  pro2 : ContinuousMonoidHom Γ P
  /-- The ν-compatibility `ν_{t,q} ∘ tame = ν_P ∘ pro2` (what lands `b_Γ` in `∂`). -/
  compat : ∀ g : Γ, nuTq q (tame g) = nuP (pro2 g)
  /-- Eq. (27): joint surjectivity of `b_Γ : Γ ↠ ∂`. -/
  surj : Function.Surjective
    (fun g : Γ => (⟨(tame g, pro2 g), compat g⟩ : ↥(boundarySubgroupQ q nuP)))
  /-- The promoted field (recon 12 + 1): `pro2` is *the* maximal pro-2 quotient map. -/
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 Γ
  /-- The ambient `ZMod 2`-scalar action of the source (trivial, by `htriv` below). -/
  smulZmod2 : DistribMulAction ↥Γ (ZMod 2)
  /-- Continuity of the ambient scalar action. -/
  contSMulZmod2 : letI := smulZmod2; ContinuousSMul ↥Γ (ZMod 2)
  /-- The ambient scalar action is trivial. -/
  htriv : letI := smulZmod2; ∀ (γ : ↥Γ) (m : ZMod 2), γ • m = m
  /-- **(ii.1) topological finite generation** (a record field, per the FG1 Route-D shape;
  at `S₂ = G_K` this is FG1's theorem, from B1). -/
  tfg : ∃ s : Finset (Γ : Type),
    (Subgroup.closure (s : Set (Γ : Type))).topologicalClosure = ⊤
  /-- **(ii.2) Lemma 8.2 at degree `n`**: `#Hom_cont(Γ, 𝔽₂) = SN.homScalar`
  (`= 2^{n+2}` at the standard numerics; the model's `hom8 = 8`). -/
  homCard : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = SN.homScalar
  /-- **(ii.5, leaf) `#H²(Γ, 𝔽₂) = 2`** — degree-independent (`dim H² = 1` for every local
  field; memo §1.1). -/
  cardH2 : letI := smulZmod2; Nat.card (H2 Γ (ZMod 2)) = 2
  /-- **(ii.3) the `M`-stage multiplicity** (props 5.15/5.16): `#LiftsOver(ρ) = SN.mMult #M_B`
  (`= #M_B^{n+1}` standard; the model's `#M_B ^ 2`).  One deliberate binder widening versus
  the model's field: `[TopologicalSpace Y] [DiscreteTopology Y]` are carried, because the
  two-sided flip hosts the `G_ℚ₂` witness `liftsOver_card_local` (`GQ2/MStageCount.lean:702`)
  *inside* the record and that leaf demands them — every consumer site (the SD-R2/SD-R3
  producers, SD3's lanes, ASK's `K`-supply clone of the leaf) has them in scope anyway. -/
  liftsOver_card : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC),
    Nat.card (LiftsOverK RF b F ρ) = SN.mMult (Nat.card ↥RF.MB)
  /-- **(ii.4) Lemma 8.6 (half-torsor count)** ⟦lem-radicaledge⟧ — shape unchanged at degree
  `n` (the `2` is the half-torsor index, from `cardH2 = 2`, not from `n`; memo §1.1). -/
  lem86 : ∀ {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg), D.NoDescent →
    ∀ (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)), Function.Surjective ρ →
      2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ)
  /-- **(ii.5, assembled) the (136) stage at the block frame** — shape unchanged; the counts
  and `mBK` are the SD-R clones. -/
  stageR136 : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E),
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
            - exactImageCountK b F (blockFrameImpl T Blk hE2).TB)
  /-- **(ii.6) the `T`-cocycle count** in the `muZeroN` closed form:
  `SN.tMult #T * #fixedPts` (`= #T^{n+1} · #(T^∨)^{Y_B/M}` standard; the model's `#T ^ 2 · …`
  — the `fixedPts` factor is the `#H²`-by-duality term and stays a separate literal factor,
  memo §1.3). -/
  tcocycle_card : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC),
    Nat.card (TCocycle (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
      = SN.tMult (Nat.card (Additive ↥(En.radData l h).T))
        * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
            (ElemDual (Additive ↥(En.radData l h).T)))
  /-- **(ii.6) the `(T^∨)^C`-separation**: a `V`-cocycle whose `χ`-obstructions all vanish is
  `T`-liftable — shape unchanged (WW4's §6.2 family 2). -/
  hsep : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
    (c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)),
    (∀ χ : ↥(TCharC (En.radData l h)),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
      TLiftable (descSigma_spec En l h Dsc) c
  /-- **(ii.6) nondegeneracy of the obstruction pairing in the character** — shape unchanged
  (WW4's §6.2 family 3). -/
  hpartial : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
    (χ : ↥(TCharC (En.radData l h))), χ ≠ 0 →
    ∃ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
        ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
  /-- **(ii.6) the `V`-cocycle count** `#Z¹(V) = #V * SN.h1Mult #V` (`= #V^{n+1}` standard).
  ⚠ The SD-R3 shape rule is load-bearing: the **outer** `#V` is `#B¹` (degree-independent,
  the `GaussZResidueK` normalization), the **inner** factor `SN.h1Mult #V = #H¹` is the one
  that moves — NOT `#V^2`-shaped (memo §1.3, `two_mul_card_centralImageN`'s `vH` slot). -/
  hZcard : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∀ W : AddSubgroup En.Vmod, (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ v : En.Vmod, v ≠ 0) →
    (∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v) →
    ∀ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card (VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
        = Nat.card En.Vmod * SN.h1Mult (Nat.card En.Vmod)
  /-- **(ii.7) the Gauss-`Z` residue, unramified head**, at the externally given
  `G0 = SN.gaussUnram m` (`= (−1)^n 2^{nm}` standard; the recon's shared-`G0` seam): at the
  SD-R clone of the head-inflated enrichment, with the head dichotomy `F.alpha (tqTau q)`-
  trivial.  The `hq0`/`hqe` binders are `blockEnrichmentDK`'s (F3's lemmas need exactly
  these; at `q = 2` they are discharged by `two_ne_zero`/`even_two` and the enrichment is
  definitionally the model's). -/
  gaussZ_unramified : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hunram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v = v),
    letI := smulZmod2
    GaussZResidueK (sourceBoundaryMapK tame pro2 compat) F
      (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h (SN.gaussUnram m)
  /-- **(ii.7) the Gauss-`Z` residue, ramified head** (`G0 = SN.gaussRam m`, `= +2^{nm}`
  standard). -/
  gaussZ_ramified : ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v ≠ v),
    letI := smulZmod2
    GaussZResidueK (sourceBoundaryMapK tame pro2 compat) F
      (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h (SN.gaussRam m)

namespace SourceDataN

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
  {SN : SourceNumerics n} (S : SourceDataN n q P hP nuP SN)

/-- The source's boundary map `b_Γ : Γ → ∂` (eq. (27)); at the `n = 1` instances this is
definitionally the old boundary map (`sourceA_N_b`/`sourceR_N_b`/`sourceF_N_b` below). -/
noncomputable def b : ContinuousMonoidHom S.Γ ↥(boundarySubgroupQ q nuP) :=
  sourceBoundaryMapK S.tame S.pro2 S.compat

@[simp] theorem b_apply_coe (g : S.Γ) : (S.b g : Tq q × P) = (S.tame g, S.pro2 g) :=
  rfl

theorem b_surjective : Function.Surjective S.b := S.surj

/-- Surjectivity of the source's pro-2 coordinate, derived from the joint surjectivity
`surj` through `nuTq_surjective` — clone of `GQ2.SourceData.pro2_surjective`
(`GQ2/SourceData.lean:286`); the exact `hpro2ᵢ` input of the SD-R2 terminal lane
(`terminal_count_eqK`). -/
theorem pro2_surjective : Function.Surjective S.pro2 := fun p => by
  obtain ⟨t, ht⟩ := nuTq_surjective q (nuP p)
  obtain ⟨g, hg⟩ := S.surj ⟨(t, p), ht⟩
  exact ⟨g, congrArg (fun x : ↥(boundarySubgroupQ q nuP) => x.val.2) hg⟩

end SourceDataN

/-! ## The `n = 1` instances

All three at `SourceDataN 1 2 PiBd SectionThree.piBd_isProP nuTwo (standardNumerics 1)`: the refl-bridge
(probe P1) puts them at *literally* the old boundary, so the field witnesses are the frozen
supply lemmas unchanged — `F.toBoundaryFrame` mediates the (definitionally transparent)
frame repackaging, and only the two memo §1.4 value bridges are non-`rfl`. -/

section NEqOneInstances

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- **The `Γ_A` instance** — reproduces `BoundaryMaps.sourceA` (`GQ2/SourceData.lean:297`)
field-for-field (the 4 + 8 marked/pinning fields are dropped, memo Q2; their data remains
available as `B.tameA_sigma` etc. at the `BoundaryMaps` bundle).  Every witness is
`sourceA`'s own, with the `hZcard`/`gaussZ_*` value bridges of memo §1.4. -/
noncomputable def sourceA_N (B : BoundaryMaps) :
    SourceDataN 1 2 PiBd SectionThree.piBd_isProP nuTwo (standardNumerics 1) where
  Γ := GammaA
  tame := B.tameA
  pro2 := B.pro2A
  compat := B.compatA
  surj := B.surjA
  ker_pro2 := SectionNine.ker_pro2A B
  smulZmod2 := inferInstance
  contSMulZmod2 := inferInstance
  htriv := RStageGammaA.htriv_gammaA
  tfg := gammaA_topologicallyFinitelyGenerated
  homCard := lemma_8_2_gammaA
  cardH2 := CardH2GammaA.card_H2_gammaA
  liftsOver_card := fun RF b F ρ => RF.liftsOver_card_gammaA b F.toBoundaryFrame ρ
  lem86 := fun D hedge ρ hρ => lemma_8_6_gammaA D hedge ρ hρ
  stageR136 := fun hE2 hRK hR2 b F =>
    CardH2GammaA.stageR136_gammaA hE2 hRK hR2 b F.toBoundaryFrame
  tcocycle_card := fun b F En l h ρ =>
    Phase140GammaA.tcocycle_card_gammaA b F.toBoundaryFrame En l h ρ
  hsep := fun b F En l h Dsc ρ c hc =>
    Phase140GammaA.hsep_gammaA b F.toBoundaryFrame En l h Dsc ρ c hc
  hpartial := fun b F En l h Dsc ρ χ hχ =>
    Phase140GammaA.hpartial_gammaA b F.toBoundaryFrame En l h Dsc ρ χ hχ
  hZcard := fun b F En l h hsimple hVne hnt ρ =>
    (Phase140GammaA.hZcard_gammaA b F.toBoundaryFrame En l h hsimple hVne hnt ρ).trans
      (by rw [standardNumerics_one_h1Mult])
  gaussZ_unramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hunram => by
    rw [standardNumerics_one_gaussUnram]
    exact SectionNine.gaussZResidueD_gammaA_unramified T Blk hE2 B F.toBoundaryFrame
      hsimple hVne hnt m hm hcard l h hunram
  gaussZ_ramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hram => by
    rw [standardNumerics_one_gaussRam]
    exact SectionNine.gaussZResidueD_gammaA_ramified T Blk hE2 B F.toBoundaryFrame
      hsimple hVne hnt m hm hcard l h hram

/-- The load-bearing definitional identity (memo §8 acceptance (1)): `sourceA_N`'s boundary
map **is** `B.bA` — the K-factory at `q = 2` is the model's construction on the same
fields.  The `n = 1` analogue of `BoundaryMaps.sourceA_b` (`GQ2/SourceData.lean:339`). -/
@[simp] theorem sourceA_N_b (B : BoundaryMaps) : (sourceA_N B).b = B.bA := rfl

/-- **The `Γ_R` instance** — reproduces `GQ2.sourceR` (`GQ2/Roe/Main.lean`) under the same
`hBLab` binder (B-Lab stays a hypothesis; never an axiom) and the same
`[CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]` section instances
(`Roe/Main.lean:220` — the pro-2 side is B-Lab-conditional *through* `AbsGalQ2`), minus the
dropped marked/pinning fields (which is where `sourceR`'s choice-valued
`sigmaMarkR`/`x0MarkR`/`x1MarkR` lived — the honest-generator caveat documented there
evaporates with them).  `Γ` is the frozen `GQ2.GammaR`, written qualified: F3's
*parameterized* `GQ2.Dyadic.GammaR n q R` (`Dyadic/TameBoundary.lean:286`) shadows the
frozen name inside this namespace. -/
noncomputable def sourceR_N [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hBLab : BLabHypothesis) :
    SourceDataN 1 2 PiBd SectionThree.piBd_isProP nuTwo (standardNumerics 1) where
  Γ := GQ2.GammaR
  tame := phiR
  pro2 := pro2R hBLab
  compat := pro2R_compat hBLab
  surj := bR_joint_surjective hBLab
  ker_pro2 := ker_pro2R hBLab
  smulZmod2 := RStageGammaR.instDistribMulActionGammaR
  contSMulZmod2 := inferInstance
  htriv := RStageGammaR.htriv_gammaR
  tfg := gammaR_topologicallyFinitelyGenerated
  homCard := lemma_8_2_R
  cardH2 := SectionEight.LedgerGammaR.card_H2_gammaR
  liftsOver_card := fun RF b F ρ => RF.liftsOver_card_gammaR b F.toBoundaryFrame ρ
  lem86 := fun D hedge ρ hρ => SectionEight.LedgerGammaR.lemma_8_6_gammaR D hedge ρ hρ
  stageR136 := fun hE2 hRK hR2 b F => RStageGammaR.stageR136_gammaR_of_hcard hE2 hRK hR2
    SectionEight.LedgerGammaR.card_H2_gammaR b F.toBoundaryFrame
  tcocycle_card := fun b F En l h ρ =>
    Phase140GammaR.tcocycle_card_gammaR b F.toBoundaryFrame En l h ρ
  hsep := fun b F En l h Dsc ρ c hc =>
    Phase140GammaR.hsep_gammaR b F.toBoundaryFrame En l h Dsc ρ c hc
  hpartial := fun b F En l h Dsc ρ χ hχ =>
    Phase140GammaR.hpartial_gammaR b F.toBoundaryFrame En l h Dsc ρ χ hχ
  hZcard := fun b F En l h hsimple hVne hnt ρ =>
    (Phase140GammaR.hZcard_gammaR b F.toBoundaryFrame En l h hsimple hVne hnt ρ).trans
      (by rw [standardNumerics_one_h1Mult])
  gaussZ_unramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hunram => by
    rw [standardNumerics_one_gaussUnram]
    exact SectionNine.gaussZResidueD_gammaR_unramified T Blk hE2 phiR (pro2R hBLab)
      (pro2R_compat hBLab) phiR_gammaSigma phiR_gammaTau phiR_gammaX0 phiR_gammaX1
      F.toBoundaryFrame hsimple hVne hnt m hm hcard l h hunram
  gaussZ_ramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hram => by
    rw [standardNumerics_one_gaussRam]
    exact SectionNine.gaussZResidueD_gammaR_ramified T Blk hE2 phiR (pro2R hBLab)
      (pro2R_compat hBLab) phiR_gammaSigma phiR_gammaTau phiR_gammaX0 phiR_gammaX1
      F.toBoundaryFrame hsimple hVne hnt m hm hcard l h hram

/-- `sourceR_N`'s boundary map **is** `sourceR`'s — `rfl` (memo §8 acceptance (1)). -/
@[simp] theorem sourceR_N_b [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hBLab : BLabHypothesis) :
    (sourceR_N hBLab).b = (sourceR hBLab).b := rfl

/-- **The `G_ℚ₂` instance — the two-sided flip's genuinely new `n = 1` object** (memo §3.4):
the B-side of `thm_4_2`, packaged as a record from the verified `*_local` leaf pack of
memo §3.1's removal list.  The binder migration is exactly §3.1's: the theorem-level
`[CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]` instances and the
`(R, horient)` reciprocity pair (needed only by the ramified Gauss leaf) move here, into
the `S₂`-instantiation.  This is the `n = 1` case of the ASK ticket's `G_K` record
(memo §3.3): `tame`/`pro2`/`surj` ← the `BoundaryMaps` bundle (at `K`: B10-K + the
marked-core certificate), `tfg` ← `Foundations` B1 (at `K`: FG1's theorem), the counting
leaves ← `MStageCount`/`RStage.Local`/`Phase140.Local` (at `K`: their Euler-characteristic
clones), the Gauss leaves ← `GaussZ.FinalD` (at `K`: LG5's `local_gauss_K` through the
(83)-evaluation bridge). -/
noncomputable def sourceF_N (B : BoundaryMaps) (R : LocalReciprocity)
    (horient : TameUnitOrientation R B.tameF)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    SourceDataN 1 2 PiBd SectionThree.piBd_isProP nuTwo (standardNumerics 1) where
  Γ := ProfiniteGrp.of AbsGalQ2
  tame := B.tameF
  pro2 := B.pro2F
  compat := B.compatF
  surj := B.surjF
  ker_pro2 := B.ker_pro2F
  smulZmod2 := inferInstanceAs (DistribMulAction AbsGalQ2 (ZMod 2))
  contSMulZmod2 := inferInstanceAs (ContinuousSMul AbsGalQ2 (ZMod 2))
  htriv := fun γ m => htriv_local' γ m
  tfg := Foundations.absGalQ2_isTopologicallyFinitelyGenerated
  homCard := lemma_8_2_local B
  cardH2 := LocalLiftingDuality.card_H2_zmod2_eq_two fun γ m => htriv_local' γ m
  liftsOver_card := fun RF b F ρ => RF.liftsOver_card_local b F.toBoundaryFrame ρ
  lem86 := fun D hedge ρ hρ => lemma_8_6_local D
    Foundations.absGalQ2_isTopologicallyFinitelyGenerated hedge ρ hρ
  stageR136 := fun hE2 hRK hR2 b F => RStageLocal.stageR136_local hE2 hRK hR2
    Foundations.absGalQ2_isTopologicallyFinitelyGenerated b F.toBoundaryFrame
  tcocycle_card := fun b F En l h ρ =>
    tcocycle_card_local b F.toBoundaryFrame En l h ρ
  hsep := fun b F En l h Dsc ρ c hc =>
    hsep_local b F.toBoundaryFrame En l h Dsc ρ c hc
  hpartial := fun b F En l h Dsc ρ χ hχ =>
    hpartial_local b F.toBoundaryFrame En l h Dsc ρ χ hχ
  hZcard := fun b F En l h hsimple hVne hnt ρ =>
    (hZcard_local b F.toBoundaryFrame En l h hsimple hVne hnt ρ).trans
      (by rw [standardNumerics_one_h1Mult])
  gaussZ_unramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hunram => by
    rw [standardNumerics_one_gaussUnram]
    exact SectionNine.gaussZResidueD_local_unramified T Blk hE2 B F.toBoundaryFrame
      (tateDuality 2) hsimple hVne hnt m hm hcard l h hunram
  gaussZ_ramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hram => by
    rw [standardNumerics_one_gaussRam]
    exact SectionNine.gaussZResidueD_local_ramified T Blk hE2 B F.toBoundaryFrame
      (tateDuality 2) R horient hsimple hVne hnt m hm hcard l h hram

/-- `sourceF_N`'s boundary map **is** `B.bF` — `rfl` (the F-side analogue of
`sourceA_N_b`; what lets SD3's regression theorem re-derive `thm_4_2`'s exact statement). -/
@[simp] theorem sourceF_N_b (B : BoundaryMaps) (R : LocalReciprocity)
    (horient : TameUnitOrientation R B.tameF)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    (sourceF_N B R horient).b = B.bF := rfl

end NEqOneInstances

end GQ2.Dyadic
