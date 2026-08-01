/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.SourceDataN
import GQ2.Dyadic.Recursion.Induction
import GQ2.Dyadic.Recursion.BlockRStage
import GQ2.SectionTen
import GQ2.ThmFourTwo

/-!
# The two-sided degree-`n` theorem  (dyadic campaign, ticket SD3)

The SD lane's sink: **packet Thm 11.1** (`thm:source-abstract`) in Lean.  Two sources over the
same abstract slot — same residue cardinality `q`, same marked pro-2 slot `(P, hP, νP)`, same
numerics `SN` — have equal boundary-framed exact-image counts, hence equal continuous-surjection
counts onto every finite group, hence isomorphic groups.

This file contains **no mathematics that the frozen `ℚ₂` stack does not already contain**: it is
`GQ2/ThmFourTwo.lean:386-414`'s strong induction replayed over `SourceDataN` (SD2) against the
SD-R1–3 spine clone (`GQ2/Dyadic/Recursion/`), plus the §10 frame summation at the `K`-boundary
and the (boundary-free) `GQ2/Reconstruction.lean` corollary.

## What the two-sided flip removes  (SD1 memo §3.1)

The one-sided `thm_4_2_of_sources` pins its second source to `G_ℚ₂` through `B : BoundaryMaps`,
`(R, horient)`, the `AbsGalQ2` instance binders and the whole `*_local` supply pack.  **None of
those appear below.**  They become the `S₂`-instantiation's obligations — discharged at `n = 1`
by SD2's `sourceF_N` (see the regression section), and at general `K` by the ASK ticket.

The structural consequence, first observed by SD-R3 and confirmed here by measurement: the
generic theorem is **B-axiom-free**.  `closedRecursionK_of_source` prints std-3 where its model
`prop_8_9` needs `{B6, B7}`, because B6/B7 entered only through the `G_ℚ₂` side's `_local`
leaves.  B-axioms re-enter this file exactly once, in the `n = 1` regression, through
`sourceF_N`/`sourceR_N` — never in the generic statement.

## The lanes  (the model's, one line at a time)

| lane | model | here |
|---|---|---|
| terminal | `terminal_count_eq_of_sources` | `terminal_count_eqK` (SD-R2), both sides through records |
| `M`-stage (`R = ⊥`) | `mStage_lane` | `mStage_laneN`, at `mult := SN.mMult #M_B` from both records |
| `R`-stage (`R ≠ ⊥`) | `rStage_lane` | `rStage_laneN`, through `prop_8_9_of_sourcesN` + `count_eq_of_closedRecursionK` |

`prop_8_9_of_sourcesN` is the SD-R3 refactor cashed in: the model's `prop_8_9_of_source` is a
*hybrid* (source through hypotheses, `G_ℚ₂` through `_local`), which cannot be cloned
two-sidedly.  SD-R3 factored it into the one-sided producer `closedRecursionK_of_source`; this
file applies that producer **once per source** at a shared reference edge `(l₀, h₀)`, shared
`G0`, shared `tMult` and shared `En`, and packages the `∃`.  Both `ClosedRecursionK`s then carry
syntactically identical `(μ, G⁰, D_T, phase, cS, mM, vH)`, which is exactly what SD-R2's solver
`count_eq_of_closedRecursionK` consumes.  The model's `_local` branch simply disappears.

Both positivity-cancels are discharged upstream (SD-R2 inside the solver, SD-R3 inside
`nPhaseK_eq_of_strata`); this file only *feeds* them, from `SourceNumerics.homScalar_pos`.

## Threaded binders

`hq0 : q ≠ 0`, `hqe : Even q` (F3's tame lemmas, via `terminal_count_eqK` and
`blockEnrichmentDK`) and `hnuP : Function.Surjective nuP` (the terminal lane's slot condition —
instantiation-side, not a record field: it is a property of the shared slot, not of a source).
At `q = 2`, `P := PiBd`, `nuP := nuTwo` all three are `two_ne_zero`/`even_two`/`nuTwo`'s
surjectivity.

Plain-import (memo §5).

Axioms: **no new axioms; none of the nine obligations as axioms.**  SD-n *is* one of the nine,
and `thm_4_2_of_sourcesN` is its discharge at the generic level — so the headline theorem is
sorry-free and axiom-clean.  Print check performed per declaration (measured, not budgeted):

* **all 24 declarations other than the two regression theorems** — the Gauss obtain,
  `prop_8_9_of_sourcesN`, the four lanes,
  `thm_4_2_of_sourcesN`, the whole §10-K block, `contSurj_card_eq_of_sourcesN`,
  `nonempty_continuousMulEquiv_of_sourcesN`, `boundaryFrameK` — print **exactly std-3**
  `[propext, Classical.choice, Quot.sound]`.  Not one B-axiom in the generic layer: measured
  confirmation of SD-R3's structural claim, now at capstone level.  The model
  `GQ2.thm_4_2_of_sources` needs `{B1, B6, B7, B9, B11a}` for the same mathematics.
* `thm_4_2_via_N` — std-3 ∪ {B1 `absGalQ2_isTopologicallyFinitelyGenerated`, B6 `tateDualityAt`,
  B7 `absGalQ2_localEulerCharacteristic`, B9 `relativeStiefelWhitney_dyadic`,
  B11a `hilbertSymbol_normCriterion_finiteDyadic`}: **byte-identical to the frozen
  `GQ2.thm_4_2`'s own print**.  Re-deriving the capstone through the clone costs zero axioms.
* `thm_4_2_gammaR_via_N` — that set ∪ {B3c `dyadicOrientation`, B5 `localReciprocity`,
  B8 `peripheralCyclotomicAction`}, i.e. exactly `thm_4_2`'s ∪ `sourceR`'s, as SD2 measured for
  `sourceR_N`.  B-Lab stays the `hBLab` binder, never an axiom.

No frozen file is touched, so the audited capstone prints cannot move: `scripts/check_axioms.sh`
check 5 green (5 capstones at the census set, 3 twin pairs identical), census still 11.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
-- The model's open list (`GQ2/SourceData.lean:52`), minus `QuadraticFp2`: SD-R3's convention
-- for the clone tree is never to open it in a file that mentions `sign`.
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
  {SN : SourceNumerics n}

/-! ## The shared-`G0` Gauss obtain, two-sidedly

Clone of `GQ2.gaussZ_obtain_blockD_of_sources` (`GQ2/SourceData.lean:387`) with the `G_ℚ₂` side
replaced by a second record.  The exponent `m` (from the nonsingular form on `V`) and the head
dichotomy (on `F.alpha (tqTau q)`) are **source-independent**, so they are decided once and each
source then contributes exactly its own record leaf at the resulting shared
`G0 = SN.gaussUnram m` resp. `SN.gaussRam m`. -/

section GaussObtain

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- **The shared-`G0` obtain over two abstract sources** at the `K`-boundary.  Two-sided clone of
`GQ2.gaussZ_obtain_blockD_of_sources` (`GQ2/SourceData.lean:387`); `tameTau` becomes `tqTau q`
and the `ℚ₂` twins `gaussZResidueD_local_*` are gone — both sides are record leaves. -/
theorem gaussZ_obtain_blockDK_of_sourcesN (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (S₁ S₂ : SourceDataN n q P hP nuP SN) (F : BoundaryFrameK q P H E)
    (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
      (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
    (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
      (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v) :
    ∃ G0 : ℤ,
      (letI := S₁.smulZmod2
        ∀ (l : (SectionNine.blockFrame T Blk hE2).DR)
          (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR),
          GaussZResidueK S₁.b F (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h G0) ∧
      (letI := S₂.smulZmod2
        ∀ (l : (SectionNine.blockFrame T Blk hE2).DR)
          (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR),
          GaussZResidueK S₂.b F (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h G0) := by
  classical
  letI := blockPS_commGroup Blk
  letI := SectionNine.headAct T Blk
  by_cases hex : ∃ l : (SectionNine.blockFrame T Blk hE2).DR,
      l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR
  · obtain ⟨l₀, hl₀⟩ := hex
    have hl₀' : l₀.1 ≠ Blk.frattiniK := fun heq => hl₀ (Subtype.ext heq)
    -- `m` from the nonsingular form on `V` (A-4.6b), `l`-free through `#V`
    obtain ⟨m, hm, hcard⟩ := exists_one_le_card_eq_two_pow_of_nonsingular
      (blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l₀ hl₀')
      (blockHquadK T Blk hq0 hqe F.alpha F.alpha_surjective l₀ hl₀')
      (blockHnsK T Blk hq0 hqe F.alpha F.alpha_surjective l₀ hl₀')
      (SectionNine.blockPS_exp2 T Blk) hVne
    -- the source-uniform head dichotomy, at the general tame head element `tqTau q`
    by_cases hd : ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v = v
    · exact ⟨SN.gaussUnram m,
        fun l h => S₁.gaussZ_unramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hd,
        fun l h => S₂.gaussZ_unramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hd⟩
    · push Not at hd
      exact ⟨SN.gaussRam m,
        fun l h => S₁.gaussZ_ramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hd,
        fun l h => S₂.gaussZ_ramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hd⟩
  · push Not at hex
    exact ⟨0, fun l h => absurd (hex l) h, fun l h => absurd (hex l) h⟩

end GaussObtain

/-! ## Proposition 8.9, two-sidedly  (the SD-R3 refactor, cashed in)

The model's `GQ2.prop_8_9_of_sources` (`GQ2/SourceData.lean:441`) forwards to the *hybrid*
`prop_8_9_of_source`, whose `G_ℚ₂` branch (`GQ2/Prop89Close.lean:348-360`) cites the `_local`
pack.  SD-R3 factored the generic half out as the one-sided producer
`closedRecursionK_of_source`, so the two-sided version below is pure `∃`-packaging: apply the
producer once per source at a **shared** reference edge `(l₀, h₀)`, shared `Fintype` instance,
shared `G0`, shared `tMult := SN.tMult` and shared `En`.  Sharing one `SN` between the records
makes the numeric triple `(cS, mM, vH)` syntactically equal on both sides, which is what
`count_eq_of_closedRecursionK` needs; no equality side condition between the sources' numerics
ever arises (memo §3.2). -/

section Prop89

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- **Proposition 8.9 over two abstract sources** at the `K`-boundary, numerically parameterized.
Two-sided clone of `GQ2.prop_8_9_of_sources` (`GQ2/SourceData.lean:441`).

The three numeric slots are read off the shared `SN`: `cS = SN.homScalar` (memo §4.1a),
`mM = SN.mMult #M_B` (§4.1b), `vH = SN.h1Mult #V` (§4.1c); `μ` folds in `SN.tMult` through
`muZeroN`.  `hRK`/`hR2` are Lemma 7.2's block facts, source-independent (`lemma_7_2_core`), and
are supplied by the caller so that this statement stays free of §7 plumbing. -/
theorem prop_8_9_of_sourcesN (S₁ S₂ : SourceDataN n q P hP nuP SN) (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (En : (blockFrameImpl T Blk hE2).Enrichment) (F : BoundaryFrameK q P H E)
    (hhead₁ : Function.Surjective (fun γ : S₁.Γ => (F.frameMap (S₁.b γ)).1))
    (hhead₂ : Function.Surjective (fun γ : S₂.Γ => (F.frameMap (S₂.b γ)).1))
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : (blockFrameImpl T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : (blockFrameImpl T Blk hE2).YC) (v : En.Vmod), g • v ≠ v)
    (G0 : ℤ)
    (hGaussZ₁ : letI := S₁.smulZmod2
      ∀ (l : (blockFrameImpl T Blk hE2).DR) (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR),
        GaussZResidueK S₁.b F En l h G0)
    (hGaussZ₂ : letI := S₂.smulZmod2
      ∀ (l : (blockFrameImpl T Blk hE2).DR) (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR),
        GaussZResidueK S₂.b F En l h G0) :
    ∃ (μ : ℕ) (G0' : ℤ) (DT : Type) (_ : Fintype DT)
      (phase : (l : (blockFrameImpl T Blk hE2).DR) →
        l ≠ (blockFrameImpl T Blk hE2).zeroDR → DT →
          CentralCover (blockFrameImpl T Blk hE2).YC),
      0 < Nat.card DT ∧
        ClosedRecursionK (blockFrameImpl T Blk hE2) S₁.b F μ G0' DT phase SN.homScalar
            (SN.mMult (Nat.card ↥(blockFrameImpl T Blk hE2).MB))
            (SN.h1Mult (Nat.card En.Vmod)) ∧
        ClosedRecursionK (blockFrameImpl T Blk hE2) S₂.b F μ G0' DT phase SN.homScalar
            (SN.mMult (Nat.card ↥(blockFrameImpl T Blk hE2).MB))
            (SN.h1Mult (Nat.card En.Vmod)) := by
  classical
  by_cases hex : ∃ l : (blockFrameImpl T Blk hE2).DR, l ≠ (blockFrameImpl T Blk hE2).zeroDR
  · -- some `λ ≠ 0` exists: share `DT := (T^∨)^C`, read at a reference edge `λ₀`
    obtain ⟨l₀, h₀⟩ := hex
    haveI : Fintype ↥(TCharC (En.radData l₀ h₀)) := Fintype.ofFinite _
    have hcr₁ : ClosedRecursionK (blockFrameImpl T Blk hE2) S₁.b F
        (Nat.card En.Vmod * muZeroN SN.tMult En l₀ h₀) G0 ↥(TCharC (En.radData l₀ h₀))
        (phaseFamily En l₀ h₀) SN.homScalar
        (SN.mMult (Nat.card ↥(blockFrameImpl T Blk hE2).MB))
        (SN.h1Mult (Nat.card En.Vmod)) := by
      letI := S₁.smulZmod2
      letI := S₁.contSMulZmod2
      exact closedRecursionK_of_source (blockFrameImpl T Blk hE2) En S₁.b F l₀ h₀ _ _ _ _ G0
        S₁.htriv S₁.tfg S₁.homCard S₁.cardH2 hhead₁ (S₁.stageR136 hE2 hRK hR2 S₁.b F)
        (fun D hedge ρ hρ => S₁.lem86 D hedge ρ hρ)
        (S₁.liftsOver_card _ S₁.b F)
        (fun l h ρ => S₁.tcocycle_card S₁.b F En l h ρ)
        (fun l h Dsc ρ c hc => S₁.hsep S₁.b F En l h Dsc ρ c hc)
        (fun l h Dsc ρ χ hχ => S₁.hpartial S₁.b F En l h Dsc ρ χ hχ)
        (fun l h ρ => S₁.hZcard S₁.b F En l h hsimple hVne hnt ρ)
        hGaussZ₁
    have hcr₂ : ClosedRecursionK (blockFrameImpl T Blk hE2) S₂.b F
        (Nat.card En.Vmod * muZeroN SN.tMult En l₀ h₀) G0 ↥(TCharC (En.radData l₀ h₀))
        (phaseFamily En l₀ h₀) SN.homScalar
        (SN.mMult (Nat.card ↥(blockFrameImpl T Blk hE2).MB))
        (SN.h1Mult (Nat.card En.Vmod)) := by
      letI := S₂.smulZmod2
      letI := S₂.contSMulZmod2
      exact closedRecursionK_of_source (blockFrameImpl T Blk hE2) En S₂.b F l₀ h₀ _ _ _ _ G0
        S₂.htriv S₂.tfg S₂.homCard S₂.cardH2 hhead₂ (S₂.stageR136 hE2 hRK hR2 S₂.b F)
        (fun D hedge ρ hρ => S₂.lem86 D hedge ρ hρ)
        (S₂.liftsOver_card _ S₂.b F)
        (fun l h ρ => S₂.tcocycle_card S₂.b F En l h ρ)
        (fun l h Dsc ρ c hc => S₂.hsep S₂.b F En l h Dsc ρ c hc)
        (fun l h Dsc ρ χ hχ => S₂.hpartial S₂.b F En l h Dsc ρ χ hχ)
        (fun l h ρ => S₂.hZcard S₂.b F En l h hsimple hVne hnt ρ)
        hGaussZ₂
    exact ⟨_, G0, _, inferInstance, phaseFamily En l₀ h₀, card_TCharC_pos En l₀ h₀, hcr₁, hcr₂⟩
  · -- no nonzero `λ`: (137)–(140) are vacuous and only the two (136) stages are live
    exact ⟨1, G0, PUnit, inferInstance, fun l h _ => absurd ⟨l, h⟩ hex, by simp,
      closedRecursionK_of_source_degenerate (blockFrameImpl T Blk hE2) S₁.b F _ _ _ _ G0 _ _
        S₁.tfg S₁.homCard hhead₁ hex (S₁.stageR136 hE2 hRK hR2 S₁.b F),
      closedRecursionK_of_source_degenerate (blockFrameImpl T Blk hE2) S₂.b F _ _ _ _ G0 _ _
        S₂.tfg S₂.homCard hhead₂ hex (S₂.stageR136 hE2 hRK hR2 S₂.b F)⟩

end Prop89

/-! ## The `M`-stage lane  (`R = ⊥`)

Clone of the `private` `GQ2.mStage_lane` (`GQ2/ThmFourTwo.lean:104-202`), two-sidedly.  The
model's asymmetry — `S.tfg`/`S.liftsOver_card` on one side, `Foundations.absGalQ2_…`/
`liftsOver_card_local` on the other — disappears: both sides read their record.  The
multiplicity is `SN.mMult #M_B` in place of the model's `#M_B ^ 2`; `mStage_partitionK` is
already multiplicity-generic (SD-R2), so nothing else moves. -/

section Lanes

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

private theorem mStage_laneN (S₁ S₂ : SourceDataN n q P hP nuP SN) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (Blk : SectionSeven.MinimalBlock T.LY) (hR : Blk.frattiniK = ⊥) (N : ℕ)
    (hcard : Nat.card ↥T.LY = N)
    (IH : ∀ m, m < N → ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [DiscreteTopology Z]
      [Finite Z] (T' : MarkedTarget H E Z), Nat.card ↥T'.LY = m →
      exactImageCountK S₁.b F T' = exactImageCountK S₂.b F T') :
    exactImageCountK S₁.b F T = exactImageCountK S₂.b F T := by
  classical
  by_cases hhead : Function.Surjective
      (fun x : ↥(boundarySubgroupQ q nuP) => (F.frameMap x).1)
  · -- head covered: run the partition at both sources
    have hhead₁ : Function.Surjective (fun γ : S₁.Γ => (F.frameMap (S₁.b γ)).1) :=
      hhead.comp S₁.b_surjective
    have hhead₂ : Function.Surjective (fun γ : S₂.Γ => (F.frameMap (S₂.b γ)).1) :=
      hhead.comp S₂.b_surjective
    -- the multiplicity `SN.mMult #M_B`, per source (each record's `liftsOver_card`)
    have hmult₁ := S₁.liftsOver_card (blockFrameImpl T Blk hE2) S₁.b F
    have hmult₂ := S₂.liftsOver_card (blockFrameImpl T Blk hE2) S₂.b F
    -- the two partition identities (SD-R2's `mStage_partitionK`)
    have hpart₁ := mStage_partitionK (blockFrameImpl T Blk hE2) S₁.tfg S₁.b F hhead₁
      (SN.mMult (Nat.card ↥(blockFrameImpl T Blk hE2).MB)) hmult₁
    have hpart₂ := mStage_partitionK (blockFrameImpl T Blk hE2) S₂.tfg S₂.b F hhead₂
      (SN.mMult (Nat.card ↥(blockFrameImpl T Blk hE2).MB)) hmult₂
    -- IH at the `C`-stage (`|L_C| < |L_Y| = N`, (145c))
    have hTC : exactImageCountK S₁.b F (blockFrameImpl T Blk hE2).TC
        = exactImageCountK S₂.b F (blockFrameImpl T Blk hE2).TC := by
      refine IH _ ?_ _ (blockFrameImpl T Blk hE2).TC rfl
      exact hcard ▸ card_LC_lt T Blk hE2
    -- IH at the proper `C`-onto strata (the `M`-stage bound, all-`R` valid)
    have hstrata : ∀ J ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
          J.map (blockFrameImpl T Blk hE2).piBC = ⊤} \ {⊤},
        exactImageCountOnK S₁.b F (blockFrameImpl T Blk hE2).TB J
          = exactImageCountOnK S₂.b F (blockFrameImpl T Blk hE2).TB J := by
      rintro J ⟨hJC, hJne⟩
      simp only [exactImageCountOnK]
      by_cases hJ : Function.Surjective
          ((blockFrameImpl T Blk hE2).TB.piY.comp J.subtype)
      · rw [dif_pos hJ, dif_pos hJ]
        refine IH _ ?_ _ ((blockFrameImpl T Blk hE2).TB.stratum J hJ) rfl
        exact hcard ▸ card_stratum_mStage_lt T Blk hE2 J (by simpa using hJne) hJC hJ
      · rw [dif_neg hJ, dif_neg hJ]
    -- the `⊤`-stratum is the ambient count (`R = ⊥` ⟹ `π_B` iso)
    have htop₁ : exactImageCountOnK S₁.b F (blockFrameImpl T Blk hE2).TB ⊤
        = exactImageCountK S₁.b F T := by
      rw [exactImageCountOnK_top,
        exactImageCountK_TB_of_R_bot (blockFrameImpl T Blk hE2) S₁.b F hR]
    have htop₂ : exactImageCountOnK S₂.b F (blockFrameImpl T Blk hE2).TB ⊤
        = exactImageCountK S₂.b F T := by
      rw [exactImageCountOnK_top,
        exactImageCountK_TB_of_R_bot (blockFrameImpl T Blk hE2) S₂.b F hR]
    -- split the `⊤` stratum off both partitions and cancel the (equal) proper parts
    haveI : Finite (Subgroup (blockFrameImpl T Blk hE2).YB) :=
      Finite.of_injective _ SetLike.coe_injective
    have hS_top : (⊤ : Subgroup (blockFrameImpl T Blk hE2).YB)
        ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
            J.map (blockFrameImpl T Blk hE2).piBC = ⊤} :=
      Subgroup.map_top_of_surjective _ (blockFrameImpl T Blk hE2).piBC_surj
    have hsplit : ∀ g : Subgroup (blockFrameImpl T Blk hE2).YB → ℕ,
        ∑ᶠ J ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
            J.map (blockFrameImpl T Blk hE2).piBC = ⊤}, g J
          = g ⊤ + ∑ᶠ J ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
              J.map (blockFrameImpl T Blk hE2).piBC = ⊤} \ {⊤}, g J := by
      intro g
      rw [← finsum_mem_singleton
        (a := (⊤ : Subgroup (blockFrameImpl T Blk hE2).YB)) (f := g)]
      exact (finsum_mem_add_sdiff (Set.singleton_subset_iff.mpr hS_top)
        (Set.toFinite _)).symm
    have hSsum : ∑ᶠ J ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
          J.map (blockFrameImpl T Blk hE2).piBC = ⊤},
          exactImageCountOnK S₁.b F (blockFrameImpl T Blk hE2).TB J
        = ∑ᶠ J ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
            J.map (blockFrameImpl T Blk hE2).piBC = ⊤},
            exactImageCountOnK S₂.b F (blockFrameImpl T Blk hE2).TB J := by
      rw [← hpart₁, ← hpart₂, hTC]
    rw [hsplit, hsplit, htop₁, htop₂, finsum_mem_congr rfl hstrata] at hSsum
    exact Nat.add_right_cancel hSsum
  · -- head not covered: both counts vanish
    rw [exactImageCountK_eq_zero_of_not_headSurj S₁.b F T hhead,
      exactImageCountK_eq_zero_of_not_headSurj S₂.b F T hhead]

/-! ## The `R`-stage lane  (`R ≠ ⊥`) -/

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`R`-stage IH at the pulled `B`-strata** ((148)), two-sidedly.  Clone of the `private`
`GQ2.rStage_pull` (`GQ2/ThmFourTwo.lean:207-237`) — verbatim modulo the `K`-typed counts. -/
private theorem rStage_pullN (S₁ S₂ : SourceDataN n q P hP nuP SN) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (Blk : SectionSeven.MinimalBlock T.LY) (hR : Blk.frattiniK ≠ ⊥) (N : ℕ)
    (hcard : Nat.card ↥T.LY = N)
    (IH : ∀ m, m < N → ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [DiscreteTopology Z]
      [Finite Z] (T' : MarkedTarget H E Z), Nat.card ↥T'.LY = m →
      exactImageCountK S₁.b F T' = exactImageCountK S₂.b F T')
    (l : (blockFrameImpl T Blk hE2).DR) (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR)
    (J' : Subgroup ((blockFrameImpl T Blk hE2).scalarCover l h).cover)
    (hJtop : J'.map ((blockFrameImpl T Blk hE2).scalarCover l h).p ≠ ⊤)
    (hJC : (J'.map ((blockFrameImpl T Blk hE2).scalarCover l h).p).map
        (blockFrameImpl T Blk hE2).piBC = ⊤) :
    exactImageCountOnK S₁.b F
        (((blockFrameImpl T Blk hE2).scalarCover l h).pullTarget
          (blockFrameImpl T Blk hE2).TB) J'
      = exactImageCountOnK S₂.b F
          (((blockFrameImpl T Blk hE2).scalarCover l h).pullTarget
            (blockFrameImpl T Blk hE2).TB) J' := by
  simp only [exactImageCountOnK]
  by_cases hJ' : Function.Surjective
      ((((blockFrameImpl T Blk hE2).scalarCover l h).pullTarget
        (blockFrameImpl T Blk hE2).TB).piY.comp J'.subtype)
  · rw [dif_pos hJ', dif_pos hJ']
    refine IH _ ?_ _
      ((((blockFrameImpl T Blk hE2).scalarCover l h).pullTarget
        (blockFrameImpl T Blk hE2).TB).stratum J' hJ') rfl
    exact hcard ▸ card_stratum_LB_lt T Blk hE2 hR
      ((blockFrameImpl T Blk hE2).scalarCover l h) J' hJ' hJtop
      (sup_MB_eq_top_of_map_piBC T Blk hE2 hJC)
  · rw [dif_neg hJ', dif_neg hJ']

/-- **`R`-stage phase-cover counts agree** ((141)/(142)), two-sidedly.  The `lemma_8_3` half and
the scalar cancellation are SD-R3's `nPhaseK_eq_of_strata` (which is where the model's `omega` on
the literal `8` became a positivity-cancel at the opaque `cS`); this theorem supplies only its
`hstr` — the induction hypothesis at the (153) bound, which SD-R3 deliberately left to SD3
because deriving it *is* the induction step.  The positivity feed is `SN.homScalar_pos`. -/
private theorem rStage_phaseN (S₁ S₂ : SourceDataN n q P hP nuP SN) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (Blk : SectionSeven.MinimalBlock T.LY) (N : ℕ) (hcard : Nat.card ↥T.LY = N)
    (IH : ∀ m, m < N → ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [DiscreteTopology Z]
      [Finite Z] (T' : MarkedTarget H E Z), Nat.card ↥T'.LY = m →
      exactImageCountK S₁.b F T' = exactImageCountK S₂.b F T')
    (Cζ : CentralCover (blockFrameImpl T Blk hE2).YC) :
    nPhaseK (blockFrameImpl T Blk hE2) S₁.b F Cζ
      = nPhaseK (blockFrameImpl T Blk hE2) S₂.b F Cζ := by
  refine nPhaseK_eq_of_strata (blockFrameImpl T Blk hE2) F S₁.b S₂.b S₁.tfg S₂.tfg
    SN.homScalar SN.homScalar_pos S₁.homCard S₂.homCard Cζ ?_
  intro J' _
  simp only [exactImageCountOnK]
  by_cases hJ' : Function.Surjective
      ((Cζ.pullTarget (blockFrameImpl T Blk hE2).TC).piY.comp J'.subtype)
  · rw [dif_pos hJ', dif_pos hJ']
    refine IH _ ?_ _
      ((Cζ.pullTarget (blockFrameImpl T Blk hE2).TC).stratum J' hJ') rfl
    exact hcard ▸ card_stratum_LC_lt T Blk hE2 Cζ J' hJ'
  · rw [dif_neg hJ', dif_neg hJ']

/-- **The `R`-stage lane** (`R ≠ ⊥`), two-sidedly.  Clone of the `private` `GQ2.rStage_lane`
(`GQ2/ThmFourTwo.lean:290-377`): the closed system from `prop_8_9_of_sourcesN` at the
head-inflated enrichment `blockEnrichmentDK`, solved by SD-R2's `count_eq_of_closedRecursionK`
against the IH at the (145)/(148)/(153) bounds.

The model's `(R, horient)` reciprocity binders are gone — they were the `G_ℚ₂` side's ramified
Gauss input, and that side is now a record (memo §3.1). -/
private theorem rStage_laneN (S₁ S₂ : SourceDataN n q P hP nuP SN) (F : BoundaryFrameK q P H E)
    (hq0 : q ≠ 0) (hqe : Even q)
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (Blk : SectionSeven.MinimalBlock T.LY)
    (_hstack : ¬ SectionSeven.IsScalarStack T.LY) (hR : Blk.frattiniK ≠ ⊥) (N : ℕ)
    (hcard : Nat.card ↥T.LY = N)
    (IH : ∀ m, m < N → ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [DiscreteTopology Z]
      [Finite Z] (T' : MarkedTarget H E Z), Nat.card ↥T'.LY = m →
      exactImageCountK S₁.b F T' = exactImageCountK S₂.b F T') :
    exactImageCountK S₁.b F T = exactImageCountK S₂.b F T := by
  classical
  by_cases hhead : Function.Surjective
      (fun x : ↥(boundarySubgroupQ q nuP) => (F.frameMap x).1)
  · -- head covered: obtain the closed system and feed the solver
    have hhead₁ : Function.Surjective (fun γ : S₁.Γ => (F.frameMap (S₁.b γ)).1) :=
      hhead.comp S₁.b_surjective
    have hhead₂ : Function.Surjective (fun γ : S₂.Γ => (F.frameMap (S₂.b γ)).1) :=
      hhead.comp S₂.b_surjective
    -- block normality instances (the `blockEnrichmentDK` section hypotheses)
    haveI : (Blk.S.subgroupOf Blk.P).Normal := Blk.hS.subgroupOf Blk.P
    haveI : Blk.K.Normal := Blk.hK
    haveI : Blk.frattiniK.Normal := SectionSeven.frattiniLike_normal Blk.K Blk.hK
    -- Lemma 7.2's block facts, source-independent (SD-R1's `lemma_7_2_core`)
    obtain ⟨hRK, hR2, -⟩ := lemma_7_2_core Blk
    -- the chief-factor structure of the enrichment module
    have hSimp := SectionNine.blockHsimple T Blk
    have hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
        (∀ g : (blockFrameImpl T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤ :=
      hSimp.2
    have hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0 := by
      haveI : Nontrivial (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod := hSimp.1
      exact exists_ne 0
    have hnt : ∃ (g : (blockFrameImpl T Blk hE2).YC)
        (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v :=
      SectionNine.blockHnt T Blk
    -- the Gauss-`Z` residues at the shared `G0`, each side contributing its record leaf
    obtain ⟨G0, hGaussZ₁, hGaussZ₂⟩ := gaussZ_obtain_blockDK_of_sourcesN T Blk hE2 hq0 hqe
      S₁ S₂ F hsimple hVne hnt
    -- the closed system (Prop. 8.9 over the two records)
    obtain ⟨μ, G0', DT, instDT, phase, hDTpos, h₁, h₂⟩ :=
      prop_8_9_of_sourcesN S₁ S₂ T Blk hE2 (blockEnrichmentDK T Blk hE2 hq0 hqe F) F
        hhead₁ hhead₂ hRK hR2 hsimple hVne hnt G0 hGaussZ₁ hGaussZ₂
    letI := instDT
    -- IH at the `B`-stage ((145b), needs `R ≠ ⊥`)
    have hTB : exactImageCountK S₁.b F (blockFrameImpl T Blk hE2).TB
        = exactImageCountK S₂.b F (blockFrameImpl T Blk hE2).TB := by
      refine IH _ ?_ _ (blockFrameImpl T Blk hE2).TB rfl
      exact hcard ▸ card_LB_lt T Blk hE2 hR
    -- IH at the `C`-stage ((145c))
    have hTC : exactImageCountK S₁.b F (blockFrameImpl T Blk hE2).TC
        = exactImageCountK S₂.b F (blockFrameImpl T Blk hE2).TC := by
      refine IH _ ?_ _ (blockFrameImpl T Blk hE2).TC rfl
      exact hcard ▸ card_LC_lt T Blk hE2
    -- IH at the pulled `B`-strata ((148)) and phase-cover agreement ((141)/(142)); then solve.
    exact count_eq_of_closedRecursionK (blockFrameImpl T Blk hE2) S₁.b S₂.b F μ G0' DT phase
      SN.homScalar _ _ SN.homScalar_pos h₁ h₂ hDTpos.ne' hTB hTC
      (fun l h J' hJtop hJC =>
        rStage_pullN S₁ S₂ F T hE2 Blk hR N hcard IH l h J' hJtop hJC)
      (fun l h ζ => rStage_phaseN S₁ S₂ F T hE2 Blk N hcard IH (phase l h ζ))
  · -- head not covered: both counts vanish
    rw [exactImageCountK_eq_zero_of_not_headSurj S₁.b F T hhead,
      exactImageCountK_eq_zero_of_not_headSurj S₂.b F T hhead]

end Lanes

/-! ## The two-sided degree-`n` theorem (packet Thm 11.1, exact-image clause) -/

/-- **Theorem 4.2 over two abstract degree-`n` sources** — the SD-n obligation at the generic
level (packet Thm 11.1 `thm:source-abstract`, exact-image clause).  For any two sources over the
same slot `(q, P, hP, νP)` with the same numerics `SN`, any `K`-boundary frame and any
boundary-framed marked target, the exact-image lift counts agree.

Same strong induction on `|L_Y|` as the frozen `GQ2.thm_4_2_of_sources`
(`GQ2/ThmFourTwo.lean:386`), with all three lanes two-sided.  Everything that pinned the second
source to `G_ℚ₂` (memo §3.1's removal list: `BoundaryMaps`, `(R, horient)`, the `AbsGalQ2`
instance binders, `absGalQ2_isTopologicallyFinitelyGenerated`, `liftsOver_card_local`,
`lemma_8_2_local`, `B.pro2F`/`ker_pro2F`, the `gaussZResidueD_local_*` twins and the whole
`prop_8_9` `_local` discharge block) is gone; what remains are the three slot conditions
`hq0`/`hqe`/`hnuP`, which are properties of the slot rather than of either source.

**Axiom-wise this is the theorem's whole point**: its print is std-3 — no B-axiom whatsoever.
The B-axioms of the `ℚ₂` capstone entered only through the `G_ℚ₂` side's `_local` leaves, so
under the two-sided restatement they leave the spine entirely and re-enter only at an
instantiation (at `n = 1` through `sourceF_N`, at general `K` through the ASK supply package). -/
theorem thm_4_2_of_sourcesN (S₁ S₂ : SourceDataN n q P hP nuP SN)
    (F : BoundaryFrameK q P H E) (hq0 : q ≠ 0) (hqe : Even q)
    (hnuP : Function.Surjective nuP)
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1) :
    exactImageCountK S₁.b F T = exactImageCountK S₂.b F T := by
  -- Strong induction on the marked-kernel size `N = |L_Y|` (§9, pp. 44–47), generalizing the
  -- whole target `(Y, 𝒴)` exactly as in the model.
  suffices h : ∀ (N : ℕ) (Y : Type) [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
      [Finite Y] (T : MarkedTarget H E Y), Nat.card ↥T.LY = N →
      exactImageCountK S₁.b F T = exactImageCountK S₂.b F T by
    exact h (Nat.card ↥T.LY) Y T rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro Y instGY instTY instDY instFY T hcard
    by_cases hstack : SectionSeven.IsScalarStack T.LY
    · -- **Terminal lane** (§9.1–9.2): the two exact-image problems are identified through the
      -- common marked pro-2 quotient (SD-R2's `terminal_count_eqK`, via `ker_pro2`).
      exact terminal_count_eqK hq0 hqe hP hnuP F S₁.b S₁.b_surjective S₁.pro2
        S₁.pro2_surjective (fun _ => rfl) S₁.ker_pro2 S₂.b S₂.b_surjective S₂.pro2
        S₂.pro2_surjective (fun _ => rfl) S₂.ker_pro2 T hE2 hstack
    · -- Inductive case: a nonscalar chief factor exists; choose the §7 minimal block.
      obtain ⟨Blk⟩ := SectionSeven.exists_minimalBlock T.normal T.isPGroup_two hstack
      by_cases hR : Blk.frattiniK = ⊥
      · -- **`M`-stage lane** (`R = ⊥`, §9.2)
        exact mStage_laneN S₁ S₂ F T hE2 Blk hR N hcard IH
      · -- **`R`-stage lane** (`R ≠ ⊥`, §9.3)
        exact rStage_laneN S₁ S₂ F hq0 hqe T hE2 Blk hstack hR N hcard IH

/-! ## §10 at the `K`-boundary — passage to all finite quotients

Clone of the boundary-dependent half of `GQ2/SectionTen.lean` (memo §3.2's "K-clone of §10's
frame summation").  The **2-core layer is not cloned**: `twoCore`, its three properties, the
marked target `tameTarget G` and the trivial decoration `E₀` are boundary-free and are the
model's, by import.  What moves is exactly the tame coordinate (`Ttame → Tq q`), the frame
builder, the frame index and Lemma 10.1's descent. -/

section SectionTenK

open SectionTen

/-- **`T_q` is topologically finitely generated** (by `σ_q, τ_q`), in the `Finset` form the
hom-finiteness machinery consumes.  Clone of `GQ2.SectionTen.ttame_tfg`
(`GQ2/SectionTen.lean:118`); `topGen_tq` is F3's. -/
theorem tq_tfg (q : ℕ) :
    ∃ s : Finset (Tq q), (Subgroup.closure (s : Set (Tq q))).topologicalClosure = ⊤ := by
  classical
  exact ⟨{tqSigma q, tqTau q}, by simpa using topGen_tq q⟩

/-- **The §10 frame index** at the `K`-boundary: continuous surjections `T_q ↠ G/O₂(G)`.  Clone
of `GQ2.SectionTen.TameFrames` (`GQ2/SectionTen.lean:113`). -/
def TameFramesK (q : ℕ) (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [Finite G] : Type :=
  {α : ContinuousMonoidHom (Tq q) (G ⧸ twoCore G) // Function.Surjective α}

/-- The frame index is finite (`T_q` is topologically 2-generated).  Clone of the model's
`instance : Finite (TameFrames G)` (`GQ2/SectionTen.lean:126`). -/
instance instFiniteTameFramesK (q : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [Finite G] : Finite (TameFramesK q G) := by
  haveI : Finite (ContinuousMonoidHom (Tq q) (G ⧸ twoCore G)) :=
    finite_continuousMonoidHom (tq_tfg q) _
  exact Subtype.finite

/-- **The §10 boundary frame** of a tame frame `α : T_q ↠ H` at the `K`-boundary (decoration
`E₀` trivial, `ψ̄ = 1`).  Clone of `GQ2.SectionTen.tameFrame` (`GQ2/SectionTen.lean:102`). -/
noncomputable def tameFrameK {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] (α : ContinuousMonoidHom (Tq q) H) (hα : Function.Surjective α) :
    BoundaryFrameK q P H E₀ where
  alpha := α
  alpha_surjective := hα
  exponent_two := fun _ => rfl
  psiBar := 1

section TameCoordK

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-- **The tame coordinate** `pr₁ ∘ b : Γ → T_q` of a `K`-boundary map.  Clone of
`GQ2.SectionTen.tameCoord` (`GQ2/SectionTen.lean:141`).  For a record this is `S.tame` on the
nose (`SourceDataN.b_apply_coe`). -/
noncomputable def tameCoordK (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) :
    ContinuousMonoidHom Γ (Tq q) where
  toFun γ := (b γ : Tq q × P).1
  map_one' := by rw [map_one]; rfl
  map_mul' x y := by rw [map_mul]; rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).comp b.continuous_toFun

@[simp] theorem tameCoordK_apply (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (γ : Γ) : tameCoordK b γ = (b γ : Tq q × P).1 := rfl

/-- The tame coordinate of a record's boundary map **is** its `tame` field — `rfl`. -/
@[simp] theorem tameCoordK_b (S : SourceDataN n q P hP nuP SN) : tameCoordK S.b = S.tame := rfl

end TameCoordK

section ExhaustionK

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]

omit [IsTopologicalGroup Γ] [Finite G] in
/-- The image of the wild kernel under a continuous epimorphism lands in the 2-core.  Clone of
`GQ2.SectionTen.map_wildKer_le_twoCore` (`GQ2/SectionTen.lean:165`) — verbatim. -/
theorem map_wildKer_le_twoCoreK (hwild : IsProP 2 (tameCoordK b).toMonoidHom.ker)
    (f : ContSurj Γ G) :
    ((tameCoordK b).toMonoidHom.ker.map f.1.toMonoidHom) ≤ twoCore G :=
  le_twoCore ((MonoidHom.normal_ker _).map f.1.toMonoidHom f.2)
    (SectionThree.isPGroup_map_of_isProP hwild f.1.toMonoidHom f.1.continuous_toFun)

/-- **The descended homomorphism** of Lemma 10.1's forward map at the `K`-boundary.  Clone of
`GQ2.SectionTen.inducedHom` (`GQ2/SectionTen.lean:174`) — verbatim. -/
noncomputable def inducedHomK (htame : Function.Surjective (tameCoordK b))
    (hwild : IsProP 2 (tameCoordK b).toMonoidHom.ker) (f : ContSurj Γ G) :
    Tq q →* G ⧸ twoCore G :=
  (tameCoordK b).toMonoidHom.liftOfSurjective htame
    ⟨(QuotientGroup.mk' (twoCore G)).comp f.1.toMonoidHom, fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact map_wildKer_le_twoCoreK b G hwild f (Subgroup.mem_map_of_mem _ hx)⟩

omit [IsTopologicalGroup Γ] [Finite G] in
/-- The defining property of the descent.  Clone of `GQ2.SectionTen.inducedHom_tameCoord`
(`GQ2/SectionTen.lean:184`). -/
theorem inducedHomK_tameCoordK (htame : Function.Surjective (tameCoordK b))
    (hwild : IsProP 2 (tameCoordK b).toMonoidHom.ker) (f : ContSurj Γ G) (γ : Γ) :
    inducedHomK b G htame hwild f (tameCoordK b γ) = QuotientGroup.mk' (twoCore G) (f.1 γ) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ γ

/-- **The induced tame frame** of a continuous epimorphism.  Clone of
`GQ2.SectionTen.inducedFrame` (`GQ2/SectionTen.lean:194`) — verbatim; `T_q` is profinite, hence
Hausdorff, so the closed-map/quotient-map argument is unchanged. -/
noncomputable def inducedFrameK [CompactSpace Γ] (htame : Function.Surjective (tameCoordK b))
    (hwild : IsProP 2 (tameCoordK b).toMonoidHom.ker) (f : ContSurj Γ G) : TameFramesK q G :=
  have hquot : Topology.IsQuotientMap (tameCoordK b) :=
    (tameCoordK b).continuous_toFun.isClosedMap.isQuotientMap (tameCoordK b).continuous_toFun
      htame
  ⟨{ toMonoidHom := inducedHomK b G htame hwild f
     continuous_toFun := hquot.continuous_iff.mpr <|
       (QuotientGroup.continuous_mk.comp f.1.continuous_toFun).congr fun γ =>
         (inducedHomK_tameCoordK b G htame hwild f γ).symm },
   fun y => by
     obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (twoCore G) y
     obtain ⟨γ, rfl⟩ := f.2 g
     exact ⟨tameCoordK b γ, inducedHomK_tameCoordK b G htame hwild f γ⟩⟩

omit [IsTopologicalGroup Γ] in
/-- **Lemma 10.1 (exhaustion by tame boundary frames)** at the `K`-boundary, partition form.
Clone of `GQ2.SectionTen.lemma_10_1` (`GQ2/SectionTen.lean:217`) — verbatim. -/
theorem lemma_10_1K [CompactSpace Γ] (htame : Function.Surjective (tameCoordK b))
    (hwild : IsProP 2 (tameCoordK b).toMonoidHom.ker) :
    Nonempty (ContSurj Γ G ≃
      (α : TameFramesK q G) × BoundaryLiftsK b (tameFrameK (P := P) α.1 α.2) (tameTarget G)) := by
  refine ⟨(Equiv.sigmaFiberEquiv (inducedFrameK b G htame hwild)).symm.trans
    (Equiv.sigmaCongrRight fun α => Equiv.subtypeEquivRight fun f => ?_)⟩
  constructor
  · -- membership in the fiber of `α_f` IS the boundary-framing condition for `α_f`
    rintro rfl γ
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    exact (inducedHomK_tameCoordK b G htame hwild f γ).symm
  · -- disjointness: the framing condition for `α` forces `α_f = α`
    intro hf
    refine Subtype.ext (ContinuousMonoidHom.ext fun t => ?_)
    obtain ⟨γ, rfl⟩ := htame t
    exact (inducedHomK_tameCoordK b G htame hwild f γ).trans (congrArg Prod.fst (hf γ))

/-- **Lemma 10.1, counting form** at the `K`-boundary — the frame summation the two-sided
theorem is consumed through.  Clone of `GQ2.SectionTen.card_contSurj_eq`
(`GQ2/SectionTen.lean:241`).

⚠ Deviation from the model: the model can `omit [IsTopologicalGroup Γ]` here; the clone cannot,
because `finite_boundaryLiftsK` (`Recursion/Frame.lean:111`) carries that instance where the
model's `finite_boundaryLifts` does not.  Cosmetic — both sources are profinite. -/
theorem card_contSurjK_eq [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (htame : Function.Surjective (tameCoordK b))
    (hwild : IsProP 2 (tameCoordK b).toMonoidHom.ker)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) :
    Nat.card (ContSurj Γ G)
      = ∑ᶠ α : TameFramesK q G,
          exactImageCountK b (tameFrameK (P := P) α.1 α.2) (tameTarget G) := by
  classical
  obtain ⟨e⟩ := lemma_10_1K b G htame hwild
  haveI : ∀ α : TameFramesK q G,
      Finite (BoundaryLiftsK b (tameFrameK (P := P) α.1 α.2) (tameTarget G)) :=
    fun α => finite_boundaryLiftsK b (tameFrameK (P := P) α.1 α.2) (tameTarget G) hfg
  haveI : Fintype (TameFramesK q G) := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma, finsum_eq_sum_of_fintype]
  rfl

end ExhaustionK

end SectionTenK

/-! ## The surjection-count and reconstruction corollaries (packet Thm 11.1, clauses 2 and 3) -/

/-- **Packet Thm 11.1, surjection-count clause**: two sources over the same slot have identical
continuous-surjection counts onto every finite group.  The `K`-analogue of `eq_154`
(`GQ2/SectionTenSources.lean:103`): `card_contSurjK_eq` rewrites each count as the sum of the
fixed-frame exact-image counts over `TameFramesK q G`, and `thm_4_2_of_sourcesN` equates them
frame by frame (`hE2` is trivial on `E₀ = PUnit`).

`htame`/`hwild` are §10's two per-source conditions — the tame coordinate is onto with pro-2
kernel.  They are **not** `SourceDataN` fields (the recursion never needs them), so they stay
instantiation-side, exactly as the model's `tameCoord_b*_surjective`/`_ker_isProP` do. -/
theorem contSurj_card_eq_of_sourcesN (S₁ S₂ : SourceDataN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₁ : Function.Surjective S₁.tame) (hwild₁ : IsProP 2 S₁.tame.toMonoidHom.ker)
    (htame₂ : Function.Surjective S₂.tame) (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker)
    (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G] :
    Nat.card (ContSurj S₁.Γ G) = Nat.card (ContSurj S₂.Γ G) := by
  have hE2 : ∀ e : SectionTen.E₀, e ^ 2 = 1 := fun _ => Subsingleton.elim _ _
  rw [card_contSurjK_eq S₁.b G htame₁ hwild₁ S₁.tfg,
    card_contSurjK_eq S₂.b G htame₂ hwild₂ S₂.tfg]
  exact finsum_congr fun α =>
    thm_4_2_of_sourcesN S₁ S₂ (tameFrameK α.1 α.2) hq0 hqe hnuP (SectionTen.tameTarget G) hE2

/-- **Packet Thm 11.1, reconstruction clause**: two sources over the same slot are isomorphic as
topological groups.  The surjection-count clause plus the two records' `tfg` fields, fed to the
unchanged, boundary-free `GQ2.reconstruction` (`GQ2/Reconstruction.lean:396`, Lemma 2.5) — the
memo §3.2 route, with no new mathematics on this file's side. -/
theorem nonempty_continuousMulEquiv_of_sourcesN (S₁ S₂ : SourceDataN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₁ : Function.Surjective S₁.tame) (hwild₁ : IsProP 2 S₁.tame.toMonoidHom.ker)
    (htame₂ : Function.Surjective S₂.tame) (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker) :
    Nonempty (ContinuousMulEquiv S₁.Γ S₂.Γ) :=
  reconstruction S₁.tfg S₂.tfg fun G _ _ _ _ =>
    contSurj_card_eq_of_sourcesN S₁ S₂ hq0 hqe hnuP htame₁ hwild₁ htame₂ hwild₂ G

/-! ## The `n = 1` regression  (memo §8 acceptance (1))

`thm_4_2`'s **statement**, re-derived through the clone at `n = 1` from SD2's adapters.  The
frozen `GQ2.thm_4_2` (`GQ2/ThmFourTwo.lean:443`) is untouched: this is a second, independent
derivation of the same proposition, and the point of it is that it typechecks *at the old
boundary with no transport* — probes P1/P1b (`boundarySubgroupQ 2 nuTwo = boundarySubgroup` and
`exactImageCountK … = exactImageCount …`, both `rfl`) plus SD2's `sourceA_N_b`/`sourceF_N_b`
(also `rfl`) make the whole chain definitional. -/

section Regression

/-- The inverse of `BoundaryFrameK.toBoundaryFrame` (`Recursion/Frame.lean:132`): a `ℚ₂`
boundary frame **is** a `K`-frame at `q = 2`, `P := PiBd`, because `Tq 2 = Ttame` is `rfl` — the
four fields are literally the same terms.  Declared prefix-style (not as `BoundaryFrame.…`) to
keep the frozen `GQ2.BoundaryFrame` namespace untouched. -/
def boundaryFrameK (F : BoundaryFrame H E) : BoundaryFrameK 2 PiBd H E where
  alpha := F.alpha
  alpha_surjective := F.alpha_surjective
  exponent_two := F.exponent_two
  psiBar := F.psiBar

/-- The two frame coercions are mutually inverse — `rfl` both ways (structure eta). -/
@[simp] theorem boundaryFrameK_toBoundaryFrame (F : BoundaryFrame H E) :
    (boundaryFrameK F).toBoundaryFrame = F := rfl

/-- **REGRESSION (memo §8 acceptance (1)): `thm_4_2`'s statement, through the degree-`n` clone.**

Byte-for-byte the frozen `GQ2.thm_4_2`'s statement (`GQ2/ThmFourTwo.lean:443-449`) — same
binders, same conclusion `exactImageCount B.bA F T = exactImageCount B.bF F T` at the *old*
boundary and the *old* frame type — proved by instantiating the two-sided degree-`n` theorem at
SD2's `sourceA_N B` and `sourceF_N B R horient`.

The instantiation is **rfl-level: no transport, no `rw`, no cast.**  Every bridge fires
definitionally: `boundarySubgroupQ 2 nuTwo = boundarySubgroup`, `(sourceA_N B).b = B.bA`,
`(sourceF_N B R horient).b = B.bF`, `(boundaryFrameK F).frameMap = F.frameMap`,
`exactImageCountK = exactImageCount`.  The three slot conditions are discharged by
`two_ne_zero`, `even_two` and `SectionThree.nuTwo_surjective`.

Note where the `ℚ₂`-specific binders sit: `B`, `(R, horient)` and the two `AbsGalQ2` instance
binders appear **only** as arguments to `sourceF_N` — memo §3.1's migration, executed. -/
theorem thm_4_2_via_N (B : BoundaryMaps) (F : BoundaryFrame H E)
    (R : LocalReciprocity) (horient : TameUnitOrientation R B.tameF)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1) :
    exactImageCount B.bA F T = exactImageCount B.bF F T :=
  thm_4_2_of_sourcesN (sourceA_N B) (sourceF_N B R horient) (boundaryFrameK F)
    two_ne_zero even_two SectionThree.nuTwo_surjective T hE2

/-- The same regression with the **candidate** source `Γ_R` on the left (R32's consumption
shape): `sourceR_N` against `sourceF_N`, under the B-Lab binder.  Also rfl-level. -/
theorem thm_4_2_gammaR_via_N [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hBLab : BLabHypothesis) (B : BoundaryMaps) (F : BoundaryFrame H E)
    (R : LocalReciprocity) (horient : TameUnitOrientation R B.tameF)
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1) :
    exactImageCount (GQ2.sourceR hBLab).b F T = exactImageCount B.bF F T :=
  thm_4_2_of_sourcesN (sourceR_N hBLab) (sourceF_N B R horient) (boundaryFrameK F)
    two_ne_zero even_two SectionThree.nuTwo_surjective T hE2

end Regression

end GQ2.Dyadic
