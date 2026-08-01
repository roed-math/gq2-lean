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
sorry-free and axiom-clean.  Print check performed per declaration; see the section notes.
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

end GQ2.Dyadic
