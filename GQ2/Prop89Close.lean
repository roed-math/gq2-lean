import GQ2.KeystoneDelta
import GQ2.RStageLocal
import GQ2.Half139Local
import GQ2.HalfTorsorGammaA
import GQ2.FinitelyGenerated
import GQ2.PhaseLIndep
import GQ2.PhaseMuIndep
import GQ2.PhaseGaussLIndep
import GQ2.GaussZReduction
import GQ2.Phase140Assembly
import GQ2.RStageGammaA
import GQ2.Phase140Local
import GQ2.CardH2GammaA
import GQ2.MStageCountGammaA

/-!
# The P-16 capstone: `prop_8_9` at the concrete block frame  (P-16d6e)

**Proposition 8.9 (closed exact-image recursion)**, relocated here from `SectionEight.lean`
(which cannot name `blockFrameImpl` — it sits above `BlockFrameImpl.lean` in the import
order; `thm_4_2`-relocation pattern).  Two reviewed statement actions relative to the
original draft (`docs/p16d6e-assembly-plan.md` §1, the authoritative record):

* **Per-`λ` phase family** — the paper's (134) classes `Δ_{χ,κ}` carry the scalar-pushout
  class `κ = κ_λ` of the `λ`-cover, so the family is
  `phase : (l : DR) → l ≠ zeroDR → DT → CentralCover YC` (the shared-family draft form was
  a transcription deviation; it would force an unproven `zBC`-l-independence).
* **Concrete block frame + hypothesis ledger** — the statement is at
  `RF := blockFrameImpl T Blk hE2` (the only intended consumer: SectionNine's inductive
  branch at `blockFrame`/`blockEnrichment`, P-17c/P-17h; general-`RF` (136) is not provable
  — no axioms tie a bare frame's `DR`/`zR`/`mB` to obstruction theory).  Hypothesis-side
  (dischargers recorded in the plan doc §1): `hE2` (P-17a standing), `hfgF` (**B1**, first
  consumption reserved to P-17i), `hheadA`/`hheadF` (§9 boundary data), `hsimple`/`hVne`/
  `hnt` (the block's chief-factor structure, P-17h — `hnt` = `SectionNine.blockHnt`; the
  former `hfaith` was weakened to it at the P-17i coordination flag, 2026-07-08:
  faithfulness is NOT block-derivable, and only `hnt` was consumed), `hG0indep` (c3-G0's
  `gaussSum_qbar_l_indep_*` at the block's tame package, P-17h).
* Conclusion strengthened with `0 < Nat.card DT` (P-17i; free — `0 ∈ (T^∨)^C`).

## Skeleton status (P-16d6e7, skeleton-first per the row plan)

The witness assembly below is **plumbing-complete**: the `hex`-split, the shared
`DT := (T^∨)^C` at a reference `λ₀` (definitionally `λ`-independent — `radData`'s `T`/`hT`
are the literal frame fields), the `dite`-phase family with its `dif_pos`-reduction
(`phaseFamily_pos`), the shared `μ = #V·μ₀` value (`muZero`, read at `λ₀` and transported by
`tcocycle_card_l_indep`), and the two `prop_8_9_aux` splices.  `hRK`/`hR2` are discharged
internally (`lemma_7_2` at `π := T.piY`, `cH := F.alpha` — the plan-doc ledger) and `hfgA`
internally (`gammaA_topologicallyFinitelyGenerated`); `hnt` is a hypothesis (the block's
`nontrivial_action`, via `SectionNine.blockHnt`).

**Live**: the `¬hex` branch entirely; both `stageR136` fields; the full local (`G_ℚ₂`)
input bundle (`half139_local`, `phase140_local` — P-16d6e3 closed); the `Γ_A` `half139`
field (`half139_gammaA` below — P-16d6e6, `lemma_8_6_gammaA` + the P-17i
`liftsOver_card_gammaA` through `half139_via_radData`).  **Sorried (1)**: the `Γ_A`
`phase140` field (needs P-16d6e6's `phase140_gammaA` mirror — `hZcard_gammaA`/`hsep_A` ✓
landed, `hpartial_A`/`tcocycle_card_gammaA` open; consume with `phaseFamily_pos` +
`hGaussZA l h` exactly as the local branch).
-/

namespace GQ2

namespace SectionEight

open SectionSeven AffineTLift CentralObstruction ContCoh LocalLiftingDuality FoxH
open scoped Classical

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-! ## The shared witness data: descent unpacking, phase family, `μ₀` -/

section PhaseWitness

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}

/-- **The (140) zero-edge unpacking**: the `RecursionInputs.phase140` hypothesis *is* the
descent condition of the assembled per-`λ` datum (`Enrichment.radData_noDescent_iff` is
`Iff.rfl`), so it unpacks verbatim to an `AffineTLift.Descent`. -/
noncomputable def descentOf (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hN : ∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) :
    Descent (En.radData l h) :=
  ⟨hN.choose, hN.choose_spec.1, hN.choose_spec.2.1, hN.choose_spec.2.2⟩

/-- The zero-cocycle (split) double cover `𝔽₂ × C₀`: the junk value of the phase family off
the zero-edge locus.  (140)'s hypothesis restricts attention to the locus, so this value is
never inspected. -/
noncomputable def trivialPhaseCover (C0 : Type) [Group C0] [Finite C0] : CentralCover C0 :=
  centralCoverOfCocycle (fun _ => (0 : ZMod 2)) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl)

/-- **The shared per-`λ` phase family** (the paper's `Δ_{ζ,κ_λ}`-covers, (134)): on the
zero-edge locus, the `phaseChi`-cover through the unpacked descent; off it, the trivial
cover.  The phase index `ζ` is typed at a reference `(l₀, h₀)`: `TCharC (En.radData l h)`
is **definitionally** `(l,h)`-independent (`radData`'s `T`/`hT` are the literal frame
fields `RF.TBsub`/`RF.TBsub_normal` — plan §1A), so the same `ζ` is accepted at every `λ`. -/
noncomputable def phaseFamily (En : RF.Enrichment) (l₀ : RF.DR) (h₀ : l₀ ≠ RF.zeroDR)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (ζ : ↥(TCharC (En.radData l₀ h₀))) :
    CentralCover RF.YC :=
  if hN : ∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N then
    phaseChi En l h (descentOf En l h hN) ζ
  else
    trivialPhaseCover RF.YC

/-- The `dif_pos`-reduction of the phase family on the zero-edge locus (the pre-analyzed
elaboration risk (b) of the row: the rewrite is proof-irrelevant in the stored descent
witness, since `descentOf` consumes whichever proof the caller holds). -/
theorem phaseFamily_pos (En : RF.Enrichment) (l₀ : RF.DR) (h₀ : l₀ ≠ RF.zeroDR)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hN : ∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N)
    (ζ : ↥(TCharC (En.radData l₀ h₀))) :
    phaseFamily En l₀ h₀ l h ζ = phaseChi En l h (descentOf En l h hN) ζ :=
  dif_pos hN

/-- **The shared `T`-cocycle count `μ₀`** (the paper's `#Z¹(T_B)`, (132)), read at the
reference `(l₀, h₀)`.  Frame-level (`radData`'s `T`/`M` are the literal `RF.TBsub`/`RF.MB`),
hence `(l,h)`-independent by `tcocycle_card_l_indep`; its per-`ρ` constancy and value are
the sources' `tcocycle_card_*` theorems (local ✓ e3; `Γ_A` = e6). -/
noncomputable def muZero (En : RF.Enrichment) (l₀ : RF.DR) (h₀ : l₀ ≠ RF.zeroDR) : ℕ :=
  Nat.card (Additive ↥(En.radData l₀ h₀).T) ^ 2
    * Nat.card (fixedPts (RF.YB ⧸ (En.radData l₀ h₀).M)
        (ElemDual (Additive ↥(En.radData l₀ h₀).T)))

end PhaseWitness

/-! ## The `Γ_A` (139) half count (P-16d6e6)

The `half139_local` twin: both deep inputs are already banked — `lemma_8_6_gammaA`
(P-16c, the word-side half-torsor count) and the P-17i `M`-lift count
`liftsOver_card_gammaA` (`MStageCountGammaA`), the latter transported through the
`LiftsOver ↔ MLifts` bridge (`RadicalEdgeBridge.liftsOver_equiv`).  Wired through the
source-generic `half139_via_radData`. -/

section Half139GammaA

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- **`hlem86M` for `Γ_A`** — the source's Lemma 8.6 half-torsor count over every boundary
lift, for the radical datum `En.radData l h`, threading the `NoDescent` field hypothesis
(the `hlem86M_local` mirror; no `hfg` needed — `lemma_8_6_gammaA` is word-side). -/
theorem hlem86M_gammaA
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom GammaA ↥boundarySubgroup)
    (F : BoundaryFrame H E) (En : RF.Enrichment)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hedge : ¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N)
    (ρ : BoundaryLifts b F RF.TC) :
    2 * Nat.card {f : MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) //
        f.Central}
      = Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) :=
  lemma_8_6_gammaA (En.radData l h) hedge (RF.rhoPrime b F (En.radData l h) rfl ρ)
    (rhoPrime_surjective RF b F (En.radData l h) rfl ρ)

/-- **`hMcountM` for `Γ_A`** — the unrestricted `M`-lift count `#(M-lifts) = |M_B|²`: the
P-17i `LiftsOver` count transported through the `LiftsOver ↔ MLifts` bridge. -/
theorem hMcountM_gammaA
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom GammaA ↥boundarySubgroup)
    (F : BoundaryFrame H E) (En : RF.Enrichment)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = (Nat.card ↥RF.MB) ^ 2 :=
  (Nat.card_congr (RF.liftsOver_equiv b F (En.radData l h) rfl ρ)).symm.trans
    (RF.liftsOver_card_gammaA b F ρ)

/-- **P-16d6e6 deliverable**: the (139) half count for `Γ_A`, in the exact shape of the
`RecursionInputs.half139` field (the `half139_local` twin). -/
theorem half139_gammaA
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom GammaA ↥boundarySubgroup)
    (F : BoundaryFrame H E) (En : RF.Enrichment)
    (hfg : ∃ s : Finset GammaA, (Subgroup.closure (s : Set GammaA)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hedge : ¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) :
    2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC :=
  half139_via_radData RF b F En l h hfg
    (hlem86M_gammaA RF b F En l h hedge) (hMcountM_gammaA RF b F En l h)

end Half139GammaA

/-- **Proposition 8.9 (closed exact-image recursion)**: for the concrete block frame of a
boundary-framed target with a §7 simple-head block, there are **shared** data
`(μ, G⁰, D_T)` and a **per-`λ`** phase family such that the boxed system (136)–(142) holds
for **both sources**.  Every count on the right sides concerns a target with strictly
smaller marked 2-kernel, so the system is a closed deterministic recursion (paper, end of
§8).  [P-16 statement — relocated & amended at P-16d6e, see the module docstring; proof =
the P-16d6e assembly, axioms ≤ {B6, B7, B9} per App. D.] -/
theorem prop_8_9 (B : BoundaryMaps) {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (En : (blockFrameImpl T Blk hE2).Enrichment) (F : BoundaryFrame H E)
    [CompactSpace GammaA] [TotallyDisconnectedSpace GammaA] [IsTopologicalGroup GammaA]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [IsTopologicalGroup AbsGalQ2]
    (hfgF : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (hheadA : Function.Surjective (fun γ : GammaA => (F.frameMap (B.bA γ)).1))
    (hheadF : Function.Surjective (fun γ : AbsGalQ2 => (F.frameMap (B.bF γ)).1))
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : (blockFrameImpl T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : (blockFrameImpl T Blk hE2).YC) (v : En.Vmod), g • v ≠ v)
    (G0 : ℤ)
    (hGaussZA : ∀ (l : (blockFrameImpl T Blk hE2).DR)
      (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR), GaussZResidue B.bA F En l h G0)
    (hGaussZF : ∀ (l : (blockFrameImpl T Blk hE2).DR)
      (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR), GaussZResidue B.bF F En l h G0) :
    ∃ (μ : ℕ) (G0' : ℤ) (DT : Type) (_ : Fintype DT)
      (phase : (l : (blockFrameImpl T Blk hE2).DR) →
        l ≠ (blockFrameImpl T Blk hE2).zeroDR → DT →
          CentralCover (blockFrameImpl T Blk hE2).YC),
      0 < Nat.card DT ∧
        ClosedRecursion (blockFrameImpl T Blk hE2) B.bA F μ G0' DT phase ∧
          ClosedRecursion (blockFrameImpl T Blk hE2) B.bF F μ G0' DT phase := by
  classical
  -- the block's R-layer facts, discharged internally (plan-doc ledger: `lemma_7_2` at
  -- `π := T.piY`, `cH := F.alpha`)
  obtain ⟨hRK, hR2, -⟩ :=
    lemma_7_2 T.piY T.piY_surjective T.ker_piY F.alpha F.alpha_surjective Blk
  -- `Γ_A` is t.f.g. (internal)
  have hfgA : ∃ s : Finset GammaA,
      (Subgroup.closure (s : Set GammaA)).topologicalClosure = ⊤ :=
    gammaA_topologicallyFinitelyGenerated
  by_cases hex : ∃ l : (blockFrameImpl T Blk hE2).DR, l ≠ (blockFrameImpl T Blk hE2).zeroDR
  · -- some `λ ≠ 0` exists: share `DT := (T^∨)^C`, read at a reference `λ₀`
    obtain ⟨l₀, h₀⟩ := hex
    haveI : Fintype ↥(TCharC (En.radData l₀ h₀)) := Fintype.ofFinite _
    refine ⟨Nat.card En.Vmod * muZero En l₀ h₀, G0, ↥(TCharC (En.radData l₀ h₀)),
      inferInstance, phaseFamily En l₀ h₀, card_TCharC_pos En l₀ h₀, ?_, ?_⟩
    · -- the `Γ_A` recursion
      refine prop_8_9_aux _ hfgA B.bA F lemma_8_2_gammaA hheadA _ _ _ _ ?_
      refine ⟨CardH2GammaA.stageR136_gammaA hE2 hRK hR2 B.bA F, fun l h hedge => ?_, fun l h hN => ?_⟩
      · exact half139_gammaA _ B.bA F En hfgA l h hedge
      · -- (140) for `Γ_A` — GATED on P-16d6e6's `phase140_gammaA` (the `phase140_local`
        -- mirror: `hZcard_gammaA` ✓; `hsep_A`/`hpartial_A`/`tcocycle_card_gammaA` open);
        -- consume with `phaseFamily_pos` + the shared `hμ`-transport + `hGaussZA l h`,
        -- exactly as the local branch below
        sorry
    · -- the `G_ℚ₂` recursion — fully live (P-16d6e3 closed)
      refine prop_8_9_aux _ hfgF B.bF F (lemma_8_2_local B) hheadF _ _ _ _ ?_
      refine ⟨RStageLocal.stageR136_local hE2 hRK hR2 hfgF B.bF F, fun l h hedge => ?_, fun l h hN => ?_⟩
      · exact half139_local _ B.bF F En hfgF l h hedge
      · -- the landed local (140) at the unpacked descent + the `dif_pos`-reduction
        have h140 := phase140_local B.bF F En l h (descentOf En l h hN) hfgF
          (muZero En l₀ h₀) G0 hsimple hVne hnt
          (fun ρ => (tcocycle_card_l_indep _ B.bF F En l h l₀ h₀ ρ).trans
            (tcocycle_card_local B.bF F En l₀ h₀ ρ))
          (hGaussZF l h)
        simp only [phaseFamily_pos En l₀ h₀ l h hN]
        exact h140
  · -- no nonzero `λ`: (137)–(140) are vacuous, and only the two (136) stages are live
    refine ⟨1, G0, PUnit, inferInstance, fun l h _ => absurd ⟨l, h⟩ hex, by simp, ?_, ?_⟩
    · exact prop_8_9_aux _ hfgA B.bA F lemma_8_2_gammaA hheadA _ _ _ _
        ⟨CardH2GammaA.stageR136_gammaA hE2 hRK hR2 B.bA F,
          fun l h => absurd ⟨l, h⟩ hex, fun l h => absurd ⟨l, h⟩ hex⟩
    · exact prop_8_9_aux _ hfgF B.bF F (lemma_8_2_local B) hheadF _ _ _ _
        ⟨RStageLocal.stageR136_local hE2 hRK hR2 hfgF B.bF F,
          fun l h => absurd ⟨l, h⟩ hex, fun l h => absurd ⟨l, h⟩ hex⟩

end SectionEight

end GQ2
