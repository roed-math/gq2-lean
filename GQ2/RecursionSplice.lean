import GQ2.RStageObstructionBuild
import GQ2.RadicalEdgeBridge
import GQ2.AffineTLift

/-!
# §8 capstone — the Prop 8.9 two-source splice  (P-16d6)

`GQ2.SectionEight.prop_8_9` asserts the boxed recursion system `ClosedRecursion` for **both**
sources `B.bA` (`Γ_A`) and `B.bF` (`G_ℚ₂`), sharing one witness `(μ, G0, DT, phase)`.  Its proof is
the final assembly of §8: `prop_8_9_aux` turns a per-source `RecursionInputs` bundle
(`stageR136` + `half139` + `phase140`, with `(137)`/`(138)` discharged internally) into
`ClosedRecursion`, and the two sources share the phase witness.

This file builds the splice **in a leaf, off the co-owned `SectionEight.lean`** (per the parallel
shared-tree convention): `prop_8_9_of` reduces `prop_8_9`'s conclusion to the per-source inputs +
witness, and the component-discharge lemmas feed those inputs from the landed
P-16d2/d3/d4/d5 APIs.  The final one-line splice into `prop_8_9` (`exact prop_8_9_of …`) is a
trivial coordinated edit to `SectionEight.lean` done last.

## Inputs (per source `s ∈ {A, F}`, `Γ_s ∈ {Γ_A, G_ℚ₂}`)

* `stageR136` — `RStageObstructionBuild.stageR136_ofRSepData` from a concrete `RObstructionData`
  + the source residues (`hsep_hom`, `hZcount`) + `hE2` (P-16d2).
* `half139` — `RecursionFrame.half139_of` (P-16d3) discharged by `centralOver_equiv`/`liftsOver_equiv`
  + `lemma_8_6_local` (`G_ℚ₂`) / `lemma_8_6_gammaA` (`Γ_A`) + the `M`-lift count (5.15/5.16).
* `phase140` — the `lemma_8_7`/`lemma_8_5`/Prop 8.8/`lemma_6_21`/cor 5.17 chain (P-16d4/d5).
* the witness `(μ, G0, DT, phase)` — `phaseFamily`/`centralCoverOfCocycle` (P-16d5).
* side conditions `hfg` / `hscalar` / `hhead` — the source's t.f.g., `#Hom(Γ,𝔽₂)=8`, head surjectivity.
-/

namespace GQ2

namespace SectionEight

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- **Prop 8.9, reduced to the per-source `RecursionInputs` + shared witness** (the splice backbone).
Given the shared phase witness `(μ, G0, DT, phase)`, the two per-source side-condition triples, and
the two `RecursionInputs` bundles, the boxed system holds for both sources — each via
`prop_8_9_aux`.  The remaining work (the component-discharge lemmas below) feeds the two
`RecursionInputs`. -/
theorem prop_8_9_of (B : BoundaryMaps)
    [CompactSpace GammaA] [TotallyDisconnectedSpace GammaA] [IsTopologicalGroup GammaA]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] [IsTopologicalGroup AbsGalQ2]
    {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (F : BoundaryFrame H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT] (phase : DT → CentralCover RF.YC)
    (hfgA : ∃ s : Finset GammaA, (Subgroup.closure (s : Set GammaA)).topologicalClosure = ⊤)
    (hheadA : Function.Surjective (fun γ : GammaA => (F.frameMap (B.bA γ)).1))
    (hfgF : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (hheadF : Function.Surjective (fun γ : AbsGalQ2 => (F.frameMap (B.bF γ)).1))
    (inpA : RecursionInputs RF B.bA F μ G0 DT phase)
    (inpF : RecursionInputs RF B.bF F μ G0 DT phase) :
    ∃ (μ' : ℕ) (G0' : ℤ) (DT' : Type) (_ : Fintype DT')
      (phase' : DT' → CentralCover RF.YC),
      ClosedRecursion RF B.bA F μ' G0' DT' phase' ∧
        ClosedRecursion RF B.bF F μ' G0' DT' phase' :=
  -- `hscalar` (#Hom(Γ,𝔽₂) = 8) is discharged internally from the proved `lemma_8_2_*`.
  ⟨μ, G0, DT, inferInstance, phase,
    prop_8_9_aux RF hfgA B.bA F lemma_8_2_gammaA hheadA μ G0 DT phase inpA,
    prop_8_9_aux RF hfgF B.bF F (lemma_8_2_local B) hheadF μ G0 DT phase inpF⟩

/-! ## `half139` reduced to the source's `MLifts`-level count (d3 bridge discharged)

`half139_via_radData` strips the P-16d3 bridge plumbing (`centralOver_equiv`/`liftsOver_equiv`
over `En.radData`) off the `half139` obligation, reducing it to the two **pure `MLifts` source
facts** for the transported lower map `ρ' = rhoPrime …`:

* `hlem86M` — the source's Lemma 8.6 half-torsor identity `2·#{central M-lifts} = #(M-lifts)`
  (`lemma_8_6_local` ✓ for `G_ℚ₂`; `lemma_8_6_gammaA` = P-16c for `Γ_A`), and
* `hMcountM` — the `M`-lift count `#(M-lifts) = |M_B|²` (props 5.15/5.16).

So a caller feeds `half139_of` (hence `RecursionInputs.half139`) directly from the source arithmetic,
with no `CentralOver`/`LiftsOver` bookkeeping. -/
theorem half139_via_radData {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hlem86M : ∀ ρ : BoundaryLifts b F RF.TC,
      2 * Nat.card {f : MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) //
          f.Central}
        = Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)))
    (hMcountM : ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
        = (Nat.card ↥RF.MB) ^ 2) :
    2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC := by
  refine RF.half139_of b F hfg l h (fun ρ => ?_) (fun ρ => ?_)
  · rw [Nat.card_congr (RF.centralOver_equiv b F l h (En.radData l h) rfl rfl ρ),
      Nat.card_congr (RF.liftsOver_equiv b F (En.radData l h) rfl ρ)]
    exact hlem86M ρ
  · rw [Nat.card_congr (RF.liftsOver_equiv b F (En.radData l h) rfl ρ)]
    exact hMcountM ρ

/-! ## `phase140` reduced to a clean "phase datum" (the `lemma_8_5`/8.7 analog of `stageR136_of`) -/

/-- **(140) reduced to the phase datum.**  Given the **μ-fibration** `hfib : zBC = μ · M` (Lemma
8.7's `T`-cocycle torsor count over the `V`-coordinate) and the **aggregated constrained-Gauss
identity** `hgauss` (`lemma_8_5` over the descended module `V = M_B/T_B`, `G0 = G(q̄)`), the (140)
display follows by pure algebra: `2|D_T|·zBC = 2|D_T|·μ·M = μ·(2|D_T|·M) = μ·(…)`.

This is the zero-edge analog of `stageR136_of` — it isolates the two hard counts (`hfib`, `hgauss`)
as a clean interface, exactly as `stageR136_of` isolated `hmB`/`hobs`/`hfib` for (136).  Constructing
`M`/`hfib`/`hgauss` for the concrete frame is the "(140) phase-module" O-half (see
`docs/p16d6-plan.md`): the fibration (`centralOver_equiv` + `lemma_8_7_count`) and `lemma_8_5` on the
`V`-descent, with the witness `(μ,G0,DT,phase)` defined alongside. -/
theorem phase140_ofPhaseData {Γ : Type} [Group Γ] [TopologicalSpace Γ] {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT] (phase : DT → CentralCover RF.YC)
    (l : RF.DR) (_h : l ≠ RF.zeroDR) (Mcount : ℕ)
    (hfib : RF.zBC b F l _h = μ * Mcount)
    (hgauss : 2 * (Nat.card DT : ℤ) * (Mcount : ℤ)
      = (Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
        + G0 * ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ) - exactImageCount b F RF.TC)) :
    2 * (Nat.card DT : ℤ) * RF.zBC b F l _h
      = μ * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
          + G0 * ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ) - exactImageCount b F RF.TC)) := by
  have hz : (RF.zBC b F l _h : ℤ) = (μ : ℤ) * (Mcount : ℤ) := by exact_mod_cast hfib
  rw [hz]
  linear_combination (μ : ℤ) * hgauss

end SectionEight

end GQ2
