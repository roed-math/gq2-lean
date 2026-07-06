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

/-- **The `zBC` fibration** over the lower exact-image map `ρ`: `zBC = Σ_ρ #CentralOver(ρ)`.  Both
the (139) and (140) counts rest on this (it is the first step inside `half139_of`); extracted here
so the (140) `hfib` datum `zBC = μ·M` gets it too — `zBC = Σ_ρ #CentralOver = Σ_ρ μ·M_ρ = μ·M`. -/
theorem zBC_eq_sum_centralOver {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR) :
    RF.zBC b F l h = ∑ᶠ ρ : BoundaryLifts b F RF.TC, Nat.card (RF.CentralOver b F l h ρ) := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLifts b F RF.TC) := finite_boundaryLifts b F RF.TC hfg
  haveI : Fintype (BoundaryLifts b F RF.TC) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, RecursionFrame.zBC]
  haveI : Finite {pr : BoundaryLifts b F RF.TC × ContinuousMonoidHom Γ RF.YB //
      (∀ γ : Γ, RF.piBC (pr.2 γ) = pr.1.1.1 γ) ∧ IsBoundaryLift b F RF.TB pr.2 ∧
        ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
          ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = pr.2 γ} := Subtype.finite
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv (fun x => x.1.1)).symm, Nat.card_sigma]
  exact Finset.sum_congr rfl (fun ρ _ => Nat.card_congr (RF.zBCfibreEquiv b F l h ρ))

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

/-! ## `hfib` level 2 — the per-`ρ` μ-partition of the central `M`-lifts -/

open AffineTLift CentralObstruction in
/-- **The per-`ρ` μ-partition** (P-16d6, `hfib` level 2): in the zero-edge regime the central
`M`-lifts of a lower map `ρ` split into the fibres of the `T`-reduction map `red_T`, and each
(nonempty) fibre is a free `Z¹_{Γ,ρ}(T)`-torsor of size `μ = #Z¹(T)` (`lemma_8_7_count`,
`Central` constant by `central_twist_iff`).  Hence the central-lift count factors as
`(#achievable central `T`-reductions) · μ`.  Summed over the `C`-image `ρ` (via
`zBC_eq_sum_centralOver`, after transport through `centralOver_equiv`) and combined with the
μ-independence `#Z¹(T) = μ`, this is the (140) `hfib` datum `zBC = μ·M` fed to
`phase140_ofPhaseData`; here `M = Σ_ρ #achievable central `T`-reductions` is the constrained
count of `lemma_8_5`. -/
theorem central_card_eq_reductions_mul_tcocycle
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg}
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)) (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) :
    Nat.card {f : MLifts D ρ // f.Central}
      = Nat.card ↥(Set.range (fun f : {f : MLifts D ρ // f.Central} => redT ρ f.1))
        * Nat.card (TCocycle D ρ) := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ Bg) := finite_continuousMonoidHom hfg Bg
  haveI : Finite (MLifts D ρ) := Subtype.finite
  haveI : Finite {f : MLifts D ρ // f.Central} := Subtype.finite
  -- the `T`-reduction map on central lifts, corestricted to its (finite) range
  set red : {f : MLifts D ρ // f.Central} → (Γ → Bg ⧸ D.T) := fun s => redT ρ s.1 with hred
  haveI : Fintype ↥(Set.range red) := Fintype.ofFinite _
  -- fibre `red` over its range and apply `lemma_8_7_count` to each fibre
  have hfibre : ∀ r : ↥(Set.range red),
      Nat.card {s : {f : MLifts D ρ // f.Central} //
        (⟨red s, s, rfl⟩ : ↥(Set.range red)) = r} = Nat.card (TCocycle D ρ) := by
    intro r
    obtain ⟨s₀, hs₀⟩ := r.2
    calc Nat.card {s : {f : MLifts D ρ // f.Central} //
              (⟨red s, s, rfl⟩ : ↥(Set.range red)) = r}
        = Nat.card {s : {f : MLifts D ρ // f.Central} // red s = r.1} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun _ => Subtype.ext_iff)
      _ = Nat.card {s : {f : MLifts D ρ // f.Central} // red s = red s₀} := by rw [← hs₀]
      _ = Nat.card {f : MLifts D ρ // f.Central ∧ redT ρ f = redT ρ s₀.1} := by
          rw [hred]
          exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (MLifts.Central D)
            (fun f => redT ρ f = redT ρ s₀.1))
      _ = Nat.card (TCocycle D ρ) := lemma_8_7_count ρ Dsc htriv s₀.1 s₀.2
  calc Nat.card {f : MLifts D ρ // f.Central}
      = Nat.card (Σ r : ↥(Set.range red),
          {s : {f : MLifts D ρ // f.Central} // (⟨red s, s, rfl⟩ : ↥(Set.range red)) = r}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv
          (fun s : {f : MLifts D ρ // f.Central} => (⟨red s, s, rfl⟩ : ↥(Set.range red))))).symm
    _ = ∑ r : ↥(Set.range red), Nat.card {s : {f : MLifts D ρ // f.Central} //
          (⟨red s, s, rfl⟩ : ↥(Set.range red)) = r} := Nat.card_sigma
    _ = ∑ _r : ↥(Set.range red), Nat.card (TCocycle D ρ) :=
        Finset.sum_congr rfl (fun r _ => hfibre r)
    _ = Nat.card ↥(Set.range red) * Nat.card (TCocycle D ρ) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]

open AffineTLift CentralObstruction in
/-- **The per-`ρ` μ-partition, in bridge vocabulary** (P-16d6): transporting
`central_card_eq_reductions_mul_tcocycle` through `centralOver_equiv`, the `zBC`-fibre
`#CentralOver(ρ)` (the summand of `zBC_eq_sum_centralOver`) factors as
`(#achievable central `T`-reductions of `ρ' = rhoPrime …`) · #Z¹(T)`.  This is the per-fibre form
of the (140) `hfib` datum: once `#Z¹(T) = μ` is shown `ρ`-independent, summing over `ρ` gives
`zBC = μ · M` with `M = Σ_ρ #achievable central `T`-reductions` (the `lemma_8_5` count). -/
theorem centralOver_card_eq_reductions_mul_tcocycle {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (hC : D.C = RF.scalarCover l h) (ρ : BoundaryLifts b F RF.TC) (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) :
    Nat.card (RF.CentralOver b F l h ρ)
      = Nat.card ↥(Set.range (fun f : {f : MLifts D (RF.rhoPrime b F D hD ρ) // f.Central} =>
          redT (RF.rhoPrime b F D hD ρ) f.1))
        * Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ)) := by
  rw [Nat.card_congr (RF.centralOver_equiv b F l h D hD hC ρ)]
  exact central_card_eq_reductions_mul_tcocycle (RF.rhoPrime b F D hD ρ) Dsc htriv hfg

open AffineTLift CentralObstruction in
/-- **The (140) `hfib` datum, reduced to μ-independence** (P-16d6).  Summing the per-`ρ`
μ-partition (`centralOver_card_eq_reductions_mul_tcocycle`) over the `C`-image via
`zBC_eq_sum_centralOver` and factoring out the common `μ` (hypothesis `hμ`: the `T`-cocycle
count `#Z¹(T)` is `ρ`-independent — the source 5.15/5.16 fact) gives the (140) fibration
`zBC = μ · M`, with `M = Σ_ρ #achievable central `T`-reductions`.  This is exactly the `hfib`
argument of `phase140_ofPhaseData`: the (140) fibration is now reduced to the single source
input `hμ` (and `M` is the `lemma_8_5` constrained count fed to `hgauss`). -/
theorem zBC_eq_mu_mul_reductionCount {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (hC : D.C = RF.scalarCover l h) (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) (μ : ℕ)
    (hμ : ∀ ρ : BoundaryLifts b F RF.TC, Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ)) = μ) :
    RF.zBC b F l h = μ * ∑ᶠ ρ : BoundaryLifts b F RF.TC,
      Nat.card ↥(Set.range (fun f : {f : MLifts D (RF.rhoPrime b F D hD ρ) // f.Central} =>
        redT (RF.rhoPrime b F D hD ρ) f.1)) := by
  classical
  haveI : Finite (BoundaryLifts b F RF.TC) := finite_boundaryLifts b F RF.TC hfg
  haveI : Fintype (BoundaryLifts b F RF.TC) := Fintype.ofFinite _
  rw [zBC_eq_sum_centralOver RF b F hfg l h, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => by
    rw [centralOver_card_eq_reductions_mul_tcocycle RF b F l h D hD hC ρ Dsc htriv hfg, hμ ρ]
    exact mul_comm _ _

/-! ## `hgauss` level 1 — aggregating the Gauss engine `lemma_8_5` over the ρ-family -/

open QuadraticFp2 in
/-- **The aggregated constrained-Gauss identity** (P-16d6, `hgauss` level 1): summing the proved
Gauss engine `lemma_8_5` over a finite index family `I` (the `C`-image `ρ`, each with its own
constraint `(κ_i, ε_i)`) and swapping the resulting double sum gives

  `2·|E^∨|·Σ_i N(κ_i,ε_i) = |I|·|W| + G(Q)·Σ_χ Σ_i (−1)^{χκ_i+ε_i+Q(a_χ)}`.

Pure `𝔽₂`-linear algebra — no frame data.  This is the aggregation step of `hgauss`: with the
concrete correspondences `Σ_i N(κ_i,ε_i) = M`, `|I| = e_Γ(C)`, `|W| = |V|`, `|E^∨| = |D_T|`,
`G(Q) = G0`, and the phase reindex `Σ_i sign(χκ_i+ε_i+Q(a_χ)) = 2·nPhase(phase χ) − e_Γ(C)`
(the Prop 8.8 / (135) content coupled to the witness), it becomes the `hgauss` hypothesis of
`phase140_ofPhaseData`. -/
theorem lemma_8_5_aggregated {W E : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (L : W →ₗ[ZMod 2] E) (hL : Function.Surjective L) (Q : W → ZMod 2)
    (a : Module.Dual (ZMod 2) E → W)
    (ha : ∀ (χ : Module.Dual (ZMod 2) E) (x : W), polar Q (a χ) x = χ (L x))
    {I : Type*} [Fintype I] (κ : I → E) (ε : I → ZMod 2) :
    2 * (Nat.card (Module.Dual (ZMod 2) E) : ℤ)
        * ∑ i : I, (Nat.card {x : W // L x = κ i ∧ Q x = ε i} : ℤ)
      = (Fintype.card I : ℤ) * (Nat.card W : ℤ)
        + gaussSum Q * ∑ᶠ χ : Module.Dual (ZMod 2) E,
            ∑ i : I, sign (χ (κ i) + ε i + Q (a χ)) := by
  classical
  haveI : Fintype (Module.Dual (ZMod 2) E) := Fintype.ofFinite _
  have hswap : (∑ i : I, ∑ᶠ χ : Module.Dual (ZMod 2) E, sign (χ (κ i) + ε i + Q (a χ)))
      = ∑ᶠ χ : Module.Dual (ZMod 2) E, ∑ i : I, sign (χ (κ i) + ε i + Q (a χ)) := by
    rw [finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        finsum_eq_sum_of_fintype (fun χ : Module.Dual (ZMod 2) E => sign (χ (κ i) + ε i + Q (a χ)))]
    exact Finset.sum_comm
  calc 2 * (Nat.card (Module.Dual (ZMod 2) E) : ℤ)
          * ∑ i : I, (Nat.card {x : W // L x = κ i ∧ Q x = ε i} : ℤ)
      = ∑ i : I, 2 * (Nat.card (Module.Dual (ZMod 2) E) : ℤ)
          * (Nat.card {x : W // L x = κ i ∧ Q x = ε i} : ℤ) := by rw [Finset.mul_sum]
    _ = ∑ i : I, ((Nat.card W : ℤ)
          + gaussSum Q * ∑ᶠ χ : Module.Dual (ZMod 2) E, sign (χ (κ i) + ε i + Q (a χ))) :=
        Finset.sum_congr rfl fun i _ => lemma_8_5 L hL Q a ha (κ i) (ε i)
    _ = (∑ _i : I, (Nat.card W : ℤ))
          + gaussSum Q * ∑ i : I, ∑ᶠ χ : Module.Dual (ZMod 2) E, sign (χ (κ i) + ε i + Q (a χ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (Fintype.card I : ℤ) * (Nat.card W : ℤ)
          + gaussSum Q * ∑ᶠ χ : Module.Dual (ZMod 2) E, ∑ i : I, sign (χ (κ i) + ε i + Q (a χ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hswap]

/-! ## The capstone (140) reducer — `phase140` from the concrete correspondences -/

open QuadraticFp2 AffineTLift CentralObstruction in
/-- **The (140) display, reduced to the concrete correspondences** (P-16d6): the `phase140`
field of `RecursionInputs`, derived from the abstract engine + the concrete data.  This is the
(140) analog of `stageR136_ofRObstructionData` — it assembles `zBC_eq_mu_mul_reductionCount`
(the `hfib` half, needing μ-independence `hμ`) and `lemma_8_5_aggregated` (the Gauss half) into
the boxed (140) identity, isolating exactly the two hard **Prop 8.8** correspondences as
hypotheses:

* `hM` — the (135)/Prop 8.8 identity `#achievable-central-T-reductions(ρ) = N(κ_ρ, ε_ρ)`
  (central-liftable ⟺ `Q x = ε_ρ ∧ L x = κ_ρ`), per lower map `ρ`;
* `hphase` — the phase reindex `Σ_χ Σ_ρ (−1)^{χκ_ρ+ε_ρ+Q(a_χ)} = Σ_ζ (2·nPhase(phase ζ) − e_Γ(C))`
  (matching `V^∨`-characters to the `D_T`-indexed phase covers).

The remaining `hμ`/`hM`/`hphase` and the cardinality matches `hDT`/`hWV`/`hG0` are the concrete
`(140)` O-half; everything else (the fibration, the Gauss aggregation, the algebra) is now proven. -/
theorem phase140_of_gaussCorrespondence {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT] (phase : DT → CentralCover RF.YC)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) (hC : D.C = RF.scalarCover l h)
    (Dsc : Descent D) (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    [Fintype (BoundaryLifts b F RF.TC)]
    {W Efp : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup Efp] [Module (ZMod 2) Efp] [Finite Efp]
    (Lin : W →ₗ[ZMod 2] Efp) (hLin : Function.Surjective Lin) (Q : W → ZMod 2)
    (aa : Module.Dual (ZMod 2) Efp → W)
    (haa : ∀ (χ : Module.Dual (ZMod 2) Efp) (x : W), polar Q (aa χ) x = χ (Lin x))
    (κ : BoundaryLifts b F RF.TC → Efp) (ε : BoundaryLifts b F RF.TC → ZMod 2)
    (hμ : ∀ ρ : BoundaryLifts b F RF.TC, Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ)) = μ)
    (hM : ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card ↥(Set.range (fun f : {f : MLifts D (RF.rhoPrime b F D hD ρ) // f.Central} =>
        redT (RF.rhoPrime b F D hD ρ) f.1)) = Nat.card {x : W // Lin x = κ ρ ∧ Q x = ε ρ})
    (hDT : Nat.card (Module.Dual (ZMod 2) Efp) = Nat.card DT)
    (hWV : Nat.card W = Nat.card ↥RF.MB / Nat.card ↥RF.TBsub)
    (hG0 : gaussSum Q = G0)
    (hphase : (∑ᶠ χ : Module.Dual (ZMod 2) Efp, ∑ ρ : BoundaryLifts b F RF.TC,
                sign (χ (κ ρ) + ε ρ + Q (aa χ)))
              = ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ)
                  - (exactImageCount b F RF.TC : ℤ))) :
    2 * (Nat.card DT : ℤ) * RF.zBC b F l h
      = μ * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
          + G0 * ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ)
              - (exactImageCount b F RF.TC : ℤ))) := by
  classical
  set Mcount : ℕ := ∑ ρ : BoundaryLifts b F RF.TC,
    Nat.card {x : W // Lin x = κ ρ ∧ Q x = ε ρ} with hMc
  have hexact : (exactImageCount b F RF.TC : ℤ)
      = (Fintype.card (BoundaryLifts b F RF.TC) : ℤ) := by
    rw [show exactImageCount b F RF.TC = Nat.card (BoundaryLifts b F RF.TC) from rfl,
      Nat.card_eq_fintype_card]
  -- `hfib`: the fibration, via μ-independence and the Prop-8.8 count `hM`
  have hfib : RF.zBC b F l h = μ * Mcount := by
    rw [zBC_eq_mu_mul_reductionCount RF b F l h D hD hC Dsc htriv hfg μ hμ]
    congr 1
    rw [finsum_eq_sum_of_fintype, hMc]
    exact Finset.sum_congr rfl fun ρ _ => hM ρ
  -- `hgauss`: the aggregated Gauss identity, with the cardinality matches and the phase reindex
  have hgauss : 2 * (Nat.card DT : ℤ) * (Mcount : ℤ)
      = (Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
        + G0 * ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ)
            - (exactImageCount b F RF.TC : ℤ)) := by
    rw [hMc, Nat.cast_sum, ← hDT, ← hG0, ← hphase,
      lemma_8_5_aggregated Lin hLin Q aa haa κ ε]
    congr 1
    rw [hWV, ← hexact]
    push_cast
    ring
  exact phase140_ofPhaseData RF b F μ G0 DT phase l h Mcount hfib hgauss

/-! ## Discharging the polar data `a_χ` from nonsingularity (the `En.hns` supply) -/

open QuadraticFp2 AffineTLift in
/-- **The canonical polar shift `a_χ`** (P-16d6): for a nonsingular quadratic `Q` on a finite
`𝔽₂`-space `W` and a linear `L : W → E`, the unique `a` with `B_Q(a, ·) = χ ∘ L`
(`exists_polar_inverse`).  This is `lemma_8_5`'s `a`-datum, supplied by the enrichment's
`qbar`/`hns`/`hquad` — so the (140) reducer need not take `a`/`ha` as bare hypotheses. -/
noncomputable def polarInverseL {W Efp : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup Efp] [Module (ZMod 2) Efp]
    (Q : W → ZMod 2) (hquad : IsQuadraticFp2 Q) (hns : Nonsingular Q)
    (L : W →ₗ[ZMod 2] Efp) (χ : Module.Dual (ZMod 2) Efp) : W :=
  Classical.choose (exists_polar_inverse Q hquad hns (χ.comp L))

open QuadraticFp2 AffineTLift in
/-- The defining spec of `polarInverseL`: `B_Q(a_χ, v) = χ(L v)` (the `ha` clause of `lemma_8_5`
and `phase140_of_gaussCorrespondence`). -/
theorem polarInverseL_spec {W Efp : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup Efp] [Module (ZMod 2) Efp]
    (Q : W → ZMod 2) (hquad : IsQuadraticFp2 Q) (hns : Nonsingular Q)
    (L : W →ₗ[ZMod 2] Efp) (χ : Module.Dual (ZMod 2) Efp) (v : W) :
    polar Q (polarInverseL Q hquad hns L χ) v = χ (L v) := by
  exact Classical.choose_spec (exists_polar_inverse Q hquad hns (χ.comp L)) v

open QuadraticFp2 AffineTLift CentralObstruction in
/-- **The (140) reducer from nonsingularity** (P-16d6): `phase140_of_gaussCorrespondence` with the
polar data `a`/`ha` discharged from `En.hns`/`En.hquad` via `polarInverseL`.  So the (140) engine
inputs are exactly what the enrichment supplies (`Q = qbar`, nonsingular + quadratic), and the
residual concrete facts are just `hM` (Prop 8.8 count), `hphase` (character↔phase reindex, now
phrased with the canonical `a_χ = polarInverseL …`), `hμ` (μ-independence), and the matches. -/
theorem phase140_of_nonsingular {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT] (phase : DT → CentralCover RF.YC)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) (hC : D.C = RF.scalarCover l h)
    (Dsc : Descent D) (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    [Fintype (BoundaryLifts b F RF.TC)]
    {W Efp : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup Efp] [Module (ZMod 2) Efp] [Finite Efp]
    (Lin : W →ₗ[ZMod 2] Efp) (hLin : Function.Surjective Lin) (Q : W → ZMod 2)
    (hquad : IsQuadraticFp2 Q) (hns : Nonsingular Q)
    (κ : BoundaryLifts b F RF.TC → Efp) (ε : BoundaryLifts b F RF.TC → ZMod 2)
    (hμ : ∀ ρ : BoundaryLifts b F RF.TC, Nat.card (TCocycle D (RF.rhoPrime b F D hD ρ)) = μ)
    (hM : ∀ ρ : BoundaryLifts b F RF.TC,
      Nat.card ↥(Set.range (fun f : {f : MLifts D (RF.rhoPrime b F D hD ρ) // f.Central} =>
        redT (RF.rhoPrime b F D hD ρ) f.1)) = Nat.card {x : W // Lin x = κ ρ ∧ Q x = ε ρ})
    (hDT : Nat.card (Module.Dual (ZMod 2) Efp) = Nat.card DT)
    (hWV : Nat.card W = Nat.card ↥RF.MB / Nat.card ↥RF.TBsub)
    (hG0 : gaussSum Q = G0)
    (hphase : (∑ᶠ χ : Module.Dual (ZMod 2) Efp, ∑ ρ : BoundaryLifts b F RF.TC,
                sign (χ (κ ρ) + ε ρ + Q (polarInverseL Q hquad hns Lin χ)))
              = ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ)
                  - (exactImageCount b F RF.TC : ℤ))) :
    2 * (Nat.card DT : ℤ) * RF.zBC b F l h
      = μ * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
          + G0 * ∑ᶠ ζ : DT, (2 * (RF.nPhase b F (phase ζ) : ℤ)
              - (exactImageCount b F RF.TC : ℤ))) :=
  phase140_of_gaussCorrespondence RF b F μ G0 DT phase l h D hD hC Dsc htriv hfg
    Lin hLin Q (polarInverseL Q hquad hns Lin)
    (fun χ v => polarInverseL_spec Q hquad hns Lin χ v) κ ε hμ hM hDT hWV hG0 hphase

end SectionEight

end GQ2
