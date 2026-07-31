/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Bridge
import GQ2.RecursionSplice

/-!
# The recursion splice at the `K`-boundary (dyadic campaign, ticket SD-R3)

Clone of the **generic `b`-typed layer** of `GQ2/RecursionSplice.lean` (363 ln), re-typed at the
general `K`-boundary, with the (139) multiplicity parameterized (memo §4.1(b)).

## Finding: 4 of the model's 10 declarations are spine (~120 of 363 ln)

The split is three-way, and only the middle third is SD-R work:

* **`AbsGalQ2`-typed (NOT spine)** — `prop_8_9_of_inputs` (`:48`) and `prop_8_9_of` (`:79`) take
  `B : BoundaryMaps` and the `AbsGalQ2` instance package: they are the *one-sided* `ℚ₂` splice.
  Under the memo's two-sided restatement (§3.1) these do not get cloned at all — their role is
  taken by SD3's two-sided assembly over `closedRecursionK_of_source` (`Prop89Close.lean`).
  The budget grep (SD-R2's rule) flags them: 6 `AbsGalQ2` mentions, all in these two.
* **`b`-typed (cloned below, 4 decls)** — `half139_via_radData`, `zBC_eq_sum_centralOver`,
  `centralOver_card_eq_reductions_mul_tcocycle`, `zBC_eq_mu_mul_reductionCount`.
* **boundary-free (consumed by import, 4 decls)** — `central_card_eq_reductions_mul_tcocycle`
  (`:175`, the per-`ρ` μ-partition — the actual mathematics), `lemma_8_5_aggregated` (`:291`, the
  Gauss aggregation), `enrichment_card_Vmod` (`:334`).

So the `hfib`/μ-partition core and the Gauss aggregation are both below the boundary and are
reused untouched; what clones is the fibration bookkeeping that indexes them by boundary lifts.

## Parameterization delta versus the `ℚ₂` model

`half139_via_radDataK` carries the (139) multiplicity as an opaque `(mM : ℕ)` in place of the
model's literal `(Nat.card ↥RF.MB) ^ 2` (memo §4.1(b)), matching `half139_ofK`'s parameter and
hence `RecursionInputsK.half139`.  Everything else is types only, and every proof is verbatim.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-! ## The (139) reduction to `MLifts`-level source facts -/

/-- **`half139` reduced to the source's `MLifts`-level count** at the `K`-boundary, at an opaque
multiplicity `mM`.  Clone of `GQ2.SectionEight.half139_via_radData`
(`GQ2/RecursionSplice.lean:115`); the model's literal `(Nat.card ↥RF.MB) ^ 2` becomes `mM`
(memo §4.1(b) — `SN.mMult (Nat.card ↥RF.MB)` at instantiation).

Strips the bridge plumbing off the (139) obligation: a caller supplies only the two pure `MLifts`
source facts for the transported lower map `ρ'` (Lemma 8.6's half-torsor identity, and the
`M`-lift count of props 5.15/5.16). -/
theorem half139_via_radDataK {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (mM : ℕ)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hlem86M : ∀ ρ : BoundaryLiftsK b F RF.TC,
      2 * Nat.card {f : MLifts (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) //
          f.Central}
        = Nat.card (MLifts (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)))
    (hMcountM : ∀ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card (MLifts (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)) = mM) :
    2 * zBCK RF b F l h = mM * exactImageCountK b F RF.TC := by
  refine half139_ofK RF b F hfg l h mM (fun ρ => ?_) (fun ρ => ?_)
  · rw [Nat.card_congr (centralOverK_equiv RF b F l h (En.radData l h) rfl rfl ρ),
      Nat.card_congr (liftsOverK_equiv RF b F (En.radData l h) rfl ρ)]
    exact hlem86M ρ
  · rw [Nat.card_congr (liftsOverK_equiv RF b F (En.radData l h) rfl ρ)]
    exact hMcountM ρ

/-! ## The `zBC` fibration -/

/-- **The `zBC` fibration** over the lower exact-image map `ρ` at the `K`-boundary.  Clone of
`GQ2.SectionEight.zBC_eq_sum_centralOver` (`GQ2/RecursionSplice.lean:140`) — verbatim. -/
theorem zBC_eq_sum_centralOverK {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR) :
    zBCK RF b F l h = ∑ᶠ ρ : BoundaryLiftsK b F RF.TC, Nat.card (CentralOverK RF b F l h ρ) := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLiftsK b F RF.TC) := finite_boundaryLiftsK b F RF.TC hfg
  haveI : Fintype (BoundaryLiftsK b F RF.TC) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, zBCK]
  haveI : Finite {pr : BoundaryLiftsK b F RF.TC × ContinuousMonoidHom Γ RF.YB //
      (∀ γ : Γ, RF.piBC (pr.2 γ) = pr.1.1.1 γ) ∧ IsBoundaryLiftK b F RF.TB pr.2 ∧
        ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
          ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = pr.2 γ} := Subtype.finite
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv (fun x => x.1.1)).symm, Nat.card_sigma]
  exact Finset.sum_congr rfl fun ρ _ => Nat.card_congr (zBCfibreEquivK RF b F l h ρ)

/-! ## The per-`ρ` μ-partition and the (140) `hfib` datum -/

open AffineTLift CentralObstruction in
/-- **The per-`ρ` μ-partition** at the `K`-boundary.  Clone of
`GQ2.SectionEight.centralOver_card_eq_reductions_mul_tcocycle`
(`GQ2/RecursionSplice.lean:229`) — verbatim; the mathematics
(`central_card_eq_reductions_mul_tcocycle`) is boundary-free and is the model's, by import. -/
theorem centralOverK_card_eq_reductions_mul_tcocycle {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (hC : D.C = RF.scalarCover l h) (ρ : BoundaryLiftsK b F RF.TC) (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) :
    Nat.card (CentralOverK RF b F l h ρ)
      = Nat.card ↥(Set.range (fun f : {f : MLifts D (rhoPrimeK RF b F D hD ρ) // f.Central} =>
          redT (rhoPrimeK RF b F D hD ρ) f.1))
        * Nat.card (TCocycle D (rhoPrimeK RF b F D hD ρ)) := by
  rw [Nat.card_congr (centralOverK_equiv RF b F l h D hD hC ρ)]
  exact central_card_eq_reductions_mul_tcocycle (rhoPrimeK RF b F D hD ρ) Dsc htriv hfg

open AffineTLift CentralObstruction in
/-- **The (140) `hfib` datum, reduced to μ-independence** at the `K`-boundary.  Clone of
`GQ2.SectionEight.zBC_eq_mu_mul_reductionCount` (`GQ2/RecursionSplice.lean:254`) — verbatim.

This is the `T`-torsor factoring consumed by `phase140_of_phaseObstructionK`. -/
theorem zBCK_eq_mu_mul_reductionCount {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB)
    (hC : D.C = RF.scalarCover l h) (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) (μ : ℕ)
    (hμ : ∀ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card (TCocycle D (rhoPrimeK RF b F D hD ρ)) = μ) :
    zBCK RF b F l h = μ * ∑ᶠ ρ : BoundaryLiftsK b F RF.TC,
      Nat.card ↥(Set.range (fun f : {f : MLifts D (rhoPrimeK RF b F D hD ρ) // f.Central} =>
        redT (rhoPrimeK RF b F D hD ρ) f.1)) := by
  classical
  haveI : Finite (BoundaryLiftsK b F RF.TC) := finite_boundaryLiftsK b F RF.TC hfg
  haveI : Fintype (BoundaryLiftsK b F RF.TC) := Fintype.ofFinite _
  rw [zBC_eq_sum_centralOverK RF b F hfg l h, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => by
    rw [centralOverK_card_eq_reductions_mul_tcocycle RF b F l h D hD hC ρ Dsc htriv hfg, hμ ρ]
    exact mul_comm _ _

end GQ2.Dyadic
