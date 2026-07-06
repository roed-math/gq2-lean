import GQ2.RecursionSplice

/-!
# P-16d6d: the (139) half count for the local source `G_ℚ₂`

Discharge the two per-source hypotheses of `half139_via_radData` (`RecursionSplice.lean`) for the
**local** source `Γ = G_ℚ₂ = AbsGalQ2`, producing the (139) identity
`2·zBC = |M_B|²·exactImageCount` in exactly the shape of the `RecursionInputs.half139` field
(consumed at P-16d6e).

Two obligations, per boundary lift `ρ` of the `C`-target:

* **`hlem86M`** — the source's Lemma 8.6 half-torsor count
  `2·#{central M-lifts} = #(M-lifts)`.  This is `lemma_8_6_local` (✓, B6/B7) applied to the
  transported lower map `ρ' = rhoPrime … ρ`, with `hedge` threaded from the `NoDescent` field
  hypothesis and `hρ'` from `rhoPrime_surjective` (below).  ~Pure plumbing.
* **`hMcountM`** — the unrestricted `M`-lift count `#(M-lifts) = |M_B|²`.  The genuine content:
  `MLifts` is a `Z¹_cont(G_ℚ₂, M_B)`-torsor and `#Z¹ = |M_B|²·#H²(G_ℚ₂, M_B)`
  (`card_Z1_eq`), so the identity reduces to `#H²(G_ℚ₂, M_B) = 1`, i.e. the vanishing of the
  `YC`-coinvariants of `M_B`.

Axioms (audit at close): `⊆ {B6, B7, B9}` — B6/B7 via `lemma_8_6_local` and the local Euler
characteristic behind `card_Z1_eq`.
-/

namespace GQ2

namespace SectionEight

open CentralObstruction AffineTLift

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-! ## `rhoPrime` surjectivity (both sources) -/

/-- **The transported lower map `ρ' = piBCiso⁻¹ ∘ ρ` is surjective.**  A boundary lift `ρ` wraps a
`ContSurj` (`ρ.1.2 : Surjective ρ.1.1`), and `piBCiso.symm` is a `MulEquiv`, so the composite is
onto `B/M`.  Feeds `lemma_8_6_local`'s surjectivity hypothesis. -/
theorem rhoPrime_surjective {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) (ρ : BoundaryLifts b F RF.TC) :
    Function.Surjective (RF.rhoPrime b F D hD ρ) := fun y => by
  obtain ⟨γ, hγ⟩ := ρ.1.2 (RF.piBCiso D hD y)
  exact ⟨γ, by rw [RF.rhoPrime_apply, hγ, MulEquiv.symm_apply_apply]⟩

/-! ## The two hypotheses for `G_ℚ₂` -/

/-- **`hlem86M` for `G_ℚ₂`** — the source's Lemma 8.6 half-torsor count over every boundary lift,
for the radical datum `En.radData l h`, threading the `NoDescent` field hypothesis. -/
theorem hlem86M_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    [IsTopologicalGroup AbsGalQ2]
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup)
    (F : BoundaryFrame H E) (En : RF.Enrichment)
    (hfg : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hedge : ¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N)
    (ρ : BoundaryLifts b F RF.TC) :
    2 * Nat.card {f : MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ) // f.Central}
      = Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ)) :=
  lemma_8_6_local (En.radData l h) hfg hedge (RF.rhoPrime b F (En.radData l h) rfl ρ)
    (rhoPrime_surjective RF b F (En.radData l h) rfl ρ)

/-- **`hMcountM` for `G_ℚ₂`** — the unrestricted `M`-lift count `#(M-lifts) = |M_B|²`.

**⚠ Not yet proved — the genuine `Z¹`-torsor + duality content of P-16d6d.**  This same fact
(`κ_M = #MLifts`, ρ-independent) is the shared deep input consumed by the concurrent P-16d6b
(`PhaseMuIndep.tcocycle_mu_indep`'s `hML`/`κM`).  Full roadmap in
`docs/p16d6d-hMcount-handoff.md`; the route (all steps over `G_ℚ₂ = AbsGalQ2`):

1. **Additive `M`-module** `MBmod := Additive ↥(En.radData l h).M` (`= Additive ↥RF.MB`), with the
   `ρ'`-conjugation `DistribMulAction AbsGalQ2 MBmod` and the descended `DistribMulAction RF.YC
   MBmod` (factoring through `ρ'`, `hcomp`), continuity, `2`-torsion (`RF.MB_elem`).  **Pattern:
   copy `RadicalEdgeLocal.lean:73–135`** (the `D.T` version) with `D.T ⤳ D.M`, using `D.hM`
   (normality ⟹ conjugation stays in `M`) and `D.hcomm` (`M` abelian ⟹ the action factors through
   `Bg/M`), which are the exact `D.T`-analogues already invoked there.
2. **Torsor bridge** `MLifts D ρ' ≃ Z¹_cont(AbsGalQ2, MBmod)` — `f ↦ (γ ↦ f γ · f₀ γ⁻¹)` for a base
   lift `f₀`.  **Nonemptiness of `MLifts` is a theorem, not a hypothesis**: the lift obstruction of
   `ρ' : Γ → YB/M_B` through `YB ↠ YB/M_B` lives in `H²(AbsGalQ2, M_B)`, which is `0` by step 4 —
   so `MLifts` is nonempty and the torsor bijection holds.  (No existing `H²`-obstruction-vanishing
   lemma in-repo; this is the piece to build/locate.)
3. **`card_Z1_eq`** (`LocalLiftingDuality.lean:264`, B7 Euler char):
   `#Z¹(AbsGalQ2, MBmod) = |MBmod|² · #fixedPts RF.YC (ElemDual MBmod)`, feeding `hρ = rhoPrime`
   surjectivity (`rhoPrime_surjective`), `hcomp` from step 1, `hA₂` from `RF.MB_elem`.
4. **`#fixedPts RF.YC (ElemDual MBmod) = 1`** — i.e. `H²(AbsGalQ2, M_B) = 0`
   (`card_H2_eq_fixedPts`, B6), i.e. the `YC`-coinvariants `(M_B)_{YC} = 0`.  **This is the key
   structural fact, from minimality of `K`** (`Blk.minimal`): a nonzero trivial `YC`-quotient
   `M_B ↠ 𝔽₂` cannot kill `T_B` (as `V = M_B/T_B = P/S` is a nontrivial chief factor with no trivial
   quotient — `Blk.chief`/`Blk.nontrivial_action`), so its index-`2` kernel `M'` has `M' + T_B =
   M_B`; the `Y`-normal preimage `K'` (`Blk.R ≤ K' < Blk.K`) then satisfies `K' ⊔ Blk.S = Blk.P`,
   contradicting `Blk.minimal`.  Hence no trivial quotient, `(M_B)_{YC} = 0`, `#fixedPts = 1`.
5. Combine: `#MLifts = #Z¹ = |M_B|² · 1 = |M_B|²`.

Expected axioms at close: `std-3 + B6 + B7` (B6 via `card_H2_eq_fixedPts`, B7 via `card_Z1_eq`). -/
theorem hMcountM_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    [IsTopologicalGroup AbsGalQ2]
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup)
    (F : BoundaryFrame H E) (En : RF.Enrichment)
    (hfg : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (MLifts (En.radData l h) (RF.rhoPrime b F (En.radData l h) rfl ρ))
      = (Nat.card ↥RF.MB) ^ 2 := by
  sorry

/-- **P-16d6d deliverable**: the (139) half count for `G_ℚ₂`, in the exact shape of the
`RecursionInputs.half139` field (consumed at P-16d6e). -/
theorem half139_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    [IsTopologicalGroup AbsGalQ2]
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup)
    (F : BoundaryFrame H E) (En : RF.Enrichment)
    (hfg : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hedge : ¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) :
    2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC :=
  half139_via_radData RF b F En l h hfg
    (hlem86M_local RF b F En hfg l h hedge) (hMcountM_local RF b F En hfg l h)

end SectionEight

end GQ2
