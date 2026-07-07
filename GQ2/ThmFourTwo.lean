import GQ2.SectionNine
import GQ2.BlockEnrichment
import GQ2.Prop89Close

/-!
# Theorem 4.2 — the §9 sink  (P-17i)

`thm_4_2` (the boundary-framed exact-image theorem) and its stratum clause, **relocated from
`GQ2/SectionNine.lean`** (second hop of the established relocation pattern; first hop was
`BoundaryFrame → SectionNine`, P-17a).  The move is forced by the import DAG: the `R`-stage
lane consumes `prop_8_9` (`GQ2/Prop89Close.lean`, incomparable with `SectionNine`) **and**
`SectionNine.blockEnrichment` (`GQ2/BlockEnrichment.lean`, strictly *downstream* of
`SectionNine` because it consumes `kappa0_exists`) — so the proof cannot live inside
`SectionNine.lean`.  A comment-pointer remains there; the fully qualified name `GQ2.thm_4_2`
is unchanged, so call sites only gain an import.

The proof: strong induction on `|L_Y|` with three lanes — terminal (`terminal_count_eq`,
P-17b), `M`-stage (`R = ⊥`: `mStage_partition` ×2 at multiplicity `|M_B|²`, P-17f +
`MStageCount`/`MStageCountGammaA`), and `R`-stage (`R ≠ ⊥`: `blockEnrichment` + `prop_8_9`
solved by `count_eq_of_closedRecursion` against the P-17g bounds).
-/

namespace GQ2

open SectionEight

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- **Theorem 4.2 (boundary-framed exact-image theorem).**  For every boundary frame and
every boundary-framed marked target `𝒴`, the exact-image lift counts from the two sources
agree: `e^β_{Γ_A}(𝒴) = e^β_{G_ℚ₂}(𝒴)`.

Stated for any `BoundaryMaps` witness of the Prop 3.14 data (the choice is fixed "once and
for all" in §4 and only its bundled properties are used).

**Amended (P-17a, 2026-07-06, documented)** with `(hE2 : ∀ e : E, e ^ 2 = 1)`: the §9
induction descends the θ-decoration through the block via `lemma_7_3`, whose (paper-stated)
hypothesis is that the decoration target is elementary abelian 2; the terminal case kills
the odd complement through `θ` for the same reason.  §10 consumes the theorem at `E = 0`
only, so the amendment is downstream-harmless.  Relocated `BoundaryFrame → SectionNine`
(P-17a: the proof needs §§5–9 machinery) `→ ThmFourTwo` (P-17i: the `R`-stage lane needs
`blockEnrichment` + `prop_8_9`, both off-limits inside `SectionNine` — see the module
docstring).

**Instance binders (P-17i, documented)**: the two `AbsGalQ2` topology hypotheses mirror
`terminal_count_eq`'s (the `Half139Local`/`BoundaryMapsWitness` tower discipline — they are
deliberately not global instances); the sole consumer `eq_154` (P-18e) already carries exactly
these two.  The remaining topology instances the inductive lanes need (`GammaA`'s
compact/t.d./topological-group triple, `IsTopologicalGroup AbsGalQ2`) are globally inferable
(`GammaA : ProfiniteGrp`; mathlib's Krull-topology instance), so they are *not* binders.

*Status*: P-17i — induction scaffold, terminal lane, and the full `M`-stage lane are proved;
the `R`-stage lane is the remaining sorry (assembled against `prop_8_9`, which is itself
mid-close at P-16d6e; axioms B1/B3c/B6/B7/B7′/B8/B9 enter through the ingredients, per
App. D). -/
theorem thm_4_2 (B : BoundaryMaps) (F : BoundaryFrame H E)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    exactImageCount B.bA F T = exactImageCount B.bF F T := by
  -- Strong induction on the marked-kernel size `n = |L_Y|` (§9, pp. 44–47), generalizing the
  -- whole target `(Y, 𝒴)`: the IH must quantify over *all* strictly smaller marked targets
  -- (the recursion passes to quotients, strata and pulled-back covers of `Y`), not just
  -- sub-targets of the fixed `T`.  `B`, `F`, `hE2` and the section data stay fixed.
  suffices h : ∀ (n : ℕ) (Y : Type) [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
      [Finite Y] (T : MarkedTarget H E Y), Nat.card ↥T.LY = n →
      exactImageCount B.bA F T = exactImageCount B.bF F T by
    exact h (Nat.card ↥T.LY) Y T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Y instGY instTY instDY instFY T hcard
    by_cases hstack : SectionSeven.IsScalarStack T.LY
    · -- **Terminal lane** (`IsScalarStack T.LY`, §9.1–9.2): the two exact-image problems are
      -- identified through the common marked pro-2 quotient — `terminal_count_eq` (P-17b).
      exact SectionNine.terminal_count_eq B F T hE2 hstack
    · -- Inductive case: a nonscalar chief factor exists; choose the §7 minimal block.
      obtain ⟨Blk⟩ := SectionSeven.exists_minimalBlock T.normal T.isPGroup_two hstack
      by_cases hR : Blk.R = ⊥
      · -- **`M`-stage lane** (`Blk.R = ⊥`, §9.2): the two `mStage_partition` (P-17f)
        -- identities at the block frame, multiplicity `|M_B|²` per source, solved against
        -- the IH.
        classical
        by_cases hhead : Function.Surjective (fun x : ↥boundarySubgroup => (F.frameMap x).1)
        · -- head covered: run the partition at both sources
          have hfgA : ∃ s : Finset GammaA,
              (Subgroup.closure (s : Set GammaA)).topologicalClosure = ⊤ :=
            gammaA_topologicallyFinitelyGenerated
          have hfgF : ∃ s : Finset AbsGalQ2,
              (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤ :=
            Foundations.absGalQ2_isTopologicallyFinitelyGenerated
          have hheadA : Function.Surjective (fun γ : GammaA => (F.frameMap (B.bA γ)).1) :=
            hhead.comp B.bA_surjective
          have hheadF : Function.Surjective (fun γ : AbsGalQ2 => (F.frameMap (B.bF γ)).1) :=
            hhead.comp B.bF_surjective
          -- the multiplicity `|M_B|²`, per source (`MStageCount` / `MStageCountGammaA`)
          have hmultF : ∀ ρ : BoundaryLifts B.bF F (blockFrameImpl T Blk hE2).TC,
              Nat.card ((blockFrameImpl T Blk hE2).LiftsOver B.bF F ρ)
                = (Nat.card ↥(blockFrameImpl T Blk hE2).MB) ^ 2 :=
            (blockFrameImpl T Blk hE2).liftsOver_card_local B.bF F
          have hmultA : ∀ ρ : BoundaryLifts B.bA F (blockFrameImpl T Blk hE2).TC,
              Nat.card ((blockFrameImpl T Blk hE2).LiftsOver B.bA F ρ)
                = (Nat.card ↥(blockFrameImpl T Blk hE2).MB) ^ 2 :=
            (blockFrameImpl T Blk hE2).liftsOver_card_gammaA B.bA F
          -- the two partition identities (P-17f)
          have hpartA := SectionNine.mStage_partition (blockFrameImpl T Blk hE2)
            hfgA B.bA F hheadA ((Nat.card ↥(blockFrameImpl T Blk hE2).MB) ^ 2)
            hmultA
          have hpartF := SectionNine.mStage_partition (blockFrameImpl T Blk hE2)
            hfgF B.bF F hheadF ((Nat.card ↥(blockFrameImpl T Blk hE2).MB) ^ 2)
            hmultF
          -- IH at the `C`-stage (`|L_C| < |L_Y| = n`, (145c))
          have hTC : exactImageCount B.bA F (blockFrameImpl T Blk hE2).TC
              = exactImageCount B.bF F (blockFrameImpl T Blk hE2).TC := by
            refine IH _ ?_ _ (blockFrameImpl T Blk hE2).TC rfl
            rw [← hcard]
            exact card_LC_lt T Blk hE2
          -- IH at the proper `C`-onto strata (the `M`-stage bound, all-`R` valid)
          have hstrata : ∀ J ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
                J.map (blockFrameImpl T Blk hE2).piBC = ⊤} \ {⊤},
              SectionEight.exactImageCountOn B.bA F
                  (blockFrameImpl T Blk hE2).TB J
                = SectionEight.exactImageCountOn B.bF F
                    (blockFrameImpl T Blk hE2).TB J := by
            rintro J ⟨hJC, hJne⟩
            simp only [SectionEight.exactImageCountOn]
            by_cases hJ : Function.Surjective
                ((blockFrameImpl T Blk hE2).TB.piY.comp J.subtype)
            · rw [dif_pos hJ, dif_pos hJ]
              refine IH _ ?_ _ ((blockFrameImpl T Blk hE2).TB.stratum J hJ) rfl
              rw [← hcard]
              exact card_stratum_mStage_lt T Blk hE2 J (by simpa using hJne) hJC hJ
            · rw [dif_neg hJ, dif_neg hJ]
          -- the `⊤`-stratum is the ambient count (`R = ⊥` ⟹ `π_B` iso)
          have htopA : SectionEight.exactImageCountOn B.bA F
                (blockFrameImpl T Blk hE2).TB ⊤ = exactImageCount B.bA F T := by
            rw [SectionEight.exactImageCountOn_top,
              (blockFrameImpl T Blk hE2).exactImageCount_TB_of_R_bot B.bA F hR]
          have htopF : SectionEight.exactImageCountOn B.bF F
                (blockFrameImpl T Blk hE2).TB ⊤ = exactImageCount B.bF F T := by
            rw [SectionEight.exactImageCountOn_top,
              (blockFrameImpl T Blk hE2).exactImageCount_TB_of_R_bot B.bF F hR]
          -- split the `⊤` stratum off both partitions and cancel the (equal) proper parts
          haveI : Finite (Subgroup (blockFrameImpl T Blk hE2).YB) :=
            Finite.of_injective
              (fun J : Subgroup (blockFrameImpl T Blk hE2).YB =>
                (J : Set (blockFrameImpl T Blk hE2).YB))
              SetLike.coe_injective
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
                SectionEight.exactImageCountOn B.bA F
                  (blockFrameImpl T Blk hE2).TB J
              = ∑ᶠ J ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
                  J.map (blockFrameImpl T Blk hE2).piBC = ⊤},
                  SectionEight.exactImageCountOn B.bF F
                    (blockFrameImpl T Blk hE2).TB J := by
            rw [← hpartA, ← hpartF, hTC]
          rw [hsplit, hsplit, htopA, htopF, finsum_mem_congr rfl hstrata] at hSsum
          exact Nat.add_right_cancel hSsum
        · -- head not covered: both counts vanish
          rw [exactImageCount_eq_zero_of_not_headSurj B.bA F T hhead,
            exactImageCount_eq_zero_of_not_headSurj B.bF F T hhead]
      · -- **`R`-stage lane** (`Blk.R ≠ ⊥`, §9.3): the closed system of `prop_8_9` (P-16d6) at
        -- `blockEnrichment` (P-17d), solved by `count_eq_of_closedRecursion` (P-17h) against
        -- the IH at the (145)/(148)/(153) bounds (P-17g).  [P-17i, assembly in progress.]
        sorry

/-- Theorem 4.2's second clause: "the same equality holds for every exact-image target `𝒥`"
— an *instance* of the first (strata are ordinary objects of the same category), recorded to
fix the consumption shape for §8.  [Relocated with `thm_4_2`; carries the same `hE2`.] -/
theorem thm_4_2_stratum (B : BoundaryMaps) (F : BoundaryFrame H E)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (hE2 : ∀ e : E, e ^ 2 = 1) (J : Subgroup Y)
    (hJ : Function.Surjective (T.piY.comp J.subtype)) :
    exactImageCount B.bA F (T.stratum J hJ) = exactImageCount B.bF F (T.stratum J hJ) :=
  thm_4_2 B F (T.stratum J hJ) hE2

end GQ2
