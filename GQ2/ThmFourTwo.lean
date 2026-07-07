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

/-! ## `R`-stage helpers -/

section RStageHelpers

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- **The `C`-stage is nontrivial off the scalar-stack regime** (discharges `prop_8_9`'s
`[Nontrivial YC]`): if `K = ⊤` then `L_Y = ⊤`, so `Y` is a finite 2-group, hence nilpotent —
and its upper central series exhibits `L_Y` as a scalar stack, contradicting the inductive
branch's `¬IsScalarStack`. -/
theorem nontrivial_YC_of_not_scalarStack (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (hstack : ¬ SectionSeven.IsScalarStack T.LY) :
    Nontrivial (blockFrameImpl T Blk hE2).YC := by
  by_contra hsub
  rw [not_nontrivial_iff_subsingleton] at hsub
  -- `K = ⊤` (everything dies in the `C`-quotient)
  have hK : Blk.K = ⊤ := by
    rw [← (blockFrameImpl T Blk hE2).ker_piC]
    exact top_unique fun y _ => MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
  -- hence `L_Y = ⊤` and `Y` is a finite 2-group
  have hLtop : T.LY = ⊤ :=
    top_unique (hK ▸ blockFrameImpl_K_le_LY T Blk)
  have h2Y : IsPGroup 2 Y := by
    intro y
    obtain ⟨k, hk⟩ := T.isPGroup_two ⟨y, by rw [hLtop]; trivial⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hnil : Group.IsNilpotent Y := h2Y.isNilpotent
  -- the upper central series is a scalar stack for `⊤ = L_Y`
  obtain ⟨n, hn⟩ := hnil.nilpotent
  refine hstack ⟨n, fun i => Subgroup.upperCentralSeries Y i, Subgroup.upperCentralSeries_zero Y,
    by rw [hLtop]; exact hn,
    fun i => Subgroup.upperCentralSeries_mono Y (Nat.le_succ i),
    fun i => show (Subgroup.upperCentralSeries Y i).Normal from inferInstance, ?_⟩
  intro i y x hx
  have h := (Subgroup.mem_upperCentralSeries_succ_iff).mp hx y
  have hrw : y * x * y⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
  rw [hrw]
  exact inv_mem h

/-- `C`-ontoness of a `B`-subgroup in sup form: `J.map π_{BC} = ⊤ ⟹ J ⊔ M_B = ⊤` (the shape
`card_stratum_LB_lt` consumes; `ker π_{BC} = M_B`). -/
theorem sup_MB_eq_top_of_map_piBC (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    {J : Subgroup (blockFrameImpl T Blk hE2).YB}
    (hJC : J.map (blockFrameImpl T Blk hE2).piBC = ⊤) :
    J ⊔ (blockFrameImpl T Blk hE2).MB = ⊤ := by
  refine top_unique fun y _ => ?_
  have hy : (blockFrameImpl T Blk hE2).piBC y ∈ J.map (blockFrameImpl T Blk hE2).piBC := by
    rw [hJC]
    exact Subgroup.mem_top _
  obtain ⟨j, hjJ, hj⟩ := Subgroup.mem_map.mp hy
  have hk : j⁻¹ * y ∈ (blockFrameImpl T Blk hE2).MB := by
    rw [← (blockFrameImpl T Blk hE2).ker_piBC]
    exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hj, inv_mul_cancel])
  have hyJ : y = j * (j⁻¹ * y) := by group
  rw [hyJ]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjJ) (Subgroup.mem_sup_right hk)

end RStageHelpers

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
        -- the IH at the (145)/(148)/(153) bounds (P-17g).
        classical
        by_cases hhead : Function.Surjective (fun x : ↥boundarySubgroup => (F.frameMap x).1)
        · -- head covered: obtain the closed system and feed the solver
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
          -- block normality instances (the `blockEnrichment` section hypotheses)
          haveI : (Blk.S.subgroupOf Blk.P).Normal := Blk.hS.subgroupOf Blk.P
          haveI : Nontrivial (blockFrameImpl T Blk hE2).YC :=
            nontrivial_YC_of_not_scalarStack T Blk hE2 hstack
          -- the chief-factor structure of the enrichment module (P-17d's `blockHsimple`)
          have hSimp := SectionNine.blockHsimple T Blk
          have hsimple : ∀ W : AddSubgroup (SectionNine.blockEnrichment T Blk hE2 F).Vmod,
              (∀ g : (blockFrameImpl T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤ :=
            hSimp.2
          have hVne : ∃ v : (SectionNine.blockEnrichment T Blk hE2 F).Vmod, v ≠ 0 := by
            haveI : Nontrivial (SectionNine.blockEnrichment T Blk hE2 F).Vmod := hSimp.1
            exact exists_ne 0
          -- ⚠ `hfaith` is NOT derivable from the block (a central 2-part of `Y` outside `K`
          -- centralizes `V` — e.g. `C₂ × (C₃ ⋉ C₂²)`-type blocks); flagged to P-16d6e6/e7:
          -- weaken `prop_8_9`'s hypothesis to the nontrivial-action form if the internal
          -- uses permit (the skeleton head only derives `hnt` from it).  Scoped sorry.
          have hfaith : ∀ g : (blockFrameImpl T Blk hE2).YC,
              (∀ v : (SectionNine.blockEnrichment T Blk hE2 F).Vmod, g • v = v) → g = 1 := by
            sorry
          -- the Gauss-`Z` residues (P-16d6e4a, in flight; the local value is the (83)
          -- evaluation `∓2^m`, the candidate side may stay on the ledger per the e4a design
          -- fallback).  Scoped sorry.
          obtain ⟨G0, hGaussZA, hGaussZF⟩ :
              ∃ G0 : ℤ,
                (∀ (l : (blockFrameImpl T Blk hE2).DR)
                  (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR),
                  SectionEight.GaussZResidue B.bA F
                    (SectionNine.blockEnrichment T Blk hE2 F) l h G0) ∧
                (∀ (l : (blockFrameImpl T Blk hE2).DR)
                  (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR),
                  SectionEight.GaussZResidue B.bF F
                    (SectionNine.blockEnrichment T Blk hE2 F) l h G0) := by
            sorry
          -- the closed system (P-16d6)
          obtain ⟨μ, G0', DT, instDT, phase, hDTpos, hA, hF⟩ :=
            SectionEight.prop_8_9 B T Blk hE2 (SectionNine.blockEnrichment T Blk hE2 F) F
              hfgF hheadA hheadF hsimple hfaith hVne G0 hGaussZA hGaussZF
          letI := instDT
          -- IH at the `B`-stage ((145b), needs `R ≠ ⊥`)
          have hTB : exactImageCount B.bA F (blockFrameImpl T Blk hE2).TB
              = exactImageCount B.bF F (blockFrameImpl T Blk hE2).TB := by
            refine IH _ ?_ _ (blockFrameImpl T Blk hE2).TB rfl
            rw [← hcard]
            exact card_LB_lt T Blk hE2 hR
          -- IH at the `C`-stage ((145c))
          have hTC : exactImageCount B.bA F (blockFrameImpl T Blk hE2).TC
              = exactImageCount B.bF F (blockFrameImpl T Blk hE2).TC := by
            refine IH _ ?_ _ (blockFrameImpl T Blk hE2).TC rfl
            rw [← hcard]
            exact card_LC_lt T Blk hE2
          -- IH at the pulled `B`-strata over proper `C`-onto images ((148))
          have hpull : ∀ (l : (blockFrameImpl T Blk hE2).DR)
              (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR)
              (J' : Subgroup ((blockFrameImpl T Blk hE2).scalarCover l h).cover),
              J'.map ((blockFrameImpl T Blk hE2).scalarCover l h).p ≠ ⊤ →
              (J'.map ((blockFrameImpl T Blk hE2).scalarCover l h).p).map
                  (blockFrameImpl T Blk hE2).piBC = ⊤ →
              SectionEight.exactImageCountOn B.bA F
                  (((blockFrameImpl T Blk hE2).scalarCover l h).pullTarget
                    (blockFrameImpl T Blk hE2).TB) J'
                = SectionEight.exactImageCountOn B.bF F
                    (((blockFrameImpl T Blk hE2).scalarCover l h).pullTarget
                      (blockFrameImpl T Blk hE2).TB) J' := by
            intro l hl J' hJtop hJC
            simp only [SectionEight.exactImageCountOn]
            by_cases hJ' : Function.Surjective
                ((((blockFrameImpl T Blk hE2).scalarCover l hl).pullTarget
                  (blockFrameImpl T Blk hE2).TB).piY.comp J'.subtype)
            · rw [dif_pos hJ', dif_pos hJ']
              refine IH _ ?_ _
                ((((blockFrameImpl T Blk hE2).scalarCover l hl).pullTarget
                  (blockFrameImpl T Blk hE2).TB).stratum J' hJ') rfl
              rw [← hcard]
              exact card_stratum_LB_lt T Blk hE2 hR
                ((blockFrameImpl T Blk hE2).scalarCover l hl) J' hJ' hJtop
                (sup_MB_eq_top_of_map_piBC T Blk hE2 hJC)
            · rw [dif_neg hJ', dif_neg hJ']
          -- the phase-cover counts agree ((141)/(142) via `lemma_8_3` at `⊤` + (153)-IH)
          have hphase : ∀ (l : (blockFrameImpl T Blk hE2).DR)
              (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR) (ζ : DT),
              (blockFrameImpl T Blk hE2).nPhase B.bA F (phase l h ζ)
                = (blockFrameImpl T Blk hE2).nPhase B.bF F (phase l h ζ) := by
            intro l hl ζ
            have hstr : ∀ J' ∈ {J' : Subgroup (phase l hl ζ).cover |
                J'.map (phase l hl ζ).p = ⊤},
                SectionEight.exactImageCountOn B.bA F
                    ((phase l hl ζ).pullTarget (blockFrameImpl T Blk hE2).TC) J'
                  = SectionEight.exactImageCountOn B.bF F
                      ((phase l hl ζ).pullTarget (blockFrameImpl T Blk hE2).TC) J' := by
              intro J' _
              simp only [SectionEight.exactImageCountOn]
              by_cases hJ' : Function.Surjective
                  (((phase l hl ζ).pullTarget (blockFrameImpl T Blk hE2).TC).piY.comp
                    J'.subtype)
              · rw [dif_pos hJ', dif_pos hJ']
                refine IH _ ?_ _
                  (((phase l hl ζ).pullTarget (blockFrameImpl T Blk hE2).TC).stratum J' hJ')
                  rfl
                rw [← hcard]
                exact card_stratum_LC_lt T Blk hE2 (phase l hl ζ) J' hJ'
              · rw [dif_neg hJ', dif_neg hJ']
            have h8A := SectionEight.lemma_8_3 hfgA B.bA F (blockFrameImpl T Blk hE2).TC
              (phase l hl ζ) SectionEight.lemma_8_2_gammaA ⊤
              (blockFrameImpl T Blk hE2).TC.top_head_surjective
            have h8F := SectionEight.lemma_8_3 hfgF B.bF F (blockFrameImpl T Blk hE2).TC
              (phase l hl ζ) (SectionEight.lemma_8_2_local B) ⊤
              (blockFrameImpl T Blk hE2).TC.top_head_surjective
            have heq : 8 * SectionEight.liftableCount B.bA F (blockFrameImpl T Blk hE2).TC
                  (phase l hl ζ) ⊤ (blockFrameImpl T Blk hE2).TC.top_head_surjective
                = 8 * SectionEight.liftableCount B.bF F (blockFrameImpl T Blk hE2).TC
                    (phase l hl ζ) ⊤ (blockFrameImpl T Blk hE2).TC.top_head_surjective := by
              rw [h8A, h8F]
              exact finsum_mem_congr rfl hstr
            rw [(blockFrameImpl T Blk hE2).nPhase_eq_liftableCount_top B.bA F (phase l hl ζ),
              (blockFrameImpl T Blk hE2).nPhase_eq_liftableCount_top B.bF F (phase l hl ζ)]
            omega
          -- solve (P-17h)
          exact SectionNine.count_eq_of_closedRecursion (blockFrameImpl T Blk hE2) B.bA B.bF F
            μ G0' DT phase hA hF (Nat.pos_iff_ne_zero.mp hDTpos) hTB hTC hpull hphase
        · -- head not covered: both counts vanish
          rw [exactImageCount_eq_zero_of_not_headSurj B.bA F T hhead,
            exactImageCount_eq_zero_of_not_headSurj B.bF F T hhead]

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
