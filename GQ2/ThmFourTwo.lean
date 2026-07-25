/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionNine
import GQ2.Block.Enrichment
import GQ2.Prop89Close
import GQ2.GaussZ.GammaAD
import GQ2.SourceData

/-!
# Theorem 4.2 — the §9 sink

`thm_4_2` (the boundary-framed exact-image theorem) and its stratum clause, **relocated from
`GQ2/SectionNine.lean`** (second hop of the established relocation pattern; first hop was
`BoundaryFrame → SectionNine`, the §9 induction).  The move is forced by the import DAG: the `R`-stage
lane consumes `prop_8_9` (`GQ2/Prop89Close.lean`, incomparable with `SectionNine`) **and**
`SectionNine.blockEnrichment` (`GQ2/BlockEnrichment.lean`, strictly *downstream* of
`SectionNine` because it consumes `kappa0_exists`) — so the proof cannot live inside
`SectionNine.lean`.  A comment-pointer remains there; the fully qualified name `GQ2.thm_4_2`
is unchanged, so call sites only gain an import.

The proof: strong induction on `|L_Y|` with three lanes — terminal (`terminal_count_eq`,
the §9 induction), `M`-stage (`R = ⊥`: `mStage_partition` ×2 at multiplicity `|M_B|²`, the §9 induction +
`MStageCount`/`MStageCountGammaA`), and `R`-stage (`R ≠ ⊥`: `blockEnrichment` + `prop_8_9`
solved by `count_eq_of_closedRecursion` against the §9 induction bounds).
-/

namespace GQ2

open SectionEight

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-! ## `R`-stage helpers -/

section RStageHelpers

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
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
  -- the upper central series is a scalar stack for `⊤ = L_Y`
  obtain ⟨n, hn⟩ := h2Y.isNilpotent.nilpotent
  refine hstack ⟨n, fun i => Subgroup.upperCentralSeries Y i, Subgroup.upperCentralSeries_zero Y,
    by rw [hLtop]; exact hn,
    fun i => Subgroup.upperCentralSeries_mono Y (Nat.le_succ i),
    fun i => show (Subgroup.upperCentralSeries Y i).Normal from inferInstance, ?_⟩
  intro i y x hx
  have h := Subgroup.mem_upperCentralSeries_succ_iff.mp hx y
  rw [show y * x * y⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ by group]
  exact inv_mem h

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `C`-ontoness of a `B`-subgroup in sup form: `J.map π_{BC} = ⊤ ⟹ J ⊔ M_B = ⊤` (the shape
`card_stratum_LB_lt` consumes; `ker π_{BC} = M_B`). -/
theorem sup_MB_eq_top_of_map_piBC (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    {J : Subgroup (blockFrameImpl T Blk hE2).YB}
    (hJC : J.map (blockFrameImpl T Blk hE2).piBC = ⊤) :
    J ⊔ (blockFrameImpl T Blk hE2).MB = ⊤ := by
  refine top_unique fun y _ => ?_
  have hy : (blockFrameImpl T Blk hE2).piBC y ∈ J.map (blockFrameImpl T Blk hE2).piBC := by
    rw [hJC]; exact Subgroup.mem_top _
  obtain ⟨j, hjJ, hj⟩ := Subgroup.mem_map.mp hy
  have hk : j⁻¹ * y ∈ (blockFrameImpl T Blk hE2).MB := by
    rw [← (blockFrameImpl T Blk hE2).ker_piBC]
    exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hj, inv_mul_cancel])
  rw [show y = j * (j⁻¹ * y) by group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjJ) (Subgroup.mem_sup_right hk)

end RStageHelpers

/-- **The `M`-stage lane** (`R = ⊥`) of the §9 master induction: the two `mStage_partition`
(the §9 induction) identities at the block frame, multiplicity `|M_B|²` per source, solved against the
strong-induction hypothesis `IH`.  Extracted from `thm_4_2`; source-generic over
`S : SourceData` since the SourceData refactor (the `Γ_A` supply enters through `S.tfg` and
`S.liftsOver_card`). -/
private theorem mStage_lane (S : SourceData) (B : BoundaryMaps) (F : BoundaryFrame H E)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (Blk : SectionSeven.MinimalBlock T.LY) (hR : Blk.frattiniK = ⊥) (n : ℕ)
    (hcard : Nat.card ↥T.LY = n)
    (IH : ∀ m, m < n → ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [DiscreteTopology Z]
      [Finite Z] (T' : MarkedTarget H E Z), Nat.card ↥T'.LY = m →
      exactImageCount S.b F T' = exactImageCount B.bF F T') :
    exactImageCount S.b F T = exactImageCount B.bF F T := by
  classical
  by_cases hhead : Function.Surjective (fun x : ↥boundarySubgroup => (F.frameMap x).1)
  · -- head covered: run the partition at both sources
    have hfgS : ∃ s : Finset ↥S.Γ,
        (Subgroup.closure (s : Set ↥S.Γ)).topologicalClosure = ⊤ :=
      S.tfg
    have hfgF : ∃ s : Finset AbsGalQ2,
        (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤ :=
      Foundations.absGalQ2_isTopologicallyFinitelyGenerated
    have hheadS : Function.Surjective (fun γ : ↥S.Γ => (F.frameMap (S.b γ)).1) :=
      hhead.comp S.b_surjective
    have hheadF : Function.Surjective (fun γ : AbsGalQ2 => (F.frameMap (B.bF γ)).1) :=
      hhead.comp B.bF_surjective
    -- the multiplicity `|M_B|²`, per source (`MStageCount` / the source obligation)
    have hmultF : ∀ ρ : BoundaryLifts B.bF F (blockFrameImpl T Blk hE2).TC,
        Nat.card ((blockFrameImpl T Blk hE2).LiftsOver B.bF F ρ)
          = (Nat.card ↥(blockFrameImpl T Blk hE2).MB) ^ 2 :=
      (blockFrameImpl T Blk hE2).liftsOver_card_local B.bF F
    have hmultS : ∀ ρ : BoundaryLifts S.b F (blockFrameImpl T Blk hE2).TC,
        Nat.card ((blockFrameImpl T Blk hE2).LiftsOver S.b F ρ)
          = (Nat.card ↥(blockFrameImpl T Blk hE2).MB) ^ 2 :=
      S.liftsOver_card (blockFrameImpl T Blk hE2) S.b F
    -- the two partition identities (the §9 induction)
    have hpartS := SectionNine.mStage_partition (blockFrameImpl T Blk hE2)
      hfgS S.b F hheadS ((Nat.card ↥(blockFrameImpl T Blk hE2).MB) ^ 2)
      hmultS
    have hpartF := SectionNine.mStage_partition (blockFrameImpl T Blk hE2)
      hfgF B.bF F hheadF ((Nat.card ↥(blockFrameImpl T Blk hE2).MB) ^ 2)
      hmultF
    -- IH at the `C`-stage (`|L_C| < |L_Y| = n`, (145c))
    have hTC : exactImageCount S.b F (blockFrameImpl T Blk hE2).TC
        = exactImageCount B.bF F (blockFrameImpl T Blk hE2).TC := by
      refine IH _ ?_ _ (blockFrameImpl T Blk hE2).TC rfl
      exact hcard ▸ card_LC_lt T Blk hE2
    -- IH at the proper `C`-onto strata (the `M`-stage bound, all-`R` valid)
    have hstrata : ∀ J ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
          J.map (blockFrameImpl T Blk hE2).piBC = ⊤} \ {⊤},
        SectionEight.exactImageCountOn S.b F
            (blockFrameImpl T Blk hE2).TB J
          = SectionEight.exactImageCountOn B.bF F
              (blockFrameImpl T Blk hE2).TB J := by
      rintro J ⟨hJC, hJne⟩
      simp only [SectionEight.exactImageCountOn]
      by_cases hJ : Function.Surjective
          ((blockFrameImpl T Blk hE2).TB.piY.comp J.subtype)
      · rw [dif_pos hJ, dif_pos hJ]
        refine IH _ ?_ _ ((blockFrameImpl T Blk hE2).TB.stratum J hJ) rfl
        exact hcard ▸ card_stratum_mStage_lt T Blk hE2 J (by simpa using hJne) hJC hJ
      · rw [dif_neg hJ, dif_neg hJ]
    -- the `⊤`-stratum is the ambient count (`R = ⊥` ⟹ `π_B` iso)
    have htopS : SectionEight.exactImageCountOn S.b F
          (blockFrameImpl T Blk hE2).TB ⊤ = exactImageCount S.b F T := by
      rw [SectionEight.exactImageCountOn_top,
        (blockFrameImpl T Blk hE2).exactImageCount_TB_of_R_bot S.b F hR]
    have htopF : SectionEight.exactImageCountOn B.bF F
          (blockFrameImpl T Blk hE2).TB ⊤ = exactImageCount B.bF F T := by
      rw [SectionEight.exactImageCountOn_top,
        (blockFrameImpl T Blk hE2).exactImageCount_TB_of_R_bot B.bF F hR]
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
          SectionEight.exactImageCountOn S.b F
            (blockFrameImpl T Blk hE2).TB J
        = ∑ᶠ J ∈ {J : Subgroup (blockFrameImpl T Blk hE2).YB |
            J.map (blockFrameImpl T Blk hE2).piBC = ⊤},
            SectionEight.exactImageCountOn B.bF F
              (blockFrameImpl T Blk hE2).TB J := by
      rw [← hpartS, ← hpartF, hTC]
    rw [hsplit, hsplit, htopS, htopF, finsum_mem_congr rfl hstrata] at hSsum
    exact Nat.add_right_cancel hSsum
  · -- head not covered: both counts vanish
    rw [exactImageCount_eq_zero_of_not_headSurj S.b F T hhead,
      exactImageCount_eq_zero_of_not_headSurj B.bF F T hhead]

/-- **`R`-stage IH at the pulled `B`-strata** ((148)): over a proper image that is onto `C`,
the pulled-back stratum `J'` is a strictly smaller marked target (`card_stratum_LB_lt`), so
the two source exact-image counts agree by the induction hypothesis. -/
private theorem rStage_pull (S : SourceData) (B : BoundaryMaps) (F : BoundaryFrame H E)
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (Blk : SectionSeven.MinimalBlock T.LY) (hR : Blk.frattiniK ≠ ⊥) (n : ℕ)
    (hcard : Nat.card ↥T.LY = n)
    (IH : ∀ m, m < n → ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [DiscreteTopology Z]
      [Finite Z] (T' : MarkedTarget H E Z), Nat.card ↥T'.LY = m →
      exactImageCount S.b F T' = exactImageCount B.bF F T')
    (l : (blockFrameImpl T Blk hE2).DR) (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR)
    (J' : Subgroup ((blockFrameImpl T Blk hE2).scalarCover l h).cover)
    (hJtop : J'.map ((blockFrameImpl T Blk hE2).scalarCover l h).p ≠ ⊤)
    (hJC : (J'.map ((blockFrameImpl T Blk hE2).scalarCover l h).p).map
        (blockFrameImpl T Blk hE2).piBC = ⊤) :
    SectionEight.exactImageCountOn S.b F
        (((blockFrameImpl T Blk hE2).scalarCover l h).pullTarget
          (blockFrameImpl T Blk hE2).TB) J'
      = SectionEight.exactImageCountOn B.bF F
          (((blockFrameImpl T Blk hE2).scalarCover l h).pullTarget
            (blockFrameImpl T Blk hE2).TB) J' := by
  simp only [SectionEight.exactImageCountOn]
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

/-- **`R`-stage phase-cover counts agree** ((141)/(142)): for any phase cover `Cζ ↠ C`, the
`⊤`-stratum eight-lift partition (`lemma_8_3`) has proper summands agreeing by the IH at the
`C`-strata, so the two source `n_{Γ,0}(ζ)` counts agree. -/
private theorem rStage_phase (S : SourceData) (B : BoundaryMaps) (F : BoundaryFrame H E)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (Blk : SectionSeven.MinimalBlock T.LY) (n : ℕ) (hcard : Nat.card ↥T.LY = n)
    (IH : ∀ m, m < n → ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [DiscreteTopology Z]
      [Finite Z] (T' : MarkedTarget H E Z), Nat.card ↥T'.LY = m →
      exactImageCount S.b F T' = exactImageCount B.bF F T')
    (hfgS : ∃ s : Finset ↥S.Γ,
      (Subgroup.closure (s : Set ↥S.Γ)).topologicalClosure = ⊤)
    (hfgF : ∃ s : Finset AbsGalQ2,
      (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (Cζ : CentralCover (blockFrameImpl T Blk hE2).YC) :
    (blockFrameImpl T Blk hE2).nPhase S.b F Cζ
      = (blockFrameImpl T Blk hE2).nPhase B.bF F Cζ := by
  have hstr : ∀ J' ∈ {J' : Subgroup Cζ.cover | J'.map Cζ.p = ⊤},
      SectionEight.exactImageCountOn S.b F
          (Cζ.pullTarget (blockFrameImpl T Blk hE2).TC) J'
        = SectionEight.exactImageCountOn B.bF F
            (Cζ.pullTarget (blockFrameImpl T Blk hE2).TC) J' := by
    intro J' _
    simp only [SectionEight.exactImageCountOn]
    by_cases hJ' : Function.Surjective
        ((Cζ.pullTarget (blockFrameImpl T Blk hE2).TC).piY.comp J'.subtype)
    · rw [dif_pos hJ', dif_pos hJ']
      refine IH _ ?_ _
        ((Cζ.pullTarget (blockFrameImpl T Blk hE2).TC).stratum J' hJ') rfl
      exact hcard ▸ card_stratum_LC_lt T Blk hE2 Cζ J' hJ'
    · rw [dif_neg hJ', dif_neg hJ']
  have h8S := SectionEight.lemma_8_3 hfgS S.b F (blockFrameImpl T Blk hE2).TC
    Cζ S.hom8 ⊤
    (blockFrameImpl T Blk hE2).TC.top_head_surjective
  have h8F := SectionEight.lemma_8_3 hfgF B.bF F (blockFrameImpl T Blk hE2).TC
    Cζ (SectionEight.lemma_8_2_local B) ⊤
    (blockFrameImpl T Blk hE2).TC.top_head_surjective
  have heq : 8 * SectionEight.liftableCount S.b F (blockFrameImpl T Blk hE2).TC
        Cζ ⊤ (blockFrameImpl T Blk hE2).TC.top_head_surjective
      = 8 * SectionEight.liftableCount B.bF F (blockFrameImpl T Blk hE2).TC
          Cζ ⊤ (blockFrameImpl T Blk hE2).TC.top_head_surjective := by
    rw [h8S, h8F]
    exact finsum_mem_congr rfl hstr
  rw [(blockFrameImpl T Blk hE2).nPhase_eq_liftableCount_top S.b F Cζ,
    (blockFrameImpl T Blk hE2).nPhase_eq_liftableCount_top B.bF F Cζ]
  omega

/-- **The `R`-stage lane** (`R ≠ ⊥`) of the §9 master induction: the closed system of
`prop_8_9` (the Prop. 8.9 assembly) at `blockEnrichment` (the §9 induction), solved by `count_eq_of_closedRecursion`
(the §9 induction) against the IH at the (145)/(148)/(153) bounds.  Extracted from `thm_4_2`. -/
private theorem rStage_lane (S : SourceData) (B : BoundaryMaps) (F : BoundaryFrame H E)
    (R : LocalReciprocity) (horient : TameUnitOrientation R B.tameF)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (Blk : SectionSeven.MinimalBlock T.LY)
    (_hstack : ¬ SectionSeven.IsScalarStack T.LY) (hR : Blk.frattiniK ≠ ⊥) (n : ℕ)
    (hcard : Nat.card ↥T.LY = n)
    (IH : ∀ m, m < n → ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [DiscreteTopology Z]
      [Finite Z] (T' : MarkedTarget H E Z), Nat.card ↥T'.LY = m →
      exactImageCount S.b F T' = exactImageCount B.bF F T') :
    exactImageCount S.b F T = exactImageCount B.bF F T := by
  classical
  by_cases hhead : Function.Surjective (fun x : ↥boundarySubgroup => (F.frameMap x).1)
  · -- head covered: obtain the closed system and feed the solver
    have hfgS : ∃ s : Finset ↥S.Γ,
        (Subgroup.closure (s : Set ↥S.Γ)).topologicalClosure = ⊤ :=
      S.tfg
    have hfgF : ∃ s : Finset AbsGalQ2,
        (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤ :=
      Foundations.absGalQ2_isTopologicallyFinitelyGenerated
    have hheadS : Function.Surjective (fun γ : ↥S.Γ => (F.frameMap (S.b γ)).1) :=
      hhead.comp S.b_surjective
    have hheadF : Function.Surjective (fun γ : AbsGalQ2 => (F.frameMap (B.bF γ)).1) :=
      hhead.comp B.bF_surjective
    -- block normality instances (the `blockEnrichmentD` section hypotheses)
    haveI : (Blk.S.subgroupOf Blk.P).Normal := Blk.hS.subgroupOf Blk.P
    haveI : Blk.K.Normal := Blk.hK
    haveI : Blk.frattiniK.Normal := SectionSeven.frattiniLike_normal Blk.K Blk.hK
    haveI : Nontrivial (blockFrameImpl T Blk hE2).YC :=
      nontrivial_YC_of_not_scalarStack T Blk hE2 _hstack
    -- the source's ambient scalar action (the SourceData refactor)
    letI := S.smulZmod2
    -- the chief-factor structure of the enrichment module (the §9 induction's `blockHsimple`)
    have hSimp := SectionNine.blockHsimple T Blk
    have hsimple : ∀ W : AddSubgroup (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod,
        (∀ g : (blockFrameImpl T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤ :=
      hSimp.2
    have hVne : ∃ v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod, v ≠ 0 := by
      haveI : Nontrivial (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod := hSimp.1
      exact exists_ne 0
    -- `hnt` (the nontrivial `Y/K`-action on `V`): the block's `nontrivial_action`
    -- field in the enrichment-module form (`blockHnt`).  The former `hfaith`
    -- the weaker hypothesis is sufficient here —
    -- faithfulness is NOT block-derivable (a central 2-part of `Y` outside `K`
    -- centralizes `V` — e.g. `C₂ × (C₃ ⋉ C₂²)`-type blocks).
    have hnt : ∃ (g : (blockFrameImpl T Blk hE2).YC)
        (v : (SectionNine.blockEnrichmentD T Blk hE2 F).Vmod), g • v ≠ v :=
      SectionNine.blockHnt T Blk
    -- the Gauss-`Z` residues: the hypothesis-free obtain at the head-inflated enrichment —
    -- `G0 = ∓2^m` by the head dichotomy, orientation from the theorem's `(R, horient)`
    -- binders; the source contributes its `gaussZ_*` dichotomy leaves (the SourceData
    -- refactor's external-`G0` seam)
    obtain ⟨G0, hGaussZS, hGaussZF⟩ :
        ∃ G0 : ℤ,
          (∀ (l : (blockFrameImpl T Blk hE2).DR)
            (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR),
            SectionEight.GaussZResidue S.b F
              (SectionNine.blockEnrichmentD T Blk hE2 F) l h G0) ∧
          (∀ (l : (blockFrameImpl T Blk hE2).DR)
            (h : l ≠ (blockFrameImpl T Blk hE2).zeroDR),
            SectionEight.GaussZResidue B.bF F
              (SectionNine.blockEnrichmentD T Blk hE2 F) l h G0) :=
      gaussZ_obtain_blockD_of_sources T Blk hE2 S B F R horient hsimple hVne hnt
    -- the closed system (the Prop. 8.9 assembly, over the bundled source)
    obtain ⟨μ, G0', DT, instDT, phase, hDTpos, hS, hF⟩ :=
      prop_8_9_of_sources S B T Blk hE2 (SectionNine.blockEnrichmentD T Blk hE2 F) F
        hfgF hheadS hheadF hsimple hVne hnt G0 hGaussZS hGaussZF
    letI := instDT
    -- IH at the `B`-stage ((145b), needs `R ≠ ⊥`)
    have hTB : exactImageCount S.b F (blockFrameImpl T Blk hE2).TB
        = exactImageCount B.bF F (blockFrameImpl T Blk hE2).TB := by
      refine IH _ ?_ _ (blockFrameImpl T Blk hE2).TB rfl
      exact hcard ▸ card_LB_lt T Blk hE2 hR
    -- IH at the `C`-stage ((145c))
    have hTC : exactImageCount S.b F (blockFrameImpl T Blk hE2).TC
        = exactImageCount B.bF F (blockFrameImpl T Blk hE2).TC := by
      refine IH _ ?_ _ (blockFrameImpl T Blk hE2).TC rfl
      exact hcard ▸ card_LC_lt T Blk hE2
    -- IH at the pulled `B`-strata ((148), `rStage_pull`) and phase-cover agreement
    -- ((141)/(142), `rStage_phase`); then solve (the §9 induction).
    exact SectionNine.count_eq_of_closedRecursion (blockFrameImpl T Blk hE2) S.b B.bF F
      μ G0' DT phase hS hF hDTpos.ne' hTB hTC
      (fun l h J' hJtop hJC => rStage_pull S B F T hE2 Blk hR n hcard IH l h J' hJtop hJC)
      (fun l h ζ => rStage_phase S B F T hE2 Blk n hcard IH hfgS hfgF (phase l h ζ))
  · -- head not covered: both counts vanish
    rw [exactImageCount_eq_zero_of_not_headSurj S.b F T hhead,
      exactImageCount_eq_zero_of_not_headSurj B.bF F T hhead]

/-- **Theorem 4.2 over an abstract source** (the SourceData refactor): for every
`S : SourceData`, every boundary frame, and every boundary-framed marked target `𝒴`, the
exact-image lift counts of `S` and `G_ℚ₂` agree: `e^β_S(𝒴) = e^β_{G_ℚ₂}(𝒴)`.  The `Γ_A`
capstone `thm_4_2` below is this statement at `B.sourceA` (definitionally: `B.sourceA.b`
**is** `B.bA`); R32 instantiates it at `sourceR` with zero further refactoring.  Same
strong-induction skeleton as `thm_4_2`, with the terminal lane through
`terminal_count_eq_of_sources`. -/
theorem thm_4_2_of_sources (S : SourceData) (B : BoundaryMaps) (F : BoundaryFrame H E)
    (R : LocalReciprocity) (horient : TameUnitOrientation R B.tameF)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    exactImageCount S.b F T = exactImageCount B.bF F T := by
  -- Strong induction on the marked-kernel size `n = |L_Y|` (§9, pp. 44–47), generalizing
  -- the whole target `(Y, 𝒴)` exactly as in `thm_4_2` below.
  suffices h : ∀ (n : ℕ) (Y : Type) [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
      [Finite Y] (T : MarkedTarget H E Y), Nat.card ↥T.LY = n →
      exactImageCount S.b F T = exactImageCount B.bF F T by
    exact h (Nat.card ↥T.LY) Y T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Y instGY instTY instDY instFY T hcard
    by_cases hstack : SectionSeven.IsScalarStack T.LY
    · -- **Terminal lane** (`IsScalarStack T.LY`, §9.1–9.2): the two exact-image problems
      -- are identified through the common marked pro-2 quotient
      -- (`terminal_count_eq_of_sources`, via the promoted `ker_pro2` field).
      exact terminal_count_eq_of_sources S B F T hE2 hstack
    · -- Inductive case: a nonscalar chief factor exists; choose the §7 minimal block.
      obtain ⟨Blk⟩ := SectionSeven.exists_minimalBlock T.normal T.isPGroup_two hstack
      by_cases hR : Blk.frattiniK = ⊥
      · -- **`M`-stage lane** (`R = ⊥`, §9.2): delegated to `mStage_lane`.
        exact mStage_lane S B F T hE2 Blk hR n hcard IH
      · -- **`R`-stage lane** (`R ≠ ⊥`, §9.3): delegated to `rStage_lane`.
        exact rStage_lane S B F R horient T hE2 Blk hstack hR n hcard IH

/-- **Theorem 4.2 (boundary-framed exact-image theorem).**  For every boundary frame and
every boundary-framed marked target `𝒴`, the exact-image lift counts from the two sources
agree: `e^β_{Γ_A}(𝒴) = e^β_{G_ℚ₂}(𝒴)`.

Stated for any `BoundaryMaps` witness of the Prop 3.14 data (the choice is fixed "once and
for all" in §4 and only its bundled properties are used).

**Encoding correction** (documented in `docs/section9-extraction.md`): the hypothesis
`(hE2 : ∀ e : E, e ^ 2 = 1)` is required because the §9 induction descends the θ-decoration
through the block via `lemma_7_3`, whose (paper-stated)
hypothesis is that the decoration target is elementary abelian 2; the terminal case kills
the odd complement through `θ` for the same reason.  §10 consumes the theorem at `E = 0`
only, so the correction is downstream-harmless.  The theorem lives here because its proof
needs §§5–9 machinery, including `blockEnrichment` and
`prop_8_9`, both downstream of `SectionNine`; see the module docstring.

**Instance binders**: the two `AbsGalQ2` topology hypotheses mirror
`terminal_count_eq`'s (the `Half139Local`/`BoundaryMapsWitness` tower discipline — they are
deliberately not global instances); the consumer `eq_154` already carries exactly
these two.  The remaining topology instances the inductive lanes need (`GammaA`'s
compact/t.d./topological-group triple, `IsTopologicalGroup AbsGalQ2`) are globally inferable
(`GammaA : ProfiniteGrp`; mathlib's Krull-topology instance), so they are *not* binders.

The proof combines the induction scaffold, terminal lane, `M`-stage lane, and the `R`-stage lane
assembled against `prop_8_9` in `GQ2/Prop89Close.lean`.
Axioms B1/B3c/B6/B7/B8/B9 enter through the ingredients, per App. D (B7′, the dyadic Hilbert
symbol, is now an in-repo theorem, not an axiom). -/
theorem thm_4_2 (B : BoundaryMaps) (F : BoundaryFrame H E)
    (R : LocalReciprocity) (horient : TameUnitOrientation R B.tameF)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (hE2 : ∀ e : E, e ^ 2 = 1) :
    exactImageCount B.bA F T = exactImageCount B.bF F T := by
  -- The same-name flip (the SourceData refactor): the strong induction lives in
  -- `thm_4_2_of_sources`; this capstone is its instance at the `Γ_A` bundle `B.sourceA`,
  -- whose boundary map is definitionally `B.bA` (`BoundaryMaps.sourceA_b`).
  exact thm_4_2_of_sources B.sourceA B F R horient T hE2

/-- Theorem 4.2's second clause: "the same equality holds for every exact-image target `𝒥`"
— an *instance* of the first (strata are ordinary objects of the same category), recorded to
fix the consumption shape for §8.  [Relocated with `thm_4_2`; carries the same `hE2`.] -/
theorem thm_4_2_stratum (B : BoundaryMaps) (F : BoundaryFrame H E)
    (R : LocalReciprocity) (horient : TameUnitOrientation R B.tameF)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y)
    (hE2 : ∀ e : E, e ^ 2 = 1) (J : Subgroup Y)
    (hJ : Function.Surjective (T.piY.comp J.subtype)) :
    exactImageCount B.bA F (T.stratum J hJ) = exactImageCount B.bF F (T.stratum J hJ) :=
  thm_4_2 B F R horient (T.stratum J hJ) hE2

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Prop 3.14 = ⟦prop-compatiblemarking⟧
  * Theorem 4.2 = ⟦thm-fixedframe⟧
-/
