/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.BlockEnrichment
import GQ2.Block.HeadDat

/-!
# The head-inflated block enrichment at a general residue cardinality (ticket SD-R1)

Clone of the `F.alpha`-consuming tier of `GQ2/Block/HeadDat.lean` (370 ln), re-typed at F3's
`Tq q`.  Completes SD-R1's part of the Block trio: the tame pair itself is in
`GQ2/Dyadic/Recursion/Block.lean` (`hvSigmaK`, `hvTauK`, `hv_genK`, `hv_relK`); this file adds
the `H_V`-level invariance, κ⁰ datum and the head-inflated enrichment.

## What is reused rather than cloned

The entire head-quotient apparatus is boundary-free and consumed by import: `headEquiv` (:55),
`headAct` (:81), `blockPiCH` (:89), `blockPiCH_compat` (:110), `headActKer` (:132),
`headActKer_normal` (:142), `HVq` (:149), `hvAct` (:152), `hvAct_faithful` (:178),
`blockProjF` (:192), `blockProjF_compat` (:203), `hv_simple` (:267), `blockPiCH_eq_TC_piY`
(:359).  Only `blockProjF_surjective` (:197) is copied, because it is `private`.

`boundaryLift_head_gammaA` (:342) and `boundaryLift_head_local` (:350) are **not** cloned:
they are the `Γ_A`/`G_ℚ₂` instantiations.  Their `K`-analogue is the generic one-liner
`boundaryLift_headK` below, which serves any source.

## ⚠ SEAM B, threaded (dated 2026-07-31) — SD-R2 obligation

As in `GQ2/Dyadic/Recursion/BlockEnrichment.lean`: `GQ2.kappa0_exists_tame`
(`GQ2/KappaNormalForm.lean:1150`) demands `hrel : s⁻¹ * t * s = t ^ 2`, while `hv_relK` proves
the true general-`q` statement `= t ^ q`.  The exponent-2 clause is threaded here as `hrel2HV`
(the `H_V`-level binder) alongside `hrel2` (the head-level binder inherited from
`blockEnrichmentK`).  SD-R2 removes both when it generalizes `ActsThroughTame`/`kappa0_exists`/
`kappa0_exists_tame` to `t ^ q`; at `q = 2` both are free (`hv_relK` resp. `tame_rel_map_q`).

Axioms: none beyond std-3; each clone's print equals its model's.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionSeven GQ2.SectionEight GQ2.SectionNine QuadraticFp2

open scoped Classical

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
variable {q : ℕ} {P : ProfiniteGrp}


/-! Three `private` helpers copied from the model (`GQ2/Block/HeadDat.lean:95,102,197`) — not
referenceable from here, and degree-blind. -/
omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal]
  [(Blk.S.subgroupOf Blk.P).Normal] in
@[simp] private theorem blockPiCH_mkK (y : Y) :
    blockPiCH T Blk (QuotientGroup.mk' Blk.K y) = T.piY y :=
  QuotientGroup.lift_mk' _ _ _
omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal]
  [(Blk.S.subgroupOf Blk.P).Normal] in
private theorem blockPiCH_surjectiveK : Function.Surjective (blockPiCH T Blk) := fun h => by
  obtain ⟨y, hy⟩ := T.piY_surjective h
  exact ⟨QuotientGroup.mk' Blk.K y, (blockPiCH_mkK T Blk y).trans hy⟩
omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
private theorem blockProjF_surjectiveK : Function.Surjective (blockProjF T Blk) :=
  (QuotientGroup.mk'_surjective _).comp (blockPiCH_surjectiveK T Blk)


omit [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- Invariance of `q̄_λ` under the faithful `H_V`-action.  Clone of `GQ2.SectionNine.hv_inv`
(`GQ2/Block/HeadDat.lean:251`). -/
theorem hv_invK (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
    (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    letI := blockPS_commGroup Blk
    letI := hvAct T Blk
    IsInvariant (HVq T Blk) (blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := hvAct T Blk
  intro g v
  obtain ⟨c, rfl⟩ := blockProjF_surjectiveK T Blk g
  rw [← blockProjF_compat T Blk c v]
  exact blockHinvK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne c v

/-- The `H_V`-level κ⁰ existential.  Clone of `GQ2.SectionNine.blockKappa0HV`
(`GQ2/Block/HeadDat.lean:286`); `hrel2HV` is the threaded SEAM-B clause. -/
noncomputable def blockKappa0HVK (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
    (hrel2HV : (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F = hvTauK T Blk F ^ 2)
    (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :=
  letI := blockPS_commGroup Blk
  letI := hvAct T Blk
  kappa0_exists_tame (hv_genK T Blk F) (hrel2HV)
    (blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne)
    (blockHquadK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne)
    (blockHnsK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne)
    (hv_invK T Blk hq0 hqe F l hlne) (blockHsimple T Blk).1 (hv_simple T Blk)

/-- The chosen `H_V`-level base-class datum.  Clone of `GQ2.SectionNine.blockDatHV`
(`GQ2/Block/HeadDat.lean:296`). -/
noncomputable def blockDatHVK (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
    (hrel2HV : (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F = hvTauK T Blk F ^ 2)
    (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    letI := blockPS_commGroup Blk
    FactorSet (HVq T Blk) (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
  (blockKappa0HVK T Blk hq0 hqe F hrel2HV l hlne).choose

omit [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- Clone of `GQ2.SectionNine.blockDatHV_spec` (`GQ2/Block/HeadDat.lean:302`). -/
theorem blockDatHV_specK (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
    (hrel2HV : (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F = hvTauK T Blk F ^ 2)
    (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    letI := blockPS_commGroup Blk
    letI := hvAct T Blk
    IsEquivariantFactorSet
      (blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne)
      (blockDatHVK T Blk hq0 hqe F hrel2HV l hlne) :=
  (blockKappa0HVK T Blk hq0 hqe F hrel2HV l hlne).choose_spec

/-- **The head-inflated block enrichment** at a general residue cardinality.  Clone of
`GQ2.SectionNine.blockEnrichmentD` (`GQ2/Block/HeadDat.lean:318`).  Inhabits the same type as
the model. -/
noncomputable def blockEnrichmentDK (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (hrel2 : (F.alpha (tqSigma q))⁻¹ * F.alpha (tqTau q) * F.alpha (tqSigma q)
      = (F.alpha (tqTau q)) ^ 2)
    (hrel2HV : (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F = hvTauK T Blk F ^ 2) :
    (blockFrame T Blk hE2).Enrichment :=
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := hvAct T Blk
  { blockEnrichmentK T Blk hE2 hq0 hqe F hrel2 with
    dat := fun l h =>
      (blockDatHVK T Blk hq0 hqe F hrel2HV l (fun heq => h (Subtype.ext heq))).reindexHom
        ⇑(blockProjF T Blk)
    hdat := fun l h =>
      IsEquivariantFactorSet.comapHom
        (blockDatHV_specK T Blk hq0 hqe F hrel2HV l (fun heq => h (Subtype.ext heq)))
        (blockProjF T Blk) (blockProjF_compat T Blk) }

omit [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal] in
/-- **The boundary equation's head component** at the `K`-boundary: every boundary lift is
tame-factored at the head through the fixed `F.alpha`.  `rfl`-deep from `IsBoundaryLiftK`.

Generic in the source, so this single declaration replaces the model's two source-specific
twins `boundaryLift_head_gammaA` / `boundaryLift_head_local`
(`GQ2/Block/HeadDat.lean:342,350`). -/
theorem boundaryLift_headK {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {nuP : ContinuousMonoidHom P Ztwo} (hE2 : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F (blockFrame T Blk hE2).TC) (γ : Γ) :
    (blockFrame T Blk hE2).TC.piY (ρ.1.1 γ) = F.alpha (b γ).val.1 :=
  congrArg Prod.fst (ρ.2 γ)

end GQ2.Dyadic
