/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Recursion
import GQ2.Block.HeadDat

/-!
# The `K`-side block tame pair — and the two seams that stop here (ticket SD-R1)

This file lands the part of the SD1 memo's "Block trio" (`GQ2/Block/Enrichment.lean` 340 ln,
`GQ2/Block/HeadDat.lean` 370 ln, `GQ2/Block/RStage.lean` 449 ln) that is genuinely clonable at
the `K`-boundary, and **documents precisely where the clone stops**.  Read the seam sections
before extending it: the blockers are not in this file's scope, and SD-R1's brief is to report
them rather than to work around them.

## What is reused rather than cloned (the majority of all three files)

Boundary-free, hence consumed by import — no clone needed:

* `Enrichment.lean`: `blockLY_normal`, `blockPS_exp2` (:51), `blockHsimple` (:66), `blockHnt`
  (:150), `blockLY_smul_eqY` (:181), `blockActLY` (:197), `blockActLY_mk'` (:222).
* `HeadDat.lean`: `headEquiv` (:55), `headAct` (:81), `blockPiCH` (:89), `blockPiCH_compat`
  (:110), `headActKer` (:132), `headActKer_normal`, `HVq` (:149), `hvAct` (:152),
  `hvAct_faithful` (:178), `blockProjF` (:192), `blockProjF_compat` (:203), `hv_simple` (:267),
  `blockPiCH_eq_TC_piY` (:359).
* `RStage.lean`: everything up to and including `blockRObstructionData` (:38-~307) —
  `blockRCoverData`, `RCharSub`, `RCharKerSub`, `RCharMulHom`, `RCharKer`, and the obstruction
  datum itself.

Together with the `RecursionFrame`/`Enrichment` finding recorded in
`GQ2/Dyadic/Recursion/Recursion.lean`, this means the *target-side* half of the §8/§9 block
apparatus needs no degree-`n` copy at all.

## What this file clones

The tame pair in the faithful head quotient `H_V`, re-typed at `Tq q`: `hvSigmaK`, `hvTauK`,
`hv_genK`, `hv_relK`.  These are the exact inputs the κ⁰ existential wants, so landing them now
pins the interface for whoever discharges the seams below.

Note `hv_relK` proves the **`q`-th power** relation `s⁻¹ t s = t ^ q` — the true statement at a
general residue cardinality, and (since SD-R2) exactly what the §6 entry point
`GQ2.Dyadic.kappa0_exists_tameK` accepts.

## ⚠ SEAM A — §7 `prop_7_4` is typed at `Ttame`  (blocks `blockEnrichment`)

`GQ2.SectionSeven.prop_7_4` (`GQ2/SectionSeven/Prop74.lean:307`) takes
`cH : ContinuousMonoidHom Ttame H`, and the `Block/FormFields.lean` layer built on it
(`blockProp74` :77, `blockQ`, `blockQbar`, `blockHquad`, `blockHns`, `blockHinv`, …) inherits
that type.  A `K`-frame supplies `F.alpha : ContinuousMonoidHom (Tq q) H`.  Verbatim error:

```
error: Application type mismatch: The argument
  F.alpha
has type
  ↑(Tq q).toProfinite.toTop →ₜ* H
but is expected to have type
  ↑Ttame.toProfinite.toTop →ₜ* H
in the application
  blockQ T Blk F.alpha
```

Inside `prop_7_4` the `Ttame` typing is used at `Prop74.lean:101-108` for generation
(`SectionThree.gen_ttame_quotient`), the relation (`tame_relation`), and oddness of
`orderOf (cH tameTau)` (`Tame.tame_odd_order`).  F3 exports the general-`q` counterparts
(`gen_tq_quotient`, `tame_relation_q`, `TameQ.odd_order` — the last under `q ≠ 0`, `Even q`),
so the obstruction is a *typing and hypothesis-threading* obstruction, not an absent theorem.

## SEAM B — DISCHARGED by SD-R2 (`GQ2/Dyadic/Recursion/Kappa.lean`)

SD-R1 reported that `GQ2.SectionNine.ActsThroughTame` (`GQ2/SectionNine/Induction.lean:155`)
carries `s⁻¹ * t * s = t ^ 2` **literally in its definition** (:160) and forwards it to
`GQ2.kappa0_exists_tame` (`GQ2/KappaNormalForm.lean:1150`), so no `K`-side head could meet it
at `q ≠ 2`.  SD-R2 supplied the general-`q` predicate `ActsThroughTameQ q` and the clones
`kappa0_exists_tameK` / `kappa0_existsK` (the frozen `ℚ₂` definitions untouched), and the six
threaded binders are gone from `blockHtameK`, `blockKappa0K`, `blockEnrichmentK`,
`blockKappa0HVK`, `blockDatHVK` and `blockEnrichmentDK`.  `hv_relK` below is the `H_V`-level
producer they consume.

## ⏸ `Block/RStage.lean`'s three `b`-typed theorems are an SD-R3 dependency, not a seam

`blockStageR136` (:341), `hsep_hom_of_splitCriterion` (:372) and
`blockStageR136_ofSplitCriterion` (:415) are `b`-typed but reduce to
`GQ2.stageR136_ofRSepData` (`GQ2/RStage/ObstructionBuild.lean:731`), which lives in the
`RStage/Obstruction`+`ObstructionBuild` pair the memo's §4.3 table assigns to **SD-R3**.  They
are therefore deferred on dependency order, not blocked mathematically: SD-R3 should clone them
alongside its own `RStage` files rather than leaving them to a later pass.

Axioms: none beyond std-3; each clone's print equals its model's.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionNine GQ2.SectionSeven

open scoped Classical

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
variable {q : ℕ} {P : ProfiniteGrp}
variable (F : BoundaryFrameK q P H E)

/-! ## The tame pair in the faithful head quotient `H_V`, at `T_q`

`HVq`, `headActKer` and `hvAct` are the model's (`GQ2/Block/HeadDat.lean:132,149,152`) — they
are boundary-free.  Only the two *generators* move, from `F.alpha tameSigma/tameTau` to
`F.alpha (tqSigma q)/(tqTau q)`. -/

/-- The `σ`-generator of the tame pair in `H_V`.  Clone of `GQ2.SectionNine.hvSigma`
(`GQ2/Block/HeadDat.lean:223`) with `tameSigma` replaced by `tqSigma q`. -/
noncomputable def hvSigmaK : HVq T Blk :=
  QuotientGroup.mk' (headActKer T Blk) (F.alpha (tqSigma q))

/-- The `τ`-generator of the tame pair in `H_V`.  Clone of `GQ2.SectionNine.hvTau`
(`GQ2/Block/HeadDat.lean:227`) with `tameTau` replaced by `tqTau q`. -/
noncomputable def hvTauK : HVq T Blk :=
  QuotientGroup.mk' (headActKer T Blk) (F.alpha (tqTau q))

omit [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- `H_V` is generated by the tame pair.  Clone of `GQ2.SectionNine.hv_gen`
(`GQ2/Block/HeadDat.lean:232`) — verbatim, with F3's `gen_tq_quotient` in place of
`SectionThree.gen_ttame_quotient`. -/
theorem hv_genK : Subgroup.closure {hvSigmaK T Blk F, hvTauK T Blk F} = ⊤ := by
  have hH : Subgroup.closure {F.alpha (tqSigma q), F.alpha (tqTau q)} = ⊤ :=
    gen_tq_quotient F.alpha.toMonoidHom F.alpha.continuous_toFun F.alpha_surjective
  have hmap := congrArg (Subgroup.map (QuotientGroup.mk' (headActKer T Blk))) hH
  rwa [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _), Set.image_pair] at hmap

omit [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- The tame relation in `H_V` **at the general residue cardinality**: `s⁻¹ t s = t ^ q`.
Clone of `GQ2.SectionNine.hv_rel` (`GQ2/Block/HeadDat.lean:242`) — verbatim, with F3's
`tame_relation_q` in place of `tame_relation`.

This is the statement SEAM B turned on: the model's conclusion is `t ^ 2`.  Since SD-R2 the
`K`-side §6 consumers (`ActsThroughTameQ`, `kappa0_existsK`, `kappa0_exists_tameK`) are written
against `t ^ q`, and this theorem is the `H_V`-level producer they take.  See the module
docstring. -/
theorem hv_relK :
    (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F = hvTauK T Blk F ^ q := by
  have h := congrArg (⇑F.alpha) (tame_relation_q q)
  rw [conjP, map_mul, map_mul, map_inv, map_pow] at h
  have h2 := congrArg (⇑(QuotientGroup.mk' (headActKer T Blk))) h
  rwa [map_mul, map_mul, map_inv, map_pow] at h2

/-! ## The `n = 1` refl-bridges -/

omit [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- At `n = 1` the `σ`-generator **is** the model's — `rfl`. -/
theorem hvSigmaK_eq (F : BoundaryFrameK 2 PiBd H E) :
    hvSigmaK T Blk F = hvSigma T Blk F.toBoundaryFrame := rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- At `n = 1` the `τ`-generator **is** the model's — `rfl`. -/
theorem hvTauK_eq (F : BoundaryFrameK 2 PiBd H E) :
    hvTauK T Blk F = hvTau T Blk F.toBoundaryFrame := rfl

end GQ2.Dyadic
