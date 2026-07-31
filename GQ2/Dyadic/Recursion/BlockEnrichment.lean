/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.BlockFormFields
import GQ2.Dyadic.Recursion.Block
import GQ2.Block.Enrichment

/-!
# The concrete block enrichment at a general residue cardinality (ticket SD-R1)

Clone of the `F.alpha`-consuming tier of `GQ2/Block/Enrichment.lean` (340 ln), re-typed at
F3's `Tq q`: `blockHtameK`, `blockKappa0K`, `blockEnrichmentK`.

## What is reused rather than cloned

Everything in the model that never touches the frame is consumed by import, unchanged:
`blockLY_normal` (:45), `blockPS_exp2` (:51), `blockHsimple` (:66), `blockHnt` (:150),
`blockLY_smul_eqY` (:181), `blockActLY` (:197), `blockActLY_mk'` (:222).  `blockFrame` and
`RecursionFrame.Enrichment` are likewise the model's, so `blockEnrichmentK` inhabits **the same
type** as `blockEnrichment` — no transport is ever needed between the two spines.

## ⚠ SEAM B, threaded — an SD-R2 obligation (dated 2026-07-31)

`GQ2.SectionNine.ActsThroughTame` (`GQ2/SectionNine/Induction.lean:155`) embeds the exponent-2
tame relation `s⁻¹ * t * s = t ^ 2` **in its definition** (:160), and `kappa0_exists` (:196)
forwards it to `GQ2.kappa0_exists_tame` (`GQ2/KappaNormalForm.lean:1150`), whose signature
demands the same.  At a general residue cardinality the head's tame pair satisfies `= t ^ q`
(proved: `GQ2.Dyadic.hv_relK`, `GQ2/Dyadic/Recursion/Block.lean`), so the exponent-2 clause is
**not available** and is threaded here as the explicit hypothesis

```
hrel2 : (F.alpha (tqSigma q))⁻¹ * F.alpha (tqTau q) * F.alpha (tqSigma q)
          = (F.alpha (tqTau q)) ^ 2
```

on `blockHtameK`, `blockKappa0K` and `blockEnrichmentK`.

**SD-R2 owns the fix** (`Induction.lean` is in its scope): generalize `ActsThroughTame`'s
relation clause to `t ^ q` under `q ≠ 0`/`Even q` — and correspondingly `kappa0_exists` and
`GQ2.kappa0_exists_tame`.  When that lands, `hrel2` is discharged by `tame_rel_map_q` (and, at
the `H_V` level, by `hv_relK`) and the binder disappears from all three declarations below; no
other change is needed here.

At `q = 2` the binder is **free**: `GQ2.Dyadic.tame_rel_map_q F.alpha.toMonoidHom` has exactly
this type, since `^ q` *is* `^ 2` there.  Verified in-session:

```lean
noncomputable example (F : BoundaryFrameK 2 P H E) : (blockFrame T Blk hE2).Enrichment :=
  blockEnrichmentK T Blk hE2 (by norm_num) (by decide) F (tame_rel_map_q F.alpha.toMonoidHom)
```

so the `n = 1` regression is unaffected by this seam.

⚠ Note for whoever discharges it (from the adopted depth assessment):
`GQ2.Dyadic.lemma_6_11_of_tame_pair_pow` is stated at `q = 2^f` with `1 ≤ f`, **not** at
`Even q ∧ q ≠ 0`.  If the §6.11 entry point is needed, use the two general-`q` leaves
`tame_odd_order_pow` / `tame_zpowers_normal_pow` (`GQ2/Dyadic/Projectivity.lean`) with
`lemma_6_11_of_odd_normal` directly.

Axioms: none beyond std-3; each clone's print equals its model's.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionSeven GQ2.SectionEight GQ2.SectionNine QuadraticFp2 FoxH

open scoped Classical

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
variable {q : ℕ} {P : ProfiniteGrp}

omit [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- `htame` at a general residue cardinality.  Clone of `GQ2.SectionNine.blockHtame`
(`GQ2/Block/Enrichment.lean:229`) with `α : T_q ↠ H`; the exponent-2 tame clause is the
threaded `hrel2` (SEAM B — see the module docstring). -/
theorem blockHtameK (F : BoundaryFrameK q P H E)
    (hrel2 : (F.alpha (tqSigma q))⁻¹ * F.alpha (tqTau q) * F.alpha (tqSigma q)
      = (F.alpha (tqTau q)) ^ 2) :
    letI := blockPS_commGroup Blk
    letI := blockActV Blk
    ActsThroughTame (Y ⧸ Blk.K) (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := blockActLY T Blk
  -- the head iso `e : Y/L_Y ≃* H` (descend `T.piY`)
  have hLYker : T.LY ≤ T.piY.ker := le_of_eq T.ker_piY.symm
  let d : (Y ⧸ T.LY) →* H := QuotientGroup.lift T.LY T.piY hLYker
  have hd_mk : ∀ y : Y, d (QuotientGroup.mk' T.LY y) = T.piY y :=
    fun y => QuotientGroup.lift_mk' _ _ _
  have hdsurj : Function.Surjective d := by
    intro h; obtain ⟨y, hy⟩ := T.piY_surjective h
    exact ⟨QuotientGroup.mk' T.LY y, by rwa [hd_mk]⟩
  have hdinj : Function.Injective d := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective T.LY x
    rw [hd_mk] at hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← T.ker_piY]
  let e : (Y ⧸ T.LY) ≃* H := MulEquiv.ofBijective d ⟨hdinj, hdsurj⟩
  have he_mk : ∀ y : Y, e (QuotientGroup.mk' T.LY y) = T.piY y := hd_mk
  -- the head action (transport `blockActLY` along `e`) and `π`
  letI actH : DistribMulAction H (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
    DistribMulAction.compHom _ e.symm.toMonoidHom
  have hKker : Blk.K ≤ T.piY.ker := by rw [T.ker_piY]; exact Blk.hKP.trans Blk.hPL
  let piKH : (Y ⧸ Blk.K) →* H := QuotientGroup.lift Blk.K T.piY hKker
  have hpiKH_mk : ∀ y : Y, piKH (QuotientGroup.mk' Blk.K y) = T.piY y :=
    fun y => QuotientGroup.lift_mk' _ _ _
  refine ⟨H, inferInstance, inferInstance, actH, piKH,
    F.alpha (tqSigma q), F.alpha (tqTau q), ?_, ?_, ?_, ?_⟩
  · -- `π` surjective
    intro h; obtain ⟨y, hy⟩ := T.piY_surjective h
    exact ⟨QuotientGroup.mk' Blk.K y, by rwa [hpiKH_mk]⟩
  · -- compatibility `c • v = π c • v`
    intro c v
    induction c using QuotientGroup.induction_on with | _ y =>
    show (QuotientGroup.mk' Blk.K y) • v
      = e.symm (piKH (QuotientGroup.mk' Blk.K y)) • v
    rw [blockActV_mk' Blk y v, hpiKH_mk y,
      show T.piY y = e (QuotientGroup.mk' T.LY y) from (he_mk y).symm, e.symm_apply_apply,
      blockActLY_mk' T Blk y v]
  · -- generation
    exact GQ2.Dyadic.gen_tq_quotient F.alpha.toMonoidHom F.alpha.continuous_toFun
      F.alpha_surjective
  · -- tame relation: SEAM B.  `ActsThroughTame` demands the exponent-2 shape, which the
    -- `K`-side head does not satisfy at `q ≠ 2`; threaded as `hrel2` until SD-R2 generalizes
    -- the definition.  `hv_relK` (GQ2/Dyadic/Recursion/Block.lean) proves the `^ q` producer.
    exact hrel2

/-- The κ⁰ base-class datum at a general residue cardinality.  Clone of
`GQ2.SectionNine.blockKappa0` (`GQ2/Block/Enrichment.lean:284`). -/
noncomputable def blockKappa0K (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
    (hrel2 : (F.alpha (tqSigma q))⁻¹ * F.alpha (tqTau q) * F.alpha (tqSigma q)
      = (F.alpha (tqTau q)) ^ 2)
    (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :=
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  kappa0_exists (blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne)
    (blockHquadK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne)
    (blockHnsK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne)
    (blockHinvK T Blk hq0 hqe F.alpha F.alpha_surjective l hlne)
    (blockHsimple T Blk) (blockHtameK T Blk F hrel2)

/-- **The concrete block enrichment at a general residue cardinality**.  Clone of
`GQ2.SectionNine.blockEnrichment` (`GQ2/Block/Enrichment.lean:300`).  Inhabits **the same type**
as the model, since `blockFrame` and `Enrichment` are boundary-free and reused. -/
noncomputable def blockEnrichmentK (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
    (hrel2 : (F.alpha (tqSigma q))⁻¹ * F.alpha (tqTau q) * F.alpha (tqSigma q)
      = (F.alpha (tqTau q)) ^ 2) :
    (blockFrame T Blk hE2).Enrichment := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  exact
    { q := fun l h => blockQK T Blk hq0 hqe F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hq := fun l h =>
        blockHqK T Blk hE2 hq0 hqe F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hrad := fun l h =>
        blockHradK T Blk hq0 hqe F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hTzero := fun l h =>
        blockHTzeroK T Blk hq0 hqe F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      Vmod := Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)
      addV := inferInstance
      finV := inferInstance
      actV := blockActV Blk
      descend := blockDescend Blk
      descend_surj := blockDescend_surjective Blk
      descend_ker := blockDescend_ker Blk
      descend_conj := fun bb m hm =>
        (congrArg Multiplicative.ofAdd (blockDescend_conj Blk bb m hm)).symm
      qbar := fun l h =>
        blockQbarK T Blk hq0 hqe F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hqbar := fun l h =>
        blockHqbarK T Blk hq0 hqe F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hquad := fun l h =>
        blockHquadK T Blk hq0 hqe F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hns := fun l h => blockHnsK T Blk hq0 hqe F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hinv := fun l h =>
        blockHinvK T Blk hq0 hqe F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      dat := fun l h => (blockKappa0K T Blk hq0 hqe F hrel2 l (fun heq => h (Subtype.ext heq))).choose
      hdat := fun l h => (blockKappa0K T Blk hq0 hqe F hrel2 l (fun heq => h (Subtype.ext heq))).choose_spec }

end GQ2.Dyadic
