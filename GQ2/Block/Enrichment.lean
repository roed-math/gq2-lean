/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Block.FormFields

/-!
# §9 concrete block enrichment — `SectionNine.blockEnrichment`

Assembles `(blockFrame T Blk hE2).Enrichment` from the descent (`GQ2/BlockDescent.lean`),
the form fields (`GQ2/BlockFormFields.lean`), and the κ⁰ base-class datum.  Placed in a
separate module (under `namespace SectionNine`, preserving the FQN `SectionNine.blockEnrichment`)
because it consumes `SectionNine.kappa0_exists`/`ActsThroughTame`, so it must sit *downstream* of
`GQ2.SectionNine`.  The two substantive pieces use only the standard axioms:

* `blockHsimple` — `V = P/S` is a simple `𝔽₂[Y/K]`-module (`blockPS_exp2` exp-2 + `Blk.chief`
  under the `W ↦ WP ≤ ↥P ↦ X ≤ Y` subgroup correspondence);
* `blockHtame` — the `Y/K`-action factors through the tame head `H` (`blockLY_smul_eqY` via
  `FoxH.lemma_5_12` ⟹ the action descends `Y/K ↠ Y/L_Y ≅ H`, generators `α σ, α τ`).

`dat`/`hdat` come from `blockKappa0` (= `kappa0_exists`).  The signature takes
`F : BoundaryFrame H E` (`cH := F.alpha`, `hcH := F.alpha_surjective`
for `prop_7_4`, and the tame generators `F.alpha tameSigma/tameTau` for `htame`).
-/

namespace GQ2

namespace SectionNine

open SectionSeven SectionEight QuadraticFp2

open scoped Classical

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
  (cH : ContinuousMonoidHom Ttame H) (hcH : Function.Surjective cH)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]

open FoxH

/-- `L_Y ◁ Y` (the marked normal subgroup), as an instance for `Y ⧸ T.LY`. -/
instance blockLY_normal : (T.LY).Normal := T.normal

/-! ## `hsimple` : `V = P/S` is a simple `𝔽₂[Y/K]`-module -/
omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] [Blk.K.Normal] in
/-- `V = P/S` is **exponent 2**: every element has a `K`-representative `k`, and `k² ∈ R ≤ S`. -/
theorem blockPS_exp2 :
    ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), v + v = 0 := by
  intro v
  obtain ⟨k, hk, hv⟩ := exists_K_rep Blk (Additive.toMul v)
  have hkkS : (k * k : Y) ∈ Blk.S := ((lemma_7_1_head Blk).trans inf_le_right) (blockHsq T Blk k hk)
  have hsq1 : Additive.toMul v * Additive.toMul v = 1 := by
    rw [← hv, mkP_mul Blk (Blk.hKP hk) (Blk.hKP hk), QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hkkS
  show Additive.ofMul (Additive.toMul v * Additive.toMul v) = 0
  rw [hsq1]; rfl

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- `hsimple`: `V = P/S` is a simple `𝔽₂[Y/K]`-module (nontrivial; the only `Y/K`-stable
`AddSubgroup`s are `⊥`/`⊤`, by `Blk.chief` under the subgroup correspondence). -/
theorem blockHsimple :
    letI := blockPS_commGroup Blk
    letI := blockActV Blk
    IsSimpleModTwo (Y ⧸ Blk.K) (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  constructor
  · -- Nontrivial: `S < P` gives `p ∈ P ∖ S`, so `⟦p⟧_S ≠ 1`.
    obtain ⟨p, hpP, hpS⟩ := SetLike.exists_of_lt Blk.hSP
    refine ⟨Additive.ofMul (QuotientGroup.mk ⟨p, hpP⟩), 0, ?_⟩
    intro hcon
    apply hpS
    have : (QuotientGroup.mk ⟨p, hpP⟩ : ↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) = 1 :=
      congrArg Additive.toMul hcon
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    exact this
  · -- chief correspondence: a `Y/K`-stable `W` pulls back to a `Y`-normal `X` with `S ≤ X ≤ P`
    intro W hWstable
    -- `WP ≤ ↥P` = preimage of `W` under `⟦·⟧_S`
    let WP : Subgroup ↥Blk.P :=
      { carrier := {p | Additive.ofMul (QuotientGroup.mk p) ∈ W}
        one_mem' := by
          show Additive.ofMul (QuotientGroup.mk (1 : ↥Blk.P)) ∈ W
          rw [QuotientGroup.mk_one]; exact W.zero_mem
        mul_mem' := fun {a b} ha hb => by
          show Additive.ofMul (QuotientGroup.mk (a * b)) ∈ W
          exact W.add_mem ha hb
        inv_mem' := fun {a} ha => by
          show Additive.ofMul (QuotientGroup.mk a⁻¹) ∈ W
          exact W.neg_mem ha }
    -- push forward to `X ≤ Y`
    set X : Subgroup Y := WP.map Blk.P.subtype with hXdef
    have hSX : Blk.S ≤ X := by
      intro s hs
      have hsP : s ∈ Blk.P := Blk.hSP.le hs
      refine Subgroup.mem_map.mpr ⟨⟨s, hsP⟩, ?_, rfl⟩
      show Additive.ofMul (QuotientGroup.mk (⟨s, hsP⟩ : ↥Blk.P)) ∈ W
      rw [show (QuotientGroup.mk (⟨s, hsP⟩ : ↥Blk.P) : ↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) = 1 from
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hs)]
      exact W.zero_mem
    have hXP : X ≤ Blk.P := by rintro x ⟨p, _, rfl⟩; exact p.2
    have hXN : X.Normal := by
      refine ⟨fun x hx y => ?_⟩
      obtain ⟨p, hpWP, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨conjHom Blk.P Blk.hP y p, ?_, rfl⟩
      show Additive.ofMul (QuotientGroup.mk (conjHom Blk.P Blk.hP y p)) ∈ W
      rw [show Additive.ofMul (QuotientGroup.mk (conjHom Blk.P Blk.hP y p))
          = (QuotientGroup.mk' Blk.K y) • Additive.ofMul (QuotientGroup.mk p) by
        rw [blockActV_mk' Blk y (Additive.ofMul (QuotientGroup.mk p)), blockActVY_mk Blk y p]]
      exact hWstable (QuotientGroup.mk' Blk.K y) _ hpWP
    rcases Blk.chief X hXN hSX hXP with hXS | hXP'
    · -- `X = S` ⟹ `W = ⊥`
      left
      refine (AddSubgroup.eq_bot_iff_forall W).mpr (fun w hw => ?_)
      obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
      have hpW : Additive.ofMul (QuotientGroup.mk p) ∈ W := by
        rwa [hp]
      have hpX : (p : Y) ∈ X := Subgroup.mem_map.mpr ⟨p, hpW, rfl⟩
      rw [hXS] at hpX
      have hmk1 : (QuotientGroup.mk p : ↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hpX)
      have hweq : w = Additive.ofMul (QuotientGroup.mk p) := by rw [hp]; rfl
      rw [hweq, hmk1]; rfl
    · -- `X = P` ⟹ `W = ⊤`
      right
      refine (AddSubgroup.eq_top_iff' W).mpr (fun w => ?_)
      obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
      have hpX : (p : Y) ∈ X := by rw [hXP']; exact p.2
      obtain ⟨p', hp'WP, hp'eq⟩ := Subgroup.mem_map.mp hpX
      have hpWP : Additive.ofMul (QuotientGroup.mk p) ∈ W := by
        rwa [← Subtype.ext hp'eq]
      have hweq : w = Additive.ofMul (QuotientGroup.mk p) := by rw [hp]; rfl
      rw [hweq]; exact hpWP

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
omit [Blk.frattiniK.Normal] in
/-- **`hnt`: the `Y/K`-action on `V = P/S` is nontrivial** — the enrichment-module form of
the block's `nontrivial_action` field.  Only nontriviality is assumed: faithfulness is not
block-derivable (a central
2-part of `Y` outside `K` centralizes `V`), but the capstone only consumed `hfaith` through
`hnt`.)  The moving pair is `(⟦y⟧_K, ⟦p⟧_S)`: `⟦y⟧•⟦p⟧ = ⟦p⟧` would put `y p y⁻¹ p⁻¹ ∈ S`
(conjugating the coset relation by `p`), against `nontrivial_action`. -/
theorem blockHnt :
    letI := blockPS_commGroup Blk
    letI := blockActV Blk
    ∃ (g : Y ⧸ Blk.K) (v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)), g • v ≠ v := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  obtain ⟨y, p, hpP, hys⟩ := Blk.nontrivial_action
  refine ⟨QuotientGroup.mk' Blk.K y,
    Additive.ofMul (QuotientGroup.mk (⟨p, hpP⟩ : ↥Blk.P)), fun hcon => hys ?_⟩
  rw [blockActV_mk' Blk y, blockActVY_mk Blk y ⟨p, hpP⟩] at hcon
  have h2 : (QuotientGroup.mk (conjHom Blk.P Blk.hP y ⟨p, hpP⟩)
      : ↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) = QuotientGroup.mk ⟨p, hpP⟩ :=
    Additive.ofMul.injective hcon
  have h3 : (conjHom Blk.P Blk.hP y ⟨p, hpP⟩)⁻¹ * ⟨p, hpP⟩ ∈ Blk.S.subgroupOf Blk.P :=
    (QuotientGroup.eq (s := Blk.S.subgroupOf Blk.P)).mp h2
  have h4 : (y * p * y⁻¹)⁻¹ * p ∈ Blk.S := Subgroup.mem_subgroupOf.mp h3
  have h5 : p⁻¹ * (y * p * y⁻¹) ∈ Blk.S := by
    have h5' := Blk.S.inv_mem h4
    have heq : ((y * p * y⁻¹)⁻¹ * p)⁻¹ = p⁻¹ * (y * p * y⁻¹) := by group
    rwa [heq] at h5'
  have h6 := Blk.hS.conj_mem _ h5 p
  have heq : p * (p⁻¹ * (y * p * y⁻¹)) * p⁻¹ = y * p * y⁻¹ * p⁻¹ := by group
  rwa [heq] at h6

/-! ## `htame` : the `Y/K`-action factors through the tame head `H` -/

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- **`L_Y` acts trivially on `V`**: `L_Y/K` is a normal 2-subgroup of `Y/K` acting on the simple
module `V`, hence trivial by `FoxH.lemma_5_12`; pull back to the `Y`-conjugation action. -/
theorem blockLY_smul_eqY (l : Y) (hl : l ∈ T.LY) :
    letI := blockActVY Blk
    ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), l • v = v := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  intro v
  have h512 := FoxH.lemma_5_12 (blockPS_exp2 T Blk) (blockHsimple T Blk)
    ((T.LY).map (QuotientGroup.mk' Blk.K))
    (T.normal.map (QuotientGroup.mk' Blk.K) (QuotientGroup.mk'_surjective Blk.K))
    (T.isPGroup_two.map _)
    (QuotientGroup.mk' Blk.K l) (Subgroup.mem_map_of_mem _ hl) v
  rwa [← blockActV_mk' Blk l v]

/-- **The descended `Y/L_Y`-action on `V`** — `blockActVY` descends because `L_Y` acts trivially
(`blockLY_smul_eqY`); mirrors `blockActV`'s descent through `Y/K`. -/
@[reducible] noncomputable def blockActLY :
    letI := blockPS_commGroup Blk
    DistribMulAction (Y ⧸ T.LY) (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  { smul := fun yb v => Quotient.liftOn' yb (fun y => (y : Y) • v) (by
      intro y₁ y₂ h
      have htriv : (y₁⁻¹ * y₂) • v = v :=
        blockLY_smul_eqY T Blk (y₁⁻¹ * y₂) (QuotientGroup.leftRel_apply.mp h) v
      rw [← mul_inv_cancel_left y₁ y₂, mul_smul, htriv])
    one_smul := fun v => one_smul Y v
    mul_smul := fun yb1 yb2 v => by
      induction yb1 using QuotientGroup.induction_on with | _ y₁ =>
      induction yb2 using QuotientGroup.induction_on with | _ y₂ =>
      exact mul_smul y₁ y₂ v
    smul_zero := fun yb => by
      induction yb using QuotientGroup.induction_on with | _ y =>
      exact smul_zero y
    smul_add := fun yb a b => by
      induction yb using QuotientGroup.induction_on with | _ y =>
      exact smul_add y a b }

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E]
  [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- `Y/L_Y`-action on `mk' L_Y y` reduces to the `Y`-conjugation action of `y`. -/
theorem blockActLY_mk' (y : Y) (v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :
    letI := blockActLY T Blk; letI := blockActVY Blk
    (QuotientGroup.mk' T.LY y) • v = y • v := rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] in
/-- `htame`: the `Y/K`-action on `V` factors through the tame head `H` (`α : Ttame ↠ H`);
the action descends `Y/K ↠ Y/L_Y ≅ H`, generators `α σ, α τ` satisfy the tame relation. -/
theorem blockHtame (F : BoundaryFrame H E) :
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
    F.alpha tameSigma, F.alpha tameTau, ?_, ?_, ?_, ?_⟩
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
    exact GQ2.SectionThree.gen_ttame_quotient F.alpha.toMonoidHom F.alpha.continuous_toFun
      F.alpha_surjective
  · -- tame relation
    have h := congrArg (⇑F.alpha) tame_relation
    rwa [conjP, map_mul, map_mul, map_inv, map_pow] at h

/-! ## `dat`/`hdat` and the final assembly -/

/-- The κ⁰ base-class datum for `q̄_λ`, from the proved `kappa0_exists` (Lemma 6.3),
discharging its `hsimple`/`htame` hypotheses via `blockHsimple`/`blockHtame`. -/
noncomputable def blockKappa0 (F : BoundaryFrame H E) (l : BlockDR T Blk)
    (hlne : l.1 ≠ Blk.frattiniK) :=
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  kappa0_exists (blockQbar T Blk F.alpha F.alpha_surjective l hlne)
    (blockHquad T Blk F.alpha F.alpha_surjective l hlne)
    (blockHns T Blk F.alpha F.alpha_surjective l hlne)
    (blockHinv T Blk F.alpha F.alpha_surjective l hlne)
    (blockHsimple T Blk) (blockHtame T Blk F)

/-- **The concrete block enrichment** (the §9 induction): the full `RF.Enrichment` record assembled from
the §9 induction descent (`blockDescend*`/`blockActV`), the §9 induction form fields
(`blockQ`/`blockQbar`/…), and the κ⁰ datum (`blockKappa0`).  Takes the boundary frame `F`
(supplying `cH := F.alpha` for `prop_7_4` and the tame generators for `htame`).  Axiom-clean
modulo `kappa0_exists` (the §9 induction). -/
noncomputable def blockEnrichment (F : BoundaryFrame H E) : (blockFrame T Blk hE2).Enrichment := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  exact
    { q := fun l h => blockQ T Blk F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hq := fun l h =>
        blockHq T Blk hE2 F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hrad := fun l h =>
        blockHrad T Blk F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hTzero := fun l h =>
        blockHTzero T Blk F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
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
        blockQbar T Blk F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hqbar := fun l h =>
        blockHqbar T Blk F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hquad := fun l h =>
        blockHquad T Blk F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hns := fun l h => blockHns T Blk F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      hinv := fun l h =>
        blockHinv T Blk F.alpha F.alpha_surjective l (fun heq => h (Subtype.ext heq))
      dat := fun l h => (blockKappa0 T Blk F l (fun heq => h (Subtype.ext heq))).choose
      hdat := fun l h => (blockKappa0 T Blk F l (fun heq => h (Subtype.ext heq))).choose_spec }

end SectionNine

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 6.3 = ⟦lem-basedetclass⟧
-/
