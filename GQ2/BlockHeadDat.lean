import GQ2.BlockEnrichment
import GQ2.ShapiroDeepness

/-!
# P-16d6e4aA-P4b — the head-inflated block enrichment (`blockEnrichmentD`)

Substrate for the c3-G0 **head-inflation reshape** (`docs/p16d6e4aA-p4-tame-package.md`,
authoritative; the frozen `TamePackage`/`hpack` shape is refuted there).  This leaf builds:

* the head identification `headEquiv : Y⧸L_Y ≃* H` and the `H`-action on `V = P/S`
  (`headAct`, the `blockHtame` construction as *data*), with the C-head `blockPiCH : Y⧸K →* H`
  and the compatibility `c • v = blockPiCH c • v`;
* the **faithful head quotient** `HVq := H ⧸ headActKer` with its descended action (`hvAct`),
  faithfulness *by construction* (`hvAct_faithful`), and the full projection
  `blockProjF : Y⧸K →* HVq`;
* the tame pair `hvSigma/hvTau` (classes of `α σ, α τ`) with generation and the tame relation,
  the invariance/simplicity transports, and the `H_V`-level κ⁰ datum
  `blockDatHV := (kappa0_exists_tame …).choose`;
* **`blockEnrichmentD`** — `blockEnrichment` with `dat := (blockDatHV).reindexHom blockProjF`
  (definitionally transparent: `blockEnrichmentD_dat_eq` is `rfl`), so every
  `QZero`/`Q0loc` evaluation transports down `graphPullback_reindexHom`/`Q0loc_reindexHom`
  to `C := HVq`, where every boundary lift is tame-factored through the *fixed*
  `mk' ∘ F.alpha` (the boundary equation's head component, `boundaryLift_head_*`), `hfaith`
  holds by construction, and the wild slots are literally `1`;
* the boundary-equation head components `boundaryLift_head_gammaA`/`boundaryLift_head_local`
  (the per-lift tame factorization at the head — `rfl`-level from `IsBoundaryLift`).

Everything here is std-3 (no sorries; `kappa0_exists_tame` is the landed P-17e5 theorem).
Consumers: P4c (local residue twins at `blockEnrichmentD`), P4d (`Γ_A` twins), P4e (the
hypothesis-free G0-obtain), P5 (the ThmFourTwo `En`-swap).
-/

namespace GQ2

namespace SectionNine

open SectionSeven SectionEight QuadraticFp2

open scoped Classical

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY)
variable [Blk.R.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]

/-! ## The head action as data (the `blockHtame` construction, unpacked) -/

/-- The head identification `Y ⧸ L_Y ≃* H`: `π_Y` descends with kernel exactly `L_Y`. -/
noncomputable def headEquiv : (Y ⧸ T.LY) ≃* H :=
  MulEquiv.ofBijective (QuotientGroup.lift T.LY T.piY (le_of_eq T.ker_piY.symm))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective T.LY x
      rw [show QuotientGroup.lift T.LY T.piY (le_of_eq T.ker_piY.symm)
          (QuotientGroup.mk' T.LY y) = T.piY y from QuotientGroup.lift_mk' _ _ _] at hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← T.ker_piY]
      exact hx,
    fun h => by
      obtain ⟨y, hy⟩ := T.piY_surjective h
      refine ⟨QuotientGroup.mk' T.LY y, ?_⟩
      rw [show QuotientGroup.lift T.LY T.piY (le_of_eq T.ker_piY.symm)
          (QuotientGroup.mk' T.LY y) = T.piY y from QuotientGroup.lift_mk' _ _ _]
      exact hy⟩

@[simp] theorem headEquiv_mk (y : Y) :
    headEquiv T (QuotientGroup.mk' T.LY y) = T.piY y :=
  show QuotientGroup.lift T.LY T.piY (le_of_eq T.ker_piY.symm)
      (QuotientGroup.mk' T.LY y) = T.piY y from QuotientGroup.lift_mk' _ _ _

/-- The `H`-action on `V = P/S`: the `Y⧸L_Y`-conjugation action (`blockActLY`) transported
along `headEquiv.symm`. -/
@[reducible] noncomputable def headAct :
    letI := blockPS_commGroup Blk
    DistribMulAction H (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
  letI := blockPS_commGroup Blk
  letI := blockActLY T Blk
  DistribMulAction.compHom _ (headEquiv T).symm.toMonoidHom

/-- The C-target's head map `Y⧸K →* H` (defeq to `(blockFrame T Blk hE2).TC.piY`). -/
noncomputable def blockPiCH : (Y ⧸ Blk.K) →* H :=
  QuotientGroup.lift Blk.K T.piY (by rw [T.ker_piY]; exact Blk.hKP.trans Blk.hPL)

@[simp] theorem blockPiCH_mk (y : Y) :
    blockPiCH T Blk (QuotientGroup.mk' Blk.K y) = T.piY y :=
  QuotientGroup.lift_mk' _ _ _

theorem blockPiCH_surjective : Function.Surjective (blockPiCH T Blk) := fun h => by
  obtain ⟨y, hy⟩ := T.piY_surjective h
  exact ⟨QuotientGroup.mk' Blk.K y, (blockPiCH_mk T Blk y).trans hy⟩

/-- The `Y⧸K`-action on `V` is the `blockPiCH`-pullback of the `H`-action (the `blockHtame`
compatibility clause, as a standalone fact). -/
theorem blockPiCH_compat :
    letI := blockPS_commGroup Blk
    letI := blockActV Blk
    letI := headAct T Blk
    ∀ (c : Y ⧸ Blk.K) (v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)),
      c • v = blockPiCH T Blk c • v := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := blockActLY T Blk
  letI := headAct T Blk
  intro c v
  induction c using QuotientGroup.induction_on with | _ y =>
  show (QuotientGroup.mk' Blk.K y) • v
    = (headEquiv T).symm (blockPiCH T Blk (QuotientGroup.mk' Blk.K y)) • v
  rw [blockActV_mk' Blk y v, blockPiCH_mk T Blk y,
    show T.piY y = headEquiv T (QuotientGroup.mk' T.LY y) from (headEquiv_mk T y).symm,
    (headEquiv T).symm_apply_apply]
  exact (blockActLY_mk' T Blk y v).symm

/-! ## The faithful head quotient `H_V` -/

/-- The kernel of the `H`-action on `V` (the acts-trivially subgroup). -/
noncomputable def headActKer : Subgroup H :=
  letI := blockPS_commGroup Blk
  letI := headAct T Blk
  { carrier := {h : H | ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), h • v = v}
    one_mem' := fun v => one_smul H v
    mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
    inv_mem' := fun {a} ha v => by
      conv_lhs => rw [← ha v]
      rw [← mul_smul, inv_mul_cancel, one_smul] }

instance headActKer_normal : (headActKer T Blk).Normal := by
  letI := blockPS_commGroup Blk
  letI := headAct T Blk
  refine ⟨fun h hh g => ?_⟩
  intro v
  rw [mul_smul, mul_smul, hh (g⁻¹ • v), ← mul_smul, mul_inv_cancel, one_smul]

/-- The faithful head quotient `H_V := H ⧸ ker(action)`. -/
abbrev HVq := H ⧸ headActKer T Blk

/-- The descended (faithful) `H_V`-action on `V`. -/
@[reducible] noncomputable def hvAct :
    letI := blockPS_commGroup Blk
    DistribMulAction (HVq T Blk) (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
  letI := blockPS_commGroup Blk
  letI := headAct T Blk
  { smul := fun hb v => Quotient.liftOn' hb (fun h => h • v) (by
      intro h₁ h₂ hrel
      have hmem : h₁⁻¹ * h₂ ∈ headActKer T Blk := QuotientGroup.leftRel_apply.mp hrel
      have htriv : (h₁⁻¹ * h₂) • v = v := hmem v
      calc h₁ • v = h₁ • ((h₁⁻¹ * h₂) • v) := by rw [htriv]
        _ = (h₁ * (h₁⁻¹ * h₂)) • v := (mul_smul _ _ _).symm
        _ = h₂ • v := by rw [mul_inv_cancel_left])
    one_smul := fun v => one_smul H v
    mul_smul := fun a b v => by
      induction a using QuotientGroup.induction_on with | _ h₁ =>
      induction b using QuotientGroup.induction_on with | _ h₂ =>
      exact mul_smul h₁ h₂ v
    smul_zero := fun a => by
      induction a using QuotientGroup.induction_on with | _ h =>
      exact smul_zero h
    smul_add := fun a x y => by
      induction a using QuotientGroup.induction_on with | _ h =>
      exact smul_add h x y }

theorem hvAct_mk (h : H) (v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :
    letI := blockPS_commGroup Blk
    letI := headAct T Blk
    letI := hvAct T Blk
    (QuotientGroup.mk' (headActKer T Blk) h) • v = h • v := rfl

/-- **Faithfulness by construction**: the `H_V`-action on `V` is faithful — the `hfaith`
input of the local residue chain, free at the faithful head quotient. -/
theorem hvAct_faithful :
    letI := blockPS_commGroup Blk
    letI := hvAct T Blk
    ∀ g : HVq T Blk,
      (∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), g • v = v) → g = 1 := by
  letI := blockPS_commGroup Blk
  letI := headAct T Blk
  letI := hvAct T Blk
  intro g hg
  induction g using QuotientGroup.induction_on with | _ h =>
  rw [QuotientGroup.eq_one_iff]
  exact fun v => hg v

/-- The full projection `Y⧸K →* H_V` (head, then faithful quotient). -/
noncomputable def blockProjF : (Y ⧸ Blk.K) →* HVq T Blk :=
  (QuotientGroup.mk' (headActKer T Blk)).comp (blockPiCH T Blk)

theorem blockProjF_surjective : Function.Surjective (blockProjF T Blk) :=
  (QuotientGroup.mk'_surjective _).comp (blockPiCH_surjective T Blk)

/-- The `Y⧸K`-action on `V` is the `blockProjF`-pullback of the faithful `H_V`-action. -/
theorem blockProjF_compat :
    letI := blockPS_commGroup Blk
    letI := blockActV Blk
    letI := hvAct T Blk
    ∀ (c : Y ⧸ Blk.K) (v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)),
      c • v = blockProjF T Blk c • v := by
  letI := blockPS_commGroup Blk
  letI := blockActV Blk
  letI := headAct T Blk
  letI := hvAct T Blk
  intro c v
  rw [blockPiCH_compat T Blk c v]
  rfl

/-! ## The tame pair in `H_V` and the transports -/

section TamePair

variable (F : BoundaryFrame H E)

/-- The `σ`-generator of the tame pair in `H_V`: the class of `α(tameSigma)`. -/
noncomputable def hvSigma : HVq T Blk :=
  QuotientGroup.mk' (headActKer T Blk) (F.alpha tameSigma)

/-- The `τ`-generator of the tame pair in `H_V`: the class of `α(tameTau)`. -/
noncomputable def hvTau : HVq T Blk :=
  QuotientGroup.mk' (headActKer T Blk) (F.alpha tameTau)

/-- `H_V` is generated by the tame pair (image of `gen_ttame_quotient` at `F.alpha`). -/
theorem hv_gen : Subgroup.closure {hvSigma T Blk F, hvTau T Blk F} = ⊤ := by
  have hH : Subgroup.closure {F.alpha tameSigma, F.alpha tameTau} = ⊤ :=
    GQ2.SectionThree.gen_ttame_quotient F.alpha.toMonoidHom F.alpha.continuous_toFun
      F.alpha_surjective
  have hmap := congrArg (Subgroup.map (QuotientGroup.mk' (headActKer T Blk))) hH
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)] at hmap
  rw [show (QuotientGroup.mk' (headActKer T Blk)) ''
      {F.alpha tameSigma, F.alpha tameTau} = {hvSigma T Blk F, hvTau T Blk F} from by
    rw [Set.image_pair]; rfl] at hmap
  exact hmap

/-- The tame relation in `H_V` (image of `tame_relation` through `α` and the quotient). -/
theorem hv_rel :
    (hvSigma T Blk F)⁻¹ * hvTau T Blk F * hvSigma T Blk F = hvTau T Blk F ^ 2 := by
  have h := congrArg (⇑F.alpha) tame_relation
  rw [conjP, map_mul, map_mul, map_inv, map_pow] at h
  have h2 := congrArg (⇑(QuotientGroup.mk' (headActKer T Blk))) h
  rw [map_mul, map_mul, map_inv, map_pow] at h2
  exact h2

/-- Invariance of `q̄_λ` under the faithful `H_V`-action (transport of `blockHinv`). -/
theorem hv_inv (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    letI := blockPS_commGroup Blk
    letI := hvAct T Blk
    IsInvariant (HVq T Blk) (blockQbar T Blk F.alpha F.alpha_surjective l hlne) := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := hvAct T Blk
  intro g v
  obtain ⟨c, rfl⟩ := blockProjF_surjective T Blk g
  rw [← blockProjF_compat T Blk c v]
  exact blockHinv T Blk F.alpha F.alpha_surjective l hlne c v

/-- Simplicity of `V` under the faithful `H_V`-action (transport of `blockHsimple`). -/
theorem hv_simple :
    letI := blockPS_commGroup Blk
    letI := hvAct T Blk
    ∀ W : AddSubgroup (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)),
      (∀ (g : HVq T Blk) (w : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)),
        w ∈ W → g • w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := hvAct T Blk
  intro W hW
  refine (blockHsimple T Blk).2 W fun c w hw => ?_
  rw [blockProjF_compat T Blk c w]
  exact hW (blockProjF T Blk c) w hw

/-! ## The `H_V`-level κ⁰ datum and the head-inflated enrichment -/

/-- The `H_V`-level κ⁰ existential: Lemma 6.3 (`kappa0_exists_tame`, landed P-17e5) at the
faithful head quotient with the tame pair `(hvSigma, hvTau)`. -/
noncomputable def blockKappa0HV (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :=
  letI := blockPS_commGroup Blk
  letI := hvAct T Blk
  kappa0_exists_tame (hv_gen T Blk F) (hv_rel T Blk F)
    (blockQbar T Blk F.alpha F.alpha_surjective l hlne)
    (blockHquad T Blk F.alpha F.alpha_surjective l hlne)
    (blockHns T Blk F.alpha F.alpha_surjective l hlne)
    (hv_inv T Blk F l hlne) (blockHsimple T Blk).1 (hv_simple T Blk)

/-- The chosen `H_V`-level base-class datum. -/
noncomputable def blockDatHV (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    letI := blockPS_commGroup Blk
    FactorSet (HVq T Blk) (Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)) :=
  (blockKappa0HV T Blk F l hlne).choose

theorem blockDatHV_spec (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    letI := blockPS_commGroup Blk
    letI := hvAct T Blk
    IsEquivariantFactorSet (blockQbar T Blk F.alpha F.alpha_surjective l hlne)
      (blockDatHV T Blk F l hlne) :=
  (blockKappa0HV T Blk F l hlne).choose_spec

end TamePair

/-- **The head-inflated block enrichment** (P-16d6e4aA-P4b): `blockEnrichment` with the κ⁰
datum replaced by the definitionally-transparent inflation
`(blockDatHV …).reindexHom blockProjF` of the faithful-head-quotient datum — every other
field (module, action, forms, descent) is `blockEnrichment`'s own.  At this enrichment every
`QZero`/`Q0loc` evaluation transports down `graphPullback_reindexHom` to `C := H_V`, where
every boundary lift is tame-factored through the *fixed* `mk' ∘ F.alpha` and `hfaith` holds
by construction (`hvAct_faithful`) — see `docs/p16d6e4aA-p4-tame-package.md`. -/
noncomputable def blockEnrichmentD (hE2 : ∀ e : E, e ^ 2 = 1) (F : BoundaryFrame H E) :
    (blockFrame T Blk hE2).Enrichment :=
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := hvAct T Blk
  { blockEnrichment T Blk hE2 F with
    dat := fun l h =>
      (blockDatHV T Blk F l (fun heq => h (Subtype.ext heq))).reindexHom
        ⇑(blockProjF T Blk)
    hdat := fun l h =>
      IsEquivariantFactorSet.comapHom
        (blockDatHV_spec T Blk F l (fun heq => h (Subtype.ext heq)))
        (blockProjF T Blk) (blockProjF_compat T Blk) }

/-- The datum of `blockEnrichmentD` is the inflation, definitionally — the entry point for
the `graphPullback_reindexHom`/`Q0loc_reindexHom` transports. -/
theorem blockEnrichmentD_dat_eq (hE2 : ∀ e : E, e ^ 2 = 1) (F : BoundaryFrame H E)
    (l : (blockFrame T Blk hE2).DR) (h : l ≠ (blockFrame T Blk hE2).zeroDR) :
    (blockEnrichmentD T Blk hE2 F).dat l h
      = (blockDatHV T Blk F l (fun heq => h (Subtype.ext heq))).reindexHom
          ⇑(blockProjF T Blk) :=
  rfl

/-! ## The boundary equation's head component

Every boundary lift of either source is tame-factored **at the head**, through the fixed
`F.alpha` — the first component of `IsBoundaryLift`, `rfl`-deep.  This replaces the refuted
per-lift `hpack` factorizations: composing with `mk' (headActKer)` gives the `H_V`-level
factorization through `mk' ∘ F.alpha`, uniformly in `ρ`. -/

/-- `Γ_A` version: `TC.piY ∘ ρ = α ∘ tameA`. -/
theorem boundaryLift_head_gammaA (hE2 : ∀ e : E, e ^ 2 = 1) (B : BoundaryMaps)
    (F : BoundaryFrame H E)
    (ρ : BoundaryLifts B.bA F (blockFrame T Blk hE2).TC) (γ : GammaA) :
    (blockFrame T Blk hE2).TC.piY (ρ.1.1 γ) = F.alpha (B.tameA γ) :=
  congrArg Prod.fst (ρ.2 γ)

/-- Local version: `TC.piY ∘ ρ = α ∘ tameF`. -/
theorem boundaryLift_head_local (hE2 : ∀ e : E, e ^ 2 = 1) (B : BoundaryMaps)
    (F : BoundaryFrame H E)
    (ρ : BoundaryLifts B.bF F (blockFrame T Blk hE2).TC) (γ : AbsGalQ2) :
    (blockFrame T Blk hE2).TC.piY (ρ.1.1 γ) = F.alpha (B.tameF γ) :=
  congrArg Prod.fst (ρ.2 γ)

/-- The block frame's C-head is `blockPiCH` (definitional alignment for the consumers). -/
theorem blockPiCH_eq_TC_piY (hE2 : ∀ e : E, e ^ 2 = 1) :
    blockPiCH T Blk = (blockFrame T Blk hE2).TC.piY :=
  rfl

end SectionNine

end GQ2
