/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Block.RStage
import GQ2.LocalLiftingDuality

/-!
# The (136) R-stage for `Γ = G_ℚ₂`

Discharges the per-source residues of `blockStageR136` (`GQ2/BlockRStage.lean`) at the local
source `Γ = AbsGalQ2`, per the route of record (`docs/orchestration/p16d6a-handoff.md` §3): **one
`prop_5_16`-package invocation per twisted module**, through its standalone pieces —

* `hcard` — `#H²(G_ℚ₂, 𝔽₂) = 2` = `card_H2_zmod2_eq_two` (clause (iii));
* `hZcount` — `#RCocycle = z_R = #R²·#D_R`: the crossed-cocycle group is `Z¹(G_ℚ₂, R_{f₀})`
  (multiplicative↔additive bridge, the Prop. 8.9 assembly `TCocycle` pattern), counted by `card_Z1_eq`
  (clause (ii)), with `#fixedPts C (R^∨) = #D_R` via the `Y`-invariance bridge
  (`fixedPtsEquivRChar`) + `blockRChar_card`;
* `hsep_hom` — the `(R^∨)^C`-separation: `obs g = 0` forces every invariant character to kill
  the paired defect class (`obs_zero_iff_pairClass_zero`), the paired classes are the
  `cup20`-values of the `R`-valued defect class, `bijective_cup20_dualEval` (clause (vi))
  forces `[rDefect] = 0` in `H²(G_ℚ₂, R_ρ)`, `B²`-extraction produces the continuous
  splitting cochain, and `homLift_of_split` assembles the lift.

The twisted action throughout is the `C = Y/K`-conjugation on `R` (well-defined by
`lemma_7_2`'s `K`-centrality, threaded as `hRK`), pulled back along the *surjective* lower map
of the boundary lift (`BoundaryLifts` bundles surjectivity — this is why `hsep_hom` is
supplied directly to `blockStageR136` rather than through `hsep_hom_of_splitCriterion`, whose
`hsplit` quantifies over arbitrary, possibly non-surjective `g`).

The `lemma_7_2` outputs (`hRK` = `R` central in `K`, `hR2` = `R` exponent 2) and `hfg`
(t.f.g. of `G_ℚ₂` — **B1**, reserved for the §9 induction) thread hypothesis-side to the assembly.
Axioms here: std-3 + B6 + B7 (through `card_Z1_eq`/`card_H2_zmod2_eq_two`/
`bijective_cup20_dualEval`).

Main result: **`stageR136_local`** — the (136) identity for the block frame at the local
source, the exact `stageR136` field of the `RecursionInputs` bundle (the Prop. 8.9 assembly).
-/

namespace GQ2

namespace RStageLocal

open ContCoh SectionEight SectionSeven LocalLiftingDuality GQ2.FoxH

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- `K ◁ Y` as an instance (the `MinimalBlock` field, made searchable). -/
instance : Blk.K.Normal := Blk.hK


/-! ## The `C = Y/K` conjugation action on `R` (well-defined by `K`-centrality) -/

section ConjAction

variable (Blk) in
/-- `R` is abelian: it is central in `K` (`hRK`, from `lemma_7_2`) and contained in `K`. -/
@[reducible] def rCommGroup (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r) :
    CommGroup ↥Blk.frattiniK :=
  { (inferInstance : Group ↥Blk.frattiniK) with
    mul_comm := fun r s => Subtype.ext
      (hRK (r : Y) r.2 (s : Y) (SectionSeven.frattiniLike_le Blk.K s.2)) }

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- Conjugation on `R` by an element of `Y` depends only on its `K`-coset (`K`-centrality). -/
theorem conj_eq_of_mk_eq_K (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r) {y w : Y}
    (h : QuotientGroup.mk' Blk.K y = QuotientGroup.mk' Blk.K w) (r : ↥Blk.frattiniK) :
    y * (r : Y) * y⁻¹ = w * (r : Y) * w⁻¹ := by
  obtain ⟨k, hk, hyk⟩ := (QuotientGroup.mk'_eq_mk' Blk.K).mp h
  subst hyk
  calc y * (r : Y) * y⁻¹ = y * (k * (r : Y) * k⁻¹) * y⁻¹ := by
        rw [← hRK (r : Y) r.2 k hk]; group
    _ = y * k * (r : Y) * (y * k)⁻¹ := by group

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- Conjugation by `y` lands back in `R` (`R ◁ Y`). -/
theorem conj_mem_R (y : Y) (r : ↥Blk.frattiniK) : y * (r : Y) * y⁻¹ ∈ Blk.frattiniK :=
  (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem (r : Y) r.2 y

variable (Blk) in
/-- The `C = Y/K` conjugation action on `Additive R` (`Quotient.out`-conjugation; independent
of the representative by `conj_eq_of_mk_eq_K`). -/
@[reducible] noncomputable def conjC (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r) :
    DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) where
  smul c a := Additive.ofMul
    ⟨Quotient.out c * ((Additive.toMul a : ↥Blk.frattiniK) : Y) * (Quotient.out c)⁻¹,
      conj_mem_R _ _⟩
  one_smul a := by
    have h1 : QuotientGroup.mk' Blk.K (Quotient.out (1 : Y ⧸ Blk.K))
        = QuotientGroup.mk' Blk.K 1 := by
      rw [map_one]
      exact Quotient.out_eq (1 : Y ⧸ Blk.K)
    refine Additive.toMul.injective (Subtype.ext ?_)
    show Quotient.out (1 : Y ⧸ Blk.K) * _ * (Quotient.out (1 : Y ⧸ Blk.K))⁻¹ = _
    rw [conj_eq_of_mk_eq_K hRK h1]
    group
  mul_smul c d a := by
    have hcd : QuotientGroup.mk' Blk.K (Quotient.out (c * d))
        = QuotientGroup.mk' Blk.K (Quotient.out c * Quotient.out d) := by
      have hx : ∀ x : Y ⧸ Blk.K, QuotientGroup.mk' Blk.K (Quotient.out x) = x :=
        fun x => Quotient.out_eq x
      rw [map_mul, hx, hx, hx]
    refine Additive.toMul.injective (Subtype.ext ?_)
    show Quotient.out (c * d) * _ * (Quotient.out (c * d))⁻¹ = _
    rw [conj_eq_of_mk_eq_K hRK hcd]
    show _ = Quotient.out c * (Quotient.out d * _ * (Quotient.out d)⁻¹) * (Quotient.out c)⁻¹
    group
  smul_zero c := by
    refine Additive.toMul.injective (Subtype.ext ?_)
    show Quotient.out c * (1 : Y) * (Quotient.out c)⁻¹ = 1
    group
  smul_add c a b := by
    refine Additive.toMul.injective (Subtype.ext ?_)
    show Quotient.out c * (((Additive.toMul a : ↥Blk.frattiniK) : Y)
        * ((Additive.toMul b : ↥Blk.frattiniK) : Y)) * (Quotient.out c)⁻¹ = _
    show _ = (Quotient.out c * _ * (Quotient.out c)⁻¹) * (Quotient.out c * _ * (Quotient.out c)⁻¹)
    group

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- The action computed at any coset representative. -/
theorem conjC_smul_of_mk (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r) (y : Y)
    (r : ↥Blk.frattiniK) :
    letI := conjC Blk hRK
    (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K) • Additive.ofMul r
      = Additive.ofMul (⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩ : ↥Blk.frattiniK) := by
  letI := conjC Blk hRK
  have hout : QuotientGroup.mk' Blk.K (Quotient.out (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K))
      = QuotientGroup.mk' Blk.K y := Quotient.out_eq _
  refine Additive.toMul.injective (Subtype.ext ?_)
  show Quotient.out (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K) * (r : Y) * _⁻¹
    = y * (r : Y) * y⁻¹
  exact conj_eq_of_mk_eq_K hRK hout r

end ConjAction

/-! ## Shared `C = Y/K`-module helpers (used by `hZcount` and `hsep_hom`) -/
omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `R = Φ(K)` is elementary abelian: `Additive R` is 2-torsion. -/
private lemma frattiniK_add_self
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1) :
    letI : CommGroup ↥Blk.frattiniK := rCommGroup Blk hRK
    ∀ a : Additive ↥Blk.frattiniK, a + a = 0 := by
  letI : CommGroup ↥Blk.frattiniK := rCommGroup Blk hRK
  intro a
  refine Additive.toMul.injective (Subtype.ext ?_)
  exact hR2 _ (Additive.toMul a).2

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- A `C = Y/K`-invariant character of `R` takes equal values on `Y`-conjugates: the fixed-point
condition, evaluated through `conjC_smul_of_mk` at `y⁻¹`. -/
private lemma elemDual_fixed_apply_conj
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r) :
    letI : CommGroup ↥Blk.frattiniK := rCommGroup Blk hRK
    letI := conjC Blk hRK
    ∀ lam : GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK),
      lam ∈ GQ2.FoxH.fixedPts (Y ⧸ Blk.K) (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK)) →
      ∀ (y : Y) (r : ↥Blk.frattiniK),
        lam (Additive.ofMul ⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩)
          = lam (Additive.ofMul r) := by
  letI : CommGroup ↥Blk.frattiniK := rCommGroup Blk hRK
  letI := conjC Blk hRK
  intro lam hfix y r
  have hfixy := hfix (QuotientGroup.mk' Blk.K y)
  have h1 := congrArg (fun mu : GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK) =>
    mu (Additive.ofMul ⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩)) hfixy
  have h3 : (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)⁻¹
      • Additive.ofMul (⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩ : ↥Blk.frattiniK)
      = Additive.ofMul r := by
    rw [← map_inv,
      conjC_smul_of_mk hRK y⁻¹ ⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩]
    refine congrArg _ (Subtype.ext ?_)
    show y⁻¹ * (y * (r : Y) * y⁻¹) * y⁻¹⁻¹ = (r : Y)
    group
  have h2 : ((QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K) • lam)
      (Additive.ofMul ⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩)
      = lam (Additive.ofMul r) := by
    rw [GQ2.FoxH.ElemDual.smul_apply, h3]
  rw [h2] at h1
  exact h1.symm

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- The invariant-character bridge `(R^∨)^C ≃ D_Rmod`: `#fixedPts C (R^∨) = #RCharSub`. -/
private lemma card_fixedPts_eq_card_RCharSub
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r) :
    letI : CommGroup ↥Blk.frattiniK := rCommGroup Blk hRK
    letI := conjC Blk hRK
    Nat.card
      (GQ2.FoxH.fixedPts (Y ⧸ Blk.K) (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK)))
      = Nat.card ↥(RCharSub Blk) := by
  letI : CommGroup ↥Blk.frattiniK := rCommGroup Blk hRK
  letI := conjC Blk hRK
  refine Nat.card_congr
    { toFun := fun lam => ⟨lam.1, fun y r => elemDual_fixed_apply_conj hRK lam.1 lam.2 y r⟩
      invFun := fun chi => ⟨chi.1, fun c => ?_⟩
      left_inv := fun lam => rfl
      right_inv := fun chi => rfl }
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Blk.K c
  refine GQ2.FoxH.ElemDual.ext fun a => ?_
  rw [GQ2.FoxH.ElemDual.smul_apply]
  have h3 : (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)⁻¹ • a
      = Additive.ofMul (⟨y⁻¹ * ((Additive.toMul a : ↥Blk.frattiniK) : Y) * y⁻¹⁻¹,
          conj_mem_R y⁻¹ (Additive.toMul a)⟩ : ↥Blk.frattiniK) := by
    rw [← map_inv]
    exact conjC_smul_of_mk hRK y⁻¹ (Additive.toMul a)
  rw [h3]
  exact chi.2 y⁻¹ (Additive.toMul a)

/-! ## `hZcount`: the `z_R` torsor count at the local source -/

section ZCount

/-- **The `z_R` torsor count, local source** (the Prop. 8.9 assembly residue): for every boundary lift `f₀`,
`#RCocycle = z_R = #R² · #D_R`.  Route: `RCocycle ≃ Z¹(G_ℚ₂, R_{f₀})` (multiplicative crossed ↔
additive, the conjugation action through `C = Y/K` pulled back along the surjective
`mk' K ∘ f₀`), `card_Z1_eq` (5.16 clause (ii), B6+B7), and the invariant-character bridge
`fixedPts C (R^∨) ≃ D_Rmod` + `blockRChar_card`. -/
theorem hZcount_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup) (F : BoundaryFrame H E)
    (f₀ : BoundaryLifts b F T) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1)
      = (blockFrameImpl T Blk hE2).zR := by
  classical
  letI : CommGroup ↥Blk.frattiniK := rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) := conjC Blk hRK
  -- the lower map through `C = Y/K`, surjective
  set θ : ContinuousMonoidHom AbsGalQ2 (Y ⧸ Blk.K) :=
    ⟨(QuotientGroup.mk' Blk.K).comp f₀.1.1.toMonoidHom, by
      show Continuous fun γ => QuotientGroup.mk' Blk.K (f₀.1.1 γ)
      exact Continuous.comp continuous_of_discreteTopology
        f₀.1.1.continuous_toFun⟩ with hθdef
  have hθs : Function.Surjective ⇑θ := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
    obtain ⟨γ, hγ⟩ := f₀.1.2 y
    exact ⟨γ, by show QuotientGroup.mk' Blk.K (f₀.1.1 γ) = c; rw [hγ, hy]⟩
  letI actG : DistribMulAction AbsGalQ2 (Additive ↥Blk.frattiniK) :=
    DistribMulAction.compHom _ θ.toMonoidHom
  letI : TopologicalSpace (Additive ↥Blk.frattiniK) :=
    (inferInstance : TopologicalSpace ↥Blk.frattiniK)
  haveI : DiscreteTopology (Additive ↥Blk.frattiniK) :=
    ⟨(inferInstance : DiscreteTopology ↥Blk.frattiniK).eq_bot⟩
  haveI : Finite (Additive ↥Blk.frattiniK) := (inferInstance : Finite ↥Blk.frattiniK)
  haveI : ContinuousSMul AbsGalQ2 (Additive ↥Blk.frattiniK) := by
    refine ⟨?_⟩
    have hfac : (fun p : AbsGalQ2 × Additive ↥Blk.frattiniK => p.1 • p.2)
        = (fun q : (Y ⧸ Blk.K) × Additive ↥Blk.frattiniK => q.1 • q.2)
          ∘ (fun p : AbsGalQ2 × Additive ↥Blk.frattiniK => (θ p.1, p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hcomp : ∀ (γ : AbsGalQ2) (a : Additive ↥Blk.frattiniK), γ • a = θ γ • a := fun _ _ => rfl
  have hA₂ : ∀ a : Additive ↥Blk.frattiniK, a + a = 0 := frattiniK_add_self hRK hR2
  -- the action at the `f₀`-representative
  have hsmul : ∀ (γ : AbsGalQ2) (a : Additive ↥Blk.frattiniK),
      γ • a
        = Additive.ofMul (⟨f₀.1.1 γ * ((Additive.toMul a : ↥Blk.frattiniK) : Y) * (f₀.1.1 γ)⁻¹,
            conj_mem_R (f₀.1.1 γ) (Additive.toMul a)⟩ : ↥Blk.frattiniK) := by
    intro γ a
    have h1 : γ • a
        = (QuotientGroup.mk' Blk.K (f₀.1.1 γ) : Y ⧸ Blk.K) • Additive.ofMul (Additive.toMul a) :=
      rfl
    rw [h1]
    exact conjC_smul_of_mk hRK (f₀.1.1 γ) (Additive.toMul a)
  -- the multiplicative↔additive crossed-cocycle bridge
  have hequiv : RCocycle (blockFrameImpl T Blk hE2) f₀.1.1
      ≃ ↥(Z1 AbsGalQ2 (Additive ↥Blk.frattiniK)) :=
    { toFun := fun c =>
        ⟨fun γ => Additive.ofMul ⟨c.u γ, c.mem γ⟩, by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · show Continuous fun γ => (⟨c.u γ, c.mem γ⟩ : ↥Blk.frattiniK)
            exact Continuous.subtype_mk c.cont _
          · intro γ δ
            rw [hsmul γ (Additive.ofMul ⟨c.u δ, c.mem δ⟩)]
            refine Additive.toMul.injective (Subtype.ext ?_)
            show c.u (γ * δ) = c.u γ * (f₀.1.1 γ * c.u δ * (f₀.1.1 γ)⁻¹)
            exact c.crossed γ δ⟩
      invFun := fun z =>
        { u := fun γ => ((Additive.toMul (z.1 γ) : ↥Blk.frattiniK) : Y)
          mem := fun γ => (Additive.toMul (z.1 γ)).2
          cont := by
            have hz := (mem_Z1_iff.mp z.2).1
            exact continuous_subtype_val.comp hz
          crossed := by
            intro γ δ
            have hz := (mem_Z1_iff.mp z.2).2 γ δ
            rw [hsmul γ (z.1 δ)] at hz
            have := congrArg (fun a => ((Additive.toMul a : ↥Blk.frattiniK) : Y)) hz
            simpa using this }
      left_inv := fun c => RCocycle.ext rfl
      right_inv := fun z => Subtype.ext (funext fun γ => rfl) }
  rw [Nat.card_congr hequiv, card_Z1_eq hθs hcomp hA₂,
    card_fixedPts_eq_card_RCharSub hRK, blockRChar_card T Blk hE2,
    Nat.card_congr (Additive.toMul (α := ↥Blk.frattiniK))]
  rfl

end ZCount

/-! ## `hsep_hom`: the `(R^∨)^C` separation at the local source -/

/-- The `G_ℚ₂`-action on `𝔽₂` is trivial (any group action on `ZMod 2` fixes both elements). -/
theorem htriv_local (γ : AbsGalQ2) (m : ZMod 2) : γ • m = m := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz m with rfl | rfl
  · exact smul_zero γ
  · by_contra hne
    have h1 : γ • (1 : ZMod 2) = 0 := by
      rcases hz (γ • (1 : ZMod 2)) with h | h
      · exact h
      · exact absurd h hne
    have h2 : (1 : ZMod 2) = γ⁻¹ • (0 : ZMod 2) := by
      rw [← h1, inv_smul_smul]
    rw [smul_zero] at h2
    exact one_ne_zero h2

section SepHom

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- First stage of `hsep_hom_local`: when `obs g = 0`, every paired defect class in `H²(Γ,𝔽₂)`
vanishes (`obs_zero_iff_pairClass_zero`, with the zero-`DR` case handled directly). -/
private theorem pairClass_all_zero [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup) (F : BoundaryFrame H E)
    (g : BoundaryLifts b F (blockFrameImpl T Blk hE2).TB)
    (hg : obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv_local
        (card_H2_zmod2_eq_two htriv_local) g.1.1 = 0)
    (d : (blockRObstructionData T Blk hE2).DRmod) :
    H2mk AbsGalQ2 (ZMod 2)
      ⟨fun gd => (blockRObstructionData T Blk hE2).pair d
          (Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 gd.1 gd.2)),
        pairDefect_mem_Z2_all (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
          htriv_local g.1.1 d⟩ = 0 := by
  by_cases h : (blockRObstructionData T Blk hE2).toDR d = (blockFrameImpl T Blk hE2).zeroDR
  · have hd : d = 0 := by
      rw [← (blockRObstructionData T Blk hE2).h0, ← h, Equiv.symm_apply_apply]
    subst hd
    have hz : (⟨fun gd => (blockRObstructionData T Blk hE2).pair 0
        (Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 gd.1 gd.2)),
        pairDefect_mem_Z2_all (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
          htriv_local g.1.1 0⟩ : ↥(Z2 AbsGalQ2 (ZMod 2))) = 0 := by
      apply Subtype.ext
      funext gd
      simp only [map_zero, AddMonoidHom.zero_apply]
      rfl
    rw [hz, map_zero]
  · exact (obs_zero_iff_pairClass_zero (blockFrameImpl T Blk hE2)
      (blockRObstructionData T Blk hE2) htriv_local (card_H2_zmod2_eq_two htriv_local)
      g.1.1 d h).mp (LinearMap.congr_fun hg d)

/-- **The `(R^∨)^C`-separation, local source** (the Prop. 8.9 assembly residue): if the obstruction functional
of a boundary lift `g` vanishes, `g` lifts to a continuous homomorphism into `Y`.  Route:
`obs g = 0` kills every paired defect class (`obs_zero_iff_pairClass_zero`); the paired classes
are the `cup20`-values of the `R`-valued defect class against the invariant characters, and
`H⁰(G_ℚ₂, R^∨) = (R^∨)^C = D_Rmod` by surjectivity of the lower map; `bijective_cup20_dualEval`
(5.16 clause (vi), B6) then forces `[rDefect] = 0` in `H²(G_ℚ₂, R_ρ)`; `B²`-extraction yields a
continuous splitting cochain (exponent 2 kills the signs), and `homLift_of_split` assembles the
lift. -/
theorem hsep_hom_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup) (F : BoundaryFrame H E) :
    ∀ g : BoundaryLifts b F (blockFrameImpl T Blk hE2).TB,
      obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv_local
          (card_H2_zmod2_eq_two htriv_local) g.1.1 = 0 →
        ∃ φ : ContinuousMonoidHom AbsGalQ2 Y,
          ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ := by
  classical
  intro g hg
  -- every paired defect class vanishes (mirror of `hsep_hom_of_splitCriterion`'s first stage)
  have hall : ∀ d : (blockRObstructionData T Blk hE2).DRmod, H2mk AbsGalQ2 (ZMod 2)
      ⟨fun gd => (blockRObstructionData T Blk hE2).pair d
          (Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 gd.1 gd.2)),
        pairDefect_mem_Z2_all (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
          htriv_local g.1.1 d⟩ = 0 :=
    fun d => pairClass_all_zero hE2 b F g hg d
  -- the instance stack for the twisted module `A = Additive R` along `ϑ = piBC ∘ g`
  letI : CommGroup ↥Blk.frattiniK := rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) := conjC Blk hRK
  have hRleK : Blk.frattiniK ≤ Blk.K := SectionSeven.frattiniLike_le Blk.K
  set θ : ContinuousMonoidHom AbsGalQ2 (Y ⧸ Blk.K) :=
    ⟨MonoidHom.mk' (fun γ => QuotientGroup.mk' Blk.K
        (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))) (fun γ δ => by
      rw [← map_mul]
      apply (QuotientGroup.mk'_eq_mk' Blk.K).mpr
      refine ⟨(slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))⁻¹
          * (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ : Y)
          * slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)),
        hRleK (by
          have := (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem _
            (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ).2
            (slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))⁻¹
          rwa [inv_inv] at this), ?_⟩
      show slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ))
          * ((slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))⁻¹
            * (slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
              * slift (blockFrameImpl T Blk hE2) (g.1.1 δ)
              * (slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))⁻¹)
            * slift (blockFrameImpl T Blk hE2) (g.1.1 (γ * δ)))
        = slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
            * slift (blockFrameImpl T Blk hE2) (g.1.1 δ)
      group), by
      show Continuous fun γ => QuotientGroup.mk' Blk.K
        (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))
      exact Continuous.comp continuous_of_discreteTopology
        (Continuous.comp continuous_of_discreteTopology g.1.1.continuous_toFun)⟩ with hθdef
  have hθs : Function.Surjective ⇑θ := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
    obtain ⟨γ, hγ⟩ := g.1.2 ((blockFrameImpl T Blk hE2).piB y)
    refine ⟨γ, ?_⟩
    show QuotientGroup.mk' Blk.K (slift (blockFrameImpl T Blk hE2) (g.1.1 γ)) = c
    rw [hγ, ← hy]
    apply (QuotientGroup.mk'_eq_mk' Blk.K).mpr
    have hker : (slift (blockFrameImpl T Blk hE2) ((blockFrameImpl T Blk hE2).piB y))⁻¹ * y
        ∈ Blk.frattiniK := by
      rw [← (blockFrameImpl T Blk hE2).ker_piB, MonoidHom.mem_ker, map_mul, map_inv,
        piB_slift]
      group
    exact ⟨(slift (blockFrameImpl T Blk hE2) ((blockFrameImpl T Blk hE2).piB y))⁻¹ * y,
      hRleK hker, by group⟩
  letI actG : DistribMulAction AbsGalQ2 (Additive ↥Blk.frattiniK) :=
    DistribMulAction.compHom _ θ.toMonoidHom
  letI : TopologicalSpace (Additive ↥Blk.frattiniK) :=
    (inferInstance : TopologicalSpace ↥Blk.frattiniK)
  haveI : DiscreteTopology (Additive ↥Blk.frattiniK) :=
    ⟨(inferInstance : DiscreteTopology ↥Blk.frattiniK).eq_bot⟩
  haveI : Finite (Additive ↥Blk.frattiniK) := (inferInstance : Finite ↥Blk.frattiniK)
  haveI : ContinuousSMul AbsGalQ2 (Additive ↥Blk.frattiniK) := by
    refine ⟨?_⟩
    have hfac : (fun p : AbsGalQ2 × Additive ↥Blk.frattiniK => p.1 • p.2)
        = (fun q : (Y ⧸ Blk.K) × Additive ↥Blk.frattiniK => q.1 • q.2)
          ∘ (fun p : AbsGalQ2 × Additive ↥Blk.frattiniK => (θ p.1, p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hA₂ : ∀ a : Additive ↥Blk.frattiniK, a + a = 0 := frattiniK_add_self hRK hR2
  -- the action at the `slift ∘ g` representative
  have hsmul : ∀ (γ : AbsGalQ2) (a : Additive ↥Blk.frattiniK),
      γ • a = Additive.ofMul
        (⟨slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
            * ((Additive.toMul a : ↥Blk.frattiniK) : Y)
            * (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))⁻¹,
          conj_mem_R _ (Additive.toMul a)⟩ : ↥Blk.frattiniK) := by
    intro γ a
    have h1 : γ • a = QuotientGroup.mk' Blk.K
        (slift (blockFrameImpl T Blk hE2) (g.1.1 γ)) • Additive.ofMul (Additive.toMul a) := rfl
    rw [h1]
    exact conjC_smul_of_mk hRK _ (Additive.toMul a)
  -- the `R`-valued defect as an additive 2-cocycle
  have hdefZ2 : (fun p : AbsGalQ2 × AbsGalQ2 =>
      Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 p.1 p.2))
      ∈ Z2 AbsGalQ2 (Additive ↥Blk.frattiniK) := by
    refine mem_Z2_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun p : AbsGalQ2 × AbsGalQ2 =>
        (rDefect (blockFrameImpl T Blk hE2) g.1.1 p.1 p.2 : ↥Blk.frattiniK)
      apply Continuous.subtype_mk
      have hs : Continuous fun x : (blockFrameImpl T Blk hE2).YB =>
          slift (blockFrameImpl T Blk hE2) x := continuous_of_discreteTopology
      have h1 : Continuous fun p : AbsGalQ2 × AbsGalQ2 =>
          slift (blockFrameImpl T Blk hE2) (g.1.1 p.1) :=
        hs.comp (g.1.1.continuous_toFun.comp continuous_fst)
      have h2 : Continuous fun p : AbsGalQ2 × AbsGalQ2 =>
          slift (blockFrameImpl T Blk hE2) (g.1.1 p.2) :=
        hs.comp (g.1.1.continuous_toFun.comp continuous_snd)
      have h3 : Continuous fun p : AbsGalQ2 × AbsGalQ2 =>
          slift (blockFrameImpl T Blk hE2) (g.1.1 (p.1 * p.2)) :=
        hs.comp (g.1.1.continuous_toFun.comp continuous_mul)
      exact (h1.mul h2).mul h3.inv
    · intro γ δ ε
      rw [hsmul γ]
      apply Additive.toMul.injective
      show (⟨slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
            * (rDefect (blockFrameImpl T Blk hE2) g.1.1 δ ε : Y)
            * (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))⁻¹, _⟩ : ↥Blk.frattiniK)
          * rDefect (blockFrameImpl T Blk hE2) g.1.1 γ (δ * ε)
        = rDefect (blockFrameImpl T Blk hE2) g.1.1 (γ * δ) ε
          * rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ
      rw [mul_comm (rDefect (blockFrameImpl T Blk hE2) g.1.1 (γ * δ) ε)
        (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ)]
      apply Subtype.ext
      show slift (blockFrameImpl T Blk hE2) (g.1.1 γ)
            * (rDefect (blockFrameImpl T Blk hE2) g.1.1 δ ε : Y)
            * (slift (blockFrameImpl T Blk hE2) (g.1.1 γ))⁻¹
          * (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ (δ * ε) : Y)
        = (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ : Y)
          * (rDefect (blockFrameImpl T Blk hE2) g.1.1 (γ * δ) ε : Y)
      have hrd : ∀ α β : AbsGalQ2, (rDefect (blockFrameImpl T Blk hE2) g.1.1 α β : Y)
          = slift (blockFrameImpl T Blk hE2) (g.1.1 α)
            * slift (blockFrameImpl T Blk hE2) (g.1.1 β)
            * (slift (blockFrameImpl T Blk hE2) (g.1.1 (α * β)))⁻¹ := fun _ _ => rfl
      rw [hrd, hrd, hrd, hrd,
        show γ * (δ * ε) = γ * δ * ε from (mul_assoc γ δ ε).symm]
      group
  -- the dual-side instances and the evaluation-pairing equivariance
  letI actGD : DistribMulAction AbsGalQ2 (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK)) :=
    DistribMulAction.compHom _ θ.toMonoidHom
  letI : TopologicalSpace (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK)) := ⊥
  haveI : DiscreteTopology (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK)) := ⟨rfl⟩
  haveI : ContinuousSMul AbsGalQ2 (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK)) := by
    refine ⟨?_⟩
    have hfac : (fun p : AbsGalQ2 × GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK) => p.1 • p.2)
        = (fun q : (Y ⧸ Blk.K) × GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK) => q.1 • q.2)
          ∘ (fun p => (θ p.1, p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hpair : ∀ (γ : AbsGalQ2) (a : Additive ↥Blk.frattiniK)
      (lam : GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK)),
      GQ2.FoxH.dualEval _ (γ • a) (γ • lam) = γ • GQ2.FoxH.dualEval _ a lam := by
    intro γ a lam
    rw [htriv_local γ (GQ2.FoxH.dualEval _ a lam)]
    show (θ γ • lam) (θ γ • a) = lam a
    rw [GQ2.FoxH.ElemDual.smul_apply, inv_smul_smul]
  -- every `cup20`-value of the defect class vanishes
  have hcup : ∀ n : ↥(H0 AbsGalQ2 (GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK))),
      cup20 (GQ2.FoxH.dualEval _) hpair
        (H2mk AbsGalQ2 (Additive ↥Blk.frattiniK) ⟨_, hdefZ2⟩) n = 0 := by
    intro n
    -- `Γ`-invariance transports to `Y`-invariance through the surjective `θ`
    have hYinv : ∀ (y : Y) (r : ↥Blk.frattiniK),
        n.1 (Additive.ofMul (⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩ : ↥Blk.frattiniK))
          = n.1 (Additive.ofMul r) := by
      intro y r
      obtain ⟨γ, hγ⟩ := hθs (QuotientGroup.mk' Blk.K y)
      have hfix := n.2 γ
      have h1 := congrArg (fun mu : GQ2.FoxH.ElemDual (Additive ↥Blk.frattiniK) =>
        mu (Additive.ofMul (⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩ : ↥Blk.frattiniK))) hfix
      have h2 : (γ • n.1) (Additive.ofMul (⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩ : ↥Blk.frattiniK))
          = n.1 (Additive.ofMul r) := by
        show (θ γ • n.1) _ = _
        rw [GQ2.FoxH.ElemDual.smul_apply, hγ, ← map_inv,
          conjC_smul_of_mk hRK y⁻¹ ⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩]
        refine congrArg _ (congrArg _ (Subtype.ext ?_))
        show y⁻¹ * (y * (r : Y) * y⁻¹) * y⁻¹⁻¹ = (r : Y)
        group
      rw [h2] at h1
      exact h1.symm
    -- the value is the paired defect class, which `hall` kills
    have hred : cup20 (GQ2.FoxH.dualEval _) hpair
        (H2mk AbsGalQ2 (Additive ↥Blk.frattiniK) ⟨_, hdefZ2⟩) n
        = H2mk AbsGalQ2 (ZMod 2)
          ⟨fun gd => (blockRObstructionData T Blk hE2).pair
              ⟨(n.1 : Additive ↥Blk.frattiniK →+ ZMod 2), fun y r => hYinv y r⟩
              (Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 gd.1 gd.2)),
            pairDefect_mem_Z2_all (blockFrameImpl T Blk hE2)
              (blockRObstructionData T Blk hE2) htriv_local g.1.1 _⟩ := by
      have hfun : (fun gd : AbsGalQ2 × AbsGalQ2 => GQ2.FoxH.dualEval _
          (Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 gd.1 gd.2))
          ((gd.1 * gd.2) • n.1))
          = fun gd => (blockRObstructionData T Blk hE2).pair
              ⟨(n.1 : Additive ↥Blk.frattiniK →+ ZMod 2), fun y r => hYinv y r⟩
              (Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 gd.1 gd.2)) := by
        funext gd
        rw [n.2 (gd.1 * gd.2)]
        rfl
      exact congrArg (H2mk AbsGalQ2 (ZMod 2)) (Subtype.ext hfun)
    rw [hred]
    exact hall ⟨(n.1 : Additive ↥Blk.frattiniK →+ ZMod 2), fun y r => hYinv y r⟩
  -- injectivity of the `(2,0)` cup forces the defect class to vanish
  have hzero : H2mk AbsGalQ2 (Additive ↥Blk.frattiniK) ⟨_, hdefZ2⟩ = 0 := by
    apply (bijective_cup20_dualEval hA₂ htriv_local hpair).1
    show cup20 (GQ2.FoxH.dualEval _) hpair _ = cup20 (GQ2.FoxH.dualEval _) hpair 0
    rw [map_zero]
    exact AddMonoidHom.ext fun n => hcup n
  -- `B²`-extraction: a continuous splitting cochain
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hzero
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨ψ, hψC1, hψeq⟩ := hmem
  have hψc : Continuous ψ := hψC1
  refine homLift_of_split (blockFrameImpl T Blk hE2) g.1.1
    (fun γ => Additive.toMul (ψ γ)) ?_ ?_
  · show Continuous fun γ => ((Additive.toMul (ψ γ) : ↥Blk.frattiniK) : Y)
    exact continuous_subtype_val.comp hψc
  · intro γ δ
    have h : γ • ψ δ - ψ (γ * δ) + ψ γ
        = Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ) :=
      congrFun hψeq (γ, δ)
    -- `dOne ψ (γ,δ) = γ•ψδ − ψ(γδ) + ψγ = defect`; exponent 2 kills the sign
    have hD : -(Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ))
        = Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ) :=
      neg_eq_of_add_eq_zero_left (hA₂ _)
    have h2 : ψ (γ * δ) = ψ γ + γ • ψ δ
        + Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ) := by
      have h3 : ψ (γ * δ) = γ • ψ δ + ψ γ
          - Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g.1.1 γ δ) := by
        rw [← h]
        abel
      rw [h3, sub_eq_add_neg, hD, add_comm (γ • ψ δ) (ψ γ)]
    rw [hsmul γ (ψ δ)] at h2
    exact congrArg (fun a : Additive ↥Blk.frattiniK => ((Additive.toMul a : ↥Blk.frattiniK) : Y)) h2

end SepHom

/-! ## The assembly, parametric over `hsep_hom` -/

section Assembly


/-- **(136) for the block frame at the local source, parametric over `hsep_hom`**
(the Prop. 8.9 assembly residue assembly): `htriv`/`hcard`/`hZcount` are discharged
(`htriv_local`/`card_H2_zmod2_eq_two`/`hZcount_local`); the remaining inputs are the
`lemma_7_2` structural facts (`hRK`/`hR2`), `hfg` (**B1**, reserved for the §9 induction), and
**`hsep_hom`** — the `(R^∨)^C`-separation (next increment: `prop_5_16` clause (vi) +
`B²`-extraction + `homLift_of_split`; see the module docstring for the surjectivity
scoping note). -/
theorem stageR136_local_of_hsep [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (hfg : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hsep_hom : ∀ g : BoundaryLifts b F (blockFrameImpl T Blk hE2).TB,
      obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv_local
          (card_H2_zmod2_eq_two htriv_local) g.1.1 = 0 →
        ∃ φ : ContinuousMonoidHom AbsGalQ2 Y,
          ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCount b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * ((blockFrameImpl T Blk hE2).mB b F l : ℤ)
            - exactImageCount b F (blockFrameImpl T Blk hE2).TB) :=
  blockStageR136 T Blk hE2 htriv_local (card_H2_zmod2_eq_two htriv_local) hfg b F hsep_hom
    (fun f₀ => hZcount_local hE2 hRK hR2 b F f₀)

/-- **(136) for the block frame at the local source — all residues discharged**
(the Prop. 8.9 assembly): `htriv`/`hcard`/`hZcount`/`hsep_hom` are all proved; the remaining hypotheses are
the `lemma_7_2` structural facts (`hRK`/`hR2`) and `hfg` (**B1**, reserved for the §9 induction).  The
conclusion is the `stageR136` field of the local `RecursionInputs` bundle, verbatim. -/
theorem stageR136_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (hfg : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup) (F : BoundaryFrame H E) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCount b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * ((blockFrameImpl T Blk hE2).mB b F l : ℤ)
            - exactImageCount b F (blockFrameImpl T Blk hE2).TB) :=
  stageR136_local_of_hsep hE2 hRK hR2 hfg b F (hsep_hom_local hE2 hRK hR2 b F)

end Assembly

end RStageLocal

end GQ2
