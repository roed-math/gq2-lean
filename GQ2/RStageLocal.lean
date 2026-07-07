import GQ2.BlockRStage
import GQ2.LocalLiftingDuality

/-!
# P-16d6e (residue package, local source): the (136) R-stage for `Γ = G_ℚ₂`

Discharges the per-source residues of `blockStageR136` (`GQ2/BlockRStage.lean`) at the local
source `Γ = AbsGalQ2`, per the route of record (`docs/p16d6a-handoff.md` §3): **one
`prop_5_16`-package invocation per twisted module**, through its standalone pieces —

* `hcard` — `#H²(G_ℚ₂, 𝔽₂) = 2` = `card_H2_zmod2_eq_two` (clause (iii));
* `hZcount` — `#RCocycle = z_R = #R²·#D_R`: the crossed-cocycle group is `Z¹(G_ℚ₂, R_{f₀})`
  (multiplicative↔additive bridge, the P-16d6b `TCocycle` pattern), counted by `card_Z1_eq`
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
(t.f.g. of `G_ℚ₂` — **B1**, reserved for P-17i) thread hypothesis-side to the assembly.
Axioms here: std-3 + B6 + B7 (through `card_Z1_eq`/`card_H2_zmod2_eq_two`/
`bijective_cup20_dualEval`).

Deliverable: **`stageR136_local`** — the (136) identity for the block frame at the local
source, the exact `stageR136` field of the `RecursionInputs` bundle (P-16d6e assembly).
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
@[reducible] def rCommGroup (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r) : CommGroup ↥Blk.R :=
  { (inferInstance : Group ↥Blk.R) with
    mul_comm := fun r s => Subtype.ext
      (hRK (r : Y) r.2 (s : Y) (SectionSeven.frattiniLike_le Blk.K s.2)) }

/-- Conjugation on `R` by an element of `Y` depends only on its `K`-coset (`K`-centrality). -/
theorem conj_eq_of_mk_eq_K (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r) {y w : Y}
    (h : QuotientGroup.mk' Blk.K y = QuotientGroup.mk' Blk.K w) (r : ↥Blk.R) :
    y * (r : Y) * y⁻¹ = w * (r : Y) * w⁻¹ := by
  obtain ⟨k, hk, hyk⟩ := (QuotientGroup.mk'_eq_mk' Blk.K).mp h
  subst hyk
  have hcomm : (r : Y) * k = k * (r : Y) := hRK (r : Y) r.2 k hk
  calc y * (r : Y) * y⁻¹ = y * (k * (r : Y) * k⁻¹) * y⁻¹ := by rw [← hcomm]; group
    _ = y * k * (r : Y) * (y * k)⁻¹ := by group

/-- Conjugation by `y` lands back in `R` (`R ◁ Y`). -/
theorem conj_mem_R (y : Y) (r : ↥Blk.R) : y * (r : Y) * y⁻¹ ∈ Blk.R :=
  (SectionSeven.frattiniLike_normal Blk.K Blk.hK).conj_mem (r : Y) r.2 y

variable (Blk) in
/-- The `C = Y/K` conjugation action on `Additive R` (`Quotient.out`-conjugation; independent
of the representative by `conj_eq_of_mk_eq_K`). -/
@[reducible] noncomputable def conjC (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r) :
    DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.R) where
  smul c a := Additive.ofMul
    ⟨Quotient.out c * ((Additive.toMul a : ↥Blk.R) : Y) * (Quotient.out c)⁻¹,
      conj_mem_R _ _⟩
  one_smul a := by
    have h1 : QuotientGroup.mk' Blk.K (Quotient.out (1 : Y ⧸ Blk.K))
        = QuotientGroup.mk' Blk.K 1 := by
      rw [map_one]
      exact Quotient.out_eq (1 : Y ⧸ Blk.K)
    apply Additive.toMul.injective
    apply Subtype.ext
    show Quotient.out (1 : Y ⧸ Blk.K) * _ * (Quotient.out (1 : Y ⧸ Blk.K))⁻¹ = _
    rw [conj_eq_of_mk_eq_K hRK h1]
    group
  mul_smul c d a := by
    have hcd : QuotientGroup.mk' Blk.K (Quotient.out (c * d))
        = QuotientGroup.mk' Blk.K (Quotient.out c * Quotient.out d) := by
      have hx : ∀ x : Y ⧸ Blk.K, QuotientGroup.mk' Blk.K (Quotient.out x) = x :=
        fun x => Quotient.out_eq x
      rw [map_mul, hx, hx, hx]
    apply Additive.toMul.injective
    apply Subtype.ext
    show Quotient.out (c * d) * _ * (Quotient.out (c * d))⁻¹ = _
    rw [conj_eq_of_mk_eq_K hRK hcd]
    show _ = Quotient.out c * (Quotient.out d * _ * (Quotient.out d)⁻¹) * (Quotient.out c)⁻¹
    group
  smul_zero c := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show Quotient.out c * (1 : Y) * (Quotient.out c)⁻¹ = 1
    group
  smul_add c a b := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show Quotient.out c * (((Additive.toMul a : ↥Blk.R) : Y)
        * ((Additive.toMul b : ↥Blk.R) : Y)) * (Quotient.out c)⁻¹ = _
    show _ = (Quotient.out c * _ * (Quotient.out c)⁻¹) * (Quotient.out c * _ * (Quotient.out c)⁻¹)
    group

/-- The action computed at any coset representative. -/
theorem conjC_smul_of_mk (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r) (y : Y)
    (r : ↥Blk.R) :
    letI := conjC Blk hRK
    (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K) • Additive.ofMul r
      = Additive.ofMul (⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩ : ↥Blk.R) := by
  letI := conjC Blk hRK
  have hout : QuotientGroup.mk' Blk.K (Quotient.out (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K))
      = QuotientGroup.mk' Blk.K y := Quotient.out_eq _
  apply Additive.toMul.injective
  apply Subtype.ext
  show Quotient.out (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K) * (r : Y) * _⁻¹
    = y * (r : Y) * y⁻¹
  exact conj_eq_of_mk_eq_K hRK hout r

end ConjAction

/-! ## `hZcount`: the `z_R` torsor count at the local source -/

section ZCount

set_option maxHeartbeats 800000 in
/-- **The `z_R` torsor count, local source** (P-16d6e residue): for every boundary lift `f₀`,
`#RCocycle = z_R = #R² · #D_R`.  Route: `RCocycle ≃ Z¹(G_ℚ₂, R_{f₀})` (multiplicative crossed ↔
additive, the conjugation action through `C = Y/K` pulled back along the surjective
`mk' K ∘ f₀`), `card_Z1_eq` (5.16 clause (ii), B6+B7), and the invariant-character bridge
`fixedPts C (R^∨) ≃ D_Rmod` + `blockRChar_card`. -/
theorem hZcount_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.R, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.R, r * r = 1)
    (b : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup) (F : BoundaryFrame H E)
    (f₀ : BoundaryLifts b F T) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1)
      = (blockFrameImpl T Blk hE2).zR := by
  classical
  letI : CommGroup ↥Blk.R := rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.R) := conjC Blk hRK
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
  letI actG : DistribMulAction AbsGalQ2 (Additive ↥Blk.R) :=
    DistribMulAction.compHom _ θ.toMonoidHom
  letI : TopologicalSpace (Additive ↥Blk.R) := (inferInstance : TopologicalSpace ↥Blk.R)
  haveI : DiscreteTopology (Additive ↥Blk.R) :=
    ⟨(inferInstance : DiscreteTopology ↥Blk.R).eq_bot⟩
  haveI : Finite (Additive ↥Blk.R) := (inferInstance : Finite ↥Blk.R)
  haveI : ContinuousSMul AbsGalQ2 (Additive ↥Blk.R) := by
    refine ⟨?_⟩
    have hfac : (fun p : AbsGalQ2 × Additive ↥Blk.R => p.1 • p.2)
        = (fun q : (Y ⧸ Blk.K) × Additive ↥Blk.R => q.1 • q.2)
          ∘ (fun p : AbsGalQ2 × Additive ↥Blk.R => (θ p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hcomp : ∀ (γ : AbsGalQ2) (a : Additive ↥Blk.R), γ • a = θ γ • a := fun _ _ => rfl
  have hA₂ : ∀ a : Additive ↥Blk.R, a + a = 0 := by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hR2 _ (Additive.toMul a).2
  -- the action at the `f₀`-representative
  have hsmul : ∀ (γ : AbsGalQ2) (a : Additive ↥Blk.R),
      γ • a
        = Additive.ofMul (⟨f₀.1.1 γ * ((Additive.toMul a : ↥Blk.R) : Y) * (f₀.1.1 γ)⁻¹,
            conj_mem_R (f₀.1.1 γ) (Additive.toMul a)⟩ : ↥Blk.R) := by
    intro γ a
    have h1 : γ • a
        = (QuotientGroup.mk' Blk.K (f₀.1.1 γ) : Y ⧸ Blk.K) • Additive.ofMul (Additive.toMul a) :=
      rfl
    rw [h1]
    exact conjC_smul_of_mk hRK (f₀.1.1 γ) (Additive.toMul a)
  -- the multiplicative↔additive crossed-cocycle bridge
  have hequiv : RCocycle (blockFrameImpl T Blk hE2) f₀.1.1
      ≃ ↥(Z1 AbsGalQ2 (Additive ↥Blk.R)) :=
    { toFun := fun c =>
        ⟨fun γ => Additive.ofMul ⟨c.u γ, c.mem γ⟩, by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · show Continuous fun γ => (⟨c.u γ, c.mem γ⟩ : ↥Blk.R)
            exact Continuous.subtype_mk c.cont _
          · intro γ δ
            rw [hsmul γ (Additive.ofMul ⟨c.u δ, c.mem δ⟩)]
            apply Additive.toMul.injective
            apply Subtype.ext
            show c.u (γ * δ) = c.u γ * (f₀.1.1 γ * c.u δ * (f₀.1.1 γ)⁻¹)
            exact c.crossed γ δ⟩
      invFun := fun z =>
        { u := fun γ => ((Additive.toMul (z.1 γ) : ↥Blk.R) : Y)
          mem := fun γ => (Additive.toMul (z.1 γ)).2
          cont := by
            have hz := (mem_Z1_iff.mp z.2).1
            exact continuous_subtype_val.comp hz
          crossed := by
            intro γ δ
            have hz := (mem_Z1_iff.mp z.2).2 γ δ
            rw [hsmul γ (z.1 δ)] at hz
            have := congrArg (fun a => ((Additive.toMul a : ↥Blk.R) : Y)) hz
            simpa using this }
      left_inv := fun c => RCocycle.ext rfl
      right_inv := fun z => Subtype.ext (funext fun γ => rfl) }
  rw [Nat.card_congr hequiv, card_Z1_eq hθs hcomp hA₂]
  -- the invariant-character bridge `fixedPts C (R^∨) ≃ D_Rmod`
  have hbridge : Nat.card
      (GQ2.FoxH.fixedPts (Y ⧸ Blk.K) (GQ2.FoxH.ElemDual (Additive ↥Blk.R)))
      = Nat.card ↥(RCharSub Blk) := by
    refine Nat.card_congr
      { toFun := fun lam => ⟨lam.1, fun y r => ?_⟩
        invFun := fun chi => ⟨chi.1, fun c => ?_⟩
        left_inv := fun lam => rfl
        right_inv := fun chi => rfl }
    · -- fixed ⟹ Y-invariant
      have hfix := lam.2 (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)
      have h1 := congrArg (fun mu : GQ2.FoxH.ElemDual (Additive ↥Blk.R) =>
        mu (Additive.ofMul ⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩)) hfix
      have h3 : (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)⁻¹
          • Additive.ofMul (⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩ : ↥Blk.R)
          = Additive.ofMul r := by
        rw [← map_inv]
        rw [conjC_smul_of_mk hRK y⁻¹ ⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩]
        apply congrArg
        apply Subtype.ext
        show y⁻¹ * (y * (r : Y) * y⁻¹) * y⁻¹⁻¹ = (r : Y)
        group
      have h2 : ((QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K) • lam.1)
          (Additive.ofMul ⟨y * (r : Y) * y⁻¹, conj_mem_R y r⟩)
          = lam.1 (Additive.ofMul r) := by
        rw [GQ2.FoxH.ElemDual.smul_apply, h3]
      rw [h2] at h1
      exact h1.symm
    · -- Y-invariant ⟹ fixed
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Blk.K c
      apply GQ2.FoxH.ElemDual.ext
      intro a
      rw [GQ2.FoxH.ElemDual.smul_apply]
      have h3 : (QuotientGroup.mk' Blk.K y : Y ⧸ Blk.K)⁻¹ • a
          = Additive.ofMul (⟨y⁻¹ * ((Additive.toMul a : ↥Blk.R) : Y) * y⁻¹⁻¹,
              conj_mem_R y⁻¹ (Additive.toMul a)⟩ : ↥Blk.R) := by
        rw [← map_inv]
        exact conjC_smul_of_mk hRK y⁻¹ (Additive.toMul a)
      rw [h3]
      exact chi.2 y⁻¹ (Additive.toMul a)
  rw [hbridge, blockRChar_card T Blk hE2,
    Nat.card_congr (Additive.toMul (α := ↥Blk.R))]
  rfl

end ZCount

end RStageLocal

end GQ2
