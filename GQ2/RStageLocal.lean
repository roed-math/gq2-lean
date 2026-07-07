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

end RStageLocal

end GQ2
