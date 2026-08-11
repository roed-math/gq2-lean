/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.SectionSix

@[expose] public section

/-!
# Representative independence of `Q⁰_loc`  (Lemma 6.4 layer ⟹ Lemma 6.14)

The base quadratic connecting map `Q⁰_loc` (`GQ2/SectionSix.lean`, eq. (92)) is defined on
`H¹`-classes through the canonical cocycle representative `Quotient.out`.  Its well-definedness —
that `H2ofFun (graphPullback dat ρ ·)` is invariant under a cohomologous change of the `Z¹`
representative — is **Lemma 6.4**.  We prove it (`repIndep`) by exhibiting the explicit
conjugation coboundary (a 6.22-style char-2 cochain identity), then read off **Lemma 6.14**
(eq. (102), regular-module realization) via the on-the-nose `comap` identity + `mapCoeff1`
functoriality.  Axioms: **∅** (std-3).

The `SectionSix.lemma_6_14` statement is amended (documented) with the compatibility hypotheses
its use of `Q⁰_loc` requires: `hdatW` (equivariant factor set on `W`), `hiC` (`i` is a
`C`-module map — eq. (77)'s `i ⋊ 1`), and `hρW` (`G_ℚ₂` acts on `W` through `ρ`).
-/

namespace GQ2
namespace RepIndependence

open ContCoh QuadraticFp2 Corestriction SectionSix
open scoped Classical

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]
variable {W : Type} [AddCommGroup W] [TopologicalSpace W] [DiscreteTopology W] [Finite W]
  [DistribMulAction AbsGalQ2 W] [ContinuousSMul AbsGalQ2 W] [DistribMulAction C W]

/-- If two raw 2-cochains differ by a continuous coboundary, their `H2ofFun` classes agree.
(Replica of `ShapiroLedger.H2ofFun_eq_of_sub_mem_B2`, kept local to avoid a cross-module import.) -/
theorem h2ofFun_eq_of_sub_mem_B2 {φ ψ : AbsGalQ2 × AbsGalQ2 → ZMod 2}
    (h : φ - ψ ∈ B2 AbsGalQ2 (ZMod 2)) : H2ofFun AbsGalQ2 φ = H2ofFun AbsGalQ2 ψ := by
  by_cases hφ : φ ∈ Z2 AbsGalQ2 (ZMod 2)
  · have hψ : ψ ∈ Z2 AbsGalQ2 (ZMod 2) := by
      have := sub_mem hφ (B2_le_Z2 h); rwa [sub_sub_cancel] at this
    rw [H2ofFun_of_mem hφ, H2ofFun_of_mem hψ, ← sub_eq_zero, ← map_sub]
    refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]
    exact h
  · have hψ : ψ ∉ Z2 AbsGalQ2 (ZMod 2) := fun hψ =>
      hφ <| by rw [show φ = ψ + (φ - ψ) from by abel]; exact add_mem hψ (B2_le_Z2 h)
    rw [H2ofFun, H2ofFun, dif_neg hφ, dif_neg hψ]

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [TopologicalSpace W]
  [DiscreteTopology W] [Finite W] [DistribMulAction AbsGalQ2 W] [ContinuousSMul AbsGalQ2 W] in
/-- **`κ⁰` is a 2-cocycle on `V ⋊ C`** (the factor-set cocycle identity — display (61)/Lemma 6.1 —
from the equivariant factor-set axioms `m_mul`, `m_quad`, `f_cocycle`). -/
theorem kappa0_cocycle {q : W → ZMod 2} {dat : FactorSet C W}
    (hdat : IsEquivariantFactorSet q dat) (a b c : SemiProd C W) :
    kappa0 dat a b + kappa0 dat (a * b) c = kappa0 dat a (b * c) + kappa0 dat b c := by
  obtain ⟨fcoc, _, _, _, _, mquad, mmul, _⟩ := hdat
  obtain ⟨v, cc⟩ := a; obtain ⟨w, d⟩ := b; obtain ⟨x, e⟩ := c
  simp only [kappa0, SemiProd.mul_def, smul_add, mul_smul]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    mmul cc d x + mquad cc w (d • x) + fcoc v (cc • w) (cc • (d • x))

/-- The inner-conjugation 1-cochain `η_s(x) = κ⁰(s, x) + κ⁰(sxs⁻¹, s)` on `V ⋊ C`. -/
def etaS {C W : Type*} [Group C] [AddCommGroup W] [DistribMulAction C W]
    (dat : FactorSet C W) (s x : SemiProd C W) : ZMod 2 :=
  kappa0 dat s x + kappa0 dat (s * x * s⁻¹) s

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [TopologicalSpace W]
  [DiscreteTopology W] [Finite W] [DistribMulAction AbsGalQ2 W] [ContinuousSMul AbsGalQ2 W] in
/-- **Inner automorphisms act trivially on `H²`** (pointwise): `c_s^*κ⁰ − κ⁰ = δ¹(η_s)`, i.e.
`η_s(y) + η_s(xy) + η_s(x) = κ⁰(sxs⁻¹, sys⁻¹) + κ⁰(x, y)` in char 2.  Three instances of the
2-cocycle identity `kappa0_cocycle` at `(s,x,y)`, `(sxs⁻¹, s, y)`, `(sxs⁻¹, sys⁻¹, s)`. -/
theorem innerConj {q : W → ZMod 2} {dat : FactorSet C W}
    (hdat : IsEquivariantFactorSet q dat) (s x y : SemiProd C W) :
    etaS dat s y + etaS dat s (x * y) + etaS dat s x
      = kappa0 dat (s * x * s⁻¹) (s * y * s⁻¹) + kappa0 dat x y := by
  have A1 := kappa0_cocycle hdat s x y
  have A3 := kappa0_cocycle hdat (s * x * s⁻¹) s y
  have A2 := kappa0_cocycle hdat (s * x * s⁻¹) (s * y * s⁻¹) s
  rw [show s * x * s⁻¹ * s = s * x from by group] at A3
  rw [show s * x * s⁻¹ * (s * y * s⁻¹) = s * (x * y) * s⁻¹ from by group,
    show s * y * s⁻¹ * s = s * y from by group] at A2
  simp only [etaS]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) A1 + A2 + A3

omit [Finite C] [Finite W] [ContinuousSMul AbsGalQ2 W] in
/-- **Core cochain identity (Lemma 6.4 / conjugation coboundary).**  Shifting a cocycle `b` by the
principal coboundary `g ↦ g·w₀ − w₀` changes `graphPullback dat ρ b` by a 2-coboundary — the
`(−w₀,1)`-conjugation phase `ψ = η_s ∘ φ_b` on `V ⋊ C` (`φ_b(g) = (b g, ρ g)`, `s = (−w₀,1)`;
`graphPullback(b) = φ_b^*κ⁰` and `φ_{b+δ⁰w₀} = c_s ∘ φ_b`). -/
theorem graphPullback_sub_mem_B2 {q : W → ZMod 2} (dat : FactorSet C W)
    (hdat : IsEquivariantFactorSet q dat) (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (w : W), g • w = ρ g • w) (b : Z1 AbsGalQ2 W) (w₀ : W) :
    graphPullback dat ρ (fun g => b.1 g + (g • w₀ - w₀)) - graphPullback dat ρ b.1
      ∈ B2 AbsGalQ2 (ZMod 2) := by
  obtain ⟨hbc, hb⟩ := mem_Z1_iff.mp b.2
  set s : SemiProd C W := ((-w₀ : W), (1 : C)) with hs
  set φb : AbsGalQ2 → SemiProd C W := fun g' => (b.1 g', ρ g') with hφ
  have hb1 : ∀ g' : AbsGalQ2,
      s * φb g' * s⁻¹ = ((b.1 g' + (g' • w₀ - w₀), ρ g') : SemiProd C W) := by
    intro g'
    rw [hρ g' w₀]
    simp only [hφ, hs, SemiProd.mul_def, SemiProd.inv_def, one_smul, one_mul, mul_one,
      inv_one, neg_neg]
    show ((-w₀ + b.1 g' + ρ g' • w₀, ρ g') : W × C) = (b.1 g' + (ρ g' • w₀ - w₀), ρ g')
    rw [Prod.mk.injEq]
    exact ⟨by abel, rfl⟩
  have hmul : ∀ g' h' : AbsGalQ2, φb (g' * h') = φb g' * φb h' := by
    intro g' h'
    simp only [hφ, SemiProd.mul_def]
    rw [hb g' h', map_mul ρ g' h', hρ g' (b.1 h')]
  refine (AddSubgroup.mem_map).mpr ⟨fun g => etaS dat s (φb g), ?_, ?_⟩
  · -- continuity: `η_s ∘ (g ↦ (b g, ρ g))`, factoring through the finite discrete `W × C`
    refine mem_C1_iff.mpr ?_
    have hF : Continuous fun g : AbsGalQ2 => ((b.1 g, ρ g) : W × C) :=
      hbc.prodMk ρ.continuous_toFun
    exact (continuous_of_discreteTopology (f := fun t : W × C => etaS dat s t)).comp hF
  · funext p
    obtain ⟨g, h⟩ := p
    have hgp1 : graphPullback dat ρ (fun g => b.1 g + (g • w₀ - w₀)) (g, h)
        = kappa0 dat (s * φb g * s⁻¹) (s * φb h * s⁻¹) := by
      rw [hb1 g, hb1 h]; rfl
    have hgp2 : graphPullback dat ρ b.1 (g, h) = kappa0 dat (φb g) (φb h) := rfl
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, absGal_smul_zmodTwo, Pi.sub_apply,
      hgp1, hgp2, hmul g h]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      innerConj hdat s (φb g) (φb h)

omit [Finite C] [Finite W] [ContinuousSMul AbsGalQ2 W] in
/-- **Representative independence (Lemma 6.4).**  `H2ofFun (graphPullback dat ρ ·)` depends only on
the `H¹`-class of the cocycle. -/
theorem repIndep {q : W → ZMod 2} (dat : FactorSet C W) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (w : W), g • w = ρ g • w)
    (b₁ b₂ : Z1 AbsGalQ2 W) (hcoh : H1mk AbsGalQ2 W b₁ = H1mk AbsGalQ2 W b₂) :
    H2ofFun AbsGalQ2 (graphPullback dat ρ b₁.1) = H2ofFun AbsGalQ2 (graphPullback dat ρ b₂.1) := by
  -- `b₁ − b₂ ∈ B¹`: extract the 0-cochain `w₀`.
  have hker : (b₁ - b₂) ∈ (B1 AbsGalQ2 W).addSubgroupOf (Z1 AbsGalQ2 W) := by
    have h0 : H1mk AbsGalQ2 W (b₁ - b₂) = 0 := by rw [map_sub, hcoh, sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).mp h0
  rw [AddSubgroup.mem_addSubgroupOf] at hker
  obtain ⟨w₀, hw₀⟩ := hker
  -- so `b₁.1 g = b₂.1 g + (g·w₀ − w₀)`
  have hb1 : b₁.1 = fun g => b₂.1 g + (g • w₀ - w₀) := by
    funext g
    have := congrFun hw₀ g
    simp only [dZero, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddSubgroup.coe_sub,
      Pi.sub_apply] at this
    rw [this]; abel
  apply h2ofFun_eq_of_sub_mem_B2
  rw [hb1]
  exact graphPullback_sub_mem_B2 dat hdat ρ hρ b₂ w₀

/-- `H1mk` of the canonical representative is the identity. -/
lemma H1mk_out {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] (y : H1 AbsGalQ2 M) :
    H1mk AbsGalQ2 M (Quotient.out y) = y := Quotient.out_eq y

omit [Finite V] [Finite C] [Finite W] in
/-- **Lemma 6.14 (regular-module realization), eq. (102).**  Amended (documented) with the
compatibility hypotheses `Q⁰_loc` requires: `hdatW` (equivariant factor set on `W`), `hiC`
(`i` a `C`-module map, eq. (77)'s `i ⋊ 1`), `hρW` (`G_ℚ₂` acts on `W` through `ρ`). -/
theorem lemma_6_14 (D : TateDuality 2)
    (datW : FactorSet C W) (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (i : V →+ W) (hic : Continuous i) (hicompat : ∀ (g : AbsGalQ2) (v : V), i (g • v) = g • i v)
    {q : W → ZMod 2} (hdatW : IsEquivariantFactorSet q datW)
    (hiC : ∀ (c : C) (v : V), i (c • v) = c • i v)
    (hρW : ∀ (g : AbsGalQ2) (w : W), g • w = ρ g • w)
    (x : H1 AbsGalQ2 V) :
    Q0loc D (datW.comap i) ρ x = Q0loc D datW ρ (mapCoeff1 i hic hicompat x) := by
  -- reduce to equality of the two `H2ofFun` arguments
  show iotaF D (H2ofFun AbsGalQ2 (graphPullback (datW.comap i) ρ (Quotient.out x).1))
      = iotaF D (H2ofFun AbsGalQ2 (graphPullback datW ρ
          (Quotient.out (mapCoeff1 i hic hicompat x)).1))
  refine congrArg (iotaF D) ?_
  -- the pushed cocycle `i ∘ out(x)`
  set b₁ : Z1 AbsGalQ2 W :=
    Z1comap (ContinuousMonoidHom.id AbsGalQ2) i hic (fun g n => hicompat g n) (Quotient.out x)
    with hb1def
  set b₂ : Z1 AbsGalQ2 W := Quotient.out (mapCoeff1 i hic hicompat x) with hb2def
  -- Step A: `graphPullback (comap i) ρ (out x) = graphPullback datW ρ b₁` on the nose
  have hb1val : b₁.1 = fun g => i ((Quotient.out x).1 g) := rfl
  have hStepA : graphPullback (datW.comap i) ρ (Quotient.out x).1 = graphPullback datW ρ b₁.1 := by
    rw [hb1val]
    funext p
    simp only [graphPullback, FactorSet.comap]
    rw [hiC]
  rw [hStepA]
  -- Step B: `b₁` and `b₂` are cohomologous, so the `H2ofFun`s agree (Lemma 6.4)
  refine repIndep datW hdatW ρ hρW b₁ b₂ ?_
  have h1 : mapCoeff1 i hic hicompat (H1mk AbsGalQ2 V (Quotient.out x)) = H1mk AbsGalQ2 W b₁ := by
    rw [hb1def]; rfl
  rw [← h1, H1mk_out, hb2def, H1mk_out]

end RepIndependence
end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (102) = ⟦eq-regularnaturality⟧
  * eq. (77) = ⟦eq-basepullback⟧
  * eq. (92) = ⟦eq-localbaseQ⟧
  * Lemma 6.1 = ⟦lem-extraspecialconnecting⟧
  * Lemma 6.14 = ⟦lem-regularrealization⟧
  * Lemma 6.4 = ⟦lem-detnormalizationindependence⟧
-/
