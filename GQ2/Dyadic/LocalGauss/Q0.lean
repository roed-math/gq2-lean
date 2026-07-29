/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.DeepPart.Q0locLayer
public import GQ2.CupSymmetry

@[expose] public section

/-!
# `Q⁰_{K,V}` and its polarization over a general local dualizing source (LG2)

**Packet Prop. 6.6 (`prop:local-polar`), group-generic.**  This file is the clone-retype of the
ℚ₂ `Q⁰_loc` layer (`GQ2.SectionSix.Q0loc`, `GQ2/SectionSix.lean`, and the quadratic-structure
block `GQ2/DeepPart/Q0locLayer.lean`) with the ambient `G_ℚ₂` replaced by an arbitrary
topological group `Γ` carrying a **local Tate-duality bundle** `D : TateDualityG Γ 2`
(`GQ2/TateDuality.lean`).  In the dyadic campaign `Γ = G_K = ↥U` for `U ≤ G_ℚ₂` open of finite
index; §6 below supplies the bundle for exactly those `Γ` from the base-generalized B6
(`GQ2.tateDualityAt`) via `IsLocalDualizingGroup` (`GQ2/TateDuality.lean`).  The ℚ₂ originals are
untouched (design memo `docs/dyadic/lg-design.md` §2: 13/13 clone, zero in-place edits).

## What Prop. 6.6 says, and where it is

Given a `C`-module `V` with an equivariant factor-set datum `dat` for a quadratic form `q`
(`GQ2.FactorSet`/`GQ2.IsEquivariantFactorSet`, `GQ2/OrbitData.lean` — the extraspecial datum:
the normalized class `κ⁰_q = GQ2.kappa0 dat` and its existence/normalization stay part of the
determinant datum) and a continuous `ρ : Γ →* C` through which `Γ` acts on `V`:

* **well-definedness** — `Q0loc_H1mk`: the value `ι_F((b, ρ)^* κ⁰_q)` may be computed from *any*
  cocycle representative `b` of a class.  Cohomologous cocycles have `V`-conjugate graph
  homomorphisms `φ_b : Γ → V ⋊ C`, so their `κ⁰_q`-pullbacks differ by the explicit coboundary
  `δ¹(η_s ∘ φ_b)` (`graphPullback_sub_mem_B2`, `repIndep`);
* **polarization** — `polar_Q0loc`: `B_{Q⁰}(x, y) = ι_F(y ∪_{b_q} x)`, `ι_F = inv_Γ` the invariant
  map of the bundle through the `𝔽₂ ≅ μ₂` bridge; with `isQuadraticFp2_Q0loc` this makes `Q⁰` a
  normalized quadratic map on `H¹(Γ, V)`;
* **nonsingularity** — `nonsingular_Q0loc`: from the bundle's `(1,1)`-perfectness clause (B6)
  through the polar `μ₂`-self-duality of `V`.

## Contents

* §0 trivial-coefficient facts at a general `Γ` (`smul_zmodTwo`, `smul_muTwo`) — replacing the
  `rfl`-lemma `GQ2.absGal_smul_zmodTwo` and `GQ2.DeepPart.muTwo_smul_trivial`, both of which are
  `G_ℚ₂`-typed.  *Both actions are automatically trivial: a group acting by additive
  automorphisms on a two-element group acts trivially.*
* §1 `iotaF` — the local source functional at `Γ`.
* §2 `Q0loc` and `graphPullback_mem_Z2`.
* §3 **well-definedness** (Prop. 6.6, first clause): `repIndep`, `Q0loc_H1mk`.
* §4 **polarization** (Prop. 6.6, second clause): `Q0loc_add`, `polar_Q0loc`,
  `isQuadraticFp2_Q0loc`.
* §5 **nonsingularity** (Prop. 6.6, third clause, via B6): `nonsingular_Q0loc`.
* §6 local dualizing sources: `subgroup_isLocalDualizingGroup` and the composition lemma
  `isLocalDualizingGroup_of_openEmbedding` (nested subgroups: `N ≤ ↥U ≤ G_ℚ₂`).
* §7 the reusable **group-side transport** `H0congrGroup`/`H1congrGroup`/`H2congrGroup` along a
  `ContinuousMulEquiv` with a matched coefficient equivalence (memo §2: the single mitigation for
  the `↥(N_K)`-vs-`↥N` nested-subtype friction, and the memo's L6).

Axioms: every declaration here is parametrized over the bundle `D`, so `#print axioms` is the
standard three throughout — exactly as for the ℚ₂ models.  (B6 enters only where a consumer
builds `D` from `GQ2.tateDualityAt`; §6's `subgroup_isLocalDualizingGroup` is itself axiom-free —
it produces the *hypothesis* of that axiom, not the bundle.)
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh GQ2.QuadraticFp2
open scoped Classical

/-! ## §0 Trivial coefficients at a general ambient group

The ℚ₂ layer uses `GQ2.absGal_smul_zmodTwo : g • m = m` (a `rfl`-lemma for the transported
`Kummer` instance) and `GQ2.DeepPart.muTwo_smul_trivial`.  Neither is available at a general `Γ`,
but neither needs to be assumed: an additive automorphism of a two-element group is the
identity. -/

section TrivialCoefficients

variable {Γ : Type*} [Group Γ]

/-- **Any group action on `𝔽₂` is trivial** — the `Γ`-generic replacement for the ℚ₂ `rfl`-lemma
`GQ2.absGal_smul_zmodTwo`. -/
theorem smul_zmodTwo [DistribMulAction Γ (ZMod 2)] (g : Γ) (m : ZMod 2) : g • m = m := by
  have hcase : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcase m with rfl | rfl
  · exact smul_zero g
  · rcases hcase (g • (1 : ZMod 2)) with h | h
    · exact absurd ((smul_eq_zero_iff_eq g).mp h) (by decide)
    · exact h

/-- **Any group action on `μ₂` is trivial** — the `Γ`-generic form of
`GQ2.DeepPart.muTwo_smul_trivial` (same proof: `μ₂` has two elements). -/
theorem smul_muTwo [DistribMulAction Γ (MuN 2)] (g : Γ) (x : MuN 2) : g • x = x := by
  rcases DeepPart.muTwo_eq_zero_or_gen x with rfl | rfl
  · exact smul_zero g
  · rcases DeepPart.muTwo_eq_zero_or_gen (g • DeepPart.muTwoGen) with h | h
    · exact absurd ((smul_eq_zero_iff_eq g).mp h) DeepPart.muTwoGen_ne_zero
    · exact h

/-- The coefficient bridge `𝔽₂ →+ μ₂` is `Γ`-equivariant for any `Γ` (both actions trivial). -/
theorem muTwoOfF2_equivariant [DistribMulAction Γ (ZMod 2)] [DistribMulAction Γ (MuN 2)]
    (g : Γ) (n : ZMod 2) :
    SectionSix.muTwoOfF2 (g • n) = g • SectionSix.muTwoOfF2 n := by
  rw [smul_zmodTwo, smul_muTwo]

end TrivialCoefficients

/-! ## §1 The local source functional `ι_F = inv_Γ`

`GQ2.SectionSix.iotaF` at a general bundle (`GQ2/SectionSix.lean`). -/

section Iota

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]

/-- **The local source functional `ι_F = inv_Γ : H²(Γ, 𝔽₂) → 𝔽₂`** through the `𝔽₂ ≅ μ₂` bridge
and the bundle's invariant map — the `Γ`-generic `GQ2.SectionSix.iotaF`. -/
noncomputable def iotaF (D : TateDualityG Γ 2) : H2 Γ (ZMod 2) →+ ZMod 2 :=
  D.inv.toAddMonoidHom.comp
    (mapCoeff2 SectionSix.muTwoOfF2 continuous_of_discreteTopology muTwoOfF2_equivariant)

end Iota

/-! ## §2 `Q⁰` and the graph pullback

`GQ2.SectionSix.Q0loc` (eq. (92)) and its well-formedness clause `graphPullback_mem_Z2`
(Lemma 6.1, display (62)) at a general `Γ`.  The datum layer (`FactorSet`, `kappa0`,
`graphPullback`, `FactorSet.comap`) lives in `GQ2/OrbitData.lean` and is already ambient-free —
`graphPullback` is stated for an arbitrary index group — so nothing there is cloned. -/

section Q0loc

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

/-- **`Q⁰_{Γ,V}`** (eq. (92)): `Q⁰([b]) = inv_Γ((b, ρ)^* κ⁰_q)` on `H¹(Γ, V)`, through the
canonical cocycle representative.  Well-definedness is `Q0loc_H1mk` below (Prop. 6.6, first
clause), not baked into the definition; junk value `0` off the cocycle locus. -/
noncomputable def Q0loc (D : TateDualityG Γ 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C) : H1 Γ V → ZMod 2 :=
  fun x ↦ iotaF D (H2ofFun Γ (graphPullback dat ρ (Quotient.out x).1))

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- `Q⁰` unfolded (definitional). -/
theorem Q0loc_apply (D : TateDualityG Γ 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C) (x : H1 Γ V) :
    Q0loc D dat ρ x = iotaF D (H2ofFun Γ (graphPullback dat ρ (Quotient.out x).1)) := rfl

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] [DistribMulAction Γ (MuN 2)]
  [ContinuousSMul Γ (MuN 2)] [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- **Well-formedness of the graph pullback** (Lemma 6.1, display (62)) at a general `Γ`: for an
equivariant factor-set datum and a continuous 1-cocycle `b` (with `Γ` acting on `V` through
`ρ`), the pullback is a continuous 2-cocycle. -/
theorem graphPullback_mem_Z2 {q : V → ZMod 2} (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q dat) (ρ : ContinuousMonoidHom Γ C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (b : Z1 Γ V) :
    graphPullback dat ρ b.1 ∈ Z2 Γ (ZMod 2) := by
  obtain ⟨hbc, hb⟩ := mem_Z1_iff.mp b.2
  refine mem_Z2_iff.mpr ⟨?_, fun g h k ↦ ?_⟩
  · -- continuity: factor through the finite discrete triple `C × V × V`
    have hF : Continuous fun p : Γ × Γ ↦ ((ρ p.1, b.1 p.1, b.1 p.2) : C × V × V) :=
      (ρ.continuous_toFun.comp continuous_fst).prodMk
        ((hbc.comp continuous_fst).prodMk (hbc.comp continuous_snd))
    exact (continuous_of_discreteTopology
      (f := fun t : C × V × V ↦ dat.f t.2.1 (t.1 • t.2.2) + dat.m t.1 t.2.2)).comp hF
  · -- the cocycle identity: (59) + (60) + the factor-set identity, in char 2
    rw [smul_zmodTwo]
    show dat.f (b.1 h) (ρ h • b.1 k) + dat.m (ρ h) (b.1 k)
        + (dat.f (b.1 g) (ρ g • b.1 (h * k)) + dat.m (ρ g) (b.1 (h * k)))
        = dat.f (b.1 (g * h)) (ρ (g * h) • b.1 k) + dat.m (ρ (g * h)) (b.1 k)
        + (dat.f (b.1 g) (ρ g • b.1 h) + dat.m (ρ g) (b.1 h))
    have hbk : b.1 (h * k) = b.1 h + ρ h • b.1 k := by rw [hb h k, hρ]
    have hbg : b.1 (g * h) = b.1 g + ρ g • b.1 h := by rw [hb g h, hρ]
    have hρm : ρ (g * h) = ρ g * ρ h := map_mul _ _ _
    rw [hbk, hbg, hρm, smul_add, ← mul_smul]
    have h59 := hdat.m_quad (ρ g) (b.1 h) (ρ h • b.1 k)
    have h60 := hdat.m_mul (ρ g) (ρ h) (b.1 k)
    have hco := hdat.f_cocycle (b.1 g) (ρ g • b.1 h) ((ρ g * ρ h) • b.1 k)
    rw [← mul_smul] at h59
    linear_combination h59 - h60 - hco
      + CharTwo.add_self_eq_zero (dat.f (b.1 h) (ρ h • b.1 k))
      - CharTwo.add_self_eq_zero (dat.m (ρ g) (b.1 h))
      - CharTwo.add_self_eq_zero (dat.m (ρ g) (ρ h • b.1 k))

end Q0loc

/-! ## §3 Well-definedness — packet Prop. 6.6, first clause

Cohomologous cocycles have `V`-conjugate graph homomorphisms, hence equal `κ⁰_q`-pullbacks in
`H²`.  The `Γ`-generic form of `GQ2.RepIndependence.{h2ofFun_eq_of_sub_mem_B2,
graphPullback_sub_mem_B2, repIndep}` (`GQ2/RepIndependence.lean`).  The two purely algebraic
inputs `GQ2.RepIndependence.{kappa0_cocycle, innerConj}` and the conjugation cochain
`GQ2.RepIndependence.etaS` are ambient-free already and are consumed verbatim. -/

section RepIndep

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
  [DistribMulAction Γ V] [DistribMulAction C V]

/-- Two raw 2-cochains differing by a continuous coboundary have the same `H2ofFun` class. -/
theorem h2ofFun_eq_of_sub_mem_B2 {φ ψ : Γ × Γ → ZMod 2} (h : φ - ψ ∈ B2 Γ (ZMod 2)) :
    H2ofFun Γ φ = H2ofFun Γ ψ := by
  by_cases hφ : φ ∈ Z2 Γ (ZMod 2)
  · have hψ : ψ ∈ Z2 Γ (ZMod 2) := by
      have := sub_mem hφ (B2_le_Z2 h); rwa [sub_sub_cancel] at this
    rw [H2ofFun_of_mem hφ, H2ofFun_of_mem hψ, ← sub_eq_zero, ← map_sub]
    refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]
    exact h
  · have hψ : ψ ∉ Z2 Γ (ZMod 2) := fun hψ =>
      hφ <| by rw [show φ = ψ + (φ - ψ) from by abel]; exact add_mem hψ (B2_le_Z2 h)
    rw [H2ofFun, H2ofFun, dif_neg hφ, dif_neg hψ]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **The conjugation coboundary (Lemma 6.4 core identity) at a general `Γ`.**  Shifting a
cocycle `b` by the principal coboundary `g ↦ g·w₀ − w₀` changes `graphPullback dat ρ b` by the
2-coboundary `δ¹(η_s ∘ φ_b)`, where `φ_b(g) = (b g, ρ g)` and `s = (−w₀, 1) ∈ V ⋊ C`. -/
theorem graphPullback_sub_mem_B2 {q : V → ZMod 2} (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q dat) (ρ : ContinuousMonoidHom Γ C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (b : Z1 Γ V) (w₀ : V) :
    graphPullback dat ρ (fun g => b.1 g + (g • w₀ - w₀)) - graphPullback dat ρ b.1
      ∈ B2 Γ (ZMod 2) := by
  obtain ⟨hbc, hb⟩ := mem_Z1_iff.mp b.2
  set s : SectionSix.SemiProd C V := ((-w₀ : V), (1 : C)) with hs
  set φb : Γ → SectionSix.SemiProd C V := fun g' => (b.1 g', ρ g') with hφ
  have hb1 : ∀ g' : Γ, s * φb g' * s⁻¹ = ((b.1 g' + (g' • w₀ - w₀), ρ g') : SectionSix.SemiProd C V) := by
    intro g'
    rw [hρ g' w₀]
    simp only [hφ, hs, SectionSix.SemiProd.mul_def, SectionSix.SemiProd.inv_def, one_smul, one_mul, mul_one,
      inv_one, neg_neg]
    show ((-w₀ + b.1 g' + ρ g' • w₀, ρ g') : V × C) = (b.1 g' + (ρ g' • w₀ - w₀), ρ g')
    rw [Prod.mk.injEq]
    exact ⟨by abel, rfl⟩
  have hmul : ∀ g' h' : Γ, φb (g' * h') = φb g' * φb h' := by
    intro g' h'
    simp only [hφ, SectionSix.SemiProd.mul_def]
    rw [hb g' h', map_mul ρ g' h', hρ g' (b.1 h')]
  refine (AddSubgroup.mem_map).mpr ⟨fun g => RepIndependence.etaS dat s (φb g), ?_, ?_⟩
  · -- continuity: `η_s ∘ (g ↦ (b g, ρ g))`, factoring through the discrete `V × C`
    refine mem_C1_iff.mpr ?_
    have hF : Continuous fun g : Γ => ((b.1 g, ρ g) : V × C) := hbc.prodMk ρ.continuous_toFun
    exact (continuous_of_discreteTopology
      (f := fun t : V × C => RepIndependence.etaS dat s t)).comp hF
  · funext p
    obtain ⟨g, h⟩ := p
    have hgp1 : graphPullback dat ρ (fun g => b.1 g + (g • w₀ - w₀)) (g, h)
        = kappa0 dat (s * φb g * s⁻¹) (s * φb h * s⁻¹) := by
      rw [hb1 g, hb1 h]; rfl
    have hgp2 : graphPullback dat ρ b.1 (g, h) = kappa0 dat (φb g) (φb h) := rfl
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_zmodTwo, Pi.sub_apply,
      hgp1, hgp2, hmul g h]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      RepIndependence.innerConj hdat s (φb g) (φb h)

/-- **Representative independence (Lemma 6.4) at a general `Γ`** — packet Prop. 6.6, first
clause: `H2ofFun (graphPullback dat ρ ·)` depends only on the `H¹`-class of the cocycle. -/
theorem repIndep {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (b₁ b₂ : Z1 Γ V) (hcoh : H1mk Γ V b₁ = H1mk Γ V b₂) :
    H2ofFun Γ (graphPullback dat ρ b₁.1) = H2ofFun Γ (graphPullback dat ρ b₂.1) := by
  have hker : (b₁ - b₂) ∈ (B1 Γ V).addSubgroupOf (Z1 Γ V) := by
    have h0 : H1mk Γ V (b₁ - b₂) = 0 := by rw [map_sub, hcoh, sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).mp h0
  rw [AddSubgroup.mem_addSubgroupOf] at hker
  obtain ⟨w₀, hw₀⟩ := hker
  have hb1 : b₁.1 = fun g => b₂.1 g + (g • w₀ - w₀) := by
    funext g
    have := congrFun hw₀ g
    simp only [dZero, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddSubgroup.coe_sub,
      Pi.sub_apply] at this
    rw [this]; abel
  apply h2ofFun_eq_of_sub_mem_B2
  rw [hb1]
  exact graphPullback_sub_mem_B2 dat hdat ρ hρ b₂ w₀

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- `H1mk` of the canonical representative is the identity. -/
theorem H1mk_out {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction Γ M] [ContinuousSMul Γ M] (y : H1 Γ M) :
    H1mk Γ M (Quotient.out y) = y := Quotient.out_eq y

end RepIndep

/-! ## §4 The polar form — packet Prop. 6.6, second clause -/

section Polar

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] [DiscreteTopology C] [Finite C]
  [Finite V] [ContinuousSMul Γ V] [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)] in
/-- **The (93) cochain identity** at a general `Γ`: the graph pullback is quadratic in the
cocycle, with the cup cocycle of the polar pairing (swapped slots) as cross-term, up to the
explicit coboundary `δ¹(g ↦ f(b₁ g, b₂ g))`. -/
theorem graphPullback_add_sub_mem_B2 (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (b₁ b₂ : ↥(Z1 Γ V)) :
    graphPullback dat ρ ((b₁ + b₂ : ↥(Z1 Γ V)) : Γ → V)
      - (graphPullback dat ρ b₁.1 + graphPullback dat ρ b₂.1
        + cup11Fun (polarBihom q hq) b₂.1 b₁.1) ∈ B2 Γ (ZMod 2) := by
  obtain ⟨hb₁c, hb₁⟩ := mem_Z1_iff.mp b₁.2
  obtain ⟨hb₂c, hb₂⟩ := mem_Z1_iff.mp b₂.2
  refine AddSubgroup.mem_map.mpr ⟨fun g => dat.f (b₁.1 g) (b₂.1 g), ?_, ?_⟩
  · -- continuity of the correcting 1-cochain
    refine mem_C1_iff.mpr ?_
    have hF : Continuous fun g : Γ => ((b₁.1 g, b₂.1 g) : V × V) := hb₁c.prodMk hb₂c
    exact (continuous_of_discreteTopology (f := fun t : V × V => dat.f t.1 t.2)).comp hF
  · funext p
    obtain ⟨g, h⟩ := p
    have hgh₁ : b₁.1 (g * h) = b₁.1 g + ρ g • b₁.1 h := by rw [hb₁ g h, hρ]
    have hgh₂ : b₂.1 (g * h) = b₂.1 g + ρ g • b₂.1 h := by rw [hb₂ g h, hρ]
    have hm := hdat.m_quad (ρ g) (b₁.1 h) (b₂.1 h)
    have R₁ := hdat.f_cocycle (b₁.1 g) (b₂.1 g) (ρ g • b₁.1 h + ρ g • b₂.1 h)
    have R₂ := hdat.f_cocycle (b₁.1 g) (ρ g • b₁.1 h) (b₂.1 g + ρ g • b₂.1 h)
    have R₃ := hdat.f_cocycle (b₂.1 g) (ρ g • b₁.1 h) (ρ g • b₂.1 h)
    have R₄ := hdat.f_cocycle (ρ g • b₁.1 h) (b₂.1 g) (ρ g • b₂.1 h)
    have P := hdat.f_polar (b₂.1 g) (ρ g • b₁.1 h)
    rw [show b₂.1 g + (ρ g • b₁.1 h + ρ g • b₂.1 h)
        = ρ g • b₁.1 h + (b₂.1 g + ρ g • b₂.1 h) from by abel] at R₁
    rw [show ρ g • b₁.1 h + b₂.1 g = b₂.1 g + ρ g • b₁.1 h from by abel] at R₄
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_zmodTwo,
      Pi.sub_apply, Pi.add_apply, AddSubgroup.coe_add, graphPullback, cup11Fun,
      polarBihom_apply, smul_add]
    rw [hgh₁, hgh₂]
    simp only [hρ]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hm + R₁ + R₂ + R₃ + R₄ + P

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)] [DiscreteTopology C] [Finite C] [TopologicalSpace V]
  [DiscreteTopology V] [Finite V] [ContinuousSMul Γ V] [DistribMulAction Γ (MuN 2)]
  [ContinuousSMul Γ (MuN 2)] in
/-- A `Γ`-invariant form has `Γ`-invariant polar form. -/
theorem polar_smul_smul (q : V → ZMod 2) (hqG : ∀ (g : Γ) (v : V), q (g • v) = q v)
    (g : Γ) (a b : V) : polar q (g • a) (g • b) = polar q a b := by
  unfold GQ2.QuadraticFp2.polar
  rw [← smul_add, hqG, hqG, hqG]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)]
  [DiscreteTopology C] [Finite C] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [ContinuousSMul Γ V] [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)] in
/-- The polar pairing is `Γ`-equivariant for a `Γ`-invariant `q` (`𝔽₂` acts trivially). -/
theorem polarBihom_equivariant (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqG : ∀ (g : Γ) (v : V), q (g • v) = q v) (g : Γ) (v w : V) :
    polarBihom q hq (g • v) (g • w) = g • polarBihom q hq v w := by
  rw [smul_zmodTwo, polarBihom_apply, polarBihom_apply]
  exact polar_smul_smul q hqG g v w

omit [Finite C] [Finite V] in
/-- **Eq. (93), class level**: `Q⁰(x+y) = Q⁰(x) + Q⁰(y) + ι_F(y ∪_B x)`. -/
theorem Q0loc_add (D : TateDualityG Γ 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : Γ) (v : V), q (g • v) = q v) (x y : H1 Γ V) :
    Q0loc D dat ρ (x + y)
      = Q0loc D dat ρ x + Q0loc D dat ρ y
        + iotaF D (cup11 (polarBihom q hq)
            (polarBihom_equivariant q hq hqG) y x) := by
  classical
  have hmem₁ : graphPullback dat ρ (Quotient.out x).1 ∈ Z2 Γ (ZMod 2) :=
    graphPullback_mem_Z2 dat hdat ρ hρ _
  have hmem₂ : graphPullback dat ρ (Quotient.out y).1 ∈ Z2 Γ (ZMod 2) :=
    graphPullback_mem_Z2 dat hdat ρ hρ _
  have hmem₃ : cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1
      ∈ Z2 Γ (ZMod 2) :=
    cup11_mem_Z2 _ (polarBihom_equivariant q hq hqG) _ _
  have hrep : H2ofFun Γ (graphPullback dat ρ (Quotient.out (x + y)).1)
      = H2ofFun Γ (graphPullback dat ρ
          ((Quotient.out x + Quotient.out y : ↥(Z1 Γ V)) : Γ → V)) := by
    apply repIndep dat hdat ρ hρ
    rw [H1mk_out, map_add, H1mk_out, H1mk_out]
  have hsplit : H2ofFun Γ (graphPullback dat ρ
        ((Quotient.out x + Quotient.out y : ↥(Z1 Γ V)) : Γ → V))
      = H2ofFun Γ (graphPullback dat ρ (Quotient.out x).1
          + graphPullback dat ρ (Quotient.out y).1
          + cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1) :=
    h2ofFun_eq_of_sub_mem_B2 (graphPullback_add_sub_mem_B2 q hq dat hdat ρ hρ _ _)
  rw [Q0loc_apply, Q0loc_apply, Q0loc_apply, hrep, hsplit,
    H2ofFun_of_mem (add_mem (add_mem hmem₁ hmem₂) hmem₃),
    H2ofFun_of_mem hmem₁, H2ofFun_of_mem hmem₂]
  have hmk : (⟨graphPullback dat ρ (Quotient.out x).1
        + graphPullback dat ρ (Quotient.out y).1
        + cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1,
      add_mem (add_mem hmem₁ hmem₂) hmem₃⟩ : ↥(Z2 Γ (ZMod 2)))
      = ⟨graphPullback dat ρ (Quotient.out x).1, hmem₁⟩
        + ⟨graphPullback dat ρ (Quotient.out y).1, hmem₂⟩
        + ⟨cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1, hmem₃⟩ :=
    Subtype.ext rfl
  rw [hmk, map_add, map_add, map_add, map_add]
  congr 1
  conv_rhs => rw [← H1mk_out y, ← H1mk_out x, cup11_mk_mk]

omit [Finite C] [Finite V] in
/-- **Well-definedness of `Q⁰` (packet Prop. 6.6, first clause), usable form**: the value at a
class may be read off from *any* cocycle representative, not just `Quotient.out`. -/
theorem Q0loc_H1mk (D : TateDualityG Γ 2) {q : V → ZMod 2} (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q dat) (ρ : ContinuousMonoidHom Γ C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (b : ↥(Z1 Γ V)) :
    Q0loc D dat ρ (H1mk Γ V b) = iotaF D (H2ofFun Γ (graphPullback dat ρ b.1)) := by
  rw [Q0loc_apply]
  exact congrArg (iotaF D) (repIndep dat hdat ρ hρ _ b (H1mk_out _))

omit [Finite C] [Finite V] in
/-- **The polar form of `Q⁰` is the cup of the polar pairing through `ι_F`** — packet Prop. 6.6,
second clause: `B_{Q⁰}(x, y) = inv_Γ(y ∪_{b_q} x)`. -/
theorem polar_Q0loc (D : TateDualityG Γ 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : Γ) (v : V), q (g • v) = q v) (x y : H1 Γ V) :
    polar (Q0loc D dat ρ) x y
      = iotaF D (cup11 (polarBihom q hq)
          (polarBihom_equivariant q hq hqG) y x) := by
  unfold GQ2.QuadraticFp2.polar
  rw [Q0loc_add D q hq dat hdat ρ hρ hqG x y]
  linear_combination CharTwo.add_self_eq_zero (Q0loc D dat ρ x)
    + CharTwo.add_self_eq_zero (Q0loc D dat ρ y)

omit [Finite C] [Finite V] in
/-- **`Q⁰` is a quadratic map** on `H¹(Γ, V)` (eq. (93)): normalized, with biadditive polar
form. -/
theorem isQuadraticFp2_Q0loc (D : TateDualityG Γ 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : Γ) (v : V), q (g • v) = q v) :
    IsQuadraticFp2 (Q0loc D dat ρ (V := V)) := by
  constructor
  · -- normalization `Q⁰(0) = 0`
    have hzero : graphPullback dat ρ ((0 : ↥(Z1 Γ V)) : Γ → V) = 0 := by
      funext p
      show dat.f ((0 : Γ → V) p.1) (ρ p.1 • (0 : Γ → V) p.2) + dat.m (ρ p.1) ((0 : Γ → V) p.2) = 0
      simp only [Pi.zero_apply]
      rw [hdat.f_zero_left, hdat.m_zero, add_zero]
    have hrep0 : H2ofFun Γ (graphPullback dat ρ (Quotient.out (0 : H1 Γ V)).1)
        = H2ofFun Γ (graphPullback dat ρ ((0 : ↥(Z1 Γ V)) : Γ → V)) := by
      apply repIndep dat hdat ρ hρ
      rw [H1mk_out, map_zero]
    rw [Q0loc_apply, hrep0, hzero, H2ofFun_of_mem (zero_mem _),
      show (⟨(0 : Γ × Γ → ZMod 2), zero_mem _⟩ : ↥(Z2 Γ (ZMod 2))) = 0 from rfl,
      map_zero, map_zero]
  · -- polar additive, left
    intro u v w
    rw [polar_Q0loc D q hq dat hdat ρ hρ hqG, polar_Q0loc D q hq dat hdat ρ hρ hqG,
      polar_Q0loc D q hq dat hdat ρ hρ hqG, map_add, map_add]
  · -- polar additive, right
    intro u v w
    rw [polar_Q0loc D q hq dat hdat ρ hρ hqG, polar_Q0loc D q hq dat hdat ρ hρ hqG,
      polar_Q0loc D q hq dat hdat ρ hρ hqG, map_add, AddMonoidHom.add_apply, map_add]

end Polar

/-! ## §5 Nonsingularity — packet Prop. 6.6, third clause (B6 `perfect11`)

The `Γ`-generic form of `GQ2.DeepPart.nonsingular_Q0loc` and its support lemmas.  The route is
unchanged: the polar `μ₂`-self-duality of `V` moves a nonzero `H¹(Γ, V)`-class to a nonzero
`H¹(Γ, V′)`-class, and the bundle's `(1,1)`-perfectness produces a partner it cups
non-trivially against. -/

section Nonsingular

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]

omit [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] [DistribMulAction Γ (MuN 2)]
  [ContinuousSMul Γ (MuN 2)] in
/-- **Injectivity extraction from `perfect11`** at a general bundle — the `TateDualityG`-form of
`GQ2.TateDuality.exists_cup_ne_zero_of_ne_zero`: a nonzero `H¹(Γ, M′)`-class cups non-trivially
against some `H¹(Γ, M)`-class. -/
theorem exists_cup_ne_zero_of_ne_zero {n : ℕ} [NeZero n] [DistribMulAction Γ (MuN n)]
    [ContinuousSMul Γ (MuN n)] (D : TateDualityG Γ n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction Γ M] [ContinuousSMul Γ M] [Finite M] (htor : ∀ x : M, n • x = 0)
    {c : H1 Γ (MuDual n M)} (hc : c ≠ 0) :
    ∃ d : H1 Γ M, cup11 (muDualPairing n M) (muDualPairing_equivariant n M) c d ≠ 0 := by
  by_contra! hall
  apply hc
  apply (D.perfect11 M htor).1
  show D.inv.toAddMonoidHom.comp (cup11 (muDualPairing n M) (muDualPairing_equivariant n M) c)
      = D.inv.toAddMonoidHom.comp (cup11 (muDualPairing n M) (muDualPairing_equivariant n M) 0)
  ext d
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  rw [hall d, cup11_zero_left]

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V]

/-- The `μ₂`-valued polar self-duality `v ↦ (w ↦ bridge(B(v, w)))`. -/
noncomputable def polarMuDual (q : V → ZMod 2) (hq : IsQuadraticFp2 q) : V →+ MuDual 2 V :=
  postPairing (polarBihom q hq) SectionSix.muTwoOfF2

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)] [ContinuousSMul Γ (MuN 2)] [TopologicalSpace V]
  [DiscreteTopology V] [Finite V] [ContinuousSMul Γ V] in
/-- Equivariance of the polar `μ₂`-dual map. -/
theorem polarMuDual_equivariant (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqG : ∀ (g : Γ) (v : V), q (g • v) = q v) (g : Γ) (v : V) :
    polarMuDual q hq (g • v) = g • polarMuDual q hq v := by
  refine DFunLike.ext _ _ fun m => ?_
  rw [muDual_smul_apply, smul_muTwo]
  show SectionSix.muTwoOfF2 (polar q (g • v) m) = SectionSix.muTwoOfF2 (polar q v (g⁻¹ • m))
  congr 1
  have hps := polar_smul_smul (Γ := Γ) q hqG g v (g⁻¹ • m)
  rw [smul_inv_smul] at hps
  exact hps

omit [TopologicalSpace V] [DiscreteTopology V] [DistribMulAction Γ V] [ContinuousSMul Γ V] in
/-- `#Hom(V, μ₂) = #V` for exponent-2 `V`. -/
theorem card_muDual (h2 : ∀ v : V, v + v = 0) : Nat.card (MuDual 2 V) = Nat.card V := by
  have h1 : Nat.card (MuDual 2 V) = Nat.card (V →+ ZMod 2) := by
    refine Nat.card_congr ⟨fun f =>
        DeepPart.zmodTwoEquivMuTwo.symm.toAddMonoidHom.comp (f : V →+ MuN 2),
      fun f => (DeepPart.zmodTwoEquivMuTwo.toAddMonoidHom.comp f : MuDual 2 V),
      fun f => ?_, fun f => ?_⟩
    · refine DFunLike.ext _ _ fun m => ?_
      show DeepPart.zmodTwoEquivMuTwo
          (DeepPart.zmodTwoEquivMuTwo.symm ((f : V →+ MuN 2) m)) = f m
      rw [AddEquiv.apply_symm_apply]
    · ext m
      show DeepPart.zmodTwoEquivMuTwo.symm (DeepPart.zmodTwoEquivMuTwo (f m)) = f m
      rw [AddEquiv.symm_apply_apply]
  rw [h1, card_addHom_zmod2 V h2]

omit [TopologicalSpace V] [DiscreteTopology V] [DistribMulAction Γ V] [ContinuousSMul Γ V] in
/-- The polar `μ₂`-dual map is bijective (nonsingularity + counting). -/
theorem polarMuDual_bijective (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2 : ∀ v : V, v + v = 0) :
    Function.Bijective (polarMuDual q hq (V := V)) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (MuDual 2 V) := Fintype.ofFinite _
  have hinj : Function.Injective (polarMuDual q hq (V := V)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    obtain ⟨w, hw⟩ := hns v hne
    apply hw
    have h0 : SectionSix.muTwoOfF2 (polar q v w) = 0 := by
      have := DFunLike.congr_fun hv w
      rwa [MuDual.zero_apply] at this
    exact DeepPart.muTwoOfF2_injective (by rw [h0, map_zero])
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_muDual h2]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)] [AddCommGroup V] [TopologicalSpace V]
  [DiscreteTopology V] [Finite V] [DistribMulAction Γ V] [ContinuousSMul Γ V] in
/-- **`mapCoeff1` of an equivariant additive bijection is injective** (coboundaries pull back
along the inverse). -/
theorem mapCoeff1_injective {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [DiscreteTopology A] [DiscreteTopology B]
    [DistribMulAction Γ A] [ContinuousSMul Γ A] [DistribMulAction Γ B] [ContinuousSMul Γ B]
    (f : A →+ B) (hf : Continuous f) (hcompat : ∀ (g : Γ) (a : A), f (g • a) = g • f a)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) :
    Function.Injective (mapCoeff1 f hf hcompat) := by
  rw [injective_iff_map_eq_zero]
  intro xq
  induction xq using QuotientAddGroup.induction_on with
  | H b =>
    intro hxq
    have hxq' : H1mk Γ B
        (Z1comap (ContinuousMonoidHom.id Γ) f hf (fun g n => hcompat g n) b) = 0 := hxq
    have hmem := (QuotientAddGroup.eq_zero_iff _).mp hxq'
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨n, hn⟩ := hmem
    obtain ⟨m, rfl⟩ := hsurj n
    show H1mk Γ A b = 0
    refine (QuotientAddGroup.eq_zero_iff b).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨m, ?_⟩
    funext g
    apply hinj
    have hg := congrFun hn g
    show f (g • m - m) = f (b.1 g)
    rw [map_sub, hcompat]
    exact hg

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] [ContinuousSMul Γ (MuN 2)]
  [Finite V] in
/-- **Cup coefficient naturality at the polar pairing**: pushing the `𝔽₂`-valued polar cup along
the `μ₂`-bridge is the `μ₂`-evaluation cup against the polar `μ₂`-dual class. -/
theorem mapCoeff2_muTwo_cup (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqG : ∀ (g : Γ) (v : V), q (g • v) = q v) (y x : H1 Γ V) :
    mapCoeff2 SectionSix.muTwoOfF2 continuous_of_discreteTopology muTwoOfF2_equivariant
        (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) y x)
      = cup11 (muDualPairing 2 V) (muDualPairing_equivariant 2 V)
          (mapCoeff1 (polarMuDual q hq) continuous_of_discreteTopology
            (polarMuDual_equivariant q hq hqG) y) x := by
  induction y using QuotientAddGroup.induction_on with
  | H b =>
    induction x using QuotientAddGroup.induction_on with
    | H a => rfl

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction C V]

/-- **`Q⁰` is nonsingular** — packet Prop. 6.6, third clause: its polar form is a perfect pairing
on `H¹(Γ, V)`, via the bundle's `perfect11` clause (B6) through the polar `μ₂`-self-duality. -/
theorem nonsingular_Q0loc (D : TateDualityG Γ 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2 : ∀ v : V, v + v = 0)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : Γ) (v : V), q (g • v) = q v) :
    Nonsingular (Q0loc D dat ρ (V := V)) := by
  intro x hx
  have htor : ∀ v : V, (2 : ℕ) • v = 0 := fun v => (two_nsmul v).trans (h2 v)
  have hbij := polarMuDual_bijective q hq hns h2
  have hxne : mapCoeff1 (polarMuDual q hq) continuous_of_discreteTopology
      (polarMuDual_equivariant q hq hqG) x ≠ 0 := by
    intro h0
    exact hx (mapCoeff1_injective _ _ _ hbij.1 hbij.2 (by rw [h0, map_zero]))
  obtain ⟨d, hd⟩ := exists_cup_ne_zero_of_ne_zero D V htor hxne
  refine ⟨d, ?_⟩
  rw [polar_comm, polar_Q0loc D q hq dat hdat ρ hρ hqG d x]
  have hnat := mapCoeff2_muTwo_cup q hq hqG x d
  intro h0
  apply hd
  have hz : mapCoeff2 SectionSix.muTwoOfF2 continuous_of_discreteTopology
      muTwoOfF2_equivariant
      (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) x d) = 0 := by
    apply D.inv.injective
    rw [map_zero]
    exact h0
  rwa [hnat] at hz

end Nonsingular

/-! ## §6 Local dualizing sources: open finite-index subgroups

`GQ2.IsLocalDualizingGroup` (`GQ2/TateDuality.lean`) is the truth-side hypothesis gating the
base-generalized B6 axiom `GQ2.tateDualityAt`.  `GQ2.ker_isLocalDualizingGroup`
(`GQ2/DeepDualityK.lean`) covers `ker ρ ≤ G_ℚ₂` only; the dyadic lane needs the general open
finite-index subgroup `G_K = ↥U` and the *nested* case `N ≤ ↥U ≤ G_ℚ₂`. -/

section DualizingSources

/-- **Every open finite-index subgroup of `G_ℚ₂` is a local dualizing group** — the subtype
embedding is an open embedding onto `W` itself, and the `μₙ`-action is restriction. -/
theorem subgroup_isLocalDualizingGroup (n : ℕ) [NeZero n] (W : Subgroup AbsGalQ2)
    (hW : IsOpen (W : Set AbsGalQ2)) [W.FiniteIndex] : IsLocalDualizingGroup ↥W n := by
  refine ⟨W.subtype, hW.isOpenEmbedding_subtypeVal, ?_, fun _ _ => rfl⟩
  rw [Subgroup.range_subtype]
  infer_instance

/-- **Transitivity of the dualizing hypothesis along an open finite-index embedding**: if `Γ` is
a local dualizing group and `G` embeds openly in `Γ` with finite-index image (compatibly on
`μₙ`), then `G` is a local dualizing group.  This is the nested case `N ≤ ↥U ≤ G_ℚ₂`. -/
theorem isLocalDualizingGroup_of_openEmbedding {n : ℕ} [NeZero n] {G Γ : Type}
    [Group G] [TopologicalSpace G] [DistribMulAction G (MuN n)]
    [Group Γ] [TopologicalSpace Γ] [DistribMulAction Γ (MuN n)]
    (hΓ : IsLocalDualizingGroup Γ n) (ι : G →* Γ) (hι : Topology.IsOpenEmbedding ι)
    (hfi : (ι.range).FiniteIndex) (hsmul : ∀ (g : G) (x : MuN n), g • x = ι g • x) :
    IsLocalDualizingGroup G n := by
  obtain ⟨j, hjemb, hjfi, hjsmul⟩ := hΓ
  refine ⟨j.comp ι, hjemb.comp hι, ?_, fun g x => by rw [hsmul, hjsmul]; rfl⟩
  -- `(j ∘ ι).range = j(ι.range)`, and `index_map` splits the index in the injective case
  have hmap : (j.comp ι).range = (ι.range).map j := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨ι g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨g, rfl⟩, rfl⟩; exact ⟨g, rfl⟩
  have hker : j.ker = ⊥ := (MonoidHom.ker_eq_bot_iff j).mpr hjemb.injective
  refine ⟨?_⟩
  rw [hmap, Subgroup.index_map, hker, sup_bot_eq]
  exact Nat.mul_ne_zero hfi.index_ne_zero hjfi.index_ne_zero

end DualizingSources

/-! ## §7 Group-side transport of `Hⁱ`

The single mitigation for the nested-subtype friction flagged in the design memo (§2, §7.2): the
same abstract group may be presented as `↥(N)` for `N : Subgroup ↥U` or as `↥(N.map U.subtype)`
for a subgroup of `G_ℚ₂`.  Transport `Hⁱ` along a `ContinuousMulEquiv` with a matched coefficient
`AddEquiv`, in all three degrees.  (Memo item L6.) -/

section GroupCongr

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
variable {M' : Type*} [AddCommGroup M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
  [DistribMulAction G' M'] [ContinuousSMul G' M']
variable (e : ContinuousMulEquiv G G') (f : M ≃+ M') (hf : Continuous f)
  (hf' : Continuous f.symm) (hcompat : ∀ (g : G) (m : M), f (g • m) = e g • f m)

/-- The forward `ContinuousMonoidHom` of a `ContinuousMulEquiv`. -/
def congrHom : ContinuousMonoidHom G G' := ⟨e.toMonoidHom, e.continuous_toFun⟩

/-- The backward `ContinuousMonoidHom` of a `ContinuousMulEquiv`. -/
def congrHomSymm : ContinuousMonoidHom G' G := ⟨e.symm.toMonoidHom, e.symm.continuous_toFun⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
/-- `congrHomSymm` undoes `congrHom`. -/
theorem congrHomSymm_congrHom (g : G) : congrHomSymm e (congrHom e g) = g :=
  e.symm_apply_apply g

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
/-- `congrHom` undoes `congrHomSymm`. -/
theorem congrHom_congrHomSymm (g' : G') : congrHom e (congrHomSymm e g') = g' :=
  e.apply_symm_apply g'

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul G M] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousSMul G' M'] in
include hcompat in
/-- The matched coefficient equivalence along the backward group map (the direction the `comap`
of the *forward* transport needs). -/
theorem congr_compat_fwd (g' : G') (m : M) : f (congrHomSymm e g' • m) = g' • f m := by
  rw [hcompat]
  exact congrArg (fun z => z • f m) (congrHom_congrHomSymm e g')

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul G M] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousSMul G' M'] in
include hcompat in
/-- The matched coefficient equivalence along the forward group map, on the inverse
coefficients. -/
theorem congr_compat_bwd (g : G) (m' : M') : f.symm (congrHom e g • m') = g • f.symm m' := by
  apply f.injective
  rw [f.apply_symm_apply, hcompat, f.apply_symm_apply]
  rfl

/-- **`H⁰` group-side transport.** -/
def H0congrGroup : ↥(H0 G M) ≃+ ↥(H0 G' M') where
  toFun := H0comap (congrHomSymm e) f.toAddMonoidHom (congr_compat_fwd e f hcompat)
  invFun := H0comap (congrHom e) f.symm.toAddMonoidHom (congr_compat_bwd e f hcompat)
  left_inv x := Subtype.ext (f.symm_apply_apply x.1)
  right_inv x := Subtype.ext (f.apply_symm_apply x.1)
  map_add' _ _ := map_add _ _ _

/-- **`H¹` group-side transport** — the memo's `H1congrGroup`. -/
noncomputable def H1congrGroup : H1 G M ≃+ H1 G' M' where
  toFun := H1comap (congrHomSymm e) f.toAddMonoidHom hf (congr_compat_fwd e f hcompat)
  invFun := H1comap (congrHom e) f.symm.toAddMonoidHom hf' (congr_compat_bwd e f hcompat)
  left_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      refine congrArg (H1mk G M) (Subtype.ext (funext fun g => ?_))
      show f.symm (f (a.1 (congrHomSymm e (congrHom e g)))) = a.1 g
      rw [f.symm_apply_apply, congrHomSymm_congrHom]
  right_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      refine congrArg (H1mk G' M') (Subtype.ext (funext fun g => ?_))
      show f (f.symm (a.1 (congrHom e (congrHomSymm e g)))) = a.1 g
      rw [f.apply_symm_apply, congrHom_congrHomSymm]
  map_add' := map_add _

/-- **`H²` group-side transport.** -/
noncomputable def H2congrGroup : H2 G M ≃+ H2 G' M' where
  toFun := H2comap (congrHomSymm e) f.toAddMonoidHom hf (congr_compat_fwd e f hcompat)
  invFun := H2comap (congrHom e) f.symm.toAddMonoidHom hf' (congr_compat_bwd e f hcompat)
  left_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      refine congrArg (H2mk G M) (Subtype.ext (funext fun p => ?_))
      show f.symm (f (a.1 (congrHomSymm e (congrHom e p.1),
        congrHomSymm e (congrHom e p.2)))) = a.1 p
      rw [f.symm_apply_apply, congrHomSymm_congrHom, congrHomSymm_congrHom]
  right_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      refine congrArg (H2mk G' M') (Subtype.ext (funext fun p => ?_))
      show f (f.symm (a.1 (congrHom e (congrHomSymm e p.1),
        congrHom e (congrHomSymm e p.2)))) = a.1 p
      rw [f.apply_symm_apply, congrHom_congrHomSymm, congrHom_congrHomSymm]
  map_add' := map_add _

end GroupCongr

/-! ## §8 The `n = 1` regression: the retype is definitionally the ℚ₂ layer

At `Γ := AbsGalQ2` the group-generic declarations reduce **on the nose** (`rfl`) to the ℚ₂
originals — the retype changed no mathematics, only the ambient binder.  LG5's `n = 1` pins can
rewrite along these. -/

section Q2Regression

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- `ι_F` at `Γ = G_ℚ₂` is `GQ2.SectionSix.iotaF`. -/
theorem iotaF_absGalQ2 (D : TateDuality 2) : iotaF D = SectionSix.iotaF D := rfl

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **`n = 1` regression**: `Q⁰` at `Γ = G_ℚ₂` is `GQ2.SectionSix.Q0loc`. -/
theorem Q0loc_absGalQ2 (D : TateDuality 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) :
    Q0loc D dat ρ (V := V) = SectionSix.Q0loc D dat ρ := rfl

end Q2Regression

end GQ2.Dyadic
