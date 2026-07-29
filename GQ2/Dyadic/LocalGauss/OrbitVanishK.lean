/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.LocalGauss.Q0
import GQ2.OrbitVanish

/-!
# The Lemma-6.17 vanishing reducer over a general local source (LG4c, part 1)

`GQ2/OrbitVanish.lean` retyped from `G_ℚ₂` to an arbitrary topological group `Γ` carrying a local
Tate-duality bundle `D : TateDualityG Γ 2` (LG2's parameterization, `LocalGauss/Q0.lean`).  In the
dyadic campaign `Γ = G_K = ↥U` for `U ≤ G_ℚ₂` open of finite index.  The `ℚ₂` original is untouched
(design memo `docs/dyadic/lg-design.md` §2: clone, zero in-place edits).

## What actually needed retyping

Most of `GQ2/OrbitVanish.lean` is **already ambient-free** — the `ℚ₂` file's section variables carry
`[DistribMulAction AbsGalQ2 V]` but every declaration below `§DatumSum` `omit`s it, so the following
are consumed **verbatim** at any `Γ` (checked by `#check`; no clone):

* `GQ2.OrbitVanish.sumDatum`, `graphPullback_sumDatum` (the datum-additivity brick);
* `GQ2.OrbitVanish.H2ofFun_sum_of_mem_Z2` (the `H²` additivity backbone, stated over abstract `G`);
* `GQ2.OrbitVanish.diffDatum`, `graphPullback_diffDatum`, `isEquivariantFactorSet_diffDatum`;
* `GQ2.OrbitVanish.exists_refinement_of_zero_form`, `exists_equivariant_refinement` (increments
  A + B of the datum-independence core — pure `𝔽₂`-linear algebra plus the odd-normal averaging).

What is `AbsGalQ2`-typed, and is retyped here, is exactly the layer that mentions the **ambient
cohomology** `H²(G_ℚ₂, 𝔽₂)`, the corestriction `cor2Fun` from an open subgroup, and `Q⁰_loc`:

* §1 the corestriction-of-coboundary bridge (`H2ofFun_cor2Fun_coboundary_eq_zero_K`,
  `H2ofFun_cor2Fun_eq_zero_of_H2_eq_zero_K`);
* §2 the vanishing assembly (`Q0loc_vanish_of_orbit_sum_K`);
* §3 the `hexp` reducer and the full reducer (`Q0loc_eq_orbit_sum_of_decomp_K`,
  `Q0loc_vanish_of_decomp_K`);
* §4 the datum-level reducer (`Q0loc_vanish_of_datum_decomp_K`) — the shape the LG4c assembly
  consumes;
* §5 `Q⁰_loc` datum-independence (`Q0loc_datum_indep_K`), needed to move from the caller's
  arbitrary equivariant factor set to the orbit-sum datum on the regular module.

## Trivial coefficients

The `ℚ₂` file uses the `rfl`-lemma `GQ2.absGal_smul_zmodTwo`; at a general `Γ` the replacement is
LG2's `GQ2.Dyadic.smul_zmodTwo` (a *theorem*, not `rfl`), so every place the `ℚ₂` proof relied on
definitional triviality of the `𝔽₂`-action becomes an explicit rewrite (the LG2 `smul` trap).

Axioms: everything is parametrized over the bundle `D`, so `#print axioms` is the standard three
throughout — exactly as for the `ℚ₂` models.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh GQ2.Corestriction GQ2.SectionSix

/-! ## §1 The corestriction-of-coboundary bridge

`GQ2.OrbitVanish.H2ofFun_cor2Fun_coboundary_eq_zero` (`GQ2/OrbitVanish.lean` :53) and its
class-level form (:87), retyped.  The only change is `absGal_smul_zmodTwo ↦ smul_zmodTwo`. -/

section CorestrictionBridge

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

/-- **Corestriction of a coboundary vanishes in `H²`** — `GQ2.OrbitVanish` :53 retyped: if
`inner = δ¹c` is the trivial-action coboundary of a continuous 1-cochain `c : ↥U → 𝔽₂` on an open
finite-index `U ≤ Γ`, then `cor2Fun U inner` is `0` in `H²(Γ, 𝔽₂)`.

`cor2Fun_dOne` rewrites `cor2Fun U (δ¹c) = δ¹(cor1Fun U c)`, the coboundary of the continuous
cochain `cor1Fun U c` (`continuous_lTrans'`), so it lies in `B²`. -/
theorem H2ofFun_cor2Fun_coboundary_eq_zero_K (U : Subgroup Γ) [Finite (Γ ⧸ U)]
    (hUo : IsOpen (U : Set Γ)) (c : ↥U → ZMod 2) (hc : Continuous c) :
    H2ofFun Γ (cor2Fun U (fun ab => c ab.2 - c (ab.1 * ab.2) + c ab.1)) = 0 := by
  classical
  haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _
  -- (1) `cor2Fun` of the coboundary form = `δ¹(cor1Fun c)` (trivial `𝔽₂`-action)
  have hcor : cor2Fun U (fun ab => c ab.2 - c (ab.1 * ab.2) + c ab.1)
      = dOne Γ (ZMod 2) (cor1Fun U c) := by
    rw [cor2Fun_dOne U c]
    funext p
    show cor1Fun U c p.2 - cor1Fun U c (p.1 * p.2) + cor1Fun U c p.1
        = p.1 • cor1Fun U c p.2 - cor1Fun U c (p.1 * p.2) + cor1Fun U c p.1
    rw [smul_zmodTwo]
  -- (2) `cor1Fun c` is continuous (finite sum of `c ∘ ℓ_u`, each continuous)
  have hcont : Continuous (cor1Fun U c) := by
    have hEq : cor1Fun U c = fun γ => ∑ u : Γ ⧸ U, c (lTrans U u γ) := by
      funext γ; exact finsum_eq_sum_of_fintype _
    rw [hEq]
    exact continuous_finsetSum _ fun u _ => hc.comp (ShapiroLedger.continuous_lTrans' U hUo u)
  -- (3) hence the corestriction lies in `B²`, so its `H²`-class is `0`
  have hz : H2ofFun Γ (0 : Γ × Γ → ZMod 2) = 0 := by
    rw [H2ofFun_of_mem (zero_mem _)]; exact map_zero _
  rw [← hz]
  exact ShapiroLedger.H2ofFun_eq_of_sub_mem_B2
    (by rw [sub_zero, hcor]; exact ⟨cor1Fun U c, hcont, rfl⟩)

/-- **Class-level form** — `GQ2.OrbitVanish` :87 retyped: if a 2-cocycle `inner` on `↥U` has
trivial class in `H²(↥U, 𝔽₂)`, its degree-2 corestriction vanishes in `H²(Γ, 𝔽₂)`.  This is the
shape the per-orbit outputs feed. -/
theorem H2ofFun_cor2Fun_eq_zero_of_H2_eq_zero_K (U : Subgroup Γ) [Finite (Γ ⧸ U)]
    (hUo : IsOpen (U : Set Γ)) (inner : ↥U × ↥U → ZMod 2)
    (hZ2 : inner ∈ Z2 ↥U (ZMod 2)) (h0 : H2ofFun ↥U inner = 0) :
    H2ofFun Γ (cor2Fun U inner) = 0 := by
  -- `H² = 0` ⟹ `inner ∈ B²(↥U)` ⟹ `inner = δ¹c` for a continuous `c`
  rw [H2ofFun_of_mem hZ2] at h0
  have hmem : ((⟨inner, hZ2⟩ : Z2 ↥U (ZMod 2)) : ↥U × ↥U → ZMod 2) ∈ B2 ↥U (ZMod 2) := by
    have h := (QuotientAddGroup.eq_zero_iff _).mp h0
    rwa [AddSubgroup.mem_addSubgroupOf] at h
  simp only [B2, AddSubgroup.mem_map] at hmem
  obtain ⟨c, hc, hceq⟩ := hmem
  -- rewrite `inner` in the trivial-action coboundary form and apply the cochain bridge
  have hform : inner = fun ab => c ab.2 - c (ab.1 * ab.2) + c ab.1 := by
    rw [← hceq]; funext ab
    show ab.1 • c ab.2 - c (ab.1 * ab.2) + c ab.1 = c ab.2 - c (ab.1 * ab.2) + c ab.1
    rw [smul_zmodTwo]
  rw [hform]
  exact H2ofFun_cor2Fun_coboundary_eq_zero_K U hUo c hc

end CorestrictionBridge

/-! ## §2 The Lemma-6.17 vanishing assembly

`GQ2.OrbitVanish.Q0loc_vanish_of_orbit_sum` (:127) retyped. -/

section Assembly

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- **The Lemma-6.17 vanishing assembly** at a general local source: if `Q⁰_loc` at a class `x`
decomposes as a finite sum of per-orbit corestriction contributions (`hexp`) and each orbit's inner
2-cocycle vanishes in the subgroup's `H²` (`hvanish`), then `Q⁰_loc x = 0`. -/
theorem Q0loc_vanish_of_orbit_sum_K (D : TateDualityG Γ 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C) (x : H1 Γ V)
    {ι : Type*} (s : Finset ι) (U : ι → Subgroup Γ)
    (hfin : ∀ o ∈ s, Finite (Γ ⧸ U o))
    (hopen : ∀ o ∈ s, IsOpen (U o : Set Γ))
    (inner : (o : ι) → ↥(U o) × ↥(U o) → ZMod 2)
    (hZ2 : ∀ o ∈ s, inner o ∈ Z2 ↥(U o) (ZMod 2))
    (hexp : Q0loc D dat ρ x = ∑ o ∈ s, iotaF D (H2ofFun Γ (cor2Fun (U o) (inner o))))
    (hvanish : ∀ o ∈ s, H2ofFun ↥(U o) (inner o) = 0) :
    Q0loc D dat ρ x = 0 := by
  rw [hexp]
  refine Finset.sum_eq_zero fun o ho => ?_
  haveI := hfin o ho
  rw [H2ofFun_cor2Fun_eq_zero_of_H2_eq_zero_K (U o) (hopen o ho) (inner o) (hZ2 o ho)
    (hvanish o ho), map_zero]

end Assembly

/-! ## §3 The `hexp` reducer and the full reducer

`GQ2.OrbitVanish.Q0loc_eq_orbit_sum_of_decomp` (:201) and `Q0loc_vanish_of_decomp` (:220),
retyped.  `H2ofFun_sum_of_mem_Z2` (the additivity backbone) is consumed verbatim from the `ℚ₂`
file — it is already stated over an abstract `G`. -/

section Reducer

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- **The `hexp` producer** at a general local source: from the raw cochain decomposition
`hdecomp` and the Lemma-6.15 cohomologies `hcoh`, `Q⁰_loc x` is the orbit sum consumed by
`Q0loc_vanish_of_orbit_sum_K`. -/
theorem Q0loc_eq_orbit_sum_of_decomp_K (D : TateDualityG Γ 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C) (x : H1 Γ V)
    {ι : Type*} (s : Finset ι) (φ : ι → Γ × Γ → ZMod 2)
    (hφZ2 : ∀ o ∈ s, φ o ∈ Z2 Γ (ZMod 2))
    (hdecomp : graphPullback dat ρ (Quotient.out x).1 = ∑ o ∈ s, φ o)
    (U : ι → Subgroup Γ) (inner : (o : ι) → ↥(U o) × ↥(U o) → ZMod 2)
    (hcoh : ∀ o ∈ s, H2ofFun Γ (φ o) = H2ofFun Γ (cor2Fun (U o) (inner o))) :
    Q0loc D dat ρ x = ∑ o ∈ s, iotaF D (H2ofFun Γ (cor2Fun (U o) (inner o))) := by
  show iotaF D (H2ofFun Γ (graphPullback dat ρ (Quotient.out x).1)) = _
  rw [hdecomp, OrbitVanish.H2ofFun_sum_of_mem_Z2 s φ hφZ2, map_sum]
  exact Finset.sum_congr rfl fun o ho => congrArg (iotaF D) (hcoh o ho)

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- **The full vanishing reducer** at a general local source: from the raw per-orbit cochain
decomposition `hdecomp`, the Lemma-6.15 cohomologies `hcoh`, and the deep-class per-orbit
vanishing `hvanish`, `Q⁰_loc x = 0`. -/
theorem Q0loc_vanish_of_decomp_K (D : TateDualityG Γ 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C) (x : H1 Γ V)
    {ι : Type*} (s : Finset ι) (φ : ι → Γ × Γ → ZMod 2)
    (hφZ2 : ∀ o ∈ s, φ o ∈ Z2 Γ (ZMod 2))
    (hdecomp : graphPullback dat ρ (Quotient.out x).1 = ∑ o ∈ s, φ o)
    (U : ι → Subgroup Γ) (hfin : ∀ o ∈ s, Finite (Γ ⧸ U o))
    (hopen : ∀ o ∈ s, IsOpen (U o : Set Γ))
    (inner : (o : ι) → ↥(U o) × ↥(U o) → ZMod 2) (hZ2 : ∀ o ∈ s, inner o ∈ Z2 ↥(U o) (ZMod 2))
    (hcoh : ∀ o ∈ s, H2ofFun Γ (φ o) = H2ofFun Γ (cor2Fun (U o) (inner o)))
    (hvanish : ∀ o ∈ s, H2ofFun ↥(U o) (inner o) = 0) :
    Q0loc D dat ρ x = 0 :=
  Q0loc_vanish_of_orbit_sum_K D dat ρ x s U hfin hopen inner hZ2
    (Q0loc_eq_orbit_sum_of_decomp_K D dat ρ x s φ hφZ2 hdecomp U inner hcoh) hvanish

end Reducer

/-! ## §4 The datum-level reducer

`GQ2.OrbitVanish.Q0loc_vanish_of_datum_decomp` (:298) retyped — the shape the LG4c assembly
(`LocalGauss/VanishCloseK.lean`) consumes.  The datum-additivity brick
`GQ2.OrbitVanish.graphPullback_sumDatum` is ambient-free and used verbatim. -/

section DatumReducer

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

omit [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- **The datum-level vanishing reducer** at a general local source: if the (regular-module) datum
decomposes as a pointwise sum of per-orbit equivariant factor sets `dat = Σ_o datf_o` (`hdat_eq`),
each per-orbit pullback is cohomologous to its Lemma-6.15 corestriction (`hcoh`), and each
corestriction's inner cocycle vanishes in the subgroup's `H²` (`hvanish`), then `Q⁰_loc x = 0`. -/
theorem Q0loc_vanish_of_datum_decomp_K (D : TateDualityG Γ 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (x : H1 Γ V)
    {ι : Type*} (s : Finset ι) (datf : ι → FactorSet C V)
    (qf : ι → V → ZMod 2) (hdatf : ∀ o ∈ s, IsEquivariantFactorSet (qf o) (datf o))
    (hdat_eq : dat = OrbitVanish.sumDatum s datf)
    (U : ι → Subgroup Γ) (hfin : ∀ o ∈ s, Finite (Γ ⧸ U o))
    (hopen : ∀ o ∈ s, IsOpen (U o : Set Γ))
    (inner : (o : ι) → ↥(U o) × ↥(U o) → ZMod 2) (hZ2 : ∀ o ∈ s, inner o ∈ Z2 ↥(U o) (ZMod 2))
    (hcoh : ∀ o ∈ s, H2ofFun Γ (graphPullback (datf o) ρ (Quotient.out x).1)
      = H2ofFun Γ (cor2Fun (U o) (inner o)))
    (hvanish : ∀ o ∈ s, H2ofFun ↥(U o) (inner o) = 0) :
    Q0loc D dat ρ x = 0 := by
  refine Q0loc_vanish_of_decomp_K D dat ρ x s
    (fun o => graphPullback (datf o) ρ (Quotient.out x).1)
    (fun o ho => graphPullback_mem_Z2 (datf o) (hdatf o ho) ρ hρ (Quotient.out x))
    ?_ U hfin hopen inner hZ2 hcoh hvanish
  rw [hdat_eq]
  exact OrbitVanish.graphPullback_sumDatum s datf (⇑ρ) (Quotient.out x).1

end DatumReducer

/-! ## §5 `Q⁰_loc` datum-independence

`GQ2.OrbitVanish.Q0loc_datum_indep_of_core` (:419), `graphPullback_mem_B2_of_refinement` (:669),
`Q0loc_datum_indep_of_refinement` (:693) and `Q0loc_datum_indep` (:711), retyped.  The two
existence increments A/B (`exists_refinement_of_zero_form`, `exists_equivariant_refinement`) and
the difference-datum brick are ambient-free and consumed verbatim. -/

section DatumIndependence

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- **`Q⁰_loc` datum-independence, parametric on DI-core** at a general local source: if the graph
pullback of the zero-form difference datum lands in `B²`, then `Q⁰_loc` agrees for the two
equivariant factor sets. -/
theorem Q0loc_datum_indep_of_core_K (D : TateDualityG Γ 2) (dat1 dat2 : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C) (x : H1 Γ V)
    (hcore : graphPullback (OrbitVanish.diffDatum dat1 dat2) ρ (Quotient.out x).1
      ∈ B2 Γ (ZMod 2)) :
    Q0loc D dat1 ρ x = Q0loc D dat2 ρ x := by
  show iotaF D (H2ofFun Γ (graphPullback dat1 ρ (Quotient.out x).1))
      = iotaF D (H2ofFun Γ (graphPullback dat2 ρ (Quotient.out x).1))
  refine congrArg _ (ShapiroLedger.H2ofFun_eq_of_sub_mem_B2 ?_)
  have hlin : graphPullback dat1 ρ (Quotient.out x).1 - graphPullback dat2 ρ (Quotient.out x).1
      = graphPullback (OrbitVanish.diffDatum dat1 dat2) ρ (Quotient.out x).1 := by
    rw [OrbitVanish.graphPullback_diffDatum]
    funext p
    simp only [Pi.sub_apply, Pi.add_apply, CharTwo.sub_eq_add]
  rw [hlin]; exact hcore

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] [DistribMulAction Γ (MuN 2)]
  [ContinuousSMul Γ (MuN 2)] [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- **The DI-core cochain assembly** at a general local source: a quadratic refinement `Δφ` of a
zero-form factor set gives the explicit `B²`-witness `Λ(g) = Δφ(b g)` for its graph pullback.
(The `ℚ₂` model's `absGal_smul_zmodTwo` becomes the LG2 rewrite `smul_zmodTwo`.) -/
private theorem graphPullback_mem_B2_of_refinement_K (Δdat : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (Δφ : V → ZMod 2)
    (hQ : ∀ u w : V, Δφ (u + w) = Δφ u + Δφ w + Δdat.f u w)
    (hE : ∀ (c : C) (v : V), Δφ (c • v) = Δφ v + Δdat.m c v)
    (b : Z1 Γ V) :
    graphPullback Δdat ρ b.1 ∈ B2 Γ (ZMod 2) := by
  obtain ⟨hbc, hb⟩ := mem_Z1_iff.mp b.2
  refine AddSubgroup.mem_map.mpr ⟨fun g => Δφ (b.1 g), ?_, ?_⟩
  · exact mem_C1_iff.mpr ((continuous_of_discreteTopology (f := Δφ)).comp hbc)
  · funext p
    obtain ⟨g, h⟩ := p
    have hbgh : b.1 (g * h) = b.1 g + ρ g • b.1 h := by rw [hb g h, hρ]
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_zmodTwo, graphPullback]
    rw [hbgh]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hQ (b.1 g) (ρ g • b.1 h) + hE (ρ g) (b.1 h)

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul Γ V] in
/-- **`Q⁰_loc` datum-independence from a refinement** at a general local source. -/
theorem Q0loc_datum_indep_of_refinement_K (D : TateDualityG Γ 2) (dat1 dat2 : FactorSet C V)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (x : H1 Γ V) (Δφ : V → ZMod 2)
    (hQ : ∀ u w : V, Δφ (u + w) = Δφ u + Δφ w + (OrbitVanish.diffDatum dat1 dat2).f u w)
    (hE : ∀ (c : C) (v : V), Δφ (c • v) = Δφ v + (OrbitVanish.diffDatum dat1 dat2).m c v) :
    Q0loc D dat1 ρ x = Q0loc D dat2 ρ x :=
  Q0loc_datum_indep_of_core_K D dat1 dat2 ρ x
    (graphPullback_mem_B2_of_refinement_K (OrbitVanish.diffDatum dat1 dat2) ρ hρ Δφ hQ hE
      (Quotient.out x))

omit [DiscreteTopology C] [ContinuousSMul Γ V] in
/-- **`Q⁰_loc` datum-independence** at a general local source (`GQ2.OrbitVanish.Q0loc_datum_indep`
retyped): for two equivariant factor sets `dat1`, `dat2` of the **same** form `q`, an odd normal
subgroup `I ◁ C` acting fixed-point-freely forces `Q⁰_loc dat1 = Q⁰_loc dat2`.  The tame
instantiation of `(I, hIn, hodd, hVI)` stays with the caller — in the dyadic campaign it is the
general-`q` tame inertia `⟨t⟩` through PJ1's `tame_zpowers_normal_pow` / `tame_odd_order_pow`,
*not* the `ℚ₂` `Ttame`-hardcoded `tameInertia_normal` / `odd_orderOf_tameInertia`. -/
theorem Q0loc_datum_indep_K (D : TateDualityG Γ 2) {q : V → ZMod 2}
    (dat1 dat2 : FactorSet C V)
    (hdat1 : IsEquivariantFactorSet q dat1) (hdat2 : IsEquivariantFactorSet q dat2)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (I : Subgroup C) (hIn : I.Normal) (hodd : Odd (Nat.card I))
    (hVI : ∀ v : V, (∀ i ∈ I, i • v = v) → v = 0)
    (x : H1 Γ V) :
    Q0loc D dat1 ρ x = Q0loc D dat2 ρ x := by
  obtain ⟨Δφ, hQ, hE⟩ := OrbitVanish.exists_equivariant_refinement
    (OrbitVanish.diffDatum dat1 dat2)
    (OrbitVanish.isEquivariantFactorSet_diffDatum hdat1 hdat2) hV2 I hIn hodd hVI
  exact Q0loc_datum_indep_of_refinement_K D dat1 dat2 ρ hρ x Δφ hQ hE

end DatumIndependence

end GQ2.Dyadic
