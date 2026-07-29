/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.LocalGauss.ReadPerOrbitK
import GQ2.Dyadic.LocalGauss.InvolutionSpliceK
import GQ2.Dyadic.Projectivity
import GQ2.VanishClose

/-!
# The Lemma-6.17 vanishing endpoint over a general local source (LG4c, part 4)

`GQ2.VanishClose.lemma_6_17_vanish_final` (`GQ2/VanishClose.lean` :205) retyped from `G_ℚ₂` to an
arbitrary topological group `Γ` with an anchor `anc : Γ →ₜ* G_ℚ₂` and a local Tate-duality bundle
`D : TateDualityG Γ 2`.  **The output is literally LG4a's `Q0locVanishesOnDeep D dat anc ρ`**
(`LocalGauss/DeepPackage.lean` §8) — the binder LG4b's endpoint takes — so the final composition
with the dimension lane is definitionally trivial.

## The three interface changes against the `ℚ₂` model

1. **Tame marking → tame pair at `q_K = 2^f`.**  The `ℚ₂` proof consumes a marking
   `c : T_tame ↠ C` and the `q = 2` producers `gen_of_surjective`, `odd_orderOf_tameInertia`,
   `tameInertia_normal`, `rho_surjective`.  Here the interface is PJ1's abstract tame pair
   `(sg, t)` with `hgen : ⟨sg, t⟩ = C`, `hrel : sg⁻¹ t sg = t^(2^f)`, `1 ≤ f` — the shape
   `GQ2.Dyadic.lemma_6_11_of_tame_pair_pow`, `tame_zpowers_normal_pow` and `tame_odd_order_pow`
   take.  `hρsurj` becomes an explicit binder (LG3's `prop_6_18_unramified_K` derives it from its
   `tameFK`/`hc`/`hfac` binders the same way).
2. **Splitting fields threaded, not built.**  Following LG4a §6, the field cutting out the
   anchored splitting group is the binder pair `(k₀, hker₀)`; the per-involution tower and the
   analytic `hunram` come from the `InvolutionFieldPackage` binder (§1 below), which is exactly
   the AX3/AX4 field-side interface of `LocalGauss/InvolutionSpliceK.lean`.  **No axiom, no census
   change.**
3. **Anchor injectivity.**  `hancinj : Function.Injective anc` (true for `anc = U.subtype`, vacuous
   at `anc = id`) is what turns LG4a's `ancSubgroup`-shaped `hker` into the pointwise `Γ`-side
   membership test the involution splice needs (`mem_ker_iff_anc_mem`).

## Contents

* §1 the `InvolutionFieldPackage` interface;
* §2 wiring bricks: `eOfSurjK`, `out_notMem_and_out_sq_memK`, `evensNormFun_orbit_mem_Z2_K`,
  `hvanish_cup_conj_ker_K` (the free branch, LG4a §6 + §7), and `lemma_6_14_K` (the retype of
  `GQ2.RepIndependence.lemma_6_14`);
* §3 `regular_isometric_embedding_orbit_pow` — the orbit-sum isometric embedding at a general
  `q_K = 2^f` (the `ℚ₂` `regular_isometric_embedding_orbit` with `GQ2.lemma_6_11` replaced by
  PJ1's `lemma_6_11_of_tame_pair_pow`);
* §4 the endpoint `lemma_6_17_vanish_final_K : Q0locVanishesOnDeep D dat anc ρ`.

The `ℚ₂` file's wiring bricks `reindexHom_sumDatum` and `isEquivariantFactorSet_reindexHom` are
ambient-free and are consumed verbatim, as are all of `GQ2/OrbitDecomp.lean` and
`GQ2.ShapiroDeepness.graphPullback_reindexHom`.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh GQ2.Corestriction GQ2.SectionSix GQ2.QuadraticFp2 GQ2.ShapiroRead

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The `AlgEquiv`-flavoured spelling of `G_ℚ₂` (LG4a's anchoring convention). -/
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

/-! ## §1 The involution field package (the AX3/AX4 field-side interface)

Per involution lift `ĝ` the splice of `LocalGauss/InvolutionSpliceK.lean` needs a finite subfield
`k ≤ k₀` cutting out `U₀ = ker ρ ⊔ ⟨ĝ⟩` through the anchor, with `[k₀ : k] = 2` on the Galois side
and the analytic norm-matching clause `hunram`.  In the `ℚ₂` model these are produced by
`ResidueLift.splitField` / `InfiniteGalois.fixingSubgroup_fixedField` /
`UnramifiedBridge.hunram_involution`; in the dyadic campaign that production **is** the AX3/AX4
interface, so it is threaded. -/

section Package

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {C : Type} [Group C] [TopologicalSpace C]

/-- **The involution field package** at an anchored local source, relative to the field `k₀`
cutting out the anchored splitting group: for every involution lift `ĝ` of `Γ ⧸ ker ρ` there is a
finite subfield `k ≤ k₀` whose fixing subgroup is the anchor image of `U₀ = ker ρ ⊔ ⟨ĝ⟩`, of
Galois index 2 in `k₀`'s, over which every nonzero element of `k₀` has a norm-matching partner. -/
def InvolutionFieldPackage (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)
    (k₀ : IntermediateField ℚ_[2] ℚ̄₂) : Prop :=
  ∀ ĝ : Γ, ĝ ∉ (ρ.toMonoidHom.ker : Subgroup Γ) → ĝ * ĝ ∈ (ρ.toMonoidHom.ker : Subgroup Γ) →
    ∃ (k : IntermediateField ℚ_[2] ℚ̄₂) (_ : FiniteDimensional ℚ_[2] k),
      k ≤ k₀ ∧
      (∀ x : Γ, x ∈ (ρ.toMonoidHom.ker : Subgroup Γ) ⊔ Subgroup.zpowers ĝ
        ↔ anc x ∈ k.fixingSubgroup) ∧
      ((k₀.fixingSubgroup).subgroupOf k.fixingSubgroup).index = 2 ∧
      (∀ y : ℚ̄₂, y ≠ 0 → y ∈ k₀ → ∃ z : ℚ̄₂, z ≠ 0 ∧ z ∈ k ∧ ‖y‖ = ‖z‖)

end Package

/-! ## §2 Wiring bricks -/

section ETower

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {C : Type} [Group C] [TopologicalSpace C]

/-- **The classifying equivalence** `e : C ≃* Γ ⧸ ker ρ` for a surjective `ρ` —
`GQ2.VanishClose.eOfSurj` retyped. -/
noncomputable def eOfSurjK (ρ : ContinuousMonoidHom Γ C) (hρsurj : Function.Surjective ρ) :
    C ≃* Γ ⧸ (ρ.toMonoidHom.ker : Subgroup Γ) :=
  (QuotientGroup.quotientKerEquivOfSurjective ρ.toMonoidHom hρsurj).symm

/-- **`e ∘ ρ = mk'`** — `GQ2.VanishClose.eOfSurj_rho` retyped. -/
theorem eOfSurjK_rho (ρ : ContinuousMonoidHom Γ C) (hρsurj : Function.Surjective ρ) (g : Γ) :
    eOfSurjK ρ hρsurj (ρ g) = QuotientGroup.mk g :=
  (QuotientGroup.quotientKerEquivOfSurjective ρ.toMonoidHom hρsurj).symm_apply_eq.mpr
    (QuotientGroup.kerLift_mk _ g).symm

end ETower

section Bricks

variable {G : Type*} [Group G]

/-- **Out-lift of an order-2 nontrivial coset is a non-`N` involution mod `N`** —
`GQ2.VanishClose.out_notMem_and_out_sq_mem` retyped over an abstract `G`. -/
theorem out_notMem_and_out_sq_memK (N : Subgroup G) [N.Normal] {w : G ⧸ N}
    (hw2 : w * w = 1) (hwne : w ≠ 1) :
    Quotient.out w ∉ N ∧ Quotient.out w * Quotient.out w ∈ N := by
  have hw : QuotientGroup.mk' N (Quotient.out w) = w := by
    rw [QuotientGroup.mk'_apply]; exact QuotientGroup.out_eq' w
  refine ⟨fun h => hwne ?_, ?_⟩
  · have h1 : QuotientGroup.mk' N (Quotient.out w) = 1 := by
      rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff _).mpr h
    rwa [hw] at h1
  · have h1 : QuotientGroup.mk' N (Quotient.out w * Quotient.out w) = 1 := by
      rw [map_mul, hw]; exact hw2
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

end Bricks

section Z2Brick

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **The involution orbit's inner cochain is a 2-cocycle** —
`GQ2.VanishClose.evensNormFun_orbit_mem_Z2` retyped (the `ℚ₂` `rfl`-triviality of the `𝔽₂`-action
becomes LG2's `smul_zmodTwo`). -/
theorem evensNormFun_orbit_mem_Z2_K (N : Subgroup Γ) [N.Normal]
    (hNopen : IsOpen (N : Set Γ)) (g : Γ) (hgN : g ∉ N) (hg2 : g * g ∈ N)
    (β : Γ → RegRep N) (hZ1 : shapiroCoord N β ∈ Z1 ↥N (ZMod 2)) :
    evensNormFun (N.subgroupOf (N ⊔ Subgroup.zpowers g))
        ⟨g, Subgroup.mem_sup_right (Subgroup.mem_zpowers g)⟩
        (fun w => shapiroCoord N β ⟨w.1.1, w.2⟩)
      ∈ Z2 ↥(N ⊔ Subgroup.zpowers g) (ZMod 2) := by
  have hsU : (⟨g, Subgroup.mem_sup_right (Subgroup.mem_zpowers g)⟩ : ↥(N ⊔ Subgroup.zpowers g))
      ∉ N.subgroupOf (N ⊔ Subgroup.zpowers g) :=
    fun h => hgN (Subgroup.mem_subgroupOf.mp h)
  have hUi : (N.subgroupOf (N ⊔ Subgroup.zpowers g)).index = 2 :=
    InvolutionSplice.index_eq_two_of_decomp hsU (fun bb hbb => by
      rcases InvolutionSplice.mem_or_mul_mem_of_mem_sup hg2 bb.2 with hbN | hbg
      · exact absurd (Subgroup.mem_subgroupOf.mpr hbN) hbb
      · exact Subgroup.mem_subgroupOf.mpr hbg)
  have hUo : IsOpen (((N.subgroupOf (N ⊔ Subgroup.zpowers g))
      : Subgroup ↥(N ⊔ Subgroup.zpowers g)) : Set ↥(N ⊔ Subgroup.zpowers g)) :=
    hNopen.preimage continuous_subtype_val
  obtain ⟨hjc, hjhom⟩ :=
    (mem_Z1_iff_of_trivial (fun n m => smul_zmodTwo n m)).mp hZ1
  have hα : ∀ w z : ↥(N.subgroupOf (N ⊔ Subgroup.zpowers g)),
      shapiroCoord N β ⟨(w * z).1.1, (w * z).2⟩
        = shapiroCoord N β ⟨w.1.1, w.2⟩ + shapiroCoord N β ⟨z.1.1, z.2⟩ := by
    intro w z
    have := hjhom ⟨w.1.1, w.2⟩ ⟨z.1.1, z.2⟩
    rwa [show (⟨(w * z).1.1, (w * z).2⟩ : ↥N) = ⟨w.1.1, w.2⟩ * ⟨z.1.1, z.2⟩ from Subtype.ext rfl]
  have hαc : Continuous fun w : ↥(N.subgroupOf (N ⊔ Subgroup.zpowers g)) =>
      shapiroCoord N β ⟨w.1.1, w.2⟩ :=
    hjc.comp (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
  exact evensNormFun_mem_Z2 (fun n m => smul_zmodTwo n m) hUo hUi hsU _ hα hαc

end Z2Brick

section FreeBranch

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)

/-- **The free orbit's inner cochain vanishes in `H²`** — `GQ2.VanishClose.hvanish_free_conj`
retyped: the cup of a deep `ker ρ`-block cocycle with the `g`-conjugate of another deep block
cocycle is an `H²`-coboundary.  Composes LG4a §7 (`conjAct_deepClassesAt`, conjugation stability
of the anchored deep classes) with LG4a §6 (`hvanish_cup_ker_K`), and is stated for arbitrary
scalar cocycles rather than only for `shapiroCoord`s. -/
theorem hvanish_cup_conj_ker_K (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (α γ : ↥(ρ.toMonoidHom.ker : Subgroup Γ) → ZMod 2) (g : Γ)
    (hZα : α ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
    (hZγ : γ ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
    (hDα : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) α ∈ deepClassesAt (kerAnc anc ρ))
    (hDγ : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) γ ∈ deepClassesAt (kerAnc anc ρ)) :
    H2ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
        (cup11Fun AddMonoidHom.mul α (fun n => γ (conjMap ρ g n))) = 0 := by
  have hZ1conj : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) => γ (conjMap ρ g n))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) :=
    comp_conjMap_mem_Z1 ρ hZγ g
  have hdeepconj : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
      (fun n => γ (conjMap ρ g n)) ∈ deepClassesAt (kerAnc anc ρ) := by
    rw [show H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) (fun n => γ (conjMap ρ g n))
        = conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) γ) from
      (conjAct_h1ofFun ρ g hZγ).symm]
    exact conjAct_deepClassesAt anc ρ g hDγ
  exact hvanish_cup_ker_K anc ρ k hker α (fun n => γ (conjMap ρ g n)) hZα hZ1conj hDα hdeepconj

end FreeBranch

section Lemma614

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]
variable {W : Type} [AddCommGroup W] [TopologicalSpace W] [DiscreteTopology W] [Finite W]
  [DistribMulAction Γ W] [ContinuousSMul Γ W] [DistribMulAction C W]

omit [Finite V] [Finite C] [Finite W] in
/-- **Lemma 6.14 (regular-module realization), eq. (102), at a general local source** —
`GQ2.RepIndependence.lemma_6_14` retyped: `Q⁰_loc` of a comapped datum at `x` is `Q⁰_loc` of the
datum at the pushed-forward class. -/
theorem lemma_6_14_K (D : TateDualityG Γ 2)
    (datW : FactorSet C W) (ρ : ContinuousMonoidHom Γ C)
    (i : V →+ W) (hic : Continuous i) (hicompat : ∀ (g : Γ) (v : V), i (g • v) = g • i v)
    {q : W → ZMod 2} (hdatW : IsEquivariantFactorSet q datW)
    (hiC : ∀ (c : C) (v : V), i (c • v) = c • i v)
    (hρW : ∀ (g : Γ) (w : W), g • w = ρ g • w)
    (x : H1 Γ V) :
    Q0loc D (datW.comap i) ρ x = Q0loc D datW ρ (mapCoeff1 i hic hicompat x) := by
  show iotaF D (H2ofFun Γ (graphPullback (datW.comap i) ρ (Quotient.out x).1))
      = iotaF D (H2ofFun Γ (graphPullback datW ρ
          (Quotient.out (mapCoeff1 i hic hicompat x)).1))
  refine congrArg (iotaF D) ?_
  set b₁ : Z1 Γ W :=
    Z1comap (ContinuousMonoidHom.id Γ) i hic (fun g n => hicompat g n) (Quotient.out x)
    with hb1def
  set b₂ : Z1 Γ W := Quotient.out (mapCoeff1 i hic hicompat x) with hb2def
  have hb1val : b₁.1 = fun g => i ((Quotient.out x).1 g) := rfl
  have hStepA : graphPullback (datW.comap i) ρ (Quotient.out x).1
      = graphPullback datW ρ b₁.1 := by
    rw [hb1val]
    funext p
    simp only [graphPullback, FactorSet.comap]
    rw [hiC]
  rw [hStepA]
  refine repIndep datW hdatW ρ hρW b₁ b₂ ?_
  have h1 : mapCoeff1 i hic hicompat (H1mk Γ V (Quotient.out x)) = H1mk Γ W b₁ := by
    rw [hb1def]; rfl
  rw [← h1, H1mk_out, hb2def, H1mk_out]

end Lemma614

/-! ## §3 The orbit-sum isometric embedding at `q_K = 2^f`

`GQ2.regular_isometric_embedding_orbit` (`GQ2/RegularIsometry.lean` :159) with its `T_tame`
marking replaced by PJ1's abstract tame pair, so that the ramified split-summand input is
`GQ2.Dyadic.lemma_6_11_of_tame_pair_pow` (the AX5 deliverable) rather than the `q = 2`
`GQ2.lemma_6_11`.  Everything downstream of the split package — the reindex `reBlock` along
`e : C ≃* G ⧸ N` and the §6.2 orbit decomposition — is ambient- and `q`-free and is reused. -/

section OrbitEmbedding

variable {C : Type} [Group C]
variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

private theorem reSummand_smulK (e : C ≃* G ⧸ N) (c : C) (fn : C → ZMod 2) :
    reSummand N e (fun x => fn (c⁻¹ * x)) = e c • reSummand N e fn := by
  funext h
  show fn (c⁻¹ * e.symm h) = reSummand N e fn ((e c)⁻¹ * h)
  show fn (c⁻¹ * e.symm h) = fn (e.symm ((e c)⁻¹ * h))
  rw [map_mul, map_inv, MulEquiv.symm_apply_apply]

private theorem reBlock_applyK (e : C ≃* G ⧸ N) {K : ℕ} (F : Fin K → C → ZMod 2) (k : Fin K) :
    reBlock N e K F k = reSummand N e (F k) := rfl

private theorem reBlock_smulK (e : C ≃* G ⧸ N) {K : ℕ} (c : C) (F : PermW C K) :
    reBlock N e K (c • F) = e c • reBlock N e K F := by
  funext k
  show reSummand N e (fun x => F k (c⁻¹ * x)) = e c • reBlock N e K F k
  rw [reBlock_applyK, reSummand_smulK]

private theorem reBlock_symm_smulK (e : C ≃* G ⧸ N) {K : ℕ} (d : G ⧸ N)
    (Y : Fin K → RegRep N) :
    (reBlock N e K).symm (d • Y) = e.symm d • (reBlock N e K).symm Y := by
  apply (reBlock N e K).injective
  rw [AddEquiv.apply_symm_apply, reBlock_smulK, AddEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

/-- **The orbit-sum isometric embedding at a general `q_K = 2^f`** — the retype of
`GQ2.regular_isometric_embedding_orbit` over PJ1's tame pair: a ramified simple faithful quadratic
`𝔽₂[C]`-module `(V, q)` embeds `C`-equivariantly (through `e : C ≃* G ⧸ N`) as a split summand of
`Fin K → RegRep N`, carrying the pulled-back form `Q_W := q ∘ r` together with the §6.2 orbit-sum
datum for it, an isometry. -/
theorem regular_isometric_embedding_orbit_pow [Finite C] [Fintype (G ⧸ N)]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (e : C ≃* G ⧸ N) {sg t : C} {f : ℕ} (hf : 1 ≤ f)
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ (2 ^ f))
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hinv : IsInvariant C q)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) :
    ∃ (K : ℕ) (ι : V →+ (Fin K → RegRep N)) (r : (Fin K → RegRep N) →+ V),
      IsEquivariantFactorSet (fun F => q (r F))
        (OrbitVanish.sumDatum (orbitIndexSet N (fun F => q (r F))) (orbitDatum N)) ∧
      (∀ v : V, q (r (ι v)) = q v) ∧
      (∀ (a : C) (v : V), ι (a • v) = e a • ι v) ∧
      (∀ v : V, r (ι v) = v) := by
  haveI : Finite (G ⧸ N) := Finite.of_fintype _
  obtain ⟨K, ι₀, r₀, hι, hr, hri⟩ :=
    lemma_6_11_of_tame_pair_pow hf hgen hrel hV2 hfaith hsimple hram
  -- recast the two equivariances into the `PermW` `DistribMulAction` form
  have hιsmul : ∀ (h : C) (v : V), ι₀ (h • v) = h • ι₀ v := by
    intro h v
    funext n x
    exact hι h v n x
  have hrsmul : ∀ (h : C) (F : PermW C K), r₀ (h • F) = h • r₀ F := by
    intro h F
    show r₀ (fun n x => F n (h⁻¹ * x)) = h • r₀ F
    exact hr h F
  set ι : V →+ (Fin K → RegRep N) := (reBlock N e K).toAddMonoidHom.comp ι₀ with hι_def
  set r : (Fin K → RegRep N) →+ V := r₀.comp (reBlock N e K).symm.toAddMonoidHom with hr_def
  -- retraction
  have hretr : ∀ v : V, r (ι v) = v := by
    intro v
    show r₀ ((reBlock N e K).symm (reBlock N e K (ι₀ v))) = v
    rw [AddEquiv.symm_apply_apply, hri]
  -- equivariance of `r` in the `G ⧸ N` action
  have hrsmul' : ∀ (d : G ⧸ N) (F : Fin K → RegRep N), r (d • F) = e.symm d • r F := by
    intro d F
    show r₀ ((reBlock N e K).symm (d • F)) = e.symm d • r₀ ((reBlock N e K).symm F)
    rw [reBlock_symm_smulK, hrsmul]
  -- the pulled-back form is invariant and quadratic
  have hqWinv : IsInvariant (G ⧸ N) (fun F => q (r F)) := by
    intro d F
    show q (r (d • F)) = q (r F)
    rw [hrsmul' d F, hinv]
  have hqWquad : IsQuadraticFp2 (fun F : Fin K → RegRep N => q (r F)) := by
    constructor
    · show q (r 0) = 0
      rw [map_zero, hq.map_zero]
    · intro A B E
      simpa only [polar, map_add] using hq.polar_add_left (r A) (r B) (r E)
    · intro A B E
      simpa only [polar, map_add] using hq.polar_add_right (r A) (r B) (r E)
  refine ⟨K, ι, r, isEquivariantFactorSet_orbitSumDatum N hqWquad hqWinv, ?_, ?_, hretr⟩
  · intro v; rw [hretr v]
  · intro a v
    show reBlock N e K (ι₀ (a • v)) = e a • reBlock N e K (ι₀ v)
    rw [hιsmul, reBlock_smulK]

end OrbitEmbedding

/-! ## §4 The endpoint

`GQ2.VanishClose.lemma_6_17_vanish_final` (`GQ2/VanishClose.lean` :205) retyped, with the output
in LG4a's `Q0locVanishesOnDeep` shape. -/

section Endpoint

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

/-- **`lemma_6_17_vanish`, closed downstream, over a general local source** — the retype of
`GQ2.VanishClose.lemma_6_17_vanish_final`.  The base connecting map `Q⁰_loc` vanishes identically
on the anchored deep half `X₊`, i.e. the conclusion is *literally* LG4a's
`Q0locVanishesOnDeep D dat anc ρ` (`LocalGauss/DeepPackage.lean` §8), the hypothesis slot of the
LG4b join `card_Q0loc_zero_eq_of_dim_of_vanish_K`.

Route (unchanged from the `ℚ₂` model): datum-independence (`Q0loc_datum_indep_K`) moves the
caller's arbitrary equivariant factor set to the §6.2 orbit-sum datum on the regular module;
Lemma 6.14 (`lemma_6_14_K`) transports along the isometric embedding
(`regular_isometric_embedding_orbit_pow`); the orbit reducer
(`Q0loc_vanish_of_datum_decomp_K`) then needs, per orbit, a Lemma-6.15 cohomology
(`hcoh_{square,free,involution}_K`) and a deep-class vanishing — square/free from LG4a §6 + §7
(`hvanish_cup_ker_K`, `hvanish_cup_conj_ker_K`), involution from the threaded splice
(`hvanish_involution_ker_K` at the field data supplied by `hpkg`). -/
theorem lemma_6_17_vanish_final_K (D : TateDualityG Γ 2)
    (anc : ContinuousMonoidHom Γ GalQ2) (hancinj : Function.Injective ⇑anc)
    (ρ : ContinuousMonoidHom Γ C) (hρsurj : Function.Surjective ⇑ρ)
    {sg t : C} {f : ℕ} (hf : 1 ≤ f)
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ (2 ^ f))
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (k₀ : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k₀]
    (hker₀ : ∀ y : GalQ2, y ∈ ancSubgroup (kerAnc anc ρ) ↔ y ∈ k₀.fixingSubgroup)
    (hpkg : InvolutionFieldPackage anc ρ k₀) :
    Q0locVanishesOnDeep D dat anc ρ := by
  classical
  intro x hx
  set N : Subgroup Γ := ρ.toMonoidHom.ker with hN
  have hNopen : IsOpen (N : Set Γ) := isOpen_ker ρ
  haveI hNn : N.Normal := inferInstance
  haveI : Finite (Γ ⧸ N) :=
    Finite.of_injective _ (QuotientGroup.quotientKerEquivRange ρ.toMonoidHom).injective
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  set e : C ≃* Γ ⧸ N := eOfSurjK ρ hρsurj with he_def
  obtain ⟨K, ι, r, hEqfs, hIso, hιe, hri⟩ :=
    regular_isometric_embedding_orbit_pow (G := Γ) N e hf hgen hrel q hq hinv hV2
      hfaith hsimple hram
  -- base `RegRep N` instances (the block module is the `Pi`-lift)
  haveI : Finite (RegRep N) := inferInstanceAs (Finite ((Γ ⧸ N) → ZMod 2))
  letI : TopologicalSpace (RegRep N) := ⊥
  haveI : DiscreteTopology (RegRep N) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (RegRep N) :=
    { continuous_add := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  haveI hdq : DiscreteTopology (Γ ⧸ N) := QuotientGroup.discreteTopology hNopen
  letI actAbs : DistribMulAction Γ (RegRep N) :=
    DistribMulAction.compHom _ (QuotientGroup.mk' N)
  letI actC : DistribMulAction C (RegRep N) := DistribMulAction.compHom _ e.toMonoidHom
  haveI : ContinuousSMul Γ (RegRep N) := by
    refine ⟨?_⟩
    have h1 : Continuous fun p : Γ × RegRep N =>
        ((QuotientGroup.mk' N p.1, p.2) : (Γ ⧸ N) × RegRep N) :=
      (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd
    exact (continuous_of_discreteTopology
      (f := fun p : (Γ ⧸ N) × RegRep N => p.1 • p.2)).comp h1
  haveI : Finite (Fin K → RegRep N) := inferInstance
  haveI : DiscreteTopology (Fin K → RegRep N) := Pi.discreteTopology
  haveI : ContinuousSMul Γ (Fin K → RegRep N) := by
    refine ⟨?_⟩
    have h1 : Continuous fun p : Γ × (Fin K → RegRep N) =>
        ((QuotientGroup.mk' N p.1, p.2) : (Γ ⧸ N) × (Fin K → RegRep N)) :=
      (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd
    exact (continuous_of_discreteTopology
      (f := fun p : (Γ ⧸ N) × (Fin K → RegRep N) => p.1 • p.2)).comp h1
  -- the base compatibility identities (`Pi`-lifts inherit them)
  have hmk : ∀ (g : Γ) (y : RegRep N), g • y = QuotientGroup.mk' N g • y :=
    fun _ _ => rfl
  have hρW : ∀ (g : Γ) (w : Fin K → RegRep N), g • w = ρ g • w := by
    intro g w
    funext j
    show QuotientGroup.mk' N g • w j = e (ρ g) • w j
    rw [QuotientGroup.mk'_apply, ← eOfSurjK_rho ρ hρsurj g, he_def]
  set qW : (Fin K → RegRep N) → ZMod 2 := fun F => q (r F) with hqW_def
  set datW : FactorSet (Γ ⧸ N) (Fin K → RegRep N) :=
    OrbitVanish.sumDatum (orbitIndexSet N qW) (orbitDatum N) with hdatW_def
  set datWC : FactorSet C (Fin K → RegRep N) := datW.reindexHom e.toMonoidHom with hdatWC_def
  have hEqfsC : IsEquivariantFactorSet qW datWC :=
    VanishClose.isEquivariantFactorSet_reindexHom hEqfs e.toMonoidHom (fun _ _ => rfl)
  have hqeq : (fun v => qW (ι v)) = q := funext hIso
  have hcomap : IsEquivariantFactorSet q (datWC.comap ι) := by
    have := datum_comap hEqfsC ι (fun cc v => hιe cc v)
    rwa [hqeq] at this
  -- the tame-inertia data (PJ1's abstract pair, replacing the `ℚ₂` `Ttame` producers)
  have heven : Even ((2 : ℕ) ^ f) := by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    exact ⟨2 ^ f', by rw [pow_succ]; ring⟩
  have hInorm : (Subgroup.zpowers t).Normal := tame_zpowers_normal_pow hgen hrel
  have hodd : Odd (Nat.card (Subgroup.zpowers t)) := by
    rw [Nat.card_zpowers]
    exact tame_odd_order_pow (orderOf_pos sg).ne' (pow_ne_zero _ two_ne_zero) heven hrel
  have hVI : ∀ v : V, (∀ i ∈ Subgroup.zpowers t, i • v = v) → v = 0 :=
    LocalKummer.fixedByNormal_eq_bot (Subgroup.zpowers t) hInorm hsimple
      (by obtain ⟨v, hv⟩ := hram; exact ⟨t, Subgroup.mem_zpowers _, v, hv⟩)
  have hstep1 : Q0loc D dat ρ x = Q0loc D (datWC.comap ι) ρ x :=
    Q0loc_datum_indep_K D dat (datWC.comap ι) hdat hcomap ρ hρ hV2
      (Subgroup.zpowers t) hInorm hodd hVI x
  have hic : Continuous (ι : V → Fin K → RegRep N) := continuous_of_discreteTopology
  have heρ : ∀ g : Γ, e (ρ g) = QuotientGroup.mk' N g := by
    intro g
    rw [he_def, eOfSurjK_rho ρ hρsurj g, QuotientGroup.mk'_apply]
  have hicompat : ∀ (g : Γ) (v : V), ι (g • v) = g • ι v := by
    intro g v
    rw [hρ g v, hιe (ρ g) v, heρ g]
    rfl
  have hstep2 : Q0loc D (datWC.comap ι) ρ x
      = Q0loc D datWC ρ (mapCoeff1 ι hic hicompat x) :=
    lemma_6_14_K D datWC ρ ι hic hicompat hEqfsC (fun cc v => hιe cc v) hρW x
  rw [hstep1, hstep2]
  set xW : H1 Γ (Fin K → RegRep N) := mapCoeff1 ι hic hicompat x with hxW_def
  have hxW : xW ∈ deepPartK (V := Fin K → RegRep N) anc ρ :=
    deepPartK_mapCoeff1 anc hρ hρW ι hic hicompat hx
  set b : ↥(Z1 Γ (Fin K → RegRep N)) := Quotient.out xW with hb_def
  -- the per-orbit subgroup and inner cochain (matching `hcoh_*`)
  set Uf : OrbitIx K (Γ ⧸ N) → Subgroup Γ := fun o =>
    match o with
    | Sum.inl _ => N
    | Sum.inr (Sum.inl (_, u)) => N ⊔ Subgroup.zpowers (Quotient.out u)
    | Sum.inr (Sum.inr _) => N with hUf_def
  set innerf : (o : OrbitIx K (Γ ⧸ N)) → ↥(Uf o) × ↥(Uf o) → ZMod 2 := fun o =>
    match o with
    | Sum.inl j => fun p =>
        shapiroCoord N (fun g => b.1 g j) p.1 * shapiroCoord N (fun g => b.1 g j) p.2
    | Sum.inr (Sum.inl (j, u)) => fun p =>
        evensNormFun (N.subgroupOf (N ⊔ Subgroup.zpowers (Quotient.out u)))
          ⟨Quotient.out u, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
          (fun w => shapiroCoord N (fun g => b.1 g j) ⟨w.1.1, w.2⟩) (p.1, p.2)
    | Sum.inr (Sum.inr (j, k, u)) => fun p =>
        shapiroCoord N (fun g => b.1 g j) p.1 *
          shapiroCoord N (fun g => b.1 g k) ⟨(Quotient.out u)⁻¹ * (p.2 : Γ) * Quotient.out u,
            by simpa using Subgroup.Normal.conj_mem hNn _ p.2.2 (Quotient.out u)⁻¹⟩
      with hinnerf_def
  -- **The LG2 `smul` trap at the reducer's interface.**  At `G_ℚ₂` the cup cochain
  -- `cup11Fun μ a c p = μ (a p.1) (p.1 • c p.2)` is *definitionally* the pointwise product,
  -- because the `𝔽₂`-action is `rfl`-trivial; at a general `Γ` it is only `smul_zmodTwo`-equal.
  -- `innerf` is kept in the product form (matching `hcoh_*`/Lemma 6.15 verbatim) and converted
  -- here for the two `cup11`-shaped obligations (`hZ2`, `hvanish`).
  have hcupval : ∀ (a c : ↥N → ZMod 2) (p : ↥N × ↥N),
      cup11Fun AddMonoidHom.mul a c p = a p.1 * c p.2 := by
    intro a c p
    show AddMonoidHom.mul (a p.1) (p.1 • c p.2) = a p.1 * c p.2
    rw [smul_zmodTwo]
    rfl
  have hsqeq : ∀ j : Fin K, innerf (Sum.inl j) = cup11Fun AddMonoidHom.mul
      (shapiroCoord N (fun g => (Quotient.out xW).1 g j))
      (shapiroCoord N (fun g => (Quotient.out xW).1 g j)) := by
    intro j
    funext p
    rw [hcupval]
  have hfreeeq : ∀ (j k : Fin K) (u : Γ ⧸ N),
      innerf (Sum.inr (Sum.inr (j, k, u)))
        = cup11Fun AddMonoidHom.mul (shapiroCoord N (fun g => (Quotient.out xW).1 g j))
          (fun n => shapiroCoord N (fun g => (Quotient.out xW).1 g k)
            (conjMap ρ (Quotient.out u) n)) := by
    intro j k u
    funext p
    rw [hcupval]
    rfl
  -- shared facts: `N ≤ Uf o`, openness, finiteness
  have hNleU : ∀ o : OrbitIx K (Γ ⧸ N), N ≤ Uf o := by
    intro o
    match o with
    | Sum.inl _ => exact le_refl N
    | Sum.inr (Sum.inl (_, u)) => exact le_sup_left
    | Sum.inr (Sum.inr _) => exact le_refl N
  have hUopen : ∀ o, IsOpen ((Uf o : Subgroup Γ) : Set Γ) := fun o =>
    Subgroup.isOpen_mono (hNleU o) hNopen
  have hUfin : ∀ o, Finite (Γ ⧸ Uf o) := by
    intro o
    haveI hfi : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hdvd : (Uf o).index ∣ N.index := Subgroup.index_dvd_of_le (hNleU o)
    haveI : (Uf o).FiniteIndex :=
      ⟨fun h0 => hfi.index_ne_zero (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  -- the block coordinates are deep `Z¹`-cocycles
  have hZ1blk : ∀ j : Fin K,
      shapiroCoord N (fun g => (Quotient.out xW).1 g j) ∈ Z1 ↥N (ZMod 2) :=
    fun j => shapiroCoord_mem_Z1 (block_cocycleK N hmk (Quotient.out xW) j)
      (block_continuousK N (Quotient.out xW) j) (fun n m => smul_zmodTwo n m)
  have hdeepblk : ∀ j : Fin K,
      H1ofFun ↥N (shapiroCoord N (fun g => (Quotient.out xW).1 g j))
        ∈ deepClassesAt (kerAnc anc ρ) :=
    fun j => shapiroCoord_mem_deepClassesAt ρ anc j hxW
  -- involution-position facts, shared across the three `Sum.inr (Sum.inl _)` branches
  have hu_all : ∀ w : Γ ⧸ N, QuotientGroup.mk' N (Quotient.out w) = w := fun w => by
    rw [QuotientGroup.mk'_apply]; exact QuotientGroup.out_eq' w
  refine Q0loc_vanish_of_datum_decomp_K D datWC ρ hρW xW
    (orbitIndexSet N qW) (fun o => (orbitDatum N o).reindexHom e.toMonoidHom)
    (orbitSquareMap N) ?_ ?_ Uf ?_ ?_ innerf ?_ ?_ ?_
  · exact fun o ho =>
      VanishClose.isEquivariantFactorSet_reindexHom (isEqFS_orbitDatum N qW o ho) e.toMonoidHom
        (fun _ _ => rfl)
  · rw [hdatWC_def, hdatW_def]
    exact VanishClose.reindexHom_sumDatum (orbitIndexSet N qW) (orbitDatum N) (⇑e.toMonoidHom)
  · exact fun o _ => hUfin o
  · exact fun o _ => hUopen o
  · -- hZ2
    intro o ho
    rcases o with j | ⟨j, u⟩ | ⟨j, k, u⟩
    · rw [hsqeq j]
      exact cup11_mem_Z2 AddMonoidHom.mul (fun g m n => by
        rw [smul_zmodTwo, smul_zmodTwo, smul_zmodTwo]) ⟨_, hZ1blk j⟩ ⟨_, hZ1blk j⟩
    · simp only [mem_orbitIndexSet_inv, invIdx, Finset.mem_filter, Finset.mem_univ,
        true_and] at ho
      obtain ⟨hu2, hune, -⟩ := ho
      obtain ⟨hgN, hg2⟩ := out_notMem_and_out_sq_memK N hu2 hune
      exact evensNormFun_orbit_mem_Z2_K N hNopen (Quotient.out u) hgN hg2
        (fun g => (Quotient.out xW).1 g j) (hZ1blk j)
    · rw [hfreeeq j k u]
      exact cup11_mem_Z2 AddMonoidHom.mul (fun g m n => by
        rw [smul_zmodTwo, smul_zmodTwo, smul_zmodTwo])
        ⟨_, hZ1blk j⟩ ⟨_, comp_conjMap_mem_Z1 ρ (hZ1blk k) (Quotient.out u)⟩
  · -- hcoh
    intro o ho
    have hcomp : (⇑e.toMonoidHom ∘ ⇑ρ : Γ → Γ ⧸ N) = ⇑(QuotientGroup.mk' N) :=
      funext heρ
    rw [ShapiroDeepness.graphPullback_reindexHom (orbitDatum N o) (⇑e.toMonoidHom)
      (fun _ _ => rfl) (⇑ρ) (Quotient.out xW).1, hcomp]
    rcases o with j | ⟨j, u⟩ | ⟨j, k, u⟩
    · exact hcoh_square_K N hmk j hNopen (Quotient.out xW)
    · simp only [mem_orbitIndexSet_inv, invIdx, Finset.mem_filter, Finset.mem_univ,
        true_and] at ho
      obtain ⟨hu2, hune, -⟩ := ho
      have hu : QuotientGroup.mk' N (Quotient.out u) = u := hu_all u
      obtain ⟨hgN, hg2⟩ := out_notMem_and_out_sq_memK N hu2 hune
      have hs : (⟨Quotient.out u, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩ :
          ↥(N ⊔ Subgroup.zpowers (Quotient.out u)))
          ∉ N.subgroupOf (N ⊔ Subgroup.zpowers (Quotient.out u)) :=
        fun h => hgN (Subgroup.mem_subgroupOf.mp h)
      have hg := hcoh_involution_K N hmk j (Quotient.out u) hNopen hgN hg2
        (N ⊔ Subgroup.zpowers (Quotient.out u)) rfl hs (Quotient.out xW)
      rw [hu] at hg
      exact hg
    · have hu : QuotientGroup.mk' N (Quotient.out u) = u := hu_all u
      have hg := hcoh_free_K N hmk j k (Quotient.out u) hNopen (Quotient.out xW)
      rw [hu] at hg
      exact hg
  · -- hvanish
    intro o ho
    rcases o with j | ⟨j, u⟩ | ⟨j, k, u⟩
    · rw [hsqeq j]
      exact hvanish_cup_ker_K anc ρ k₀ hker₀
        (shapiroCoord N (fun g => (Quotient.out xW).1 g j))
        (shapiroCoord N (fun g => (Quotient.out xW).1 g j)) (hZ1blk j) (hZ1blk j)
        (hdeepblk j) (hdeepblk j)
    · simp only [mem_orbitIndexSet_inv, invIdx, Finset.mem_filter, Finset.mem_univ,
        true_and] at ho
      obtain ⟨hu2, hune, -⟩ := ho
      obtain ⟨hgN, hg2⟩ := out_notMem_and_out_sq_memK N hu2 hune
      obtain ⟨kf, hkfd, hkle, hkerU, hkindex, hunram⟩ := hpkg (Quotient.out u) hgN hg2
      haveI := hkfd
      exact hvanish_involution_ker_K anc ρ hancinj kf k₀ hkle hker₀ hkindex hunram
        (shapiroCoord N (fun g => (Quotient.out xW).1 g j)) (hZ1blk j) (hdeepblk j)
        (Quotient.out u) hgN hg2 (N ⊔ Subgroup.zpowers (Quotient.out u)) rfl
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hkerU
    · rw [hfreeeq j k u]
      exact hvanish_cup_conj_ker_K anc ρ k₀ hker₀
        (shapiroCoord N (fun g => (Quotient.out xW).1 g j))
        (shapiroCoord N (fun g => (Quotient.out xW).1 g k)) (Quotient.out u)
        (hZ1blk j) (hZ1blk k) (hdeepblk j) (hdeepblk k)

end Endpoint

end GQ2.Dyadic
