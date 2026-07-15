/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.InvolutionVanish
import GQ2.UnramifiedBridge

/-!
# The involution `hvanish` in `ker ρ`-vocabulary  (the U₀-splice)

The last §6.3 input of the `lemma_6_17_vanish` assembly: for a deep block coordinate
`α : ↥(ker ρ) → 𝔽₂` and an involution lift `ĝ` (`ĝ ∉ ker ρ`, `ĝ² ∈ ker ρ`,
`U₀ = ker ρ ⊔ ⟨ĝ⟩`), the Evens-norm inner cochain of the reducer's involution orbit vanishes:
`H²ofFun ↥U₀ (evensNormFun ((ker ρ).subgroupOf U₀) ⟨ĝ,_⟩ (α-restriction)) = 0`.

The c2 lane delivers this over the splitting-field tower — `hvanish_involution`
(`ShapiroDeepness`, via `lemma_6_16`), the c2a Kummer package
(`kummer_presentation_of_index_two`), and the analytic `hunram_involution`
(`UnramifiedBridge`, c2c) — all in `(k, L)` `IntermediateField`-vocabulary.  This file is the
**splice**:

* **No Evens-norm cohomology-invariance is needed** (the flagged f2d risk dissolves): with
  trivial coefficients `B¹ = 0`, so cohomologous scalar cocycles are **equal** —
  `eq_of_H1ofFun_eq` extracts, from the deep-class witness of `[α]`, a square root `β` with
  `kummerCocycleFun β = α` *on the nose* on `ker ρ`.  The two candidate inner cochains
  coincide.
* **The tower**: `L := ResidueLift.splitField ρ`, `k := fixedField (toGal U₀)` (the
  `kerGal`-idiom carrier copy), with the infinite Galois correspondence recovering
  `k.fixingSubgroup = toGal U₀`; `[k : ℚ₂] < ∞` from `U₀ ⊇ ker ρ` open.
* **The index-2 bricks**: `(N.subgroupOf U₀).index = 2` in both views, from the coset
  decomposition of `N ⊔ ⟨ĝ⟩` (`N` normal, `ĝ² ∈ N`: every element lands in `N ∪ Nĝ⁻¹`).
* **The carrier splice**: `evensAux`/`bS`/`evensNormFun` are `Quotient.out`-free (membership
  tests and `s`-translates only), so the `↥U₀`- and `↥k.fixingSubgroup`-side Evens cochains
  agree **pointwise** under the underlying-identity `ι₀`; the `B²`-witness of the field-side
  vanishing pulls back along `ι₀` (the `DeepDualityK.kerToFixing` pattern), and
  `H2ofFun ↥U₀ … = 0` follows.

The two Galois-group views (`AbsGalQ2` vs `Kummer.GaloisGroup ℚ_[2]`) share their group
operations at default transparency; all cross-view steps are `rfl`-bridges in the `kerGal`
idiom (`ResidueLift` §Plumbing).

Main result: **`hvanish_involution_ker`** — consumed by the `lemma_6_17_vanish` assembly
(`docs/orchestration/p15f2d-handoff.md` §3) at the involution orbits.  `R : LocalReciprocity` and
`horient : TameUnitOrientation R B.tameF` are threaded per the c2c4 consumer note (the
`hc`/`hV2` amendment precedent; the architecture review flag).

Axioms: std-3 + {B5 (via `R`-instantiation downstream), B9, B11a/b (via `lemma_6_16`),
B13 (`dyadicUnitFiltration`, via `hunram_involution`)} — the §6.3 involution budget.
-/

namespace GQ2

namespace InvolutionSplice

open ContCoh

/-! ## The `B¹ = 0` extraction: cohomologous scalar cocycles are equal -/

section Extraction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- **Trivial-coefficient rigidity**: two continuous 1-cocycles with the same `H1ofFun` class
are equal — `B¹(G, 𝔽₂) = 0` for the trivial action, so nothing is identified.  This dissolves
the feared Evens-norm cohomology-invariance gap: the deep-class witness's Kummer cocycle *is*
the block coordinate. -/
theorem eq_of_H1ofFun_eq (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    {φ ψ : G → ZMod 2} (hφ : φ ∈ Z1 G (ZMod 2)) (hψ : ψ ∈ Z1 G (ZMod 2))
    (h : H1ofFun G φ = H1ofFun G ψ) : φ = ψ := by
  rw [H1ofFun_of_mem hφ, H1ofFun_of_mem hψ] at h
  have h0 : H1mk G (ZMod 2) (⟨φ, hφ⟩ - ⟨ψ, hψ⟩) = 0 := by
    rw [map_sub, h, sub_self]
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp h0
  rwa [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub,
    B1_eq_bot_of_trivial htriv, AddSubgroup.mem_bot, sub_eq_zero] at hmem

end Extraction

/-! ## The index-2 bricks -/

section IndexTwo

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The coset decomposition of `N ⊔ ⟨ĝ⟩` for `N` normal with `ĝ² ∈ N`: every element is in
`N` or lands there after one more `ĝ`. -/
theorem mem_or_mul_mem_of_mem_sup {N : Subgroup G} [hNn : N.Normal] {ĝ : G}
    (hĝ2 : ĝ * ĝ ∈ N) {x : G} (hx : x ∈ N ⊔ Subgroup.zpowers ĝ) :
    x ∈ N ∨ x * ĝ ∈ N := by
  have hset : (x : G) ∈ (N : Set G) * (Subgroup.zpowers ĝ : Set G) := by
    rwa [← Subgroup.normal_mul]
  obtain ⟨n, hn, z, hz, rfl⟩ := hset
  obtain ⟨m, rfl⟩ := (Subgroup.mem_zpowers_iff).mp hz
  have hsq : ∀ k : ℤ, ĝ ^ (2 * k) ∈ N := fun k => by
    rw [zpow_mul]
    exact Subgroup.zpow_mem N (by rw [zpow_two]; exact hĝ2) k
  rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    subst hk
    exact N.mul_mem hn (by rw [show k + k = 2 * k by ring]; exact hsq k)
  · right
    subst hk
    have hrw : n * ĝ ^ (2 * k + 1) * ĝ = n * (ĝ ^ (2 * k) * (ĝ * ĝ)) := by
      rw [zpow_add, zpow_one]
      group
    rw [hrw]
    exact N.mul_mem hn (N.mul_mem (hsq k) hĝ2)

/-- **Index 2 of the kernel inside the involution overgroup**, decomposition form: if
`⟨ĝ⟩ ∉ N'`, and every element outside `N'` returns to it after multiplying by `⟨ĝ⟩`, then
`N'` has index 2. -/
theorem index_eq_two_of_decomp {U₀ : Subgroup G} {N' : Subgroup ↥U₀} {s : ↥U₀}
    (hs : s ∉ N') (hdec : ∀ b : ↥U₀, b ∉ N' → b * s ∈ N') : N'.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨s, fun b => ?_⟩
  by_cases hb : b ∈ N'
  · refine Or.inr ⟨hb, fun hbs => hs ?_⟩
    have : b⁻¹ * (b * s) ∈ N' := N'.mul_mem (N'.inv_mem hb) hbs
    rwa [inv_mul_cancel_left] at this
  · exact Or.inl ⟨hdec b hb, hb⟩

/-- **Index 2 of a normal subgroup inside its involution overgroup**: for `N` normal with
`ĝ² ∈ N`, the subgroup `N` has index 2 inside `U₀ = N ⊔ ⟨ĝ⟩` (combining the coset
decomposition `mem_or_mul_mem_of_mem_sup` with `index_eq_two_of_decomp`). -/
theorem subgroupOf_index_eq_two_of_sup {N : Subgroup G} [N.Normal] {ĝ : G}
    (hĝ2 : ĝ * ĝ ∈ N) {U₀ : Subgroup G} (hU₀ : U₀ = N ⊔ Subgroup.zpowers ĝ)
    (hmem : ĝ ∈ U₀) (hsUnot : (⟨ĝ, hmem⟩ : ↥U₀) ∉ N.subgroupOf U₀) :
    (N.subgroupOf U₀).index = 2 := by
  refine index_eq_two_of_decomp hsUnot (fun b hb => ?_)
  have hbU : (b : G) ∈ N ⊔ Subgroup.zpowers ĝ := hU₀ ▸ b.2
  rcases mem_or_mul_mem_of_mem_sup hĝ2 hbU with hbN | hbg
  · exact absurd (Subgroup.mem_subgroupOf.mpr hbN) hb
  · exact Subgroup.mem_subgroupOf.mpr hbg

end IndexTwo

/-! ## The Galois-view repackaging (the `kerGal` idiom, for overgroups of `ker ρ`) -/

section ToGal

/-- The identity bridge into the `AlgEquiv`-view Galois group (inverse of
`ResidueLift.toAbs`; keeps mixed-view products elaborable). -/
def toGalElem (x : AbsGalQ2) : Kummer.GaloisGroup ℚ_[2] := x

/-- A subgroup of `AbsGalQ2`, repackaged in the `AlgEquiv`-view Galois group (the
`ResidueLift.kerGal` idiom: same carrier; the closure proofs cross the two views'
default-transparency-equal group structures by `rfl`-bridges). -/
def toGal (U : Subgroup AbsGalQ2) : Subgroup (Kummer.GaloisGroup ℚ_[2]) where
  carrier := {x : Kummer.GaloisGroup ℚ_[2] | ResidueLift.toAbs x ∈ U}
  one_mem' := U.one_mem
  mul_mem' := fun {_ _} ha hb => U.mul_mem ha hb
  inv_mem' := fun {_} ha => U.inv_mem ha

private theorem mem_toGal (U : Subgroup AbsGalQ2) (x : Kummer.GaloisGroup ℚ_[2]) :
    x ∈ U ↔ x ∈ toGal U := Iff.rfl

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

omit [Finite C] in
/-- `toGal` of an overgroup of `ker ρ` is open (it contains the open `kerGal ρ`). -/
theorem toGal_isOpen_of_ker_le (ρ : ContinuousMonoidHom AbsGalQ2 C) {U : Subgroup AbsGalQ2}
    (hle : (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ≤ U) :
    IsOpen ((toGal U : Subgroup (Kummer.GaloisGroup ℚ_[2]))
      : Set (Kummer.GaloisGroup ℚ_[2])) := by
  exact Subgroup.isOpen_mono
    (fun x hx => (mem_toGal U x).mp (hle ((ResidueLift.mem_kerGal ρ x).mpr hx)))
    (ResidueLift.kerGal_isOpen ρ)

end ToGal

/-! ## The generic `H²ofFun`-vanishing transport along a continuous multiplicative map -/

section Transport

variable {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [DistribMulAction G₁ (ZMod 2)] [ContinuousSMul G₁ (ZMod 2)]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  [DistribMulAction G₂ (ZMod 2)] [ContinuousSMul G₂ (ZMod 2)]

/-- **`H²ofFun`-vanishing pulls back along a continuous multiplicative map** (trivial
coefficients): if `F₁ = F₂ ∘ (e × e)` pointwise, `F₁` is a 2-cocycle, and `F₂` is a 2-cocycle
with trivial `H²ofFun` class, then so is `F₁` — the `B²`-witness `ψ` of `F₂` pulls back to
`ψ ∘ e` (`δ¹` commutes with precomposition by multiplicativity; the trivial actions make the
`smul`-terms invisible). -/
theorem H2ofFun_eq_zero_comp (e : G₁ →* G₂) (hec : Continuous e)
    (htriv₁ : ∀ (g : G₁) (m : ZMod 2), g • m = m)
    (htriv₂ : ∀ (g : G₂) (m : ZMod 2), g • m = m)
    {F₁ : G₁ × G₁ → ZMod 2} {F₂ : G₂ × G₂ → ZMod 2}
    (hcomp : ∀ p : G₁ × G₁, F₁ p = F₂ (e p.1, e p.2))
    (hZ1 : F₁ ∈ Z2 G₁ (ZMod 2)) (hZ2 : F₂ ∈ Z2 G₂ (ZMod 2))
    (hvan : H2ofFun G₂ F₂ = 0) :
    H2ofFun G₁ F₁ = 0 := by
  -- extract the `B²`-witness on the `G₂` side
  rw [H2ofFun_of_mem hZ2] at hvan
  have hB2 : F₂ ∈ B2 G₂ (ZMod 2) :=
    AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp hvan)
  obtain ⟨ψ, hψC1, hψeq⟩ := AddSubgroup.mem_map.mp hB2
  -- pull it back
  have hδeq : dOne G₁ (ZMod 2) (fun x => ψ (e x)) = F₁ := by
    funext p
    have hp := congrFun hψeq (e p.1, e p.2)
    have hR : F₂ (e p.1, e p.2) = ψ (e p.2) - ψ (e p.1 * e p.2) + ψ (e p.1) := by
      rw [← hp]
      show e p.1 • ψ (e p.2) - ψ (e p.1 * e p.2) + ψ (e p.1) = _
      rw [htriv₂]
    show p.1 • ψ (e p.2) - ψ (e (p.1 * p.2)) + ψ (e p.1) = F₁ p
    rw [htriv₁, hcomp p, hR, map_mul]
  have hB1 : F₁ ∈ B2 G₁ (ZMod 2) :=
    AddSubgroup.mem_map.mpr ⟨fun x => ψ (e x), mem_C1_iff.mpr (hψC1.comp hec), hδeq⟩
  exact ShapiroDeepness.H2ofFun_eq_zero_of_H2mk hZ1
    ((QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hB1))

end Transport

/-! ## `evensNormFun` along an index-preserving multiplicative map -/

section EvensComp

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

/-- **`evensNormFun` is functorial along a multiplicative map matching the index-2 data**:
`evensAux`/`bS` are membership tests and `s`-translates only (no transversal choice), so with
corresponding memberships (`hmem`), matched slices (`hs`), and matched scalar values (`hval`),
the two Evens cochains agree pointwise. -/
theorem evensNormFun_comp (e : G₁ →* G₂) {U₁ : Subgroup G₁} {U₂ : Subgroup G₂}
    {s₁ : G₁} {s₂ : G₂}
    (hmem : ∀ x : G₁, x ∈ U₁ ↔ e x ∈ U₂) (hs : e s₁ = s₂)
    (hUi₁ : U₁.index = 2) (hs₁ : s₁ ∉ U₁) (hUi₂ : U₂.index = 2) (hs₂ : s₂ ∉ U₂)
    (α₁ : ↥U₁ → ZMod 2) (α₂ : ↥U₂ → ZMod 2)
    (hval : ∀ (x : G₁) (hx : x ∈ U₁), α₁ ⟨x, hx⟩ = α₂ ⟨e x, (hmem x).mp hx⟩)
    (p : G₁ × G₁) :
    evensNormFun U₁ s₁ α₁ p = evensNormFun U₂ s₂ α₂ (e p.1, e p.2) := by
  classical
  -- the `evensAux` agreement
  have hAux : ∀ x : G₁, evensAux U₁ s₁ α₁ x = evensAux U₂ s₂ α₂ (e x) := by
    intro x
    by_cases hx : x ∈ U₁
    · rw [evensAux_of_mem α₁ hx, evensAux_of_mem α₂ ((hmem x).mp hx)]
      exact hval x hx
    · have hx₂ : e x ∉ U₂ := fun h => hx ((hmem x).mpr h)
      rw [evensAux_of_notMem hUi₁ hs₁ α₁ hx, evensAux_of_notMem hUi₂ hs₂ α₂ hx₂]
      have hxs : x * s₁ ∈ U₁ := notMem_mul_mem hUi₁ hx hs₁
      have hcast : (⟨e (x * s₁), (hmem _).mp hxs⟩ : ↥U₂)
          = ⟨e x * s₂, notMem_mul_mem hUi₂ hx₂ hs₂⟩ :=
        Subtype.ext (show e (x * s₁) = e x * s₂ by rw [map_mul, hs])
      rw [hval (x * s₁) hxs, hcast]
  -- the `bS` agreement
  have hbS : ∀ x : G₁, bS U₁ s₁ α₁ x = bS U₂ s₂ α₂ (e x) := by
    intro x
    show evensAux U₁ s₁ α₁ (s₁⁻¹ * x) = evensAux U₂ s₂ α₂ (s₂⁻¹ * e x)
    rw [show s₂⁻¹ * e x = e (s₁⁻¹ * x) by rw [map_mul, map_inv, hs]]
    exact hAux (s₁⁻¹ * x)
  -- the `evensNormFun` agreement
  show (if p.1 ∈ U₁ then evensAux U₁ s₁ α₁ p.1 * bS U₁ s₁ α₁ p.2
      else evensAux U₁ s₁ α₁ p.1 * evensAux U₁ s₁ α₁ p.2
        + evensAux U₁ s₁ α₁ p.2 * bS U₁ s₁ α₁ p.2)
    = (if e p.1 ∈ U₂ then evensAux U₂ s₂ α₂ (e p.1) * bS U₂ s₂ α₂ (e p.2)
      else evensAux U₂ s₂ α₂ (e p.1) * evensAux U₂ s₂ α₂ (e p.2)
        + evensAux U₂ s₂ α₂ (e p.2) * bS U₂ s₂ α₂ (e p.2))
  by_cases hp : p.1 ∈ U₁
  · rw [if_pos hp, if_pos ((hmem p.1).mp hp), hAux, hbS]
  · rw [if_neg hp, if_neg (fun h => hp ((hmem p.1).mpr h)), hAux p.1, hAux p.2, hbS p.2]

end EvensComp

/-! ## The capstone: the involution `hvanish` in `ker ρ`-vocabulary -/

section Capstone

open SectionSix LocalKummer ShapiroDeepness

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

omit [Finite C] in
/-- The kernel of a continuous hom into a finite discrete group is open (its carrier is the
preimage of the open point `{1}`). -/
private theorem ker_isOpen (ρ : ContinuousMonoidHom AbsGalQ2 C) :
    IsOpen ((ρ.toMonoidHom.ker : Subgroup AbsGalQ2) : Set AbsGalQ2) := by
  have hset : ((ρ.toMonoidHom.ker : Subgroup AbsGalQ2) : Set AbsGalQ2) = ⇑ρ ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rfl
  rw [hset]
  exact (isOpen_discrete {1}).preimage ρ.continuous_toFun

/-- **`IsDeepUnit` transports along a carrier inclusion**: if every element of `N₁` lies in
`N₂`, a deep unit for `N₂` is a deep unit for `N₁` (used to move the deep witness from
`ker ρ` up to `(splitField ρ).fixingSubgroup`). -/
private theorem isDeepUnit_of_forall_mem {N₁ N₂ : Subgroup (Kummer.GaloisGroup ℚ_[2])} {A : ℚ̄₂}
    (h : ∀ g : Kummer.GaloisGroup ℚ_[2], g ∈ N₁ → g ∈ N₂) (hd : IsDeepUnit N₂ A) :
    IsDeepUnit N₁ A := by
  obtain ⟨hA0, hAfix, b, hbfix, hbeq, hbnorm⟩ := hd
  exact ⟨hA0, fun g hg => hAfix g (h g hg), b, fun g hg => hbfix g (h g hg), hbeq, hbnorm⟩

omit [DiscreteTopology C] [Finite C] in
/-- **The Galois-view index-2 brick**: `kerGal ρ` has index 2 inside `toGal U₀` for
`U₀ = ker ρ ⊔ ⟨ĝ⟩`, the `kerGal`-idiom mirror of `subgroupOf_index_eq_two_of_sup`. -/
private theorem kerGal_subgroupOf_toGal_index_eq_two (ρ : ContinuousMonoidHom AbsGalQ2 C)
    {ĝ : AbsGalQ2} (hĝN : ĝ ∉ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (hĝ2 : ĝ * ĝ ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) {U₀ : Subgroup AbsGalQ2}
    (hU₀ : U₀ = (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ⊔ Subgroup.zpowers ĝ)
    (hmem : ĝ ∈ U₀) :
    ((ResidueLift.kerGal ρ).subgroupOf (toGal U₀)).index = 2 := by
  have hgmemGal : toGalElem ĝ ∈ toGal U₀ := hmem
  refine index_eq_two_of_decomp (s := ⟨toGalElem ĝ, hgmemGal⟩)
    (fun h => hĝN ((ResidueLift.mem_kerGal ρ (toGalElem ĝ)).mpr
      (Subgroup.mem_subgroupOf.mp h)))
    (fun b hb => ?_)
  have hbU : ResidueLift.toAbs b.1 ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      ⊔ Subgroup.zpowers ĝ := hU₀ ▸ ((mem_toGal U₀ b.1).mpr b.2)
  rcases mem_or_mul_mem_of_mem_sup hĝ2 hbU with hbN | hbg
  · exact absurd (Subgroup.mem_subgroupOf.mpr
      ((ResidueLift.mem_kerGal ρ b.1).mp hbN)) hb
  · refine Subgroup.mem_subgroupOf.mpr ?_
    refine (ResidueLift.mem_kerGal ρ _).mp ?_
    have hbr : ResidueLift.toAbs ((b * ⟨toGalElem ĝ, hgmemGal⟩ : ↥(toGal U₀))
        : Kummer.GaloisGroup ℚ_[2])
        = ResidueLift.toAbs b.1 * ĝ := rfl
    show ResidueLift.toAbs ((b * ⟨toGalElem ĝ, hgmemGal⟩ : ↥(toGal U₀))
        : Kummer.GaloisGroup ℚ_[2]) ∈ ρ.toMonoidHom.ker
    rw [hbr]
    exact hbg

/-- **Additivity of the Kummer cocycle on a `subgroupOf` of Galois fixing-subgroups**: the
`hα`-style side condition for `lemma_6_16`, with the double-subtype coercion factored out. -/
private theorem kummerCocycleFun_add_on_subgroupOf {W L' : Subgroup (Kummer.GaloisGroup ℚ_[2])}
    {A β : ℚ̄₂} (hβ : β ^ 2 = A) (hβ0 : β ≠ 0) (hAfix : ∀ g ∈ L', g • A = A)
    (w z : ↥(L'.subgroupOf W)) :
    Kummer.kummerCocycleFun β ((w * z : ↥W) : Kummer.GaloisGroup ℚ_[2])
      = Kummer.kummerCocycleFun β ((w : ↥W) : Kummer.GaloisGroup ℚ_[2])
        + Kummer.kummerCocycleFun β ((z : ↥W) : Kummer.GaloisGroup ℚ_[2]) := by
  have hwL := Subgroup.mem_subgroupOf.mp w.2
  have hzL := Subgroup.mem_subgroupOf.mp z.2
  have hmul : ((w * z : ↥W) : Kummer.GaloisGroup ℚ_[2])
      = ((w : ↥W) : Kummer.GaloisGroup ℚ_[2]) * ((z : ↥W) : Kummer.GaloisGroup ℚ_[2]) := rfl
  rw [hmul]
  exact kummerCocycleFun_hom_on hβ hβ0 hAfix ⟨_, hwL⟩ ⟨_, hzL⟩

/-- **The involution `hvanish` over `ker ρ`** (the Lemma 6.17 vanishing proof, the U₀-splice): for a deep block
coordinate `α` on `N = ker ρ` and an involution lift `ĝ` (`ĝ ∉ N`, `ĝ² ∈ N`,
`U₀ = N ⊔ ⟨ĝ⟩`), the Evens-norm inner cochain of the reducer's involution orbit has trivial
`H²ofFun` class.  This is the reducer's `hvanish`-input at the involution orbits, with the
inner cochain matching `ShapiroRead.hcoh_involution`'s output verbatim.

Chains: `B¹ = 0` extraction (the deep witness's Kummer cocycle *equals* `α`), the splitting
tower `k = fixedField (toGal U₀) ≤ L = splitField ρ` with the infinite Galois correspondence,
the c2a Kummer package (`kummer_presentation_of_index_two`), the c2c analytic `hunram`
(`hunram_involution`), the c2b spine (`hvanish_involution` = Lemma 6.16 + descent), and the
carrier splice pulling the `B²`-witness back along the underlying-identity `↥U₀ →
↥k.fixingSubgroup`. -/
theorem hvanish_involution_ker (R : LocalReciprocity) (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (horient : TameUnitOrientation R B.tameF)
    (α : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → ZMod 2)
    (hαZ1 : α ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
    (hdeep : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) α
      ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (ĝ : AbsGalQ2) (hĝN : ĝ ∉ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (hĝ2 : ĝ * ĝ ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (U₀ : Subgroup AbsGalQ2)
    (hU₀ : U₀ = (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ⊔ Subgroup.zpowers ĝ)
    (hmem : ĝ ∈ U₀) :
    H2ofFun ↥U₀ (evensNormFun
      ((ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subgroupOf U₀) ⟨ĝ, hmem⟩
      (fun w => α ⟨w.1.1, w.2⟩)) = 0 := by
  classical
  -- ### the deep witness, extracted on the nose (`B¹ = 0`)
  obtain ⟨A, β, hdeepN, hβ, hβ0, heqN⟩ := hdeep
  have htrivN : ∀ (n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (m : ZMod 2),
      n • m = m := fun _ _ => rfl
  have hZ1kcf : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
      Kummer.kummerCocycleFun β (n : AbsGalQ2)) ∈
      Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) := by
    rw [mem_Z1_iff_of_trivial htrivN]
    exact ⟨(Kummer.kummerCocycleFun_continuous β).comp continuous_subtype_val,
      kummerCocycleFun_hom_on hβ hβ0 hdeepN.2.1⟩
  have hfeq : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
      Kummer.kummerCocycleFun β (n : AbsGalQ2)) = α :=
    eq_of_H1ofFun_eq htrivN hZ1kcf hαZ1 heqN
  -- ### the tower
  haveI : FiniteDimensional ℚ_[2] (ResidueLift.splitField ρ) :=
    ResidueLift.splitField_finiteDimensional ρ
  have hLfix : (ResidueLift.splitField ρ).fixingSubgroup = ResidueLift.kerGal ρ :=
    ResidueLift.fixingSubgroup_splitField ρ
  have hNle : (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ≤ U₀ := hU₀ ▸ le_sup_left
  have hU₀open : IsOpen ((toGal U₀ : Subgroup (Kummer.GaloisGroup ℚ_[2]))
      : Set (Kummer.GaloisGroup ℚ_[2])) := toGal_isOpen_of_ker_le ρ hNle
  have hkfix : (IntermediateField.fixedField (toGal U₀)).fixingSubgroup = toGal U₀ :=
    InfiniteGalois.fixingSubgroup_fixedField
      ⟨toGal U₀, Subgroup.isClosed_of_isOpen _ hU₀open⟩
  haveI : FiniteDimensional ℚ_[2] (IntermediateField.fixedField (toGal U₀)) := by
    refine (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField (toGal U₀))).mp ?_
    rw [hkfix]
    exact hU₀open
  have hkerm : ∀ y : Kummer.GaloisGroup ℚ_[2],
      y ∈ (ResidueLift.splitField ρ).fixingSubgroup
        ↔ y ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
    intro y
    rw [hLfix]
    exact (ResidueLift.mem_kerGal ρ y).symm
  have hkL : IntermediateField.fixedField (toGal U₀) ≤ ResidueLift.splitField ρ := by
    intro x hx g
    exact hx ⟨g.1, (mem_toGal U₀ g.1).mp (hNle ((ResidueLift.mem_kerGal ρ g.1).mpr g.2))⟩
  -- ### index 2, both views
  have hsUnot : (⟨ĝ, hmem⟩ : ↥U₀)
      ∉ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subgroupOf U₀ :=
    fun h => hĝN (Subgroup.mem_subgroupOf.mp h)
  have hUiU : ((ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subgroupOf U₀).index = 2 :=
    subgroupOf_index_eq_two_of_sup hĝ2 hU₀ hmem hsUnot
  have hindexK : (((ResidueLift.splitField ρ).fixingSubgroup).subgroupOf
      (IntermediateField.fixedField (toGal U₀)).fixingSubgroup).index = 2 := by
    rw [hLfix, hkfix]
    exact kerGal_subgroupOf_toGal_index_eq_two ρ hĝN hĝ2 hU₀ hmem
  -- ### the deep unit over `L`
  have hdeepL : IsDeepUnit (ResidueLift.splitField ρ).fixingSubgroup A :=
    isDeepUnit_of_forall_mem (fun g hg => (hkerm g).mp hg) hdeepN
  -- ### the c2a Kummer package and the c2c `hunram`
  obtain ⟨d, δ, u, v, hδ, hδL, hLδ, hAuv⟩ :=
    kummer_presentation_of_index_two (IntermediateField.fixedField (toGal U₀))
      (ResidueLift.splitField ρ) hkL hindexK A hdeepL
  have hunram := UnramifiedBridge.hunram_involution R B c hc ρ hfac horient hkL hindexK hLfix
  -- ### the carrier bridge `↥U₀ →* ↥k.fixingSubgroup` (underlying identity)
  have hkm : ∀ x : ↥U₀,
      (x : AbsGalQ2) ∈ (IntermediateField.fixedField (toGal U₀)).fixingSubgroup := by
    intro x
    rw [hkfix]
    exact (mem_toGal U₀ x.1).mp x.2
  let e₀ : ↥U₀ →* ↥(IntermediateField.fixedField (toGal U₀)).fixingSubgroup :=
    { toFun := fun x => ⟨x.1, hkm x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have he₀c : Continuous e₀ := Continuous.subtype_mk continuous_subtype_val _
  have hmemiff : ∀ x : ↥U₀,
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subgroupOf U₀
        ↔ e₀ x ∈ ((ResidueLift.splitField ρ).fixingSubgroup).subgroupOf
          (IntermediateField.fixedField (toGal U₀)).fixingSubgroup := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (hkerm x.1).symm
  have hsKnot : e₀ ⟨ĝ, hmem⟩ ∉ ((ResidueLift.splitField ρ).fixingSubgroup).subgroupOf
      (IntermediateField.fixedField (toGal U₀)).fixingSubgroup :=
    fun h => hsUnot ((hmemiff ⟨ĝ, hmem⟩).mpr h)
  have htrivK : ∀ (g : ↥(IntermediateField.fixedField (toGal U₀)).fixingSubgroup)
      (m : ZMod 2), g • m = m := fun _ _ => rfl
  have hUoK : IsOpen (((((ResidueLift.splitField ρ).fixingSubgroup).subgroupOf
      (IntermediateField.fixedField (toGal U₀)).fixingSubgroup)
      : Subgroup ↥(IntermediateField.fixedField (toGal U₀)).fixingSubgroup)
      : Set ↥(IntermediateField.fixedField (toGal U₀)).fixingSubgroup) := by
    have hLopen : IsOpen (((ResidueLift.splitField ρ).fixingSubgroup
        : Subgroup (Kummer.GaloisGroup ℚ_[2])) : Set (Kummer.GaloisGroup ℚ_[2])) := by
      rw [hLfix]
      exact ResidueLift.kerGal_isOpen ρ
    exact hLopen.preimage continuous_subtype_val
  have hAfixL : ∀ g ∈ (ResidueLift.splitField ρ).fixingSubgroup, g • A = A := hdeepL.2.1
  have hα : ∀ w z : ↥(((ResidueLift.splitField ρ).fixingSubgroup).subgroupOf
      (IntermediateField.fixedField (toGal U₀)).fixingSubgroup),
      Kummer.kummerCocycleFun β
        ((w * z : ↥(IntermediateField.fixedField (toGal U₀)).fixingSubgroup)
          : Kummer.GaloisGroup ℚ_[2])
        = Kummer.kummerCocycleFun β
            ((w : ↥(IntermediateField.fixedField (toGal U₀)).fixingSubgroup)
              : Kummer.GaloisGroup ℚ_[2])
          + Kummer.kummerCocycleFun β
              ((z : ↥(IntermediateField.fixedField (toGal U₀)).fixingSubgroup)
                : Kummer.GaloisGroup ℚ_[2]) :=
    kummerCocycleFun_add_on_subgroupOf hβ hβ0 hAfixL
  have hαc : Continuous fun w : ↥(((ResidueLift.splitField ρ).fixingSubgroup).subgroupOf
      (IntermediateField.fixedField (toGal U₀)).fixingSubgroup) =>
      Kummer.kummerCocycleFun β
        ((w : ↥(IntermediateField.fixedField (toGal U₀)).fixingSubgroup)
          : Kummer.GaloisGroup ℚ_[2]) :=
    (Kummer.kummerCocycleFun_continuous β).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  -- ### the field-side vanishing (c2b spine = Lemma 6.16)
  have hvan := hvanish_involution (IntermediateField.fixedField (toGal U₀))
    (ResidueLift.splitField ρ) hkL hindexK hunram d δ hδ hδL hLδ A β hdeepL hβ hβ0
    u v hAuv (e₀ ⟨ĝ, hmem⟩) hsKnot htrivK hUoK hα hαc
  -- ### the U₀-side inner is the Kummer cocycle on the nose
  have hinner : (fun w : ↥((ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subgroupOf U₀) =>
      α ⟨w.1.1, w.2⟩)
      = fun w : ↥((ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subgroupOf U₀) =>
        Kummer.kummerCocycleFun β (w.1.1 : AbsGalQ2) := by
    funext w
    rw [← hfeq]
  rw [hinner]
  -- ### `Z²`-memberships on both sides
  have hNopen : IsOpen ((ρ.toMonoidHom.ker : Subgroup AbsGalQ2) : Set AbsGalQ2) := ker_isOpen ρ
  have hUoU : IsOpen ((((ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subgroupOf U₀)
      : Subgroup ↥U₀) : Set ↥U₀) := hNopen.preimage continuous_subtype_val
  have htrivU : ∀ (g : ↥U₀) (m : ZMod 2), g • m = m := fun _ _ => rfl
  have hαU : ∀ w z : ↥((ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subgroupOf U₀),
      Kummer.kummerCocycleFun β (((w * z).1.1 : AbsGalQ2))
        = Kummer.kummerCocycleFun β ((w.1.1 : AbsGalQ2))
          + Kummer.kummerCocycleFun β ((z.1.1 : AbsGalQ2)) :=
    fun w z => kummerCocycleFun_hom_on hβ hβ0 hdeepN.2.1 ⟨w.1.1, w.2⟩ ⟨z.1.1, z.2⟩
  have hαcU : Continuous fun w : ↥((ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subgroupOf U₀) =>
      Kummer.kummerCocycleFun β (w.1.1 : AbsGalQ2) :=
    (Kummer.kummerCocycleFun_continuous β).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hZ2U := evensNormFun_mem_Z2 htrivU hUoU hUiU hsUnot _ hαU hαcU
  have hZ2K := evensNormFun_mem_Z2 htrivK hUoK hindexK hsKnot _ hα hαc
  -- ### transport the vanishing along `e₀`
  exact H2ofFun_eq_zero_comp e₀ he₀c htrivU htrivK
    (evensNormFun_comp e₀ hmemiff rfl hUiU hsUnot hindexK hsKnot _ _ (fun x hx => rfl))
    hZ2U hZ2K hvan

end Capstone

/-! ## The square/free `hvanish` in `ker ρ`-vocabulary (the deep-cup vanishing) -/

section CupKer

open SectionSix LocalKummer ShapiroDeepness ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- **`cup11Fun` functoriality** along a multiplicative map (trivial coefficients): matched scalar
values give equal cup cochains under `(e × e)`. -/
theorem cup11Fun_comp {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    [DistribMulAction G₁ (ZMod 2)] [DistribMulAction G₂ (ZMod 2)]
    (htriv₁ : ∀ (g : G₁) (m : ZMod 2), g • m = m)
    (htriv₂ : ∀ (g : G₂) (m : ZMod 2), g • m = m)
    (e : G₁ →* G₂) (α₁ β₁ : G₁ → ZMod 2) (α₂ β₂ : G₂ → ZMod 2)
    (hα : ∀ x, α₁ x = α₂ (e x)) (hβ : ∀ x, β₁ x = β₂ (e x)) (p : G₁ × G₁) :
    cup11Fun AddMonoidHom.mul α₁ β₁ p = cup11Fun AddMonoidHom.mul α₂ β₂ (e p.1, e p.2) := by
  show AddMonoidHom.mul (α₁ p.1) (p.1 • β₁ p.2)
      = AddMonoidHom.mul (α₂ (e p.1)) (e p.1 • β₂ (e p.2))
  rw [htriv₁, htriv₂, hα, hβ]

omit [Finite C] in
/-- **The square/free `hvanish` over `ker ρ`** (the Lemma 6.17 vanishing proof): the cup of two deep block coordinates
over `N = ker ρ` has trivial `H²ofFun` class.  Same tower/carrier splice as
`hvanish_involution_ker`, but with `U = N` (no lift, no index-2) and the cup in place of the
Evens norm; the field-side vanishing is `hvanish_cup` (eq.-(94) orthogonality). -/
theorem hvanish_cup_ker (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (α β : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → ZMod 2)
    (hαZ1 : α ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
    (hβZ1 : β ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
    (hαdeep : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) α
      ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (hβdeep : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) β
      ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    H2ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      (cup11Fun AddMonoidHom.mul α β) = 0 := by
  classical
  haveI : FiniteDimensional ℚ_[2] (ResidueLift.splitField ρ) :=
    ResidueLift.splitField_finiteDimensional ρ
  have hkfix : (ResidueLift.splitField ρ).fixingSubgroup = ResidueLift.kerGal ρ :=
    ResidueLift.fixingSubgroup_splitField ρ
  have hkerm : ∀ y : Kummer.GaloisGroup ℚ_[2],
      y ∈ (ResidueLift.splitField ρ).fixingSubgroup
        ↔ y ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
    intro y; rw [hkfix]; exact (ResidueLift.mem_kerGal ρ y).symm
  have hkm : ∀ x : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2),
      (x : AbsGalQ2) ∈ (ResidueLift.splitField ρ).fixingSubgroup := fun x => (hkerm x.1).mpr x.2
  let e₀ : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) →*
      ↥(ResidueLift.splitField ρ).fixingSubgroup :=
    { toFun := fun x => ⟨x.1, hkm x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have he₀c : Continuous e₀ := Continuous.subtype_mk continuous_subtype_val _
  have htrivK : ∀ (g : ↥(ResidueLift.splitField ρ).fixingSubgroup) (m : ZMod 2), g • m = m :=
    fun _ _ => rfl
  have htrivN : ∀ (g : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (m : ZMod 2), g • m = m :=
    fun _ _ => rfl
  -- the field-side deep cocycle of a `ker ρ` deep class
  have hfield : ∀ (γ : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → ZMod 2),
      γ ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) →
      H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) γ
        ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) →
      ∃ (γ' : ↥(ResidueLift.splitField ρ).fixingSubgroup → ZMod 2)
        (hγ'Z1 : γ' ∈ Z1 ↥(ResidueLift.splitField ρ).fixingSubgroup (ZMod 2)),
        H1mk (ResidueLift.splitField ρ).fixingSubgroup (ZMod 2) ⟨γ', hγ'Z1⟩
          ∈ deepClasses (ResidueLift.splitField ρ).fixingSubgroup ∧
        ∀ x, γ x = γ' (e₀ x) := by
    intro γ hγZ1 hγdeep
    obtain ⟨A, βk, hdeepA, hβk, hβk0, hclass⟩ := hγdeep
    have hAfix : ∀ g ∈ (ResidueLift.splitField ρ).fixingSubgroup, g • A = A :=
      fun g hg => hdeepA.2.1 g ((hkerm g).mp hg)
    have hγeq : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        Kummer.kummerCocycleFun βk (n : AbsGalQ2)) = γ := by
      refine eq_of_H1ofFun_eq htrivN ?_ hγZ1 hclass
      rw [mem_Z1_iff_of_trivial htrivN]
      exact ⟨(Kummer.kummerCocycleFun_continuous βk).comp continuous_subtype_val,
        kummerCocycleFun_hom_on hβk hβk0 hdeepA.2.1⟩
    have hZ1' : (fun w : ↥(ResidueLift.splitField ρ).fixingSubgroup =>
        Kummer.kummerCocycleFun βk (w : Kummer.GaloisGroup ℚ_[2]))
        ∈ Z1 ↥(ResidueLift.splitField ρ).fixingSubgroup (ZMod 2) := by
      rw [mem_Z1_iff_of_trivial htrivK]
      exact ⟨(Kummer.kummerCocycleFun_continuous βk).comp continuous_subtype_val,
        kummerCocycleFun_hom_on hβk hβk0 hAfix⟩
    refine ⟨fun w => Kummer.kummerCocycleFun βk (w : Kummer.GaloisGroup ℚ_[2]), hZ1', ?_, ?_⟩
    · refine ⟨A, βk, ⟨hdeepA.1, hAfix, ?_⟩, hβk, hβk0, H1ofFun_of_mem hZ1'⟩
      obtain ⟨b, hbf, hbe, hbn⟩ := hdeepA.2.2
      exact ⟨b, fun g hg => hbf g ((hkerm g).mp hg), hbe, hbn⟩
    · intro x
      exact (congrFun hγeq x).symm
  obtain ⟨α', hα'Z1, hα'deep, hα'eq⟩ := hfield α hαZ1 hαdeep
  obtain ⟨β', hβ'Z1, hβ'deep, hβ'eq⟩ := hfield β hβZ1 hβdeep
  -- field-side vanishing (eq.-(94))
  have hvan := hvanish_cup (ResidueLift.splitField ρ) htrivK ⟨α', hα'Z1⟩ ⟨β', hβ'Z1⟩
    hα'deep hβ'deep
  -- transport along `e₀`
  have hZ2N : cup11Fun AddMonoidHom.mul α β
      ∈ Z2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
    cup11_mem_Z2 AddMonoidHom.mul (fun g m n => by rw [htrivN, htrivN, htrivN])
      ⟨α, hαZ1⟩ ⟨β, hβZ1⟩
  have hZ2K : cup11Fun AddMonoidHom.mul α' β'
      ∈ Z2 ↥(ResidueLift.splitField ρ).fixingSubgroup (ZMod 2) :=
    cup11_mem_Z2 AddMonoidHom.mul (fun g m n => by rw [htrivK, htrivK, htrivK])
      ⟨α', hα'Z1⟩ ⟨β', hβ'Z1⟩
  exact H2ofFun_eq_zero_comp e₀ he₀c htrivN htrivK
    (cup11Fun_comp htrivN htrivK e₀ α β α' β' hα'eq hβ'eq)
    hZ2N hZ2K hvan

end CupKer

end InvolutionSplice

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 6.16 = ⟦lem-evensvanish⟧
-/
