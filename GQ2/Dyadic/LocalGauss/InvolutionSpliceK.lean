/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.LocalGauss.DeepPackage
import GQ2.InvolutionSplice

/-!
# The involution `hvanish` over a general local source (LG4c, part 3)

`GQ2.InvolutionSplice.hvanish_involution_ker` (`GQ2/InvolutionSplice.lean` :357) retyped from
`G_ℚ₂` to an arbitrary topological group `Γ` with an anchor `anc : Γ →ₜ* G_ℚ₂` (LG4a's anchoring
convention, `LocalGauss/DeepPackage.lean` §1).  The `ℚ₂` original is untouched.

## What actually needed retyping

`GQ2/InvolutionSplice.lean`'s §Extraction, §IndexTwo, §Transport and §EvensComp are stated over an
**abstract `G`** already, hence consumed verbatim:

* `GQ2.InvolutionSplice.eq_of_H1ofFun_eq` (trivial-coefficient rigidity — see the dedup note on
  `eq_of_H1ofFun_eq_K` below);
* `mem_or_mul_mem_of_mem_sup`, `index_eq_two_of_decomp`, `subgroupOf_index_eq_two_of_sup`;
* `H2ofFun_eq_zero_comp` (the `H²`-vanishing pullback along a continuous multiplicative map);
* `evensNormFun_comp` (functoriality of the Evens cochain).

What is `AbsGalQ2`-typed is the **capstone** `hvanish_involution_ker` together with its
`ResidueLift`-based tower construction, and that is what is rebuilt here.

## The `(k, L)` threading and the AX3/AX4 interface (memo risk 3, c2c route)

The `ℚ₂` proof *constructs* its tower internally: `L := ResidueLift.splitField ρ`,
`k := fixedField (toGal U₀)`, and it obtains the analytic input `hunram` from
`GQ2.UnramifiedBridge.hunram_involution`, whose own proof consumes the local reciprocity /
boundary-map package (`R`, `B`, `c`, `hfac`, `horient`) and the B13 dyadic unit filtration — i.e.
exactly the `AX3`/`AX4` field-side interface of the dyadic campaign.

Following LG4a §6 (`hvanish_cup_ker_K`, which threads `(k, hker)` rather than building the
splitting field) and LG3 (`prop_6_18_unramified_K`, whose three binders `tameFK`/`htameFK`/`hfac`
carry the AX3/AX4 content), **the tower and the analytic input are threaded as explicit hypothesis
binders**.  There is no axiom here and the census is unchanged; concretely
`hvanish_involution_ker_K` takes

| binder | content | `ℚ₂` source it replaces |
|---|---|---|
| `k`, `L`, `[FiniteDimensional ℚ_[2] k]`, `[FiniteDimensional ℚ_[2] L]`, `hkL : k ≤ L` | the tower | `ResidueLift.splitField` + `fixedField (toGal U₀)` |
| `hkerL` | `L` cuts out the **anchored** splitting group (LG4a's `hker` shape) | `ResidueLift.fixingSubgroup_splitField` |
| `hkerU` | `k` cuts out `U₀` through the anchor | `InfiniteGalois.fixingSubgroup_fixedField` |
| `hindex` | `[L : k] = 2` on the Galois side | `kerGal_subgroupOf_toGal_index_eq_two` |
| `hunram` | **the AX3/AX4-touching clause**: every nonzero `x ∈ L` has a norm-matching `y ∈ k` | `UnramifiedBridge.hunram_involution` (B13 + `R`/`horient`) |
| `hancinj` | the anchor is injective (`anc = U.subtype` in the campaign) | vacuous at `anc = id` |

Because `hunram` is a binder, this file's `#print axioms` is **strictly smaller** than the `ℚ₂`
model's: `hvanish_involution_ker_K` prints the model's set minus B13 and minus the reciprocity
leaves — `{B9, B11a}` from `lemma_6_16`'s Evens/Kummer spine, inherited through
`GQ2.ShapiroDeepness.hvanish_involution`.

## Dedup note on `eq_of_H1ofFun_eq`

Three copies of trivial-coefficient rigidity now exist, all with distinct names and none deleted:

* `GQ2.InvolutionSplice.eq_of_H1ofFun_eq` — the `ℚ₂` original, already abstract-`G`, takes the
  triviality of the action as the hypothesis `htriv`;
* `GQ2.Dyadic.eq_of_H1ofFun_eq_dp` (`LocalGauss/DeepPackage.lean` §5B) — LG4a's local copy, made
  because `DeepPackage` does not import `InvolutionSplice`; it *proves* triviality from LG2's
  `smul_zmodTwo` instead of assuming it;
* `GQ2.Dyadic.eq_of_H1ofFun_eq_K` below — the permanent `GQ2.Dyadic` home, defined as the `ℚ₂`
  original specialised through `smul_zmodTwo`.  It is definitionally interchangeable with LG4a's
  `_dp` copy; LG5 may collapse the `_dp` copy onto it once the import graph allows.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh GQ2.SectionSix GQ2.LocalKummer GQ2.ShapiroDeepness

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The `AlgEquiv`-flavoured spelling of `G_ℚ₂` (LG4a's anchoring convention). -/
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

/-! ## §1 Trivial-coefficient rigidity at a general source -/

section Rigidity

variable {Θ : Type} [Group Θ] [TopologicalSpace Θ] [IsTopologicalGroup Θ]
  [DistribMulAction Θ (ZMod 2)] [ContinuousSMul Θ (ZMod 2)]

/-- **Trivial-coefficient rigidity** (`B¹(Θ, 𝔽₂) = 0`): two continuous 1-cocycles with the same
`H1ofFun` class are equal.  This is `GQ2.InvolutionSplice.eq_of_H1ofFun_eq` (already abstract-`G`)
with its `htriv` hypothesis discharged by LG2's `smul_zmodTwo`; see the module docstring for the
three-way dedup with LG4a's `eq_of_H1ofFun_eq_dp`. -/
theorem eq_of_H1ofFun_eq_K {φ ψ : Θ → ZMod 2} (hφ : φ ∈ Z1 Θ (ZMod 2))
    (hψ : ψ ∈ Z1 Θ (ZMod 2)) (h : H1ofFun Θ φ = H1ofFun Θ ψ) : φ = ψ :=
  InvolutionSplice.eq_of_H1ofFun_eq (fun g m => smul_zmodTwo g m) hφ hψ h

end Rigidity

/-! ## §2 The anchored Galois dictionary

The one bridge between LG4a's `ancSubgroup`-shaped hypotheses and the `Γ`-side membership tests
the splice needs.  An **injective** anchor (in the campaign `anc = U.subtype`) turns
`hker : ∀ x : G_ℚ₂, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup` into the pointwise
`Γ`-statement `x ∈ ker ρ ↔ anc x ∈ k.fixingSubgroup`, which is what the carrier bridge
`↥U₀ →* ↥k.fixingSubgroup` is built from. -/

section Dictionary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)

/-- **The anchored Galois dictionary at the splitting group**: under an injective anchor, LG4a's
`hker` reads pointwise on `Γ`. -/
theorem mem_ker_iff_anc_mem (hancinj : Function.Injective ⇑anc)
    {k : IntermediateField ℚ_[2] ℚ̄₂}
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup) (x : Γ) :
    x ∈ (ρ.toMonoidHom.ker : Subgroup Γ) ↔ anc x ∈ k.fixingSubgroup := by
  rw [← hker]
  constructor
  · exact fun hx => ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨n, hn⟩
    exact hancinj (show anc (n : Γ) = anc x from hn) ▸ n.2

end Dictionary

/-! ## §3 The capstone: the involution `hvanish` in `ker ρ`-vocabulary -/

section Capstone

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C]
variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)

/-- **The involution `hvanish` over `ker ρ`, at a general local source** — the retype of
`GQ2.InvolutionSplice.hvanish_involution_ker`.

For a deep block coordinate `α` on `N = ker ρ ≤ Γ` and an involution lift `ĝ ∈ Γ` (`ĝ ∉ N`,
`ĝ² ∈ N`, `U₀ = N ⊔ ⟨ĝ⟩`), the Evens-norm inner cochain of the reducer's involution orbit has
trivial `H²ofFun` class.  This is the reducer's `hvanish` input at the involution orbits, with the
inner cochain matching `hcoh_involution_K`'s output verbatim.

The splitting tower `(k, L)`, the Galois index-2 clause and the analytic `hunram` are **threaded**
(module docstring): the `ℚ₂` proof's `ResidueLift`/`UnramifiedBridge` construction of them is the
AX3/AX4 field-side interface, which the dyadic campaign must not internalise as an axiom.  The
proof then runs exactly as the model: `B¹ = 0` extraction (the deep witness's Kummer cocycle
*equals* `α` on the nose), the c2a Kummer package `kummer_presentation_of_index_two`, the c2b
spine `hvanish_involution` (= Lemma 6.16), and the carrier splice pulling the `B²`-witness back
along the anchor `↥U₀ →* ↥k.fixingSubgroup`. -/
theorem hvanish_involution_ker_K
    (hancinj : Function.Injective ⇑anc)
    (k L : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] k] [FiniteDimensional ℚ_[2] L] (hkL : k ≤ L)
    (hkerL : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ L.fixingSubgroup)
    (hindex : ((L.fixingSubgroup).subgroupOf k.fixingSubgroup).index = 2)
    (hunram : ∀ x : ℚ̄₂, x ≠ 0 → x ∈ L → ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖)
    (α : ↥(ρ.toMonoidHom.ker : Subgroup Γ) → ZMod 2)
    (hαZ1 : α ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
    (hdeep : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) α ∈ deepClassesAt (kerAnc anc ρ))
    (ĝ : Γ) (hĝN : ĝ ∉ (ρ.toMonoidHom.ker : Subgroup Γ))
    (hĝ2 : ĝ * ĝ ∈ (ρ.toMonoidHom.ker : Subgroup Γ))
    (U₀ : Subgroup Γ)
    (hU₀ : U₀ = (ρ.toMonoidHom.ker : Subgroup Γ) ⊔ Subgroup.zpowers ĝ)
    (hmem : ĝ ∈ U₀)
    (hkerU : ∀ x : Γ, x ∈ U₀ ↔ anc x ∈ k.fixingSubgroup) :
    H2ofFun ↥U₀ (evensNormFun
      ((ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀) ⟨ĝ, hmem⟩
      (fun w => α ⟨w.1.1, w.2⟩)) = 0 := by
  classical
  -- ### the deep witness, extracted on the nose (`B¹ = 0`)
  obtain ⟨A, β, hdeepN, hβ, hβ0, heqN⟩ := hdeep
  have hZ1kcf : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) =>
      Kummer.kummerCocycleFun β (anc (n : Γ)))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) :=
    kummerAnc_mem_Z1 (kerAnc anc ρ) hβ hβ0 hdeepN.2.1
  have hfeq : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) =>
      Kummer.kummerCocycleFun β (anc (n : Γ))) = α :=
    eq_of_H1ofFun_eq_K hZ1kcf hαZ1 heqN
  -- ### the `Γ`-side dictionary and the deep unit over `L`
  have hkerN : ∀ x : Γ, x ∈ (ρ.toMonoidHom.ker : Subgroup Γ) ↔ anc x ∈ L.fixingSubgroup :=
    mem_ker_iff_anc_mem anc ρ hancinj hkerL
  have hAfixL : ∀ g ∈ L.fixingSubgroup, g • A = A := fun g hg => hdeepN.2.1 g ((hkerL g).mpr hg)
  have hdeepL : SectionSix.IsDeepUnit L.fixingSubgroup A :=
    isDeepUnit_of_le' (fun g hg => (hkerL g).mpr hg) hdeepN
  -- ### index 2, both views
  have hsUnot : (⟨ĝ, hmem⟩ : ↥U₀)
      ∉ (ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀ :=
    fun h => hĝN (Subgroup.mem_subgroupOf.mp h)
  have hUiU : ((ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀).index = 2 :=
    InvolutionSplice.subgroupOf_index_eq_two_of_sup hĝ2 hU₀ hmem hsUnot
  -- ### the carrier bridge `↥U₀ →* ↥k.fixingSubgroup` (the anchor)
  have hkm : ∀ x : ↥U₀, anc (x : Γ) ∈ k.fixingSubgroup := fun x => (hkerU x.1).mp x.2
  let e₀ : ↥U₀ →* ↥k.fixingSubgroup :=
    { toFun := fun x => ⟨anc (x : Γ), hkm x⟩
      map_one' := Subtype.ext (map_one anc)
      map_mul' := fun _ _ => Subtype.ext (map_mul anc _ _) }
  have he₀c : Continuous e₀ :=
    Continuous.subtype_mk (anc.continuous_toFun.comp continuous_subtype_val) _
  have hmemiff : ∀ x : ↥U₀,
      x ∈ (ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀
        ↔ e₀ x ∈ (L.fixingSubgroup).subgroupOf k.fixingSubgroup := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hkerN x.1
  have hsKnot : e₀ ⟨ĝ, hmem⟩ ∉ (L.fixingSubgroup).subgroupOf k.fixingSubgroup :=
    fun h => hsUnot ((hmemiff ⟨ĝ, hmem⟩).mpr h)
  -- ### trivial coefficients on both sides (the LG2 `smul` trap: only the `k`-side is `rfl`)
  have htrivK : ∀ (g : ↥k.fixingSubgroup) (m : ZMod 2), g • m = m := fun _ _ => rfl
  have htrivU : ∀ (g : ↥U₀) (m : ZMod 2), g • m = m := fun g m => smul_zmodTwo g m
  -- ### openness of the two index-2 pairs
  have hUoK : IsOpen ((((L.fixingSubgroup).subgroupOf k.fixingSubgroup)
      : Subgroup ↥k.fixingSubgroup) : Set ↥k.fixingSubgroup) := by
    have hLopen : IsOpen ((L.fixingSubgroup : Subgroup GalQ2) : Set GalQ2) :=
      (InfiniteGalois.isOpen_iff_finite L).mpr inferInstance
    exact hLopen.preimage continuous_subtype_val
  have hNopen : IsOpen ((ρ.toMonoidHom.ker : Subgroup Γ) : Set Γ) := isOpen_ker ρ
  have hUoU : IsOpen ((((ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀)
      : Subgroup ↥U₀) : Set ↥U₀) := hNopen.preimage continuous_subtype_val
  -- ### the c2a Kummer package
  obtain ⟨d, δ, u, v, hδ, hδL, hLδ, hAuv⟩ :=
    kummer_presentation_of_index_two k L hkL hindex A hdeepL
  -- ### the `k`-side Kummer cocycle is a `Z¹` (additivity + continuity)
  have hα : ∀ w z : ↥((L.fixingSubgroup).subgroupOf k.fixingSubgroup),
      Kummer.kummerCocycleFun β ((w * z : ↥k.fixingSubgroup) : GalQ2)
        = Kummer.kummerCocycleFun β ((w : ↥k.fixingSubgroup) : GalQ2)
          + Kummer.kummerCocycleFun β ((z : ↥k.fixingSubgroup) : GalQ2) := by
    intro w z
    exact kcf_hom_of_fixed hβ hβ0 (hAfixL _ (Subgroup.mem_subgroupOf.mp w.2))
      (hAfixL _ (Subgroup.mem_subgroupOf.mp z.2))
  have hαc : Continuous fun w : ↥((L.fixingSubgroup).subgroupOf k.fixingSubgroup) =>
      Kummer.kummerCocycleFun β ((w : ↥k.fixingSubgroup) : GalQ2) :=
    (Kummer.kummerCocycleFun_continuous β).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  -- ### the field-side vanishing (the c2b spine = Lemma 6.16)
  have hvan := hvanish_involution k L hkL hindex hunram d δ hδ hδL hLδ A β hdeepL hβ hβ0
    u v hAuv (e₀ ⟨ĝ, hmem⟩) hsKnot htrivK hUoK hα hαc
  -- ### the `U₀`-side inner cochain is the anchored Kummer cocycle on the nose
  have hinner : (fun w : ↥((ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀) =>
      α ⟨w.1.1, w.2⟩)
      = fun w : ↥((ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀) =>
        Kummer.kummerCocycleFun β (anc (w.1.1 : Γ)) := by
    funext w
    rw [← hfeq]
  rw [hinner]
  -- ### `Z²`-memberships on both sides
  have hαU : ∀ w z : ↥((ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀),
      Kummer.kummerCocycleFun β (anc ((w * z).1.1 : Γ))
        = Kummer.kummerCocycleFun β (anc (w.1.1 : Γ))
          + Kummer.kummerCocycleFun β (anc (z.1.1 : Γ)) := by
    intro w z
    have hAanc : ∀ y : ↥((ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀),
        anc (y.1.1 : Γ) • A = A := by
      intro y
      exact hdeepN.2.1 _ (mem_ancSubgroup (kerAnc anc ρ)
        ⟨(y.1.1 : Γ), Subgroup.mem_subgroupOf.mp y.2⟩)
    rw [show ((w * z).1.1 : Γ) = (w.1.1 : Γ) * (z.1.1 : Γ) from rfl, map_mul]
    exact kcf_hom_of_fixed hβ hβ0 (hAanc w) (hAanc z)
  have hαcU : Continuous fun w : ↥((ρ.toMonoidHom.ker : Subgroup Γ).subgroupOf U₀) =>
      Kummer.kummerCocycleFun β (anc (w.1.1 : Γ)) :=
    (Kummer.kummerCocycleFun_continuous β).comp
      (anc.continuous_toFun.comp (continuous_subtype_val.comp continuous_subtype_val))
  have hZ2U := evensNormFun_mem_Z2 htrivU hUoU hUiU hsUnot _ hαU hαcU
  have hZ2K := evensNormFun_mem_Z2 htrivK hUoK hindex hsKnot _ hα hαc
  -- ### transport the vanishing along the anchor bridge `e₀`
  exact InvolutionSplice.H2ofFun_eq_zero_comp e₀ he₀c htrivU htrivK
    (InvolutionSplice.evensNormFun_comp e₀ hmemiff rfl hUiU hsUnot hindex hsKnot _ _
      (fun x hx => rfl))
    hZ2U hZ2K hvan

end Capstone

end GQ2.Dyadic
