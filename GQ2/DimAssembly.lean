/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.AdmissibleCount
import GQ2.DeepDuality
import GQ2.RegularSummand
import GQ2.Prop32
import GQ2.Shapiro.Extend

/-!
# The parametric `lemma_6_17_dim` assembly

The capstone `card_deepPart_sq_of_duality` (`GQ2/AdmissibleCount.lean`) proves
`#X₊² = #H¹(ℚ₂,V)` — `lemma_6_17_dim`'s exact conclusion — from: `hρsurj`, `hinf`, `hext`,
a regular-summand package `(ι, r)` for the **dual** module `V^∨ = V →+ 𝔽₂`, and the graded
duality `hduality`.  This file exposes two parametric assembly theorems: one taking both `hext`
and `hduality`, and one deriving `hext` internally and taking only `hduality`.

* **profinite plumbing** — `rho_surjective` (`ρ = c ∘ tameF` is onto), `gen_of_surjective`
  (the images of `σ, τ` generate the finite discrete image, via `SectionThree.gen_ttame_quotient`),
  `tame_rel_image` (the tame relation `σ⁻¹τσ = τ²` pushed through `c`, from `tame_relation`);
* **`hinf`** — discharged via the banked `inflationVanishes_ramifiedTame`;
* **the `V^∨` package** — `lemma_6_11_of_tame_pair` applied at `dualModule`,
  with the 𝔽₂-dual transport bricks `dual_faithful` / `dual_simple` / `dual_ram` proving that
  `V^∨` inherits faithfulness, simplicity, and inertia-nontriviality from `V` (separation of
  points by functionals, `exists_functional_ne_zero`; annihilator + double-dual counting via
  `card_addHom_zmod2` for simplicity).

The second theorem derives `FamiliesExtend` from the `V`-side regular-module package using inverse
Shapiro and retract transfer.  The concrete arithmetic producer for `hduality` lives in
`GQ2/DeepCount.lean`.

The declarations here use only the standard axioms; B6/B7 enter through the supplied downstream
lemmas at instantiation.
-/

namespace GQ2

namespace DimAssembly

open ContCoh LocalKummer

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-! ## Profinite plumbing -/
omit [DiscreteTopology C] [Finite C] in
/-- `ρ = c ∘ tameF` is surjective when `c` is (`tameF` is onto, `B.tameF_surjective`). -/
theorem rho_surjective (B : BoundaryMaps) (c : ContinuousMonoidHom Ttame C)
    (hc : Function.Surjective ⇑c) (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hfac : ∀ g, ρ g = c (B.tameF g)) : Function.Surjective ⇑ρ := by
  intro y
  obtain ⟨t, ht⟩ := hc y
  obtain ⟨g, hg⟩ := B.tameF_surjective t
  exact ⟨g, by rw [hfac, hg, ht]⟩

omit [Finite C] in
/-- The images of `σ, τ` generate any finite discrete continuous image of `T_tame`
(`gen_ttame_quotient`; the discrete group is topological for free). -/
theorem gen_of_surjective (c : ContinuousMonoidHom Ttame C)
    (hc : Function.Surjective ⇑c) :
    Subgroup.closure {c tameSigma, c tameTau} = ⊤ := by
  haveI : IsTopologicalGroup C :=
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }
  exact SectionThree.gen_ttame_quotient c.toMonoidHom c.continuous_toFun hc

omit [DiscreteTopology C] [Finite C] in
/-- The tame relation `σ⁻¹τσ = τ²` in the image (`tame_relation` pushed through `c`). -/
theorem tame_rel_image (c : ContinuousMonoidHom Ttame C) :
    (c tameSigma)⁻¹ * c tameTau * c tameSigma = c tameTau ^ 2 := by
  simpa only [conjP, map_mul, map_inv, map_pow] using congrArg (⇑c) tame_relation

/-! ## 𝔽₂-dual transport: `V^∨` inherits the ramified-simple-faithful package from `V`

Stated in **pointwise** form (no `SMul (V →+ 𝔽₂)` instance mentioned), so they can be consumed
under any `letI := dualModule` without instance-diamond friction (the deep-part proof handoff idiom). -/

section Dual

variable {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]

omit [Finite V] in
/-- Functionals separate points (via `exists_functional_ne_zero`). -/
theorem eq_of_forall_functional_eq (hV2 : ∀ v : V, v + v = 0) {a b : V}
    (h : ∀ φ : V →+ ZMod 2, φ a = φ b) : a = b := by
  by_contra hne
  obtain ⟨φ, hφ⟩ := exists_functional_ne_zero hV2 (sub_ne_zero.mpr hne)
  exact hφ (by rw [map_sub, h φ, sub_self])

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [Finite V] in
/-- Dual faithfulness: if `h` fixes every functional (pointwise form
`φ (h⁻¹ • v) = φ v`), it is the identity. -/
theorem dual_faithful (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1) (h : C)
    (hh : ∀ (φ : V →+ ZMod 2) (v : V), φ (h⁻¹ • v) = φ v) : h = 1 := by
  have hinv : h⁻¹ = 1 := hfaith h⁻¹ fun v =>
    eq_of_forall_functional_eq hV2 fun φ => hh φ v
  rw [← inv_inv h, hinv, inv_one]

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [Finite V] in
/-- Dual inertia-nontriviality: if `t` moves a vector, it moves a functional
(pointwise form). -/
theorem dual_ram (hV2 : ∀ v : V, v + v = 0) {t : C} (hram : ∃ v : V, t • v ≠ v) :
    ∃ (φ : V →+ ZMod 2) (v : V), φ (t⁻¹ • v) ≠ φ v := by
  by_contra hall
  obtain ⟨v, hv⟩ := hram
  have htriv : ∀ w : V, t⁻¹ • w = w := fun w =>
    eq_of_forall_functional_eq hV2 fun φ => by
      by_contra hne
      exact hall ⟨φ, w, hne⟩
  have h1 : t⁻¹ • (t • v) = t • v := htriv (t • v)
  rw [inv_smul_smul] at h1
  exact hv h1.symm

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] in
/-- Dual simplicity: a `C`-stable subgroup of `V^∨` (stability in composition form) is
`⊥` or `⊤`.  Route: the annihilator in `V` is `C`-stable, hence `⊥` by simplicity of `V`
(it cannot be `⊤` unless `W = ⊥`); then evaluation `V ↪ W^∨` is injective and the
`card_addHom_zmod2` count forces `#W = #V^∨`. -/
theorem dual_simple (hV2 : ∀ v : V, v + v = 0)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : AddSubgroup (V →+ ZMod 2))
    (hW : ∀ (h : C), ∀ φ ∈ W, φ.comp (DistribSMul.toAddMonoidHom V h⁻¹) ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  haveI : Finite (V →+ ZMod 2) := Finite.of_injective _ DFunLike.coe_injective
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  -- the annihilator of `W` in `V`
  let ann : AddSubgroup V :=
    { carrier := {v | ∀ φ ∈ W, φ v = 0}
      zero_mem' := fun φ _ => map_zero φ
      add_mem' := fun {a b} ha hb φ hφ => by
        rw [map_add, ha φ hφ, hb φ hφ, add_zero]
      neg_mem' := fun {a} ha φ hφ => by rw [map_neg, ha φ hφ, neg_zero] }
  have hann_stab : ∀ (h : C), ∀ v ∈ ann, h • v ∈ ann := by
    intro h v hv φ hφ
    have hmem : φ.comp (DistribSMul.toAddMonoidHom V h) ∈ W := by
      have h' := hW h⁻¹ φ hφ
      rwa [inv_inv] at h'
    exact hv _ hmem
  have hann_ne : ann ≠ ⊤ := by
    intro htop
    apply hbot
    refine (AddSubgroup.eq_bot_iff_forall _).mpr fun φ hφ => ?_
    ext v
    have hv : v ∈ ann := by rw [htop]; trivial
    simpa using hv φ hφ
  have hann_bot : ann = ⊥ := (hsimple ann hann_stab).resolve_right hann_ne
  -- evaluation `V ↪ (↥W →+ 𝔽₂)`
  let ev : V →+ (↥W →+ ZMod 2) :=
    { toFun := fun v =>
        { toFun := fun φ => (φ : V →+ ZMod 2) v
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      map_zero' := by ext φ; exact map_zero (φ : V →+ ZMod 2)
      map_add' := fun a b => by ext φ; exact map_add (φ : V →+ ZMod 2) a b }
  have hev_inj : Function.Injective ev := by
    intro a b hab
    have hmem : a - b ∈ ann := by
      intro φ hφ
      have h1 : (φ : V →+ ZMod 2) a = (φ : V →+ ZMod 2) b :=
        congrArg (fun F : ↥W →+ ZMod 2 => F ⟨φ, hφ⟩) hab
    -- note: `ev a ⟨φ, hφ⟩ = φ a` definitionally
      rw [map_sub, h1, sub_self]
    rw [hann_bot, AddSubgroup.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  -- counting: `#V ≤ #(W^∨) = #W ≤ #(V^∨) = #V`
  haveI : Finite ↥W := Subtype.finite
  haveI : Finite (↥W →+ ZMod 2) := Finite.of_injective _ DFunLike.coe_injective
  have hWtors : ∀ x : ↥W, x + x = 0 := fun x =>
    Subtype.ext (FoxH.ElemDual.add_self_eq_zero (x : V →+ ZMod 2))
  have h1 : Nat.card V ≤ Nat.card (↥W →+ ZMod 2) :=
    Nat.card_le_card_of_injective ev hev_inj
  have h2 : Nat.card (↥W →+ ZMod 2) = Nat.card ↥W :=
    QuadraticFp2.card_addHom_zmod2 ↥W hWtors
  have h3 : Nat.card (V →+ ZMod 2) = Nat.card V := QuadraticFp2.card_addHom_zmod2 V hV2
  have h4 : Nat.card ↥W ≤ Nat.card (V →+ ZMod 2) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have hcard : Nat.card ↥W = Nat.card (V →+ ZMod 2) := by omega
  exact AddSubgroup.eq_top_of_card_eq W hcard

end Dual

/-! ## The parametric close -/

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- **`lemma_6_17_dim`, parametric over `hext` and `hduality`** (the deep-part proof, increment 1):
from `lemma_6_17_dim`'s own hypothesis set, discharge `hρsurj`/`hgen`/`hinf` (profinite
plumbing + `inflationVanishes_ramifiedTame`) and the `V^∨` regular-summand package
(`lemma_6_11_of_tame_pair` at `dualModule`, via the 𝔽₂-dual transport bricks), and apply the
f6 capstone.  The parameters are `hext` (`FamiliesExtend`)
and `hduality` (the deep-part proof's result). -/
theorem lemma_6_17_dim_of_hext_hduality (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))]
    (hext : FamiliesExtend (V := V) ρ)
    (hduality :
      letI := conjModuleDeep ρ (rho_surjective B c hc ρ hfac)
      letI := conjModuleQuot ρ (rho_surjective B c hc ρ hfac)
      letI : DistribMulAction C (V →+ ZMod 2) := dualModule
      Nat.card ↥(equivHoms C (V →+ ZMod 2)
          ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)))
        = Nat.card ↥(equivHoms C (V →+ ZMod 2)
            (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
              deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)))) :
    Nat.card (SectionSix.deepPart (V := V) ρ) ^ 2 = Nat.card (H1 AbsGalQ2 V) := by
  classical
  have hρsurj : Function.Surjective ⇑ρ := rho_surjective B c hc ρ hfac
  have hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤ := gen_of_surjective c hc
  have hinf : InflationVanishes (V := V) ρ :=
    inflationVanishes_ramifiedTame ρ c hρ hV2 hρsurj hgen hsimple hram
  -- the `V^∨` regular-summand package
  haveI : Finite (V →+ ZMod 2) := Finite.of_injective _ DFunLike.coe_injective
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  have hV2D : ∀ φ : V →+ ZMod 2, φ + φ = 0 := fun φ => FoxH.ElemDual.add_self_eq_zero φ
  have hfaithD : ∀ h : C, (∀ φ : V →+ ZMod 2, h • φ = φ) → h = 1 := by
    intro h hh
    exact dual_faithful hV2 hfaith h fun φ v =>
      congrArg (fun ψ : V →+ ZMod 2 => ψ v) (hh φ)
  have hsimpleD : ∀ W : AddSubgroup (V →+ ZMod 2),
      (∀ (h : C), ∀ φ ∈ W, h • φ ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    dual_simple hV2 hsimple W fun h φ hφ => hW h φ hφ
  have hramD : ∃ φ : V →+ ZMod 2, c tameTau • φ ≠ φ := by
    obtain ⟨φ, v, hφv⟩ := dual_ram hV2 hram
    exact ⟨φ, fun heq => hφv (congrArg (fun ψ : V →+ ZMod 2 => ψ v) heq)⟩
  obtain ⟨Nreg, ι, r, hι, hr, hri⟩ :=
    lemma_6_11_of_tame_pair (V := V →+ ZMod 2) hgen (tame_rel_image c)
      hV2D hfaithD hsimpleD hramD
  exact card_deepPart_sq_of_duality ρ hρ hV2 hρsurj hinf hext ι r
    (fun h φ n x => hι h φ n x) (fun h F => hr h F) hri hduality

/-- **`lemma_6_17_dim`, parametric over `hduality` alone** (the deep-part proof, increment 2): the `hext`
parameter of `lemma_6_17_dim_of_hext_hduality` is now **discharged** — the `V`-side
regular-summand package (`lemma_6_11_of_tame_pair` at `V` itself, whose hypotheses are the
theorem's own) feeds `ShapiroExtend.familiesExtend_of_package` (inverse Shapiro at the regular
module + the retract transfer).  The final parameter is the deep-part duality hypothesis `hduality`. -/
theorem lemma_6_17_dim_of_hduality (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))]
    (hduality :
      letI := conjModuleDeep ρ (rho_surjective B c hc ρ hfac)
      letI := conjModuleQuot ρ (rho_surjective B c hc ρ hfac)
      letI : DistribMulAction C (V →+ ZMod 2) := dualModule
      Nat.card ↥(equivHoms C (V →+ ZMod 2)
          ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)))
        = Nat.card ↥(equivHoms C (V →+ ZMod 2)
            (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
              deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)))) :
    Nat.card (SectionSix.deepPart (V := V) ρ) ^ 2 = Nat.card (H1 AbsGalQ2 V) := by
  have hρsurj : Function.Surjective ⇑ρ := rho_surjective B c hc ρ hfac
  have hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤ := gen_of_surjective c hc
  -- the `V`-side regular-summand package discharges `hext`
  obtain ⟨NregV, ιV, rV, hιV, hrV, hriV⟩ :=
    lemma_6_11_of_tame_pair (V := V) hgen (tame_rel_image c) hV2 hfaith hsimple hram
  have hext : FamiliesExtend (V := V) ρ :=
    ShapiroExtend.familiesExtend_of_package hρ hρsurj ιV rV hιV hrV hriV
  exact lemma_6_17_dim_of_hext_hduality B c hc ρ hfac hρ hV2 hfaith hsimple hram hext hduality

end DimAssembly

end GQ2
