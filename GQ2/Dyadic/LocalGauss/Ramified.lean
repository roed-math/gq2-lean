/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.LocalGauss.DeepPackage
import GQ2.Dyadic.LocalGauss.Unramified
import GQ2.DeepCount
import GQ2.DetRamified

/-!
# The ramified Gauss sign over a general local source (LG4b) — the dimension lane and assembly

The second half of LG4.  LG4a (`GQ2/Dyadic/LocalGauss/DeepPackage.lean`) owns the deep-unit
package and the vanishing lane; this file owns

* the **dimension lane** `lemma_6_17_dim_final_K` (`#X₊² = #H¹`),
* the **join** `card_Q0loc_zero_eq_of_dim_of_vanish_K` (packet Prop. 6.12/6.14: the deep half is
  a Lagrangian, so the Gauss sign is `+`),
* the **endpoint** `prop_6_18_ramified_K` (packet Prop. 6.18 / eq. (115), ramified case, over a
  finite extension `K/ℚ₂`), and
* the **`n = 1` regression** against `GQ2.DetRamified.prop_6_18_ramified`.

Everything follows LG4a's **anchoring convention** (its §1): deep units are `AbsGalQ2`-side
objects reached through an anchor `anc : ContinuousMonoidHom Γ GalQ2`, at the anchored subgroup
`ancSubgroup (kerAnc anc ρ)`; deep *classes* live on the `Γ`-side splitting group `N_K = ker ρ`.
No cohomology transport, no `Subgroup ↥U`-vs-`Subgroup AbsGalQ2` cast.

## Contents

* §1 **`FamiliesExtendK` discharged** — the retype of `GQ2.ShapiroExtend.familiesExtend_of_package`
  (`GQ2/Shapiro/Extend.lean` :272): inverse Shapiro at the regular module `RegMod C Nr`, then the
  retract transfer along `mapCoeff1 r`.  Fed by PJ1's `lemma_6_11_of_tame_pair_pow`.
* §2 **the conjugation modules** on the deep subgroup and on the quotient
  (`conjModuleDeepK`/`conjModuleQuotK`) — `GQ2.conjModuleDeep`/`conjModuleQuot` retyped.
* §3 **the admissible-family ↔ equivariant-Hom bridges** (`GQ2/AdmissibleCount.lean` :250–:455
  retyped) and the SES count.
* §4 **the `hduality`-parametric dimension clause** `card_deepPartK_sq_of_duality` —
  `GQ2.card_deepPart_sq_of_duality` (:466) retyped.
* §5 **the middle twist (H5)** — `GQ2.conjAct_mid_sub_mem_deep` /
  `conjAct_surjInv_conj_mid_sub_mem_deep` (`GQ2/DeepDuality.lean` :1134/:1256) retyped at the
  anchor; residue-triviality is taken at `ancSubgroup (kerAnc anc ρ)`, so the `ℚ₂` predicate
  `GQ2.IsResidueTrivial` is consumed verbatim.
* §6 **the `N_K ↔ G_k` transport and the structural count** (H4 sharpness) —
  `GQ2/DeepCount/Transport.lean` retyped.  This is where the anchor must be **injective on the
  splitting group** (`hancinj`): the `ℚ₂` transport is an identity inclusion in both directions,
  and only the `→` direction is available from `hker` alone.  In the campaign `anc = U.subtype`,
  so `hancinj` is free.
* §7 **`hduality_of_data_K`** — `GQ2.hduality_of_data` (`GQ2/DeepCount/Finale.lean` :46) retyped.
* §8 **the dimension lane** `lemma_6_17_dim_final_K`.
* §9 **the join** `card_Q0loc_zero_eq_of_dim_of_vanish_K`.
* §10 **the endpoint** `prop_6_18_ramified_K`, packaged over F1's `FieldParameters` exactly as
  LG3's `prop_6_18_unramified_K`.
* §11 the `n = 1` regression.

## The `ResidueLift` decision (recorded for the orchestrator)

The `ℚ₂` dimension lane closes `lemma_6_17_dim` outright by *building* the splitting field
(`GQ2.ResidueLift.splitField`, `fixingSubgroup_splitField`) and *deriving* the residue-trivial
tame lift (`exists_residueTrivial_tameLift`).  Both derivations are `ℚ₂`-specific in shape but not
in content:

* the splitting field of a general `Γ` is **not** an `IntermediateField ℚ_[2] ℚ̄₂` unless `Γ` is
  already a subgroup of `G_ℚ₂` — at a general anchored source the correct object is the fixed
  field of `ancSubgroup (kerAnc anc ρ)`, which needs the anchor's range to be closed.  So the
  `(k, hker)` pair is **threaded**, exactly as LG4a threaded it in its §4/§6 (memo §2 row 3);
* the residue-trivial lift is likewise threaded as `(g₀, hg₀, hg₀rt)`.

Both are supplied by the caller at `Γ = ↥U` (LG5 / the AS lane) from the Galois correspondence
for the open subgroup `ancSubgroup (kerAnc U.subtype ρ) ≤ G_ℚ₂`, which is a `ℚ₂`-side statement
and therefore reuses `GQ2.ResidueLift` verbatim.  Nothing is lost and no axiom is added.

## Axiom hygiene

Every declaration here is parametrized over the duality bundle `D` and over the `k`-side data, so
the prints are the `ℚ₂` models' (std-3 + the B6/B7/B11a/B12/B13 §6.3 budget reached through the
imported `ℚ₂` leaves).  AX3/AX4 content appears **only** as explicit binders (`tameFK`, `htameFK`,
`hfac`), following LG3's three-binder pattern.  Census unchanged.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh GQ2.LocalKummer GQ2.QuadraticFp2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The `AlgEquiv`-flavoured spelling of `G_ℚ₂` (LG4a's convention: anchors are typed with this
spelling so instance search finds the `AlgEquiv`-action on `ℚ̄₂`). -/
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

/-! ## §1 `FamiliesExtendK`, discharged from the Lemma 6.11 package

`GQ2.ShapiroExtend.familiesExtend_of_package` (`GQ2/Shapiro/Extend.lean` :272) retyped: inverse
Shapiro at the regular module (the explicit coinduced-coefficient cocycle built out of the
family's evaluation seeds), then the retract transfer along `mapCoeff1 r`.  Together with LG4a's
§5A discharge of `InflationVanishesK` this closes packet Def. 6.11(a) at a general local source.

The **regular module** `GQ2.ShapiroExtend.RegMod C Nr` and its `ev`-span
(`evReg`, `addHom_eq_sum_evReg`) mention only `C`, so they are consumed **verbatim** — only the
section/word layer and the naturality lemma move from `G_ℚ₂` to `Γ`. -/

section FamiliesExtend

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

open scoped Classical in
/-- A set-theoretic section of `ρ`, normalized so that `sec1K ρ hρsurj 1 = 1` —
`GQ2.ShapiroExtend.sec1` retyped. -/
noncomputable def sec1K (ρ : ContinuousMonoidHom Γ C) (hρsurj : Function.Surjective ⇑ρ)
    (c : C) : Γ :=
  if c = 1 then 1 else Function.surjInv hρsurj c

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DiscreteTopology C] [Finite C] in
private theorem sec1K_spec (ρ : ContinuousMonoidHom Γ C) (hρsurj : Function.Surjective ⇑ρ)
    (c : C) : ρ (sec1K ρ hρsurj c) = c := by
  unfold sec1K
  split_ifs with h
  · rw [h, map_one]
  · exact Function.surjInv_eq hρsurj c

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DiscreteTopology C] [Finite C] in
private theorem sec1K_one (ρ : ContinuousMonoidHom Γ C) (hρsurj : Function.Surjective ⇑ρ) :
    sec1K ρ hρsurj 1 = 1 := if_pos rfl

variable (ρ : ContinuousMonoidHom Γ C) (hρsurj : Function.Surjective ⇑ρ)

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DiscreteTopology C] [Finite C] in
/-- The Shapiro word `s(x)⁻¹ · g · s(ρ(g)⁻¹x)` lies in `N_K = ker ρ`. -/
theorem shapiroWordK_mem (g : Γ) (x : C) :
    (sec1K ρ hρsurj x)⁻¹ * g * sec1K ρ hρsurj ((ρ g)⁻¹ * x)
      ∈ (ρ.toMonoidHom.ker : Subgroup Γ) := by
  show ρ ((sec1K ρ hρsurj x)⁻¹ * g * sec1K ρ hρsurj ((ρ g)⁻¹ * x)) = 1
  rw [map_mul, map_mul, map_inv, sec1K_spec, sec1K_spec]
  group

/-- The inverse-Shapiro word as an element of `↥N_K`: the `(g, x)`-entry of the coinduced-module
extension cocycle. -/
noncomputable def shapiroWordK (g : Γ) (x : C) : ↥(ρ.toMonoidHom.ker : Subgroup Γ) :=
  ⟨(sec1K ρ hρsurj x)⁻¹ * g * sec1K ρ hρsurj ((ρ g)⁻¹ * x), shapiroWordK_mem ρ hρsurj g x⟩

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DiscreteTopology C] [Finite C] in
/-- Middle-insertion factorization — the source of the cocycle identity for the extension. -/
theorem shapiroWordK_mul (g h : Γ) (x : C) :
    shapiroWordK ρ hρsurj (g * h) x
      = shapiroWordK ρ hρsurj g x * shapiroWordK ρ hρsurj h ((ρ g)⁻¹ * x) := by
  apply Subtype.ext
  show (sec1K ρ hρsurj x)⁻¹ * (g * h) * sec1K ρ hρsurj ((ρ (g * h))⁻¹ * x)
    = ((sec1K ρ hρsurj x)⁻¹ * g * sec1K ρ hρsurj ((ρ g)⁻¹ * x))
      * ((sec1K ρ hρsurj ((ρ g)⁻¹ * x))⁻¹ * h * sec1K ρ hρsurj ((ρ h)⁻¹ * ((ρ g)⁻¹ * x)))
  have harg : (ρ (g * h))⁻¹ * x = (ρ h)⁻¹ * ((ρ g)⁻¹ * x) := by
    rw [map_mul, mul_inv_rev, mul_assoc]
  rw [harg]
  group

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DiscreteTopology C] [Finite C] in
/-- On the kernel, at the base point `x = 1`, the word is the element itself. -/
theorem shapiroWordK_ker_one (n₀ : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    shapiroWordK ρ hρsurj (n₀ : Γ) 1 = n₀ := by
  apply Subtype.ext
  show (sec1K ρ hρsurj 1)⁻¹ * (n₀ : Γ) * sec1K ρ hρsurj ((ρ n₀)⁻¹ * 1) = (n₀ : Γ)
  have h1 : ρ (n₀ : Γ) = 1 := n₀.2
  rw [h1, inv_one, one_mul, sec1K_one, inv_one, one_mul, mul_one]

omit [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] [Finite C] in
/-- Continuity of the word in `g` (the `C`-inputs are discrete, so the section legs are free). -/
theorem continuous_shapiroWordK (x : C) :
    Continuous fun g : Γ => shapiroWordK ρ hρsurj g x := by
  apply Continuous.subtype_mk
  have hsec : Continuous fun g : Γ => sec1K ρ hρsurj ((ρ g)⁻¹ * x) :=
    show Continuous ((fun c : C => sec1K ρ hρsurj (c⁻¹ * x)) ∘ ⇑ρ) from
      continuous_of_discreteTopology.comp ρ.continuous_toFun
  exact (continuous_const.mul continuous_id).mul hsec

variable {ρ}

omit [DiscreteTopology C] [Finite C] in
/-- **`phiResK` is natural in the coefficient module** — `GQ2.ShapiroExtend.phiRes_mapCoeff1`
retyped: restricting a pushed-forward class is pre-composing the functional. -/
theorem phiResK_mapCoeff1 {W₁ W₂ : Type}
    [AddCommGroup W₁] [TopologicalSpace W₁] [DiscreteTopology W₁] [IsTopologicalAddGroup W₁]
    [DistribMulAction Γ W₁] [ContinuousSMul Γ W₁] [DistribMulAction C W₁]
    [AddCommGroup W₂] [TopologicalSpace W₂] [DiscreteTopology W₂] [IsTopologicalAddGroup W₂]
    [DistribMulAction Γ W₂] [ContinuousSMul Γ W₂] [DistribMulAction C W₂]
    (hρ₁ : ∀ (g : Γ) (w : W₁), g • w = ρ g • w) (hρ₂ : ∀ (g : Γ) (w : W₂), g • w = ρ g • w)
    (f : W₁ →+ W₂) (hf : Continuous f) (hcompat : ∀ (g : Γ) (w : W₁), f (g • w) = g • f w)
    (x : H1 Γ W₁) (φ : W₂ →+ ZMod 2) :
    phiResK ρ (mapCoeff1 f hf hcompat x) φ = phiResK ρ x (φ.comp f) := by
  have hb : H1mk Γ W₁ (Quotient.out x) = x := Quotient.out_eq x
  have hmap : H1mk Γ W₂
      (Z1comap (ContinuousMonoidHom.id Γ) f hf (fun g n => hcompat g n) (Quotient.out x))
      = mapCoeff1 f hf hcompat x := by
    conv_rhs => rw [← hb]
    exact (mapCoeff1_H1mk f hf hcompat (Quotient.out x)).symm
  have h1 := phiResK_of_rep ρ hρ₂ hmap φ
  have h2 := phiResK_of_rep ρ hρ₁ hb (φ.comp f)
  rw [← h1, ← h2]
  rfl

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

/-- **`FamiliesExtendK` from the Lemma 6.11 package** — `GQ2.ShapiroExtend.familiesExtend_of_package`
retyped to a general local source.  Given the equivariant split-summand package `(ι, r)`
embedding `V` into the regular module `𝔽₂[C]^{Nr}` (PJ1's `lemma_6_11_of_tame_pair_pow` output
shape), every admissible family extends to a class of `H¹(Γ, V)`.

The statement is `V`-side only; the regular module and its actions live inside the proof. -/
theorem familiesExtendK_of_package
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (hρsurj : Function.Surjective ⇑ρ) {Nr : ℕ}
    (ι : V →+ (Fin Nr → C → ZMod 2)) (r : (Fin Nr → C → ZMod 2) →+ V)
    (hι : ∀ (h : C) (v : V) (n : Fin Nr) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin Nr → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : V, r (ι v) = v) :
    FamiliesExtendK (V := V) ρ := by
  classical
  intro ξ
  -- move the package to the instance-opaque carrier
  let ι' : V →+ ShapiroExtend.RegMod C Nr := ι
  let r' : ShapiroExtend.RegMod C Nr →+ V := r
  -- the `Γ`-action through `ρ` (the `C`-action is the global left-translation instance)
  letI instGR : DistribMulAction Γ (ShapiroExtend.RegMod C Nr) :=
    DistribMulAction.compHom _ ρ.toMonoidHom
  haveI : ContinuousSMul Γ (ShapiroExtend.RegMod C Nr) := by
    refine ⟨?_⟩
    have hfac : (fun p : Γ × ShapiroExtend.RegMod C Nr => p.1 • p.2)
        = (fun q : C × ShapiroExtend.RegMod C Nr => q.1 • q.2)
          ∘ (fun p : Γ × ShapiroExtend.RegMod C Nr => (ρ p.1, p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  haveI : IsTopologicalAddGroup V :=
    { continuous_add := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  have hρR : ∀ (g : Γ) (F : ShapiroExtend.RegMod C Nr), g • F = ρ g • F := fun _ _ => rfl
  -- the family pushed to the regular module
  set Ξ : (ShapiroExtend.RegMod C Nr →+ ZMod 2)
      → H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) :=
    fun ψ => ξ.fam (ψ.comp ι') with hΞdef
  -- `ι` is `Γ`-equivariant (through `ρ`, via the package's translation form)
  have hιG : ∀ (g : Γ) (v : V), ι' (g • v) = g • ι' v := by
    intro g v
    show ι (g • v) = (fun n x => ι v n ((ρ g)⁻¹ * x) : ShapiroExtend.RegMod C Nr)
    funext n x
    rw [hρ g v, hι (ρ g) v n x]
  -- `Ξ` is additive and conjugation-equivariant
  have hΞadd : ∀ ψ ψ', Ξ (ψ + ψ') = Ξ ψ + Ξ ψ' := by
    intro ψ ψ'
    show ξ.fam ((ψ + ψ').comp ι') = ξ.fam (ψ.comp ι') + ξ.fam (ψ'.comp ι')
    rw [AddMonoidHom.add_comp, ξ.add']
  have hΞequiv : ∀ (g : Γ) (ψ : ShapiroExtend.RegMod C Nr →+ ZMod 2),
      conjAct ρ g (Ξ ψ)
        = Ξ (ψ.comp (DistribSMul.toAddMonoidHom (ShapiroExtend.RegMod C Nr) g⁻¹)) := by
    intro g ψ
    show conjAct ρ g (ξ.fam (ψ.comp ι'))
      = ξ.fam ((ψ.comp (DistribSMul.toAddMonoidHom (ShapiroExtend.RegMod C Nr) g⁻¹)).comp ι')
    rw [ξ.equiv' g]
    congr 1
    ext v
    show ψ (ι' (g⁻¹ • v)) = ψ (g⁻¹ • ι' v)
    rw [hιG g⁻¹ v]
  -- the evaluation seeds and the Shapiro cocycle
  set u : Fin Nr → ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :=
    fun n => Quotient.out (Ξ (ShapiroExtend.evReg Nr n 1)) with hudef
  have hu_mk : ∀ n, H1mk ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) (u n)
      = Ξ (ShapiroExtend.evReg Nr n 1) := fun n => Quotient.out_eq _
  have hu_hom : ∀ (n : Fin Nr) (a b : ↥(ρ.toMonoidHom.ker : Subgroup Γ)),
      (u n).1 (a * b) = (u n).1 a + (u n).1 b := by
    intro n a b
    obtain ⟨-, hcoc⟩ := mem_Z1_iff.mp (u n).2
    rw [hcoc a b, smul_zmodTwo]
  set b : Γ → ShapiroExtend.RegMod C Nr :=
    fun g => fun n x => (u n).1 (shapiroWordK ρ hρsurj g x) with hbdef
  have hbZ1 : b ∈ Z1 Γ (ShapiroExtend.RegMod C Nr) := by
    refine mem_Z1_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun g : Γ => (fun n x => (u n).1 (shapiroWordK ρ hρsurj g x)
        : Fin Nr → C → ZMod 2)
      refine continuous_pi fun n => continuous_pi fun x => ?_
      exact (mem_Z1_iff.mp (u n).2).1.comp (continuous_shapiroWordK ρ hρsurj x)
    · intro g h
      funext n x
      show (u n).1 (shapiroWordK ρ hρsurj (g * h) x)
        = (u n).1 (shapiroWordK ρ hρsurj g x) + (u n).1 (shapiroWordK ρ hρsurj h ((ρ g)⁻¹ * x))
      rw [shapiroWordK_mul ρ hρsurj g h x, hu_hom]
  set xR : H1 Γ (ShapiroExtend.RegMod C Nr) :=
    H1mk Γ (ShapiroExtend.RegMod C Nr) ⟨b, hbZ1⟩ with hxRdef
  -- seed agreement at `ev (n, 1)`
  have hev1 : ∀ n : Fin Nr,
      phiResK ρ xR (ShapiroExtend.evReg Nr n 1) = Ξ (ShapiroExtend.evReg Nr n 1) := by
    intro n
    have hrep := phiResK_of_rep ρ (V := ShapiroExtend.RegMod C Nr) hρR
      (b := ⟨b, hbZ1⟩) (x := xR) hxRdef.symm (ShapiroExtend.evReg Nr n 1)
    rw [← hrep, ← hu_mk n]
    have hfun : (fun n₀ : ↥(ρ.toMonoidHom.ker : Subgroup Γ) =>
        ShapiroExtend.evReg Nr n 1
          ((⟨b, hbZ1⟩ : ↥(Z1 Γ (ShapiroExtend.RegMod C Nr))).1 (n₀ : Γ)))
        = (u n).1 := by
      funext n₀
      show (u n).1 (shapiroWordK ρ hρsurj (n₀ : Γ) 1) = (u n).1 n₀
      rw [shapiroWordK_ker_one ρ hρsurj n₀]
    rw [hfun, H1ofFun_of_mem (u n).2]
  -- the conjugation bootstrap: agreement at every `ev (n, c)`
  have hev : ∀ (n : Fin Nr) (c : C),
      phiResK ρ xR (ShapiroExtend.evReg Nr n c) = Ξ (ShapiroExtend.evReg Nr n c) := by
    intro n c
    have hgc : ρ (Function.surjInv hρsurj c) = c := Function.surjInv_eq hρsurj c
    set g : Γ := Function.surjInv hρsurj c
    have hcomp : (ShapiroExtend.evReg Nr n 1).comp
        (DistribSMul.toAddMonoidHom (ShapiroExtend.RegMod C Nr) g⁻¹)
        = ShapiroExtend.evReg Nr n c := by
      ext F
      show (g⁻¹ • F) n 1 = F n c
      show F n ((ρ g⁻¹)⁻¹ * 1) = F n c
      rw [map_inv, inv_inv, mul_one, hgc]
    have h1 := phiResK_conj ρ (V := ShapiroExtend.RegMod C Nr) hρR xR
      (ShapiroExtend.evReg Nr n 1) g
    have h2 := hΞequiv g (ShapiroExtend.evReg Nr n 1)
    rw [hcomp] at h1 h2
    rw [← h1, ← h2, hev1 n]
  -- span upgrade: agreement on every functional of the regular module
  have hall : ∀ ψ : ShapiroExtend.RegMod C Nr →+ ZMod 2, phiResK ρ xR ψ = Ξ ψ := by
    have hsum : ∀ (T : (ShapiroExtend.RegMod C Nr →+ ZMod 2)
          → H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)),
        T 0 = 0 → (∀ ψ₁ ψ₂, T (ψ₁ + ψ₂) = T ψ₁ + T ψ₂) →
        ∀ s : Finset (Fin Nr × C),
          T (∑ p ∈ s, ShapiroExtend.evReg Nr p.1 p.2)
            = ∑ p ∈ s, T (ShapiroExtend.evReg Nr p.1 p.2) := by
      intro T h0 hadd s
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.sum_empty, h0]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
    have hz0 : Ξ 0 = 0 := by
      have h2 : Ξ 0 + Ξ 0 = Ξ 0 + 0 := by rw [← hΞadd 0 0, add_zero, add_zero]
      exact add_left_cancel h2
    have hp0 : phiResK ρ xR 0 = 0 := by
      have h1 : phiResK ρ xR 0 + phiResK ρ xR 0 = phiResK ρ xR 0 + 0 := by
        rw [← phiResK_add_phi ρ (V := ShapiroExtend.RegMod C Nr) hρR xR 0 0, add_zero, add_zero]
      exact add_left_cancel h1
    intro ψ
    haveI : Fintype C := Fintype.ofFinite C
    rw [ShapiroExtend.addHom_eq_sum_evReg Nr ψ,
      hsum (phiResK ρ xR) hp0 (phiResK_add_phi ρ (V := ShapiroExtend.RegMod C Nr) hρR xR) _,
      hsum Ξ hz0 hΞadd _]
    exact Finset.sum_congr rfl fun p _ => hev p.1 p.2
  -- the retract transfer: pull the extending class back to `V`
  have hcompat_r : ∀ (g : Γ) (F : ShapiroExtend.RegMod C Nr), r' (g • F) = g • r' F := by
    intro g F
    show r (fun n x => F n ((ρ g)⁻¹ * x)) = g • r' F
    rw [hr (ρ g) F, ← hρ g (r F)]
    rfl
  refine ⟨mapCoeff1 r' continuous_of_discreteTopology hcompat_r xR, fun φ => ?_⟩
  rw [phiResK_mapCoeff1 hρR hρ r' continuous_of_discreteTopology hcompat_r xR φ,
    hall (φ.comp r')]
  show ξ.fam ((φ.comp r').comp ι') = ξ.fam φ
  congr 1
  ext v
  show φ (r (ι v)) = φ v
  rw [hri v]

end FamiliesExtend

/-! ## §2 The conjugation modules on the deep subgroup and on the quotient

`GQ2.conjActHom`/`conjModuleDeep`/`conjActQuotHom`/`conjModuleQuot` (`GQ2/AdmissibleCount.lean`
:172–:248) retyped: LG4a's `conjAct_deepClassesAt` (its §7) is exactly the invariance that lets
the `conjModule` conjugation action restrict to `deepClassesSubgroupAt` and descend to the
quotient. -/

section ConjModules

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)

/-- `conjAct ρ g` packaged as an additive endomorphism of `H¹(N_K, 𝔽₂)`, so it can feed
`QuotientAddGroup.map`. -/
noncomputable def conjActHomK (g : Γ) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) →+
      H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) :=
  AddMonoidHom.mk' (conjAct ρ g) (conjAct_add ρ g)

/-- **The restricted `conjModule` action on the deep subgroup** — `GQ2.conjModuleDeep` retyped;
well-defined by LG4a's `conjAct_deepClassesAt`.  A `@[reducible] def`; consumers `letI` it. -/
@[reducible] noncomputable def conjModuleDeepK (hρsurj : Function.Surjective ⇑ρ) :
    DistribMulAction C ↥(deepClassesSubgroupAt (kerAnc anc ρ)) where
  smul c ξ := ⟨conjAct ρ (Function.surjInv hρsurj c) ξ.1,
    conjAct_deepClassesAt anc ρ (Function.surjInv hρsurj c) ξ.2⟩
  one_smul ξ := by
    apply Subtype.ext
    show conjAct ρ (Function.surjInv hρsurj 1) ξ.1 = ξ.1
    refine (conjAct_ker ρ _ 1 ?_ ξ.1).trans (conjAct_one ρ ξ.1)
    rw [Function.surjInv_eq hρsurj, map_one]
  mul_smul c d ξ := by
    apply Subtype.ext
    show conjAct ρ (Function.surjInv hρsurj (c * d)) ξ.1
      = conjAct ρ (Function.surjInv hρsurj c) (conjAct ρ (Function.surjInv hρsurj d) ξ.1)
    rw [← conjAct_comp]
    refine conjAct_ker ρ _ _ ?_ ξ.1
    rw [map_mul, Function.surjInv_eq hρsurj, Function.surjInv_eq hρsurj,
      Function.surjInv_eq hρsurj]
  smul_zero c := Subtype.ext (conjAct_zero ρ (Function.surjInv hρsurj c))
  smul_add c ξ η := Subtype.ext (conjAct_add ρ (Function.surjInv hρsurj c) ξ.1 η.1)

/-- The descent of `conjAct ρ g` to `H¹(N_K) ⧸ deepClassesSubgroupAt`. -/
noncomputable def conjActQuotHomK (g : Γ) :
    (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸ deepClassesSubgroupAt (kerAnc anc ρ)) →+
      (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸ deepClassesSubgroupAt (kerAnc anc ρ)) :=
  QuotientAddGroup.map (deepClassesSubgroupAt (kerAnc anc ρ))
    (deepClassesSubgroupAt (kerAnc anc ρ)) (conjActHomK ρ g)
    (fun _ hx => AddSubgroup.mem_comap.mpr (conjAct_deepClassesAt anc ρ g hx))

/-- Computation rule for `conjActQuotHomK` on a class. -/
theorem conjActQuotHomK_mk (g : Γ) (a : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    conjActQuotHomK anc ρ g (QuotientAddGroup.mk a) = QuotientAddGroup.mk (conjAct ρ g a) :=
  QuotientAddGroup.map_mk _ _ (conjActHomK ρ g) _ a

/-- **The induced `conjModule` action on the quotient** — `GQ2.conjModuleQuot` retyped. -/
@[reducible] noncomputable def conjModuleQuotK (hρsurj : Function.Surjective ⇑ρ) :
    DistribMulAction C (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸
        deepClassesSubgroupAt (kerAnc anc ρ)) where
  smul c x := conjActQuotHomK anc ρ (Function.surjInv hρsurj c) x
  one_smul x := by
    refine QuotientAddGroup.induction_on x (fun a => ?_)
    show conjActQuotHomK anc ρ (Function.surjInv hρsurj 1) (QuotientAddGroup.mk a)
      = QuotientAddGroup.mk a
    rw [conjActQuotHomK_mk]
    congr 1
    refine (conjAct_ker ρ _ 1 ?_ a).trans (conjAct_one ρ a)
    rw [Function.surjInv_eq hρsurj, map_one]
  mul_smul c d x := by
    refine QuotientAddGroup.induction_on x (fun a => ?_)
    show conjActQuotHomK anc ρ (Function.surjInv hρsurj (c * d)) (QuotientAddGroup.mk a)
      = conjActQuotHomK anc ρ (Function.surjInv hρsurj c)
          (conjActQuotHomK anc ρ (Function.surjInv hρsurj d) (QuotientAddGroup.mk a))
    simp only [conjActQuotHomK_mk]
    congr 1
    show conjAct ρ (Function.surjInv hρsurj (c * d)) a
      = conjAct ρ (Function.surjInv hρsurj c) (conjAct ρ (Function.surjInv hρsurj d) a)
    rw [← conjAct_comp]
    refine conjAct_ker ρ _ _ ?_ a
    rw [map_mul, Function.surjInv_eq hρsurj, Function.surjInv_eq hρsurj,
      Function.surjInv_eq hρsurj]
  smul_zero c := map_zero _
  smul_add c x y := map_add _ x y

end ConjModules

/-! ## §3 Admissible families as equivariant Homs

`GQ2/AdmissibleCount.lean` :250–:455 retyped: the bridge `AdmissibleFamK ≃ equivHoms C V^∨ H¹(N_K)`
(and its deep-valued restriction), then the `U_{e+1}` short-exact-sequence count.  The abstract
engine `GQ2.card_equivHoms_quotient_ses` and the dual module `GQ2.dualModule` mention only `C`, so
they are consumed verbatim. -/

section AdmissibleBridges

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [DistribMulAction C V]
variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)

omit [Finite C] [TopologicalSpace V] [DiscreteTopology V] [Finite V] in
/-- **The core equivariance of an admissible family** — `GQ2.fam_equivariant` retyped: `ξ.fam`
intertwines the dual action `dualModule` on `V^∨` with the conjugation action on `H¹(N_K)`. -/
theorem famK_equivariant (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hρsurj : Function.Surjective ⇑ρ) (ξ : AdmissibleFamK (V := V) ρ) (c : C)
    (φ : V →+ ZMod 2) :
    ξ.fam (φ.comp (DistribSMul.toAddMonoidHom V (c⁻¹ : C)))
      = conjAct ρ (Function.surjInv hρsurj c) (ξ.fam φ) := by
  rw [ξ.equiv' (Function.surjInv hρsurj c) φ]
  refine congrArg ξ.fam (AddMonoidHom.ext fun v => ?_)
  show φ ((c⁻¹ : C) • v) = φ ((Function.surjInv hρsurj c)⁻¹ • v)
  rw [hρ (Function.surjInv hρsurj c)⁻¹ v, map_inv, Function.surjInv_eq hρsurj]

/-- **The bridge `AdmissibleFamK ≃ equivHoms`** — `GQ2.admissibleFamEquiv` retyped. -/
noncomputable def admissibleFamKEquiv
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (hρsurj : Function.Surjective ⇑ρ) :
    letI := conjModule ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    AdmissibleFamK (V := V) ρ ≃ equivHoms C (V →+ ZMod 2)
      (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :=
  letI := conjModule ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  { toFun := fun ξ => ⟨AddMonoidHom.mk' ξ.fam ξ.add',
      fun c φ => famK_equivariant ρ hρ hρsurj ξ c φ⟩
    invFun := fun f =>
      { fam := f.1
        add' := map_add f.1
        equiv' := fun g φ => by
          calc conjAct ρ g (f.1 φ)
              = conjAct ρ (Function.surjInv hρsurj (ρ g)) (f.1 φ) :=
                conjAct_ker ρ g (Function.surjInv hρsurj (ρ g))
                  (Function.surjInv_eq hρsurj (ρ g)).symm (f.1 φ)
            _ = (dualModule.toSMul.smul (ρ g) φ |> f.1) := (f.2 (ρ g) φ).symm
            _ = f.1 (φ.comp (DistribSMul.toAddMonoidHom V g⁻¹)) :=
                congrArg f.1 (AddMonoidHom.ext fun v => by
                  show φ ((ρ g)⁻¹ • v) = φ (g⁻¹ • v)
                  rw [hρ g⁻¹ v, map_inv]) }
    left_inv := fun ξ => rfl
    right_inv := fun f => Subtype.ext (AddMonoidHom.ext fun φ => rfl) }

omit [Finite C] [TopologicalSpace V] [DiscreteTopology V] [Finite V] in
/-- **Count admissible families as equivariant Homs** — `GQ2.card_admissibleFam_eq` retyped. -/
theorem card_admissibleFamK_eq (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hρsurj : Function.Surjective ⇑ρ) :
    letI := conjModule ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    Nat.card (AdmissibleFamK (V := V) ρ)
      = Nat.card ↥(equivHoms C (V →+ ZMod 2)
          (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))) :=
  letI := conjModule ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  Nat.card_congr (admissibleFamKEquiv ρ hρ hρsurj)

/-- **The deep-families bridge** — `GQ2.deepFamEquiv` retyped. -/
noncomputable def deepFamKEquiv
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (hρsurj : Function.Surjective ⇑ρ) :
    letI := conjModuleDeepK anc ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    {ξ : AdmissibleFamK (V := V) ρ // ∀ φ : V →+ ZMod 2,
        ξ.fam φ ∈ deepClassesAt (kerAnc anc ρ)}
      ≃ equivHoms C (V →+ ZMod 2) ↥(deepClassesSubgroupAt (kerAnc anc ρ)) :=
  letI := conjModuleDeepK anc ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  { toFun := fun ξ => ⟨AddMonoidHom.mk' (fun φ => ⟨ξ.1.fam φ, ξ.2 φ⟩)
      (fun φ ψ => Subtype.ext (ξ.1.add' φ ψ)),
      fun c φ => Subtype.ext (famK_equivariant ρ hρ hρsurj ξ.1 c φ)⟩
    invFun := fun f =>
      ⟨{ fam := fun φ => (f.1 φ).1
         add' := fun φ ψ => by rw [map_add]; rfl
         equiv' := fun g φ => by
           calc conjAct ρ g ((f.1 φ).1)
               = conjAct ρ (Function.surjInv hρsurj (ρ g)) (f.1 φ).1 :=
                 conjAct_ker ρ g (Function.surjInv hρsurj (ρ g))
                   (Function.surjInv_eq hρsurj (ρ g)).symm (f.1 φ).1
             _ = ((dualModule.toSMul.smul (ρ g) φ |> f.1)
                   : ↥(deepClassesSubgroupAt (kerAnc anc ρ))).1 :=
                 (congrArg Subtype.val (f.2 (ρ g) φ)).symm
             _ = (f.1 (φ.comp (DistribSMul.toAddMonoidHom V g⁻¹))).1 :=
                 congrArg (fun ψ => (f.1 ψ).1) (AddMonoidHom.ext fun v => by
                   show φ ((ρ g)⁻¹ • v) = φ (g⁻¹ • v)
                   rw [hρ g⁻¹ v, map_inv]) },
       fun φ => (f.1 φ).2⟩
    left_inv := fun ξ => rfl
    right_inv := fun f => Subtype.ext (AddMonoidHom.ext fun φ => Subtype.ext rfl) }

omit [Finite C] [TopologicalSpace V] [DiscreteTopology V] [Finite V] in
/-- **Count the deep families as equivariant Homs into the deep subgroup** —
`GQ2.card_deepFam_eq` retyped. -/
theorem card_deepFamK_eq (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hρsurj : Function.Surjective ⇑ρ) :
    letI := conjModuleDeepK anc ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    Nat.card {ξ : AdmissibleFamK (V := V) ρ // ∀ φ : V →+ ZMod 2,
        ξ.fam φ ∈ deepClassesAt (kerAnc anc ρ)}
      = Nat.card ↥(equivHoms C (V →+ ZMod 2) ↥(deepClassesSubgroupAt (kerAnc anc ρ))) :=
  letI := conjModuleDeepK anc ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  Nat.card_congr (deepFamKEquiv anc ρ hρ hρsurj)

omit [TopologicalSpace V] [DiscreteTopology V] [DistribMulAction Γ V] in
/-- **The `U_{e+1}` short exact sequence count** — `GQ2.card_equivHoms_deepSES` retyped; the
abstract engine `GQ2.card_equivHoms_quotient_ses` is used verbatim. -/
theorem card_equivHoms_deepSESK (hρsurj : Function.Surjective ⇑ρ)
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))]
    {Nreg : ℕ} (ι : (V →+ ZMod 2) →+ (Fin Nreg → C → ZMod 2))
    (r : (Fin Nreg → C → ZMod 2) →+ (V →+ ZMod 2))
    (hι : ∀ (h : C) (φ : V →+ ZMod 2) (n : Fin Nreg) (x : C),
        ι ((dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h φ) n x = ι φ n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin Nreg → C → ZMod 2),
        r (fun n x => F n (h⁻¹ * x))
          = (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h (r F))
    (hri : ∀ φ : V →+ ZMod 2, r (ι φ) = φ) :
    letI := conjModule ρ hρsurj
    letI := conjModuleDeepK anc ρ hρsurj
    letI := conjModuleQuotK anc ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    Nat.card ↥(equivHoms C (V →+ ZMod 2) (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)))
      = Nat.card ↥(equivHoms C (V →+ ZMod 2) ↥(deepClassesSubgroupAt (kerAnc anc ρ)))
        * Nat.card ↥(equivHoms C (V →+ ZMod 2)
            (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸
              deepClassesSubgroupAt (kerAnc anc ρ))) := by
  letI := conjModule ρ hρsurj
  letI := conjModuleDeepK anc ρ hρsurj
  letI := conjModuleQuotK anc ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  haveI : Finite (V →+ ZMod 2) :=
    Finite.of_injective (DFunLike.coe : (V →+ ZMod 2) → (V → ZMod 2)) DFunLike.coe_injective
  exact card_equivHoms_quotient_ses (C := C) (U := V →+ ZMod 2)
    (A := H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
    (instA := conjModule ρ hρsurj)
    (Deep := deepClassesSubgroupAt (kerAnc anc ρ))
    (instDeep := conjModuleDeepK anc ρ hρsurj) (instQuot := conjModuleQuotK anc ρ hρsurj)
    (h1_zmodTwo_add_self_dp) ι r hι hr hri
    (fun c w => rfl)
    (fun c w => (conjActQuotHomK_mk anc ρ (Function.surjInv hρsurj c) w).symm)

/-! ### §4 The `hduality`-parametric dimension clause -/

/-- **The deep-half dimension clause from the duality** — `GQ2.card_deepPart_sq_of_duality`
(`GQ2/AdmissibleCount.lean` :466) retyped: chaining LG4a's `card_H1_eq_card_famK` /
`card_deepPartK_eq_card_deepFam` with §3's Hom-bridges and the SES count, the graded Hilbert
duality `#Hom_C(V^∨, Deep) = #Hom_C(V^∨, H¹/Deep)` collapses the product to a square. -/
theorem card_deepPartK_sq_of_duality
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (hV2 : ∀ v : V, v + v = 0)
    (hρsurj : Function.Surjective ⇑ρ)
    (hinf : InflationVanishesK (V := V) ρ) (hext : FamiliesExtendK (V := V) ρ)
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))]
    {Nreg : ℕ} (ι : (V →+ ZMod 2) →+ (Fin Nreg → C → ZMod 2))
    (r : (Fin Nreg → C → ZMod 2) →+ (V →+ ZMod 2))
    (hι : ∀ (h : C) (φ : V →+ ZMod 2) (n : Fin Nreg) (x : C),
        ι ((dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h φ) n x = ι φ n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin Nreg → C → ZMod 2),
        r (fun n x => F n (h⁻¹ * x))
          = (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h (r F))
    (hri : ∀ φ : V →+ ZMod 2, r (ι φ) = φ)
    (hduality :
      letI := conjModuleDeepK anc ρ hρsurj
      letI := conjModuleQuotK anc ρ hρsurj
      letI : DistribMulAction C (V →+ ZMod 2) := dualModule
      Nat.card ↥(equivHoms C (V →+ ZMod 2) ↥(deepClassesSubgroupAt (kerAnc anc ρ)))
        = Nat.card ↥(equivHoms C (V →+ ZMod 2)
            (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸
              deepClassesSubgroupAt (kerAnc anc ρ)))) :
    Nat.card (deepPartK (V := V) anc ρ) ^ 2 = Nat.card (H1 Γ V) := by
  letI := conjModule ρ hρsurj
  letI := conjModuleDeepK anc ρ hρsurj
  letI := conjModuleQuotK anc ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  have hH1 := card_H1_eq_card_famK hρ hV2 hinf hext
  have hAF := card_admissibleFamK_eq ρ hρ hρsurj
  have hSES := card_equivHoms_deepSESK anc ρ hρsurj ι r hι hr hri
  have hDP := card_deepPartK_eq_card_deepFam anc hρ hV2 hinf hext
  have hDF := card_deepFamK_eq anc ρ hρ hρsurj
  calc Nat.card (deepPartK (V := V) anc ρ) ^ 2
      = Nat.card ↥(equivHoms C (V →+ ZMod 2) ↥(deepClassesSubgroupAt (kerAnc anc ρ))) ^ 2 := by
        rw [hDP, hDF]
    _ = Nat.card ↥(equivHoms C (V →+ ZMod 2) ↥(deepClassesSubgroupAt (kerAnc anc ρ)))
          * Nat.card ↥(equivHoms C (V →+ ZMod 2)
            ↥(deepClassesSubgroupAt (kerAnc anc ρ))) := sq _
    _ = Nat.card ↥(equivHoms C (V →+ ZMod 2) ↥(deepClassesSubgroupAt (kerAnc anc ρ)))
          * Nat.card ↥(equivHoms C (V →+ ZMod 2)
            (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸
              deepClassesSubgroupAt (kerAnc anc ρ))) := by rw [hduality]
    _ = Nat.card ↥(equivHoms C (V →+ ZMod 2)
          (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))) := hSES.symm
    _ = Nat.card (AdmissibleFamK (V := V) ρ) := hAF.symm
    _ = Nat.card (H1 Γ V) := hH1.symm

end AdmissibleBridges

/-! ## §5 The middle twist (H5) at an anchor

`GQ2/DeepDuality.lean` §MidTwist (:1099–:1269) retyped.  Residue-triviality is a **`ℚ₂`-side**
predicate at a subgroup of `G_ℚ₂` (`GQ2.IsResidueTrivial`), so under LG4a's anchoring convention
it is taken at `ancSubgroup (kerAnc anc ρ)` and consumed verbatim; only the conjugation
bookkeeping moves, through `anc`.

Paper Lemma 6.10 / the (H5) core: a residue-trivial `anc g` moves a mid class by a deep class.
With `ξ = [κ_β]`, `β² = A = 1 + 2b` mid, 2-torsion turns the difference into
`[κ_{anc g•β}] + [κ_β] = [κ_{(anc g•β)β}]`, and `(anc g•A)·A = 1 + 2(anc g•b + b + 2(anc g•b)b)`
is a deep unit by residue-triviality at `x := b`. -/

section MidTwist

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- **Anchored-fixedness is stable under the ambient action**: if `x` is fixed by the whole
anchored splitting subgroup, so is `anc g • x` (normality of `ker ρ` in `Γ`, pushed through the
anchor).  This is the `key`/`hmove` step of LG4a's `conjAct_deepClassesAt`, named. -/
theorem smul_anc_fix (g : Γ) {x : ℚ̄₂}
    (hfix : ∀ y ∈ ancSubgroup (kerAnc anc ρ), y • x = x) :
    ∀ m ∈ ancSubgroup (kerAnc anc ρ), m • (anc g • x) = anc g • x := by
  have key : ∀ n : ↥(ρ.toMonoidHom.ker : Subgroup Γ),
      (kerAnc anc ρ n) • (anc g • x) = anc g • x := by
    intro n
    rw [← mul_smul, show kerAnc anc ρ n * anc g = anc g * ((anc g)⁻¹ * kerAnc anc ρ n * anc g)
      from by group, mul_smul,
      show ((anc g)⁻¹ * kerAnc anc ρ n * anc g) • x = x from
        hfix _ (by rw [← kerAnc_conjMap anc ρ g n]; exact mem_ancSubgroup _ _)]
  rintro _ ⟨n, rfl⟩
  exact key n

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- **Residue-triviality is conjugation-stable at an anchor** — `GQ2.IsResidueTrivial.conj`
retyped: conjugating the test vector back by `anc h` preserves anchored fixedness
(`smul_anc_fix`) and the norm (`GQ2.norm_galois`). -/
theorem isResidueTrivial_anc_conj {g : Γ}
    (hg : IsResidueTrivial (ancSubgroup (kerAnc anc ρ)) (anc g)) (h : Γ) :
    IsResidueTrivial (ancSubgroup (kerAnc anc ρ)) (anc h * anc g * (anc h)⁻¹) := by
  intro x hxfix hx1
  have hyfix : ∀ m ∈ ancSubgroup (kerAnc anc ρ), m • ((anc h)⁻¹ • x) = (anc h)⁻¹ • x := by
    have hy := smul_anc_fix anc ρ h⁻¹ hxfix
    rwa [map_inv] at hy
  have hy1 : ‖(anc h)⁻¹ • x‖ ≤ 1 := by rw [norm_galois]; exact hx1
  have hkey : (anc h * anc g * (anc h)⁻¹) • x - x
      = anc h • (anc g • ((anc h)⁻¹ • x) - (anc h)⁻¹ • x) := by
    rw [AlgEquiv.smul_def (anc h), map_sub, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
      smul_inv_smul, ← mul_smul, ← mul_smul]
  rw [hkey, norm_galois]
  exact hg ((anc h)⁻¹ • x) hyfix hy1

/-- **The middle twist, class level** (paper Lemma 6.10 / the (H5) core) —
`GQ2.conjAct_mid_sub_mem_deep` retyped at an anchor. -/
theorem conjAct_mid_sub_mem_deepAt (g : Γ)
    (hg : IsResidueTrivial (ancSubgroup (kerAnc anc ρ)) (anc g))
    {ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)}
    (hξ : ξ ∈ midClassesSubgroupAt (kerAnc anc ρ)) :
    conjAct ρ g ξ - ξ ∈ deepClassesSubgroupAt (kerAnc anc ρ) := by
  obtain ⟨A, β, hmid', hsq, hβ0, rfl⟩ := hξ
  obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hmid'
  have h2lt1 : ‖(2 : ℚ̄₂)‖ < 1 := by
    rw [show (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 from (map_ofNat _ 2).symm,
      norm_algebraMap' (𝕜' := ℚ̄₂) (2 : ℚ_[2])]
    exact Padic.norm_p_lt_one
  -- conjugated data
  have hgA0 : anc g • A ≠ 0 := by rw [AlgEquiv.smul_def]; simpa using hA0
  have hgβ0 : anc g • β ≠ 0 := by rw [AlgEquiv.smul_def]; simpa using hβ0
  have hgsq : (anc g • β) ^ 2 = anc g • A := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, ← map_pow, hsq]
  have hgAeq : anc g • A = 1 + 2 * (anc g • b) := by
    rw [hAeq, AlgEquiv.smul_def, map_add, map_one, map_mul, map_ofNat, ← AlgEquiv.smul_def]
  have hsqprod : ((anc g • β) * β) ^ 2 = (anc g • A) * A := by rw [mul_pow, hgsq, hsq]
  have hgAfix := smul_anc_fix anc ρ g hAfix
  have hgbfix := smul_anc_fix anc ρ g hbfix
  refine ⟨(anc g • A) * A, (anc g • β) * β, ⟨mul_ne_zero hgA0 hA0, fun m hm => ?_,
      anc g • b + b + 2 * (anc g • b) * b, fun m hm => ?_, by rw [hgAeq, hAeq]; ring, ?_⟩,
    hsqprod, mul_ne_zero hgβ0 hβ0, ?_⟩
  · -- anchored fixedness of the product `(anc g•A)·A`
    rw [AlgEquiv.smul_def, map_mul, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
      hgAfix m hm, hAfix m hm]
  · -- anchored fixedness of `b' = anc g•b + b + 2(anc g•b)b`
    rw [AlgEquiv.smul_def, map_add, map_add, map_mul, map_mul, map_ofNat,
      ← AlgEquiv.smul_def, ← AlgEquiv.smul_def, hgbfix m hm, hbfix m hm]
  · -- `‖b'‖ < 1`: the inertia estimate
    have hgb1 : ‖anc g • b‖ ≤ 1 := by rw [norm_galois]; exact hb
    have hsum : ‖anc g • b + b‖ < 1 := by
      have hsplit : anc g • b + b = anc g • b - b + 2 * b := by ring
      rw [hsplit]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [max_lt_iff]
      refine ⟨hg b hbfix hb, ?_⟩
      calc ‖2 * b‖ = ‖(2 : ℚ̄₂)‖ * ‖b‖ := norm_mul _ _
        _ ≤ ‖(2 : ℚ̄₂)‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = ‖(2 : ℚ̄₂)‖ := mul_one _
        _ < 1 := h2lt1
    have hprod : ‖2 * (anc g • b) * b‖ < 1 := by
      rw [norm_mul, norm_mul]
      calc ‖(2 : ℚ̄₂)‖ * ‖anc g • b‖ * ‖b‖
          ≤ ‖(2 : ℚ̄₂)‖ * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hgb1 (norm_nonneg _)) hb (norm_nonneg _)
              (by positivity)
        _ = ‖(2 : ℚ̄₂)‖ := by ring
        _ < 1 := h2lt1
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
    rw [max_lt_iff]
    exact ⟨hsum, hprod⟩
  · -- the class identity `[κ_{(anc g•β)β}] = conjAct ρ g [κ_β] − [κ_β]`
    have hZ1g := kummerAnc_mem_Z1 (kerAnc anc ρ) hgsq hgβ0 hgAfix
    have hZ1 := kummerAnc_mem_Z1 (kerAnc anc ρ) hsq hβ0 hAfix
    have heq : conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
          (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n)))
        = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
          (fun n => Kummer.kummerCocycleFun (anc g • β) (kerAnc anc ρ n)) :=
      calc conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n)))
          = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ (conjMap ρ g n))) :=
            conjAct_h1ofFun ρ g hZ1
        _ = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              (fun n => Kummer.kummerCocycleFun (anc g • β) (kerAnc anc ρ n)) := by
            congr 1
            funext n
            rw [kerAnc_conjMap anc ρ g n]
            exact kcf_conj β (anc g) (kerAnc anc ρ n)
    exact calc
      H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
          (fun n => Kummer.kummerCocycleFun ((anc g • β) * β) (kerAnc anc ρ n))
          = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              ((fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) =>
                  Kummer.kummerCocycleFun (anc g • β) (kerAnc anc ρ n))
                + fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) =>
                  Kummer.kummerCocycleFun β (kerAnc anc ρ n)) := by
            congr 1
            funext n
            exact kcf_mul_of_fixedAt hgsq hsq hgβ0 hβ0
              (hgAfix _ (mem_ancSubgroup (kerAnc anc ρ) n))
              (hAfix _ (mem_ancSubgroup (kerAnc anc ρ) n))
        _ = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              (fun n => Kummer.kummerCocycleFun (anc g • β) (kerAnc anc ρ n))
            + H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n)) :=
            DeepPart.H1ofFun_add hZ1g hZ1
        _ = conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n)))
            + H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n)) := by rw [heq]
        _ = conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n)))
            - H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
              (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n)) := by
            rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left
              (h1_zmodTwo_add_self_dp (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
                (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n))))]

/-- **The middle twist, `C`-conjugate form** — the literal `hmid` input of
`GQ2.card_equivHoms_deep_eq_quot` at the `conjModule` instantiation, retyped at an anchor: if
SOME lift `g₀ : Γ` of `t₀` is anchored-residue-trivial, then for EVERY `d : C` the `surjInv`-lift
of `d·t₀·d⁻¹` twists mid classes by deep classes. -/
theorem conjAct_surjInv_conj_mid_sub_mem_deepAt (hρsurj : Function.Surjective ⇑ρ)
    {g₀ : Γ} {t₀ : C} (hg₀ : ρ g₀ = t₀)
    (hg₀rt : IsResidueTrivial (ancSubgroup (kerAnc anc ρ)) (anc g₀)) (d : C)
    {ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)}
    (hξ : ξ ∈ midClassesSubgroupAt (kerAnc anc ρ)) :
    conjAct ρ (Function.surjInv hρsurj (d * t₀ * d⁻¹)) ξ - ξ
      ∈ deepClassesSubgroupAt (kerAnc anc ρ) := by
  have hkey : conjAct ρ (Function.surjInv hρsurj (d * t₀ * d⁻¹)) ξ
      = conjAct ρ (Function.surjInv hρsurj d * g₀ * (Function.surjInv hρsurj d)⁻¹) ξ :=
    conjAct_ker ρ _ _ (by
      rw [Function.surjInv_eq hρsurj, map_mul, map_mul, map_inv,
        Function.surjInv_eq hρsurj, hg₀]) ξ
  rw [hkey]
  refine conjAct_mid_sub_mem_deepAt anc ρ _ ?_ hξ
  have hrt := isResidueTrivial_anc_conj anc ρ hg₀rt (Function.surjInv hρsurj d)
  rwa [← map_mul, ← map_inv, ← map_mul] at hrt

end MidTwist

/-! ## §6 The `N_K ↔ G_k` transport and the (H4) structural count

`GQ2/DeepCount/Transport.lean` retyped through the anchor.  The `ℚ₂` file transports `H¹` between
`ker ρ` and `G_k` by cocycle precomposition along the two **identity inclusions**
`kerToFixing`/`fixingToKer` supplied by the pointwise `hker`.  At a general anchored source only
the forward map is free (LG4a's `kerToFixingAt`, `n ↦ anc n`); its inverse exists exactly when the
anchor is **injective** and is continuous exactly when the anchor is **inducing**.  Both hold
verbatim in the campaign (`Γ = ↥U`, `anc = U.subtype`, where they are `Subtype.val_injective` and
`Topology.IsInducing.subtypeVal`), so they are threaded as the two hypotheses `hancinj`/`hancind`
rather than assumed globally.

No subgroup-equality cast is formed anywhere: `hker` stays pointwise, exactly as in LG4a's §4. -/

section KerFixTransport

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C]

/-- **The canonical representative of an `H1ofFun`-class is the function itself** (`B¹ = 0` at
trivial coefficients) — the `out`-form of LG4a's `eq_of_H1ofFun_eq_dp`, factored out of the four
`ℚ₂` computation rules that re-prove it inline. -/
theorem out_h1ofFun_eq {Θ : Type} [Group Θ] [TopologicalSpace Θ] [IsTopologicalGroup Θ]
    [DistribMulAction Θ (ZMod 2)] [ContinuousSMul Θ (ZMod 2)]
    {f : Θ → ZMod 2} (hf : f ∈ Z1 Θ (ZMod 2)) :
    (Quotient.out (H1ofFun Θ f) : ↥(Z1 Θ (ZMod 2))).1 = f := by
  refine eq_of_H1ofFun_eq_dp (Quotient.out (H1ofFun Θ f)).2 hf ?_
  rw [H1ofFun_of_mem (Quotient.out (H1ofFun Θ f)).2]
  exact Quotient.out_eq _

variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)
  (k : IntermediateField ℚ_[2] ℚ̄₂)

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- **The anchored inclusion `N_K → G_k` is bijective**: surjectivity is `hker` read on the
anchored subgroup (which *is* the `anc`-image of `ker ρ`), injectivity is the anchor's. -/
theorem kerToFixingAt_bijective (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup) :
    Function.Bijective (kerToFixingAt anc ρ k hker) := by
  constructor
  · intro n m h
    exact Subtype.ext (hancinj (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn⟩ := (hker y).mpr hy
    exact ⟨n, Subtype.ext hn⟩

omit [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- The inverse inclusion `↥G_k → ↥N_K` — `GQ2.fixingToKer` retyped; it exists because
`kerToFixingAt` is bijective. -/
noncomputable def fixingToKerAt (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup) :
    ↥k.fixingSubgroup → ↥(ρ.toMonoidHom.ker : Subgroup Γ) :=
  (Equiv.ofBijective _ (kerToFixingAt_bijective anc ρ k hancinj hker)).symm

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
theorem kerToFixingAt_fixingToKerAt (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (y : ↥k.fixingSubgroup) :
    kerToFixingAt anc ρ k hker (fixingToKerAt anc ρ k hancinj hker y) = y :=
  (Equiv.ofBijective _ (kerToFixingAt_bijective anc ρ k hancinj hker)).apply_symm_apply y

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
theorem fixingToKerAt_kerToFixingAt (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (n : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    fixingToKerAt anc ρ k hancinj hker (kerToFixingAt anc ρ k hker n) = n :=
  (Equiv.ofBijective _ (kerToFixingAt_bijective anc ρ k hancinj hker)).symm_apply_apply n

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- The anchor value of the inverse inclusion is the element itself. -/
theorem kerAnc_fixingToKerAt (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (y : ↥k.fixingSubgroup) :
    kerAnc anc ρ (fixingToKerAt anc ρ k hancinj hker y) = (y : GalQ2) :=
  congrArg Subtype.val (kerToFixingAt_fixingToKerAt anc ρ k hancinj hker y)

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
theorem fixingToKerAt_mul (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (y z : ↥k.fixingSubgroup) :
    fixingToKerAt anc ρ k hancinj hker (y * z)
      = fixingToKerAt anc ρ k hancinj hker y * fixingToKerAt anc ρ k hancinj hker z := by
  refine (kerToFixingAt_bijective anc ρ k hancinj hker).1 ?_
  rw [kerToFixingAt_fixingToKerAt, kerToFixingAt_mul, kerToFixingAt_fixingToKerAt,
    kerToFixingAt_fixingToKerAt]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- Continuity of the inverse inclusion, from the anchor being **inducing** (in the campaign
`anc = U.subtype`, where this is `Topology.IsInducing.subtypeVal`). -/
theorem continuous_fixingToKerAt (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (hancind : Topology.IsInducing ⇑anc) :
    Continuous (fixingToKerAt anc ρ k hancinj hker) := by
  have hind : Topology.IsInducing
      (fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) => (kerAnc anc ρ n : GalQ2)) :=
    hancind.comp Topology.IsInducing.subtypeVal
  rw [hind.continuous_iff]
  have hcomp : ((fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) => (kerAnc anc ρ n : GalQ2))
      ∘ fixingToKerAt anc ρ k hancinj hker)
      = (Subtype.val : ↥k.fixingSubgroup → GalQ2) :=
    funext fun y => kerAnc_fixingToKerAt anc ρ k hancinj hker y
  rw [hcomp]
  exact continuous_subtype_val

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- Precomposition with `fixingToKerAt` carries `Z¹(N_K)` to `Z¹(G_k)`. -/
theorem comp_fixingToKerAt_mem_Z1 (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hancind : Topology.IsInducing ⇑anc)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup Γ) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    (fun n => f (fixingToKerAt anc ρ k hancinj hker n)) ∈ Z1 k.fixingSubgroup (ZMod 2) := by
  obtain ⟨hfc, hcoc⟩ := mem_Z1_iff.mp hf
  refine mem_Z1_iff.mpr
    ⟨hfc.comp (continuous_fixingToKerAt anc ρ k hancinj hker hancind), fun n m => ?_⟩
  show f (fixingToKerAt anc ρ k hancinj hker (n * m))
    = f (fixingToKerAt anc ρ k hancinj hker n) + n • f (fixingToKerAt anc ρ k hancinj hker m)
  rw [fixingToKerAt_mul, hcoc, htriv, smul_zmodTwo]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- Precomposition with `kerToFixingAt` carries `Z¹(G_k)` to `Z¹(N_K)`. -/
theorem comp_kerToFixingAt_mem_Z1
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    {f : ↥k.fixingSubgroup → ZMod 2} (hf : f ∈ Z1 k.fixingSubgroup (ZMod 2)) :
    (fun n => f (kerToFixingAt anc ρ k hker n))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) := by
  obtain ⟨hfc, hcoc⟩ := mem_Z1_iff.mp hf
  refine mem_Z1_iff.mpr ⟨hfc.comp (continuous_kerToFixingAt anc ρ k hker), fun n m => ?_⟩
  show f (kerToFixingAt anc ρ k hker (n * m))
    = f (kerToFixingAt anc ρ k hker n) + n • f (kerToFixingAt anc ρ k hker m)
  rw [kerToFixingAt_mul, hcoc, htriv, smul_zmodTwo]

/-- Transport `H¹(N_K) → H¹(G_k)` (cocycle precomposition with `fixingToKerAt`). -/
noncomputable def h1KerToFixAt (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) : H1 k.fixingSubgroup (ZMod 2) :=
  H1ofFun k.fixingSubgroup
    (fun n => (Quotient.out ξ).1 (fixingToKerAt anc ρ k hancinj hker n))

/-- Transport `H¹(G_k) → H¹(N_K)` (cocycle precomposition with `kerToFixingAt`). -/
noncomputable def h1FixToKerAt
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (η : H1 k.fixingSubgroup (ZMod 2)) : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) :=
  H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
    (fun n => (Quotient.out η).1 (kerToFixingAt anc ρ k hker n))

/-- Computation rule for `h1KerToFixAt` (`B¹ = 0`). -/
theorem h1KerToFixAt_h1ofFun (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup Γ) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    h1KerToFixAt anc ρ k hancinj hker (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) f)
      = H1ofFun k.fixingSubgroup (fun n => f (fixingToKerAt anc ρ k hancinj hker n)) := by
  unfold h1KerToFixAt
  rw [out_h1ofFun_eq hf]

/-- Computation rule for `h1FixToKerAt` (`B¹ = 0`). -/
theorem h1FixToKerAt_h1ofFun
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    {f : ↥k.fixingSubgroup → ZMod 2} (hf : f ∈ Z1 k.fixingSubgroup (ZMod 2)) :
    h1FixToKerAt anc ρ k hker (H1ofFun k.fixingSubgroup f)
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
          (fun n => f (kerToFixingAt anc ρ k hker n)) := by
  unfold h1FixToKerAt
  rw [out_h1ofFun_eq hf]

/-- The round trip `N_K → G_k → N_K` is the identity. -/
theorem h1FixToKerAt_h1KerToFixAt (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hancind : Topology.IsInducing ⇑anc)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    h1FixToKerAt anc ρ k hker (h1KerToFixAt anc ρ k hancinj hker ξ) = ξ := by
  induction ξ using QuotientAddGroup.induction_on with
  | H a =>
    rw [show (QuotientAddGroup.mk a : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) a.1 from (H1ofFun_of_mem a.2).symm,
      h1KerToFixAt_h1ofFun anc ρ k hancinj hker a.2,
      h1FixToKerAt_h1ofFun anc ρ k hker
        (comp_fixingToKerAt_mem_Z1 anc ρ k hancinj hker htriv hancind a.2)]
    exact congrArg _ (funext fun n => congrArg a.1
      (fixingToKerAt_kerToFixingAt anc ρ k hancinj hker n))

/-- The round trip `G_k → N_K → G_k` is the identity. -/
theorem h1KerToFixAt_h1FixToKerAt (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (η : H1 k.fixingSubgroup (ZMod 2)) :
    h1KerToFixAt anc ρ k hancinj hker (h1FixToKerAt anc ρ k hker η) = η := by
  induction η using QuotientAddGroup.induction_on with
  | H a =>
    rw [show (QuotientAddGroup.mk a : H1 k.fixingSubgroup (ZMod 2))
      = H1ofFun k.fixingSubgroup a.1 from (H1ofFun_of_mem a.2).symm,
      h1FixToKerAt_h1ofFun anc ρ k hker a.2,
      h1KerToFixAt_h1ofFun anc ρ k hancinj hker
        (comp_kerToFixingAt_mem_Z1 anc ρ k hker htriv a.2)]
    exact congrArg _ (funext fun n => congrArg a.1
      (kerToFixingAt_fixingToKerAt anc ρ k hancinj hker n))

/-- `h1KerToFixAt` is additive. -/
theorem h1KerToFixAt_add (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hancind : Topology.IsInducing ⇑anc)
    (ξ η : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    h1KerToFixAt anc ρ k hancinj hker (ξ + η)
      = h1KerToFixAt anc ρ k hancinj hker ξ + h1KerToFixAt anc ρ k hancinj hker η := by
  induction ξ using QuotientAddGroup.induction_on with
  | H a =>
    induction η using QuotientAddGroup.induction_on with
    | H b =>
      show h1KerToFixAt anc ρ k hancinj hker (H1mk _ _ a + H1mk _ _ b)
        = h1KerToFixAt anc ρ k hancinj hker (H1mk _ _ a)
          + h1KerToFixAt anc ρ k hancinj hker (H1mk _ _ b)
      rw [← map_add, ← H1ofFun_of_mem (a + b).2, ← H1ofFun_of_mem a.2, ← H1ofFun_of_mem b.2,
        h1KerToFixAt_h1ofFun anc ρ k hancinj hker (a + b).2,
        h1KerToFixAt_h1ofFun anc ρ k hancinj hker a.2,
        h1KerToFixAt_h1ofFun anc ρ k hancinj hker b.2]
      exact DeepPart.H1ofFun_add
        (comp_fixingToKerAt_mem_Z1 anc ρ k hancinj hker htriv hancind a.2)
        (comp_fixingToKerAt_mem_Z1 anc ρ k hancinj hker htriv hancind b.2)

/-- **The transport equivalence** `H¹(N_K, 𝔽₂) ≃+ H¹(G_k, 𝔽₂)` — `GQ2.h1KerFixEquiv` retyped. -/
noncomputable def h1KerFixEquivAt (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hancind : Topology.IsInducing ⇑anc) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ≃+ H1 k.fixingSubgroup (ZMod 2) where
  toFun := h1KerToFixAt anc ρ k hancinj hker
  invFun := h1FixToKerAt anc ρ k hker
  left_inv := h1FixToKerAt_h1KerToFixAt anc ρ k hancinj hker htriv hancind
  right_inv := h1KerToFixAt_h1FixToKerAt anc ρ k hancinj hker htriv
  map_add' := h1KerToFixAt_add anc ρ k hancinj hker htriv hancind

/-- `h1KerToFixAt` carries anchored deep classes to `k`-deep classes, and conversely: the
`(A, β)`-data transports verbatim, memberships move along `hker`. -/
theorem h1KerToFixAt_mem_deep_iff (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hancind : Topology.IsInducing ⇑anc)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    h1KerToFixAt anc ρ k hancinj hker ξ ∈ LocalKummer.deepClasses k.fixingSubgroup
      ↔ ξ ∈ deepClassesSubgroupAt (kerAnc anc ρ) := by
  constructor
  · rintro ⟨A, β, hd, hsq, hβ0, heq⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    have hZ1 : (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun β (n : GalQ2))
        ∈ Z1 k.fixingSubgroup (ZMod 2) := DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mp hg), b,
      fun g hg => hbfix g ((hker g).mp hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    calc H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
          (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n))
        = h1FixToKerAt anc ρ k hker (H1ofFun k.fixingSubgroup
            (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun β (n : GalQ2))) := by
          rw [h1FixToKerAt_h1ofFun anc ρ k hker hZ1]
          rfl
      _ = h1FixToKerAt anc ρ k hker (h1KerToFixAt anc ρ k hancinj hker ξ) := by rw [heq]
      _ = ξ := h1FixToKerAt_h1KerToFixAt anc ρ k hancinj hker htriv hancind ξ
  · rintro ⟨A, β, hd, hsq, hβ0, rfl⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    have hZ1 := kummerAnc_mem_Z1 (kerAnc anc ρ) hsq hβ0 hAfix
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mpr hg), b,
      fun g hg => hbfix g ((hker g).mpr hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    rw [h1KerToFixAt_h1ofFun anc ρ k hancinj hker hZ1]
    exact congrArg _ (funext fun n => congrArg (Kummer.kummerCocycleFun β)
      (kerAnc_fixingToKerAt anc ρ k hancinj hker n).symm)

/-- The mid-classes version of the transport. -/
theorem h1KerToFixAt_mem_mid_iff (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hancind : Topology.IsInducing ⇑anc)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :
    h1KerToFixAt anc ρ k hancinj hker ξ ∈ midClassesSubgroup k.fixingSubgroup
      ↔ ξ ∈ midClassesSubgroupAt (kerAnc anc ρ) := by
  constructor
  · rintro ⟨A, β, hd, hsq, hβ0, heq⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    have hZ1 : (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun β (n : GalQ2))
        ∈ Z1 k.fixingSubgroup (ZMod 2) := DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mp hg), b,
      fun g hg => hbfix g ((hker g).mp hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    calc H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
          (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n))
        = h1FixToKerAt anc ρ k hker (H1ofFun k.fixingSubgroup
            (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun β (n : GalQ2))) := by
          rw [h1FixToKerAt_h1ofFun anc ρ k hker hZ1]
          rfl
      _ = h1FixToKerAt anc ρ k hker (h1KerToFixAt anc ρ k hancinj hker ξ) := by rw [heq]
      _ = ξ := h1FixToKerAt_h1KerToFixAt anc ρ k hancinj hker htriv hancind ξ
  · rintro ⟨A, β, hd, hsq, hβ0, rfl⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    have hZ1 := kummerAnc_mem_Z1 (kerAnc anc ρ) hsq hβ0 hAfix
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mpr hg), b,
      fun g hg => hbfix g ((hker g).mpr hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    rw [h1KerToFixAt_h1ofFun anc ρ k hancinj hker hZ1]
    exact congrArg _ (funext fun n => congrArg (Kummer.kummerCocycleFun β)
      (kerAnc_fixingToKerAt anc ρ k hancinj hker n).symm)

/-- **The transported structural count** (the (H4) input), in `N_K`-vocabulary:
`#(H¹(N_K) ⧸ Deep) ≤ #Mid` — `GQ2.card_quot_deep_le_card_mid_ker` retyped.  The `k`-side count
`GQ2.card_quot_deep_le_card_mid` (the B13 unit filtration) is consumed verbatim. -/
theorem card_quot_deep_le_card_mid_kerAt [FiniteDimensional ℚ_[2] k]
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))]
    (hancinj : Function.Injective ⇑anc)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hancind : Topology.IsInducing ⇑anc)
    (π : ℚ̄₂) (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_zero : Nat.card (↥(normUnits k) ⧸
      (depthUnits k π 1).subgroupOf (normUnits k)) = 2 ^ f - 1)
    (hcard_gr : ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f) :
    Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸
        deepClassesSubgroupAt (kerAnc anc ρ))
      ≤ Nat.card ↥(midClassesSubgroupAt (kerAnc anc ρ)) := by
  haveI hfinFix : Finite (H1 k.fixingSubgroup (ZMod 2)) :=
    Finite.of_equiv _ (h1KerFixEquivAt anc ρ k hancinj hker htriv hancind).toEquiv
  have hcount := card_quot_deep_le_card_mid k π hπk hπ0 hπ1 hπmax he he_pos hf_pos
    hcard_zero hcard_gr
  -- (a) the ambient cards agree
  have ha : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2)) :=
    Nat.card_congr (h1KerFixEquivAt anc ρ k hancinj hker htriv hancind).toEquiv
  -- (b) the deep subgroups agree (through `coe_kummerDepth_deep`)
  have hb : Nat.card ↥(deepClassesSubgroupAt (kerAnc anc ρ))
      = Nat.card ↥(kummerDepth k π (e + 1)) := by
    refine Nat.card_congr
      ((h1KerFixEquivAt anc ρ k hancinj hker htriv hancind).toEquiv.subtypeEquiv (fun ξ => ?_))
    constructor
    · intro hξ
      have hset := Set.ext_iff.mp (coe_kummerDepth_deep k π hπk hπ0 hπ1 hπmax he_pos he)
        (h1KerToFixAt anc ρ k hancinj hker ξ)
      exact hset.mpr ((h1KerToFixAt_mem_deep_iff anc ρ k hancinj hker htriv hancind ξ).mpr hξ)
    · intro hη
      have hset := Set.ext_iff.mp (coe_kummerDepth_deep k π hπk hπ0 hπ1 hπmax he_pos he)
        (h1KerToFixAt anc ρ k hancinj hker ξ)
      exact (h1KerToFixAt_mem_deep_iff anc ρ k hancinj hker htriv hancind ξ).mp (hset.mp hη)
  -- (c) the mid subgroups agree (through `coe_kummerDepth_mid`)
  have hc : Nat.card ↥(midClassesSubgroupAt (kerAnc anc ρ))
      = Nat.card ↥(kummerDepth k π e) := by
    refine Nat.card_congr
      ((h1KerFixEquivAt anc ρ k hancinj hker htriv hancind).toEquiv.subtypeEquiv (fun ξ => ?_))
    constructor
    · intro hξ
      have hset := Set.ext_iff.mp (coe_kummerDepth_mid k π he)
        (h1KerToFixAt anc ρ k hancinj hker ξ)
      exact hset.mpr ((h1KerToFixAt_mem_mid_iff anc ρ k hancinj hker htriv hancind ξ).mpr hξ)
    · intro hη
      have hset := Set.ext_iff.mp (coe_kummerDepth_mid k π he)
        (h1KerToFixAt anc ρ k hancinj hker ξ)
      exact (h1KerToFixAt_mem_mid_iff anc ρ k hancinj hker htriv hancind ξ).mp (hset.mp hη)
  -- the quotient cards agree by Lagrange + cancellation
  haveI : Nonempty ↥(kummerDepth k π (e + 1)) := ⟨⟨0, zero_mem _⟩⟩
  have hL1 : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸
        deepClassesSubgroupAt (kerAnc anc ρ))
        * Nat.card ↥(deepClassesSubgroupAt (kerAnc anc ρ))
      = Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)) :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm
  have hL2 : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
        * Nat.card ↥(kummerDepth k π (e + 1))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2)) :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm
  have hq : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸
        deepClassesSubgroupAt (kerAnc anc ρ))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1)) := by
    have hmm : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸
          deepClassesSubgroupAt (kerAnc anc ρ))
          * Nat.card ↥(kummerDepth k π (e + 1))
        = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (e + 1)) := by
      rw [← hb, hL1, ha, ← hL2, hb]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmm
  rw [hq, hc]
  exact hcount

end KerFixTransport

/-! ## §7 `hduality` at a general anchored source

`GQ2.hduality_of_data` (`GQ2/DeepCount/Finale.lean` :46) retyped: the instantiation of the
abstract engine `GQ2.card_equivHoms_deep_eq_quot` (`GQ2/DeepDuality.lean` :874 — abstract in
`C`, `M`, `U`, used **verbatim**) at `M := H¹(N_K, 𝔽₂)` with LG2's `conjModule`, `U := V^∨` with
`dualModule`, `Deep := deepClassesSubgroupAt`, `E := midClassesSubgroupAt`, `B := pairingK`.

Every input is a named producer: (H1) LG2's `pairingK_conjModule`, (H2) LG2's `pairingK_nondeg`,
(H3) LG4a's `deepClassesSubgroupAt_le_pairPerp_pairingK`, (H4) the easy half LG4a's
`midClassesSubgroupAt_le_pairPerp_pairingK` plus §6's structural count through
`GQ2.pairPerp_le_of_card_le`, (H5) §5's `conjAct_surjInv_conj_mid_sub_mem_deepAt`. -/

section Duality

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [Finite C]
variable {V : Type} [AddCommGroup V] [DistribMulAction C V] [Finite V]

/-- **`hduality` at a general anchored source** — `GQ2.hduality_of_data` retyped.  Inputs: the
`V^∨` regular-summand package (PJ1's Lemma-6.11 output at `dualModule`), the self-duality
`eU`/`heU` and the dualized inertia `ht₀U` from the §6.17 invariant form, a residue-trivial lift
`g₀ : Γ` of `t₀` (residue-triviality read at the anchored subgroup), and the B13 bundle data for
the splitting field `k` with the pointwise anchored identification `hker`. -/
theorem hduality_of_data_K (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)
    (D : TateDualityG ↥(ρ.toMonoidHom.ker : Subgroup Γ) 2) (hρsurj : Function.Surjective ⇑ρ)
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))]
    (hsimple : ∀ S : AddSubgroup (V →+ ZMod 2),
      (∀ (h : C), ∀ w ∈ S,
        (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h w ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (hnt : Nontrivial (V →+ ZMod 2))
    {Nreg : ℕ} (ι : (V →+ ZMod 2) →+ (Fin Nreg → C → ZMod 2))
    (r : (Fin Nreg → C → ZMod 2) →+ (V →+ ZMod 2))
    (hι : ∀ (h : C) (φ : V →+ ZMod 2) (n : Fin Nreg) (x : C),
      ι ((dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h φ) n x
        = ι φ n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin Nreg → C → ZMod 2),
      r (fun n x => F n (h⁻¹ * x))
        = (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul h (r F))
    (hri : ∀ φ : V →+ ZMod 2, r (ι φ) = φ)
    (eU : (V →+ ZMod 2) ≃+ ((V →+ ZMod 2) →+ ZMod 2))
    (heU : ∀ (c : C) (φ : V →+ ZMod 2),
      letI : DistribMulAction C (V →+ ZMod 2) := dualModule
      eU ((dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul c φ)
        = (dualModule : DistribMulAction C ((V →+ ZMod 2) →+ ZMod 2)).toSMul.smul c (eU φ))
    (t₀ : C)
    (ht₀U : ∃ φ : V →+ ZMod 2,
      (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul t₀ φ ≠ φ)
    (g₀ : Γ) (hg₀ : ρ g₀ = t₀)
    (hg₀rt : IsResidueTrivial (ancSubgroup (kerAnc anc ρ)) (anc g₀))
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (hancinj : Function.Injective ⇑anc) (hancind : Topology.IsInducing ⇑anc)
    (π : ℚ̄₂) (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_zero : Nat.card (↥(normUnits k) ⧸
      (depthUnits k π 1).subgroupOf (normUnits k)) = 2 ^ f - 1)
    (hcard_gr : ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f) :
    letI := conjModuleDeepK anc ρ hρsurj
    letI := conjModuleQuotK anc ρ hρsurj
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    Nat.card ↥(equivHoms C (V →+ ZMod 2) ↥(deepClassesSubgroupAt (kerAnc anc ρ)))
      = Nat.card ↥(equivHoms C (V →+ ZMod 2)
          (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) ⧸
            deepClassesSubgroupAt (kerAnc anc ρ))) := by
  letI := conjModule ρ hρsurj
  letI instDeepI := conjModuleDeepK anc ρ hρsurj
  letI instQI := conjModuleQuotK anc ρ hρsurj
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  haveI : Finite (V →+ ZMod 2) :=
    Finite.of_injective (DFunLike.coe : (V →+ ZMod 2) → (V → ZMod 2)) DFunLike.coe_injective
  have h2M : ∀ m : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2), m + m = 0 :=
    fun m => h1_zmodTwo_add_self_dp m
  have h2U : ∀ φ : V →+ ZMod 2, φ + φ = 0 := fun φ => FoxH.ElemDual.add_self_eq_zero φ
  have hsharp : pairPerp (pairingK ρ D) (deepClassesSubgroupAt (kerAnc anc ρ))
      ≤ midClassesSubgroupAt (kerAnc anc ρ) :=
    pairPerp_le_of_card_le (pairingK ρ D) h2M (pairingK_nondeg ρ D)
      (midClassesSubgroupAt_le_pairPerp_pairingK anc ρ D k htriv hker)
      (card_quot_deep_le_card_mid_kerAt anc ρ k hancinj hker htriv hancind π hπk hπ0 hπ1 hπmax
        he he_pos hf_pos hcard_zero hcard_gr)
  exact card_equivHoms_deep_eq_quot (C := C) h2M h2U hsimple hnt ι r hι hr hri eU heU t₀
    ht₀U (pairingK ρ D) (fun c x y => pairingK_conjModule ρ D hρsurj c x y) (pairingK_nondeg ρ D)
    (deepClassesSubgroupAt (kerAnc anc ρ)) (midClassesSubgroupAt (kerAnc anc ρ))
    (fun c x hx => conjAct_deepClassesAt anc ρ (Function.surjInv hρsurj c) hx)
    (deepClassesSubgroupAt_le_pairPerp_pairingK anc ρ D k htriv hker)
    hsharp
    (fun d x hx => conjAct_surjInv_conj_mid_sub_mem_deepAt anc ρ hρsurj hg₀ hg₀rt d hx)
    (instDeep := instDeepI)
    (fun c x => rfl)
    (instQ := instQI)
    (fun c m => (conjActQuotHomK_mk anc ρ (Function.surjInv hρsurj c) m).symm)

end Duality

/-! ## §8 The dimension lane: `#X₊² = #H¹` over a general local source

`GQ2.DimAssembly.lemma_6_17_dim_of_hext_hduality` / `lemma_6_17_dim_of_hduality` /
`GQ2.DimClose.lemma_6_17_dim_of_residueLift` / `GQ2.ResidueLift.lemma_6_17_dim_final`, collapsed
into one theorem at the general tame parameter `q_K = 2^f`.

Against the `ℚ₂` chain:

* the `ℚ₂` `hext` discharge (`ShapiroExtend.familiesExtend_of_package` at the `V`-side
  Lemma-6.11 package) is §1's `familiesExtendK_of_package` at PJ1's
  `lemma_6_11_of_tame_pair_pow`;
* the `ℚ₂` `hinf` discharge (`inflationVanishes_ramifiedTame`, `q = 2`) is LG4a's
  `inflationVanishes_ramifiedTameQ` at every `q_K = 2^f`;
* the `ℚ₂` **splitting-field construction** (`ResidueLift.splitField` +
  `fixingSubgroup_splitField`) and the **residue-trivial tame lift**
  (`exists_residueTrivial_tameLift`) are `(k, hker, htriv)` and `(g₀, hg₀, hg₀rt)`, **threaded**
  — see the module docstring's `ResidueLift` decision;
* the `V^∨`-side self-duality bricks (`dualSelfDual`, `dualSelfDual_equivariant`,
  `exists_dualModule_smul_ne`) and the `𝔽₂`-dual transport (`DimAssembly.dual_*`) are
  ambient-free and are consumed **verbatim**. -/

section DimLane

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

open DimAssembly in
/-- **The §6.3 deep-half dimension identity at a general local source**:
`#X₊² = #H¹(Γ, V)` — `GQ2.ResidueLift.lemma_6_17_dim_final` retyped to a general anchored
source at every tame parameter `q_K = 2^f`.

The three `ℚ₂`-specific derivations are threaded, per the module docstring: the splitting-field
data `(k, htriv, hker)`, the residue-trivial tame lift `(g₀, hg₀, hg₀rt)`, and the anchor's
injectivity/inducingness `(hancinj, hancind)` — all free at `Γ = ↥U`, `anc = U.subtype`. -/
theorem lemma_6_17_dim_final_K {f : ℕ} (hf : 1 ≤ f)
    (anc : ContinuousMonoidHom Γ GalQ2)
    (c : ContinuousMonoidHom (Tq (2 ^ f)) C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom Γ C)
    (D : TateDualityG ↥(ρ.toMonoidHom.ker : Subgroup Γ) 2)
    (hρsurj : Function.Surjective ⇑ρ)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c (tqTau (2 ^ f)) • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))]
    (g₀ : Γ) (hg₀ : ρ g₀ = c (tqTau (2 ^ f)))
    (hg₀rt : IsResidueTrivial (ancSubgroup (kerAnc anc ρ)) (anc g₀))
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (hancinj : Function.Injective ⇑anc) (hancind : Topology.IsInducing ⇑anc) :
    Nat.card (deepPartK (V := V) anc ρ) ^ 2 = Nat.card (H1 Γ V) := by
  classical
  have hgen : Subgroup.closure {c (tqSigma (2 ^ f)), c (tqTau (2 ^ f))} = ⊤ :=
    gen_tq_quotient c.toMonoidHom c.continuous_toFun hc
  have hrel : (c (tqSigma (2 ^ f)))⁻¹ * c (tqTau (2 ^ f)) * c (tqSigma (2 ^ f))
      = c (tqTau (2 ^ f)) ^ 2 ^ f := tame_rel_map_q c.toMonoidHom
  -- (a) the inflation input, at every `q_K = 2^f` (LG4a §5A, coprime averaging)
  have hinf : InflationVanishesK (V := V) ρ :=
    inflationVanishes_ramifiedTameQ hf ρ c hρ hV2 hρsurj hgen hsimple hram
  -- (b) the extension input: §1 at the `V`-side Lemma-6.11 package (PJ1)
  obtain ⟨NregV, ιV, rV, hιV, hrV, hriV⟩ :=
    lemma_6_11_of_tame_pair_pow (V := V) hf hgen hrel hV2 hfaith hsimple hram
  have hext : FamiliesExtendK (V := V) ρ :=
    familiesExtendK_of_package hρ hρsurj ιV rV hιV hrV hriV
  -- (c) the `V^∨` regular-summand package and the self-duality data
  haveI : Finite (V →+ ZMod 2) := Finite.of_injective _ DFunLike.coe_injective
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  have hV2D : ∀ φ : V →+ ZMod 2, φ + φ = 0 := fun φ => FoxH.ElemDual.add_self_eq_zero φ
  have hfaithD : ∀ h : C, (∀ φ : V →+ ZMod 2, h • φ = φ) → h = 1 := fun h hh =>
    dual_faithful hV2 hfaith h fun φ v => congrArg (fun ψ : V →+ ZMod 2 => ψ v) (hh φ)
  have hsimpleD : ∀ W : AddSubgroup (V →+ ZMod 2),
      (∀ (h : C), ∀ φ ∈ W, h • φ ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    dual_simple hV2 hsimple W fun h φ hφ => hW h φ hφ
  have hramD : ∃ φ : V →+ ZMod 2, c (tqTau (2 ^ f)) • φ ≠ φ := by
    obtain ⟨φ, v, hφv⟩ := dual_ram hV2 hram
    exact ⟨φ, fun heq => hφv (congrArg (fun ψ : V →+ ZMod 2 => ψ v) heq)⟩
  have hnt : Nontrivial (V →+ ZMod 2) := by
    obtain ⟨φ, hφ⟩ := hramD
    exact ⟨c (tqTau (2 ^ f)) • φ, φ, hφ⟩
  obtain ⟨Nreg, ι, r, hι, hr, hri⟩ :=
    lemma_6_11_of_tame_pair_pow (V := V →+ ZMod 2) hf hgen hrel hV2D hfaithD hsimpleD hramD
  -- (d) the duality, from §7
  have hduality := hduality_of_data_K (V := V) anc ρ D hρsurj hsimpleD hnt ι r hι hr hri
    (dualSelfDual q hq hns hV2) (fun cc φ => dualSelfDual_equivariant q hq hns hV2 hinv cc φ)
    (c (tqTau (2 ^ f))) (exists_dualModule_smul_ne hV2 (c (tqTau (2 ^ f))) hram)
    g₀ hg₀ hg₀rt k htriv hker hancinj hancind
    (dyadicUnitFiltration k).π (dyadicUnitFiltration k).hπ_mem (dyadicUnitFiltration k).hπ_ne
    (dyadicUnitFiltration k).hπ_lt (dyadicUnitFiltration k).hπ_max
    (dyadicUnitFiltration k).he (dyadicUnitFiltration k).he_pos (dyadicUnitFiltration k).hf_pos
    (dyadicUnitFiltration k).card_gr_zero (dyadicUnitFiltration k).card_gr
  -- (e) the §4 collapse
  exact card_deepPartK_sq_of_duality anc ρ hρ hV2 hρsurj hinf hext ι r hι hr hri hduality

end DimLane

/-! ## §9 The join: the Lagrangian Arf count

`GQ2.DeepPart.card_Q0loc_zero_eq_of_dim_of_vanish` (`GQ2/DeepPart/Q0locLayer.lean` :547) retyped,
in the exact shape LG4a's §8 docstring fixes: the two changes against the `ℚ₂` model are
`2*m ↦ 2*(m*n)` in the count and LG2a's Euler theorem replacing the `B7` calls
(`finite_H1`/`card_H1_eq_card_of_simple`), which is why `hcard` is stated at `H¹` rather than at
`V`.  The body is `zeroCount_of_arf_zero` applied to LG4a's `arf_Q0loc_zero_of_deep`. -/

section Join

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

/-- **Packet Prop. 6.12 + Prop. 6.14 at a general local source**: given the dimension clause
`#X₊² = #H¹` and the vanishing clause `Q⁰_loc|X₊ = 0`, the deep half is a Lagrangian for the
base determinant form, so its Arf invariant vanishes and the zero-count carries the **positive**
Gauss sign

`#(Q⁰_loc)⁻¹(0) = 2^{2mn−1} + 2^{mn−1}`.

Retype of `GQ2.DeepPart.card_Q0loc_zero_eq_of_dim_of_vanish`; the `ℚ₂` model's `B7` Euler input
(`hρsurj`/`hsimple`/`h₀`/`hmoves` feeding `card_H1_eq_card_of_simple`) is replaced by the direct
`hcard` at `H¹`, which LG2a's `localEulerCharacteristic_open` supplies over `G_K` (LG3's
`card_H1_eq_two_pow_of_euler`). -/
theorem card_Q0loc_zero_eq_of_dim_of_vanish_K (D : TateDualityG Γ 2)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (hinv : ∀ (c : C) (v : V), q (c • v) = q v)
    (hV2 : ∀ v : V, v + v = 0)
    (hdim : Nat.card (deepPartK (V := V) anc ρ) ^ 2 = Nat.card (H1 Γ V))
    (hvanish : Q0locVanishesOnDeep D dat anc ρ)
    (m n : ℕ) (hmn : 1 ≤ m * n) (hcard : Nat.card (H1 Γ V) = 2 ^ (2 * (m * n))) :
    Nat.card {x : H1 Γ V // Q0loc D dat ρ x = 0}
      = 2 ^ (2 * (m * n) - 1) + 2 ^ (m * n - 1) := by
  haveI hfin : Finite (H1 Γ V) := (Nat.card_ne_zero.mp (by rw [hcard]; positivity)).2
  haveI : Fintype (H1 Γ V) := Fintype.ofFinite _
  have hqG : ∀ (g : Γ) (v : V), q (g • v) = q v := fun g v => by rw [hρ]; exact hinv _ v
  have hq' := isQuadraticFp2_Q0loc D q hq dat hdat ρ hρ hqG
  have hns' := nonsingular_Q0loc D q hq hns hV2 dat hdat ρ hρ hqG
  have harf : arf (Q0loc D dat ρ (V := V)) = 0 :=
    arf_Q0loc_zero_of_deep D q hq hns dat hdat anc ρ hρ hinv hV2 hfin hdim hvanish
  have hcnt := zeroCount_of_arf_zero (Q0loc D dat ρ (V := V)) hq' hns' hmn
    (by rw [← Nat.card_eq_fintype_card]; exact hcard) harf
  simpa only [zeroCount] using hcnt

end Join

/-! ## §10 The endpoint: packet Prop. 6.18 / eq. (115), ramified case

Packaged over F1's `FieldParameters` and the open subgroup `U ≤ G_ℚ₂` exactly as LG3's
`prop_6_18_unramified_K` (`GQ2/Dyadic/LocalGauss/Unramified.lean`), with the AX3/AX4 field-side
interface threaded as the same three explicit binders `tameFK`, `htameFK`, `hfac` (board rule:
no census change until the AX flip).

The Euler input is discharged here from LG2a (`localEulerCharacteristic_open`) plus LG3's two
collapse clauses; the deep-package inputs are the dimension clause `hdim` (§8 below discharges
it from the `(k, hker)` + residue-lift data) and the vanishing clause `hvanish` in LG4a's
`Q0locVanishesOnDeep` shape, which LG4c's `lemma_6_17_vanish_final_K` produces. -/

section Endpoint

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

omit [Finite C] in
/-- **Packet Prop. 6.18 / eq. (115) over a finite extension `K/ℚ₂`, ramified case** (the LG5
entry point, ramified half).

For `G_K = ↥U` open of finite index `n = [K : ℚ₂]` in `G_ℚ₂`, a **ramified** marking
`c : T_{q_K} ↠ C` of a simple faithful `𝔽₂[C]`-module `V` with `#V = 2^{2m}`, the base
determinant form `Q⁰` on `H¹(G_K, V)` has the **positive** Gauss sign at every degree:

  `#(Q⁰)⁻¹(0) = 2^{2mn−1} + 2^{mn−1}`,  i.e. sign `+2^{n·dim V/2}`.

Mirrors `GQ2.DetRamified.prop_6_18_ramified` (`GQ2/DetRamified.lean` :53) with `m ↦ m*n`.  The
two §6.3 Kummer cores enter as the binders `hdim` (dimension clause; §8's
`lemma_6_17_dim_final_K` discharges it) and `hvanish` (vanishing clause, in LG4a's exported
shape; LG4c's `lemma_6_17_vanish_final_K` discharges it). -/
theorem prop_6_18_ramified_K (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] (hindex : U.index = P.n)
    [DistribMulAction ↥U (ZMod 2)] [ContinuousSMul ↥U (ZMod 2)]
    [DistribMulAction ↥U (MuN 2)] [ContinuousSMul ↥U (MuN 2)]
    {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
    [DistribMulAction ↥U V] [ContinuousSMul ↥U V] [DistribMulAction C V]
    (D : TateDualityG ↥U 2)
    (tameFK : ContinuousMonoidHom ↥U (Tq P.qK)) (htameFK : Function.Surjective ⇑tameFK)
    (c : ContinuousMonoidHom (Tq P.qK) C) (hc : Function.Surjective ⇑c)
    (anc : ContinuousMonoidHom ↥U GalQ2)
    (ρ : ContinuousMonoidHom ↥U C) (hfac : ∀ g, ρ g = c (tameFK g))
    (hρ : ∀ (g : ↥U) (v : V), g • v = ρ g • v)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (hdim : Nat.card (deepPartK (V := V) anc ρ) ^ 2 = Nat.card (H1 ↥U V))
    (hvanish : Q0locVanishesOnDeep D dat anc ρ)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    Nat.card {x : H1 ↥U V // Q0loc D dat ρ x = 0}
      = 2 ^ (2 * (m * P.n) - 1) + 2 ^ (m * P.n - 1) := by
  classical
  have hV2 : ∀ v : V, v + v = 0 := DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  have hqG : ∀ (g : ↥U) (v : V), q (g • v) = q v := fun g v => by rw [hρ]; exact hinv _ v
  have hρsurj : Function.Surjective ⇑ρ := by
    intro y
    obtain ⟨t, ht⟩ := hc y
    obtain ⟨g, hg⟩ := htameFK t
    exact ⟨g, by rw [hfac, hg, ht]⟩
  haveI hVnt : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    calc (1 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨h₀, hmoves⟩ := exists_smul_neK hsimple (exists_ne (0 : V)) hV2 m hm hcard
  have hH0 : Nat.card (H0 ↥U V) = 1 :=
    card_H0_eq_one_of_surjectiveK ρ.toMonoidHom hρsurj hρ hsimple h₀ hmoves
  have hH2 : Nat.card (H2 ↥U V) = 1 :=
    card_H2_eq_one_of_card_H0_eq_oneK V D q hq hns hV2 hqG
      (localEulerCharacteristic_open U hU V).2.2.1 hH0
  have hEuler : Nat.card (H1 ↥U V) = 2 ^ (2 * (m * P.n)) :=
    card_H1_eq_two_pow_of_euler U hU V hH0 hH2 m P.n hindex hcard
  have hmn : 1 ≤ m * P.n :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by have := P.one_le_n; omega))
  exact card_Q0loc_zero_eq_of_dim_of_vanish_K D q hq hns dat hdat anc ρ hρ
    (fun cc v => hinv cc v) hV2 hdim hvanish m P.n hmn hEuler

end Endpoint

end GQ2.Dyadic
