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

omit [DiscreteTopology C] [Finite C] in
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

omit [DiscreteTopology C] [Finite C] in
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

omit [DiscreteTopology C] [Finite C] in
/-- On the kernel, at the base point `x = 1`, the word is the element itself. -/
theorem shapiroWordK_ker_one (n₀ : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    shapiroWordK ρ hρsurj (n₀ : Γ) 1 = n₀ := by
  apply Subtype.ext
  show (sec1K ρ hρsurj 1)⁻¹ * (n₀ : Γ) * sec1K ρ hρsurj ((ρ n₀)⁻¹ * 1) = (n₀ : Γ)
  have h1 : ρ (n₀ : Γ) = 1 := n₀.2
  rw [h1, inv_one, one_mul, sec1K_one, inv_one, one_mul, mul_one]

omit [Finite C] in
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
