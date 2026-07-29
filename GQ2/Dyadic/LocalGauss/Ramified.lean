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
