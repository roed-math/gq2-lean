/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-!
# The generator reduction for lower-central bounds, at arbitrary depth, in any group

W63-FOUR proved `GradedStageFour.le_of_gens_three`: if `K` is normalised by `closure S` and
contains the weight-three bracket of every triple of GENERATORS, then
`[[closure S, closure S], closure S] <= K`.  Its closing recommendation was that this be lifted
out for general use, because every lattice bound in this tree otherwise runs
`Subgroup.commutator_le` twice and so has to name a subgroup containing the intermediate image.

This file is that lift.  It sits on `Mathlib` alone - no campaign import - so any file in the
tree may use it, and it generalises the committed statement in two directions.

## ⭐⭐⭐ Headline 1: ARBITRARY DEPTH

⭐⭐⭐ `LcsGens.lcsSeries_le_of_gens`: let `K` be normalised by `S` and let `n >= 1`.  If `K`
contains every LEFT-NORMED bracket `[...[[s_0, s_1], s_2] ..., s_n]` of `n + 1` generators, then
the `n`-th term of the descending series `lcsSeries (closure S)` lies in `K`.

The committed depth-two statement is the case `n = 2` (`LcsGens.le_of_gens_three`), and the tree
also owns depth-three bounds (`GradedFiveForce.forceLcs_three_le_forceN4`,
`GradedFiveNecessity.forceLcs_three_le_gaFourSub`, `forceLcs_three_le_fiveEvenN`), which the
committed form could not reach at all.  The induction runs on the SAME middle term `commAll`,
carried as the new `K` rather than as a one-off.

## ⭐⭐ Headline 2: TWO INDEPENDENT GENERATING SETS AT DEPTH ONE

⭐⭐ `LcsGens.commutator_closure_le`: `[closure S, closure T] <= K` as soon as `S` and `T` both
normalise `K` and `[s, t] in K` for generators.  This is the reduction the depth-`n` induction is
built on and is the one most likely to be wanted on its own; nothing in the tree had it.  It is
INCOMPARABLE with `Subgroup.commutator_le`, which quantifies over the closures but asks for no
normalisation: the proof here is `Subgroup.commutator_le.mpr` applied to a generator argument.

## ⚠ Two honest limits, both load-bearing

⚠ **Normalisation cannot be dropped and it is normalisation by the IMAGE.**  Both reductions
need `{g : [p, g] in K}` to be a subgroup, and the identities
`[p, u v] = [p, u] * (u [p, v] u⁻¹)`, `[p q, u] = (p [q, u] p⁻¹) * [p, u]` supply that only when
the conjugating element normalises `K`.  W63-FOUR measured the cost of relaxing it
(`scripts/w63_four/results/normal_chain.txt`): the smallest subgroup normal in the whole carrier
containing the same brackets is four times too big, and no certificate survives on it.

⚠ **LEFT-normed only.**  `lcsGensSet` brackets on the right, matching
`lcsSeries H (n+1) = [lcsSeries H n, H]` and the tree's `forceLcs`.  The right-normed variant is
NOT a consequence of this file.

## Relation to Mathlib

`Subgroup.le_set_normalizer_iff` (`Mathlib/Algebra/Group/Subgroup/Basic.lean`) already provides
`GradedStageFour.subset_normalizer_of_conj`, which is therefore a duplicate and is not restated
here; this file uses the Mathlib lemma.  `Subgroup.commutator_le` and the Three Subgroups Lemma
are the nearest Mathlib results, and neither reduces a commutator of CLOSURES to its generators.
The `commLeft`/`commRight`/`commAll` subgroups are stated here in the `LcsGens` namespace and are
the natural mathlib-shaped API for that gap.

## Contents

* **1** the three auxiliary subgroups and the two one-sided reductions;
* **2** ⭐⭐ the depth-one reduction with two generating sets;
* **3** ⭐⭐⭐ the left-normed generator brackets and the depth-`n` reduction;
* **4** the committed depth-two statement, recovered; **5** axiom pins.

## Axiom hygiene

No `sorry`, no new axiom, no `decide`, no `native_decide`.
-/

open scoped commutatorElement

namespace GQ2

namespace Dyadic

namespace SqCore

namespace LcsGens

variable {G : Type*} [Group G] {K H : Subgroup G} {S T : Set G}

/-! ## 1 The auxiliary subgroups and the one-sided reductions -/

section Aux

/-- `{g normalising K : [g, t] in K}`.  A subgroup, because
`[p * q, t] = (p * [q, t] * p⁻¹) * [p, t]` and `p` normalises `K`. -/
def commLeft (K : Subgroup G) (t : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧ ⁅g, t⁆ ∈ K}
  mul_mem' := by
    rintro p q ⟨hp, hpt⟩ ⟨hq, hqt⟩
    refine ⟨mul_mem hp hq, ?_⟩
    have hid : ⁅p * q, t⁆ = p * ⁅q, t⁆ * p⁻¹ * ⁅p, t⁆ := by group
    exact hid ▸ mul_mem ((Subgroup.mem_normalizer_iff.mp hp _).mp hqt) hpt
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := by
    rintro p ⟨hp, hpt⟩
    refine ⟨inv_mem hp, ?_⟩
    have hid : ⁅p⁻¹, t⁆ = p⁻¹ * ⁅p, t⁆⁻¹ * p⁻¹⁻¹ := by group
    exact hid ▸ (Subgroup.mem_normalizer_iff.mp (inv_mem hp) _).mp (inv_mem hpt)

theorem mem_commLeft {t g : G} :
    g ∈ commLeft K t ↔ g ∈ Subgroup.normalizer (K : Set G) ∧ ⁅g, t⁆ ∈ K := Iff.rfl

/-- `{g normalising K : [p, g] in K}`.  A subgroup, because
`[p, u * v] = [p, u] * (u * [p, v] * u⁻¹)` and `u` normalises `K`. -/
def commRight (K : Subgroup G) (p : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧ ⁅p, g⁆ ∈ K}
  mul_mem' := by
    rintro u v ⟨hu, hpu⟩ ⟨hv, hpv⟩
    refine ⟨mul_mem hu hv, ?_⟩
    have hid : ⁅p, u * v⁆ = ⁅p, u⁆ * (u * ⁅p, v⁆ * u⁻¹) := by group
    exact hid ▸ mul_mem hpu ((Subgroup.mem_normalizer_iff.mp hu _).mp hpv)
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
  inv_mem' := by
    rintro u ⟨hu, hpu⟩
    refine ⟨inv_mem hu, ?_⟩
    have hid : ⁅p, u⁻¹⁆ = u⁻¹ * ⁅p, u⁆⁻¹ * u⁻¹⁻¹ := by group
    exact hid ▸ (Subgroup.mem_normalizer_iff.mp (inv_mem hu) _).mp (inv_mem hpu)

theorem mem_commRight {p g : G} :
    g ∈ commRight K p ↔ g ∈ Subgroup.normalizer (K : Set G) ∧ ⁅p, g⁆ ∈ K := Iff.rfl

/-- ⭐ **Reduction on the right**: a commutator into a subgroup normalised by `closure S` need
only be tested against the generators `S`. -/
theorem commutator_mem_of_gens_right
    (hS : S ⊆ Subgroup.normalizer (K : Set G)) {p : G}
    (hp : ∀ t ∈ S, ⁅p, t⁆ ∈ K) {u : G} (hu : u ∈ Subgroup.closure S) :
    ⁅p, u⁆ ∈ K :=
  (mem_commRight.mp
    ((Subgroup.closure_le (commRight K p)).mpr
      (fun t ht => mem_commRight.mpr ⟨hS ht, hp t ht⟩) hu)).2

/-- ⭐ **Reduction on the left**: …and only against the generators on the left as well. -/
theorem commutator_mem_of_gens_left
    (hS : S ⊆ Subgroup.normalizer (K : Set G)) {t : G}
    (ht : ∀ s ∈ S, ⁅s, t⁆ ∈ K) {p : G} (hp : p ∈ Subgroup.closure S) :
    ⁅p, t⁆ ∈ K :=
  (mem_commLeft.mp
    ((Subgroup.closure_le (commLeft K t)).mpr
      (fun s hs => mem_commLeft.mpr ⟨hS hs, ht s hs⟩) hp)).2

/-- `{p normalising K : [p, u] in K for every u in H}`: where the middle term of the chain has
to land, and, in the depth-`n` induction, the subgroup that plays the role of `K` one step up. -/
def commAll (K H : Subgroup G) : Subgroup G where
  carrier := {p | p ∈ Subgroup.normalizer (K : Set G) ∧ ∀ u ∈ H, ⁅p, u⁆ ∈ K}
  mul_mem' := by
    rintro p q ⟨hp, hpu⟩ ⟨hq, hqu⟩
    refine ⟨mul_mem hp hq, fun u hu => ?_⟩
    have hid : ⁅p * q, u⁆ = p * ⁅q, u⁆ * p⁻¹ * ⁅p, u⁆ := by group
    exact hid ▸ mul_mem ((Subgroup.mem_normalizer_iff.mp hp _).mp (hqu u hu)) (hpu u hu)
  one_mem' := ⟨one_mem _, fun u _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := by
    rintro p ⟨hp, hpu⟩
    refine ⟨inv_mem hp, fun u hu => ?_⟩
    have hid : ⁅p⁻¹, u⁆ = p⁻¹ * ⁅p, u⁆⁻¹ * p⁻¹⁻¹ := by group
    exact hid ▸ (Subgroup.mem_normalizer_iff.mp (inv_mem hp) _).mp (inv_mem (hpu u hu))

theorem mem_commAll {p : G} :
    p ∈ commAll K H ↔ p ∈ Subgroup.normalizer (K : Set G) ∧ ∀ u ∈ H, ⁅p, u⁆ ∈ K :=
  Iff.rfl

/-- `commAll K H` is normalised by `H` as soon as `K` is: the conjugation passes through both
arguments, `[r x r⁻¹, u] = r * [x, r⁻¹ u r] * r⁻¹`.  Mathlib's `le_set_normalizer_iff` supplies
the upgrade from conjugation-stability to membership of the normaliser. -/
theorem le_normalizer_commAll
    (hH : (H : Set G) ⊆ Subgroup.normalizer (K : Set G)) :
    (H : Set G) ⊆ Subgroup.normalizer ((commAll K H : Subgroup G) : Set G) := by
  refine Subgroup.le_set_normalizer_iff.mpr fun r hr x hx => ?_
  obtain ⟨hxn, hxu⟩ := mem_commAll.mp hx
  refine mem_commAll.mpr ⟨mul_mem (mul_mem (hH hr) hxn) (inv_mem (hH hr)), fun u hu => ?_⟩
  have hid : ⁅r * x * r⁻¹, u⁆ = r * ⁅x, r⁻¹ * u * r⁆ * r⁻¹ := by group
  exact hid ▸ (Subgroup.mem_normalizer_iff.mp (hH hr) _).mp
    (hxu _ (mul_mem (mul_mem (inv_mem hr) hu) hr))

end Aux

/-! ## 2 The depth-one reduction, with two generating sets -/

section DepthOne

/-- ⭐⭐ **The commutator of two closures, tested on generators.**  INCOMPARABLE with
`Subgroup.commutator_le`, which quantifies over the closures but asks for no normalisation: this
one tests generators, at the price that both generating sets must normalise `K`.  The proof is
`Subgroup.commutator_le.mpr` applied to a generator argument. -/
theorem commutator_closure_le
    (hS : S ⊆ Subgroup.normalizer (K : Set G)) (hT : T ⊆ Subgroup.normalizer (K : Set G))
    (hst : ∀ s ∈ S, ∀ t ∈ T, ⁅s, t⁆ ∈ K) :
    ⁅Subgroup.closure S, Subgroup.closure T⁆ ≤ K :=
  Subgroup.commutator_le.mpr fun _ hp _ hq =>
    commutator_mem_of_gens_right hT
      (fun t ht => commutator_mem_of_gens_left hS (fun s hs => hst s hs t ht) hp) hq

end DepthOne

/-! ## 3 The left-normed generator brackets, and the depth-`n` reduction -/

section DepthN

/-- The set of LEFT-NORMED brackets of `n + 1` generators:
`lcsGensSet S 0 = S` and `lcsGensSet S (n+1) = {[p, s] : p in lcsGensSet S n, s in S}`. -/
def lcsGensSet (S : Set G) : ℕ → Set G
  | 0 => S
  | n + 1 => {x | ∃ p ∈ lcsGensSet S n, ∃ s ∈ S, ⁅p, s⁆ = x}

/-- The descending series `H`, `[H, H]`, `[[H, H], H]`, … in any group; the tree's
`GradedFiveForce.forceLcs` is this at `G = SqU6 gr3R`. -/
def lcsSeries (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅lcsSeries H n, H⁆

@[simp] theorem lcsSeries_zero (H : Subgroup G) : lcsSeries H 0 = H := rfl

@[simp] theorem lcsSeries_succ (H : Subgroup G) (n : ℕ) :
    lcsSeries H (n + 1) = ⁅lcsSeries H n, H⁆ := rfl

/-- Every left-normed bracket of generators lies in the closure. -/
theorem lcsGensSet_subset_closure (S : Set G) :
    ∀ n, lcsGensSet S n ⊆ (Subgroup.closure S : Set G)
  | 0 => Subgroup.subset_closure
  | n + 1 => by
    rintro _ ⟨p, hp, s, hs, rfl⟩
    have hp' : p ∈ Subgroup.closure S := lcsGensSet_subset_closure S n hp
    have hs' : s ∈ Subgroup.closure S := Subgroup.subset_closure hs
    show ⁅p, s⁆ ∈ Subgroup.closure S
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp' hs') (inv_mem hp')) (inv_mem hs')

/-- ⭐⭐⭐ **THE GENERATOR REDUCTION AT ARBITRARY DEPTH.**  If `K` is normalised by `S` and
contains every left-normed bracket of `n + 2` generators, then it contains the `(n+1)`-st term
of the descending series of `closure S`.

The hypothesis tests only brackets of GENERATORS, and `K` is an arbitrary subgroup normalised by
`S`; no finiteness of `S` is assumed anywhere.  The induction does name an intermediate subgroup,
`D := commAll K H`, and carries it as the new `K` at the next depth. -/
theorem lcsSeries_le_of_gens (S : Set G) :
    ∀ (n : ℕ) (K : Subgroup G), S ⊆ Subgroup.normalizer (K : Set G) →
      lcsGensSet S (n + 1) ⊆ (K : Set G) → lcsSeries (Subgroup.closure S) (n + 1) ≤ K := by
  intro n
  induction n with
  | zero =>
      intro K hSK hbr
      exact commutator_closure_le hSK hSK fun s hs t ht => hbr ⟨s, hs, t, ht, rfl⟩
  | succ n ih =>
      intro K hSK hbr
      set H := Subgroup.closure S with hH
      have hHn : (H : Set G) ⊆ Subgroup.normalizer (K : Set G) := by
        rw [hH]; exact fun x hx => (Subgroup.closure_le _).mpr hSK hx
      set D := commAll K H with hD
      have hSD : S ⊆ Subgroup.normalizer ((D : Subgroup G) : Set G) := fun s hs =>
        le_normalizer_commAll hHn (Subgroup.subset_closure hs)
      have hbrD : lcsGensSet S (n + 1) ⊆ (D : Set G) := by
        intro p hp
        refine mem_commAll.mpr ⟨hHn (lcsGensSet_subset_closure S (n + 1) hp), fun u hu => ?_⟩
        exact commutator_mem_of_gens_right hSK (fun t ht => hbr ⟨p, hp, t, ht, rfl⟩) hu
      have hmid : lcsSeries H (n + 1) ≤ D := ih D hSD hbrD
      exact Subgroup.commutator_le.mpr fun p hp u hu => (mem_commAll.mp (hmid hp)).2 u hu

/-! ### The reduction is EXACT -/

/-- Each term of the descending series is stable under conjugation by `H`. -/
theorem lcsSeries_map_conj_le (H : Subgroup G) {g : G} (hg : g ∈ H) :
    ∀ n, (lcsSeries H n).map (MulAut.conj g).toMonoidHom ≤ lcsSeries H n := by
  have hH : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hg hx) (inv_mem hg)
  intro n
  induction n with
  | zero => exact hH
  | succ n ih =>
      rw [lcsSeries_succ, Subgroup.map_commutator]
      exact Subgroup.commutator_mono ih hH

/-- …hence `H` normalises it. -/
theorem le_normalizer_lcsSeries (H : Subgroup G) (n : ℕ) :
    (H : Set G) ⊆ Subgroup.normalizer ((lcsSeries H n : Subgroup G) : Set G) := by
  refine Subgroup.le_set_normalizer_iff.mpr fun g hg x hx => ?_
  exact lcsSeries_map_conj_le H hg n ⟨x, hx, by simp [MulAut.conj_apply]⟩

/-- …and it contains the left-normed generator brackets of its own weight. -/
theorem lcsGensSet_subset_lcsSeries (S : Set G) :
    ∀ n, lcsGensSet S n ⊆ (lcsSeries (Subgroup.closure S) n : Set G)
  | 0 => Subgroup.subset_closure
  | n + 1 => by
      rintro _ ⟨p, hp, s, hs, rfl⟩
      exact Subgroup.commutator_mem_commutator (lcsGensSet_subset_lcsSeries S n hp)
        (Subgroup.subset_closure hs)

/-- ⭐⭐⭐ **THE GENERATOR REDUCTION LOSES NOTHING.**  Among subgroups normalised by `S`, the
bracket condition is not merely SUFFICIENT for containing the series term: it is EQUIVALENT to
it.  So the series term is the LEAST admissible target, and the reduction computes the
achievable lattice rather than relaxing it.

W63-FOUR's `GradedStageFour` docstring asserts this in prose - "turns the achievable lattice
from a relaxation into an exact object" - and proves only the sufficient half.  This is the
other half. -/
theorem lcsSeries_le_iff_of_gens (S : Set G) (n : ℕ) {K : Subgroup G}
    (hSK : S ⊆ Subgroup.normalizer (K : Set G)) :
    lcsSeries (Subgroup.closure S) (n + 1) ≤ K ↔ lcsGensSet S (n + 1) ⊆ (K : Set G) :=
  ⟨fun hle _ hx => hle (lcsGensSet_subset_lcsSeries S (n + 1) hx),
    lcsSeries_le_of_gens S n K hSK⟩

/-- …stated as least-ness: the series term itself satisfies both hypotheses. -/
theorem lcsSeries_satisfies_gens (S : Set G) (n : ℕ) :
    S ⊆ Subgroup.normalizer ((lcsSeries (Subgroup.closure S) n : Subgroup G) : Set G)
      ∧ lcsGensSet S n ⊆ (lcsSeries (Subgroup.closure S) n : Set G) :=
  ⟨fun _ hs => le_normalizer_lcsSeries _ _ (Subgroup.subset_closure hs),
    lcsGensSet_subset_lcsSeries S n⟩

end DepthN

/-! ## 4 The committed depth-two statement, recovered -/

section DepthTwo

/-- `GradedStageFour.le_of_gens_three`, as the case `n = 1` of `lcsSeries_le_of_gens`. -/
theorem le_of_gens_three (hS : S ⊆ Subgroup.normalizer (K : Set G))
    (hbr : ∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ S, ⁅⁅s, t⁆, u⁆ ∈ K) :
    ⁅⁅Subgroup.closure S, Subgroup.closure S⁆, Subgroup.closure S⁆ ≤ K := by
  refine lcsSeries_le_of_gens S 1 K hS ?_
  rintro _ ⟨_, ⟨s, hs, t, ht, rfl⟩, u, hu, rfl⟩
  exact hbr s hs t ht u hu

/-- The depth-three statement, which the committed form could not reach: it is what
`GradedFiveForce.forceLcs_three_le_forceN4` and its two siblings bound by naming two
intermediate subgroups. -/
theorem le_of_gens_four (hS : S ⊆ Subgroup.normalizer (K : Set G))
    (hbr : ∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ S, ∀ v ∈ S, ⁅⁅⁅s, t⁆, u⁆, v⁆ ∈ K) :
    ⁅⁅⁅Subgroup.closure S, Subgroup.closure S⁆, Subgroup.closure S⁆, Subgroup.closure S⁆ ≤ K := by
  refine lcsSeries_le_of_gens S 2 K hS ?_
  rintro _ ⟨_, ⟨_, ⟨s, hs, t, ht, rfl⟩, u, hu, rfl⟩, v, hv, rfl⟩
  exact hbr s hs t ht u hu v hv

end DepthTwo

/-! ## 5 Axiom pins -/

section AxiomPins

#print axioms commLeft
#print axioms commRight
#print axioms commAll
#print axioms mem_commLeft
#print axioms mem_commRight
#print axioms mem_commAll
#print axioms commutator_mem_of_gens_right
#print axioms commutator_mem_of_gens_left
#print axioms le_normalizer_commAll
#print axioms commutator_closure_le
#print axioms lcsGensSet
#print axioms lcsSeries
#print axioms lcsSeries_zero
#print axioms lcsSeries_succ
#print axioms lcsGensSet_subset_closure
#print axioms lcsSeries_le_of_gens
#print axioms lcsSeries_map_conj_le
#print axioms le_normalizer_lcsSeries
#print axioms lcsGensSet_subset_lcsSeries
#print axioms lcsSeries_le_iff_of_gens
#print axioms lcsSeries_satisfies_gens
#print axioms le_of_gens_three
#print axioms le_of_gens_four

end AxiomPins

end LcsGens

end SqCore

end Dyadic

end GQ2
