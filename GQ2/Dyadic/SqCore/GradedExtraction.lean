/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedAbsorption

/-!
# W79-EXTRACT: the handle-tower separation, at every handle count

Wave 78's repaired reduction (`GradedAbsorption.lean`) reads

`GDecideBaseThree h → GJoinSeparationAll h → GTowerKnobRealizable h → SqLamMarkTransitivity h`
(`gAbs_markTransitivity_of_baseThree`).

This file attacks the second input.  `GJoinSeparationAll h` is the `𝔽₂`-independence
bookkeeping of `GradedUniformJoin.lean` §7: an element of the span of the `2h` handle
towers whose every handle row reads `2^{k+1}`-divisibly is trivial in the layer.  Wave 75
proved it at `h = 0` only (`gJoin_towerSeparation_handleFree`, vacuous), and scoped two
routes for the general case; this file takes the first of them, the ordered `List.ofFn`
product in `Q_{k+2}`.

## What is here

* §1, the two list facts the ordered product needs: slotwise multiplication of two
  `List.ofFn` products when the first family is central, and the value of a `List.ofFn`
  product all but one of whose factors is trivial.  Both are stated for an arbitrary group.
* §2, the handle-tower words `gExtWord`: the ordered product
  `∏_j U_j^{2^k f_j} · ∏_j V_j^{2^k g_j}`, and its readings.  Because `χ_sq` is trivial on
  the cleared handle letters, `gDelta` is *additive* along these words, so the `u_{j₀}`-row
  reads `2^k f_{j₀}` and the `v_{j₀}`-row reads `2^k g_{j₀}` on the nose.
* §3, the normal form: the words form a subgroup of `Q_{k+2}` containing the handle-tower
  generators, so every element of the span is a word (`gExt_mem_span`).
* §4, the separation at every `h` and every `k` (`gExt_towerSeparation`,
  `gExt_separationAll`), which discharges `GJoinSeparationAll h` outright.

The mathematics is Labute's: the readings of §7 already separate the generators, and what
was missing was only the normal form that turns generatorwise readings into a statement
about the span.  Nothing here is conditional.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 Ordered products of central factors

Two facts about `(List.ofFn A).prod` in a group, both proved by induction on the length.
They are the whole of the "friction" wave 75 flagged: the layer sits inside a
non-commutative quotient, so the normal form needs an ordered product and its
exponent-addition law. -/

section Ordered

variable {Q : Type*} [Group Q]

/-- An ordered product of central factors is central. -/
theorem gExt_ofFn_center {n : ℕ} {A : Fin n → Q} (hA : ∀ j, A j ∈ Subgroup.center Q) :
    (List.ofFn A).prod ∈ Subgroup.center Q := by
  refine (Subgroup.center Q).list_prod_mem ?_
  intro x hx
  obtain ⟨j, rfl⟩ : ∃ j, A j = x := by simpa using hx
  exact hA j

/-- **The exponent-addition law**: two ordered products of the same length multiply slotwise,
provided the factors of the first are central. -/
theorem gExt_ofFn_mul : ∀ {n : ℕ} (A B : Fin n → Q), (∀ j, A j ∈ Subgroup.center Q) →
    (List.ofFn A).prod * (List.ofFn B).prod = (List.ofFn fun j => A j * B j).prod := by
  intro n
  induction n with
  | zero => intro A B _; simp
  | succ n ih =>
    intro A B hA
    have hc : B 0 * (List.ofFn fun i : Fin n => A i.succ).prod
        = (List.ofFn fun i : Fin n => A i.succ).prod * B 0 :=
      Subgroup.mem_center_iff.1 (gExt_ofFn_center fun i => hA i.succ) (B 0)
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, ← ih (fun i => A i.succ) (fun i => B i.succ) fun i => hA i.succ]
    calc A 0 * (List.ofFn fun i : Fin n => A i.succ).prod
          * (B 0 * (List.ofFn fun i : Fin n => B i.succ).prod)
        = A 0 * ((List.ofFn fun i : Fin n => A i.succ).prod * B 0)
            * (List.ofFn fun i : Fin n => B i.succ).prod := by
          simp only [mul_assoc]
      _ = A 0 * (B 0 * (List.ofFn fun i : Fin n => A i.succ).prod)
            * (List.ofFn fun i : Fin n => B i.succ).prod := by rw [hc]
      _ = A 0 * B 0 * ((List.ofFn fun i : Fin n => A i.succ).prod
            * (List.ofFn fun i : Fin n => B i.succ).prod) := by
          simp only [mul_assoc]

/-- The same, with the *second* family central. -/
theorem gExt_ofFn_mul' {n : ℕ} (A B : Fin n → Q) (hB : ∀ j, B j ∈ Subgroup.center Q) :
    (List.ofFn A).prod * (List.ofFn B).prod = (List.ofFn fun j => A j * B j).prod := by
  have hfam : (fun j => B j * A j) = fun j => A j * B j :=
    funext fun j => (Subgroup.mem_center_iff.1 (hB j) (A j)).symm
  rw [Subgroup.mem_center_iff.1 (gExt_ofFn_center hB) ((List.ofFn A).prod),
    gExt_ofFn_mul B A hB, hfam]

/-- **The single-slot product**: an ordered product all but one of whose factors is trivial
is that factor.  This is the step that sees each tower generator inside the normal form. -/
theorem gExt_ofFn_single : ∀ {n : ℕ} (A : Fin n → Q) (j₀ : Fin n), (∀ j, j ≠ j₀ → A j = 1) →
    (List.ofFn A).prod = A j₀ := by
  intro n
  induction n with
  | zero => intro A j₀ _; exact absurd j₀.isLt (by omega)
  | succ n ih =>
    intro A j₀ hA
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ j₀ with rfl | ⟨i, rfl⟩
    · have htail : (List.ofFn fun i : Fin n => A i.succ).prod = 1 := by
        refine List.prod_eq_one ?_
        intro x hx
        obtain ⟨i, rfl⟩ : ∃ i : Fin n, A i.succ = x := by simpa using hx
        exact hA _ (Fin.succ_ne_zero i)
      rw [htail, mul_one]
    · have hzero : A 0 = 1 := hA 0 (Fin.succ_ne_zero i).symm
      rw [hzero, one_mul]
      exact ih (fun i' => A i'.succ) i fun j hj => hA j.succ (by simpa using hj)

end Ordered

/-! ## §2 The handle-tower words, and their readings

The span `Subgroup.closure (gJoinEichSet h ν' k)` is generated by the `2h` handle towers
`U_j^{2^k a}`, `V_j^{2^k a}`.  A **word** is the ordered product
`∏_j U_j^{2^k f_j} · ∏_j V_j^{2^k g_j}` at `ℤ₂`-exponent vectors `f`, `g`.

Because `χ_sq` is trivial on the cleared handle letters (`gDelta_chiSq_sqEichU/V`) and hence
on their towers, the crossed product rule `gDelta_mul` degenerates to additivity along a
word, so §7's generatorwise readings assemble: the `u_{j₀}`-row reads `2^k f_{j₀}` and
nothing else. -/

section Words

variable {h : ℕ}

variable (h) in
/-- The `u_j`-tower at correction depth `k` and exponent `2^k a`. -/
noncomputable def gExtTowU (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (k : ℕ) (j : Fin h) (a : ℤ_[2]) : (DSq h : Type) :=
  zpowZtwo (isProP_DSq h) (sqEichU h nu' j) (2 ^ k * a)

variable (h) in
/-- The `v_j`-tower at correction depth `k` and exponent `2^k a`. -/
noncomputable def gExtTowV (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (k : ℕ) (j : Fin h) (a : ℤ_[2]) : (DSq h : Type) :=
  zpowZtwo (isProP_DSq h) (sqEichV h nu' j) (2 ^ k * a)

variable (h) in
/-- The ordered `u`-word `∏_j U_j^{2^k f_j}`. -/
noncomputable def gExtWordU (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (k : ℕ) (f : Fin h → ℤ_[2]) : (DSq h : Type) :=
  (List.ofFn fun j => gExtTowU h nu' k j (f j)).prod

variable (h) in
/-- The ordered `v`-word `∏_j V_j^{2^k g_j}`. -/
noncomputable def gExtWordV (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (k : ℕ) (g : Fin h → ℤ_[2]) : (DSq h : Type) :=
  (List.ofFn fun j => gExtTowV h nu' k j (g j)).prod

variable (h) in
/-- **The handle-tower word** `∏_j U_j^{2^k f_j} · ∏_j V_j^{2^k g_j}`. -/
noncomputable def gExtWord (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (k : ℕ) (f g : Fin h → ℤ_[2]) : (DSq h : Type) :=
  gExtWordU h nu' k f * gExtWordV h nu' k g

variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ}

theorem gExt_chiSq_towU (j : Fin h) (a : ℤ_[2]) : chiSq h (gExtTowU h nu' k j a) = 1 :=
  gJoin_chiSq_zpow (gDelta_chiSq_sqEichU nu' j) _

theorem gExt_chiSq_towV (j : Fin h) (a : ℤ_[2]) : chiSq h (gExtTowV h nu' k j a) = 1 :=
  gJoin_chiSq_zpow (gDelta_chiSq_sqEichV nu' j) _

/-- **`gDelta` is additive along a list of `χ`-trivial factors**: the crossed term of
`gDelta_mul` carries the coefficient `χ_sq`, which is `1` on every factor. -/
theorem gExt_delta_prod (c : Fin (sqRank h) → ℤ_[2]) :
    ∀ {l : List (DSq h : Type)}, (∀ x ∈ l, chiSq h x = 1) →
      gDelta h c l.prod = (l.map (gDelta h c)).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hl
    rw [List.prod_cons, gDelta_mul, hl x List.mem_cons_self, Units.val_one, one_mul,
      List.map_cons, List.sum_cons, ih fun y hy => hl y (List.mem_cons_of_mem _ hy)]

/-- The reading of a `u`-word by an arbitrary row: the exponents, weighted by the row's
values on the cleared `u`-letters. -/
theorem gExt_delta_wordU (c : Fin (sqRank h) → ℤ_[2]) (f : Fin h → ℤ_[2]) :
    gDelta h c (gExtWordU h nu' k f)
      = ∑ j, 2 ^ k * f j * gDelta h c (sqEichU h nu' j) := by
  have hchi : ∀ x ∈ (List.ofFn fun j => gExtTowU h nu' k j (f j)), chiSq h x = 1 := by
    intro x hx
    obtain ⟨j, rfl⟩ : ∃ j, gExtTowU h nu' k j (f j) = x := by simpa using hx
    exact gExt_chiSq_towU j (f j)
  rw [gExtWordU, gExt_delta_prod c hchi]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gExtTowU, gJoin_delta_zpow c (gDelta_chiSq_sqEichU nu' j)]

/-- The reading of a `v`-word by an arbitrary row. -/
theorem gExt_delta_wordV (c : Fin (sqRank h) → ℤ_[2]) (g : Fin h → ℤ_[2]) :
    gDelta h c (gExtWordV h nu' k g)
      = ∑ j, 2 ^ k * g j * gDelta h c (sqEichV h nu' j) := by
  have hchi : ∀ x ∈ (List.ofFn fun j => gExtTowV h nu' k j (g j)), chiSq h x = 1 := by
    intro x hx
    obtain ⟨j, rfl⟩ : ∃ j, gExtTowV h nu' k j (g j) = x := by simpa using hx
    exact gExt_chiSq_towV j (g j)
  rw [gExtWordV, gExt_delta_prod c hchi]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gExtTowV, gJoin_delta_zpow c (gDelta_chiSq_sqEichV nu' j)]

/-- A `u`-word is `χ`-trivial. -/
theorem gExt_chiSq_wordU (f : Fin h → ℤ_[2]) : chiSq h (gExtWordU h nu' k f) = 1 := by
  rw [gExtWordU, map_list_prod]
  refine List.prod_eq_one ?_
  intro x hx
  simp only [List.map_ofFn] at hx
  obtain ⟨j, rfl⟩ : ∃ j, chiSq h (gExtTowU h nu' k j (f j)) = x := by simpa using hx
  exact gExt_chiSq_towU j (f j)

/-- ⭐ **The `u_{j₀}`-row reads the word's `u_{j₀}`-exponent, on the nose.** -/
theorem gExt_rowU_word (f g : Fin h → ℤ_[2]) (j₀ : Fin h) :
    gDelta h (gJoinRowU j₀) (gExtWord h nu' k f g) = 2 ^ k * f j₀ := by
  have hV : gDelta h (gJoinRowU j₀) (gExtWordV h nu' k g) = 0 := by
    rw [gExt_delta_wordV]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [gJoin_rowU_eichV nu' j₀ j, mul_zero]
  have hU : gDelta h (gJoinRowU j₀) (gExtWordU h nu' k f) = 2 ^ k * f j₀ := by
    rw [gExt_delta_wordU, Finset.sum_eq_single j₀]
    · rw [gJoin_rowU_eichU nu' j₀ j₀, if_pos rfl, mul_one]
    · intro j _ hj
      rw [gJoin_rowU_eichU nu' j₀ j, if_neg hj, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j₀) hj
  rw [gExtWord, gDelta_mul, hU, hV, mul_zero, add_zero]

/-- ⭐ **The `v_{j₀}`-row reads the word's `v_{j₀}`-exponent, on the nose.** -/
theorem gExt_rowV_word (f g : Fin h → ℤ_[2]) (j₀ : Fin h) :
    gDelta h (gJoinRowV j₀) (gExtWord h nu' k f g) = 2 ^ k * g j₀ := by
  have hU : gDelta h (gJoinRowV j₀) (gExtWordU h nu' k f) = 0 := by
    rw [gExt_delta_wordU]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [gJoin_rowV_eichU nu' j₀ j, mul_zero]
  have hV : gDelta h (gJoinRowV j₀) (gExtWordV h nu' k g) = 2 ^ k * g j₀ := by
    rw [gExt_delta_wordV, Finset.sum_eq_single j₀]
    · rw [gJoin_rowV_eichV nu' j₀ j₀, if_pos rfl, mul_one]
    · intro j _ hj
      rw [gJoin_rowV_eichV nu' j₀ j, if_neg hj, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j₀) hj
  rw [gExtWord, gDelta_mul, hU, hV, zero_add, gExt_chiSq_wordU, Units.val_one, one_mul]

end Words

/-! ## §3 The normal form

Every element of the handle-tower span is a word.  The tower classes are central in
`Q_{k+2}` (they are images of `γ_{k+1}`-elements), so §1's slotwise multiplication applies
and the words form a subgroup; the generators are the single-slot words. -/

section NormalForm

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ}

/-- A tower class is central in the level quotient. -/
theorem gExt_towU_center (j : Fin h) (a : ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (gExtTowU h nu' k j a)
      ∈ Subgroup.center (levelQuot (DSq h : Type) (k + 2)) :=
  Subgroup.mem_center_iff.2 fun x =>
    gTower_img_central (gTower_zpow_dvd_mem (by omega) ⟨a, by rw [Nat.add_sub_cancel]⟩ _) x

theorem gExt_towV_center (j : Fin h) (a : ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (gExtTowV h nu' k j a)
      ∈ Subgroup.center (levelQuot (DSq h : Type) (k + 2)) :=
  Subgroup.mem_center_iff.2 fun x =>
    gTower_img_central (gTower_zpow_dvd_mem (by omega) ⟨a, by rw [Nat.add_sub_cancel]⟩ _) x

/-- The class of a `u`-word is the ordered product of the tower classes. -/
theorem gExt_wordU_class (f : Fin h → ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (gExtWordU h nu' k f)
      = (List.ofFn fun j =>
          levelMk (DSq h : Type) (k + 2) (gExtTowU h nu' k j (f j))).prod := by
  rw [gExtWordU, map_list_prod, List.map_ofFn]
  rfl

theorem gExt_wordV_class (g : Fin h → ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (gExtWordV h nu' k g)
      = (List.ofFn fun j =>
          levelMk (DSq h : Type) (k + 2) (gExtTowV h nu' k j (g j))).prod := by
  rw [gExtWordV, map_list_prod, List.map_ofFn]
  rfl

theorem gExt_wordU_center (f : Fin h → ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (gExtWordU h nu' k f)
      ∈ Subgroup.center (levelQuot (DSq h : Type) (k + 2)) := by
  rw [gExt_wordU_class]
  exact gExt_ofFn_center fun j => gExt_towU_center j (f j)

theorem gExt_wordV_center (g : Fin h → ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (gExtWordV h nu' k g)
      ∈ Subgroup.center (levelQuot (DSq h : Type) (k + 2)) := by
  rw [gExt_wordV_class]
  exact gExt_ofFn_center fun j => gExt_towV_center j (g j)

/-- Exponents add slotwise on a single tower. -/
theorem gExt_towU_add (j : Fin h) (a b : ℤ_[2]) :
    gExtTowU h nu' k j a * gExtTowU h nu' k j b = gExtTowU h nu' k j (a + b) := by
  rw [gExtTowU, gExtTowU, gExtTowU, ← zpowZtwo_add, mul_add]

theorem gExt_towV_add (j : Fin h) (a b : ℤ_[2]) :
    gExtTowV h nu' k j a * gExtTowV h nu' k j b = gExtTowV h nu' k j (a + b) := by
  rw [gExtTowV, gExtTowV, gExtTowV, ← zpowZtwo_add, mul_add]

theorem gExt_wordU_mul (f₁ f₂ : Fin h → ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (gExtWordU h nu' k f₁) *
        levelMk (DSq h : Type) (k + 2) (gExtWordU h nu' k f₂)
      = levelMk (DSq h : Type) (k + 2) (gExtWordU h nu' k (f₁ + f₂)) := by
  have hfam : (fun j => levelMk (DSq h : Type) (k + 2) (gExtTowU h nu' k j (f₁ j)) *
      levelMk (DSq h : Type) (k + 2) (gExtTowU h nu' k j (f₂ j)))
      = fun j => levelMk (DSq h : Type) (k + 2) (gExtTowU h nu' k j ((f₁ + f₂) j)) := by
    funext j
    rw [← map_mul, gExt_towU_add]
    rfl
  rw [gExt_wordU_class, gExt_wordU_class, gExt_wordU_class,
    gExt_ofFn_mul _ _ fun j => gExt_towU_center j (f₁ j), hfam]

theorem gExt_wordV_mul (g₁ g₂ : Fin h → ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (gExtWordV h nu' k g₁) *
        levelMk (DSq h : Type) (k + 2) (gExtWordV h nu' k g₂)
      = levelMk (DSq h : Type) (k + 2) (gExtWordV h nu' k (g₁ + g₂)) := by
  have hfam : (fun j => levelMk (DSq h : Type) (k + 2) (gExtTowV h nu' k j (g₁ j)) *
      levelMk (DSq h : Type) (k + 2) (gExtTowV h nu' k j (g₂ j)))
      = fun j => levelMk (DSq h : Type) (k + 2) (gExtTowV h nu' k j ((g₁ + g₂) j)) := by
    funext j
    rw [← map_mul, gExt_towV_add]
    rfl
  rw [gExt_wordV_class, gExt_wordV_class, gExt_wordV_class,
    gExt_ofFn_mul _ _ fun j => gExt_towV_center j (g₁ j), hfam]

/-- Two words multiply by adding exponents: the `v`-half of the first commutes past the
`u`-half of the second because it is central. -/
theorem gExt_swap {Q : Type*} [Group Q] (u₁ v₁ u₂ v₂ : Q)
    (hv : v₁ ∈ Subgroup.center Q) : u₁ * v₁ * (u₂ * v₂) = u₁ * u₂ * (v₁ * v₂) := by
  have hc : u₂ * v₁ = v₁ * u₂ := Subgroup.mem_center_iff.1 hv u₂
  calc u₁ * v₁ * (u₂ * v₂) = u₁ * (v₁ * u₂) * v₂ := by simp only [mul_assoc]
    _ = u₁ * (u₂ * v₁) * v₂ := by rw [hc]
    _ = u₁ * u₂ * (v₁ * v₂) := by simp only [mul_assoc]

theorem gExt_word_mul (f₁ g₁ f₂ g₂ : Fin h → ℤ_[2]) :
    levelMk (DSq h : Type) (k + 2) (gExtWord h nu' k f₁ g₁) *
        levelMk (DSq h : Type) (k + 2) (gExtWord h nu' k f₂ g₂)
      = levelMk (DSq h : Type) (k + 2) (gExtWord h nu' k (f₁ + f₂) (g₁ + g₂)) := by
  simp only [gExtWord, map_mul]
  rw [gExt_swap _ _ _ _ (gExt_wordV_center g₁), gExt_wordU_mul, gExt_wordV_mul]

theorem gExt_towU_zero (j : Fin h) : gExtTowU h nu' k j 0 = 1 := by
  rw [gExtTowU, mul_zero, zpowZtwo_zero_exp]

theorem gExt_towV_zero (j : Fin h) : gExtTowV h nu' k j 0 = 1 := by
  rw [gExtTowV, mul_zero, zpowZtwo_zero_exp]

theorem gExt_wordU_zero : gExtWordU h nu' k 0 = 1 := by
  refine List.prod_eq_one ?_
  intro x hx
  obtain ⟨j, rfl⟩ : ∃ j, gExtTowU h nu' k j ((0 : Fin h → ℤ_[2]) j) = x := by simpa using hx
  exact gExt_towU_zero j

theorem gExt_wordV_zero : gExtWordV h nu' k 0 = 1 := by
  refine List.prod_eq_one ?_
  intro x hx
  obtain ⟨j, rfl⟩ : ∃ j, gExtTowV h nu' k j ((0 : Fin h → ℤ_[2]) j) = x := by simpa using hx
  exact gExt_towV_zero j

theorem gExt_word_zero : gExtWord h nu' k 0 0 = 1 := by
  rw [gExtWord, gExt_wordU_zero, gExt_wordV_zero, mul_one]

/-- A single-slot `u`-word is the tower of that slot. -/
theorem gExt_wordU_single (j₀ : Fin h) (a : ℤ_[2]) :
    gExtWordU h nu' k (Pi.single j₀ a) = gExtTowU h nu' k j₀ a := by
  rw [gExtWordU, gExt_ofFn_single _ j₀ fun j hj => by
    rw [Pi.single_eq_of_ne hj, gExt_towU_zero], Pi.single_eq_same]

theorem gExt_wordV_single (j₀ : Fin h) (a : ℤ_[2]) :
    gExtWordV h nu' k (Pi.single j₀ a) = gExtTowV h nu' k j₀ a := by
  rw [gExtWordV, gExt_ofFn_single _ j₀ fun j hj => by
    rw [Pi.single_eq_of_ne hj, gExt_towV_zero], Pi.single_eq_same]

variable (h) in
/-- **The word span**: the classes of the handle-tower words, as a subgroup of `Q_{k+2}`.
Closure under multiplication and inversion is §1's exponent-addition law. -/
noncomputable def gExtSpan (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (k : ℕ) : Subgroup (levelQuot (DSq h : Type) (k + 2)) where
  carrier := {z | ∃ f g : Fin h → ℤ_[2],
    z = levelMk (DSq h : Type) (k + 2) (gExtWord h nu' k f g)}
  one_mem' := ⟨0, 0, by rw [gExt_word_zero, map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨f₁, g₁, rfl⟩ ⟨f₂, g₂, rfl⟩
    exact ⟨f₁ + f₂, g₁ + g₂, gExt_word_mul f₁ g₁ f₂ g₂⟩
  inv_mem' := by
    rintro _ ⟨f, g, rfl⟩
    refine ⟨-f, -g, inv_eq_of_mul_eq_one_right ?_⟩
    rw [gExt_word_mul, add_neg_cancel, add_neg_cancel, gExt_word_zero, map_one]

/-- Every handle-tower generator is a single-slot word. -/
theorem gExt_eichSet_subset :
    gJoinEichSet h nu' k ⊆ (gExtSpan h nu' k : Set (levelQuot (DSq h : Type) (k + 2))) := by
  rintro z ⟨j₀, a, (rfl | rfl)⟩
  · exact ⟨Pi.single j₀ a, 0, by
      rw [gExtWord, gExt_wordU_single, gExt_wordV_zero, mul_one, gExtTowU]⟩
  · exact ⟨0, Pi.single j₀ a, by
      rw [gExtWord, gExt_wordU_zero, gExt_wordV_single, one_mul, gExtTowV]⟩

/-- ⭐⭐ **The normal form**: every element of the handle-tower span is a word
`∏_j U_j^{2^k f_j} · ∏_j V_j^{2^k g_j}`. -/
theorem gExt_mem_span {z : levelQuot (DSq h : Type) (k + 2)}
    (hz : z ∈ Subgroup.closure (gJoinEichSet h nu' k)) :
    ∃ f g : Fin h → ℤ_[2], z = levelMk (DSq h : Type) (k + 2) (gExtWord h nu' k f g) :=
  (Subgroup.closure_le (gExtSpan h nu' k)).2 gExt_eichSet_subset hz

end NormalForm

/-! ## §4 The separation, at every handle count and every depth

The normal form of §3 and the readings of §2 together discharge wave 75's bookkeeping
obligation outright: an element of the handle-tower span whose every handle row reads
`2^{k+1}`-divisibly has every exponent even, hence is a `2^{k+1}`-tower in every slot, hence
dies in `Q_{k+2}`.  No hypothesis on `k`, and none on `h`. -/

section Separation

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {k : ℕ}

/-- An even exponent vector makes the `u`-word die one layer up. -/
theorem gExt_wordU_mem_of_even {f : Fin h → ℤ_[2]} (hf : ∀ j, (2 : ℤ_[2]) ∣ f j) :
    gExtWordU h nu' k f ∈ twoCentralSeries (DSq h : Type) (k + 2) := by
  refine (twoCentralSeries (DSq h : Type) (k + 2)).list_prod_mem ?_
  intro x hx
  obtain ⟨j, rfl⟩ : ∃ j, gExtTowU h nu' k j (f j) = x := by simpa using hx
  obtain ⟨b, hb⟩ := hf j
  rw [gExtTowU]
  refine gTower_zpow_dvd_mem (by omega) ⟨b, ?_⟩ _
  have hkk : k + 2 - 1 = k + 1 := by omega
  rw [hkk, hb, pow_succ]
  ring

theorem gExt_wordV_mem_of_even {g : Fin h → ℤ_[2]} (hg : ∀ j, (2 : ℤ_[2]) ∣ g j) :
    gExtWordV h nu' k g ∈ twoCentralSeries (DSq h : Type) (k + 2) := by
  refine (twoCentralSeries (DSq h : Type) (k + 2)).list_prod_mem ?_
  intro x hx
  obtain ⟨j, rfl⟩ : ∃ j, gExtTowV h nu' k j (g j) = x := by simpa using hx
  obtain ⟨b, hb⟩ := hg j
  rw [gExtTowV]
  refine gTower_zpow_dvd_mem (by omega) ⟨b, ?_⟩ _
  have hkk : k + 2 - 1 = k + 1 := by omega
  rw [hkk, hb, pow_succ]
  ring

/-- A row reading that is `2^{k+1}`-divisible has an even exponent. -/
theorem gExt_even_of_dvd {a : ℤ_[2]} (ha : (2 : ℤ_[2]) ^ (k + 1) ∣ 2 ^ k * a) :
    (2 : ℤ_[2]) ∣ a := by
  obtain ⟨y, hy⟩ := ha
  refine ⟨y, ?_⟩
  have h2 : ((2 : ℤ_[2]) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine mul_left_cancel₀ h2 ?_
  rw [pow_succ] at hy
  linear_combination hy

/-- ⭐⭐⭐ **The separation, at every `h` and every `k`**: an element of the handle-tower
span all of whose handle rows read `2^{k+1}`-divisibly is trivial in the layer.  This is
wave 75's `GJoinTowerSeparation`, proved; wave 75 had it at `h = 0` only. -/
theorem gExt_towerSeparation : GJoinTowerSeparation h nu' k := by
  intro z hz hU hV
  obtain ⟨f, g, rfl⟩ := gExt_mem_span hz
  have hf : ∀ j₀ : Fin h, (2 : ℤ_[2]) ∣ f j₀ := by
    intro j₀
    have hmem := hU j₀
    rw [gJoin_mem_layerDvd, gExt_rowU_word] at hmem
    exact gExt_even_of_dvd hmem
  have hg : ∀ j₀ : Fin h, (2 : ℤ_[2]) ∣ g j₀ := by
    intro j₀
    have hmem := hV j₀
    rw [gJoin_mem_layerDvd, gExt_rowV_word] at hmem
    exact gExt_even_of_dvd hmem
  have hU1 : levelMk (DSq h : Type) (k + 2) (gExtWordU h nu' k f) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (gExt_wordU_mem_of_even hf)
  have hV1 : levelMk (DSq h : Type) (k + 2) (gExtWordV h nu' k g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (gExt_wordV_mem_of_even hg)
  rw [gExtWord, map_mul, hU1, hV1, one_mul]

/-- ⭐⭐⭐ **`GJoinSeparationAll h`, discharged**: the second of the three inputs of wave
78's repaired reduction `gAbs_markTransitivity_of_baseThree` is a theorem, at every handle
count. -/
theorem gExt_separationAll (h : ℕ) : GJoinSeparationAll h :=
  fun _ _ _ => gExt_towerSeparation

end Separation

/-! ## §5 The reduction with the separation removed

Wave 78's repaired reduction took three inputs.  §4 discharges the second, so what is left
of the odd route is the depth-3 base and the extraction. -/

section Collapse

variable {h : ℕ}

/-- ⭐⭐ **The vanishing interface from the depth-3 base alone.** -/
theorem gExt_defectVanishing_of_baseThree (H3 : GDecideBaseThree h) :
    GJoinDefectVanishing h :=
  gAbs_defectVanishing_of_baseThree H3 (gExt_separationAll h)

/-- ⭐⭐ **The per-class supply from two inputs**: the OPEN depth-3 base and the extraction. -/
theorem gExt_supply_of_baseThree (H3 : GDecideBaseThree h) (HR : GTowerKnobRealizable h) :
    ∀ k, SqClassClearingSupply h k :=
  gAbs_supply_of_baseThree H3 (gExt_separationAll h) HR

/-- ⭐⭐⭐ **The `h ≥ 1` residual from two named inputs.**  Wave 78 needed three:
`GDecideBaseThree h`, `GJoinSeparationAll h`, `GTowerKnobRealizable h`.  The middle one is
now a theorem (`gExt_separationAll`), so the odd route hangs on the depth-3 base and the
extraction only. -/
theorem gExt_markTransitivity_of_baseThree (H3 : GDecideBaseThree h)
    (HR : GTowerKnobRealizable h) : SqLamMarkTransitivity h :=
  gAbs_markTransitivity_of_baseThree H3 (gExt_separationAll h) HR

end Collapse

/-! ## §6 The multi-slot dressing

Toward the third input, `GTowerKnobRealizable h`.  Wave 74 recorded the extraction's two
missing pieces (`docs/dyadic/w74-engine-note.md`, "Where wave 73's `h ≥ 2` flag actually
lives"): (i) the multi-slot composition across all `2h + 3` slots, and (ii) the far-slot
change of basis from the letters to the accumulated frame values.

This section discharges (i), unconditionally and at every `h`.  `gTower_dress_core` did the
three core slots with the handles held fixed; `gExt_dress_handles` does the `2h` handle slots
with the core held fixed, and `gExt_dress_full` composes them.  The two blocks compose with no
cross-term bookkeeping at all, because the core move reads only `m 0, m 1, m 2` and the handle
move reads only the handle values, and each block leaves the other's slots alone.

(For (ii) see the lane note: the moves available at the non-`x₁` slots read the *frame*
values, and matching them against the knob set's far span needs the far span to lie in the
span of the non-`x₁` frame slots modulo `γ₂`.  That is a property of the frame which the
interface's hypotheses do not supply.) -/

section Handles

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {k : ℕ}

/-- **The two-sided handle bracket update**: dressing both letters of a handle by corrections
one layer down moves the handle bracket by the two knobs, the cross term `⁅c, c'⁆` dying in
`⁅γ_k, γ_k⁆ ≤ ⁅γ₂, γ_k⁆ ≤ γ_{k+2}`. -/
theorem gExt_comm_dress (hk : 2 ≤ k) (u v : levelQuot G (k + 2))
    {a b : levelQuot G (k + 2)} (ha : a ∈ lambdaImage G k (k + 2))
    (hb : b ∈ lambdaImage G k (k + 2)) :
    commP (u * a) (v * b) = commP u v * (commP a v * commP u b) := by
  have hL : commP (u * a) v = commP u v * commP a v := by
    rw [cfour_commP_mul_left, gTower_commP_vanish' (gTower_commP_mem_lambdaTwo u v) ha, mul_one]
  have hR : commP (u * a) b = commP u b := by
    rw [cfour_commP_mul_left, gTower_commP_vanish' (gTower_commP_mem_lambdaTwo u b) ha, mul_one,
      gTower_commP_vanish' (gTower_lambdaImage_le hk ha) hb, mul_one]
  have hz : commP u b ∈ zLayer G (k + 1) := cfive_commP_mem_zLayer_right u hb
  rw [cfour_commP_mul_right, gTower_commP_vanish' (gTower_commP_mem_lambdaTwo (u * a) v) hb,
    mul_one, hL, hR, ← gTower_zLayer_comm hz, mul_assoc]

/-- **The handle block, dressed all at once**: the handle word moves by the ordered product of
the per-handle knobs, which are central. -/
theorem gExt_handleWord_dress {Q : Type*} [Group Q] {n : ℕ} (u v : Fin n → Q)
    {u' v' z : Fin n → Q} (hz : ∀ i, z i ∈ Subgroup.center Q)
    (hi : ∀ i, commP (u' i) (v' i) = commP (u i) (v i) * z i) :
    handleWord u' v' = handleWord u v * (List.ofFn z).prod := by
  rw [handleWord, handleWord, ← List.ofFn_eq_map, ← List.ofFn_eq_map, gExt_ofFn_mul' _ _ hz]
  simp only [hi]

/-- ⭐⭐ **The `2h` handle slots, dressed at once** (the multi-handle composition lemma wave 73
flagged and wave 74 queued): with the core held fixed, dressing every handle slot by a
correction one layer down moves the relator by the ordered product of the `2h` handle knobs. -/
theorem gExt_dress_handles (hk : 2 ≤ k) {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G (k + 2))
    {cU cV : Fin n → levelQuot G (k + 2)}
    (hcU : ∀ i, cU i ∈ lambdaImage G k (k + 2))
    (hcV : ∀ i, cV i ∈ lambdaImage G k (k + 2))
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i) * cU i)
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i) * cV i) :
    sqRelWord m' = sqRelWord m * (List.ofFn fun i =>
      commP (cU i) (m (sqHandleIdxV i)) * commP (m (sqHandleIdxU i)) (cV i)).prod := by
  have hzc : ∀ i, (commP (cU i) (m (sqHandleIdxV i)) * commP (m (sqHandleIdxU i)) (cV i))
      ∈ Subgroup.center (levelQuot G (k + 2)) := fun i =>
    zLayer_le_center G (k + 1) (Subgroup.mul_mem _
      (cfive_commP_mem_zLayer_left (hcU i) _) (cfive_commP_mem_zLayer_right _ (hcV i)))
  have hsweep := gExt_handleWord_dress (fun i => m (sqHandleIdxU i))
    (fun i => m (sqHandleIdxV i)) (u' := fun i => m' (sqHandleIdxU i))
    (v' := fun i => m' (sqHandleIdxV i)) hzc
    (fun i => by rw [hU i, hV i, gExt_comm_dress hk _ _ (hcU i) (hcV i)])
  rw [sqRelWord, sqRelWord, h0, h1, h2, hsweep, ← mul_assoc]

/-- ⭐⭐⭐ **The full multi-slot dressing**: dressing *every* slot of the frame by a correction
one layer down moves the relator by the three core knobs times the `2h` handle knobs.  The two
blocks compose without cross terms: the core move reads `m 0, m 1, m 2` only, and the handle
block leaves those alone; the handle move reads the handle values only, and the core block
leaves those alone. -/
theorem gExt_dress_full (hk : 2 ≤ k) {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G (k + 2))
    {c0 c1 c2 : levelQuot G (k + 2)} {cU cV : Fin n → levelQuot G (k + 2)}
    (hc0 : c0 ∈ lambdaImage G k (k + 2)) (hc1 : c1 ∈ lambdaImage G k (k + 2))
    (hc2 : c2 ∈ lambdaImage G k (k + 2))
    (hcU : ∀ i, cU i ∈ lambdaImage G k (k + 2))
    (hcV : ∀ i, cV i ∈ lambdaImage G k (k + 2))
    (h0 : m' 0 = m 0 * c0) (h1 : m' 1 = m 1 * c1) (h2 : m' 2 = m 2 * c2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i) * cU i)
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i) * cV i) :
    sqRelWord m' = sqRelWord m *
      (commP c0 (m 1) * commP (m 0) c1 * (c2 ^ 2 * commP c2 (m 2)) *
        (List.ofFn fun i => commP (cU i) (m (sqHandleIdxV i)) *
          commP (m (sqHandleIdxU i)) (cV i)).prod) := by
  classical
  obtain ⟨mA, hA0, hA1, hA2, hAU, hAV⟩ :
      ∃ mA : Fin (sqRank n) → levelQuot G (k + 2),
        mA 0 = m 0 * c0 ∧ mA 1 = m 1 * c1 ∧ mA 2 = m 2 * c2 ∧
          (∀ i, mA (sqHandleIdxU i) = m (sqHandleIdxU i)) ∧
            (∀ i, mA (sqHandleIdxV i) = m (sqHandleIdxV i)) := by
    refine ⟨fun i => if (i : ℕ) = 0 then m 0 * c0 else if (i : ℕ) = 1 then m 1 * c1
      else if (i : ℕ) = 2 then m 2 * c2 else m i, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [sqVal_zero]
      norm_num
    · simp only [sqVal_one]
      norm_num
    · simp only [sqVal_two]
      norm_num
    · intro i
      simp only [sqHandleIdxU_val]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · intro i
      simp only [sqHandleIdxV_val]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hcore := gTower_dress_core hk m mA hc0 hc1 hc2 hA0 hA1 hA2 hAU hAV
  have hhand := gExt_dress_handles hk mA m' hcU hcV (by rw [h0, hA0]) (by rw [h1, hA1])
    (by rw [h2, hA2]) (fun i => by rw [hU i, hAU i]) (fun i => by rw [hV i, hAV i])
  rw [hhand, hcore]
  simp only [hAU, hAV, mul_assoc]

end Handles

/-! ## §7 Axiom pins -/

section AxiomPinsSep

#print axioms gExt_ofFn_center
#print axioms gExt_ofFn_mul
#print axioms gExt_ofFn_mul'
#print axioms gExt_ofFn_single
#print axioms gExtTowU
#print axioms gExtTowV
#print axioms gExtWordU
#print axioms gExtWordV
#print axioms gExtWord
#print axioms gExt_chiSq_towU
#print axioms gExt_chiSq_towV
#print axioms gExt_delta_prod
#print axioms gExt_delta_wordU
#print axioms gExt_delta_wordV
#print axioms gExt_chiSq_wordU
#print axioms gExt_rowU_word
#print axioms gExt_rowV_word
#print axioms gExt_towU_center
#print axioms gExt_towV_center
#print axioms gExt_wordU_class
#print axioms gExt_wordV_class
#print axioms gExt_wordU_center
#print axioms gExt_wordV_center
#print axioms gExt_towU_add
#print axioms gExt_towV_add
#print axioms gExt_wordU_mul
#print axioms gExt_wordV_mul
#print axioms gExt_swap
#print axioms gExt_word_mul
#print axioms gExt_towU_zero
#print axioms gExt_towV_zero
#print axioms gExt_wordU_zero
#print axioms gExt_wordV_zero
#print axioms gExt_word_zero
#print axioms gExt_wordU_single
#print axioms gExt_wordV_single
#print axioms gExtSpan
#print axioms gExt_eichSet_subset
#print axioms gExt_mem_span
#print axioms gExt_wordU_mem_of_even
#print axioms gExt_wordV_mem_of_even
#print axioms gExt_even_of_dvd
#print axioms gExt_towerSeparation
#print axioms gExt_separationAll
#print axioms gExt_defectVanishing_of_baseThree
#print axioms gExt_supply_of_baseThree
#print axioms gExt_markTransitivity_of_baseThree
#print axioms gExt_comm_dress
#print axioms gExt_handleWord_dress
#print axioms gExt_dress_handles
#print axioms gExt_dress_full

end AxiomPinsSep

end SqCore

end Dyadic

end GQ2
