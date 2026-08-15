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

end SqCore

end Dyadic

end GQ2
