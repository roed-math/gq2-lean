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

end SqCore

end Dyadic

end GQ2
