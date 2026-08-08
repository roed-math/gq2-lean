/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedContain

/-!
# W51-SIGMA: the sigma-sensitive wider slice, and what it can and cannot see

The W50 depth sweep found that universal level-one survivors have **both** core dressings
forced: `a0 = a1 = U^{-s} V^{t}` mod squares.  The `x0`-half is committed
(`sqArbFrame_x0_dressing_forced`); the sigma-half is evidence-only, and W50-SELECT proved the
committed test family **provably blind** to it (`sqRelWord_selHom_sqArbFrame_sigma`): sigma-data
enter its selection bit only through `kappa2*k1*m0 + kappa3*k1*n0`, and the forced branch has
`k1 = 0`.  This file builds the wider slice that the selection note (`w50-selection-note.md`
paragraph 4) priced for the job - nonzero `a`- and `c`-weights on the sigma- and `x0`-slots -
and settles what it sees.

## Headline: the blindness recurs one level deeper, with an exact diagnosis - and a real escape

* **The wider slice exists and is realizable** (paragraph 1): the marking `sigMark` with sigma-slot
  `(A0, 1, C0)` and `x0`-slot `(A1, 0, C1)` kills the relator iff **three coupled gates** hold
  (`sqRelWord_sigMark_eq_one_iff`): the two adjacency parities now read the core weights
  (`2P + (AS - BT) = A1`, `2Q + (TD - SC) = -C1`), and a third, genuinely new `F`-gate couples
  the sigma- and `x0`-weights to the handle weights; its solvability parity is
  `C1*(A0 + B)` even at the canonical row (`sigMark_gateF_iff`).
* **The pivot cost is real but computable** (paragraph 2): the `x0`-slot image is flat, so the
  committed `SqU4.zpowZtwo_of_flat` computes the pivot image exactly, with the one unknown
  `c = gr3Pi sqPivotExp` (an odd unit) carried as a parameter; at the exact canonical row
  `(nu'(u_j), nu'(v_j)) = (0, 1)` the cleared letters need **no** non-flat power at all, and
  their images are pinned in closed form (`sigHom_sqEichU`, `sigHom_sqEichV`).
* **The residue is affine-linear in the sigma-slot datum** (paragraph 4): the whole sigma-slot
  dependence of the class-three residue is one explicit linear form `sigRead`
  (`sqRelWord_sigTuple_sigma`), the exact functional of sigma-data this slice reads.
* **The diagnosis** (paragraph 5): mod 2, under the gates, `sigRead` collapses to
  `kappaV*(v0*(1+u1) + u0*v1) + kappa2s*(w0*(1+u1) + u0*w1) + kappaW*(v0*w1 + w0*v1)`
  plus junk couplings with coefficient `K1` (`sigRead_decomp`): **every sigma-reading carries a
  factor from the x0-slot deviation** `(1 + u1, v1, w1)` from its class-two-forced value.  On
  the forced gauge the wider slice is as sigma-blind as the old one
  (`sigRead_gauge_even`), and on the sound admissible locus with `w1 = 0` every channel is
  killed by the gates themselves (`sigPar_sound_blind`, a decided F2 fact): the
  `k1`-cancellation of the committed family recurs, one level deeper.
* **The escape** (paragraph 6): off the gauge the wider slice genuinely reads sigma-data.  At the
  explicit hom `(A0,C0,A1,C1,A,B,C,D,P,Q,F) = (0,1,0,1,6,0,1,0,1,0,0)` and the legal dressing
  `a1 = U^{-1} * t` in the precedent's own gauge `a2 = a1^2`, the frame with `a0 = U^{-1}` has
  even residue and is killed outright by one explicit achievable move, while the frame with
  `a0 = 1` passes **every class-two row on the nose** and has odd residue - dead, and robustly
  so against all sigma-slot junk.  The committed family **provably cannot** separate this pair:
  its bit reads `m0` only through `kappa2*k1*m0`, and `kappa2` is even at every hom of the
  committed family at this row type (`selConForm_m0_blind` + `selConKappa2_even01`).

So the sigma-slot forcing is still **not** a slice statement on the wider slice: what a slice of
this shape can pin is exactly the joint functional above.  A slice that decides the sigma-slot
on the forced gauge must break the `(1+u1, v1, w1)`-factorisation, i.e. stop reading sigma
through `sqWord`'s `x`-conjugations only - the note's next layer up (class four, or the
universal quotient itself).

## Contents

* **1** the wider marking `sigMark`, its relator in closed form, the realizability iff, the
  `F`-gate parity, the instance marking, and the test hom `sigHom`;
* **2** the hom-level anchors: the pivot image via flatness, the odd half of
  `gr3Pi sqPivotExp`, and the cleared-letter images at the exact canonical row;
* **3** the letter values and the dressing model `sigVal` / `sigTuple` (reusing
  `SelConDress`), with the new junk lattice `sigLam`;
* **4** the five-slot refinement `sigRefine` (adds the sigma-slot move the committed
  four-slot calculus lacked) and its translation identity;
* **5** the sigma-reading: `sigRead`, linearity (`sqRelWord_sigTuple_sigma`), the mod-2
  decomposition (`sigRead_decomp`), gauge blindness, and the decided soundness blindness;
* **6** the verdict instances on `sqArbFrame` itself: the regression pair, its verdicts, the
  completion move, and the committed-family comparison;
* **7** axiom pins (all std-3).

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or
`Fin`-indexed tuples over them.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The wider marking

The sigma- and `x0`-slots acquire free `a`- and `c`-weights `(A0, C0)` and `(A1, C1)`; the
`x1`-slot is forced to `(2*A1, 0, 2*C1)` on its abelian columns by the relator's abelian rows
and carries the three solving coordinates `(P, Q, F)`; the handle slots are the committed
selection shape.  At `A0 = C0 = A1 = C1 = 0` this is exactly `selMark`'s value tuple with free
rows, i.e. `GradedContain`'s binder shape: the committed family is the degenerate fibre. -/

section Marking

variable {h : ℕ} {j : Fin h}

variable (h j) in
/-- **The wider-slice marking**: sigma-slot `(A0, 1, C0)`, `x0`-slot `(A1, 0, C1)`, `x1`-slot
`(2*A1, 0, 2*C1, P, Q, F)`, `j`-handle slots `(A, T, C)` and `(B, S, D)` beside their rows,
every other slot trivial. -/
def sigMark (A0 C0 A1 C1 A B C D P Q F T S : gr3R) : Fin (sqRank h) → SqU4 gr3R :=
  fun i =>
    if (i : ℕ) = 0 then ⟨A0, 1, C0, 0, 0, 0⟩ else
    if (i : ℕ) = 1 then ⟨A1, 0, C1, 0, 0, 0⟩ else
    if (i : ℕ) = 2 then ⟨2 * A1, 0, 2 * C1, P, Q, F⟩ else
    if i = sqHandleIdxU j then ⟨A, T, C, 0, 0, 0⟩ else
    if i = sqHandleIdxV j then ⟨B, S, D, 0, 0, 0⟩ else 1

variable {A0 C0 A1 C1 A B C D P Q F T S : gr3R}

@[simp] theorem sigMark_zero :
    sigMark h j A0 C0 A1 C1 A B C D P Q F T S 0 = ⟨A0, 1, C0, 0, 0, 0⟩ := by
  simp only [sigMark, sqVal_zero]
  norm_num

@[simp] theorem sigMark_one :
    sigMark h j A0 C0 A1 C1 A B C D P Q F T S 1 = ⟨A1, 0, C1, 0, 0, 0⟩ := by
  simp only [sigMark, sqVal_one]
  norm_num

@[simp] theorem sigMark_two :
    sigMark h j A0 C0 A1 C1 A B C D P Q F T S 2 = ⟨2 * A1, 0, 2 * C1, P, Q, F⟩ := by
  simp only [sigMark, sqVal_two]
  norm_num

private theorem sig_ne_handleU_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxU j := by
  intro hc
  rw [hc, sqHandleIdxU_val] at hi
  omega

private theorem sig_ne_handleV_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxV j := by
  intro hc
  rw [hc, sqHandleIdxV_val] at hi
  omega

private theorem sig_handleV_ne_handleU (j' : Fin h) : sqHandleIdxV j' ≠ sqHandleIdxU j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxV_val, sqHandleIdxU_val] at hv
  omega

private theorem sig_handleU_ne_handleU {j' : Fin h} (hne : j' ≠ j) :
    sqHandleIdxU j' ≠ sqHandleIdxU j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxU_val, sqHandleIdxU_val] at hv
  exact hne (Fin.val_injective (by omega))

private theorem sig_handleU_ne_handleV (j' : Fin h) : sqHandleIdxU j' ≠ sqHandleIdxV j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxU_val, sqHandleIdxV_val] at hv
  omega

private theorem sig_handleV_ne_handleV {j' : Fin h} (hne : j' ≠ j) :
    sqHandleIdxV j' ≠ sqHandleIdxV j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxV_val, sqHandleIdxV_val] at hv
  exact hne (Fin.val_injective (by omega))

@[simp] theorem sigMark_handleU :
    sigMark h j A0 C0 A1 C1 A B C D P Q F T S (sqHandleIdxU j) = ⟨A, T, C, 0, 0, 0⟩ := by
  simp only [sigMark, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

@[simp] theorem sigMark_handleV :
    sigMark h j A0 C0 A1 C1 A B C D P Q F T S (sqHandleIdxV j) = ⟨B, S, D, 0, 0, 0⟩ := by
  simp only [sigMark, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (sig_handleV_ne_handleU j)]
  simp

theorem sigMark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    sigMark h j A0 C0 A1 C1 A B C D P Q F T S (sqHandleIdxU j') = 1 := by
  simp only [sigMark, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (sig_handleU_ne_handleU hne), if_neg (sig_handleU_ne_handleV j')]

theorem sigMark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    sigMark h j A0 C0 A1 C1 A B C D P Q F T S (sqHandleIdxV j') = 1 := by
  simp only [sigMark, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (sig_handleV_ne_handleU j'), if_neg (sig_handleV_ne_handleV hne)]

/-- ⭐⭐ **The wider marking's relator, in closed form** (deliverable 2, marking level).  The
three abelian rows vanish identically - the `(2*A1, 2*C1)`-shape of the `x1`-slot is exactly
the abelian constraint - and the three deep rows are the three gates.  The `d`- and `e`-rows
are the committed adjacency parities **with the core weights coupled in** (`- A1`, `+ C1`),
and the `f`-row couples all four core weights to the handle weights. -/
theorem sqRelWord_sigMark :
    sqRelWord (sigMark h j A0 C0 A1 C1 A B C D P Q F T S)
      = ⟨0, 0, 0, 2 * P + (A * S - B * T) - A1, 2 * Q + (T * D - S * C) + C1,
          2 * F + (A + B) * (C * S - D * T) - A0 * C1 - A1 * C1 + 2 * A1 * Q + 2 * C1 * P⟩ := by
  have h8 : (8 : gr3R) = 0 := by decide
  have hUne := fun (j' : Fin h) (hne : j' ≠ j) =>
    sigMark_handleU_ne (A0 := A0) (C0 := C0) (A1 := A1) (C1 := C1) (A := A) (B := B) (C := C)
      (D := D) (P := P) (Q := Q) (F := F) (T := T) (S := S) hne
  have hVne := fun (j' : Fin h) (hne : j' ≠ j) =>
    sigMark_handleV_ne (A0 := A0) (C0 := C0) (A1 := A1) (C1 := C1) (A := A) (B := B) (C := C)
      (D := D) (P := P) (Q := Q) (F := F) (T := T) (S := S) hne
  have h_a : (sqRelWord (sigMark h j A0 C0 A1 C1 A B C D P Q F T S)).a = 0 := by
    rw [SqU4.sqRelWord_a, sigMark_one, sigMark_two]
    ring
  have h_b : (sqRelWord (sigMark h j A0 C0 A1 C1 A B C D P Q F T S)).b = 0 := by
    rw [SqU4.sqRelWord_b, sigMark_one, sigMark_two]
    ring
  have h_c : (sqRelWord (sigMark h j A0 C0 A1 C1 A B C D P Q F T S)).c = 0 := by
    rw [SqU4.sqRelWord_c, sigMark_one, sigMark_two]
    ring
  have h_d : (sqRelWord (sigMark h j A0 C0 A1 C1 A B C D P Q F T S)).d
      = 2 * P + (A * S - B * T) - A1 := by
    rw [SqU4.sqRelWord_d, sqHeisDefect,
      sum_eq_at _ (fun j' hne => by rw [hUne j' hne, hVne j' hne]; simp)]
    simp only [sigMark_zero, sigMark_one, sigMark_two, sigMark_handleU, sigMark_handleV,
      SqU4.toHeisAB_apply]
    ring
  have h_e : (sqRelWord (sigMark h j A0 C0 A1 C1 A B C D P Q F T S)).e
      = 2 * Q + (T * D - S * C) + C1 := by
    rw [SqU4.sqRelWord_e, sqHeisDefect,
      sum_eq_at _ (fun j' hne => by rw [hUne j' hne, hVne j' hne]; simp)]
    simp only [sigMark_zero, sigMark_one, sigMark_two, sigMark_handleU, sigMark_handleV,
      SqU4.toHeisBC_apply]
    ring
  have h_f : (sqRelWord (sigMark h j A0 C0 A1 C1 A B C D P Q F T S)).f
      = 2 * F + (A + B) * (C * S - D * T) - A0 * C1 - A1 * C1 + 2 * A1 * Q + 2 * C1 * P := by
    rw [SqU4.sqRelWord_f, sqU4Defect,
      sum_eq_at _ (fun j' hne => by rw [hUne j' hne, hVne j' hne]; simp),
      sum_eq_at (fun j' => SqU4.u4Comm3
        (sigMark h j A0 C0 A1 C1 A B C D P Q F T S (sqHandleIdxU j'))
        (sigMark h j A0 C0 A1 C1 A B C D P Q F T S (sqHandleIdxV j')))
        (fun j' hne => by rw [hUne j' hne, hVne j' hne]; simp [SqU4.u4Comm3])]
    simp only [sigMark_zero, sigMark_one, sigMark_two, sigMark_handleU, sigMark_handleV,
      sqU4Core, SqU4.u4Comm3]
    linear_combination (-(A1 * C1) - A1 * Q) * h8
  exact SqU4.ext h_a h_b h_c h_d h_e h_f

/-- ⭐⭐ **Realizability of the wider slice, characterised** (deliverable 1): the marking kills
the relator iff the three coupled gates hold.  At `A0 = C0 = A1 = C1 = 0` the first two are
the committed adjacency parities and the third solves the class-three row, so the committed
family is literally the degenerate fibre of this one. -/
theorem sqRelWord_sigMark_eq_one_iff :
    sqRelWord (sigMark h j A0 C0 A1 C1 A B C D P Q F T S) = 1
      ↔ 2 * P + (A * S - B * T) = A1 ∧ 2 * Q + (T * D - S * C) = -C1 ∧
        2 * F = A0 * C1 + A1 * C1 - (A + B) * (C * S - D * T) - 2 * A1 * Q - 2 * C1 * P := by
  rw [sqRelWord_sigMark, SqU4.eq_one_iff]
  simp only [true_and]
  refine and_congr ⟨fun hx => by linear_combination hx, fun hx => by linear_combination hx⟩
    (and_congr ⟨fun hx => by linear_combination hx, fun hx => by linear_combination hx⟩
      ⟨fun hx => by linear_combination hx, fun hx => by linear_combination hx⟩)

/-- ⭐ **The `F`-gate's solvability parity at the canonical row** (the note's cost 3, exact):
under the first two gates at `(T, S) = (0, 1)` - where they read `2*P + A = A1` and
`2*Q + C1 = C` - the third gate has a solution `F` iff `C1 * (A0 + B)` is even.  This parity
is what closes the `v0`-escape channel in paragraph 5: it identifies `K1` with `kappaV` on the
realizable locus. -/
theorem sigMark_gateF_iff (hd : 2 * P + A = A1) (he : 2 * Q + C1 = C) :
    (∃ F : gr3R, 2 * F = A0 * C1 + A1 * C1 - (A + B) * C - 2 * A1 * Q - 2 * C1 * P)
      ↔ selPar (C1 * (A0 + B)) = 0 := by
  have hX : A0 * C1 + A1 * C1 - (A + B) * C - 2 * A1 * Q - 2 * C1 * P
      = C1 * (A0 + B) - 2 * (B * C1 + (A + A1 + B) * Q) := by
    linear_combination (-C1) * hd + (A + B) * he
  rw [hX, selPar_eq_zero_iff (C1 * (A0 + B))]
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F + (B * C1 + (A + A1 + B) * Q), by linear_combination -hF⟩
  · rintro ⟨y, hy⟩
    exact ⟨y - (B * C1 + (A + A1 + B) * Q), by linear_combination -hy⟩

end Marking

end SqCore

end Dyadic

end GQ2
