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

variable (h j A0 C0 A1 C1 A B C D P Q F T S) in
/-- ⭐ **The wider-slice test homomorphism**: any weight tuple passing the three gates is a
class-three quotient of `D_sq h`, by the committed lift. -/
noncomputable def sigHom (hd : 2 * P + (A * S - B * T) = A1)
    (he : 2 * Q + (T * D - S * C) = -C1)
    (hf : 2 * F = A0 * C1 + A1 * C1 - (A + B) * (C * S - D * T) - 2 * A1 * Q - 2 * C1 * P) :
    ContinuousMonoidHom (DSq h : Type) (SqU4 gr3R) :=
  sqU4Hom gr3R_card h (sigMark h j A0 C0 A1 C1 A B C D P Q F T S)
    (sqRelWord_sigMark_eq_one_iff.mpr ⟨hd, he, hf⟩)

variable {hd : 2 * P + (A * S - B * T) = A1} {he : 2 * Q + (T * D - S * C) = -C1}
variable {hf : 2 * F = A0 * C1 + A1 * C1 - (A + B) * (C * S - D * T) - 2 * A1 * Q - 2 * C1 * P}

@[simp] theorem sigHom_gen (i : Fin (sqRank h)) :
    sigHom h j A0 C0 A1 C1 A B C D P Q F T S hd he hf (sqGen h i)
      = sigMark h j A0 C0 A1 C1 A B C D P Q F T S i :=
  sqU4Hom_gen _ _ _ i

end Marking

/-! ### The instance weights

The escape hom of paragraph 6: `(A0, C0, A1, C1) = (0, 1, 0, 1)`, handle weights
`(A, B, C, D) = (6, 0, 1, 0)`, solving coordinates `(P, Q, F) = (1, 0, 0)`, at the canonical
row `(T, S) = (0, 1)`.  All three gates hold on the nose, the junk-lattice functionals `K1`,
`K5`, `K6` are all even (the hom is *sound*: no junk move can flip the bit), and the reading
coefficient `kappa2s = A1*Q + C1*P = 1` is odd: the sigma-slot data are read against the
`x0`-slot's `t`-component. -/

section InstanceMark

/-- The instance marking at one handle. -/
def sigWitMark : Fin (sqRank 1) → SqU4 gr3R :=
  ![⟨0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 2, 1, 0, 0⟩, ⟨6, 0, 1, 0, 0, 0⟩,
    ⟨0, 1, 0, 0, 0, 0⟩]

/-- The instance marking is the wider marking at the instance weights. -/
theorem sigWitMark_eq : sigWitMark = sigMark 1 0 0 1 0 1 6 0 1 0 1 0 0 0 1 := by
  funext i
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sigMark_zero]; rfl
  · rw [sigMark_one]; rfl
  · rw [sigMark_two]; decide
  · rw [Subsingleton.elim j' 0, sigMark_handleU]; rfl
  · rw [Subsingleton.elim j' 0, sigMark_handleV]; rfl

/-- The instance marking kills the relator: the wider slice is non-vacuously realizable. -/
theorem sqRelWord_sigWitMark : sqRelWord sigWitMark = 1 := by decide

/-- The three gates at the instance weights, by evaluation. -/
example : 2 * (1 : gr3R) + (6 * 1 - 0 * 0) = 0 ∧ 2 * (0 : gr3R) + (0 * 0 - 1 * 1) = -1 ∧
    2 * (0 : gr3R) = 0 * 1 + 0 * 1 - (6 + 0) * (1 * 1 - 0 * 0) - 2 * 0 * 0 - 2 * 1 * 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- ⭐ **The instance test hom**: the wider slice's escape hom, as an honest continuous
homomorphism `D_sq 1 → U_4(Z/8)` through the committed lift. -/
noncomputable def sigWitHom : ContinuousMonoidHom (DSq 1 : Type) (SqU4 gr3R) :=
  sqU4Hom gr3R_card 1 sigWitMark sqRelWord_sigWitMark

@[simp] theorem sigWitHom_gen (i : Fin (sqRank 1)) : sigWitHom (sqGen 1 i) = sigWitMark i :=
  sqU4Hom_gen _ _ _ i

end InstanceMark

/-! ## 2 The hom-level anchors

The note's cost 1, discharged: the `x0`-slot image `(A1, 0, C1, 0, 0, 0)` satisfies all three
flatness conditions of the committed `SqU4.zpowZtwo_of_flat` (its `b`-column vanishes), so the
pivot image is exact, `sqPivotExp`-dependent only through the single scalar
`c = gr3Pi sqPivotExp` - an odd unit, carried below as a parameter with its half exhibited.
At the exact canonical row `nu' = nuSel h j 0 1` the two cleared letters need no non-flat
power at all: `nu'(u_j) = 0` and `nu'(v_j) = 1` on the nose, so `U` maps to the raw handle
value and `V` to the handle value times the inverse pivot image.  The non-flat binomial layer
(needed for rows that are only *residually* `(0, 1)`) is deliberately out of scope; see the
scope note in paragraph 6. -/

section Anchors

variable {h : ℕ} {j : Fin h} {A0 C0 A1 C1 A B C D P Q F T S : gr3R}
variable {hd : 2 * P + (A * S - B * T) = A1} {he : 2 * Q + (T * D - S * C) = -C1}
variable {hf : 2 * F = A0 * C1 + A1 * C1 - (A + B) * (C * S - D * T) - 2 * A1 * Q - 2 * C1 * P}

/-- **The `x0`-slot image is flat**, so its `Z_2`-powers are linear (the committed
`SqU4.zpowZtwo_of_flat` applies: `b = 0` kills all three obstructions). -/
theorem sig_zpow_x0 (u : ℤ_[2]) :
    zpowZtwo isProP_two_gr3 (⟨A1, 0, C1, 0, 0, 0⟩ : SqU4 gr3R) u
      = ⟨gr3Pi u * A1, 0, gr3Pi u * C1, 0, 0, 0⟩ := by
  rw [SqU4.zpowZtwo_of_flat isProP_two_gr3 gr3Pi gr3Pi_open (by ring) (by ring) (by ring)]
  ext <;> simp

/-- **The pivot value** of the wider slice at pivot-exponent residue `c`: the image of
`w = sigma * x0^{-c}`. -/
def sigPivotVal (c A0 C0 A1 C1 : gr3R) : SqU4 gr3R :=
  ⟨A0 - c * A1, 1, C0 - c * C1, 0, -(c * C1), 0⟩

/-- ⭐ **The pivot image, exactly** (the note's cost 1): the `sqPivotExp`-dependence returns,
but only through the residue `c = gr3Pi sqPivotExp`. -/
theorem sigHom_sqPivot :
    sigHom h j A0 C0 A1 C1 A B C D P Q F T S hd he hf (sqPivot h)
      = sigPivotVal (gr3Pi sqPivotExp) A0 C0 A1 C1 := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_gr3, dsqX0, sigHom_gen, sigMark_one, sig_zpow_x0,
    dsqSigma, sigHom_gen, sigMark_zero]
  ext <;> simp [sigPivotVal] <;> ring

/-- The pivot-exponent residue is an **odd unit**: its half `h2` exists.  Every instance
statement below is quantified over `h2`, so the two-residue mitigation of the note is
automatic: the gate is run at all odd values at once. -/
theorem gr3Pi_sqPivotExp_half : ∃ h2 : gr3R, gr3Pi sqPivotExp = 1 + 2 * h2 := by
  obtain ⟨u, hu⟩ := isUnit_sqPivotExp.map (gr3Pi : ℤ_[2] →+* gr3R)
  have hall : ∀ u : gr3Rˣ, ∃ h2 : gr3R, (u : gr3R) = 1 + 2 * h2 := by decide
  rw [← hu]
  exact hall u

/-- ⭐ **The cleared `U` at the exact canonical row**: `nu'(u_j) = 0` on the nose, so no pivot
power is subtracted and `U` maps to the raw handle value - at every weight tuple of the
family. -/
theorem sigHom_sqEichU_nuSel :
    sigHom h j A0 C0 A1 C1 A B C D P Q F T S hd he hf (sqEichU h (nuSel h j 0 1) j)
      = ⟨A, T, C, 0, 0, 0⟩ := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr3, nuSel_handleU,
    toAdd_ofAdd, zpowZtwo_zero_exp, inv_one, one_mul, sigHom_gen, sigMark_handleU]

/-- ⭐ **The cleared `V` at the exact canonical row**: `nu'(v_j) = 1` on the nose, so exactly
one inverse pivot is subtracted - a single group inverse, no `Z_2`-power machinery. -/
theorem sigHom_sqEichV_nuSel :
    sigHom h j A0 C0 A1 C1 A B C D P Q F T S hd he hf (sqEichV h (nuSel h j 0 1) j)
      = ⟨B, S, D, 0, 0, 0⟩ * (sigPivotVal (gr3Pi sqPivotExp) A0 C0 A1 C1)⁻¹ := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr3, nuSel_handleV,
    toAdd_ofAdd, zpowZtwo_one_exp, sigHom_sqPivot, sigHom_gen, sigMark_handleV]

/-- ⭐ The image of the order-two class `t = x1 * x0^{-2}` on the wider slice: still
`gamma_2`-shaped with `(d, e) = (P, Q)`, but its class-three coordinate now reads the
`x0`-weight: `F - 2*C1*P`. -/
theorem sigHom_selTee :
    sigHom h j A0 C0 A1 C1 A B C D P Q F T S hd he hf (selTee h)
      = ⟨0, 0, 0, P, Q, F - 2 * (C1 * P)⟩ := by
  rw [selTee, map_mul, map_inv, map_mul, dsqX1, dsqX0, sigHom_gen, sigHom_gen, sigMark_two,
    sigMark_one]
  ext <;> simp <;> ring

end Anchors

/-! ## 3 The letters and the dressing model

The wider-slice analogue of `GradedContain` paragraphs 1-2, at the canonical row
`(T, S) = (0, 1)`.  A level-one dressing is a word in the three cleared letters `U`, `V`, `t`
times an achievable `gamma_2`-junk and a free class-three part.  All three letter images have
`b`-column zero, so the `(d, e)`-columns of any word in them add exactly (as in the committed
model), and the achievable junk `(d, e)`-pairs form the lattice `sigLam` spanned by the three
commutator pairings `[sigma, x0]`, `[sigma, V]`, `[U, V]` of the marking's generators - now
`(-A1, C1)`, `(A0 - B, D - C0)` and `(A, -C)`, all read off `commP_d` / `commP_e`.  The letter
values themselves are the hom-level anchors of paragraph 2, specialised to `(T, S) = (0, 1)`:
this model is not a postulate, it is the committed letter images with the junk parametrised. -/

section Model

variable {h : ℕ} {j : Fin h}

/-- The cleared `U`-letter value at the canonical row (the anchor at `T = 0`). -/
def sigU (A C : gr3R) : SqU4 gr3R := ⟨A, 0, C, 0, 0, 0⟩

/-- The cleared `V`-letter value at the canonical row: the handle value times the inverse
pivot image, multiplied out. -/
def sigV (c A0 C0 A1 C1 B D : gr3R) : SqU4 gr3R :=
  ⟨B - (A0 - c * A1), 0, D - (C0 - c * C1), (A0 - c * A1) - B, c * C1,
    (B - (A0 - c * A1)) * C0⟩

/-- The `t`-letter value (the anchor `sigHom_selTee`). -/
def sigTee (C1 P Q F : gr3R) : SqU4 gr3R := ⟨0, 0, 0, P, Q, F - 2 * (C1 * P)⟩

/-- The `V`-letter value is the anchor's product, multiplied out: `sigV` is honest. -/
theorem sigV_eq_mul (c A0 C0 A1 C1 B D : gr3R) :
    (⟨B, 1, D, 0, 0, 0⟩ : SqU4 gr3R) * (sigPivotVal c A0 C0 A1 C1)⁻¹
      = sigV c A0 C0 A1 C1 B D := by
  ext <;> simp [sigPivotVal, sigV] <;> ring

/-- Membership in the wider junk lattice: the `(d, e)`-pair of `z` is a combination of the
three commutator pairings `(-A1, C1)`, `(A0 - B, D - C0)`, `(A, -C)` of the wider marking's
generators (`[sigma, x0]`, `[sigma, V]`, `[U, V]` at the canonical row, by `SqU4.commP_d` and
`SqU4.commP_e`). -/
def sigLam (A0 C0 A1 C1 A B C D : gr3R) (z : SqU4 gr3R) : Prop :=
  ∃ r s t : gr3R, z.d = -(r * A1) + s * (A0 - B) + t * A ∧
    z.e = r * C1 + s * (D - C0) - t * C

/-- **The image of a level-one dressing datum** on the wider slice: `u`, `v`, `w` are the
`U`-, `V`- and `t`-components, `r`, `s`, `t` the coefficients on the three `sigLam`
generators, `f` the free class-three part.  Because all three letter images have `b = 0`, the
`(d, e)`-columns of an arbitrary word in them add exactly, so this closed form covers every
product of letter powers in any order, exactly as in the committed `selConVal`. -/
def sigVal (c A0 C0 A1 C1 A B C D P Q : gr3R) (x : SelConDress) : SqU4 gr3R :=
  ⟨A * x.u + (B - (A0 - c * A1)) * x.v, 0, C * x.u + (D - (C0 - c * C1)) * x.v,
    ((A0 - c * A1) - B) * x.v + P * x.w + (-(x.r * A1) + x.s * (A0 - B) + x.t * A),
    (c * C1) * x.v + Q * x.w + (x.r * C1 + x.s * (D - C0) - x.t * C),
    x.f⟩

variable {c A0 C0 A1 C1 A B C D P Q F : gr3R}

@[simp] theorem sigVal_triv : sigVal c A0 C0 A1 C1 A B C D P Q selConTriv = 1 := by
  ext <;> simp [sigVal, selConTriv]

/-- A junk-only datum lands in the wider junk lattice, by construction. -/
theorem sigVal_lam (x : SelConDress) (hu : x.u = 0) (hv : x.v = 0) (hw : x.w = 0) :
    sigLam A0 C0 A1 C1 A B C D (sigVal c A0 C0 A1 C1 A B C D P Q x) :=
  ⟨x.r, x.s, x.t, by simp [sigVal, hu, hv, hw], by simp [sigVal, hu, hv, hw]⟩

variable (h j) in
/-- **The wider-slice binder tuple**: the five slot images of a level-one dressed frame at the
canonical row, dressing data `x0, ..., x4` on the sigma-, `x0`-, `x1`- and two `j`-handle
slots, every other slot trivial. -/
def sigTuple (c A0 C0 A1 C1 A B C D P Q F : gr3R) (x0 x1 x2 x3 x4 : SelConDress) :
    Fin (sqRank h) → SqU4 gr3R :=
  fun i =>
    if (i : ℕ) = 0 then ⟨A0, 1, C0, 0, 0, 0⟩ * sigVal c A0 C0 A1 C1 A B C D P Q x0 else
    if (i : ℕ) = 1 then ⟨A1, 0, C1, 0, 0, 0⟩ * sigVal c A0 C0 A1 C1 A B C D P Q x1 else
    if (i : ℕ) = 2 then ⟨2 * A1, 0, 2 * C1, P, Q, F⟩ * sigVal c A0 C0 A1 C1 A B C D P Q x2
    else
    if i = sqHandleIdxU j then sigU A C * sigVal c A0 C0 A1 C1 A B C D P Q x3 else
    if i = sqHandleIdxV j then sigV c A0 C0 A1 C1 B D * sigVal c A0 C0 A1 C1 A B C D P Q x4
    else 1

variable {x0 x1 x2 x3 x4 : SelConDress}

@[simp] theorem sigTuple_zero :
    sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4 0
      = ⟨A0, 1, C0, 0, 0, 0⟩ * sigVal c A0 C0 A1 C1 A B C D P Q x0 := by
  simp only [sigTuple, sqVal_zero]
  norm_num

@[simp] theorem sigTuple_one :
    sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4 1
      = ⟨A1, 0, C1, 0, 0, 0⟩ * sigVal c A0 C0 A1 C1 A B C D P Q x1 := by
  simp only [sigTuple, sqVal_one]
  norm_num

@[simp] theorem sigTuple_two :
    sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4 2
      = ⟨2 * A1, 0, 2 * C1, P, Q, F⟩ * sigVal c A0 C0 A1 C1 A B C D P Q x2 := by
  simp only [sigTuple, sqVal_two]
  norm_num

@[simp] theorem sigTuple_handleU :
    sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4 (sqHandleIdxU j)
      = sigU A C * sigVal c A0 C0 A1 C1 A B C D P Q x3 := by
  simp only [sigTuple, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

@[simp] theorem sigTuple_handleV :
    sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4 (sqHandleIdxV j)
      = sigV c A0 C0 A1 C1 B D * sigVal c A0 C0 A1 C1 A B C D P Q x4 := by
  simp only [sigTuple, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (sig_handleV_ne_handleU j)]
  simp

theorem sigTuple_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4 (sqHandleIdxU j') = 1 := by
  simp only [sigTuple, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (sig_handleU_ne_handleU hne), if_neg (sig_handleU_ne_handleV j')]

theorem sigTuple_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4 (sqHandleIdxV j') = 1 := by
  simp only [sigTuple, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (sig_handleV_ne_handleU j'), if_neg (sig_handleV_ne_handleV hne)]

end Model

/-! ## 4 The five-slot refinement

The committed `selRefine` moves four slots; the sigma-slot move it lacks is exactly the one
the wider slice makes audible, so here is the five-slot extension (the note's recommended
ticket 3, needed rather than optional on this slice).  A `gamma_2`-move on the sigma-slot
translates the relator by `z0.d * (m 1).c - z0.e * (m 1).a` - the pairing against the
`x0`-slot columns, which the committed slice could never see because its `x0`-slot column
values were `0` mod `2`. -/

section Refine

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

variable (j) in
/-- **The five-slot refinement**: dress the sigma-slot by `z0`, the two exponent slots by
`w1`, `w2`, and the two `j`-handle slots by `z3`, `z4`, all on the right. -/
def sigRefine (m : Fin (sqRank h) → SqU4 R) (z0 w1 w2 z3 z4 : SqU4 R) :
    Fin (sqRank h) → SqU4 R :=
  fun i => if (i : ℕ) = 0 then m i * z0 else selRefine j m w1 w2 z3 z4 i

variable {m : Fin (sqRank h) → SqU4 R} {z0 w1 w2 z3 z4 : SqU4 R}

@[simp] theorem sigRefine_zero : sigRefine j m z0 w1 w2 z3 z4 0 = m 0 * z0 := by
  simp only [sigRefine, sqVal_zero]
  norm_num

@[simp] theorem sigRefine_one : sigRefine j m z0 w1 w2 z3 z4 1 = m 1 * w1 := by
  simp only [sigRefine, sqVal_one]
  norm_num

@[simp] theorem sigRefine_two : sigRefine j m z0 w1 w2 z3 z4 2 = m 2 * w2 := by
  simp only [sigRefine, sqVal_two]
  norm_num

@[simp] theorem sigRefine_handleU :
    sigRefine j m z0 w1 w2 z3 z4 (sqHandleIdxU j) = m (sqHandleIdxU j) * z3 := by
  simp only [sigRefine, sqHandleIdxU_val]
  rw [if_neg (by omega), selRefine_handleU]

@[simp] theorem sigRefine_handleV :
    sigRefine j m z0 w1 w2 z3 z4 (sqHandleIdxV j) = m (sqHandleIdxV j) * z4 := by
  simp only [sigRefine, sqHandleIdxV_val]
  rw [if_neg (by omega), selRefine_handleV]

theorem sigRefine_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    sigRefine j m z0 w1 w2 z3 z4 (sqHandleIdxU j') = m (sqHandleIdxU j') := by
  simp only [sigRefine, sqHandleIdxU_val]
  rw [if_neg (by omega), selRefine_handleU_ne hne]

theorem sigRefine_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    sigRefine j m z0 w1 w2 z3 z4 (sqHandleIdxV j') = m (sqHandleIdxV j') := by
  simp only [sigRefine, sqHandleIdxV_val]
  rw [if_neg (by omega), selRefine_handleV_ne hne]

/-- ⭐⭐ **The five-slot translation identity**: the refinement translates the relator by a
central element whose value adds the sigma-slot increment
`z0.d * (m 1).c - z0.e * (m 1).a` to the committed four-slot expression.  The proof factors
through the committed `sqRelWord_selRefine`: the five-slot move is the four-slot move of the
sigma-dressed tuple, and the sigma-slot `gamma_2`-move alone translates by its pairing against
the `x0`-slot columns. -/
theorem sqRelWord_sigRefine (hz0 : z0.IsGaTwo) (hw1 : w1.IsGaThree) (hw2 : w2.IsGaThree)
    (hz3 : z3.IsGaTwo) (hz4 : z4.IsGaTwo) :
    sqRelWord (sigRefine j m z0 w1 w2 z3 z4)
      = sqRelWord m * ⟨0, 0, 0, 0, 0,
          (z0.d * (m 1).c - z0.e * (m 1).a) + (-4 * w1.f + 2 * w2.f)
          + (z3.d * (m (sqHandleIdxV j)).c - z3.e * (m (sqHandleIdxV j)).a)
          + ((m (sqHandleIdxU j)).a * z4.e - (m (sqHandleIdxU j)).c * z4.d)⟩ := by
  obtain ⟨hz0a, hz0b, hz0c⟩ := id hz0
  set m' : Fin (sqRank h) → SqU4 R := fun i => if (i : ℕ) = 0 then m i * z0 else m i with hm'
  have hm'0 : m' 0 = m 0 * z0 := by simp only [hm', sqVal_zero]; norm_num
  have hm'ne : ∀ i : Fin (sqRank h), (i : ℕ) ≠ 0 → m' i = m i := fun i hi => if_neg hi
  have hm'1 : m' 1 = m 1 := hm'ne 1 (by rw [sqVal_one]; omega)
  have hm'2 : m' 2 = m 2 := hm'ne 2 (by rw [sqVal_two]; omega)
  have hm'U : ∀ j' : Fin h, m' (sqHandleIdxU j') = m (sqHandleIdxU j') := fun j' =>
    hm'ne _ (by rw [sqHandleIdxU_val]; omega)
  have hm'V : ∀ j' : Fin h, m' (sqHandleIdxV j') = m (sqHandleIdxV j') := fun j' =>
    hm'ne _ (by rw [sqHandleIdxV_val]; omega)
  have hstep : sigRefine j m z0 w1 w2 z3 z4 = selRefine j m' w1 w2 z3 z4 := by
    funext i
    by_cases hi : (i : ℕ) = 0
    · have hi0 : i = 0 := Fin.val_injective (by rw [hi, sqVal_zero])
      subst hi0
      rw [sigRefine_zero, selRefine_zero, hm'0]
    · simp only [sigRefine, if_neg hi]
      simp only [selRefine]
      rw [hm'ne i hi]
  have habm' : ∀ i, (m' i).a = (m i).a ∧ (m' i).b = (m i).b ∧ (m' i).c = (m i).c := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have hi0 : i = 0 := Fin.val_injective (by rw [hi, sqVal_zero])
      subst hi0
      rw [hm'0]
      exact ⟨by rw [SqU4.mul_a, hz0a, add_zero], by rw [SqU4.mul_b, hz0b, add_zero],
        by rw [SqU4.mul_c, hz0c, add_zero]⟩
    · rw [hm'ne i hi]
      exact ⟨rfl, rfl, rfl⟩
  have hzero : sqRelWord m' = sqRelWord m
      * ⟨0, 0, 0, 0, 0, z0.d * (m 1).c - z0.e * (m 1).a⟩ := by
    rw [SqU4.mul_center_f]
    have h_a : (sqRelWord m').a = (sqRelWord m).a := by
      rw [SqU4.sqRelWord_a, SqU4.sqRelWord_a, hm'1, hm'2]
    have h_b : (sqRelWord m').b = (sqRelWord m).b := by
      rw [SqU4.sqRelWord_b, SqU4.sqRelWord_b, hm'1, hm'2]
    have h_c : (sqRelWord m').c = (sqRelWord m).c := by
      rw [SqU4.sqRelWord_c, SqU4.sqRelWord_c, hm'1, hm'2]
    have h_d : (sqRelWord m').d = (sqRelWord m).d := by
      rw [SqU4.sqRelWord_d, SqU4.sqRelWord_d, hm'1, hm'2,
        sqHeisDefect_congr_ab (m := fun i => SqU4.toHeisAB (m i))
          (m' := fun i => SqU4.toHeisAB (m' i)) fun i => ⟨by simpa using (habm' i).1,
          by simpa using (habm' i).2.1⟩]
    have h_e : (sqRelWord m').e = (sqRelWord m).e := by
      rw [SqU4.sqRelWord_e, SqU4.sqRelWord_e, hm'1, hm'2,
        sqHeisDefect_congr_ab (m := fun i => SqU4.toHeisBC (m i))
          (m' := fun i => SqU4.toHeisBC (m' i)) fun i => ⟨by simpa using (habm' i).2.1,
          by simpa using (habm' i).2.2⟩]
    have h_f : (sqRelWord m').f = (sqRelWord m).f + (z0.d * (m 1).c - z0.e * (m 1).a) := by
      rw [SqU4.sqRelWord_f, SqU4.sqRelWord_f, hm'1, hm'2]
      have hdef : sqU4Defect h m' = sqU4Defect h m + (z0.d * (m 1).c - z0.e * (m 1).a) := by
        simp only [sqU4Defect]
        have hcore : sqU4Core (m' 0) (m' 1) (m' 2)
            = sqU4Core (m 0) (m 1) (m 2) + (z0.d * (m 1).c - z0.e * (m 1).a) := by
          rw [hm'0, hm'1, hm'2]
          simp only [sqU4Core, SqU4.mul_a, SqU4.mul_b, SqU4.mul_c, SqU4.mul_d, SqU4.mul_e,
            hz0a, hz0b, hz0c]
          ring
        rw [hcore, hm'1, hm'2]
        have hUV : ∀ j' : Fin h,
            (m' (sqHandleIdxU j')).b * (m' (sqHandleIdxV j')).c
                - (m' (sqHandleIdxV j')).b * (m' (sqHandleIdxU j')).c
              = (m (sqHandleIdxU j')).b * (m (sqHandleIdxV j')).c
                - (m (sqHandleIdxV j')).b * (m (sqHandleIdxU j')).c := by
          intro j'
          rw [hm'U, hm'V]
        have hcm : ∀ j' : Fin h,
            SqU4.u4Comm3 (m' (sqHandleIdxU j')) (m' (sqHandleIdxV j'))
              = SqU4.u4Comm3 (m (sqHandleIdxU j')) (m (sqHandleIdxV j')) := by
          intro j'
          rw [hm'U, hm'V]
        rw [Finset.sum_congr rfl fun j' _ => hUV j', Finset.sum_congr rfl fun j' _ => hcm j']
        ring
      rw [hdef]
      ring
    exact SqU4.ext h_a h_b h_c h_d h_e h_f
  rw [hstep, sqRelWord_selRefine hw1 hw2 hz3 hz4, hm'U, hm'V, hzero, mul_assoc]
  congr 1
  ext <;> simp
  ring

end Refine

/-! ## 5 The sigma-reading

The relator's class-three coordinate is **affine-linear in the sigma-slot datum**: the sigma
value enters `sqU4Core` only through products with its own constant `b = 1` and the `x0`-slot
columns, never quadratically in its own dressing.  So the whole sigma-dependence is one linear
form `sigRead`, and `sqRelWord_sigTuple_sigma` - swapping the sigma-datum translates the
relator by the central difference of `sigRead`-values - is the exact answer to "which
functional of sigma-data does this slice read".  `sigRead` reads the sigma-datum, the
`x0`-slot datum, and the weights; the `x1`-slot and handle data are invisible to it. -/

section ReadOut

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The sigma-reading functional**: the exact linear form in the sigma-slot datum `x` by
which the class-three residue moves, with the `x0`-slot datum `y` and the weights as
coefficients.  Every monomial carries one `x`-field; the six coefficient blocks are the six
`x`-fields' pairings against the `x0`-slot value and its junk. -/
def sigRead (c A0 C0 A1 C1 A B C D P Q : gr3R) (x y : SelConDress) : gr3R :=
  x.u * (-2 * A * C * y.t - 2 * A * C * y.u - A * C0 * y.s + A * C0 * y.v + A * C1 * y.r
      - A * C1 + A * D * y.s - A * D * y.v + A * Q * y.w - A0 * C * y.s + A1 * C * y.r
      - A1 * C + B * C * y.s - C * P * y.w)
    + x.v * (A * C0 * y.t + A * C0 * y.u - A * C1 * c * y.t - 2 * A * C1 * c * y.u
      - A * D * y.t - A * D * y.u + A0 * C * y.t + 2 * A0 * C * y.u + 2 * A0 * C0 * y.s
      - 2 * A0 * C0 * y.v - A0 * C1 * c * y.s + 2 * A0 * C1 * c * y.v - A0 * C1 * y.r
      + 2 * A0 * C1 - 2 * A0 * D * y.s + 2 * A0 * D * y.v - A0 * Q * y.w - A1 * C * c * y.t
      - 2 * A1 * C * c * y.u - A1 * C0 * c * y.s + 2 * A1 * C0 * c * y.v - A1 * C0 * y.r
      + A1 * C0 - 2 * A1 * C1 * c ^ 2 * y.v + 2 * A1 * C1 * c * y.r - 4 * A1 * C1 * c
      + A1 * D * c * y.s - 2 * A1 * D * c * y.v + A1 * D * y.r - A1 * D + A1 * Q * c * y.w
      - B * C * y.t - 2 * B * C * y.u - 2 * B * C0 * y.s + 2 * B * C0 * y.v
      + B * C1 * c * y.s - 2 * B * C1 * c * y.v + B * C1 * y.r - 2 * B * C1
      + 2 * B * D * y.s - 2 * B * D * y.v + B * Q * y.w + C0 * P * y.w - C1 * P * c * y.w
      - D * P * y.w)
    + x.w * (-A * Q * y.u + A0 * Q * y.v - A1 * Q * c * y.v - A1 * Q - B * Q * y.v
      + C * P * y.u - C0 * P * y.v + C1 * P * c * y.v + C1 * P + D * P * y.v)
    + x.r * (-A * C1 * y.u + A0 * C1 * y.v - A1 * C * y.u + A1 * C0 * y.v
      - 2 * A1 * C1 * c * y.v - 2 * A1 * C1 - A1 * D * y.v - B * C1 * y.v)
    + x.s * (A * C0 * y.u - A * D * y.u + A0 * C * y.u - 2 * A0 * C0 * y.v
      + A0 * C1 * c * y.v + A0 * C1 + 2 * A0 * D * y.v + A1 * C0 * c * y.v + A1 * C0
      - A1 * D * c * y.v - A1 * D - B * C * y.u + 2 * B * C0 * y.v - B * C1 * c * y.v
      - B * C1 - 2 * B * D * y.v)
    + x.t * (2 * A * C * y.u - A * C0 * y.v + A * C1 * c * y.v + A * C1 + A * D * y.v
      - A0 * C * y.v + A1 * C * c * y.v + A1 * C + B * C * y.v)

variable {c A0 C0 A1 C1 A B C D P Q F : gr3R} {x0 x0' x1 x2 x3 x4 : SelConDress}

/-- The trivial sigma-datum reads zero. -/
@[simp] theorem sigRead_triv (y : SelConDress) :
    sigRead c A0 C0 A1 C1 A B C D P Q selConTriv y = 0 := by
  simp [sigRead, selConTriv]

/-- ⭐⭐ **The residue is affine-linear in the sigma-slot datum** (the characterization
deliverable): swapping the sigma-datum from `x0'` to `x0` translates the relator by the
central difference of `sigRead`-values.  All five class-`<= 2` rows are untouched - the
sigma-slot's `b`-column is the constant `1` and its `a`-column enters no lower row - so the
entire sigma-dependence of the wider slice is the one linear functional `sigRead`. -/
theorem sqRelWord_sigTuple_sigma :
    sqRelWord (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4)
      = sqRelWord (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0' x1 x2 x3 x4)
        * ⟨0, 0, 0, 0, 0, sigRead c A0 C0 A1 C1 A B C D P Q x0 x1
            - sigRead c A0 C0 A1 C1 A B C D P Q x0' x1⟩ := by
  rw [SqU4.mul_center_f]
  have hUne := fun (j' : Fin h) (hne : j' ≠ j) =>
    sigTuple_handleU_ne (c := c) (A0 := A0) (C0 := C0) (A1 := A1) (C1 := C1) (A := A)
      (B := B) (C := C) (D := D) (P := P) (Q := Q) (F := F) (x0 := x0) (x1 := x1) (x2 := x2)
      (x3 := x3) (x4 := x4) hne
  have hVne := fun (j' : Fin h) (hne : j' ≠ j) =>
    sigTuple_handleV_ne (c := c) (A0 := A0) (C0 := C0) (A1 := A1) (C1 := C1) (A := A)
      (B := B) (C := C) (D := D) (P := P) (Q := Q) (F := F) (x0 := x0) (x1 := x1) (x2 := x2)
      (x3 := x3) (x4 := x4) hne
  have hUne' := fun (j' : Fin h) (hne : j' ≠ j) =>
    sigTuple_handleU_ne (c := c) (A0 := A0) (C0 := C0) (A1 := A1) (C1 := C1) (A := A)
      (B := B) (C := C) (D := D) (P := P) (Q := Q) (F := F) (x0 := x0') (x1 := x1) (x2 := x2)
      (x3 := x3) (x4 := x4) hne
  have hVne' := fun (j' : Fin h) (hne : j' ≠ j) =>
    sigTuple_handleV_ne (c := c) (A0 := A0) (C0 := C0) (A1 := A1) (C1 := C1) (A := A)
      (B := B) (C := C) (D := D) (P := P) (Q := Q) (F := F) (x0 := x0') (x1 := x1) (x2 := x2)
      (x3 := x3) (x4 := x4) hne
  refine SqU4.ext ?_ ?_ ?_ ?_ ?_ ?_
  · show (sqRelWord (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4)).a = _
    simp only [SqU4.sqRelWord_a, sigTuple_one, sigTuple_two]
  · show (sqRelWord (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4)).b = _
    simp only [SqU4.sqRelWord_b, sigTuple_one, sigTuple_two]
  · show (sqRelWord (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4)).c = _
    simp only [SqU4.sqRelWord_c, sigTuple_one, sigTuple_two]
  · show (sqRelWord (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4)).d = _
    rw [SqU4.sqRelWord_d, SqU4.sqRelWord_d]
    simp only [sqHeisDefect]
    rw [sum_eq_at _ (fun j' hne => by rw [hUne j' hne, hVne j' hne]; simp),
      sum_eq_at _ (fun j' hne => by rw [hUne' j' hne, hVne' j' hne]; simp)]
    simp only [sigTuple_zero, sigTuple_one, sigTuple_two, sigTuple_handleU, sigTuple_handleV,
      SqU4.toHeisAB_apply, sigVal, sigU, sigV, SqU4.mul_a, SqU4.mul_b]
    ring
  · show (sqRelWord (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4)).e = _
    rw [SqU4.sqRelWord_e, SqU4.sqRelWord_e]
    simp only [sqHeisDefect]
    rw [sum_eq_at _ (fun j' hne => by rw [hUne j' hne, hVne j' hne]; simp),
      sum_eq_at _ (fun j' hne => by rw [hUne' j' hne, hVne' j' hne]; simp)]
    simp only [sigTuple_zero, sigTuple_one, sigTuple_two, sigTuple_handleU, sigTuple_handleV,
      SqU4.toHeisBC_apply, sigVal, sigU, sigV, SqU4.mul_b, SqU4.mul_c]
    ring
  · show (sqRelWord (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4)).f = _
    rw [SqU4.sqRelWord_f, SqU4.sqRelWord_f]
    simp only [sqU4Defect]
    rw [sum_eq_at _ (fun j' hne => by rw [hUne j' hne, hVne j' hne]; simp),
      sum_eq_at (fun j' => SqU4.u4Comm3
        (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4 (sqHandleIdxU j'))
        (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0 x1 x2 x3 x4 (sqHandleIdxV j')))
        (fun j' hne => by rw [hUne j' hne, hVne j' hne]; simp [SqU4.u4Comm3]),
      sum_eq_at _ (fun j' hne => by rw [hUne' j' hne, hVne' j' hne]; simp),
      sum_eq_at (fun j' => SqU4.u4Comm3
        (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0' x1 x2 x3 x4 (sqHandleIdxU j'))
        (sigTuple h j c A0 C0 A1 C1 A B C D P Q F x0' x1 x2 x3 x4 (sqHandleIdxV j')))
        (fun j' hne => by rw [hUne' j' hne, hVne' j' hne]; simp [SqU4.u4Comm3])]
    simp only [sigTuple_zero, sigTuple_one, sigTuple_two, sigTuple_handleU, sigTuple_handleV,
      sqU4Core, SqU4.u4Comm3, sigVal, sigU, sigV, sigRead, SqU4.mul_a, SqU4.mul_b,
      SqU4.mul_c, SqU4.mul_d, SqU4.mul_e, SqU4.mul_f]
    ring

set_option maxRecDepth 8000 in
/-- ⭐⭐ **The mod-2 decomposition of the sigma-reading** (the diagnosis): under the gates and
the odd pivot residue, `sigRead` is the four-block form plus an even remainder.  The blocks:
`kappaV = A1*(C0+D)` reads `x.v` and `x.u` against the deviation pair `(1 + y.u, y.v)`;
`kappa2s = A1*Q + C1*P` reads `x.w` and `x.u` against `(1 + y.u, y.w)`; the cross-coefficient
reads `(x.v, x.w)` against `(y.w, y.v)`; and `K1 = A0*C1 + A1*C0 + A1*D + B*C1` carries every
junk coupling.  **Every sigma-monomial has a factor from `(1 + y.u, y.v, y.w)` or `K1`**: the
class-two-forced `x0`-gauge is `y.u` odd, `y.v`, `y.w` even, so on it only the `K1`-block can
fire - and `K1` is the sound homs' vanishing functional. -/
theorem sigRead_decomp (c A0 C0 A1 C1 A B C D P Q h2 : gr3R) (x y : SelConDress)
    (hd : 2 * P + A = A1) (he : 2 * Q + C1 = C) (hc : c = 1 + 2 * h2) :
    ∃ k : gr3R, sigRead c A0 C0 A1 C1 A B C D P Q x y
      = A1 * (C0 + D) * (x.v * (1 + y.u) + x.u * y.v)
        + (A1 * Q + C1 * P) * (x.w * (1 + y.u) + x.u * y.w)
        + ((A0 + A1 + B) * Q + (C0 + C1 + D) * P) * (x.v * y.w + x.w * y.v)
        + (A0 * C1 + A1 * C0 + A1 * D + B * C1)
            * (x.s * (1 + y.u + y.v) + (x.r + x.t) * y.v + x.v * (y.r + y.s + y.t)
              + x.u * y.s)
        + 2 * k := by
  have hA : A = A1 - 2 * P := by linear_combination hd
  have hC : C = 2 * Q + C1 := by linear_combination -he
  subst hA hC hc
  simp only [sigRead]
  refine ⟨-A0 * C0 * x.s * y.v + A0 * C0 * y.s * x.v - A0 * C0 * x.v * y.v + A0 * C1 * h2 * x.s * y.v
    - A0 * C1 * h2 * y.s * x.v + 2 * A0 * C1 * h2 * x.v * y.v - A0 * C1 * y.r * x.v - A0 * C1 *
    y.s * x.u - A0 * C1 * y.s * x.v - A0 * C1 * x.t * y.v + A0 * C1 * y.u * x.v + A0 * C1 * x.v
    * y.v + A0 * C1 * x.v + A0 * D * x.s * y.v - A0 * D * y.s * x.v + A0 * D * x.v * y.v + A0 *
    Q * x.s * y.u - A0 * Q * y.s * x.u - A0 * Q * x.t * y.v + A0 * Q * y.t * x.v + 2 * A0 * Q *
    y.u * x.v - A0 * Q * x.v * y.w + A1 * C0 * h2 * x.s * y.v - A1 * C0 * h2 * y.s * x.v + 2 *
    A1 * C0 * h2 * x.v * y.v - A1 * C0 * y.r * x.v - A1 * C0 * y.s * x.u - A1 * C0 * y.s * x.v -
    A1 * C0 * x.t * y.v + A1 * C0 * x.v * y.v - 4 * A1 * C1 * h2^2 * x.v * y.v - 2 * A1 * C1 *
    h2 * x.r * y.v + 2 * A1 * C1 * h2 * y.r * x.v + 2 * A1 * C1 * h2 * x.t * y.v - 2 * A1 * C1 *
    h2 * y.t * x.v - 4 * A1 * C1 * h2 * y.u * x.v - 4 * A1 * C1 * h2 * x.v * y.v - 4 * A1 * C1 *
    h2 * x.v - A1 * C1 * x.r * y.u - A1 * C1 * x.r * y.v - A1 * C1 * x.r + A1 * C1 * y.r * x.u +
    A1 * C1 * y.r * x.v + A1 * C1 * x.t * y.u + A1 * C1 * x.t * y.v + A1 * C1 * x.t - A1 * C1 *
    y.t * x.u - A1 * C1 * y.t * x.v - A1 * C1 * x.u * y.u - A1 * C1 * x.u - 2 * A1 * C1 * y.u *
    x.v - A1 * C1 * x.v * y.v - 2 * A1 * C1 * x.v - A1 * D * h2 * x.s * y.v + A1 * D * h2 * y.s
    * x.v - 2 * A1 * D * h2 * x.v * y.v - A1 * D * x.r * y.v - A1 * D * x.s * y.u - A1 * D * x.s
    * y.v - A1 * D * x.s - A1 * D * y.t * x.v - A1 * D * x.u * y.v - A1 * D * y.u * x.v - A1 * D
    * x.v * y.v - A1 * D * x.v + 2 * A1 * Q * h2 * x.t * y.v - 2 * A1 * Q * h2 * y.t * x.v - 4 *
    A1 * Q * h2 * y.u * x.v + A1 * Q * h2 * x.v * y.w - A1 * Q * h2 * y.v * x.w - A1 * Q * x.r *
    y.u + A1 * Q * y.r * x.u + 2 * A1 * Q * x.t * y.u + A1 * Q * x.t * y.v + A1 * Q * x.t - 2 *
    A1 * Q * y.t * x.u - A1 * Q * y.t * x.v - 2 * A1 * Q * x.u * y.u - A1 * Q * x.u - 2 * A1 * Q
    * y.u * x.v - A1 * Q * y.u * x.w - A1 * Q * y.v * x.w - A1 * Q * x.w + B * C0 * x.s * y.v -
    B * C0 * y.s * x.v + B * C0 * x.v * y.v - B * C1 * h2 * x.s * y.v + B * C1 * h2 * y.s * x.v
    - 2 * B * C1 * h2 * x.v * y.v - B * C1 * x.r * y.v - B * C1 * x.s * y.u - B * C1 * x.s * y.v
    - B * C1 * x.s - B * C1 * y.t * x.v - B * C1 * y.u * x.v - B * C1 * x.v * y.v - B * C1 * x.v
    - B * D * x.s * y.v + B * D * y.s * x.v - B * D * x.v * y.v - B * Q * x.s * y.u + B * Q *
    y.s * x.u + B * Q * x.t * y.v - B * Q * y.t * x.v - 2 * B * Q * y.u * x.v - B * Q * y.v *
    x.w - C0 * P * x.s * y.u + C0 * P * y.s * x.u + C0 * P * x.t * y.v - C0 * P * y.t * x.v - C0
    * P * x.u * y.v - C0 * P * y.u * x.v - C0 * P * y.v * x.w - 2 * C1 * P * h2 * x.t * y.v + 2
    * C1 * P * h2 * y.t * x.v + 4 * C1 * P * h2 * y.u * x.v - C1 * P * h2 * x.v * y.w + C1 * P *
    h2 * y.v * x.w + C1 * P * x.r * y.u - C1 * P * y.r * x.u - 2 * C1 * P * x.t * y.u - C1 * P *
    x.t * y.v - C1 * P * x.t + 2 * C1 * P * y.t * x.u + C1 * P * y.t * x.v + 2 * C1 * P * x.u *
    y.u - C1 * P * x.u * y.w + C1 * P * x.u + 2 * C1 * P * y.u * x.v - C1 * P * x.v * y.w + D *
    P * x.s * y.u - D * P * y.s * x.u - D * P * x.t * y.v + D * P * y.t * x.v + D * P * x.u *
    y.v + D * P * y.u * x.v - D * P * x.v * y.w - 4 * P * Q * x.t * y.u + 4 * P * Q * y.t * x.u
    + 4 * P * Q * x.u * y.u - 2 * P * Q * x.u * y.w + 2 * P * Q * y.u * x.w, ?_⟩
  ring

set_option maxRecDepth 8000 in
/-- ⭐⭐ **Blindness on the class-two-forced gauge** (the negative headline): whenever the
`x0`-slot datum is in the forced gauge - `y.u` odd, `y.v` and `y.w` even, the parities of the
committed forced value `U^{-1}` - and the hom is sound (`K1` even), the wider slice reads
**every** sigma-slot datum evenly: no relator verdict at any such hom can separate two
sigma-dressings.  The `k1`-cancellation of the committed family, one level deeper. -/
theorem sigRead_gauge_even (c A0 C0 A1 C1 A B C D P Q h2 : gr3R) (x y : SelConDress)
    (hd : 2 * P + A = A1) (he : 2 * Q + C1 = C) (hc : c = 1 + 2 * h2)
    {ya yb yc k1 : gr3R} (hyu : y.u = 1 + 2 * ya) (hyv : y.v = 2 * yb) (hyw : y.w = 2 * yc)
    (hK1 : A0 * C1 + A1 * C0 + A1 * D + B * C1 = 2 * k1) :
    ∃ k : gr3R, sigRead c A0 C0 A1 C1 A B C D P Q x y = 2 * k := by
  obtain ⟨k, hk⟩ := sigRead_decomp c A0 C0 A1 C1 A B C D P Q h2 x y hd he hc
  refine ⟨A1 * (C0 + D) * (x.v * (1 + ya) + x.u * yb)
    + (A1 * Q + C1 * P) * (x.w * (1 + ya) + x.u * yc)
    + ((A0 + A1 + B) * Q + (C0 + C1 + D) * P) * (x.v * yc + x.w * yb)
    + k1 * (x.s * (1 + y.u + y.v) + (x.r + x.t) * y.v + x.v * (y.r + y.s + y.t) + x.u * y.s)
    + k, ?_⟩
  linear_combination hk
    + (A1 * (C0 + D) * x.v + (A1 * Q + C1 * P) * x.w) * hyu
    + (A1 * (C0 + D) * x.u + ((A0 + A1 + B) * Q + (C0 + C1 + D) * P) * x.w) * hyv
    + ((A1 * Q + C1 * P) * x.u + ((A0 + A1 + B) * Q + (C0 + C1 + D) * P) * x.v) * hyw
    + (x.s * (1 + y.u + y.v) + (x.r + x.t) * y.v + x.v * (y.r + y.s + y.t) + x.u * y.s) * hK1

/-- The F2 core of the family-wide blindness, `u`- and `v`-channels: the `F`-gate and `K1`
evenness alone kill the readings `kappaV * v1 + K1 * s1` and `kappaV * (1 + u1)`. -/
private theorem sigPar_core_uv : ∀ a0 c0 a1 c1 b d u1 v1 s1 : ZMod 2,
    c1 * (a0 + b) = 0 → a0 * c1 + a1 * c0 + a1 * d + b * c1 = 0 →
    a1 * (c0 + d) * v1 + (a0 * c1 + a1 * c0 + a1 * d + b * c1) * s1 = 0 ∧
    a1 * (c0 + d) * (1 + u1) = 0 := by
  decide

/-- ...and the `w`-channel: with the two admissibility parities, the `F`-gate and `K1`
evenness, the reading `kappa2s * (1 + u1) + kappaW * v1` dies as well - the junk functionals
`K5`, `K6` are not even needed. -/
private theorem sigPar_core_w : ∀ a0 c0 a1 c1 b d p q u1 v1 : ZMod 2,
    c1 * (a0 + b) = 0 → a1 * (1 + u1) + (b + a0 + a1) * v1 = 0 →
    c1 * (1 + u1) + (d + c0 + c1) * v1 = 0 → a0 * c1 + a1 * c0 + a1 * d + b * c1 = 0 →
    (a1 * q + c1 * p) * (1 + u1) + ((a0 + a1 + b) * q + (c0 + c1 + d) * p) * v1 = 0 := by
  decide

/-- ⭐⭐ **The family-wide blindness with the exact hypotheses** (the refutation deliverable's
diagnosis, decided): at every binder point of the wider family that is realizable (the
`F`-gate parity) and sound for the sigma-slot junk (`K1` even - otherwise the junk move on
the `[sigma, V]`-generator flips the bit and the hom pins nothing), on every
class-two-admissible `x0`-slot datum (the two parities `P1`, `P2`) with even `t`-component,
all three sigma-reading channels of `sigRead_decomp` are even: the `u`-channel
`kappaV*v1 + K1*s1`, the `v`-channel `kappaV*(1 + u1)`, and the `w`-channel
`kappa2s*(1 + u1) + kappaW*v1`.  **No sound realizable hom of the wider family decides any
sigma-coordinate on the admissible locus with `w1` even.**  The one open channel is `w1`
odd - the escape of paragraph 6. -/
theorem sigPar_sound_blind {a0 c0 a1 c1 b d p q u1 v1 s1 : ZMod 2}
    (hF : c1 * (a0 + b) = 0) (hP1 : a1 * (1 + u1) + (b + a0 + a1) * v1 = 0)
    (hP2 : c1 * (1 + u1) + (d + c0 + c1) * v1 = 0)
    (hK1 : a0 * c1 + a1 * c0 + a1 * d + b * c1 = 0) :
    a1 * (c0 + d) * v1 + (a0 * c1 + a1 * c0 + a1 * d + b * c1) * s1 = 0 ∧
    a1 * (c0 + d) * (1 + u1) = 0 ∧
    (a1 * q + c1 * p) * (1 + u1) + ((a0 + a1 + b) * q + (c0 + c1 + d) * p) * v1 = 0 :=
  ⟨(sigPar_core_uv a0 c0 a1 c1 b d u1 v1 s1 hF hK1).1,
    (sigPar_core_uv a0 c0 a1 c1 b d u1 v1 s1 hF hK1).2,
    sigPar_core_w a0 c0 a1 c1 b d p q u1 v1 hF hP1 hP2 hK1⟩

/-- ⭐ **The committed family can never read the `m0`-coordinate when its two even
coefficients vanish**: `selConForm` with `kappa1 = kappa2 = 0` does not depend on `m0`.  At
every hom of the committed family `kappa1` is even outright (`selConKappa1_even`) and at the
canonical row type `kappa2` is even too (`selConKappa2_even01`), so the committed family is
`m0`-blind at type `(0, 1)` - which is exactly the coordinate the escape instance of
paragraph 6 separates. -/
theorem selConForm_m0_blind (k3 m0 m0' n0 m1 n1 k1 m3 n3 kk3 m4 n4 k4 : ZMod 2) :
    selConForm 0 0 k3 m0 n0 m1 n1 k1 m3 n3 kk3 m4 n4 k4
      = selConForm 0 0 k3 m0' n0 m1 n1 k1 m3 n3 kk3 m4 n4 k4 := by
  simp only [selConForm]
  ring

end ReadOut

end SqCore

end Dyadic

end GQ2
