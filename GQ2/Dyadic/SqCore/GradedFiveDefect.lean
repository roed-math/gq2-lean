/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFive

/-!
# W59-DEFECT5: the class-five defect closed form, and the class-five translation identity

`GradedFour` deferred the closed form of its own top row (`sqU5Defect`), on the ground that
the stage engine reached every row it needed through the two `U_4`-quotients and that a
self-standing form "earns its keep only when a wave needs the class-four gate at arbitrary
markings".  `GradedFive` deferred the class-five analogue `sqU6Defect` for the same stated
reason: the fourteen lower rows go through the two `U_5`-quotients and the top row does not.
Two carriers, one deferral.  This file discharges it at every handle count over any
commutative ring, discharges the class-four one as a corollary, and then spends the result on
what the deferral was blocking: the **class-five translation identity**, without which no
class-five analogue of `GradedContainFour`'s containment or `GradedGammaTwo`'s transport can
even be stated.

Every closed form was derived with exact integer arithmetic (`scripts/w59_defect5/`,
`derive_defect5.py`, `derive_transport.py`, `emit_lean.py`) and cross-validated against honest
`6 x 6` group collection before transcription (`validate_defect5.py`: **59400 comparisons,
zero mismatches**, over `ℤ`, `ZMod 4`, `ZMod 8` and `ZMod 16`, at handle counts `0` to `4`, at
dense, wide-range and sparse markings), plus **24** named structural checks in the derivation
and **19** in the transport.

## Headline 1: the closed form, and why it needed a new object

```text
(sqRelWord m).o = -4 * (m 1).o + 2 * (m 2).o + sqU6Defect h m           (SqU6.sqRelWord_o_defect)
(sqRelWord m).m = -4 * (m 1).m + 2 * (m 2).m + sqU6Defect4 h m          (SqU6.sqRelWord_m_defect)
```

`sqU6Defect` has five pieces, and it is `sqU4Defect`'s shape two classes up: the core word's
own class-five content `sqU6Core` (**248** terms, degree `5`, derived not typed), then the
three couplings `GradedFive`'s `sqRelWord_o` named, each a row of the core word against a
coordinate of the handle block, and then the handle block's own class-five coordinate.  The
coupling that has no class-four analogue is the third, the core word's **class-three** row
against the handle block's outermost class-two pairing.

⚠ **The obstacle that made this a deferral is real and it is not the top row's size.**
`gamma_2` is abelian through class three, so at class three the handle block is a plain sum
over the handles.  At class four and five it is not: `SqU6.handleWord_m` and
`SqU6.handleWord_o` carry a **strictly triangular cross-handle pairing** `sqCross`, absent at
`h <= 1` and unavoidable above.  A closed form of the shape "sum over handles" is therefore
false at class five, and ⭐⭐ `SqU6.handleWord_o_ne_sum` certifies it: at an explicit two-handle
point over `ZMod 8` the block differs from the sum of the per-handle class-five commutator
forms.  ⭐⭐ `SqU6.handleWord_o_order_dependent` sharpens it: the same two handle pairs in the
two possible orders have equal per-handle forms (`SqU6.u6Comm5_crossUV_swap`) and **different**
blocks, so the block is not even a function of the multiset of handle pairs.  The class-four
row does the same (`SqU6.handleWord_m_ne_sum`, `_order_dependent`), which is exactly the
"cross-handle coupling" `GradedFour`'s scope note recorded and did not close.

## Headline 2: what the closed form immediately buys

* ⭐ `SqU6.sqRelWord_eq_one_iff`: the relator dies in the class-five carrier iff it dies in
  both `U_5`-quotients and the class-five defect equation holds.  The fourteen-plus-one split
  the carrier file described, as an iff.
* ⭐ `sqU6Defect_balance`: the class-five defect equation is a **gate** at an arbitrary
  marking, the class-five `sqU4Balance`.
* ⭐⭐ `SqU6.sqRelWord_o_shift`: the relator's class-five row sees the marking's class-five
  coordinates **only** through slots `1` and `2`, with weights `-4` and `2`; the sigma slot's
  and every handle slot's class-five coordinate cancels outright, and the range along the
  central torsor is exactly `2R` (`SqU6.sqRelWord_o_range`, `_shift_even`).  This is
  `GradedThree`'s `sqU4_top_adjust`/`sqU4_top_range` two classes up.
* ⭐⭐ `sqU5Defect` and `SqU5.sqRelWord_j_defect`: `GradedFour`'s own deferral, discharged.
  The class-four carrier embeds in the class-five one as the first five columns
  (`SqU5.toU6`, split by `toU5L`), so the class-four defect is the class-five carrier's
  class-four defect at the embedded marking, with a gate corollary `sqU5Defect_balance`.

## ⭐⭐ Headline 3: the class-five translation identity, and it transposes verbatim

A five-slot `gamma_4`-dressing moves the relator by an explicit `gamma_4`-element:

```text
sqRelWord (m . z) = sqRelWord m
  * <0,...,0, -4 z_1.m + 2 z_2.m, -4 z_1.n + 2 z_2.n, -4 z_1.o + 2 z_2.o + conFiveShift h m z>
```

(`SqU6.sqRelWord_conFiveDress`), with every class-`<= 3` row untouched, the two class-four rows
moving by the Frobenius weights alone, and the class-five row by the Frobenius part, the graded
Fox form `conFiveShift`, and the relator's own abelian row against the dressing's Frobenius
`n`-row (`SqU6.sqRelWord_conFiveDress_o`).  At a relator-solution the dressed relator **is**
the translation element (`SqU6.sqRelWord_conFiveDress_of_rel`), so the class-five defect of a
`K`-dressed solution is a pure dressing artefact, and the dressing torsor is a torsor
(`conFiveDress_conFiveDress_inv`).

⭐ **`conFiveShift` is `GradedContainFour`'s `conFourShift` verbatim**, with the class-three
data `(h, i)` replaced by the class-four data `(m, n)` and the outermost abelian column `d`
replaced by `e`: the sigma slot pairs against the `x0`-letter, the `x0`-slot against
`10 x0 - sigma - 8 x1`, the `x1`-slot against itself, and each handle against the opposite
handle letter.  The extra cross term is the exact analogue of the one
`sqRelWord_conFourDress_j` carries.  **Nothing new in shape appears at class five; what was
missing was the carrier and the defect, not the shape.**

## Refutation and consistency sweep (doctrine iv)

* ⭐ **Against the committed class-four transport.**  The derivation re-derives
  `GradedContainFour`'s class-four identity with the same machinery, through the left
  `U_5`-quotient, at `h = 0, 1, 2, 3`: it reproduces `conFourShift` **and** the cross term of
  `sqRelWord_conFourDress_j` exactly.  Transcribing that theorem without its cross term leaves
  a residual of precisely `(-4 (z 1).i + 2 (z 2).i) * (-4 (m 1).a + 2 (m 2).a)`, which is the
  cross term; so the two agree and the committed statement is confirmed independently
  (`scripts/w59_defect5/results/transport.txt`).
* ⭐ **Against the committed class-three and class-two core rows.**  The derivation checks
  `sqWord.f` against `SqU6.sqWord_f` and `sqWord.j` against `GradedThree`'s `sqU4Core` through
  `toU4LL`, both exactly.
* ⚠ **Against wave 58's reconciliation, which this file must not overstate.**  W58 concluded
  that the structural cancellation ends at class five but that an arithmetic evenness keeps the
  handle block invisible at relator-killing markings through class seven.  **Nothing here
  claims visibility.**  `sqU6Defect` is a closed form, not a forcing statement: it exhibits the
  coupling `core.j * H.i` that `GradedFive` found, and says nothing about whether it is odd at
  any relator-killing marking.  The cross-handle certificates are about the handle **block**,
  at a marking that is not claimed to kill the relator.
* **Against `GradedThree`'s class-three range statements.**  `SqU6.sqRelWord_o_range` gives
  exactly `2R` along the central torsor, matching `sqU4_top_range` one level down; no sharper
  range is claimed, and the class-five obstruction lives in `R / 2R` as at every lower class.

## PROVED versus measured versus deferred

**PROVED**, with no live hypothesis: the whole file.  The handle block's ten non-abelian
coordinates in closed form at every handle count, the two new core-word rows, both defects,
the fifteen-row iff, both gates, the adjustable set and its range, the class-four defect on the
class-four carrier, the whole `gamma_4` calculus and the translation identity with its four row
corollaries, and the cross-handle certificates.

**Measured, not proved** (`scripts/w59_defect5/results/`): the closed forms against honest
`6 x 6` collection (59400 comparisons, zero mismatches); the generic-marking symbolic checks at
`h = 0, 1, 2, 3`; the handle-block closed form at `h = 0` to `4`; the uniform transport form at
`h = 0` to `3`; the class-four cross-check against the committed `conFourShift`.

**Deferred**, and named: the class-five containment through an engine (this file supplies the
translation identity, not a move lattice, and there is no class-five analogue of
`selLamThree`); the `gamma_3`- and `gamma_2`-level transports at class five, whose defect
shifts are quadratic and not covered by the affine calculus here; any statement about whether
the class-five coupling is odd at a relator-killing marking, which is wave 58's arithmetic
question and is untouched.

## Contents

* **1** `sqCross` and the handle block at class five: the ten non-abelian coordinates in
  closed form, ⭐⭐ `SqU6.handleWord_o` with two triangular cross-handle pairings;
* **2** the two genuinely new core-word rows, ⭐⭐ `SqU6.sqWord_o` (248 terms);
* **3** ⭐⭐ `sqU6Defect`, `sqU6Defect4`, the closed relator rows, the fifteen-row iff and the
  gate;
* **4** the central torsor: ⭐⭐ the adjustable set and its range, and the `h <= 1` collapses;
* **5** ⭐⭐ the `gamma_4` calculus and the class-five translation identity;
* **6** ⭐⭐ the cross-handle certified negatives;
* **7** ⭐⭐ the class-four defect on the class-four carrier, `GradedFour`'s deferral;
* **8** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`.  All **84**
committed prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a subset; no
census axiom is reachable.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The handle block at class five, and the cross-handle pairing -/

section HandleBlock

variable {R : Type} [CommRing R] {h : ℕ}

/-- **The strictly triangular cross pairing** of two handle-indexed families,
`∑_{s < t} x s * y t`.

This is the object the class-four and class-five handle blocks need and no lower class does.
`gamma_2` is abelian through class three, so the handle block's class-`<= 3` coordinates are
plain sums over the handles; at class four and five it is not, and the deficit is exactly this
form.  It is **not** symmetric, it depends on the ORDER of the handles, and it vanishes at
`h <= 1` (`sqCross_zero`, `sqCross_one`). -/
def sqCross {h : ℕ} (x y : Fin h → R) : R :=
  ∑ t : Fin h, ∑ s : Fin h, if (s : ℕ) < (t : ℕ) then x s * y t else 0

@[simp] theorem sqCross_zero (x y : Fin 0 → R) : sqCross x y = 0 := by
  simp [sqCross]

@[simp] theorem sqCross_one (x y : Fin 1 → R) : sqCross x y = 0 := by
  simp [sqCross]

/-- The recursion the handle block's induction runs on: peeling the first handle. -/
theorem sqCross_succ (x y : Fin (h + 1) → R) :
    sqCross x y = x 0 * (∑ t : Fin h, y t.succ)
      + sqCross (fun s => x s.succ) (fun t => y t.succ) := by
  simp only [sqCross, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.not_lt_zero, if_false,
    Finset.sum_const_zero, Nat.succ_lt_succ_iff, Nat.zero_lt_succ, if_true, zero_add,
    Finset.mul_sum, ← Finset.sum_add_distrib]

/-- At two handles the pairing is the single product `x 0 * y 1`. -/
theorem sqCross_two (x y : Fin 2 → R) : sqCross x y = x 0 * y 1 := by
  rw [sqCross_succ]
  simp

/-- Peeling the first handle off the handle word. -/
theorem handleWord_succ {G : Type*} [Group G] (u v : Fin (h + 1) → G) :
    handleWord u v
      = commP (u 0) (v 0) * handleWord (fun j => u j.succ) (fun j => v j.succ) := by
  rw [handleWord, handleWord, List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
  rfl

/-- The handle block's first class-two coordinate: the sum of the `(a, b)`-pairings. -/
def sqU6BlockF (u v : Fin h → SqU6 R) : R :=
  ∑ j, ((u j).a * (v j).b - (v j).a * (u j).b)

/-- …the second, on the `(b, c)`-columns. -/
def sqU6BlockG (u v : Fin h → SqU6 R) : R :=
  ∑ j, ((u j).b * (v j).c - (v j).b * (u j).c)

/-- …the third, on the `(c, d)`-columns: the one the class-four top row meets. -/
def sqU6BlockH (u v : Fin h → SqU6 R) : R :=
  ∑ j, ((u j).c * (v j).d - (v j).c * (u j).d)

/-- …and the fourth, on the `(d, e)`-columns: the one the class-five top row meets, and the
functional wave 57 said class four does not have. -/
def sqU6BlockI (u v : Fin h → SqU6 R) : R :=
  ∑ j, ((u j).d * (v j).e - (v j).d * (u j).e)

/-- The handle block's left class-three coordinate. -/
def sqU6BlockJ (u v : Fin h → SqU6 R) : R := ∑ j, SqU6.u6Comm3L (u j) (v j)

/-- The handle block's middle class-three coordinate. -/
def sqU6BlockK (u v : Fin h → SqU6 R) : R := ∑ j, SqU6.u6Comm3M (u j) (v j)

/-- The handle block's right class-three coordinate: the one the class-five top row meets
through the core word's class-two row. -/
def sqU6BlockL (u v : Fin h → SqU6 R) : R := ∑ j, SqU6.u6Comm3R (u j) (v j)

/-- ⭐ **The handle block's first class-four coordinate**: the per-handle class-four commutator
forms **plus** a strictly triangular cross-handle pairing.  This is the coupling `GradedFour`'s
scope note recorded and did not close: distinct handles interact from class four upwards. -/
def sqU6BlockM (u v : Fin h → SqU6 R) : R :=
  ∑ j, SqU6.u6Comm4L (u j) (v j)
    + sqCross (fun j => (u j).a * (v j).b - (v j).a * (u j).b)
        (fun j => (u j).c * (v j).d - (v j).c * (u j).d)

/-- …and the second, with the `(b, c)`- and `(d, e)`-pairings. -/
def sqU6BlockN (u v : Fin h → SqU6 R) : R :=
  ∑ j, SqU6.u6Comm4R (u j) (v j)
    + sqCross (fun j => (u j).b * (v j).c - (v j).b * (u j).c)
        (fun j => (u j).d * (v j).e - (v j).d * (u j).e)

/-- ⭐⭐ **The handle block's class-five coordinate**: the per-handle class-five commutator forms
plus **two** triangular cross-handle pairings, the earlier handles' class-two `(a, b)`-pairings
against the later ones' right class-three forms, and the earlier handles' left class-three forms
against the later ones' class-two `(d, e)`-pairings.  Class four has one such pairing, class
three none. -/
def sqU6BlockO (u v : Fin h → SqU6 R) : R :=
  ∑ j, SqU6.u6Comm5 (u j) (v j)
    + sqCross (fun j => (u j).a * (v j).b - (v j).a * (u j).b)
        (fun j => SqU6.u6Comm3R (u j) (v j))
    + sqCross (fun j => SqU6.u6Comm3L (u j) (v j))
        (fun j => (u j).d * (v j).e - (v j).d * (u j).e)

theorem SqU6.handleWord_f (u v : Fin h → SqU6 R) :
    (handleWord u v).f = sqU6BlockF u v := by
  induction h with
  | zero => simp [sqU6BlockF]
  | succ h ih =>
    rw [handleWord_succ, SqU6.mul_f, SqU6.commP_a, zero_mul, add_zero, SqU6.commP_f, ih,
      sqU6BlockF, sqU6BlockF, Fin.sum_univ_succ]
    ring

theorem SqU6.handleWord_g (u v : Fin h → SqU6 R) :
    (handleWord u v).g = sqU6BlockG u v := by
  induction h with
  | zero => simp [sqU6BlockG]
  | succ h ih =>
    rw [handleWord_succ, SqU6.mul_g, SqU6.commP_b, zero_mul, add_zero, SqU6.commP_g, ih,
      sqU6BlockG, sqU6BlockG, Fin.sum_univ_succ]
    ring

theorem SqU6.handleWord_h (u v : Fin h → SqU6 R) :
    (handleWord u v).h = sqU6BlockH u v := by
  induction h with
  | zero => simp [sqU6BlockH]
  | succ h ih =>
    rw [handleWord_succ, SqU6.mul_h, SqU6.commP_c, zero_mul, add_zero, SqU6.commP_h, ih,
      sqU6BlockH, sqU6BlockH, Fin.sum_univ_succ]
    ring

/-- The committed `SqU6.handleWord_i`, in the `sqU6BlockI` packaging. -/
theorem SqU6.handleWord_blockI (u v : Fin h → SqU6 R) :
    (handleWord u v).i = sqU6BlockI u v := SqU6.handleWord_i u v

theorem SqU6.handleWord_j (u v : Fin h → SqU6 R) :
    (handleWord u v).j = sqU6BlockJ u v := by
  induction h with
  | zero => simp [sqU6BlockJ]
  | succ h ih =>
    rw [handleWord_succ, SqU6.mul_j, SqU6.commP_a, zero_mul, add_zero, SqU6.handleWord_c,
      mul_zero, add_zero, SqU6.commP_j, ih, sqU6BlockJ, sqU6BlockJ, Fin.sum_univ_succ]

theorem SqU6.handleWord_k (u v : Fin h → SqU6 R) :
    (handleWord u v).k = sqU6BlockK u v := by
  induction h with
  | zero => simp [sqU6BlockK]
  | succ h ih =>
    rw [handleWord_succ, SqU6.mul_k, SqU6.commP_b, zero_mul, add_zero, SqU6.handleWord_d,
      mul_zero, add_zero, SqU6.commP_k, ih, sqU6BlockK, sqU6BlockK, Fin.sum_univ_succ]

theorem SqU6.handleWord_l (u v : Fin h → SqU6 R) :
    (handleWord u v).l = sqU6BlockL u v := by
  induction h with
  | zero => simp [sqU6BlockL]
  | succ h ih =>
    rw [handleWord_succ, SqU6.mul_l, SqU6.commP_c, zero_mul, add_zero, SqU6.handleWord_e,
      mul_zero, add_zero, SqU6.commP_l, ih, sqU6BlockL, sqU6BlockL, Fin.sum_univ_succ]

/-- ⭐ **The handle block's class-four coordinate in closed form**, at every handle count. -/
theorem SqU6.handleWord_m (u v : Fin h → SqU6 R) :
    (handleWord u v).m = sqU6BlockM u v := by
  induction h with
  | zero => simp [sqU6BlockM]
  | succ h ih =>
    rw [handleWord_succ, SqU6.mul_m, SqU6.commP_a, zero_mul, add_zero, SqU6.handleWord_d,
      mul_zero, add_zero, SqU6.commP_m, ih, SqU6.handleWord_h, SqU6.commP_f,
      sqU6BlockM, sqU6BlockM, sqU6BlockH, Fin.sum_univ_succ, sqCross_succ]
    ring

theorem SqU6.handleWord_n (u v : Fin h → SqU6 R) :
    (handleWord u v).n = sqU6BlockN u v := by
  induction h with
  | zero => simp [sqU6BlockN]
  | succ h ih =>
    rw [handleWord_succ, SqU6.mul_n, SqU6.commP_b, zero_mul, add_zero, SqU6.handleWord_e,
      mul_zero, add_zero, SqU6.commP_n, ih, SqU6.handleWord_blockI, SqU6.commP_g,
      sqU6BlockN, sqU6BlockN, sqU6BlockI, Fin.sum_univ_succ, sqCross_succ]
    ring

/-- ⭐⭐ **The handle block's class-five coordinate in closed form**, at every handle count.
Two carriers deferred this; it is the first ingredient of the class-five defect. -/
theorem SqU6.handleWord_o (u v : Fin h → SqU6 R) :
    (handleWord u v).o = sqU6BlockO u v := by
  induction h with
  | zero => simp [sqU6BlockO]
  | succ h ih =>
    rw [handleWord_succ, SqU6.mul_o, SqU6.commP_a, zero_mul, add_zero, SqU6.handleWord_e,
      mul_zero, add_zero, SqU6.commP_o, ih, SqU6.handleWord_l, SqU6.handleWord_blockI,
      SqU6.commP_f, SqU6.commP_j, sqU6BlockO, sqU6BlockO, sqU6BlockL, sqU6BlockI,
      Fin.sum_univ_succ, sqCross_succ, sqCross_succ]
    ring

end HandleBlock

/-! ## 2 The two genuinely new rows of the core word -/

section CoreWord

variable {R : Type} [CommRing R]

private theorem chooseTwoTwo : Nat.choose 2 2 = 1 := rfl
private theorem chooseTwoThree : Nat.choose 2 3 = 0 := rfl
private theorem chooseTwoFour : Nat.choose 2 4 = 0 := rfl
private theorem chooseTwoFive : Nat.choose 2 5 = 0 := rfl
private theorem chooseThreeTwo : Nat.choose 3 2 = 3 := rfl
private theorem chooseThreeThree : Nat.choose 3 3 = 1 := rfl
private theorem chooseThreeFour : Nat.choose 3 4 = 0 := rfl
private theorem chooseThreeFive : Nat.choose 3 5 = 0 := rfl

/-- The class-two content of the core word, `SqU6.sqWord_f`'s bracket, named. -/
def sqU6CoreTwo (s x y : SqU6 R) : R :=
  s.a * x.b - s.b * x.a + 10 * (x.a * x.b) - 8 * (x.a * y.b) + y.a * y.b

theorem SqU6.sqWord_f_core (s x y : SqU6 R) :
    (sqWord s x y).f = -4 * x.f + 2 * y.f + sqU6CoreTwo s x y := SqU6.sqWord_f s x y

/-- ⭐ **The class-four content of the core word**: `79` terms, degree `4`, reading the three
core slots' coordinates up to class three and no slot's own class-four coordinate.  Derived with
exact integer arithmetic (`scripts/w59_defect5/derive_defect5.py`) and validated against honest
`6 x 6` collection before transcription. -/
def sqU6Core4 (s x y : SqU6 R) : R :=
    s.a * x.k - s.d * x.j + s.f * x.h - s.h * x.f + s.j * x.d - s.k * x.a + 10 * (x.a * x.k)
      - 8 * (x.a * y.k) + 10 * (x.d * x.j) + 10 * (x.f * x.h) - 8 * (x.f * y.h)
      - 8 * (x.j * y.d) + y.a * y.k + y.d * y.j + y.f * y.h - s.a * s.b * x.h + s.a * s.d * x.g
      - s.a * s.g * x.d + s.a * s.h * x.b - 4 * (s.a * x.b * x.h) + 2 * (s.a * x.b * y.h)
      - 4 * (s.a * x.d * x.g) + 2 * (s.a * x.g * y.d) + s.a * y.b * y.h + s.a * y.d * y.g
      + 3 * (s.b * x.a * x.h) - 2 * (s.b * x.a * y.h) - 2 * (s.b * y.a * y.h) - s.c * s.f * x.d
      + 3 * (s.c * x.d * x.f) - 2 * (s.c * x.f * y.d) - 2 * (s.c * y.d * y.f) + s.d * s.f * x.c
      + s.d * x.a * x.g + s.d * x.c * x.f + s.d * y.a * y.g + s.d * y.c * y.f
      - 4 * (s.f * x.c * x.d) + 2 * (s.f * x.c * y.d) + s.f * y.c * y.d + 3 * (s.g * x.a * x.d)
      - 2 * (s.g * x.a * y.d) - 2 * (s.g * y.a * y.d) + s.h * x.a * x.b + s.h * y.a * y.b
      - 20 * (x.a * x.b * x.h) + 20 * (x.a * x.b * y.h) - 20 * (x.a * x.d * x.g)
      + 20 * (x.a * x.g * y.d) - 4 * (x.a * y.b * y.h) - 4 * (x.a * y.d * y.g)
      - 20 * (x.c * x.d * x.f) + 20 * (x.c * x.f * y.d) - 4 * (x.f * y.c * y.d)
      + s.a * s.b * s.c * x.d - s.a * s.b * s.d * x.c + 4 * (s.a * s.b * x.c * x.d)
      - 2 * (s.a * s.b * x.c * y.d) - s.a * s.b * y.c * y.d - 3 * (s.a * s.c * x.b * x.d)
      + 2 * (s.a * s.c * x.b * y.d) + s.a * s.c * y.b * y.d - s.a * s.d * x.b * x.c
      + 10 * (s.a * x.b * x.c * x.d) - 8 * (s.a * x.b * x.c * y.d) + s.a * x.b * y.c * y.d
      + s.b * s.c * y.a * y.d - s.b * s.d * y.a * y.c - 6 * (s.b * x.a * x.c * x.d)
      + 6 * (s.b * x.a * x.c * y.d) - 5 * (s.b * x.a * y.c * y.d) - 3 * (s.c * x.a * x.b * x.d)
      + 2 * (s.c * x.a * x.b * y.d) + 8 * (s.c * x.a * y.b * y.d) - s.d * x.a * x.b * x.c
      - 4 * (s.d * x.a * y.b * y.c) + 35 * (x.a * x.b * x.c * x.d)
      - 40 * (x.a * x.b * x.c * y.d) + 10 * (x.a * x.b * y.c * y.d)

/-- ⭐⭐ **The class-five content of the core word**: `248` terms, degree `5`.  It reads the
three core slots' coordinates up to class **four** and no slot's own class-five coordinate; in
particular it reads `s.m` and `s.n`, which has no class-three analogue, because conjugation
moves the top row by `g.n * p.a - g.m * p.e`. -/
def sqU6Core (s x y : SqU6 R) : R :=
    s.a * x.n - s.e * x.m + s.f * x.l - s.i * x.j + s.j * x.i - s.l * x.f + s.m * x.e
      - s.n * x.a + 10 * (x.a * x.n) - 8 * (x.a * y.n) + 10 * (x.e * x.m) + 10 * (x.f * x.l)
      - 8 * (x.f * y.l) + 10 * (x.i * x.j) - 8 * (x.j * y.i) - 8 * (x.m * y.e) + y.a * y.n
      + y.e * y.m + y.f * y.l + y.i * y.j - s.a * s.b * x.l + s.a * s.e * x.k - s.a * s.g * x.i
      + s.a * s.i * x.g - s.a * s.k * x.e + s.a * s.l * x.b - 4 * (s.a * x.b * x.l)
      + 2 * (s.a * x.b * y.l) - 4 * (s.a * x.e * x.k) - 4 * (s.a * x.g * x.i)
      + 2 * (s.a * x.g * y.i) + 2 * (s.a * x.k * y.e) + s.a * y.b * y.l + s.a * y.e * y.k
      + s.a * y.g * y.i + 3 * (s.b * x.a * x.l) - 2 * (s.b * x.a * y.l) - 2 * (s.b * y.a * y.l)
      - s.c * s.f * x.i + 3 * (s.c * x.f * x.i) - 2 * (s.c * x.f * y.i) - 2 * (s.c * y.f * y.i)
      - s.d * s.j * x.e + 3 * (s.d * x.e * x.j) - 2 * (s.d * x.j * y.e) - 2 * (s.d * y.e * y.j)
      + s.e * s.f * x.h + s.e * s.j * x.d + s.e * x.a * x.k + s.e * x.d * x.j + s.e * x.f * x.h
      + s.e * y.a * y.k + s.e * y.d * y.j + s.e * y.f * y.h - s.f * s.h * x.e + s.f * s.i * x.c
      - 4 * (s.f * x.c * x.i) + 2 * (s.f * x.c * y.i) - 4 * (s.f * x.e * x.h)
      + 2 * (s.f * x.h * y.e) + s.f * y.c * y.i + s.f * y.e * y.h + 3 * (s.g * x.a * x.i)
      - 2 * (s.g * x.a * y.i) - 2 * (s.g * y.a * y.i) + 3 * (s.h * x.e * x.f)
      - 2 * (s.h * x.f * y.e) - 2 * (s.h * y.e * y.f) + s.i * x.a * x.g + s.i * x.c * x.f
      + s.i * y.a * y.g + s.i * y.c * y.f - 4 * (s.j * x.d * x.e) + 2 * (s.j * x.d * y.e)
      + s.j * y.d * y.e + 3 * (s.k * x.a * x.e) - 2 * (s.k * x.a * y.e) - 2 * (s.k * y.a * y.e)
      + s.l * x.a * x.b + s.l * y.a * y.b - 20 * (x.a * x.b * x.l) + 20 * (x.a * x.b * y.l)
      - 20 * (x.a * x.e * x.k) - 20 * (x.a * x.g * x.i) + 20 * (x.a * x.g * y.i)
      + 20 * (x.a * x.k * y.e) - 4 * (x.a * y.b * y.l) - 4 * (x.a * y.e * y.k)
      - 4 * (x.a * y.g * y.i) - 20 * (x.c * x.f * x.i) + 20 * (x.c * x.f * y.i)
      - 20 * (x.d * x.e * x.j) + 20 * (x.d * x.j * y.e) - 20 * (x.e * x.f * x.h)
      + 20 * (x.f * x.h * y.e) - 4 * (x.f * y.c * y.i) - 4 * (x.f * y.e * y.h)
      - 4 * (x.j * y.d * y.e) + s.a * s.b * s.c * x.i - s.a * s.b * s.e * x.h
      + s.a * s.b * s.h * x.e - s.a * s.b * s.i * x.c + 4 * (s.a * s.b * x.c * x.i)
      - 2 * (s.a * s.b * x.c * y.i) + 4 * (s.a * s.b * x.e * x.h) - 2 * (s.a * s.b * x.h * y.e)
      - s.a * s.b * y.c * y.i - s.a * s.b * y.e * y.h - 3 * (s.a * s.c * x.b * x.i)
      + 2 * (s.a * s.c * x.b * y.i) + s.a * s.c * y.b * y.i + s.a * s.d * s.g * x.e
      - 3 * (s.a * s.d * x.e * x.g) + 2 * (s.a * s.d * x.g * y.e) + s.a * s.d * y.e * y.g
      - s.a * s.e * s.g * x.d - s.a * s.e * x.b * x.h - s.a * s.e * x.d * x.g
      + 4 * (s.a * s.g * x.d * x.e) - 2 * (s.a * s.g * x.d * y.e) - s.a * s.g * y.d * y.e
      - 3 * (s.a * s.h * x.b * x.e) + 2 * (s.a * s.h * x.b * y.e) + s.a * s.h * y.b * y.e
      - s.a * s.i * x.b * x.c + 10 * (s.a * x.b * x.c * x.i) - 8 * (s.a * x.b * x.c * y.i)
      + 10 * (s.a * x.b * x.e * x.h) - 8 * (s.a * x.b * x.h * y.e) + s.a * x.b * y.c * y.i
      + s.a * x.b * y.e * y.h + 10 * (s.a * x.d * x.e * x.g) - 8 * (s.a * x.d * x.g * y.e)
      + s.a * x.g * y.d * y.e + s.b * s.c * y.a * y.i - s.b * s.e * y.a * y.h
      + s.b * s.h * y.a * y.e - s.b * s.i * y.a * y.c - 6 * (s.b * x.a * x.c * x.i)
      + 6 * (s.b * x.a * x.c * y.i) - 6 * (s.b * x.a * x.e * x.h) + 6 * (s.b * x.a * x.h * y.e)
      - 5 * (s.b * x.a * y.c * y.i) - 5 * (s.b * x.a * y.e * y.h) + s.c * s.d * s.f * x.e
      + s.c * s.d * y.e * y.f - s.c * s.e * s.f * x.d - s.c * s.e * y.d * y.f
      + 4 * (s.c * s.f * x.d * x.e) - 2 * (s.c * s.f * x.d * y.e) - s.c * s.f * y.d * y.e
      - 3 * (s.c * x.a * x.b * x.i) + 2 * (s.c * x.a * x.b * y.i) + 8 * (s.c * x.a * y.b * y.i)
      - 6 * (s.c * x.d * x.e * x.f) + 6 * (s.c * x.d * x.f * y.e) - 5 * (s.c * x.f * y.d * y.e)
      - 3 * (s.d * s.f * x.c * x.e) + 2 * (s.d * s.f * x.c * y.e) + s.d * s.f * y.c * y.e
      + s.d * s.g * y.a * y.e - 3 * (s.d * x.a * x.e * x.g) + 2 * (s.d * x.a * x.g * y.e)
      + 8 * (s.d * x.a * y.e * y.g) - 3 * (s.d * x.c * x.e * x.f) + 2 * (s.d * x.c * x.f * y.e)
      + 8 * (s.d * x.f * y.c * y.e) - s.e * s.f * x.c * x.d - s.e * s.g * y.a * y.d
      - s.e * x.a * x.b * x.h - s.e * x.a * x.d * x.g - 4 * (s.e * x.a * y.b * y.h)
      - 4 * (s.e * x.a * y.d * y.g) - s.e * x.c * x.d * x.f - 4 * (s.e * x.f * y.c * y.d)
      + 10 * (s.f * x.c * x.d * x.e) - 8 * (s.f * x.c * x.d * y.e) + s.f * x.c * y.d * y.e
      - 6 * (s.g * x.a * x.d * x.e) + 6 * (s.g * x.a * x.d * y.e) - 5 * (s.g * x.a * y.d * y.e)
      - 3 * (s.h * x.a * x.b * x.e) + 2 * (s.h * x.a * x.b * y.e) + 8 * (s.h * x.a * y.b * y.e)
      - s.i * x.a * x.b * x.c - 4 * (s.i * x.a * y.b * y.c) + 35 * (x.a * x.b * x.c * x.i)
      - 40 * (x.a * x.b * x.c * y.i) + 35 * (x.a * x.b * x.e * x.h)
      - 40 * (x.a * x.b * x.h * y.e) + 10 * (x.a * x.b * y.c * y.i)
      + 10 * (x.a * x.b * y.e * y.h) + 35 * (x.a * x.d * x.e * x.g)
      - 40 * (x.a * x.d * x.g * y.e) + 10 * (x.a * x.g * y.d * y.e)
      + 35 * (x.c * x.d * x.e * x.f) - 40 * (x.c * x.d * x.f * y.e)
      + 10 * (x.c * x.f * y.d * y.e) - s.a * s.b * s.c * s.d * x.e + s.a * s.b * s.c * s.e * x.d
      - 4 * (s.a * s.b * s.c * x.d * x.e) + 2 * (s.a * s.b * s.c * x.d * y.e)
      + s.a * s.b * s.c * y.d * y.e + 3 * (s.a * s.b * s.d * x.c * x.e)
      - 2 * (s.a * s.b * s.d * x.c * y.e) - s.a * s.b * s.d * y.c * y.e
      + s.a * s.b * s.e * x.c * x.d - 10 * (s.a * s.b * x.c * x.d * x.e)
      + 8 * (s.a * s.b * x.c * x.d * y.e) - s.a * s.b * x.c * y.d * y.e
      + 6 * (s.a * s.c * x.b * x.d * x.e) - 6 * (s.a * s.c * x.b * x.d * y.e)
      + 2 * (s.a * s.c * x.b * y.d * y.e) + s.a * s.c * y.b * y.d * y.e
      + 3 * (s.a * s.d * x.b * x.c * x.e) - 2 * (s.a * s.d * x.b * x.c * y.e)
      - 2 * (s.a * s.d * x.b * y.c * y.e) - 2 * (s.a * s.d * y.b * y.c * y.e)
      + s.a * s.e * x.b * x.c * x.d + s.a * s.e * x.b * y.c * y.d + s.a * s.e * y.b * y.c * y.d
      - 20 * (s.a * x.b * x.c * x.d * x.e) + 20 * (s.a * x.b * x.c * x.d * y.e)
      - 4 * (s.a * x.b * x.c * y.d * y.e) - s.b * s.c * s.d * y.a * y.e
      + s.b * s.c * s.e * y.a * y.d + 3 * (s.b * s.c * x.a * y.d * y.e)
      - s.b * s.c * y.a * y.d * y.e - 2 * (s.b * s.d * x.a * y.c * y.e)
      + 2 * (s.b * s.d * y.a * y.c * y.e) - s.b * s.e * x.a * y.c * y.d
      - s.b * s.e * y.a * y.c * y.d + 10 * (s.b * x.a * x.c * x.d * x.e)
      - 12 * (s.b * x.a * x.c * x.d * y.e) + 3 * (s.b * x.a * x.c * y.d * y.e)
      - 4 * (s.c * s.d * x.a * y.b * y.e) + 4 * (s.c * s.e * x.a * y.b * y.d)
      + 6 * (s.c * x.a * x.b * x.d * x.e) - 6 * (s.c * x.a * x.b * x.d * y.e)
      + 11 * (s.c * x.a * x.b * y.d * y.e) + 3 * (s.d * x.a * x.b * x.c * x.e)
      - 2 * (s.d * x.a * x.b * x.c * y.e) - 20 * (s.d * x.a * x.b * y.c * y.e)
      + s.e * x.a * x.b * x.c * x.d + 10 * (s.e * x.a * x.b * y.c * y.d)
      - 56 * (x.a * x.b * x.c * x.d * x.e) + 70 * (x.a * x.b * x.c * x.d * y.e)
      - 20 * (x.a * x.b * x.c * y.d * y.e)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- ⭐ **The class-four row of the core word.** -/
theorem SqU6.sqWord_m (s x y : SqU6 R) :
    (sqWord s x y).m = -4 * x.m + 2 * y.m + sqU6Core4 s x y := by
  simp only [sqWord, sqU6Core4, SqU6.mul_a, SqU6.mul_f, SqU6.mul_j, SqU6.mul_m, SqU6.inv_a,
    SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_f, SqU6.inv_g, SqU6.inv_h, SqU6.inv_j,
    SqU6.inv_k, SqU6.inv_m, SqU6.conjP_a, SqU6.conjP_b, SqU6.conjP_c, SqU6.conjP_d, SqU6.conjP_f,
    SqU6.conjP_g, SqU6.conjP_h, SqU6.conjP_j, SqU6.conjP_k, SqU6.conjP_m, SqU6.pow_a, SqU6.pow_b,
    SqU6.pow_c, SqU6.pow_d, SqU6.pow_f, SqU6.pow_g, SqU6.pow_h, SqU6.pow_j, SqU6.pow_k,
    SqU6.pow_m, SqU6.commP_d, SqU6.commP_h, SqU6.commP_k, SqU6.commP_m, SqU6.u6Comm3M,
    SqU6.u6Comm4L, chooseTwoTwo, chooseTwoThree, chooseTwoFour, chooseThreeTwo, chooseThreeThree,
    chooseThreeFour]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- ⭐⭐ **The class-five row of the core word.**  The row two carriers deferred. -/
theorem SqU6.sqWord_o (s x y : SqU6 R) :
    (sqWord s x y).o = -4 * x.o + 2 * y.o + sqU6Core s x y := by
  simp only [sqWord, sqU6Core, SqU6.mul_a, SqU6.mul_f, SqU6.mul_j, SqU6.mul_m, SqU6.mul_o,
    SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f, SqU6.inv_g,
    SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m, SqU6.inv_n,
    SqU6.inv_o, SqU6.conjP_a, SqU6.conjP_b, SqU6.conjP_c, SqU6.conjP_d, SqU6.conjP_e,
    SqU6.conjP_f, SqU6.conjP_g, SqU6.conjP_h, SqU6.conjP_i, SqU6.conjP_j, SqU6.conjP_k,
    SqU6.conjP_l, SqU6.conjP_m, SqU6.conjP_n, SqU6.conjP_o, SqU6.pow_a, SqU6.pow_b, SqU6.pow_c,
    SqU6.pow_d, SqU6.pow_e, SqU6.pow_f, SqU6.pow_g, SqU6.pow_h, SqU6.pow_i, SqU6.pow_j,
    SqU6.pow_k, SqU6.pow_l, SqU6.pow_m, SqU6.pow_n, SqU6.pow_o, SqU6.commP_e, SqU6.commP_i,
    SqU6.commP_l, SqU6.commP_n, SqU6.commP_o, SqU6.u6Comm3R, SqU6.u6Comm4R, SqU6.u6Comm5,
    chooseTwoTwo, chooseTwoThree, chooseTwoFour, chooseThreeTwo, chooseThreeThree,
    chooseThreeFour, chooseTwoFive, chooseThreeFive]
  push_cast
  ring

end CoreWord

/-! ## 3 The class-five defect of a general marking -/

section Defect

variable {R : Type} [CommRing R] {h : ℕ}

variable (h) in
/-- ⭐ **The class-four defect of a marking.**  The class-four coordinate the relator would have
if the `(1,5)`-coordinates of the marking were all `0`. -/
def sqU6Defect4 (m : Fin (sqRank h) → SqU6 R) : R :=
  sqU6Core4 (m 0) (m 1) (m 2)
    + (-4 * (m 1).a + 2 * (m 2).a)
        * sqU6BlockK (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))
    + (-4 * (m 1).f + 2 * (m 2).f + sqU6CoreTwo (m 0) (m 1) (m 2))
        * sqU6BlockH (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))
    + sqU6BlockM (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))

variable (h) in
/-- ⭐⭐ **The class-five defect of a marking**: the class-five coordinate the relator would have
if the `(1,6)`-coordinates of the marking were all `0`.  Five pieces:

* `sqU6Core`, the core word's own class-five content;
* the relator vector's abelian row against the handle block's second class-four coordinate;
* the core word's class-two row against the handle block's right class-three coordinate;
* ⭐ the core word's **class-three** row against the handle block's outermost class-two
  pairing, the coupling with no class-four analogue;
* the handle block's own class-five coordinate, cross-handle pairings included. -/
def sqU6Defect (m : Fin (sqRank h) → SqU6 R) : R :=
  sqU6Core (m 0) (m 1) (m 2)
    + (-4 * (m 1).a + 2 * (m 2).a)
        * sqU6BlockN (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))
    + (-4 * (m 1).f + 2 * (m 2).f + sqU6CoreTwo (m 0) (m 1) (m 2))
        * sqU6BlockL (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))
    + (-4 * (m 1).j + 2 * (m 2).j
        + sqU4Core (SqU6.toU4LL (m 0)) (SqU6.toU4LL (m 1)) (SqU6.toU4LL (m 2)))
        * sqU6BlockI (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))
    + sqU6BlockO (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))

/-- ⭐ **The class-four row of the relator in closed form**, at every handle count and every
marking. -/
theorem SqU6.sqRelWord_m_defect (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).m = -4 * (m 1).m + 2 * (m 2).m + sqU6Defect4 h m := by
  rw [SqU6.sqRelWord_m, SqU6.sqWord_m, SqU6.sqWord_a, SqU6.sqWord_f_core, SqU6.handleWord_k,
    SqU6.handleWord_h, SqU6.handleWord_m, sqU6Defect4]
  ring

/-- ⭐⭐ **The class-five row of the relator in closed form**, at every handle count and every
marking.  This is the statement `GradedFour` deferred as `sqU5Defect` and `GradedFive` deferred
as `sqU6Defect`. -/
theorem SqU6.sqRelWord_o_defect (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).o = -4 * (m 1).o + 2 * (m 2).o + sqU6Defect h m := by
  rw [SqU6.sqRelWord_o, SqU6.sqWord_o, SqU6.sqWord_a, SqU6.sqWord_f_core, SqU6.sqWord_j,
    SqU6.handleWord_n, SqU6.handleWord_l, SqU6.handleWord_blockI, SqU6.handleWord_o,
    sqU6Defect]
  ring

/-- ⭐ **The relator in the class-five carrier**: the fourteen lower rows are the two
`U_5`-quotients' relator identities, and the fifteenth is the class-five defect equation. -/
theorem SqU6.sqRelWord_eq_one_iff (m : Fin (sqRank h) → SqU6 R) :
    sqRelWord m = 1 ↔ sqRelWord (fun i => SqU6.toU5L (m i)) = 1
      ∧ sqRelWord (fun i => SqU6.toU5R (m i)) = 1
      ∧ -4 * (m 1).o + 2 * (m 2).o + sqU6Defect h m = 0 := by
  rw [← SqU6.sqRelWord_o_defect, ← SqU6.toU5L_sqRelWord, ← SqU6.toU5R_sqRelWord]
  constructor
  · rintro hr
    rw [hr]
    exact ⟨map_one _, map_one _, rfl⟩
  · rintro ⟨hL, hR, ho⟩
    have hLa := congrArg SqU5.a hL
    have hLb := congrArg SqU5.b hL
    have hLc := congrArg SqU5.c hL
    have hLd := congrArg SqU5.d hL
    have hLe := congrArg SqU5.e hL
    have hLf := congrArg SqU5.f hL
    have hLg := congrArg SqU5.g hL
    have hLh := congrArg SqU5.h hL
    have hLi := congrArg SqU5.i hL
    have hLj := congrArg SqU5.j hL
    have hRd := congrArg SqU5.d hR
    have hRg := congrArg SqU5.g hR
    have hRi := congrArg SqU5.i hR
    have hRj := congrArg SqU5.j hR
    rw [SqU6.eq_one_iff]
    exact ⟨hLa, hLb, hLc, hLd, hRd, hLe, hLf, hLg, hRg, hLh, hLi, hRi, hLj, hRj, ho⟩

/-- ⭐ **The class-five defect equation is a gate.**  Every frame of `D_sq h` that kills the
relator satisfies the class-five defect equation at its own slot images, in every class-five
test group. -/
theorem sqU6Defect_balance (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    -4 * (Phi (n 1)).o + 2 * (Phi (n 2)).o + sqU6Defect h (fun i => Phi (n i)) = 0 := by
  have hkey := SqU6.sqRelWord_eq_one_iff (R := R) (h := h) fun i => Phi (n i)
  rw [← map_sqRelWord Phi n, hn, map_one] at hkey
  exact (hkey.mp rfl).2.2

end Defect

/-! ## 4 What the closed form says -/

section Structure

variable {R : Type} [CommRing R] {h : ℕ}

/-- **The central shift of a marking**: every slot moved by a `gamma_5`-element, the only
motion the class-five row's adjustable part can see. -/
def sqU6Shift (m : Fin (sqRank h) → SqU6 R) (w : Fin (sqRank h) → R) :
    Fin (sqRank h) → SqU6 R :=
  fun i => ⟨(m i).a, (m i).b, (m i).c, (m i).d, (m i).e, (m i).f, (m i).g, (m i).h, (m i).i,
    (m i).j, (m i).k, (m i).l, (m i).m, (m i).n, (m i).o + w i⟩

@[simp] theorem sqU6Shift_o (m : Fin (sqRank h) → SqU6 R) (w : Fin (sqRank h) → R)
    (i : Fin (sqRank h)) : (sqU6Shift m w i).o = (m i).o + w i := rfl

theorem sqU6Shift_eq (m : Fin (sqRank h) → SqU6 R) (w : Fin (sqRank h) → R)
    (i : Fin (sqRank h)) :
    sqU6Shift m w i = m i * (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, w i⟩ : SqU6 R) :=
  (SqU6.mul_center_o (m i) (w i)).symm

set_option maxRecDepth 100000 in
/-- ⭐ **The class-five defect is blind to the class-five coordinates of the marking**: it reads
the fourteen lower rows and nothing else. -/
theorem sqU6Defect_shift (m : Fin (sqRank h) → SqU6 R) (w : Fin (sqRank h) → R) :
    sqU6Defect h (sqU6Shift m w) = sqU6Defect h m := rfl

set_option maxRecDepth 100000 in
theorem sqU6Defect4_shift (m : Fin (sqRank h) → SqU6 R) (w : Fin (sqRank h) → R) :
    sqU6Defect4 h (sqU6Shift m w) = sqU6Defect4 h m := rfl

/-- ⭐⭐ **The class-five adjustable set.**  The relator's class-five row sees the marking's
class-five coordinates **only** through slots `1` and `2`, with weights `-4` and `2`: the sigma
slot's and every handle slot's class-five coordinate cancels outright.  This is
`GradedThree`'s `sqU4_top_adjust` two classes up. -/
theorem SqU6.sqRelWord_o_shift (m : Fin (sqRank h) → SqU6 R) (w : Fin (sqRank h) → R) :
    (sqRelWord (sqU6Shift m w)).o = (sqRelWord m).o + (-4 * w 1 + 2 * w 2) := by
  rw [SqU6.sqRelWord_o_defect, SqU6.sqRelWord_o_defect, sqU6Defect_shift, sqU6Shift_o,
    sqU6Shift_o]
  ring

/-- …so the range of the class-five row along the central torsor is exactly `2R`. -/
theorem SqU6.sqRelWord_o_range (m : Fin (sqRank h) → SqU6 R) (c : R) :
    (sqRelWord (sqU6Shift m (fun i => if (i : ℕ) = 2 then c else 0))).o
      = (sqRelWord m).o + 2 * c := by
  rw [SqU6.sqRelWord_o_shift, sqVal_one, sqVal_two]
  norm_num

/-- …and no central shift can move it outside `2R`. -/
theorem SqU6.sqRelWord_o_shift_even (m : Fin (sqRank h) → SqU6 R) (w : Fin (sqRank h) → R) :
    ∃ c : R, (sqRelWord (sqU6Shift m w)).o = (sqRelWord m).o + 2 * c :=
  ⟨w 2 - 2 * w 1, by rw [SqU6.sqRelWord_o_shift]; ring⟩

/-- At `h = 0` the class-five defect is the core word's class-five content alone. -/
theorem sqU6Defect_zero (m : Fin (sqRank 0) → SqU6 R) :
    sqU6Defect 0 m = sqU6Core (m 0) (m 1) (m 2) := by
  simp [sqU6Defect, sqU6BlockI, sqU6BlockL, sqU6BlockN, sqU6BlockO]

/-- At `h = 1` the cross-handle pairings vanish and the handle block is a plain per-handle
sum, so the defect is the class-three shape one level up. -/
theorem sqU6BlockO_one (u v : Fin 1 → SqU6 R) :
    sqU6BlockO u v = ∑ j, SqU6.u6Comm5 (u j) (v j) := by
  simp [sqU6BlockO]

theorem sqU6BlockM_one (u v : Fin 1 → SqU6 R) :
    sqU6BlockM u v = ∑ j, SqU6.u6Comm4L (u j) (v j) := by
  simp [sqU6BlockM]

theorem sqU6BlockN_one (u v : Fin 1 → SqU6 R) :
    sqU6BlockN u v = ∑ j, SqU6.u6Comm4R (u j) (v j) := by
  simp [sqU6BlockN]

end Structure

/-! ## 5 The class-five translation identity: how a dressing moves the top row -/

section GaFourCalculus

variable {R : Type} [CommRing R] {h : ℕ}

/-- **A `gamma_4`-shaped element of the class-five carrier**: only the two class-four
coordinates and the class-five one live.  This is the class-five `K`-dressing shape, the
transposition of `GradedContainFour`'s `IsGaThree` one level up. -/
def SqU6.IsGaFour (p : SqU6 R) : Prop :=
  p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.e = 0 ∧ p.f = 0 ∧ p.g = 0 ∧ p.h = 0 ∧ p.i = 0
    ∧ p.j = 0 ∧ p.k = 0 ∧ p.l = 0

/-- The central class-five translation, `GradedLift`'s `liftC` one level up. -/
def SqU6.liftO (w : R) : SqU6 R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, w⟩

@[simp] theorem SqU6.liftO_o (w : R) : (SqU6.liftO w).o = w := rfl

@[simp] theorem SqU6.liftO_mul_liftO (v w : R) :
    SqU6.liftO v * SqU6.liftO w = SqU6.liftO (v + w) := by
  ext <;> simp [SqU6.liftO]

theorem SqU6.liftO_comm (p : SqU6 R) (w : R) :
    p * SqU6.liftO w = SqU6.liftO w * p := by
  ext <;> simp [SqU6.liftO, add_comm]

/-- Central right factors of a product of two dressed factors collect. -/
private theorem SqU6.mul_liftO_mul_liftO (a b : SqU6 R) (w v : R) :
    (a * SqU6.liftO w) * (b * SqU6.liftO v) = a * b * SqU6.liftO (w + v) := by
  rw [mul_assoc, ← mul_assoc (SqU6.liftO w), ← SqU6.liftO_comm, mul_assoc,
    SqU6.liftO_mul_liftO, ← mul_assoc]

/-- ⭐ **A handle commutator swallows a `gamma_4`-dressing centrally**: the pairing of the two
dressings' `(m, n)`-data against the OPPOSITE letter's outermost abelian columns `(e, a)`.
This is `GradedContainFour`'s `commP_mul_gaThree` with `(h, i)` replaced by `(m, n)` and the
column `d` replaced by `e`. -/
theorem SqU6.commP_mul_gaFour (u v : SqU6 R) {zu zv : SqU6 R} (hu : zu.IsGaFour)
    (hv : zv.IsGaFour) :
    commP (u * zu) (v * zv)
      = commP u v
        * SqU6.liftO ((zu.m * v.e - zu.n * v.a) + (u.a * zv.n - u.e * zv.m)) := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12⟩ := hu
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := hv
  ext <;>
    simp only [commP, SqU6.liftO, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e,
      SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l,
      SqU6.mul_m, SqU6.mul_n, SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d,
      SqU6.inv_e, SqU6.inv_f, SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k,
      SqU6.inv_l, SqU6.inv_m, SqU6.inv_n, SqU6.inv_o,
      u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12,
      v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] <;> ring

/-- ⭐ **The handle block swallows an all-pair `gamma_4`-dressing centrally.** -/
theorem SqU6.handleWord_mul_gaFour_all : ∀ (n : ℕ) (u v zu zv : Fin n → SqU6 R),
    (∀ k, (zu k).IsGaFour) → (∀ k, (zv k).IsGaFour) →
    handleWord (fun k => u k * zu k) (fun k => v k * zv k)
      = handleWord u v
        * SqU6.liftO (∑ k : Fin n, (((zu k).m * (v k).e - (zu k).n * (v k).a)
            + ((u k).a * (zv k).n - (u k).e * (zv k).m)))
  | 0, u, v, zu, zv, _, _ => by
    simp only [handleWord_zero]
    ext <;> simp [SqU6.liftO]
  | n + 1, u, v, zu, zv, hzu, hzv => by
    have htail := SqU6.handleWord_mul_gaFour_all n (fun k => u k.succ) (fun k => v k.succ)
      (fun k => zu k.succ) (fun k => zv k.succ) (fun k => hzu _) (fun k => hzv _)
    rw [handleWord_succ, handleWord_succ, htail,
      SqU6.commP_mul_gaFour (u 0) (v 0) (hzu 0) (hzv 0), SqU6.mul_liftO_mul_liftO,
      Fin.sum_univ_succ]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- ⭐⭐ **The core word under `gamma_4`-dressings of its three slots**: the two class-four
rows pick up the Frobenius weights `(-4, 2)` on the exponent slots, and the class-five row the
core block of the graded Fox form.  No closed form of the word is consumed. -/
theorem SqU6.sqWord_mul_gaFour {z₀ z₁ z₂ : SqU6 R} (s x y : SqU6 R) (h₀ : z₀.IsGaFour)
    (h₁ : z₁.IsGaFour) (h₂ : z₂.IsGaFour) :
    sqWord (s * z₀) (x * z₁) (y * z₂)
      = sqWord s x y * ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
          -4 * z₁.m + 2 * z₂.m, -4 * z₁.n + 2 * z₂.n,
          -4 * z₁.o + 2 * z₂.o
            + ((x.e * z₀.m - x.a * z₀.n)
              + ((10 * x.e - s.e - 8 * y.e) * z₁.m - (10 * x.a - s.a - 8 * y.a) * z₁.n)
              + (y.e * z₂.m - y.a * z₂.n))⟩ := by
  obtain ⟨a0, b0, c0, d0, e0, f0, g0, hh0, i0, j0, k0, l0⟩ := h₀
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, hh1, i1, j1, k1, l1⟩ := h₁
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, hh2, i2, j2, k2, l2⟩ := h₂
  ext <;>
    simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
      SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
      SqU6.inv_n, SqU6.inv_o,
      a0, b0, c0, d0, e0, f0, g0, hh0, i0, j0, k0, l0,
      a1, b1, c1, d1, e1, f1, g1, hh1, i1, j1, k1, l1,
      a2, b2, c2, d2, e2, f2, g2, hh2, i2, j2, k2, l2] <;> ring

/-- **The five-slot `gamma_4`-dressing** of a frame. -/
def conFiveDress (m z : Fin (sqRank h) → SqU6 R) : Fin (sqRank h) → SqU6 R :=
  fun i => m i * z i

@[simp] theorem conFiveDress_apply (m z : Fin (sqRank h) → SqU6 R) (i : Fin (sqRank h)) :
    conFiveDress m z i = m i * z i := rfl

variable (h) in
/-- ⭐⭐ **The class-five graded Fox form**: the amount by which the class-five residue moves
under a five-slot `gamma_4`-dressing, beyond the Frobenius part `-4 (z 1).o + 2 (z 2).o` and
the relator's own abelian row against the dressing's Frobenius `n`-row.  Each slot's
`(m, n)`-data is paired against the **permuted** letter's outermost abelian columns `(e, a)`:
the sigma slot against the `x0`-letter, the `x0`-slot against `10 x0 - sigma - 8 x1`, the
`x1`-slot against itself, and each handle against the opposite handle letter.

This is `GradedContainFour`'s `conFourShift` **verbatim**, with the class-three data `(h, i)`
replaced by the class-four data `(m, n)` and the outermost abelian column `d` replaced by
`e`. -/
def conFiveShift (m z : Fin (sqRank h) → SqU6 R) : R :=
  ((m 1).e * (z 0).m - (m 1).a * (z 0).n)
    + ((10 * (m 1).e - (m 0).e - 8 * (m 2).e) * (z 1).m
      - (10 * (m 1).a - (m 0).a - 8 * (m 2).a) * (z 1).n)
    + ((m 2).e * (z 2).m - (m 2).a * (z 2).n)
    + ∑ j : Fin h,
        (((z (sqHandleIdxU j)).m * (m (sqHandleIdxV j)).e
            - (z (sqHandleIdxU j)).n * (m (sqHandleIdxV j)).a)
          + ((m (sqHandleIdxU j)).a * (z (sqHandleIdxV j)).n
            - (m (sqHandleIdxU j)).e * (z (sqHandleIdxV j)).m))

variable {m z : Fin (sqRank h) → SqU6 R}

/-- ⭐⭐ **The class-five translation identity.**  A five-slot `gamma_4`-dressing moves the
relator by an explicit `gamma_4`-element: Frobenius weights on the two class-four rows, and in
the class-five row the graded Fox form.  Every class-`<= 3` row is untouched.  This is the
statement the campaign could not make before the class-five defect existed. -/
theorem SqU6.sqRelWord_conFiveDress (hz : ∀ i, (z i).IsGaFour) :
    sqRelWord (conFiveDress m z)
      = sqRelWord m * ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
          -4 * (z 1).m + 2 * (z 2).m, -4 * (z 1).n + 2 * (z 2).n,
          -4 * (z 1).o + 2 * (z 2).o + conFiveShift h m z⟩ := by
  have hhand : handleWord (fun k => m (sqHandleIdxU k) * z (sqHandleIdxU k))
      (fun k => m (sqHandleIdxV k) * z (sqHandleIdxV k))
      = handleWord (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        * SqU6.liftO (∑ k : Fin h, (((z (sqHandleIdxU k)).m * (m (sqHandleIdxV k)).e
            - (z (sqHandleIdxU k)).n * (m (sqHandleIdxV k)).a)
          + ((m (sqHandleIdxU k)).a * (z (sqHandleIdxV k)).n
            - (m (sqHandleIdxU k)).e * (z (sqHandleIdxV k)).m))) :=
    SqU6.handleWord_mul_gaFour_all h _ _ _ _ (fun k => hz _) (fun k => hz _)
  rw [sqRelWord, sqRelWord]
  simp only [conFiveDress_apply]
  rw [SqU6.sqWord_mul_gaFour (m 0) (m 1) (m 2) (hz 0) (hz 1) (hz 2), hhand]
  ext <;>
    simp only [conFiveShift, SqU6.liftO, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d,
      SqU6.mul_e, SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k,
      SqU6.mul_l, SqU6.mul_m, SqU6.mul_n, SqU6.mul_o, SqU6.handleWord_a, SqU6.handleWord_b,
      SqU6.handleWord_c, SqU6.handleWord_d, SqU6.handleWord_e] <;> ring

/-- The two class-four rows of the dressed relator move by the Frobenius action alone. -/
theorem SqU6.sqRelWord_conFiveDress_m (hz : ∀ i, (z i).IsGaFour) :
    (sqRelWord (conFiveDress m z)).m = (sqRelWord m).m + (-4 * (z 1).m + 2 * (z 2).m) := by
  rw [SqU6.sqRelWord_conFiveDress hz, SqU6.mul_m]
  simp

theorem SqU6.sqRelWord_conFiveDress_n (hz : ∀ i, (z i).IsGaFour) :
    (sqRelWord (conFiveDress m z)).n = (sqRelWord m).n + (-4 * (z 1).n + 2 * (z 2).n) := by
  rw [SqU6.sqRelWord_conFiveDress hz, SqU6.mul_n]
  simp

/-- ⭐⭐ **The class-five row of the dressed relator**: the Frobenius part, the Fox form, and
one cross term reading the relator's own `a`-row against the dressing's Frobenius `n`-part.
The cross term is the exact analogue of the one `GradedContainFour`'s
`sqRelWord_conFourDress_j` carries, and it dies on any class-one-admissible frame. -/
theorem SqU6.sqRelWord_conFiveDress_o (hz : ∀ i, (z i).IsGaFour) :
    (sqRelWord (conFiveDress m z)).o
      = (sqRelWord m).o + (-4 * (z 1).o + 2 * (z 2).o + conFiveShift h m z)
        + (sqRelWord m).a * (-4 * (z 1).n + 2 * (z 2).n) := by
  rw [SqU6.sqRelWord_conFiveDress hz, SqU6.mul_o]
  simp

/-- ⭐⭐ **The defect of a `gamma_4`-dressed frame of a relator-solution is a pure dressing
artefact**: at a frame where the relator dies, the dressed relator IS the translation
`gamma_4`-element, reading the dressing and the frame's abelian columns and nothing else. -/
theorem SqU6.sqRelWord_conFiveDress_of_rel (hz : ∀ i, (z i).IsGaFour) (hm : sqRelWord m = 1) :
    sqRelWord (conFiveDress m z)
      = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
          -4 * (z 1).m + 2 * (z 2).m, -4 * (z 1).n + 2 * (z 2).n,
          -4 * (z 1).o + 2 * (z 2).o + conFiveShift h m z⟩ := by
  rw [SqU6.sqRelWord_conFiveDress hz, hm, one_mul]

/-- **The `gamma_4`-dressing torsor is a torsor**: the pointwise inverse dressing restores the
frame, so at a solution the dressed defect is killed unconditionally. -/
theorem conFiveDress_conFiveDress_inv (m z : Fin (sqRank h) → SqU6 R) :
    conFiveDress (conFiveDress m z) (fun i => (z i)⁻¹) = m := by
  funext i
  rw [conFiveDress_apply, conFiveDress_apply, mul_assoc, mul_inv_cancel, mul_one]

end GaFourCalculus

/-! ## 6 The cross-handle pairing is real: a certified negative -/

section CrossWitness

/-- Two handle pairs at `h = 2`: the first carries the `(a, b)`-pairing, the second the right
class-three form.  Their cross-handle product is the whole point. -/
def crossU : Fin 2 → SqU6 (ZMod 8) :=
  ![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩]

def crossV : Fin 2 → SqU6 (ZMod 8) :=
  ![⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩]

/-- …and the same two pairs in the opposite order. -/
def crossU' : Fin 2 → SqU6 (ZMod 8) := ![crossU 1, crossU 0]

def crossV' : Fin 2 → SqU6 (ZMod 8) := ![crossV 1, crossV 0]

/-- ⭐ **The cross-handle pairing does not vanish at two handles.** -/
theorem sqCross_crossUV :
    sqCross (fun j => (crossU j).a * (crossV j).b - (crossV j).a * (crossU j).b)
      (fun j => SqU6.u6Comm3R (crossU j) (crossV j)) = 1 := by decide

/-- ⭐⭐ **The handle block's class-five coordinate is not the sum of the per-handle class-five
commutator forms.**  A certified negative: no closed form of the shape "sum over handles" can
be right at class five, which is why `sqU6BlockO` needs `sqCross`. -/
theorem SqU6.handleWord_o_ne_sum :
    (handleWord crossU crossV).o ≠ ∑ j, SqU6.u6Comm5 (crossU j) (crossV j) := by decide

/-- ⭐⭐ **The handle block's class-five coordinate depends on the ORDER of the handles.**  The
two markings below carry the same two handle pairs, in the two possible orders; the per-handle
class-five forms agree, and the blocks differ.  So the block is not a function of the multiset
of handle pairs, and the triangular pairing is not an artefact of the derivation. -/
theorem SqU6.handleWord_o_order_dependent :
    (handleWord crossU crossV).o ≠ (handleWord crossU' crossV').o := by decide

theorem SqU6.u6Comm5_crossUV_swap :
    ∑ j, SqU6.u6Comm5 (crossU j) (crossV j) = ∑ j, SqU6.u6Comm5 (crossU' j) (crossV' j) := by
  decide

/-- The same phenomenon at class four, one row down: the witness is chosen so that both
cross-handle pairings are live at once. -/
theorem SqU6.handleWord_m_ne_sum :
    (handleWord crossU crossV).m ≠ ∑ j, SqU6.u6Comm4L (crossU j) (crossV j) := by decide

theorem SqU6.handleWord_m_order_dependent :
    (handleWord crossU crossV).m ≠ (handleWord crossU' crossV').m := by decide

theorem SqU6.u6Comm4L_crossUV_swap :
    ∑ j, SqU6.u6Comm4L (crossU j) (crossV j)
      = ∑ j, SqU6.u6Comm4L (crossU' j) (crossV' j) := by decide

end CrossWitness

/-! ## 7 The class-four defect on the class-four carrier -/

section ClassFour

variable {R : Type} [CommRing R] {h : ℕ}

/-- **The splitting of the left `U_5`-quotient**: the class-four carrier sits inside the
class-five one as the first five columns, with the sixth column zero.  This is a group
embedding, and `toU5L` is its retraction. -/
def SqU5.toU6 : SqU5 R →* SqU6 R where
  toFun q := ⟨q.a, q.b, q.c, q.d, 0, q.e, q.f, q.g, 0, q.h, q.i, 0, q.j, 0, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp] theorem SqU5.toU6_apply (q : SqU5 R) :
    SqU5.toU6 q = ⟨q.a, q.b, q.c, q.d, 0, q.e, q.f, q.g, 0, q.h, q.i, 0, q.j, 0, 0⟩ := rfl

@[simp] theorem SqU5.toU5L_toU6 (q : SqU5 R) : SqU6.toU5L (SqU5.toU6 q) = q := rfl

variable (h) in
/-- ⭐⭐ **The class-four defect of a marking of the class-four carrier**: the closed form
`GradedFour`'s scope note deferred as `sqU5Defect`, "a self-standing `sqU5Defect` closed form
earns its keep only when a wave needs the class-four gate at arbitrary markings".
`GradedContainFour` and `GradedGammaTwo` are that wave.  It is the class-five carrier's
class-four defect at the embedded marking, and by `SqU5.toU5L_toU6` no information is lost. -/
def sqU5Defect (m : Fin (sqRank h) → SqU5 R) : R :=
  sqU6Defect4 h (fun i => SqU5.toU6 (m i))

/-- ⭐⭐ **The class-four row of the relator in the class-four carrier, in closed form**, at
every handle count and every marking. -/
theorem SqU5.sqRelWord_j_defect (m : Fin (sqRank h) → SqU5 R) :
    (sqRelWord m).j = -4 * (m 1).j + 2 * (m 2).j + sqU5Defect h m := by
  have hmap := congrArg (fun p : SqU6 R => p.m)
    (map_sqRelWord (SqU5.toU6 (R := R)) m)
  rw [SqU6.sqRelWord_m_defect] at hmap
  exact hmap

/-- ⭐ **The class-four defect equation is a gate on the class-four carrier.** -/
theorem sqU5Defect_balance (Phi : ContinuousMonoidHom (DSq h : Type) (SqU5 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    -4 * (Phi (n 1)).j + 2 * (Phi (n 2)).j + sqU5Defect h (fun i => Phi (n i)) = 0 := by
  have hkey := SqU5.sqRelWord_j_defect (R := R) (h := h) fun i => Phi (n i)
  rw [← map_sqRelWord Phi n, hn, map_one] at hkey
  exact hkey.symm

end ClassFour

/-! ## 8 Axiom pins

Committed prints for every public declaration: all **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable. -/

section AxiomPins

#print axioms sqCross
#print axioms sqCross_zero
#print axioms sqCross_one
#print axioms sqCross_succ
#print axioms sqCross_two
#print axioms handleWord_succ
#print axioms sqU6BlockF
#print axioms sqU6BlockG
#print axioms sqU6BlockH
#print axioms sqU6BlockI
#print axioms sqU6BlockJ
#print axioms sqU6BlockK
#print axioms sqU6BlockL
#print axioms sqU6BlockM
#print axioms sqU6BlockN
#print axioms sqU6BlockO
#print axioms SqU6.handleWord_f
#print axioms SqU6.handleWord_g
#print axioms SqU6.handleWord_h
#print axioms SqU6.handleWord_blockI
#print axioms SqU6.handleWord_j
#print axioms SqU6.handleWord_k
#print axioms SqU6.handleWord_l
#print axioms SqU6.handleWord_m
#print axioms SqU6.handleWord_n
#print axioms SqU6.handleWord_o
#print axioms sqU6CoreTwo
#print axioms SqU6.sqWord_f_core
#print axioms sqU6Core4
#print axioms sqU6Core
#print axioms SqU6.sqWord_m
#print axioms SqU6.sqWord_o
#print axioms sqU6Defect4
#print axioms sqU6Defect
#print axioms SqU6.sqRelWord_m_defect
#print axioms SqU6.sqRelWord_o_defect
#print axioms SqU6.sqRelWord_eq_one_iff
#print axioms sqU6Defect_balance
#print axioms sqU6Shift
#print axioms sqU6Shift_o
#print axioms sqU6Shift_eq
#print axioms sqU6Defect_shift
#print axioms sqU6Defect4_shift
#print axioms SqU6.sqRelWord_o_shift
#print axioms SqU6.sqRelWord_o_range
#print axioms SqU6.sqRelWord_o_shift_even
#print axioms sqU6Defect_zero
#print axioms sqU6BlockO_one
#print axioms sqU6BlockM_one
#print axioms sqU6BlockN_one
#print axioms SqU6.IsGaFour
#print axioms SqU6.liftO
#print axioms SqU6.liftO_o
#print axioms SqU6.liftO_mul_liftO
#print axioms SqU6.liftO_comm
#print axioms SqU6.commP_mul_gaFour
#print axioms SqU6.handleWord_mul_gaFour_all
#print axioms SqU6.sqWord_mul_gaFour
#print axioms conFiveDress
#print axioms conFiveDress_apply
#print axioms conFiveShift
#print axioms SqU6.sqRelWord_conFiveDress
#print axioms SqU6.sqRelWord_conFiveDress_m
#print axioms SqU6.sqRelWord_conFiveDress_n
#print axioms SqU6.sqRelWord_conFiveDress_o
#print axioms SqU6.sqRelWord_conFiveDress_of_rel
#print axioms conFiveDress_conFiveDress_inv
#print axioms crossU
#print axioms crossV
#print axioms crossU'
#print axioms crossV'
#print axioms sqCross_crossUV
#print axioms SqU6.handleWord_o_ne_sum
#print axioms SqU6.handleWord_o_order_dependent
#print axioms SqU6.u6Comm5_crossUV_swap
#print axioms SqU6.handleWord_m_ne_sum
#print axioms SqU6.handleWord_m_order_dependent
#print axioms SqU6.u6Comm4L_crossUV_swap
#print axioms SqU5.toU6
#print axioms SqU5.toU6_apply
#print axioms SqU5.toU5L_toU6
#print axioms sqU5Defect
#print axioms SqU5.sqRelWord_j_defect
#print axioms sqU5Defect_balance

end AxiomPins

end SqCore

end Dyadic

end GQ2
