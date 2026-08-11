/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveDefect
import GQ2.Dyadic.SqCore.GradedFiveBlind
import GQ2.Dyadic.SqCore.GradedBlockSecond
import GQ2.Dyadic.SqCore.GradedFiveLive

/-!
# W64-SEP0H: the class-five sigma separation forces a handle, unconditionally

`docs/dyadic/w63-live5-note.md` section 6 left one question and priced it as the wave's best
remaining item: **does the class-five sigma separation force `0 < h`?**  Wave 63 measured `0`
separations in `200000` gauged `h = 0` trials, proved nothing about it, and showed that the
block instrument cannot settle it at either end.  This file settles it, in the affirmative and
**with no gauge hypothesis at all**, by an argument that uses no block reading, no frame, no
lattice and no homomorphism on `D_sq h`: the fifteen rows of the core word over an arbitrary
commutative ring.

## ⭐⭐⭐ Headline: YES, and the mechanism is that the response is a combination of lower rows

⭐⭐⭐ `SqU6.sqWord_diagDress_o`.  Over **any** commutative ring, for any three slots
`s, x, y : SqU6 R` whose `x1` abelian columns are even,

```text
(sqWord (s * x) x y).o - (sqWord s x y).o
  =  x_36 * W_13  +  x_12 x_46 * W_24  +  (x_56 x_13 + x_12 x_23 x_56) * W_35
   + (x_14 + x_12 x_24 + x_34 x_13 + x_12 x_23 x_34) * W_46
   +  x_46 * W_14  +  x_12 x_56 * W_25  +  (x_13 + x_12 x_23) * W_36
   +  x_56 * W_15  +  x_12 * W_26   +  2 * (an explicit witness)
```

where `W = sqWord s x y` is the **undressed** core word.  So the whole class-five response to
the `a0 = a1` dressing is a polynomial-coefficient combination of the nine rows of class two,
three and four of the undressed word, modulo `2`.  At `h = 0` the relator **is** the core word,
so a relator-killing marking sets all nine to `0`, and the response is even:

> ⭐⭐⭐ `SqU6.selPar_sqWord_diagDress_o`.  If `sqWord s x y = 1` over `gr3R` then
> `selPar (sqWord (s * x) x y).o = 0`.  **No hypothesis on `s`, on `x` or on `y`.**

and, in the campaign's vocabulary,

> ⭐⭐⭐ `sepZero_pos_of_bit_odd`.  At every handle count, if a marking over `gr3R` kills the
> relator and its `a0 = a1` dressing has an **odd** class-five coordinate, then `0 < h`.

with ⭐⭐ `sepZero_pos_of_bit_odd_hom` the same for a continuous homomorphism on `D_sq h`,
through the class-five gate `sqU6Balance_gen`.

⭐ The whole dressed residue, not only its top row, is even: ⭐⭐ `SqU6.sqWord_diagDress_low`
says the nine rows of class at most two do not move at all (an identity over any ring, no
hypothesis), and `SqU6.selPar_sqWord_diagDress_high` says the remaining six are even at every
relator-killing `h = 0` marking.  So at `h = 0` the `a0 = a1` dressing is congruent to the
undressed marking modulo `2` in every coordinate.

## ⭐ The instrument that made the general rows available

The tree had closed forms for the core word's rows `a`-`f`, `h`, `i`, `j`, `m`, `o`; the row
expansion also needs `g`, `k`, `l`, `n`, the four rows living in the sixth column below the top.
⭐ `SqU6.sepShiftRow` supplies all four at once: it is the monoid endomorphism of `SqU6` that
carries the `(2..6)`-corner onto the `(1..5)`-corner and kills the sixth column, so that
`(sepShiftRow p).f = p.g`, `(sepShiftRow p).j = p.k`, `(sepShiftRow p).k = p.l` and
`(sepShiftRow p).m = p.n`.  Naturality of `sqWord` then transports each committed row lemma one
step outwards, and `SqU6.sqWord_l_of_shift` is the committed class-three row transported twice.
No new closed form is derived and no new polynomial is transcribed for these four rows.

## ⭐ What is new, against what the tree already had

* Wave 58 measured the diagonal response at the **committed** sigma slot `E_23` and on the
  relator's abelian rows alone: `x_12 y_24 y_46 + x_56 y_13 y_35` (mod `2`).  That is a
  two-monomial form at ONE sigma slot.  `scripts/w64_sep0h/derive_sep0h.py` section 3 reproduces
  it from scratch as a pipeline check and records that at a general sigma slot the same
  reduction has `42` monomials, not `2`.  ⚠ So wave 58's form must not be quoted at a general
  slot, and nothing here does.
* Wave 58 section 3.3 sketched a mechanism at `sigma = E_23` ("with a dead block the relator
  forces the core word trivial ... so `y_13 y_35` must be even").  ⚠ That sketch does not
  generalise as stated: at a general sigma slot the class-four row reads
  `s_12 x_25 + s_45 x_14 + s_13 x_35 + y_13 y_35 + s_12 s_23 x_35 + ...`, and `y_13 y_35` is not
  forced even on its own.  What is forced is the whole row, which is why the identity is stated
  as a multiple of the row.
* W63-LIVE5 proved `liveBlkCore_not_relator_handleFree`: one **core pair** requires a handle.
  This file proves the **separation** requires a handle, at every marking.  The two are
  independent: that one excludes `h = 0` for a fixed `(sigma, x0)` whatever the `x1` slot and
  says nothing about separations; this one excludes the separation at every marking and says
  nothing about which core pairs are completable.
* `GradedSigmaFive.sigFourRead_diag_even_of_abelRows` is the class-**four** statement of exactly
  this shape, from exactly this hypothesis (the relator's abelian rows, no gauge).  ⭐ The
  class-five statement proved here is its transposition one level up, and it is the first time
  the class-five bit has been closed at `h = 0`.  Wave 58 recorded that the class-five diagonal
  is a *nonzero* functional where the class-four one vanishes identically; that remains true,
  and is not in tension with this file: the functional is nonzero, and it is nonetheless in the
  ideal the relator's own rows generate.

## ⚠⚠ What this does NOT do, and misreadings to refuse

1. **It does not let any committed statement drop `0 < h`.**  Every class-five statement of the
   stack is indexed by a handle `j : Fin h`, so `0 < h` is in the context before the separation
   is consulted; this is `GradedFiveLive`'s `liveBlkHom_pos_free` and `GradedBlockFrame`'s
   Honesty 1, and it applies verbatim here.  ⚠ What the forcing buys is architectural: the
   handle in the committed witnesses is **necessary**, not incidental, and the class-five
   separation is unavailable to a handle-free marking.  Any report saying a hypothesis was
   dropped is wrong.
2. ⚠ **It is not a block statement.**  Nothing here reads `SqU6.blockRead`, `blockPar` or
   `blockParCD`; `SqU6.pos_of_blockRead_odd` is not used, invoked or needed.  W63-SECOND's
   correction (the committed class-five points are not block-blind, only their core pairs are)
   therefore touches nothing here, and neither does W62's `exists_blockPar_odd_iff_pos`.
3. ⚠ **`h = 0` is load-bearing and the tree contains the witness that says so.**
   `sepZero_fiveWit_bit_odd` records ONE fact: at every `h >= 1` the `a0 = a1` dressing of
   `GradedFiveForce.fiveWit` has class-five bit `1`.  ⚠ It does not also say the relator dies
   there, and the two properties sit at DIFFERENT dressing values: the kill is
   `GradedFiveForce.sqRelWord_fiveWit_triv` at `v = 1`, while the bit is read at `v = forceX`,
   where the relator is `liftC6 7`.  The row expansion is not contradicted: at `h >= 1` the
   relator pins the core word to the handle word's inverse rather than to `1`, so the nine rows
   the response reads are free to be odd.  ⭐ That is also the sharpest reading of what a handle
   is *for* at class five: it is what lets the core word be non-trivial while the relator dies.
4. ⚠ **The statement is about the `a0 = a1` dressing only.**  `sigFiveDress m v` at a general
   `v` is not covered, and the response there is genuinely different: the `(3,5)` and `(4,6)`
   rows do move, two of the nine (`SqU6.sqWord_diagDress_low` is a statement about `v = m 1` and
   about nothing else).  Do not read this as "no sigma dressing separates at `h = 0`".
5. ⚠ **It says nothing about class six and above**, and nothing about whether an `h = 0`
   marking can separate at some other coordinate: the six high rows are proved **even**, not
   zero, and `SqU6.sqWord_diagDress_low` gives the nine low rows exactly.

## PROVED versus MEASURED

**PROVED** (no `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8` tuples):
the shift endomorphism and the four transported row lemmas; the nine rows of the response that
vanish identically; the six response identities; the gauge collapse; the `h = 0` evenness at the
tuple level and at the hom level; the forcing at both levels; the two calibration points.

**MEASURED** (`scripts/w64_sep0h/`, certified output in `scripts/w64_sep0h/results/`; plain
Python, exact integer arithmetic, no `sympy`): the coordinate law against honest integer
`6 x 6` matrices written from scratch here; every emitted witness against exact integer
evaluation; the minimality of every hypothesis of the gauge collapse; wave 58's closed form
rederived; and the sweep of `h = 0` markings that motivated the question.

## Contents

* **1** ⭐ the shift endomorphism, and the four core-word rows it transports;
* **2** the nine rows the `a0 = a1` dressing does not move, over any ring;
* **3** ⭐⭐⭐ the row expansion of the response, and ⭐ its gauge collapse;
* **4** the abelian rows, and ⭐⭐⭐ the `h = 0` evenness at the tuple level;
* **5** ⭐⭐⭐ the forcing, and its hom form through the class-five gate;
* **6** calibration: the committed `h = 0` completion, and the `h >= 1` separation;
* **7** axiom pins.

## Merge notes

Nothing is redefined.  Reused, with sources: `SqU6`, `sqWord`, `sigFiveDress`,
`sigFiveDress_zero`, `sigFiveDress_one`, `sigFiveDress_two`, `SqU6.sqWord_a`, `SqU6.sqWord_b`,
`SqU6.sqWord_c`, `SqU6.sqWord_d`, `SqU6.sqWord_e`, `SqU6.sqWord_f`, `SqU6.sqWord_j`,
`SqU6.toU4LL`, `SqU6.toU4LL_apply`, `SqU6.mul_a` .. `SqU6.mul_n`, `SqU6.one_a` .. `SqU6.one_o`,
`sqU6Balance_gen`, `sqGen`, `DSq` from `GradedFive`; `sqRank`, `sqRelWord`, `sqRelWord_zero`,
`map_sqWord` from `Cores`; `sqU4Core` from `GradedThree`; `selPar`, `selPar_eq_zero_iff` from
`GradedSelect`; `SqU6.sqWord_m`, `SqU6.sqWord_o`, `sqU6Core`, `sqU6Core4`, `sqU6CoreTwo`,
`SqU6.sqWord_f_core` from `GradedFiveDefect`; `SqU6.sqWord_i` from `GradedFiveBlind`;
`SqU6.sqWord_h` from `GradedBlockSecond`; `abelRow_even` from `GradedSigmaFive`; `fiveWit`,
`forceX`, `sqRelWord_fiveWit_diag`, `liftC6_o`, `fiveSigMark` from `GradedFiveForce`; `stageX`
from `GradedFiveStageFour`; `blindCoreY`, `sqRelWord_blindCore_handleFree` from
`GradedFiveLive`.

New public names.  Three concurrent lanes (`w64-census5`, `w64-psi4`, `w64-verify`) do not
import this file, so every name carries a `sepZero`, `sepShiftRow`, `diagDress` or `_of_shift`
marker chosen so that a collision is essentially impossible; in particular the four transported
row lemmas are deliberately **not** called `SqU6.sqWord_g` and so on, because those are the
names a sibling would pick.

`SqU6.sepShiftRow`, `SqU6.sepShiftRow_a` .. `SqU6.sepShiftRow_o`, `SqU6.sqWord_g_of_shift`,
`SqU6.sqWord_k_of_shift`, `SqU6.sqWord_l_of_shift`, `SqU6.sqWord_n_of_shift`,
`SqU6.sqWord_diagDress_low`, `sepZeroWitJ`, `sepZeroWitK`, `sepZeroWitL`, `sepZeroWitM`,
`sepZeroWitN`, `sepZeroWitO`, `sepZeroWitGauge`, `SqU6.sqWord_diagDress_j`,
`SqU6.sqWord_diagDress_k`, `SqU6.sqWord_diagDress_l`, `SqU6.sqWord_diagDress_m`,
`SqU6.sqWord_diagDress_n`, `SqU6.sqWord_diagDress_o`, `SqU6.sqWord_diagDress_o_gauge`,
`sepZero_abelRows_even`, `SqU6.selPar_sqWord_diagDress_o`,
`SqU6.selPar_sqWord_diagDress_high`, `sepZero_bit_even`, `sepZero_pos_of_bit_odd`,
`sepZero_bit_even_hom`, `sepZero_pos_of_bit_odd_hom`, `sepZero_blindCore_bit`,
`sepZero_fiveWit_bit_odd`.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  All prints are **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.
-/

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The shift endomorphism, and the four rows it transports -/

section Shift

variable {R : Type} [CommRing R]

/-- ⭐ **The shift endomorphism of the class-five carrier.**  It carries the `(2..6)`-corner of
a unitriangular matrix onto the `(1..5)`-corner and kills the sixth column, so it is the
composite of the right `U_5`-quotient with the padding of `U_5` into the top-left corner of
`U_6`.  Both halves are monoid homomorphisms, and this is written directly to avoid introducing
a padding map the tree does not have.

It exists here for one purpose: the tree has closed forms for the core word's rows `f`, `h`,
`i`, `j`, `m`, and the four remaining rows `g`, `k`, `l`, `n` are their images under this shift.
⚠ Not all at one step: `g`, `k` and `n` take ONE application, but `l` takes TWO (it is the shift
of `k`, itself the shift of `j`), which is why `SqU6.sqWord_l_of_shift` iterates `sepShiftRow`.
Naturality of `sqWord` does the rest. -/
def SqU6.sepShiftRow : SqU6 R →* SqU6 R where
  toFun p := ⟨p.b, p.c, p.d, p.e, 0, p.g, p.h, p.i, 0, p.k, p.l, 0, p.n, 0, 0⟩
  map_one' := rfl
  map_mul' p q := by
    ext <;>
      simp only [SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f,
        SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m,
        SqU6.mul_n, SqU6.mul_o] <;> ring

@[simp] theorem SqU6.sepShiftRow_a (p : SqU6 R) : (SqU6.sepShiftRow p).a = p.b := rfl
@[simp] theorem SqU6.sepShiftRow_b (p : SqU6 R) : (SqU6.sepShiftRow p).b = p.c := rfl
@[simp] theorem SqU6.sepShiftRow_c (p : SqU6 R) : (SqU6.sepShiftRow p).c = p.d := rfl
@[simp] theorem SqU6.sepShiftRow_d (p : SqU6 R) : (SqU6.sepShiftRow p).d = p.e := rfl
@[simp] theorem SqU6.sepShiftRow_e (p : SqU6 R) : (SqU6.sepShiftRow p).e = 0 := rfl
@[simp] theorem SqU6.sepShiftRow_f (p : SqU6 R) : (SqU6.sepShiftRow p).f = p.g := rfl
@[simp] theorem SqU6.sepShiftRow_g (p : SqU6 R) : (SqU6.sepShiftRow p).g = p.h := rfl
@[simp] theorem SqU6.sepShiftRow_h (p : SqU6 R) : (SqU6.sepShiftRow p).h = p.i := rfl
@[simp] theorem SqU6.sepShiftRow_i (p : SqU6 R) : (SqU6.sepShiftRow p).i = 0 := rfl
@[simp] theorem SqU6.sepShiftRow_j (p : SqU6 R) : (SqU6.sepShiftRow p).j = p.k := rfl
@[simp] theorem SqU6.sepShiftRow_k (p : SqU6 R) : (SqU6.sepShiftRow p).k = p.l := rfl
@[simp] theorem SqU6.sepShiftRow_l (p : SqU6 R) : (SqU6.sepShiftRow p).l = 0 := rfl
@[simp] theorem SqU6.sepShiftRow_m (p : SqU6 R) : (SqU6.sepShiftRow p).m = p.n := rfl
@[simp] theorem SqU6.sepShiftRow_n (p : SqU6 R) : (SqU6.sepShiftRow p).n = 0 := rfl
@[simp] theorem SqU6.sepShiftRow_o (p : SqU6 R) : (SqU6.sepShiftRow p).o = 0 := rfl

/-- **The `(2,4)` row of the core word**, the committed `SqU6.sqWord_f` shifted one step.  It is
`SqU6.sqWord_h` with the columns `(c, d)` replaced by `(b, c)`. -/
theorem SqU6.sqWord_g_of_shift (s x y : SqU6 R) :
    (sqWord s x y).g = -4 * x.g + 2 * y.g
      + (s.b * x.c - s.c * x.b + 10 * (x.b * x.c) - 8 * (x.b * y.c) + y.b * y.c) := by
  have h := congrArg SqU6.f (map_sqWord (SqU6.sepShiftRow (R := R)) s x y)
  rw [SqU6.sqWord_f_core, sqU6CoreTwo] at h
  simpa using h

/-- **The `(2,5)` row of the core word**, the committed class-three row `SqU6.sqWord_j` shifted
one step. -/
theorem SqU6.sqWord_k_of_shift (s x y : SqU6 R) :
    (sqWord s x y).k = -4 * x.k + 2 * y.k
      + sqU4Core (SqU6.toU4LL (SqU6.sepShiftRow s)) (SqU6.toU4LL (SqU6.sepShiftRow x))
        (SqU6.toU4LL (SqU6.sepShiftRow y)) := by
  have h := congrArg SqU6.j (map_sqWord (SqU6.sepShiftRow (R := R)) s x y)
  rw [SqU6.sqWord_j] at h
  simpa using h

/-- **The `(3,6)` row of the core word**, the committed class-three row shifted **twice**. -/
theorem SqU6.sqWord_l_of_shift (s x y : SqU6 R) :
    (sqWord s x y).l = -4 * x.l + 2 * y.l
      + sqU4Core (SqU6.toU4LL (SqU6.sepShiftRow (SqU6.sepShiftRow s)))
        (SqU6.toU4LL (SqU6.sepShiftRow (SqU6.sepShiftRow x)))
        (SqU6.toU4LL (SqU6.sepShiftRow (SqU6.sepShiftRow y))) := by
  have h := congrArg SqU6.k (map_sqWord (SqU6.sepShiftRow (R := R)) s x y)
  rw [SqU6.sqWord_k_of_shift] at h
  simpa using h

/-- **The `(2,6)` row of the core word**, the committed class-four row `SqU6.sqWord_m` shifted
one step.  This is the row the class-five response reads through the `x0` slot's first abelian
column, and it is the one wave 58 could not name at class four. -/
theorem SqU6.sqWord_n_of_shift (s x y : SqU6 R) :
    (sqWord s x y).n = -4 * x.n + 2 * y.n
      + sqU6Core4 (SqU6.sepShiftRow s) (SqU6.sepShiftRow x) (SqU6.sepShiftRow y) := by
  have h := congrArg SqU6.m (map_sqWord (SqU6.sepShiftRow (R := R)) s x y)
  rw [SqU6.sqWord_m] at h
  simpa using h

end Shift

/-! ## 2 The nine rows the `a0 = a1` dressing does not move -/

section LowRows

variable {R : Type} [CommRing R] (s x y : SqU6 R)

/-- ⭐⭐ **The `a0 = a1` dressing moves no row of class at most two.**  Over any commutative
ring, with no hypothesis at all.

The five abelian rows do not read the sigma slot; each of the four class-two rows reads it
through an antisymmetric pairing against the `x0` slot, and on this dressing that pairing is
against the `x0` slot itself.  ⚠ This is a statement about the dressing `v = x` only: at a
general `v` the `(3,5)` and `(4,6)` rows do move, which is `docs/dyadic/w58-sigma5-note.md`
section 2's response table. -/
theorem SqU6.sqWord_diagDress_low :
    (sqWord (s * x) x y).a = (sqWord s x y).a ∧ (sqWord (s * x) x y).b = (sqWord s x y).b ∧
      (sqWord (s * x) x y).c = (sqWord s x y).c ∧ (sqWord (s * x) x y).d = (sqWord s x y).d ∧
      (sqWord (s * x) x y).e = (sqWord s x y).e ∧ (sqWord (s * x) x y).f = (sqWord s x y).f ∧
      (sqWord (s * x) x y).g = (sqWord s x y).g ∧ (sqWord (s * x) x y).h = (sqWord s x y).h ∧
      (sqWord (s * x) x y).i = (sqWord s x y).i := by
  refine ⟨by rw [SqU6.sqWord_a, SqU6.sqWord_a], by rw [SqU6.sqWord_b, SqU6.sqWord_b],
    by rw [SqU6.sqWord_c, SqU6.sqWord_c], by rw [SqU6.sqWord_d, SqU6.sqWord_d],
    by rw [SqU6.sqWord_e, SqU6.sqWord_e], ?_, ?_, ?_, ?_⟩
  · rw [SqU6.sqWord_f_core, SqU6.sqWord_f_core, sqU6CoreTwo, sqU6CoreTwo, SqU6.mul_a, SqU6.mul_b]
    ring
  · rw [SqU6.sqWord_g_of_shift, SqU6.sqWord_g_of_shift, SqU6.mul_b, SqU6.mul_c]
    ring
  · rw [SqU6.sqWord_h, SqU6.sqWord_h, SqU6.mul_c, SqU6.mul_d]
    ring
  · rw [SqU6.sqWord_i, SqU6.sqWord_i, SqU6.mul_d, SqU6.mul_e]
    ring

end LowRows

/-! ## 3 The row expansion of the response -/

section Response

variable {R : Type} [CommRing R] {s x y : SqU6 R} {xa xc xf xg ya yb yc yd ye : R}

/-- The witness of `SqU6.sqWord_diagDress_j`, machine-emitted by
`scripts/w64_sep0h/derive_sep0h.py` section 4 and certified against exact integer evaluation of
`sqWord` at `1500` random points with even `x1`-abelian columns. -/
def sepZeroWitJ (s x y : SqU6 R) (ya yb yc _yd _ye : R) : R :=
    2 * (x.a * x.g)
    - x.a * y.g
    + 2 * (x.c * x.f)
    - x.c * y.f
    - s.b * x.a * x.c
    + s.c * x.a * x.b
    - 10 * (x.a * x.b * x.c)
    - 4 * (ya * yc * x.b)
    + 8 * (yb * x.a * x.c)
    + 8 * (yc * x.a * x.b)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 80000 in
/-- **The response at the first class-three row `(1,4)`.**  Over an arbitrary commutative
ring, with the five abelian columns of the `x1` slot even and nothing else assumed. -/
theorem SqU6.sqWord_diagDress_j
    (hya : y.a = 2 * ya) (hyb : y.b = 2 * yb) (hyc : y.c = 2 * yc)
    (_hyd : y.d = 2 * yd) (_hye : y.e = 2 * ye) :
    (sqWord (s * x) x y).j = (sqWord s x y).j
      + x.c * (sqWord s x y).f + x.a * (sqWord s x y).g
      + 2 * sepZeroWitJ s x y ya yb yc yd ye := by
  simp only [SqU6.sqWord_f_core, SqU6.sqWord_g_of_shift, 
    SqU6.sqWord_j, 
    sqU6CoreTwo, sqU4Core,
    SqU6.toU4LL_apply, 
    
    
    sepZeroWitJ, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c,
    SqU6.mul_f, SqU6.mul_g, SqU6.mul_j,
    hya, hyb, hyc]
  ring

/-- The witness of `SqU6.sqWord_diagDress_k`, machine-emitted by
`scripts/w64_sep0h/derive_sep0h.py` section 4 and certified against exact integer evaluation of
`sqWord` at `1500` random points with even `x1`-abelian columns. -/
def sepZeroWitK (s x y : SqU6 R) (_ya yb yc yd _ye : R) : R :=
    2 * (x.b * x.h)
    - x.b * y.h
    + 2 * (x.d * x.g)
    - x.d * y.g
    - s.c * x.b * x.d
    + s.d * x.b * x.c
    - 10 * (x.b * x.c * x.d)
    - 4 * (yb * yd * x.c)
    + 8 * (yc * x.b * x.d)
    + 8 * (yd * x.b * x.c)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 80000 in
/-- **The response at the second class-three row `(2,5)`.**  Over an arbitrary commutative
ring, with the five abelian columns of the `x1` slot even and nothing else assumed. -/
theorem SqU6.sqWord_diagDress_k
    (_hya : y.a = 2 * ya) (hyb : y.b = 2 * yb) (hyc : y.c = 2 * yc)
    (hyd : y.d = 2 * yd) (_hye : y.e = 2 * ye) :
    (sqWord (s * x) x y).k = (sqWord s x y).k
      + x.d * (sqWord s x y).g + x.b * (sqWord s x y).h
      + 2 * sepZeroWitK s x y ya yb yc yd ye := by
  simp only [SqU6.sqWord_g_of_shift, SqU6.sqWord_h,
    SqU6.sqWord_k_of_shift, 
    sqU4Core,
    SqU6.toU4LL_apply, SqU6.sepShiftRow_a, SqU6.sepShiftRow_b, SqU6.sepShiftRow_c,
    SqU6.sepShiftRow_f, SqU6.sepShiftRow_g,
    SqU6.sepShiftRow_j, 
    sepZeroWitK, SqU6.mul_b, SqU6.mul_c,
    SqU6.mul_d, SqU6.mul_g, SqU6.mul_h, 
    SqU6.mul_k, hyb, hyc, hyd]
  ring

/-- The witness of `SqU6.sqWord_diagDress_l`, machine-emitted by
`scripts/w64_sep0h/derive_sep0h.py` section 4 and certified against exact integer evaluation of
`sqWord` at `1500` random points with even `x1`-abelian columns. -/
def sepZeroWitL (s x y : SqU6 R) (_ya _yb yc yd ye : R) : R :=
    2 * (x.c * x.i)
    - x.c * y.i
    + 2 * (x.e * x.h)
    - x.e * y.h
    - s.d * x.c * x.e
    + s.e * x.c * x.d
    - 10 * (x.c * x.d * x.e)
    - 4 * (yc * ye * x.d)
    + 8 * (yd * x.c * x.e)
    + 8 * (ye * x.c * x.d)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 80000 in
/-- **The response at the third class-three row `(3,6)`.**  Over an arbitrary commutative
ring, with the five abelian columns of the `x1` slot even and nothing else assumed. -/
theorem SqU6.sqWord_diagDress_l
    (_hya : y.a = 2 * ya) (_hyb : y.b = 2 * yb) (hyc : y.c = 2 * yc)
    (hyd : y.d = 2 * yd) (hye : y.e = 2 * ye) :
    (sqWord (s * x) x y).l = (sqWord s x y).l
      + x.e * (sqWord s x y).h + x.c * (sqWord s x y).i
      + 2 * sepZeroWitL s x y ya yb yc yd ye := by
  simp only [SqU6.sqWord_h,
    SqU6.sqWord_i, SqU6.sqWord_l_of_shift,
    sqU4Core,
    SqU6.toU4LL_apply, SqU6.sepShiftRow_a, SqU6.sepShiftRow_b, SqU6.sepShiftRow_c,
    SqU6.sepShiftRow_d, SqU6.sepShiftRow_f, SqU6.sepShiftRow_g,
    SqU6.sepShiftRow_h, SqU6.sepShiftRow_j, SqU6.sepShiftRow_k,
    sepZeroWitL, SqU6.mul_c,
    SqU6.mul_d, SqU6.mul_e, SqU6.mul_h, SqU6.mul_i, 
    SqU6.mul_l, hyc, hyd, hye]
  ring

/-- The witness of `SqU6.sqWord_diagDress_m`, machine-emitted by
`scripts/w64_sep0h/derive_sep0h.py` section 4 and certified against exact integer evaluation of
`sqWord` at `1500` random points with even `x1`-abelian columns. -/
def sepZeroWitM (s x y : SqU6 R) (ya yb yc yd _ye : R) : R :=
    2 * (x.a * x.k)
    - x.a * y.k
    + 2 * (x.d * x.j)
    - x.d * y.j
    + 4 * (x.f * x.h)
    - x.f * y.h
    - x.h * y.f
    - s.b * x.a * x.h
    - s.c * x.d * x.f
    + s.d * x.a * x.g
    + s.d * x.c * x.f
    - s.g * x.a * x.d
    + s.h * x.a * x.b
    - 8 * (x.a * x.b * x.h)
    + 3 * (x.a * x.b * y.h)
    - 8 * (x.a * x.d * x.g)
    + 3 * (x.a * x.d * y.g)
    - 10 * (x.c * x.d * x.f)
    - 2 * (ya * x.b * y.h)
    - 4 * (ya * yd * x.g)
    + 8 * (yb * x.a * x.h)
    + 8 * (yc * x.d * x.f)
    + 8 * (yd * x.a * x.g)
    + 8 * (yd * x.c * x.f)
    - 2 * (yd * x.c * y.f)
    + s.b * s.c * x.a * x.d
    - s.b * s.d * x.a * x.c
    + 3 * (s.b * x.a * x.c * x.d)
    - 2 * (s.c * x.a * x.b * x.d)
    - s.d * x.a * x.b * x.c
    + 10 * (x.a * x.b * x.c * x.d)
    + 2 * (ya * yc * s.b * x.d)
    - 2 * (ya * yc * s.d * x.b)
    - 2 * (ya * yc * x.b * x.d)
    - 2 * (ya * yd * s.b * x.c)
    + 2 * (ya * yd * s.c * x.b)
    + 2 * (ya * yd * x.b * x.c)
    - 2 * (yb * yc * s.a * x.d)
    - 2 * (yb * yc * s.d * x.a)
    - 2 * (yb * yc * x.a * x.d)
    + 2 * (yb * yd * s.a * x.c)
    + 6 * (yb * yd * s.c * x.a)
    + 18 * (yb * yd * x.a * x.c)
    - 2 * (yc * s.a * x.b * x.d)
    + 2 * (yc * s.b * x.a * x.d)
    - 12 * (yc * x.a * x.b * x.d)
    - 4 * (yc * yd * s.b * x.a)
    - 4 * (yc * yd * x.a * x.b)
    + 2 * (yd * s.a * x.b * x.c)
    - 6 * (yd * s.b * x.a * x.c)
    + 4 * (yd * s.c * x.a * x.b)
    - 12 * (yd * x.a * x.b * x.c)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 80000 in
/-- **The response at the first class-four row `(1,5)`.**  Over an arbitrary commutative
ring, with the five abelian columns of the `x1` slot even and nothing else assumed. -/
theorem SqU6.sqWord_diagDress_m
    (hya : y.a = 2 * ya) (hyb : y.b = 2 * yb) (hyc : y.c = 2 * yc)
    (hyd : y.d = 2 * yd) (_hye : y.e = 2 * ye) :
    (sqWord (s * x) x y).m = (sqWord s x y).m
      + x.h * (sqWord s x y).f + x.a * x.d * (sqWord s x y).g
      + (x.f + x.a * x.b) * (sqWord s x y).h + x.d * (sqWord s x y).j
      + x.a * (sqWord s x y).k
      + 2 * sepZeroWitM s x y ya yb yc yd ye := by
  simp only [SqU6.sqWord_f_core, SqU6.sqWord_g_of_shift, SqU6.sqWord_h,
    SqU6.sqWord_j, SqU6.sqWord_k_of_shift, 
    SqU6.sqWord_m, sqU6Core4, sqU6CoreTwo, sqU4Core,
    SqU6.toU4LL_apply, SqU6.sepShiftRow_a, SqU6.sepShiftRow_b, SqU6.sepShiftRow_c,
    SqU6.sepShiftRow_f, SqU6.sepShiftRow_g,
    SqU6.sepShiftRow_j, 
    sepZeroWitM, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c,
    SqU6.mul_d, SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_j,
    SqU6.mul_k, hya, hyb, hyc, hyd]
  ring

/-- The witness of `SqU6.sqWord_diagDress_n`, machine-emitted by
`scripts/w64_sep0h/derive_sep0h.py` section 4 and certified against exact integer evaluation of
`sqWord` at `1500` random points with even `x1`-abelian columns. -/
def sepZeroWitN (s x y : SqU6 R) (_ya yb yc yd ye : R) : R :=
    2 * (x.b * x.l)
    - x.b * y.l
    + 2 * (x.e * x.k)
    - x.e * y.k
    + 4 * (x.g * x.i)
    - x.g * y.i
    - x.i * y.g
    - s.c * x.b * x.i
    - s.d * x.e * x.g
    + s.e * x.b * x.h
    + s.e * x.d * x.g
    - s.h * x.b * x.e
    + s.i * x.b * x.c
    - 8 * (x.b * x.c * x.i)
    + 3 * (x.b * x.c * y.i)
    - 8 * (x.b * x.e * x.h)
    + 3 * (x.b * x.e * y.h)
    - 10 * (x.d * x.e * x.g)
    - 2 * (yb * x.c * y.i)
    - 4 * (yb * ye * x.h)
    + 8 * (yc * x.b * x.i)
    + 8 * (yd * x.e * x.g)
    + 8 * (ye * x.b * x.h)
    + 8 * (ye * x.d * x.g)
    - 2 * (ye * x.d * y.g)
    + s.c * s.d * x.b * x.e
    - s.c * s.e * x.b * x.d
    + 3 * (s.c * x.b * x.d * x.e)
    - 2 * (s.d * x.b * x.c * x.e)
    - s.e * x.b * x.c * x.d
    + 10 * (x.b * x.c * x.d * x.e)
    + 2 * (yb * yd * s.c * x.e)
    - 2 * (yb * yd * s.e * x.c)
    - 2 * (yb * yd * x.c * x.e)
    - 2 * (yb * ye * s.c * x.d)
    + 2 * (yb * ye * s.d * x.c)
    + 2 * (yb * ye * x.c * x.d)
    - 2 * (yc * yd * s.b * x.e)
    - 2 * (yc * yd * s.e * x.b)
    - 2 * (yc * yd * x.b * x.e)
    + 2 * (yc * ye * s.b * x.d)
    + 6 * (yc * ye * s.d * x.b)
    + 18 * (yc * ye * x.b * x.d)
    - 2 * (yd * s.b * x.c * x.e)
    + 2 * (yd * s.c * x.b * x.e)
    - 12 * (yd * x.b * x.c * x.e)
    - 4 * (yd * ye * s.c * x.b)
    - 4 * (yd * ye * x.b * x.c)
    + 2 * (ye * s.b * x.c * x.d)
    - 6 * (ye * s.c * x.b * x.d)
    + 4 * (ye * s.d * x.b * x.c)
    - 12 * (ye * x.b * x.c * x.d)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 80000 in
/-- **The response at the second class-four row `(2,6)`.**  Over an arbitrary commutative
ring, with the five abelian columns of the `x1` slot even and nothing else assumed. -/
theorem SqU6.sqWord_diagDress_n
    (_hya : y.a = 2 * ya) (hyb : y.b = 2 * yb) (hyc : y.c = 2 * yc)
    (hyd : y.d = 2 * yd) (hye : y.e = 2 * ye) :
    (sqWord (s * x) x y).n = (sqWord s x y).n
      + x.i * (sqWord s x y).g + x.b * x.e * (sqWord s x y).h
      + (x.g + x.b * x.c) * (sqWord s x y).i + x.e * (sqWord s x y).k
      + x.b * (sqWord s x y).l
      + 2 * sepZeroWitN s x y ya yb yc yd ye := by
  simp only [SqU6.sqWord_g_of_shift, SqU6.sqWord_h,
    SqU6.sqWord_i, SqU6.sqWord_k_of_shift, SqU6.sqWord_l_of_shift,
    SqU6.sqWord_n_of_shift, sqU6Core4, sqU4Core,
    SqU6.toU4LL_apply, SqU6.sepShiftRow_a, SqU6.sepShiftRow_b, SqU6.sepShiftRow_c,
    SqU6.sepShiftRow_d, SqU6.sepShiftRow_f, SqU6.sepShiftRow_g,
    SqU6.sepShiftRow_h, SqU6.sepShiftRow_j, SqU6.sepShiftRow_k,
    sepZeroWitN, SqU6.mul_b, SqU6.mul_c,
    SqU6.mul_d, SqU6.mul_e, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, 
    SqU6.mul_k, SqU6.mul_l, hyb, hyc, hyd, hye]
  ring

/-- The witness of `SqU6.sqWord_diagDress_o`, machine-emitted by
`scripts/w64_sep0h/derive_sep0h.py` section 4 and certified against exact integer evaluation of
`sqWord` at `1500` random points with even `x1`-abelian columns. -/
def sepZeroWitO (s x y : SqU6 R) (ya yb yc yd ye : R) : R :=
    2 * (x.a * x.n)
    - x.a * y.n
    + 2 * (x.e * x.m)
    - x.e * y.m
    + 4 * (x.f * x.l)
    - x.f * y.l
    + 4 * (x.i * x.j)
    - x.i * y.j
    - x.j * y.i
    - x.l * y.f
    - s.b * x.a * x.l
    - s.c * x.f * x.i
    - s.d * x.e * x.j
    + s.e * x.a * x.k
    + s.e * x.d * x.j
    + s.e * x.f * x.h
    - s.g * x.a * x.i
    - s.h * x.e * x.f
    + s.i * x.a * x.g
    + s.i * x.c * x.f
    - s.k * x.a * x.e
    + s.l * x.a * x.b
    - 8 * (x.a * x.b * x.l)
    + 3 * (x.a * x.b * y.l)
    - 8 * (x.a * x.e * x.k)
    + 3 * (x.a * x.e * y.k)
    - 6 * (x.a * x.g * x.i)
    + 3 * (x.a * x.g * y.i)
    + 3 * (x.a * x.i * y.g)
    - 8 * (x.c * x.f * x.i)
    + 3 * (x.c * x.f * y.i)
    - x.c * y.f * y.i
    - 10 * (x.d * x.e * x.j)
    - 8 * (x.e * x.f * x.h)
    + 3 * (x.e * x.f * y.h)
    - 2 * (ya * x.b * y.l)
    - 2 * (ya * x.g * y.i)
    - 4 * (ya * ye * x.k)
    + 8 * (yb * x.a * x.l)
    + 8 * (yc * x.f * x.i)
    + 8 * (yd * x.e * x.j)
    + 8 * (ye * x.a * x.k)
    + 8 * (ye * x.d * x.j)
    - 2 * (ye * x.d * y.j)
    + 8 * (ye * x.f * x.h)
    - 2 * (ye * x.h * y.f)
    + s.a * x.b * x.c * y.i
    - s.a * x.b * x.e * y.h
    + s.b * s.c * x.a * x.i
    - s.b * s.e * x.a * x.h
    + s.b * s.h * x.a * x.e
    - s.b * s.i * x.a * x.c
    + 3 * (s.b * x.a * x.c * x.i)
    - 3 * (s.b * x.a * x.c * y.i)
    + 3 * (s.b * x.a * x.e * x.h)
    + s.b * x.a * x.e * y.h
    + s.c * s.d * x.e * x.f
    - s.c * s.e * x.d * x.f
    - 2 * (s.c * x.a * x.b * x.i)
    + 2 * (s.c * x.a * x.b * y.i)
    + 3 * (s.c * x.d * x.e * x.f)
    + s.d * s.g * x.a * x.e
    - 2 * (s.d * x.a * x.e * x.g)
    - 2 * (s.d * x.c * x.e * x.f)
    - s.e * s.g * x.a * x.d
    - s.e * x.a * x.b * x.h
    - s.e * x.a * x.d * x.g
    - s.e * x.c * x.d * x.f
    + 3 * (s.g * x.a * x.d * x.e)
    - 2 * (s.h * x.a * x.b * x.e)
    - s.i * x.a * x.b * x.c
    + 12 * (x.a * x.b * x.c * x.i)
    - 7 * (x.a * x.b * x.c * y.i)
    + 12 * (x.a * x.b * x.e * x.h)
    - 7 * (x.a * x.b * x.e * y.h)
    + 10 * (x.a * x.d * x.e * x.g)
    + 10 * (x.c * x.d * x.e * x.f)
    - ya * s.b * x.c * y.i
    + ya * s.b * x.e * y.h
    + ya * s.c * x.b * y.i
    - ya * s.e * x.b * y.h
    + ya * x.b * x.c * y.i
    - ya * x.b * x.e * y.h
    + 2 * (ya * yc * s.b * x.i)
    - 2 * (ya * yc * s.i * x.b)
    - 2 * (ya * yc * x.b * x.i)
    - 2 * (ya * yd * s.e * x.g)
    + 2 * (ya * yd * s.g * x.e)
    - 2 * (ya * yd * x.e * x.g)
    - 2 * (ya * ye * s.b * x.h)
    + 2 * (ya * ye * s.d * x.g)
    - 2 * (ya * ye * s.g * x.d)
    + 2 * (ya * ye * s.h * x.b)
    + 2 * (ya * ye * x.b * x.h)
    + 2 * (ya * ye * x.d * x.g)
    + yb * s.a * x.c * y.i
    - yb * s.a * x.e * y.h
    + 3 * (yb * s.c * x.a * y.i)
    - yb * s.e * x.a * y.h
    + 9 * (yb * x.a * x.c * y.i)
    - yb * x.a * x.e * y.h
    - 2 * (yb * yc * s.a * x.i)
    - 2 * (yb * yc * s.i * x.a)
    - 2 * (yb * yc * x.a * x.i)
    + 2 * (yb * ye * s.a * x.h)
    + 6 * (yb * ye * s.h * x.a)
    + 18 * (yb * ye * x.a * x.h)
    - 2 * (yc * s.a * x.b * x.i)
    + 2 * (yc * s.b * x.a * x.i)
    - 2 * (yc * s.b * x.a * y.i)
    - 12 * (yc * x.a * x.b * x.i)
    - 2 * (yc * x.a * x.b * y.i)
    - 2 * (yc * yd * s.e * x.f)
    - 2 * (yc * yd * s.f * x.e)
    - 2 * (yc * yd * x.e * x.f)
    + 6 * (yc * ye * s.d * x.f)
    + 2 * (yc * ye * s.f * x.d)
    + 18 * (yc * ye * x.d * x.f)
    - 2 * (yd * s.a * x.e * x.g)
    - yd * s.a * x.e * y.g
    + 2 * (yd * s.c * x.e * x.f)
    + yd * s.c * x.e * y.f
    - yd * s.e * x.a * y.g
    - yd * s.e * x.c * y.f
    - 2 * (yd * s.f * x.c * x.e)
    + 2 * (yd * s.g * x.a * x.e)
    - 12 * (yd * x.a * x.e * x.g)
    - yd * x.a * x.e * y.g
    - 12 * (yd * x.c * x.e * x.f)
    - yd * x.c * x.e * y.f
    - 4 * (yd * ye * s.c * x.f)
    - 4 * (yd * ye * s.g * x.a)
    - 4 * (yd * ye * x.a * x.g)
    - 4 * (yd * ye * x.c * x.f)
    + 2 * (ye * s.a * x.b * x.h)
    + 2 * (ye * s.a * x.d * x.g)
    + ye * s.a * x.d * y.g
    - 6 * (ye * s.b * x.a * x.h)
    - 2 * (ye * s.b * x.a * y.h)
    - 6 * (ye * s.c * x.d * x.f)
    - ye * s.c * x.d * y.f
    + 4 * (ye * s.d * x.a * x.g)
    + 3 * (ye * s.d * x.a * y.g)
    + 4 * (ye * s.d * x.c * x.f)
    + ye * s.d * x.c * y.f
    + 2 * (ye * s.f * x.c * x.d)
    - 6 * (ye * s.g * x.a * x.d)
    + 4 * (ye * s.h * x.a * x.b)
    - 12 * (ye * x.a * x.b * x.h)
    - 2 * (ye * x.a * x.b * y.h)
    - 12 * (ye * x.a * x.d * x.g)
    + 9 * (ye * x.a * x.d * y.g)
    - 12 * (ye * x.c * x.d * x.f)
    + ye * x.c * x.d * y.f
    - s.b * s.c * s.d * x.a * x.e
    + s.b * s.c * s.e * x.a * x.d
    - 3 * (s.b * s.c * x.a * x.d * x.e)
    + 2 * (s.b * s.d * x.a * x.c * x.e)
    + s.b * s.e * x.a * x.c * x.d
    - 6 * (s.b * x.a * x.c * x.d * x.e)
    + 3 * (s.c * x.a * x.b * x.d * x.e)
    + s.d * x.a * x.b * x.c * x.e
    + 2 * (s.e * x.a * x.b * x.c * x.d)
    - 25 * (x.a * x.b * x.c * x.d * x.e)
    - 2 * (ya * yc * s.d * x.b * x.e)
    - 4 * (ya * yc * yd * s.b * x.e)
    - 4 * (ya * yc * yd * s.e * x.b)
    - 4 * (ya * yc * yd * x.b * x.e)
    + 8 * (ya * yc * ye * s.b * x.d)
    + 8 * (ya * yc * ye * s.d * x.b)
    + 8 * (ya * yc * ye * x.b * x.d)
    + 2 * (ya * yd * s.c * s.e * x.b)
    + 2 * (ya * yd * s.c * x.b * x.e)
    + 2 * (ya * yd * s.e * x.b * x.c)
    + 2 * (ya * yd * x.b * x.c * x.e)
    - 4 * (ya * yd * ye * s.b * x.c)
    - 4 * (ya * yd * ye * s.c * x.b)
    - 4 * (ya * yd * ye * x.b * x.c)
    - 2 * (ya * ye * s.c * s.d * x.b)
    - 2 * (ya * ye * s.d * x.b * x.c)
    - 2 * (ya * ye * x.b * x.c * x.d)
    - 2 * (yb * yc * s.d * x.a * x.e)
    + 4 * (yb * yc * yd * s.a * x.e)
    + 4 * (yb * yc * yd * s.e * x.a)
    + 4 * (yb * yc * yd * x.a * x.e)
    - 8 * (yb * yc * ye * s.a * x.d)
    - 8 * (yb * yc * ye * s.d * x.a)
    - 8 * (yb * yc * ye * x.a * x.d)
    - 2 * (yb * yd * s.a * s.c * x.e)
    + 2 * (yb * yd * s.c * s.e * x.a)
    - 4 * (yb * yd * s.c * x.a * x.e)
    + 8 * (yb * yd * s.e * x.a * x.c)
    + 8 * (yb * yd * x.a * x.c * x.e)
    + 4 * (yb * yd * ye * s.a * x.c)
    + 4 * (yb * yd * ye * s.c * x.a)
    + 4 * (yb * yd * ye * x.a * x.c)
    + 2 * (yb * ye * s.a * s.c * x.d)
    - 2 * (yb * ye * s.c * s.d * x.a)
    + 10 * (yb * ye * s.c * x.a * x.d)
    - 8 * (yb * ye * s.d * x.a * x.c)
    - 8 * (yb * ye * x.a * x.c * x.d)
    + 2 * (yc * yd * s.a * s.b * x.e)
    + 6 * (yc * yd * s.b * x.a * x.e)
    + 6 * (yc * yd * s.e * x.a * x.b)
    + 6 * (yc * yd * x.a * x.b * x.e)
    - 2 * (yc * ye * s.a * s.b * x.d)
    - 4 * (yc * ye * s.a * x.b * x.d)
    - 4 * (yc * ye * s.b * s.d * x.a)
    - 6 * (yc * ye * s.b * x.a * x.d)
    - 22 * (yc * ye * s.d * x.a * x.b)
    - 50 * (yc * ye * x.a * x.b * x.d)
    + 2 * (yd * s.a * s.b * x.c * x.e)
    - 2 * (yd * s.a * s.c * x.b * x.e)
    + 8 * (yd * s.a * x.b * x.c * x.e)
    - 8 * (yd * s.b * x.a * x.c * x.e)
    + 28 * (yd * x.a * x.b * x.c * x.e)
    + 4 * (yd * ye * s.a * x.b * x.c)
    + 4 * (yd * ye * s.b * s.c * x.a)
    - 8 * (yd * ye * s.b * x.a * x.c)
    + 20 * (yd * ye * s.c * x.a * x.b)
    + 16 * (yd * ye * x.a * x.b * x.c)
    - 2 * (ye * s.a * s.b * x.c * x.d)
    + 2 * (ye * s.a * s.c * x.b * x.d)
    - 8 * (ye * s.a * x.b * x.c * x.d)
    + 4 * (ye * s.b * s.c * x.a * x.d)
    - 4 * (ye * s.b * s.d * x.a * x.c)
    + 20 * (ye * s.b * x.a * x.c * x.d)
    - 8 * (ye * s.c * x.a * x.b * x.d)
    - 4 * (ye * s.d * x.a * x.b * x.c)
    + 28 * (ye * x.a * x.b * x.c * x.d)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 80000 in
/-- **The response at ⭐⭐⭐ the class-five row `(1,6)`.**  Over an arbitrary commutative
ring, with the five abelian columns of the `x1` slot even and nothing else assumed. -/
theorem SqU6.sqWord_diagDress_o
    (hya : y.a = 2 * ya) (hyb : y.b = 2 * yb) (hyc : y.c = 2 * yc)
    (hyd : y.d = 2 * yd) (hye : y.e = 2 * ye) :
    (sqWord (s * x) x y).o = (sqWord s x y).o
      + x.l * (sqWord s x y).f + x.a * x.i * (sqWord s x y).g
      + (x.e * x.f + x.a * x.b * x.e) * (sqWord s x y).h
      + (x.j + x.a * x.g + x.c * x.f + x.a * x.b * x.c) * (sqWord s x y).i
      + x.i * (sqWord s x y).j + x.a * x.e * (sqWord s x y).k
      + (x.f + x.a * x.b) * (sqWord s x y).l + x.e * (sqWord s x y).m
      + x.a * (sqWord s x y).n
      + 2 * sepZeroWitO s x y ya yb yc yd ye := by
  simp only [SqU6.sqWord_o, SqU6.sqWord_f_core, SqU6.sqWord_g_of_shift, SqU6.sqWord_h,
    SqU6.sqWord_i, SqU6.sqWord_j, SqU6.sqWord_k_of_shift, SqU6.sqWord_l_of_shift,
    SqU6.sqWord_m, SqU6.sqWord_n_of_shift, sqU6Core, sqU6Core4, sqU6CoreTwo, sqU4Core,
    SqU6.toU4LL_apply, SqU6.sepShiftRow_a, SqU6.sepShiftRow_b, SqU6.sepShiftRow_c,
    SqU6.sepShiftRow_d, SqU6.sepShiftRow_f, SqU6.sepShiftRow_g,
    SqU6.sepShiftRow_h, SqU6.sepShiftRow_j, SqU6.sepShiftRow_k,
    sepZeroWitO, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c,
    SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j,
    SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n, hya, hyb, hyc, hyd, hye]
  ring

/-- The witness of `SqU6.sqWord_diagDress_o_gauge`: `149` monomials, machine-emitted by
`scripts/w64_sep0h/derive_sep0h.py` section 5. -/
def sepZeroWitGauge (s x y : SqU6 R) (xa xc xf xg ya yb yc yd ye : R) : R :=
    2 * (x.e * x.m)
    - x.e * y.m
    + 2 * (x.i * x.j)
    - x.j * y.i
    - s.d * x.e * x.j
    + s.e * x.d * x.j
    - 10 * (x.d * x.e * x.j)
    - 2 * (xa * s.b * x.l)
    + xa * s.e * x.k
    - 2 * (xa * s.g * x.i)
    - xa * s.k * x.e
    - 10 * (xa * x.e * x.k)
    + 8 * (xa * x.e * y.k)
    + 2 * (xa * xg * s.i)
    + xa * y.g * y.i
    + 2 * (xa * yb * y.l)
    + 2 * (xa * ye * y.k)
    + xc * s.f * x.i
    + 2 * (xc * xf * s.i)
    - 2 * (xc * y.f * y.i)
    - 2 * (xf * s.c * x.i)
    + xf * s.e * x.h
    - xf * s.h * x.e
    - 10 * (xf * x.e * x.h)
    + 8 * (xf * x.e * y.h)
    + 2 * (xf * yc * y.i)
    + 2 * (xf * ye * y.h)
    + xg * s.a * x.i
    - 4 * (xg * ya * y.i)
    + ya * x.i * y.g
    + 2 * (ya * yb * x.l)
    - 4 * (ya * ye * x.k)
    + yc * x.i * y.f
    + 8 * (yd * x.e * x.j)
    + 8 * (ye * x.d * x.j)
    - 2 * (ye * x.d * y.j)
    - 2 * (ye * x.h * y.f)
    + xa * s.b * s.c * x.i
    - xa * s.b * s.e * x.h
    + xa * s.b * s.h * x.e
    + 3 * (xa * s.b * x.e * x.h)
    + 2 * (xa * s.b * x.e * y.h)
    + xa * s.d * s.g * x.e
    - xa * s.e * s.g * x.d
    + 3 * (xa * s.g * x.d * x.e)
    - 2 * (xa * xc * s.b * s.i)
    + 12 * (xa * xc * s.b * x.i)
    - 8 * (xa * xc * s.b * y.i)
    + 36 * (xa * xc * yb * y.i)
    - 2 * (xa * xg * s.d * x.e)
    - 4 * (xa * xg * s.e * x.d)
    + 40 * (xa * xg * x.d * x.e)
    - 80 * (xa * xg * yd * x.e)
    - 40 * (xa * xg * yd * ye)
    + 8 * (xa * xg * ye * s.d)
    + 2 * (xa * yb * s.c * y.i)
    - 16 * (xa * yb * yc * x.i)
    + 4 * (xa * yb * ye * s.h)
    + 36 * (xa * yb * ye * x.h)
    - 2 * (xa * yc * s.b * y.i)
    + 4 * (xa * yd * s.g * x.e)
    - 4 * (xa * yd * ye * s.g)
    - 8 * (xa * ye * s.b * x.h)
    - 2 * (xa * ye * s.b * y.h)
    + 2 * (xa * ye * s.d * y.g)
    - 8 * (xa * ye * s.g * x.d)
    + 18 * (xa * ye * x.d * y.g)
    - xc * s.a * s.b * x.i
    - 2 * (xc * xf * s.d * x.e)
    - 4 * (xc * xf * s.e * x.d)
    + 40 * (xc * xf * x.d * x.e)
    - 80 * (xc * xf * yd * x.e)
    - 40 * (xc * xf * yd * ye)
    + 8 * (xc * xf * ye * s.d)
    - 2 * (xc * ya * s.b * y.i)
    + 2 * (xc * yb * s.a * y.i)
    - 2 * (xc * yd * s.e * y.f)
    - 4 * (xc * yd * s.f * x.e)
    - 2 * (xc * yd * x.e * y.f)
    + 2 * (xc * ye * s.d * y.f)
    + 4 * (xc * ye * s.f * x.d)
    + 2 * (xc * ye * x.d * y.f)
    + xf * s.c * s.d * x.e
    - xf * s.c * s.e * x.d
    + 3 * (xf * s.c * x.d * x.e)
    + 4 * (xf * yc * ye * s.d)
    + 36 * (xf * yc * ye * x.d)
    + 4 * (xf * yd * s.c * x.e)
    - 4 * (xf * yd * ye * s.c)
    - 8 * (xf * ye * s.c * x.d)
    - 4 * (xg * ya * yd * s.e)
    - 4 * (xg * ya * yd * x.e)
    + 4 * (xg * ya * ye * s.d)
    + 4 * (xg * ya * ye * x.d)
    - 4 * (xg * yd * s.a * x.e)
    + 4 * (xg * ye * s.a * x.d)
    + ya * s.b * x.e * y.h
    + 2 * (ya * yb * s.c * x.i)
    - 2 * (ya * yc * s.b * x.i)
    + 2 * (ya * yd * s.g * x.e)
    - 2 * (ya * ye * s.b * x.h)
    - 2 * (ya * ye * s.g * x.d)
    - yb * s.a * x.e * y.h
    + 2 * (yb * ye * s.a * x.h)
    - 2 * (yc * yd * s.f * x.e)
    + 2 * (yc * ye * s.f * x.d)
    - yd * s.a * x.e * y.g
    + yd * s.c * x.e * y.f
    + ye * s.a * x.d * y.g
    - ye * s.c * x.d * y.f
    - xa * s.b * s.c * s.d * x.e
    + xa * s.b * s.c * s.e * x.d
    - 3 * (xa * s.b * s.c * x.d * x.e)
    + 4 * (xa * xc * s.b * s.d * x.e)
    + 2 * (xa * xc * s.b * s.e * x.d)
    - 12 * (xa * xc * s.b * x.d * x.e)
    + 32 * (xa * xc * yb * yd * s.e)
    + 32 * (xa * xc * yb * yd * x.e)
    + 16 * (xa * xc * yb * yd * ye)
    - 32 * (xa * xc * yb * ye * s.d)
    - 32 * (xa * xc * yb * ye * x.d)
    - 24 * (xa * xc * yd * s.b * x.e)
    - 24 * (xa * xc * yd * ye * s.b)
    - 8 * (xa * xc * ye * s.b * s.d)
    + 48 * (xa * xc * ye * s.b * x.d)
    + 8 * (xa * yb * yc * yd * s.e)
    + 8 * (xa * yb * yc * yd * x.e)
    - 16 * (xa * yb * yc * ye * s.d)
    - 16 * (xa * yb * yc * ye * x.d)
    - 16 * (xa * yb * yd * s.c * x.e)
    + 8 * (xa * yb * yd * ye * s.c)
    + 20 * (xa * yb * ye * s.c * x.d)
    + 16 * (xa * yc * yd * s.b * x.e)
    - 4 * (xa * yc * ye * s.b * s.d)
    - 12 * (xa * yc * ye * s.b * x.d)
    + 4 * (xa * yd * ye * s.b * s.c)
    + 4 * (xa * ye * s.b * s.c * x.d)
    - 8 * (xc * ya * yd * ye * s.b)
    + 8 * (xc * yb * yd * ye * s.a)
    + 4 * (xc * yd * s.a * s.b * x.e)
    - 4 * (xc * ye * s.a * s.b * x.d)
    - 4 * (ya * yc * yd * s.b * x.e)
    + 8 * (ya * yc * ye * s.b * x.d)
    + 4 * (yb * yc * yd * s.a * x.e)
    - 8 * (yb * yc * ye * s.a * x.d)
    - 2 * (yb * yd * s.a * s.c * x.e)
    + 2 * (yb * ye * s.a * s.c * x.d)
    + 2 * (yc * yd * s.a * s.b * x.e)
    - 2 * (yc * ye * s.a * s.b * x.d)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 80000 in
/-- ⭐ **THE GAUGE COLLAPSE.**  On the committed class-two-forced gauge - the `x0` slot's
`(2,3)`-column vanishing and its `(1,2)`, `(3,4)`, `(1,3)`, `(2,4)` coordinates even - seven of
the nine coefficients of `SqU6.sqWord_diagDress_o` become even, and the class-five response is
carried by exactly two rows: the class-four row `(1,5)` weighted by the `x0` slot's fifth
abelian column, and the `(4,6)` row weighted by its first class-three coordinate.

⚠ This is a *reading* of the mechanism, not a strengthening: `SqU6.sqWord_diagDress_o` needs no
gauge at all and everything below is proved from it.  ⭐ Note which two hypotheses are absent:
the `x0` slot's fourth and fifth abelian columns `x_45` and `x_56` are free, and `x_56` is
exactly the datum `docs/dyadic/w58-sigma5-note.md` section 3.1 calls the escape. -/
theorem SqU6.sqWord_diagDress_o_gauge
    (hxa : x.a = 2 * xa) (hxb : x.b = 0) (hxc : x.c = 2 * xc)
    (hxf : x.f = 2 * xf) (hxg : x.g = 2 * xg)
    (hya : y.a = 2 * ya) (hyb : y.b = 2 * yb) (hyc : y.c = 2 * yc)
    (hyd : y.d = 2 * yd) (hye : y.e = 2 * ye) :
    (sqWord (s * x) x y).o = (sqWord s x y).o + x.e * (sqWord s x y).m
      + x.j * (sqWord s x y).i
      + 2 * sepZeroWitGauge s x y xa xc xf xg ya yb yc yd ye := by
  simp only [SqU6.sqWord_o, 
    SqU6.sqWord_i, 
    SqU6.sqWord_m, sqU6Core, sqU6Core4, 
    
    
    
    sepZeroWitGauge, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c,
    SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j,
    SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n, hya, hyb, hyc, hyd, hye, hxa, hxb, hxc,
    hxf, hxg]
  ring

end Response

/-! ## 4 The abelian rows, and the `h = 0` evenness -/

section HandleFree

variable {s x y : SqU6 gr3R}

/-- The relator's own abelian rows at `h = 0`: a trivial core word forces all five abelian
columns of the `x1` slot even.  Over `gr3R` only, and it is `abelRow_even` five times. -/
theorem sepZero_abelRows_even (hw : sqWord s x y = 1) :
    (∃ ya, y.a = 2 * ya) ∧ (∃ yb, y.b = 2 * yb) ∧ (∃ yc, y.c = 2 * yc) ∧
      (∃ yd, y.d = 2 * yd) ∧ (∃ ye, y.e = 2 * ye) := by
  refine ⟨abelRow_even x.a y.a ?_, abelRow_even x.b y.b ?_, abelRow_even x.c y.c ?_,
    abelRow_even x.d y.d ?_, abelRow_even x.e y.e ?_⟩
  · have h := congrArg SqU6.a hw
    simp only [SqU6.sqWord_a, SqU6.one_a] at h
    linear_combination h
  · have h := congrArg SqU6.b hw
    simp only [SqU6.sqWord_b, SqU6.one_b] at h
    linear_combination h
  · have h := congrArg SqU6.c hw
    simp only [SqU6.sqWord_c, SqU6.one_c] at h
    linear_combination h
  · have h := congrArg SqU6.d hw
    simp only [SqU6.sqWord_d, SqU6.one_d] at h
    linear_combination h
  · have h := congrArg SqU6.e hw
    simp only [SqU6.sqWord_e, SqU6.one_e] at h
    linear_combination h

/-- ⭐⭐⭐ **THE CLASS-FIVE SEPARATION BIT IS EVEN AT `h = 0`, UNCONDITIONALLY.**  If the core
word over `gr3R` is trivial then its `a0 = a1` dressing has an even class-five coordinate.
There is **no** hypothesis on the sigma slot, on the `x0` slot or on the `x1` slot: the nine
rows the response reads are rows of the *undressed* word, and a trivial word sets all nine to
zero.

This is the statement `docs/dyadic/w63-live5-note.md` section 6 left open, and it is stronger
than the gauged form that section asked for. -/
theorem SqU6.selPar_sqWord_diagDress_o (hw : sqWord s x y = 1) :
    selPar (sqWord (s * x) x y).o = 0 := by
  obtain ⟨⟨ya, hya⟩, ⟨yb, hyb⟩, ⟨yc, hyc⟩, ⟨yd, hyd⟩, ⟨ye, hye⟩⟩ := sepZero_abelRows_even hw
  rw [selPar_eq_zero_iff]
  refine ⟨sepZeroWitO s x y ya yb yc yd ye, ?_⟩
  rw [SqU6.sqWord_diagDress_o hya hyb hyc hyd hye, hw]
  rw [SqU6.one_o, SqU6.one_f, SqU6.one_g, SqU6.one_h, SqU6.one_i, SqU6.one_j, SqU6.one_k,
    SqU6.one_l, SqU6.one_m, SqU6.one_n]
  ring

/-- ⭐⭐ **The whole dressed residue is even.**  At every relator-killing `h = 0` marking over
`gr3R` the six rows of class three, four and five of the `a0 = a1` dressing are even; with
`SqU6.sqWord_diagDress_low` the nine lower rows are outright `0`.  So the dressing is congruent
to the undressed marking modulo `2` in every coordinate, and in particular it can be neither a
class-five separation nor a class-four one. -/
theorem SqU6.selPar_sqWord_diagDress_high (hw : sqWord s x y = 1) :
    selPar (sqWord (s * x) x y).j = 0 ∧ selPar (sqWord (s * x) x y).k = 0 ∧
      selPar (sqWord (s * x) x y).l = 0 ∧ selPar (sqWord (s * x) x y).m = 0 ∧
      selPar (sqWord (s * x) x y).n = 0 ∧ selPar (sqWord (s * x) x y).o = 0 := by
  obtain ⟨⟨ya, hya⟩, ⟨yb, hyb⟩, ⟨yc, hyc⟩, ⟨yd, hyd⟩, ⟨ye, hye⟩⟩ := sepZero_abelRows_even hw
  refine ⟨?_, ?_, ?_, ?_, ?_, SqU6.selPar_sqWord_diagDress_o hw⟩
  · rw [selPar_eq_zero_iff]
    refine ⟨sepZeroWitJ s x y ya yb yc yd ye, ?_⟩
    rw [SqU6.sqWord_diagDress_j hya hyb hyc hyd hye, hw, SqU6.one_j, SqU6.one_f, SqU6.one_g]
    ring
  · rw [selPar_eq_zero_iff]
    refine ⟨sepZeroWitK s x y ya yb yc yd ye, ?_⟩
    rw [SqU6.sqWord_diagDress_k hya hyb hyc hyd hye, hw, SqU6.one_k, SqU6.one_g, SqU6.one_h]
    ring
  · rw [selPar_eq_zero_iff]
    refine ⟨sepZeroWitL s x y ya yb yc yd ye, ?_⟩
    rw [SqU6.sqWord_diagDress_l hya hyb hyc hyd hye, hw, SqU6.one_l, SqU6.one_h, SqU6.one_i]
    ring
  · rw [selPar_eq_zero_iff]
    refine ⟨sepZeroWitM s x y ya yb yc yd ye, ?_⟩
    rw [SqU6.sqWord_diagDress_m hya hyb hyc hyd hye, hw, SqU6.one_m, SqU6.one_f, SqU6.one_g,
      SqU6.one_h, SqU6.one_j, SqU6.one_k]
    ring
  · rw [selPar_eq_zero_iff]
    refine ⟨sepZeroWitN s x y ya yb yc yd ye, ?_⟩
    rw [SqU6.sqWord_diagDress_n hya hyb hyc hyd hye, hw, SqU6.one_n, SqU6.one_g, SqU6.one_h,
      SqU6.one_i, SqU6.one_k, SqU6.one_l]
    ring

/-- ⭐⭐ **The relator form.**  At handle count `0` the relator is the core word, so every
relator-killing marking has an even class-five separation bit **at the `a0 = a1` dressing**.
This is the negative answer to "is there an `h = 0` class-five separation at that dressing?",
with no gauge.  ⚠ Honest limit 4 of the header forbids the general reading: `sigFiveDress m v`
at a general `v` is not covered. -/
theorem sepZero_bit_even {m : Fin (sqRank 0) → SqU6 gr3R} (hrel : sqRelWord m = 1) :
    selPar (sqRelWord (sigFiveDress m (m 1))).o = 0 := by
  rw [sqRelWord_zero] at hrel ⊢
  rw [sigFiveDress_zero, sigFiveDress_one, sigFiveDress_two]
  exact SqU6.selPar_sqWord_diagDress_o hrel

end HandleFree

/-! ## 5 The forcing, at the tuple level and at the hom level -/

section Forcing

variable {h : ℕ}

/-- ⭐⭐⭐ **THE FORCING: A CLASS-FIVE SIGMA SEPARATION REQUIRES A HANDLE.**  At every handle
count, if a marking over `gr3R` kills the relator and the `a0 = a1` dressing of the relator has
an **odd** class-five coordinate, then `0 < h`.

This is the question `docs/dyadic/w63-live5-note.md` section 6 named, answered, and answered
without the gauge that question carried.  ⚠ It is not a block statement: no reading, no pairing
and no handle minor occurs in the proof.  ⚠ And it does not let any committed statement drop
`0 < h`, because every class-five statement of the stack is indexed by a handle already. -/
theorem sepZero_pos_of_bit_odd {m : Fin (sqRank h) → SqU6 gr3R} (hrel : sqRelWord m = 1)
    (hbit : selPar (sqRelWord (sigFiveDress m (m 1))).o = 1) : 0 < h := by
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · subst h0
    rw [sepZero_bit_even hrel] at hbit
    exact absurd hbit (by decide)
  · exact hpos

/-- ⭐⭐ **The hom form of the evenness**, through the class-five gate `sqU6Balance_gen`.  Every
continuous homomorphism from the handle-free `D_sq 0` into the class-five test group has an even
class-five separation bit. -/
theorem sepZero_bit_even_hom (Phi : ContinuousMonoidHom (DSq 0 : Type) (SqU6 gr3R)) :
    selPar (sqRelWord (sigFiveDress (fun i => Phi (sqGen 0 i)) (Phi (sqGen 0 1)))).o = 0 :=
  sepZero_bit_even (sqU6Balance_gen Phi)

/-- ⭐⭐ **The hom form of the forcing.**  A continuous homomorphism on `D_sq h` whose `a0 = a1`
dressing separates at class five needs `0 < h`. -/
theorem sepZero_pos_of_bit_odd_hom (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 gr3R))
    (hbit : selPar (sqRelWord (sigFiveDress (fun i => Phi (sqGen h i))
      (Phi (sqGen h 1)))).o = 1) : 0 < h :=
  sepZero_pos_of_bit_odd (sqU6Balance_gen Phi) hbit

end Forcing

/-! ## 6 Calibration -/

section Calibration

/-- **The committed `h = 0` completion, explained.**  `GradedFiveLive.blindCoreY` completes the
committed core pair `(fiveSigMark, stageX)` at `h = 0`, and the tree's datum
(`sqRelWord_blindCore_handleFree`) is that the UNDRESSED core word there is `1`.  ⚠ What is
stated here is a PARITY and nothing more: the class-five row of the `a0 = a1` dressing is EVEN.
It is not the claim that the dressing itself leaves residue `1`.  The theorem above predicts
that parity without computing anything at the point.  ⭐ This is the composite check of doctrine
iii against the tree's own `h = 0` datum, and it passes. -/
theorem sepZero_blindCore_bit :
    selPar (sqWord (fiveSigMark gr3R * stageX) stageX blindCoreY).o = 0 := by
  have hw : sqWord (fiveSigMark gr3R) stageX blindCoreY = 1 := by
    have h := sqRelWord_blindCore_handleFree
    rw [sqRelWord_zero] at h
    exact h
  exact SqU6.selPar_sqWord_diagDress_o hw

/-- ⚠ **`h = 0` is load-bearing.**  At every handle count and every handle, the `a0 = a1`
dressing of `GradedFiveForce.fiveWit` has class-five bit `1`.  ⚠ That is the whole statement: the
relator is NOT killed at this dressing value, where `GradedFiveForce.sqRelWord_fiveWit_diag`
gives `liftC6 7`; the kill is the separate `sqRelWord_fiveWit_triv`, at `v = 1`.  The row
expansion is not contradicted: at `h >= 1` the relator pins the core word to
the handle word's inverse rather than to `1`, and the nine rows the response reads are then free
to be odd.  ⭐ That is the sharpest reading of what the handle is for at class five. -/
theorem sepZero_fiveWit_bit_odd (h : ℕ) (j : Fin h) :
    selPar (sqRelWord (fiveWit h j forceX)).o = 1 := by
  rw [sqRelWord_fiveWit_diag, liftC6_o]
  decide

end Calibration

/-! ## 7 Axiom pins -/

section AxiomPins

#print axioms SqU6.sepShiftRow
#print axioms SqU6.sepShiftRow_a
#print axioms SqU6.sepShiftRow_b
#print axioms SqU6.sepShiftRow_c
#print axioms SqU6.sepShiftRow_d
#print axioms SqU6.sepShiftRow_e
#print axioms SqU6.sepShiftRow_f
#print axioms SqU6.sepShiftRow_g
#print axioms SqU6.sepShiftRow_h
#print axioms SqU6.sepShiftRow_i
#print axioms SqU6.sepShiftRow_j
#print axioms SqU6.sepShiftRow_k
#print axioms SqU6.sepShiftRow_l
#print axioms SqU6.sepShiftRow_m
#print axioms SqU6.sepShiftRow_n
#print axioms SqU6.sepShiftRow_o
#print axioms SqU6.sqWord_g_of_shift
#print axioms SqU6.sqWord_k_of_shift
#print axioms SqU6.sqWord_l_of_shift
#print axioms SqU6.sqWord_n_of_shift
#print axioms SqU6.sqWord_diagDress_low
#print axioms sepZeroWitJ
#print axioms sepZeroWitK
#print axioms sepZeroWitL
#print axioms sepZeroWitM
#print axioms sepZeroWitN
#print axioms sepZeroWitO
#print axioms sepZeroWitGauge
#print axioms SqU6.sqWord_diagDress_j
#print axioms SqU6.sqWord_diagDress_k
#print axioms SqU6.sqWord_diagDress_l
#print axioms SqU6.sqWord_diagDress_m
#print axioms SqU6.sqWord_diagDress_n
#print axioms SqU6.sqWord_diagDress_o
#print axioms SqU6.sqWord_diagDress_o_gauge
#print axioms sepZero_abelRows_even
#print axioms SqU6.selPar_sqWord_diagDress_o
#print axioms SqU6.selPar_sqWord_diagDress_high
#print axioms sepZero_bit_even
#print axioms sepZero_pos_of_bit_odd
#print axioms sepZero_bit_even_hom
#print axioms sepZero_pos_of_bit_odd_hom
#print axioms sepZero_blindCore_bit
#print axioms sepZero_fiveWit_bit_odd

end AxiomPins

end SqCore

end Dyadic

end GQ2
