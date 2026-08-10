/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveStageFour

/-!
# W61-WIDER: the `gamma_2`-level translation identity at class five, and its quadratic block

`GradedFiveStageFour` landed the STAGE-FOUR translation identity at class five and named the
next step, twice:

> **One filtration step wider again** - `gamma_2`-dressings, which disturb the class-three
> rows - is neither proved nor refuted here, and would need the `gamma_2`-level identity at
> class five.  That identity WILL carry a quadratic block: `[gamma_2, gamma_2] = gamma_4 <> 1`
> in the class-five carrier too.

Both halves of that prediction are settled here.  The identity is built, at every handle count
and over any commutative ring; the quadratic block is real and is computed in full; and - the
finding of the wave - **it is even on the achievable lattice**, so the transport is affine mod
two after all and the difficulty the campaign had been anticipating since wave 59 collapses.

## ⭐⭐⭐ Headline 1: the identity

`SqU6.sqRelWord_gaTwoDress`.  A five-slot `gamma_2`-dressing moves the relator by an explicit
`gamma_2`-element `SqU6.gaTwoShift`, at every handle count and over any commutative ring.  Its
four class-two rows move by the Frobenius weights `(-4, 2)` on the exponent slots alone; its
three class-three rows by Frobenius plus the class-three graded Fox pairings against the
permuted letters `(x0, 10 x0 - sigma - 8 x1, x1)`; and its two class-four rows and its
class-five row by Frobenius, the Fox pairings, a **correction** and a **quadratic block**.
Three structural facts, all of them new at this class:

* ⭐ **The two class-four rows are `GradedGammaTwo` verbatim.**  `SqU6.gaTwoCorrM` and
  `SqU6.gaTwoQuadM` are the class-four `gaTwoCorr` and `gaTwoQuad` transposed through the
  `toU5L`-quotient, all forty-four coefficients and all five, and `SqU6.gaTwoCorrN`,
  `SqU6.gaTwoQuadN` are the same through `toU5R`.  So wave 54's whole transport reappears here
  twice, and the only genuinely new row is the `(1,6)`-row.
* ⭐⭐ **The class-five quadratic block is NOT frame-free.**  `GradedGammaTwo` could argue by
  weight that a term quadratic in the dressings has no room for a frame coordinate: its top row
  has weight four and `2 + 2` fills it.  At class five the top row has weight five, so
  `2 + 2 + 1` fits, and `SqU6.gaTwoQuadO` has fifty-two terms in ten blocks - one frame-free,
  and nine carrying the `a`-, `c`- and `e`-columns of the three core slots.
* ⭐⭐ **The per-handle shifts no longer collect for free.**  At class four a `gamma_3`-shaped
  handle shift is central against the handle word; at class five `[gamma_3, gamma_2] <= gamma_5`
  is non-trivial (`SqU6.gaThree_past_gaTwo`), so each handle's shift pays a price passing the
  LATER handle commutators.  `SqU6.gaTwoHandleSum` carries it, and it is a `sqCross`, hence
  strictly triangular and **order-dependent** - the same shape as wave 59's class-five defect.

## ⭐⭐⭐ Headline 2: the quadratic block is EVEN on the achievable lattice

`SqU6.gaTwoQuadO_even`, and its consequence `SqU6.sqRelWord_gaTwoDress_o_channel`.  Take wave
60's hypotheses unchanged - every letter with an even `(1,2)`- and `(3,4)`-column
(`stageN1`), every dressing in the honest `gamma_2` of the image, which
`GradedFiveStageFour.stageN2_of_commutator` puts inside `f`, `h`, `j` all even (`stageN2`).
Then modulo two the class-five residue moves by

```text
   sum over slots of   z.m * L.e  +  z.i * L.j  +  z.l * L.f
```

(`SqU6.gaTwoShiftChan`) and by **nothing else**: the correction block, the collection element,
the cross-handle term and the whole quadratic block are all even.  This is the exact analogue
of wave 54's finding one class down, where `gaTwoQuad` was even because every generator of the
achievable lattice has an even `g`-column; here three of the four channels of `u6Comm5` are
closed the same way.

⚠ **One class-four row does NOT share this.**  `SqU6.gaTwoQuadN`, the RIGHT class-four
quadratic block, is generically odd on the same lattice
(`scripts/w61_wider/results/parity_blocks.txt`; 530 of 1200 random lattice points).  The
class-five row is affine mod two, the `(2,6)`-row is not.

## What is proved versus what is measured

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`): the whole of sections 1
to 6 - the `gamma_2`-calculus with its six pairing forms as honest commutator forms, the core
shift, the handle shift, the handle-word product law with its cross-handle term, the assembled
five-slot identity, the evenness of every block of the class-five row on the lattice, the
complete mod-two transport, and the achievability step `forceLcs_one_le_stageN2` connecting the
lattice to the honest lower central series of the image.  All at every handle count, every
handle, and over any commutative ring where the statement is ring-generic.

**MEASURED** (`scripts/w61_wider/`, certified output in `results/`; `validate.txt` has 11 named
checks and 0 failures):

* the identity derived with exact integer polynomial arithmetic and checked as an EXACT
  polynomial identity in all fifteen rows at handle counts `0`, `1`, `2`
  (`results/assemble.txt`), and the handle-word product law at handle counts `0` to `3`;
* every emitted form against honest `6 x 6` matrix collection over `Z`, `Z/4`, `Z/8` and `Z/16`:
  the six pairing forms at 1600 points, `SqU6.gaTwoHandle` at 1600, `SqU6.gaTwoCore` at 1200,
  and the five-slot `SqU6.gaTwoShift` at 1200 spread over handle counts `0` to `4`, with **zero
  mismatches**, plus 600 more on the `gamma_3` specialisation;
* the evenness by brute force at 3000 achievable dressings, 0 exceptions, and its sharpness:
  without the hypotheses 734 of 1500 unrestricted dressings move the row oddly, and the
  quadratic block is non-zero at 1030 of 1200 unrestricted points, so its vanishing mod two is
  a finding and not a triviality.

## Scope, honestly

* **This is not an exclusion.**  The three channels are live: `SqU6.stageWit_gaTwo_forced` says
  the residue is forced even *modulo* `SqU6.gaTwoShiftChan`, and at wave 60's point the
  functional itself is **odd on six of the ten commutator generators** of the achievable
  lattice (`scripts/w61_wider/results/census.txt`).  A `gamma_2`-level exclusion needs a point
  at which the three channels are even, and finding one is the next step, not this one.  ⚠ No
  counterexample was found either: none of those ten generators, at any power and on any single
  slot, kills the dressed frame, so wave 60's exclusion is not refuted one step wider - it is
  simply not decided.  That census is over the GENERATORS of `[H, H]`, not over all of it.
* Like `GradedFiveStageFour`, this file works at the level of **marking tuples** in
  `SqU6 gr3R`: the hom layer of `GradedFive` is not consumed, so no statement here claims that a
  given tuple is the image of a continuous homomorphism on `D_sq h`.
* The soundness hypotheses are **sufficient, not shown sharp**, exactly as at stage four.

## Contents

* **1** the `gamma_2`-calculus: `SqU6.IsGaTwo`, the six pairing forms and
  ⭐ `SqU6.commP_gaTwo_eq`, ⭐ `SqU6.gaTwo_commP` and the two collection lemmas;
* **2** ⭐⭐ `SqU6.sqWord_mul_gaTwo`, the core shift with its correction and quadratic blocks;
* **3** ⭐ `SqU6.commP_mul_gaTwo` and ⭐⭐ `SqU6.handleWord_mul_gaTwo_all` with its cross-handle
  term; **4** ⭐⭐⭐ `SqU6.sqRelWord_gaTwoDress`, the translation identity;
* **5** ⭐⭐⭐ `SqU6.gaTwoQuadO_even` and `SqU6.sqRelWord_gaTwoDress_o_channel`;
* **6** achievability and wave 60's point; **7** kernel cross-checks; **8** axiom pins.

## Axiom hygiene

All **80** committed prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a
subset; no census axiom is reachable.  Every `decide` is on `ZMod 8`, `SqU6 (ZMod 8)` or
`Fin`-indexed tuples over them; there is no `native_decide`.

Companion memo: `docs/dyadic/w61-wider-note.md`.
-/

open Multiplicative

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The `gamma_2`-calculus on the class-five carrier -/

section GaTwoCalculus

variable {R : Type} [CommRing R]

/-- **A `gamma_2`-shaped element of the class-five carrier**: the five abelian coordinates
vanish, so ten coordinates survive.  `SqU6.IsGaThree` (`GradedFiveStageFour`) and
`SqU6.IsGaFour` (`GradedFiveDefect`) are imported, not redefined. -/
def SqU6.IsGaTwo (z : SqU6 R) : Prop :=
  z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0

theorem SqU6.IsGaThree.isGaTwo {z : SqU6 R} (hz : z.IsGaThree) : z.IsGaTwo :=
  ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1⟩

@[simp] theorem SqU6.isGaTwo_one : (1 : SqU6 R).IsGaTwo := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A commutator is always `gamma_2`-shaped. -/
theorem SqU6.commP_isGaTwo (p q : SqU6 R) : (commP p q).IsGaTwo :=
  ⟨SqU6.commP_a p q, SqU6.commP_b p q, SqU6.commP_c p q, SqU6.commP_d p q, SqU6.commP_e p q⟩

/-- The handle word is `gamma_2`-shaped. -/
theorem SqU6.handleWord_isGaTwo {h : ℕ} (u v : Fin h → SqU6 R) : (handleWord u v).IsGaTwo :=
  ⟨SqU6.handleWord_a u v, SqU6.handleWord_b u v, SqU6.handleWord_c u v,
    SqU6.handleWord_d u v, SqU6.handleWord_e u v⟩

/-- **The first class-three pairing form** of a `gamma_2` dressing against a letter. -/
def SqU6.gaTwoPairJ (z L : SqU6 R) : R := z.f * L.c - z.g * L.a

/-- …the second. -/
def SqU6.gaTwoPairK (z L : SqU6 R) : R := z.g * L.d - z.h * L.b

/-- …the third. -/
def SqU6.gaTwoPairL (z L : SqU6 R) : R := z.h * L.e - z.i * L.c

/-- **The left class-four pairing form**: `GradedGammaTwo.gaTwoPair` one class up, through the
`toU5L`-quotient. -/
def SqU6.gaTwoPairM (z L : SqU6 R) : R :=
  z.j * L.d - z.k * L.a + z.f * L.h - z.h * L.f + z.h * (L.a * L.b) - z.g * (L.a * L.d)

/-- …and the right one, through `toU5R`. -/
def SqU6.gaTwoPairN (z L : SqU6 R) : R :=
  z.k * L.e - z.l * L.b + z.g * L.i - z.i * L.g + z.i * (L.b * L.c) - z.h * (L.b * L.e)

/-- ⭐ **The class-five pairing form**: sixteen terms, and unlike every lower one it is
**quadratic in the dressing** (`z.f * z.i * L.c` and `z.f * z.h * L.e`), because `gamma_2` is
not abelian in the class-five carrier.  Its first three terms `z.m * L.e`, `z.j * L.i -
z.i * L.j` and `z.f * L.l - z.l * L.f` are the four complementary pairings of `u6Comm5`. -/
def SqU6.gaTwoPairO (z L : SqU6 R) : R :=
  z.m * L.e - z.n * L.a + z.j * L.i - z.i * L.j + z.f * L.l - z.l * L.f
    + z.l * (L.a * L.b) - z.k * (L.a * L.e) + z.i * (L.a * L.g) - z.g * (L.a * L.i)
    + z.i * (L.c * L.f) - z.h * (L.e * L.f) + z.f * z.i * L.c - z.f * z.h * L.e
    - z.i * (L.a * L.b * L.c) + z.h * (L.a * L.b * L.e)

/-- ⭐ **The six pairing forms are the honest commutator forms on `gamma_2`**: dressing a
letter by a `gamma_2`-element moves it by the `gamma_3`-element whose six coordinates are the
six pairings.  Nothing below is a convention: the forms are computed, not chosen. -/
theorem SqU6.commP_gaTwo_eq {z : SqU6 R} (hz : z.IsGaTwo) (L : SqU6 R) :
    commP z L = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, SqU6.gaTwoPairJ z L, SqU6.gaTwoPairK z L,
      SqU6.gaTwoPairL z L, SqU6.gaTwoPairM z L, SqU6.gaTwoPairN z L, SqU6.gaTwoPairO z L⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hz
  ext <;>
    simp only [commP, SqU6.gaTwoPairJ, SqU6.gaTwoPairK, SqU6.gaTwoPairL, SqU6.gaTwoPairM,
      SqU6.gaTwoPairN, SqU6.gaTwoPairO,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
      SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
      SqU6.inv_n, SqU6.inv_o, h1, h2, h3, h4, h5] <;>
    ring

/-- ⭐ **Two `gamma_2`-elements do NOT commute at class five**: their commutator is the
`gamma_4`-element with the three pairings `f`-against-`h`, `g`-against-`i` and
(`f`-against-`l` plus `j`-against-`i`).  This is the fact that makes the transport below carry
a quadratic block, and the exact analogue of `GradedGammaTwo.gaTwo_swap`; one filtration step
narrower, `SqU6.gaThree_comm` says the corresponding commutator is trivial, which is why wave
60's stage-four identity was affine. -/
theorem SqU6.gaTwo_commP {p q : SqU6 R} (hp : p.IsGaTwo) (hq : q.IsGaTwo) :
    commP p q = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, p.f * q.h - p.h * q.f,
      p.g * q.i - p.i * q.g, p.f * q.l - p.l * q.f + p.j * q.i - p.i * q.j⟩ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  ext <;>
    simp only [commP, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f,
      SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m,
      SqU6.mul_n, SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e,
      SqU6.inv_f, SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l,
      SqU6.inv_m, SqU6.inv_n, SqU6.inv_o, p1, p2, p3, p4, p5, q1, q2, q3, q4, q5] <;>
    ring

/-- **A `gamma_2`-element moves past a `gamma_2`-word with vanishing abelian columns** at the
cost of one `gamma_4`-shaped factor.  `GradedGammaTwo.gaTwo_swap` one class up, where the price
is no longer central. -/
theorem SqU6.gaTwo_past {c b : SqU6 R} (hc : c.IsGaTwo) (hb : b.IsGaTwo) :
    c * b = b * c * ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.f * b.h - c.h * b.f,
      c.g * b.i - c.i * b.g, c.f * b.l - c.l * b.f + c.j * b.i - c.i * b.j⟩ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  ext <;>
    simp only [SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f,
      SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m,
      SqU6.mul_n, SqU6.mul_o, c1, c2, c3, c4, c5, b1, b2, b3, b4, b5] <;>
    ring

/-- ⭐ **A `gamma_3`-element moves past a `gamma_2`-word with vanishing abelian columns** at the
cost of one CENTRAL factor pairing its outer class-three rows against the word's outer
class-two rows.  At class four this price is zero (`GradedGammaTwo.mul_gaThree_swap`), and that
is why the class-four handle shifts collect with no cross-handle term. -/
theorem SqU6.gaThree_past_gaTwo {c b : SqU6 R} (hc : c.IsGaThree) (hb : b.IsGaTwo) :
    c * b = b * c * SqU6.liftO (c.j * b.i - b.f * c.l) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  ext <;>
    simp only [SqU6.liftO, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e,
      SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l,
      SqU6.mul_m, SqU6.mul_n, SqU6.mul_o, c1, c2, c3, c4, c5, c6, c7, c8, c9,
      b1, b2, b3, b4, b5] <;>
    ring

end GaTwoCalculus

/-! ## 2 The core word under a three-slot `gamma_2`-dressing -/

section CoreShift

variable {R : Type} [CommRing R]

/-- **The left class-four correction block**: `GradedGammaTwo.gaTwoCorr` transposed through the
`toU5L`-quotient, all nine blocks and all forty-four coefficients verbatim. -/
def SqU6.gaTwoCorrM (s x y z₀ z₁ z₂ : SqU6 R) : R :=
  z₀.f * (-s.c * x.d + s.d * x.c - 4 * x.c * x.d + 2 * x.c * y.d + y.c * y.d)
    + z₀.g * (8 * x.a * x.d - 2 * x.a * y.d - 2 * x.d * y.a - 2 * y.a * y.d)
    + z₀.h * (s.a * x.b - s.b * x.a - 4 * x.a * x.b + 2 * x.b * y.a + y.a * y.b)
    + z₁.f * (3 * s.c * x.d - 2 * s.c * y.d + s.d * x.c - 20 * x.c * x.d + 20 * x.c * y.d
        - 4 * y.c * y.d)
    + z₁.g * (2 * s.a * s.d - 14 * s.a * x.d + 10 * s.a * y.d - 14 * s.d * x.a + 10 * s.d * y.a
        + 130 * x.a * x.d - 100 * x.a * y.d - 100 * x.d * y.a + 80 * y.a * y.d)
    + z₁.h * (-2 * s.a * s.b + 11 * s.a * x.b - 8 * s.a * y.b + 13 * s.b * x.a - 10 * s.b * y.a
        - 110 * x.a * x.b + 80 * x.a * y.b + 100 * x.b * y.a - 76 * y.a * y.b)
    + z₂.f * (-2 * s.c * y.d + s.d * y.c)
    + z₂.g * (s.a * y.d + s.d * y.a)
    + z₂.h * (s.a * y.b - 2 * s.b * y.a)

/-- **The right class-four correction block**: the same through `toU5R`. -/
def SqU6.gaTwoCorrN (s x y z₀ z₁ z₂ : SqU6 R) : R :=
  z₀.g * (-s.d * x.e + s.e * x.d - 4 * x.d * x.e + 2 * x.d * y.e + y.d * y.e)
    + z₀.h * (8 * x.b * x.e - 2 * x.b * y.e - 2 * x.e * y.b - 2 * y.b * y.e)
    + z₀.i * (s.b * x.c - s.c * x.b - 4 * x.b * x.c + 2 * x.c * y.b + y.b * y.c)
    + z₁.g * (3 * s.d * x.e - 2 * s.d * y.e + s.e * x.d - 20 * x.d * x.e + 20 * x.d * y.e
        - 4 * y.d * y.e)
    + z₁.h * (2 * s.b * s.e - 14 * s.b * x.e + 10 * s.b * y.e - 14 * s.e * x.b + 10 * s.e * y.b
        + 130 * x.b * x.e - 100 * x.b * y.e - 100 * x.e * y.b + 80 * y.b * y.e)
    + z₁.i * (-2 * s.b * s.c + 11 * s.b * x.c - 8 * s.b * y.c + 13 * s.c * x.b - 10 * s.c * y.b
        - 110 * x.b * x.c + 80 * x.b * y.c + 100 * x.c * y.b - 76 * y.b * y.c)
    + z₂.g * (-2 * s.d * y.e + s.e * y.d)
    + z₂.h * (s.b * y.e + s.e * y.b)
    + z₂.i * (s.b * y.c - 2 * s.c * y.b)

/-- ⭐⭐ **The class-five correction block**: the part of the class-five defect reading ONE
dressing coordinate against the frame's own columns, beyond the graded Fox pairings.  Twenty-one
blocks and two hundred and seventy-six coefficients, derived with exact integer arithmetic and
validated against honest collection before transcription (`scripts/w61_wider/`).  ⭐ Every
monomial of the seven blocks NOT already carrying an even dressing coordinate contains a frame
`(1,2)`- or `(3,4)`-column, which is what makes the whole block even on the achievable
lattice. -/
def SqU6.gaTwoCorrO (s x y z₀ z₁ z₂ : SqU6 R) : R :=
  z₀.f * (-s.c * x.i + s.e * x.h - s.h * x.e + s.i * x.c - 4 * x.c * x.i + 2 * x.c * y.i
        - 4 * x.e * x.h + 2 * x.h * y.e + y.c * y.i + y.e * y.h + s.c * s.d * x.e
        - s.c * s.e * x.d + 4 * s.c * x.d * x.e - 2 * s.c * x.d * y.e - s.c * y.d * y.e
        - 3 * s.d * x.c * x.e + 2 * s.d * x.c * y.e + s.d * y.c * y.e - s.e * x.c * x.d
        + 10 * x.c * x.d * x.e - 8 * x.c * x.d * y.e + x.c * y.d * y.e)
    + z₀.g * (8 * x.a * x.i - 2 * x.a * y.i - 2 * x.i * y.a - 2 * y.a * y.i - 4 * s.d * x.a * x.e
        + 2 * s.d * x.e * y.a + s.d * y.a * y.e + 4 * s.e * x.a * x.d - 2 * s.e * x.d * y.a
        - s.e * y.a * y.d - 22 * x.a * x.d * x.e + 14 * x.a * x.d * y.e - x.a * y.d * y.e
        + 8 * x.d * x.e * y.a - 4 * x.d * y.a * y.e - 2 * y.a * y.d * y.e)
    + z₀.h * (8 * x.e * x.f - 2 * x.e * y.f - 2 * x.f * y.e - 2 * y.e * y.f - 4 * s.a * x.b * x.e
        + 2 * s.a * x.b * y.e + s.a * y.b * y.e + 4 * s.b * x.a * x.e - 2 * s.b * x.a * y.e
        - s.b * y.a * y.e + 14 * x.a * x.b * x.e - 6 * x.a * x.b * y.e
        - 14 * x.b * x.e * y.a + 4 * x.b * y.a * y.e + 3 * x.e * y.a * y.b
        + 4 * y.a * y.b * y.e)
    + z₀.i * (s.a * x.g - s.c * x.f + s.f * x.c - s.g * x.a - 4 * x.a * x.g - 4 * x.c * x.f
        + 2 * x.c * y.f + 2 * x.g * y.a + y.a * y.g + y.c * y.f - s.a * s.b * x.c
        + s.a * s.c * x.b + 3 * s.b * x.a * x.c - 2 * s.b * x.c * y.a - s.b * y.a * y.c
        - 3 * s.c * x.a * x.b + 2 * s.c * x.b * y.a + s.c * y.a * y.b - 2 * x.a * x.b * x.c
        + 6 * x.b * x.c * y.a - 3 * x.c * y.a * y.b - 2 * y.a * y.b * y.c)
    + z₀.j * (-s.d * x.e + s.e * x.d - 4 * x.d * x.e + 2 * x.d * y.e + y.d * y.e)
    + z₀.k * (8 * x.a * x.e - 2 * x.a * y.e - 2 * x.e * y.a - 2 * y.a * y.e)
    + z₀.l * (s.a * x.b - s.b * x.a - 4 * x.a * x.b + 2 * x.b * y.a + y.a * y.b)
    + z₁.f * (3 * s.c * x.i - 2 * s.c * y.i + s.e * x.h + 3 * s.h * x.e - 2 * s.h * y.e
        + s.i * x.c - 20 * x.c * x.i + 20 * x.c * y.i - 20 * x.e * x.h + 20 * x.h * y.e
        - 4 * y.c * y.i - 4 * y.e * y.h - 6 * s.c * x.d * x.e + 6 * s.c * x.d * y.e
        - 5 * s.c * y.d * y.e - 3 * s.d * x.c * x.e + 2 * s.d * x.c * y.e
        + 8 * s.d * y.c * y.e - s.e * x.c * x.d - 4 * s.e * y.c * y.d + 35 * x.c * x.d * x.e
        - 40 * x.c * x.d * y.e + 10 * x.c * y.d * y.e)
    + z₁.g * (2 * s.a * s.i - 14 * s.a * x.i + 10 * s.a * y.i - 14 * s.i * x.a + 10 * s.i * y.a
        + 130 * x.a * x.i - 100 * x.a * y.i - 100 * x.i * y.a + 80 * y.a * y.i
        - 3 * s.a * s.d * x.e + 2 * s.a * s.d * y.e - s.a * s.e * x.d + 10 * s.a * x.d * x.e
        - 8 * s.a * x.d * y.e + s.a * y.d * y.e + 12 * s.d * x.a * x.e - 8 * s.d * x.a * y.e
        - 6 * s.d * x.e * y.a + 4 * s.d * y.a * y.e + 4 * s.e * x.a * x.d
        - 2 * s.e * x.d * y.a - 65 * x.a * x.d * x.e + 60 * x.a * x.d * y.e
        - 10 * x.a * y.d * y.e + 40 * x.d * x.e * y.a - 40 * x.d * y.a * y.e
        + 8 * y.a * y.d * y.e)
    + z₁.h * (2 * s.e * s.f - 14 * s.e * x.f + 10 * s.e * y.f - 14 * s.f * x.e + 10 * s.f * y.e
        + 130 * x.e * x.f - 100 * x.e * y.f - 100 * x.f * y.e + 80 * y.e * y.f
        - 6 * s.a * s.b * x.e + 6 * s.a * s.b * y.e - 9 * s.a * s.e * x.b
        + 8 * s.a * s.e * y.b + 96 * s.a * x.b * x.e - 78 * s.a * x.b * y.e
        - 80 * s.a * x.e * y.b + 64 * s.a * y.b * y.e - 7 * s.b * s.e * x.a
        + 6 * s.b * s.e * y.a + 88 * s.b * x.a * x.e - 74 * s.b * x.a * y.e
        - 72 * s.b * x.e * y.a + 60 * s.b * y.a * y.e + 94 * s.e * x.a * x.b
        - 80 * s.e * x.a * y.b - 72 * s.e * x.b * y.a + 61 * s.e * y.a * y.b
        - 965 * x.a * x.b * x.e + 780 * x.a * x.b * y.e + 800 * x.a * x.e * y.b
        - 640 * x.a * y.b * y.e + 740 * x.b * x.e * y.a - 600 * x.b * y.a * y.e
        - 610 * x.e * y.a * y.b + 488 * y.a * y.b * y.e)
    + z₁.i * (-2 * s.a * s.g + 11 * s.a * x.g - 8 * s.a * y.g - 2 * s.c * s.f + 13 * s.c * x.f
        - 10 * s.c * y.f + 11 * s.f * x.c - 8 * s.f * y.c + 13 * s.g * x.a - 10 * s.g * y.a
        - 110 * x.a * x.g + 80 * x.a * y.g - 110 * x.c * x.f + 100 * x.c * y.f
        + 80 * x.f * y.c + 100 * x.g * y.a - 76 * y.a * y.g - 76 * y.c * y.f
        + 9 * s.a * s.b * x.c - 8 * s.a * s.b * y.c + 10 * s.a * s.c * x.b
        - 8 * s.a * s.c * y.b - 100 * s.a * x.b * x.c + 80 * s.a * x.b * y.c
        + 80 * s.a * x.c * y.b - 60 * s.a * y.b * y.c + 7 * s.b * s.c * x.a
        - 6 * s.b * s.c * y.a - 97 * s.b * x.a * x.c + 80 * s.b * x.a * y.c
        + 78 * s.b * x.c * y.a - 72 * s.b * y.a * y.c - 97 * s.c * x.a * x.b
        + 80 * s.c * x.a * y.b + 74 * s.c * x.b * y.a - 57 * s.c * y.a * y.b
        + 995 * x.a * x.b * x.c - 800 * x.a * x.b * y.c - 800 * x.a * x.c * y.b
        + 640 * x.a * y.b * y.c - 780 * x.b * x.c * y.a + 640 * x.b * y.a * y.c
        + 610 * x.c * y.a * y.b - 496 * y.a * y.b * y.c)
    + z₁.j * (3 * s.d * x.e - 2 * s.d * y.e + s.e * x.d - 20 * x.d * x.e + 20 * x.d * y.e
        - 4 * y.d * y.e)
    + z₁.k * (2 * s.a * s.e - 14 * s.a * x.e + 10 * s.a * y.e - 14 * s.e * x.a + 10 * s.e * y.a
        + 130 * x.a * x.e - 100 * x.a * y.e - 100 * x.e * y.a + 80 * y.a * y.e)
    + z₁.l * (-2 * s.a * s.b + 11 * s.a * x.b - 8 * s.a * y.b + 13 * s.b * x.a - 10 * s.b * y.a
        - 110 * x.a * x.b + 80 * x.a * y.b + 100 * x.b * y.a - 76 * y.a * y.b)
    + z₂.f * (-2 * s.c * y.i + s.e * y.h - 2 * s.h * y.e + s.i * y.c + s.c * s.d * y.e
        - s.c * s.e * y.d)
    + z₂.g * (s.a * y.i + s.i * y.a + s.a * s.d * y.e + 2 * s.d * y.a * y.e - s.e * y.a * y.d)
    + z₂.h * (s.e * y.f + s.f * y.e - s.a * s.b * y.e + s.a * y.b * y.e - s.b * s.e * y.a
        - 2 * s.b * y.a * y.e - s.e * y.a * y.b)
    + z₂.i * (s.a * y.g - 2 * s.c * y.f + s.f * y.c - 2 * s.g * y.a - s.a * s.b * y.c
        + s.a * s.c * y.b - s.a * y.b * y.c + s.b * s.c * y.a + 2 * s.c * y.a * y.b)
    + z₂.j * (-2 * s.d * y.e + s.e * y.d)
    + z₂.k * (s.a * y.e + s.e * y.a)
    + z₂.l * (s.a * y.b - 2 * s.b * y.a)

/-- **The left class-four quadratic block**: `GradedGammaTwo.gaTwoQuad` verbatim through
`toU5L`, coefficients `(1, 10, -8, 1)` the binomials `C(-4, 2)`, `C(2, 2)` of the relator's
exponent vector and the `gamma_2` commutator pairing. -/
def SqU6.gaTwoQuadM (z₀ z₁ z₂ : SqU6 R) : R :=
  z₀.f * z₁.h - z₀.h * z₁.f + 10 * z₁.f * z₁.h - 8 * z₁.f * z₂.h + z₂.f * z₂.h

/-- …and the right one, through `toU5R`. -/
def SqU6.gaTwoQuadN (z₀ z₁ z₂ : SqU6 R) : R :=
  z₀.g * z₁.i - z₀.i * z₁.g + 10 * z₁.g * z₁.i - 8 * z₁.g * z₂.i + z₂.g * z₂.i

/-- ⭐⭐⭐ **THE CLASS-FIVE QUADRATIC BLOCK**, the object this wave exists to compute.  Unlike
its class-four model `GradedGammaTwo.gaTwoQuad` it is **not frame-free**: at class four a term
quadratic in the dressings had no room for a frame coordinate by weight, and at class five the
top row has weight five, so `2 + 2 + 1` fits.  Ten blocks: the frame-free one carries the two
channels `(f, l)` and `(j, i)` with the exponent binomials, and nine more carry the frame's
odd-indexed abelian columns `a`, `c`, `e` of each core slot. -/
def SqU6.gaTwoQuadO (s x y z₀ z₁ z₂ : SqU6 R) : R :=
  (z₀.f * z₁.l - z₀.i * z₁.j + z₀.j * z₁.i - z₀.l * z₁.f + 10 * z₁.f * z₁.l
        - 8 * z₁.f * z₂.l + 10 * z₁.i * z₁.j - 8 * z₁.j * z₂.i + z₂.f * z₂.l + z₂.i * z₂.j)
    + s.a * (z₀.i * z₁.g - 4 * z₁.g * z₁.i + 2 * z₁.g * z₂.i + z₂.g * z₂.i)
    + s.c * (-z₀.f * z₁.i - z₀.i * z₁.f + 4 * z₁.f * z₁.i - 2 * z₁.f * z₂.i - 2 * z₂.f * z₂.i)
    + s.e * (z₀.f * z₁.h + z₂.f * z₂.h)
    + x.a * (7 * z₀.g * z₁.i - 2 * z₀.g * z₂.i - 4 * z₀.i * z₁.g + 30 * z₁.g * z₁.i
        - 20 * z₁.g * z₂.i)
    + x.c * (-3 * z₀.f * z₁.i + 2 * z₀.f * z₂.i + z₀.i * z₁.f - 20 * z₁.f * z₁.i
        + 20 * z₁.f * z₂.i)
    + x.e * (-4 * z₀.f * z₁.h + 3 * z₀.h * z₁.f - 10 * z₁.f * z₁.h)
    + y.a * (-2 * z₀.g * z₁.i - 2 * z₀.g * z₂.i + 2 * z₀.i * z₁.g + z₀.i * z₂.g
        - 20 * z₁.g * z₁.i + 16 * z₁.g * z₂.i - z₂.g * z₂.i)
    + y.c * (z₀.f * z₂.i + z₀.i * z₂.f + 8 * z₁.f * z₁.i - 12 * z₁.f * z₂.i)
    + y.e * (2 * z₀.f * z₁.h + z₀.f * z₂.h - 2 * z₀.h * z₁.f - 2 * z₀.h * z₂.f + 12 * z₁.f * z₁.h
        - 4 * z₁.f * z₂.h + z₂.f * z₂.h)

/-- ⭐⭐ **The core shift**: the `gamma_2`-element by which the core word moves under a
three-slot `gamma_2`-dressing.  Class-two rows: the Frobenius weights `(-4, 2)` on the exponent
slots alone.  Class-three rows: Frobenius plus the class-three Fox pairings against the
permuted letters `(x0, 10 x0 - sigma - 8 x1, x1)`.  Class-four and class-five rows: Frobenius,
the Fox pairings, a correction and a **quadratic block**. -/
def SqU6.gaTwoCore (s x y z₀ z₁ z₂ : SqU6 R) : SqU6 R :=
  ⟨0, 0, 0, 0, 0,
    -4 * z₁.f + 2 * z₂.f, -4 * z₁.g + 2 * z₂.g, -4 * z₁.h + 2 * z₂.h, -4 * z₁.i + 2 * z₂.i,
    -4 * z₁.j + 2 * z₂.j + (SqU6.gaTwoPairJ z₀ x + SqU6.gaTwoPairJ z₁ (sqFoxX6 s x y)
      + SqU6.gaTwoPairJ z₂ y),
    -4 * z₁.k + 2 * z₂.k + (SqU6.gaTwoPairK z₀ x + SqU6.gaTwoPairK z₁ (sqFoxX6 s x y)
      + SqU6.gaTwoPairK z₂ y),
    -4 * z₁.l + 2 * z₂.l + (SqU6.gaTwoPairL z₀ x + SqU6.gaTwoPairL z₁ (sqFoxX6 s x y)
      + SqU6.gaTwoPairL z₂ y),
    -4 * z₁.m + 2 * z₂.m + (SqU6.gaTwoPairM z₀ x + SqU6.gaTwoPairM z₁ (sqFoxX6 s x y)
        + SqU6.gaTwoPairM z₂ y)
      + SqU6.gaTwoCorrM s x y z₀ z₁ z₂ + SqU6.gaTwoQuadM z₀ z₁ z₂,
    -4 * z₁.n + 2 * z₂.n + (SqU6.gaTwoPairN z₀ x + SqU6.gaTwoPairN z₁ (sqFoxX6 s x y)
        + SqU6.gaTwoPairN z₂ y)
      + SqU6.gaTwoCorrN s x y z₀ z₁ z₂ + SqU6.gaTwoQuadN z₀ z₁ z₂,
    -4 * z₁.o + 2 * z₂.o + (SqU6.gaTwoPairO z₀ x + SqU6.gaTwoPairO z₁ (sqFoxX6 s x y)
        + SqU6.gaTwoPairO z₂ y)
      + SqU6.gaTwoCorrO s x y z₀ z₁ z₂ + SqU6.gaTwoQuadO s x y z₀ z₁ z₂⟩

theorem SqU6.gaTwoCore_isGaTwo (s x y z₀ z₁ z₂ : SqU6 R) :
    (SqU6.gaTwoCore s x y z₀ z₁ z₂).IsGaTwo := ⟨rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem SqU6.gaTwoCore_a (s x y z₀ z₁ z₂ : SqU6 R) :
    (SqU6.gaTwoCore s x y z₀ z₁ z₂).a = 0 := rfl

@[simp] theorem SqU6.gaTwoCore_f (s x y z₀ z₁ z₂ : SqU6 R) :
    (SqU6.gaTwoCore s x y z₀ z₁ z₂).f = -4 * z₁.f + 2 * z₂.f := rfl

@[simp] theorem SqU6.gaTwoCore_g (s x y z₀ z₁ z₂ : SqU6 R) :
    (SqU6.gaTwoCore s x y z₀ z₁ z₂).g = -4 * z₁.g + 2 * z₂.g := rfl

@[simp] theorem SqU6.gaTwoCore_h (s x y z₀ z₁ z₂ : SqU6 R) :
    (SqU6.gaTwoCore s x y z₀ z₁ z₂).h = -4 * z₁.h + 2 * z₂.h := rfl

@[simp] theorem SqU6.gaTwoCore_i (s x y z₀ z₁ z₂ : SqU6 R) :
    (SqU6.gaTwoCore s x y z₀ z₁ z₂).i = -4 * z₁.i + 2 * z₂.i := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- ⭐⭐ **The core word under `gamma_2`-dressings of its three slots.**  No closed form of the
word is consumed: componentwise expansion, as in `GradedGammaTwo.sqWord_mul_gaTwo` one class
down and `GradedFiveStageFour.SqU6.sqWord_mul_gaThree` one filtration step narrower. -/
theorem SqU6.sqWord_mul_gaTwo {z₀ z₁ z₂ : SqU6 R} (s x y : SqU6 R) (h₀ : z₀.IsGaTwo)
    (h₁ : z₁.IsGaTwo) (h₂ : z₂.IsGaTwo) :
    sqWord (s * z₀) (x * z₁) (y * z₂) = sqWord s x y * SqU6.gaTwoCore s x y z₀ z₁ z₂ := by
  obtain ⟨a0, b0, c0, d0, e0⟩ := h₀
  obtain ⟨a1, b1, c1, d1, e1⟩ := h₁
  obtain ⟨a2, b2, c2, d2, e2⟩ := h₂
  ext <;>
    simp only [SqU6.gaTwoCore, SqU6.gaTwoPairJ, SqU6.gaTwoPairK, SqU6.gaTwoPairL,
      SqU6.gaTwoPairM, SqU6.gaTwoPairN, SqU6.gaTwoPairO, SqU6.gaTwoCorrM, SqU6.gaTwoCorrN,
      SqU6.gaTwoCorrO, SqU6.gaTwoQuadM, SqU6.gaTwoQuadN, SqU6.gaTwoQuadO, sqFoxX6,
      sqWord, conjP, commP, pow_succ, pow_zero, one_mul,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
      SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
      SqU6.inv_n, SqU6.inv_o,
      a0, b0, c0, d0, e0, a1, b1, c1, d1, e1, a2, b2, c2, d2, e2] <;>
    ring

end CoreShift

/-! ## 3 The handle block under an all-pair `gamma_2`-dressing -/

section HandleShift

variable {R : Type} [CommRing R]

/-- **The collection artefact of the handle shift's class-five row**: sixteen terms, the price
of moving each dressing to the end of its own commutator past the suffix of that commutator.
Every one of its four blocks carries either an even dressing coordinate or a frame
`(1,2)`- or `(3,4)`-column, which is why it dies on the achievable lattice. -/
def SqU6.gaTwoHandleX (p q z w : SqU6 R) : R :=
  w.f * ((q.c - p.c) * z.i - q.e * z.h - p.c * (p.d * q.e - p.e * q.d))
    + w.g * (p.a * (z.i + (p.d * q.e - p.e * q.d)))
    + w.h * (p.e * (z.f + (p.a * q.b - p.b * q.a)))
    + w.i * ((q.c - p.c) * z.f - q.a * z.g - p.c * (p.a * q.b - p.b * q.a))

/-- ⭐ **The handle shift**: the `gamma_3`-element by which one handle commutator moves under a
`gamma_2`-dressing of both its slots.  Class-three rows: the crosswise Fox pairings.  Class-four
and class-five rows: the crosswise pairings, the commutator of the two dressings (the quadratic
part), the commutator's own lower rows against the dressings, and the artefact.  This is
`GradedGammaTwo.gaTwoHandle` one class up, with two extra pairing channels in the top row. -/
def SqU6.gaTwoHandle (p q z w : SqU6 R) : SqU6 R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0,
    SqU6.gaTwoPairJ z q - SqU6.gaTwoPairJ w p,
    SqU6.gaTwoPairK z q - SqU6.gaTwoPairK w p,
    SqU6.gaTwoPairL z q - SqU6.gaTwoPairL w p,
    SqU6.gaTwoPairM z q - SqU6.gaTwoPairM w p + (z.f * w.h - z.h * w.f)
      + (p.a * q.b - p.b * q.a) * (z.h + w.h) - (p.c * q.d - p.d * q.c) * (z.f + w.f),
    SqU6.gaTwoPairN z q - SqU6.gaTwoPairN w p + (z.g * w.i - z.i * w.g)
      + (p.b * q.c - p.c * q.b) * (z.i + w.i) - (p.d * q.e - p.e * q.d) * (z.g + w.g),
    SqU6.gaTwoPairO z q - SqU6.gaTwoPairO w p + (z.f * w.l - z.l * w.f)
      + (z.j * w.i - z.i * w.j)
      + (p.a * q.b - p.b * q.a) * (z.l + w.l) - SqU6.u6Comm3R p q * (z.f + w.f)
      + SqU6.u6Comm3L p q * (z.i + w.i) - (p.d * q.e - p.e * q.d) * (z.j + w.j)
      + SqU6.gaTwoHandleX p q z w⟩

theorem SqU6.gaTwoHandle_isGaThree (p q z w : SqU6 R) :
    (SqU6.gaTwoHandle p q z w).IsGaThree :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem SqU6.gaTwoHandle_a (p q z w : SqU6 R) : (SqU6.gaTwoHandle p q z w).a = 0 := rfl
@[simp] theorem SqU6.gaTwoHandle_b (p q z w : SqU6 R) : (SqU6.gaTwoHandle p q z w).b = 0 := rfl
@[simp] theorem SqU6.gaTwoHandle_c (p q z w : SqU6 R) : (SqU6.gaTwoHandle p q z w).c = 0 := rfl
@[simp] theorem SqU6.gaTwoHandle_d (p q z w : SqU6 R) : (SqU6.gaTwoHandle p q z w).d = 0 := rfl
@[simp] theorem SqU6.gaTwoHandle_e (p q z w : SqU6 R) : (SqU6.gaTwoHandle p q z w).e = 0 := rfl
@[simp] theorem SqU6.gaTwoHandle_f (p q z w : SqU6 R) : (SqU6.gaTwoHandle p q z w).f = 0 := rfl
@[simp] theorem SqU6.gaTwoHandle_g (p q z w : SqU6 R) : (SqU6.gaTwoHandle p q z w).g = 0 := rfl
@[simp] theorem SqU6.gaTwoHandle_h (p q z w : SqU6 R) : (SqU6.gaTwoHandle p q z w).h = 0 := rfl
@[simp] theorem SqU6.gaTwoHandle_i (p q z w : SqU6 R) : (SqU6.gaTwoHandle p q z w).i = 0 := rfl

set_option maxHeartbeats 1000000 in
/-- ⭐ **Dressing both arguments of a commutator by `gamma_2`-elements** moves it by the handle
shift.  Unlike the committed `gamma_4`- and `gamma_3`-versions the translation touches the
commutator's class-three rows as well. -/
theorem SqU6.commP_mul_gaTwo {z w : SqU6 R} (p q : SqU6 R) (hz : z.IsGaTwo) (hw : w.IsGaTwo) :
    commP (p * z) (q * w) = commP p q * SqU6.gaTwoHandle p q z w := by
  obtain ⟨z1, z2, z3, z4, z5⟩ := hz
  obtain ⟨w1, w2, w3, w4, w5⟩ := hw
  ext <;>
    simp only [SqU6.gaTwoHandle, SqU6.gaTwoHandleX, SqU6.gaTwoPairJ, SqU6.gaTwoPairK,
      SqU6.gaTwoPairL, SqU6.gaTwoPairM, SqU6.gaTwoPairN, SqU6.gaTwoPairO, SqU6.u6Comm3L,
      SqU6.u6Comm3R, commP,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
      SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
      SqU6.inv_n, SqU6.inv_o, z1, z2, z3, z4, z5, w1, w2, w3, w4, w5] <;>
    ring

variable {h : ℕ}

/-- ⭐⭐ **The `gamma_3`-element by which the handle word moves** under an all-pair
`gamma_2`-dressing: the sum of the per-handle shifts, PLUS a strictly triangular cross-handle
term in the class-five row.  ⚠ At class four the cross term is absent, because there a
`gamma_3`-element is central against the handle word; here `[gamma_3, gamma_2] <= gamma_5` is
non-trivial, so each handle's shift pays a price as it passes the LATER handle commutators.
The term is `sqCross`-shaped and therefore **order-dependent**, exactly like the class-five
defect's cross-handle pairing. -/
def SqU6.gaTwoHandleSum (n : ℕ) (u v zu zv : Fin n → SqU6 R) : SqU6 R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0,
    ∑ k : Fin n, (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).j,
    ∑ k : Fin n, (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).k,
    ∑ k : Fin n, (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).l,
    ∑ k : Fin n, (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).m,
    ∑ k : Fin n, (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).n,
    ∑ k : Fin n, (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).o
      + sqCross (fun k => (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).j)
          (fun k => (u k).d * (v k).e - (v k).d * (u k).e)
      - sqCross (fun k => (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).l)
          (fun k => (u k).a * (v k).b - (v k).a * (u k).b)⟩

theorem SqU6.gaTwoHandleSum_isGaThree (n : ℕ) (u v zu zv : Fin n → SqU6 R) :
    (SqU6.gaTwoHandleSum n u v zu zv).IsGaThree :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⭐⭐ **The handle block under an all-pair `gamma_2`-dressing.** -/
theorem SqU6.handleWord_mul_gaTwo_all : ∀ (n : ℕ) (u v zu zv : Fin n → SqU6 R),
    (∀ k, (zu k).IsGaTwo) → (∀ k, (zv k).IsGaTwo) →
    handleWord (fun k => u k * zu k) (fun k => v k * zv k)
      = handleWord u v * SqU6.gaTwoHandleSum n u v zu zv
  | 0, u, v, zu, zv, _, _ => by
    simp only [handleWord_zero]
    ext <;> simp [SqU6.gaTwoHandleSum]
  | n + 1, u, v, zu, zv, hzu, hzv => by
    have htail := SqU6.handleWord_mul_gaTwo_all n (fun k => u k.succ) (fun k => v k.succ)
      (fun k => zu k.succ) (fun k => zv k.succ) (fun k => hzu _) (fun k => hzv _)
    have hpast := SqU6.gaThree_past_gaTwo
      (c := SqU6.gaTwoHandle (u 0) (v 0) (zu 0) (zv 0))
      (b := handleWord (fun k => u k.succ) (fun k => v k.succ))
      (SqU6.gaTwoHandle_isGaThree _ _ _ _)
      (SqU6.handleWord_isGaTwo (fun k => u k.succ) (fun k => v k.succ))
    rw [SqU6.handleWord_blockI, SqU6.handleWord_f, sqU6BlockI, sqU6BlockF] at hpast
    have hkey : SqU6.gaTwoHandle (u 0) (v 0) (zu 0) (zv 0)
        * SqU6.liftO ((SqU6.gaTwoHandle (u 0) (v 0) (zu 0) (zv 0)).j
            * ∑ j : Fin n, ((u j.succ).d * (v j.succ).e - (v j.succ).d * (u j.succ).e)
          - (∑ j : Fin n, ((u j.succ).a * (v j.succ).b - (v j.succ).a * (u j.succ).b))
            * (SqU6.gaTwoHandle (u 0) (v 0) (zu 0) (zv 0)).l)
        * SqU6.gaTwoHandleSum n (fun k => u k.succ) (fun k => v k.succ)
            (fun k => zu k.succ) (fun k => zv k.succ)
        = SqU6.gaTwoHandleSum (n + 1) u v zu zv := by
      ext <;>
        simp only [SqU6.gaTwoHandleSum, SqU6.liftO, SqU6.gaTwoHandle_a, SqU6.gaTwoHandle_b,
          SqU6.gaTwoHandle_c, SqU6.gaTwoHandle_d, SqU6.gaTwoHandle_e, SqU6.gaTwoHandle_f,
          SqU6.gaTwoHandle_g, SqU6.gaTwoHandle_h, SqU6.gaTwoHandle_i,
          SqU6.mul_a, SqU6.mul_b, SqU6.mul_c,
          SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j,
          SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n, SqU6.mul_o,
          Fin.sum_univ_succ, sqCross_succ] <;>
        ring
    rw [handleWord_succ, handleWord_succ, htail,
      SqU6.commP_mul_gaTwo (u 0) (v 0) (hzu 0) (hzv 0), mul_assoc (commP (u 0) (v 0)),
      ← mul_assoc (SqU6.gaTwoHandle (u 0) (v 0) (zu 0) (zv 0)), hpast, ← hkey]
    simp only [mul_assoc]

end HandleShift

/-! ## 4 The five-slot `gamma_2`-dressing and the translation identity -/

section Transport

variable {R : Type} [CommRing R] {h : ℕ}

variable (h) in
/-- **The collection element**: the `gamma_4`-shaped price of moving the core shift past the
handle word.  At class four this price is central and even; here it has two class-four rows as
well, and its class-five row reads the core shift's class-three rows against the handle block's
outer class-two rows. -/
def SqU6.gaTwoColl (m z : Fin (sqRank h) → SqU6 R) : SqU6 R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f
        * sqU6BlockH (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
      - (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).h
        * sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)),
    (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).g
        * sqU6BlockI (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
      - (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).i
        * sqU6BlockG (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)),
    (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f
        * sqU6BlockL (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
      - (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).l
        * sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
      + (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).j
        * sqU6BlockI (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
      - (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).i
        * sqU6BlockJ (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))⟩

theorem SqU6.gaTwoColl_isGaFour (m z : Fin (sqRank h) → SqU6 R) :
    (SqU6.gaTwoColl h m z).IsGaFour :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (h) in
/-- ⭐⭐ **The `gamma_2`-shift of the relator**: the core shift, times the summed handle shifts
with their cross-handle term, times the collection element.  `GradedGammaTwo.gaTwoShift` one
class up, and `GradedFiveStageFour.gaThreeShift` one filtration step wider. -/
def SqU6.gaTwoShift (m z : Fin (sqRank h) → SqU6 R) : SqU6 R :=
  SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)
    * (SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))
      * SqU6.gaTwoColl h m z)

theorem SqU6.gaTwoShift_isGaTwo {m z : Fin (sqRank h) → SqU6 R} :
    (SqU6.gaTwoShift h m z).IsGaTwo := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [SqU6.gaTwoShift, SqU6.gaTwoCore, SqU6.gaTwoHandleSum, SqU6.gaTwoColl,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e] <;>
    ring

variable {m z : Fin (sqRank h) → SqU6 R}

/-- ⭐⭐⭐ **THE `gamma_2`-LEVEL TRANSLATION IDENTITY AT CLASS FIVE.**  A five-slot
`gamma_2`-dressing moves the relator by the explicit `gamma_2`-element `SqU6.gaTwoShift`, at
every handle count and over any commutative ring.  This is the object `GradedFiveStageFour`
named as the next step ("one filtration step wider again ... would need the `gamma_2`-level
identity at class five.  That identity WILL carry a quadratic block") and it does: the
class-four rows carry `SqU6.gaTwoQuadM`, `SqU6.gaTwoQuadN` and the class-five row carries
`SqU6.gaTwoQuadO`, which unlike its class-four model is not even frame-free. -/
theorem SqU6.sqRelWord_gaTwoDress (hz : ∀ i, (z i).IsGaTwo) :
    sqRelWord (conFiveDress m z) = sqRelWord m * SqU6.gaTwoShift h m z := by
  have hhand := SqU6.handleWord_mul_gaTwo_all h (fun k => m (sqHandleIdxU k))
    (fun k => m (sqHandleIdxV k)) (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))
    (fun k => hz _) (fun k => hz _)
  have hpast : SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)
        * handleWord (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
      = handleWord (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        * SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2) * SqU6.gaTwoColl h m z := by
    rw [SqU6.gaTwo_past (SqU6.gaTwoCore_isGaTwo _ _ _ _ _ _) (SqU6.handleWord_isGaTwo _ _)]
    congr 1
    ext <;>
      simp only [SqU6.gaTwoColl, SqU6.handleWord_f, SqU6.handleWord_g, SqU6.handleWord_h,
        SqU6.handleWord_blockI, SqU6.handleWord_j, SqU6.handleWord_l]
  have hcomm := SqU6.gaFour_comm (SqU6.gaTwoColl_isGaFour (h := h) m z)
    (b := SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
      (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))) rfl rfl
  rw [sqRelWord, sqRelWord]
  simp only [conFiveDress_apply]
  rw [SqU6.sqWord_mul_gaTwo (m 0) (m 1) (m 2) (hz 0) (hz 1) (hz 2), hhand, SqU6.gaTwoShift]
  simp only [mul_assoc]
  refine congrArg _ ?_
  rw [← mul_assoc (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)), hpast]
  simp only [mul_assoc]
  rw [hcomm]

end Transport

/-! ## 5 The quadratic block is even on the achievable lattice -/

section Soundness

/-- The `(3,4)`-column of the `x0`-slot Fox letter; `sqFoxX6_a` is committed, this one is not
and section 5 needs it. -/
@[simp] theorem sqFoxX6_c {R : Type} [CommRing R] (s x y : SqU6 R) :
    (sqFoxX6 s x y).c = 10 * x.c - s.c - 8 * y.c := rfl

/-- A strictly triangular cross-handle pairing with an even left factor is even. -/
theorem sqCross_even_left {R : Type} [CommRing R] {n : ℕ} {x y : Fin n → R}
    (hx : ∀ s, (2 : R) ∣ x s) : (2 : R) ∣ sqCross x y := by
  refine Finset.dvd_sum fun t _ => Finset.dvd_sum fun s _ => ?_
  split_ifs
  · exact Dvd.dvd.mul_right (hx s) _
  · exact dvd_zero _

/-- …and with an even right factor. -/
theorem sqCross_even_right {R : Type} [CommRing R] {n : ℕ} {x y : Fin n → R}
    (hy : ∀ t, (2 : R) ∣ y t) : (2 : R) ∣ sqCross x y := by
  refine Finset.dvd_sum fun t _ => Finset.dvd_sum fun s _ => ?_
  split_ifs
  · exact Dvd.dvd.mul_left (hy t) _
  · exact dvd_zero _

/-- The handle block's first class-two coordinate is even when the letters' `(1,2)`-columns
are. -/
theorem sqU6BlockF_even {R : Type} [CommRing R] {n : ℕ} {u v : Fin n → SqU6 R}
    (hu : ∀ k, (2 : R) ∣ (u k).a) (hv : ∀ k, (2 : R) ∣ (v k).a) :
    (2 : R) ∣ sqU6BlockF u v :=
  Finset.dvd_sum fun k _ =>
    dvd_sub (Dvd.dvd.mul_right (hu k) _) (Dvd.dvd.mul_right (hv k) _)

/-- ⭐⭐⭐ **THE HEADLINE: the class-five quadratic block is EVEN on the achievable
lattice.**  At a marking whose slots have even `(1,2)`- and `(3,4)`-columns, and for dressings
in the honest `gamma_2` of the image (which `GradedFiveStageFour.stageN2_of_commutator` puts
inside `f`, `h`, `j` all even), every one of the fifty-two terms of `SqU6.gaTwoQuadO` is even.
So the `gamma_2` transport at class five is **affine mod two**, exactly as wave 54 found one
class down, and the difficulty the campaign had been anticipating collapses.  ⚠ The class-four
RIGHT row does not share this: `SqU6.gaTwoQuadN` is generically odd there
(`scripts/w61_wider/results/parity_blocks.txt`). -/
theorem SqU6.gaTwoQuadO_even {R : Type} [CommRing R] {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hsc : (2 : R) ∣ s.c) (hxa : (2 : R) ∣ x.a) (hxc : (2 : R) ∣ x.c)
    (hya : (2 : R) ∣ y.a) (hyc : (2 : R) ∣ y.c) (h0f : (2 : R) ∣ z₀.f) (h0h : (2 : R) ∣ z₀.h)
    (h0j : (2 : R) ∣ z₀.j) (h1f : (2 : R) ∣ z₁.f) (h1h : (2 : R) ∣ z₁.h) (h1j : (2 : R) ∣ z₁.j)
    (h2f : (2 : R) ∣ z₂.f) (h2h : (2 : R) ∣ z₂.h) (h2j : (2 : R) ∣ z₂.j) :
    (2 : R) ∣ SqU6.gaTwoQuadO s x y z₀ z₁ z₂ := by
  obtain ⟨sa, hsa⟩ := hsa
  obtain ⟨sc, hsc⟩ := hsc
  obtain ⟨xa, hxa⟩ := hxa
  obtain ⟨xc, hxc⟩ := hxc
  obtain ⟨ya, hya⟩ := hya
  obtain ⟨yc, hyc⟩ := hyc
  obtain ⟨zf0, h0f⟩ := h0f
  obtain ⟨zh0, h0h⟩ := h0h
  obtain ⟨zj0, h0j⟩ := h0j
  obtain ⟨zf1, h1f⟩ := h1f
  obtain ⟨zh1, h1h⟩ := h1h
  obtain ⟨zj1, h1j⟩ := h1j
  obtain ⟨zf2, h2f⟩ := h2f
  obtain ⟨zh2, h2h⟩ := h2h
  obtain ⟨zj2, h2j⟩ := h2j
  refine ⟨-z₀.i * zj1 - z₀.l * zf1 + z₁.i * zj0 + 10 * z₁.i * zj1 + z₁.l * zf0 + 10 * z₁.l * zf1
    - 8 * z₂.i * zj1 + z₂.i * zj2 - 8 * z₂.l * zf1 + z₂.l * zf2 + 2 * s.e * zf0 * zh1
    + 2 * s.e * zf2 * zh2 + sa * z₀.i * z₁.g - 4 * sa * z₁.g * z₁.i + 2 * sa * z₁.g * z₂.i
    + sa * z₂.g * z₂.i - 2 * sc * z₀.i * zf1 - 2 * sc * z₁.i * zf0 + 8 * sc * z₁.i * zf1
    - 4 * sc * z₂.i * zf1 - 4 * sc * z₂.i * zf2 - 8 * x.e * zf0 * zh1 + 6 * x.e * zf1 * zh0
    - 20 * x.e * zf1 * zh1 + 7 * xa * z₀.g * z₁.i - 2 * xa * z₀.g * z₂.i
    - 4 * xa * z₀.i * z₁.g + 30 * xa * z₁.g * z₁.i - 20 * xa * z₁.g * z₂.i
    + 2 * xc * z₀.i * zf1 - 6 * xc * z₁.i * zf0 - 40 * xc * z₁.i * zf1 + 4 * xc * z₂.i * zf0
    + 40 * xc * z₂.i * zf1 + 4 * y.e * zf0 * zh1 + 2 * y.e * zf0 * zh2 - 4 * y.e * zf1 * zh0
    + 24 * y.e * zf1 * zh1 - 8 * y.e * zf1 * zh2 - 4 * y.e * zf2 * zh0 + 2 * y.e * zf2 * zh2
    - 2 * ya * z₀.g * z₁.i - 2 * ya * z₀.g * z₂.i + 2 * ya * z₀.i * z₁.g + ya * z₀.i * z₂.g
    - 20 * ya * z₁.g * z₁.i + 16 * ya * z₁.g * z₂.i - ya * z₂.g * z₂.i + 2 * yc * z₀.i * zf2
    + 16 * yc * z₁.i * zf1 + 2 * yc * z₂.i * zf0 - 24 * yc * z₂.i * zf1, ?_⟩
  rw [SqU6.gaTwoQuadO, hsa, hsc, hxa, hxc, hya, hyc, h0f, h0h, h0j, h1f, h1h, h1j, h2f, h2h,
    h2j]
  ring

/-- ⭐⭐ **The class-five correction block is even on the achievable lattice.**  Nine of
its twenty-one coefficient blocks are killed by the dressing's even `f`, `h`, `j`; the other
twelve have every monomial carrying a frame `(1,2)`- or `(3,4)`-column. -/
theorem SqU6.gaTwoCorrO_even {R : Type} [CommRing R] {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hsc : (2 : R) ∣ s.c) (hxa : (2 : R) ∣ x.a) (hxc : (2 : R) ∣ x.c)
    (hya : (2 : R) ∣ y.a) (hyc : (2 : R) ∣ y.c) (h0f : (2 : R) ∣ z₀.f) (h0h : (2 : R) ∣ z₀.h)
    (h0j : (2 : R) ∣ z₀.j) (h1f : (2 : R) ∣ z₁.f) (h1h : (2 : R) ∣ z₁.h) (h1j : (2 : R) ∣ z₁.j)
    (h2f : (2 : R) ∣ z₂.f) (h2h : (2 : R) ∣ z₂.h) (h2j : (2 : R) ∣ z₂.j) :
    (2 : R) ∣ SqU6.gaTwoCorrO s x y z₀ z₁ z₂ := by
  obtain ⟨sa, hsa⟩ := hsa
  obtain ⟨sc, hsc⟩ := hsc
  obtain ⟨xa, hxa⟩ := hxa
  obtain ⟨xc, hxc⟩ := hxc
  obtain ⟨ya, hya⟩ := hya
  obtain ⟨yc, hyc⟩ := hyc
  obtain ⟨zf0, h0f⟩ := h0f
  obtain ⟨zh0, h0h⟩ := h0h
  obtain ⟨zj0, h0j⟩ := h0j
  obtain ⟨zf1, h1f⟩ := h1f
  obtain ⟨zh1, h1h⟩ := h1h
  obtain ⟨zj1, h1j⟩ := h1j
  obtain ⟨zf2, h2f⟩ := h2f
  obtain ⟨zh2, h2h⟩ := h2h
  obtain ⟨zj2, h2j⟩ := h2j
  refine ⟨-2 * s.b * sa * z₁.l - s.b * xa * z₀.l + 13 * s.b * xa * z₁.l - 10 * s.b * ya * z₁.l
    - 2 * s.b * ya * z₂.l - s.d * x.e * zj0 + 3 * s.d * x.e * zj1 - 2 * s.d * y.e * zj1
    - 2 * s.d * y.e * zj2 + 2 * s.e * s.f * zh1 + 2 * s.e * sa * z₁.k + s.e * x.d * zj0
    + s.e * x.d * zj1 - 14 * s.e * x.f * zh1 + s.e * x.h * zf0 + s.e * x.h * zf1
    - 14 * s.e * xa * z₁.k + s.e * y.d * zj2 + 10 * s.e * y.f * zh1 + s.e * y.f * zh2
    + s.e * y.h * zf2 + 10 * s.e * ya * z₁.k + s.e * ya * z₂.k - 2 * s.f * sc * z₁.i
    - 14 * s.f * x.e * zh1 + s.f * xc * z₀.i + 11 * s.f * xc * z₁.i + 10 * s.f * y.e * zh1
    + s.f * y.e * zh2 - 8 * s.f * yc * z₁.i + s.f * yc * z₂.i - 2 * s.g * sa * z₁.i
    - s.g * xa * z₀.i + 13 * s.g * xa * z₁.i - 10 * s.g * ya * z₁.i - 2 * s.g * ya * z₂.i
    - s.h * x.e * zf0 + 3 * s.h * x.e * zf1 - 2 * s.h * y.e * zf1 - 2 * s.h * y.e * zf2
    + 2 * s.i * sa * z₁.g - 14 * s.i * xa * z₁.g + 2 * s.i * xc * zf0 + 2 * s.i * xc * zf1
    + 10 * s.i * ya * z₁.g + s.i * ya * z₂.g + 2 * s.i * yc * zf2 + sa * x.b * z₀.l
    + 11 * sa * x.b * z₁.l - 14 * sa * x.e * z₁.k + sa * x.g * z₀.i + 11 * sa * x.g * z₁.i
    - 14 * sa * x.i * z₁.g - 8 * sa * y.b * z₁.l + sa * y.b * z₂.l + 10 * sa * y.e * z₁.k
    + sa * y.e * z₂.k - 8 * sa * y.g * z₁.i + sa * y.g * z₂.i + 10 * sa * y.i * z₁.g
    + sa * y.i * z₂.g - sc * x.f * z₀.i + 13 * sc * x.f * z₁.i - 2 * sc * x.i * zf0
    + 6 * sc * x.i * zf1 - 10 * sc * y.f * z₁.i - 2 * sc * y.f * z₂.i - 4 * sc * y.i * zf1
    - 4 * sc * y.i * zf2 - 4 * x.b * xa * z₀.l - 110 * x.b * xa * z₁.l + 2 * x.b * ya * z₀.l
    + 100 * x.b * ya * z₁.l - 4 * x.d * x.e * zj0 - 20 * x.d * x.e * zj1
    + 2 * x.d * y.e * zj0 + 20 * x.d * y.e * zj1 + 8 * x.e * x.f * zh0
    + 130 * x.e * x.f * zh1 - 4 * x.e * x.h * zf0 - 20 * x.e * x.h * zf1
    + 8 * x.e * xa * z₀.k + 130 * x.e * xa * z₁.k - 2 * x.e * y.f * zh0
    - 100 * x.e * y.f * zh1 - 2 * x.e * ya * z₀.k - 100 * x.e * ya * z₁.k
    - 4 * x.f * xc * z₀.i - 110 * x.f * xc * z₁.i - 2 * x.f * y.e * zh0
    - 100 * x.f * y.e * zh1 + 80 * x.f * yc * z₁.i - 4 * x.g * xa * z₀.i
    - 110 * x.g * xa * z₁.i + 2 * x.g * ya * z₀.i + 100 * x.g * ya * z₁.i
    + 2 * x.h * y.e * zf0 + 20 * x.h * y.e * zf1 + 8 * x.i * xa * z₀.g
    + 130 * x.i * xa * z₁.g - 8 * x.i * xc * zf0 - 40 * x.i * xc * zf1 - 2 * x.i * ya * z₀.g
    - 100 * x.i * ya * z₁.g + 80 * xa * y.b * z₁.l - 2 * xa * y.e * z₀.k
    - 100 * xa * y.e * z₁.k + 80 * xa * y.g * z₁.i - 2 * xa * y.i * z₀.g
    - 100 * xa * y.i * z₁.g + 2 * xc * y.f * z₀.i + 100 * xc * y.f * z₁.i
    + 4 * xc * y.i * zf0 + 40 * xc * y.i * zf1 + y.b * ya * z₀.l - 76 * y.b * ya * z₁.l
    + y.d * y.e * zj0 - 4 * y.d * y.e * zj1 - 2 * y.e * y.f * zh0 + 80 * y.e * y.f * zh1
    + y.e * y.h * zf0 - 4 * y.e * y.h * zf1 - 2 * y.e * ya * z₀.k + 80 * y.e * ya * z₁.k
    + y.f * yc * z₀.i - 76 * y.f * yc * z₁.i + y.g * ya * z₀.i - 76 * y.g * ya * z₁.i
    - 2 * y.i * ya * z₀.g + 80 * y.i * ya * z₁.g + 2 * y.i * yc * zf0 - 8 * y.i * yc * zf1
    - 14 * s.b * s.e * xa * zh1 + 12 * s.b * s.e * ya * zh1 - 2 * s.b * s.e * ya * zh2
    - 12 * s.b * sa * x.e * zh1 - 2 * s.b * sa * xc * z₀.i + 18 * s.b * sa * xc * z₁.i
    + 12 * s.b * sa * y.e * zh1 - 2 * s.b * sa * y.e * zh2 - 16 * s.b * sa * yc * z₁.i
    - 2 * s.b * sa * yc * z₂.i + 14 * s.b * sc * xa * z₁.i - 12 * s.b * sc * ya * z₁.i
    + 2 * s.b * sc * ya * z₂.i + 8 * s.b * x.e * xa * zh0 + 176 * s.b * x.e * xa * zh1
    - 144 * s.b * x.e * ya * zh1 + 6 * s.b * xa * xc * z₀.i - 194 * s.b * xa * xc * z₁.i
    - 4 * s.b * xa * y.e * zh0 - 148 * s.b * xa * y.e * zh1 + 160 * s.b * xa * yc * z₁.i
    - 4 * s.b * xc * ya * z₀.i + 156 * s.b * xc * ya * z₁.i - 2 * s.b * y.e * ya * zh0
    + 120 * s.b * y.e * ya * zh1 - 4 * s.b * y.e * ya * zh2 - 2 * s.b * ya * yc * z₀.i
    - 144 * s.b * ya * yc * z₁.i - 3 * s.d * sa * x.e * z₁.g + 2 * s.d * sa * y.e * z₁.g
    + s.d * sa * y.e * z₂.g + 2 * s.d * sc * x.e * zf0 + 2 * s.d * sc * y.e * zf2
    - 4 * s.d * x.e * xa * z₀.g + 12 * s.d * x.e * xa * z₁.g - 6 * s.d * x.e * xc * zf0
    - 6 * s.d * x.e * xc * zf1 + 2 * s.d * x.e * ya * z₀.g - 6 * s.d * x.e * ya * z₁.g
    - 8 * s.d * xa * y.e * z₁.g + 4 * s.d * xc * y.e * zf0 + 4 * s.d * xc * y.e * zf1
    + s.d * y.e * ya * z₀.g + 4 * s.d * y.e * ya * z₁.g + 2 * s.d * y.e * ya * z₂.g
    + 2 * s.d * y.e * yc * zf0 + 16 * s.d * y.e * yc * zf1 - 18 * s.e * sa * x.b * zh1
    - s.e * sa * x.d * z₁.g + 16 * s.e * sa * y.b * zh1 - 2 * s.e * sc * x.d * zf0
    - 2 * s.e * sc * y.d * zf2 + 188 * s.e * x.b * xa * zh1 - 144 * s.e * x.b * ya * zh1
    + 4 * s.e * x.d * xa * z₀.g + 4 * s.e * x.d * xa * z₁.g - 2 * s.e * x.d * xc * zf0
    - 2 * s.e * x.d * xc * zf1 - 2 * s.e * x.d * ya * z₀.g - 2 * s.e * x.d * ya * z₁.g
    - 160 * s.e * xa * y.b * zh1 + 122 * s.e * y.b * ya * zh1 - 2 * s.e * y.b * ya * zh2
    - s.e * y.d * ya * z₀.g - s.e * y.d * ya * z₂.g - 8 * s.e * y.d * yc * zf1
    + 2 * sa * sc * x.b * z₀.i + 20 * sa * sc * x.b * z₁.i - 16 * sa * sc * y.b * z₁.i
    + 2 * sa * sc * y.b * z₂.i - 8 * sa * x.b * x.e * zh0 + 192 * sa * x.b * x.e * zh1
    - 200 * sa * x.b * xc * z₁.i + 4 * sa * x.b * y.e * zh0 - 156 * sa * x.b * y.e * zh1
    + 160 * sa * x.b * yc * z₁.i + 10 * sa * x.d * x.e * z₁.g - 8 * sa * x.d * y.e * z₁.g
    - 160 * sa * x.e * y.b * zh1 + 160 * sa * xc * y.b * z₁.i + 2 * sa * y.b * y.e * zh0
    + 128 * sa * y.b * y.e * zh1 + 2 * sa * y.b * y.e * zh2 - 120 * sa * y.b * yc * z₁.i
    - 2 * sa * y.b * yc * z₂.i + sa * y.d * y.e * z₁.g - 6 * sc * x.b * xa * z₀.i
    - 194 * sc * x.b * xa * z₁.i + 4 * sc * x.b * ya * z₀.i + 148 * sc * x.b * ya * z₁.i
    + 8 * sc * x.d * x.e * zf0 - 12 * sc * x.d * x.e * zf1 - 4 * sc * x.d * y.e * zf0
    + 12 * sc * x.d * y.e * zf1 + 160 * sc * xa * y.b * z₁.i + 2 * sc * y.b * ya * z₀.i
    - 114 * sc * y.b * ya * z₁.i + 4 * sc * y.b * ya * z₂.i - 2 * sc * y.d * y.e * zf0
    - 10 * sc * y.d * y.e * zf1 + 28 * x.b * x.e * xa * zh0 - 1930 * x.b * x.e * xa * zh1
    - 28 * x.b * x.e * ya * zh0 + 1480 * x.b * x.e * ya * zh1 - 4 * x.b * xa * xc * z₀.i
    + 1990 * x.b * xa * xc * z₁.i - 12 * x.b * xa * y.e * zh0 + 1560 * x.b * xa * y.e * zh1
    - 1600 * x.b * xa * yc * z₁.i + 12 * x.b * xc * ya * z₀.i - 1560 * x.b * xc * ya * z₁.i
    + 8 * x.b * y.e * ya * zh0 - 1200 * x.b * y.e * ya * zh1 + 1280 * x.b * ya * yc * z₁.i
    - 22 * x.d * x.e * xa * z₀.g - 65 * x.d * x.e * xa * z₁.g + 20 * x.d * x.e * xc * zf0
    + 70 * x.d * x.e * xc * zf1 + 8 * x.d * x.e * ya * z₀.g + 40 * x.d * x.e * ya * z₁.g
    + 14 * x.d * xa * y.e * z₀.g + 60 * x.d * xa * y.e * z₁.g - 16 * x.d * xc * y.e * zf0
    - 80 * x.d * xc * y.e * zf1 - 4 * x.d * y.e * ya * z₀.g - 40 * x.d * y.e * ya * z₁.g
    + 1600 * x.e * xa * y.b * zh1 + 6 * x.e * y.b * ya * zh0 - 1220 * x.e * y.b * ya * zh1
    - 1600 * xa * xc * y.b * z₁.i - 1280 * xa * y.b * y.e * zh1
    + 1280 * xa * y.b * yc * z₁.i - xa * y.d * y.e * z₀.g - 10 * xa * y.d * y.e * z₁.g
    - 6 * xc * y.b * ya * z₀.i + 1220 * xc * y.b * ya * z₁.i + 2 * xc * y.d * y.e * zf0
    + 20 * xc * y.d * y.e * zf1 + 8 * y.b * y.e * ya * zh0 + 976 * y.b * y.e * ya * zh1
    - 4 * y.b * ya * yc * z₀.i - 992 * y.b * ya * yc * z₁.i - 2 * y.d * y.e * ya * z₀.g
    + 8 * y.d * y.e * ya * z₁.g, ?_⟩
  rw [SqU6.gaTwoCorrO, hsa, hsc, hxa, hxc, hya, hyc, h0f, h0h, h0j, h1f, h1h, h1j, h2f, h2h,
    h2j]
  ring

/-- **The three channels the frame does not close**: the class-five pairing
form's terms against the letter's fifth abelian column, its class-three row, and its class-two
row.  Wave 60's stage-four analogue closes two of five channels with the frame and three with
the dressing; here the same three survive, one filtration step wider. -/
def SqU6.gaTwoChannel {R : Type} [CommRing R] (z L : SqU6 R) : R :=
  z.m * L.e + z.i * L.j + z.l * L.f

/-- ⭐ **The class-five pairing form is even modulo the three channels.** -/
theorem SqU6.gaTwoPairO_channel_even {R : Type} [CommRing R] {z L : SqU6 R}
    (hLa : (2 : R) ∣ L.a) (hLc : (2 : R) ∣ L.c) (hzf : (2 : R) ∣ z.f) (hzh : (2 : R) ∣ z.h)
    (hzj : (2 : R) ∣ z.j) :
    (2 : R) ∣ (SqU6.gaTwoPairO z L - SqU6.gaTwoChannel z L) := by
  obtain ⟨La, hLa⟩ := hLa
  obtain ⟨Lc, hLc⟩ := hLc
  obtain ⟨zf, hzf⟩ := hzf
  obtain ⟨zh, hzh⟩ := hzh
  obtain ⟨zj, hzj⟩ := hzj
  refine ⟨-L.f * z.l + L.i * zj - L.j * z.i + L.l * zf - La * z.n + L.b * La * z.l
    - L.e * L.f * zh - L.e * La * z.k - 2 * L.e * zf * zh + L.f * Lc * z.i + L.g * La * z.i
    - L.i * La * z.g + 2 * Lc * z.i * zf + 2 * L.b * L.e * La * zh - 2 * L.b * La * Lc * z.i, ?_⟩
  rw [SqU6.gaTwoPairO, SqU6.gaTwoChannel, hLa, hLc, hzf, hzh, hzj]
  ring

/-- **The first class-three pairing form is even**, which is what kills the
collection element and the cross-handle term. -/
theorem SqU6.gaTwoPairJ_even {R : Type} [CommRing R] {z L : SqU6 R}
    (hzf : (2 : R) ∣ z.f) (hLa : (2 : R) ∣ L.a) : (2 : R) ∣ SqU6.gaTwoPairJ z L := by
  obtain ⟨zf, hzf⟩ := hzf
  obtain ⟨La, hLa⟩ := hLa
  exact ⟨zf * L.c - z.g * La, by rw [SqU6.gaTwoPairJ, hzf, hLa]; ring⟩

/-- ⭐ **The handle shift's class-five row is even modulo its two channels.** -/
theorem SqU6.gaTwoHandle_o_channel_even {R : Type} [CommRing R] {p q z w : SqU6 R}
    (hpa : (2 : R) ∣ p.a) (hpc : (2 : R) ∣ p.c) (hqa : (2 : R) ∣ q.a) (hqc : (2 : R) ∣ q.c)
    (hzf : (2 : R) ∣ z.f) (hzh : (2 : R) ∣ z.h) (hzj : (2 : R) ∣ z.j) (hwf : (2 : R) ∣ w.f)
    (hwh : (2 : R) ∣ w.h) (hwj : (2 : R) ∣ w.j) :
    (2 : R) ∣ ((SqU6.gaTwoHandle p q z w).o
      - (SqU6.gaTwoChannel z q - SqU6.gaTwoChannel w p)) := by
  obtain ⟨pa, hpa⟩ := hpa
  obtain ⟨pc, hpc⟩ := hpc
  obtain ⟨qa, hqa⟩ := hqa
  obtain ⟨qc, hqc⟩ := hqc
  obtain ⟨zf, hzf⟩ := hzf
  obtain ⟨zh, hzh⟩ := hzh
  obtain ⟨zj, hzj⟩ := hzj
  obtain ⟨wf, hwf⟩ := hwf
  obtain ⟨wh, hwh⟩ := hwh
  obtain ⟨wj, hwj⟩ := hwj
  refine ⟨p.f * w.l - p.i * wj + p.j * w.i - p.l * wf + pa * w.n - q.f * z.l + q.i * zj
    - q.j * z.i + q.l * zf - qa * z.n + w.i * zj + w.l * zf - wf * z.l - wj * z.i
    - p.b * pa * w.l - p.b * qa * w.l - p.b * qa * z.l - p.d * q.e * wj - p.d * q.e * zj
    + p.e * p.f * wh + p.e * pa * w.k + p.e * q.d * wj + p.e * q.d * zj + p.e * q.h * wf
    + p.e * q.h * zf + 2 * p.e * wf * wh + 2 * p.e * wh * zf - p.f * pc * w.i
    + p.f * qc * w.i + p.f * qc * z.i - p.g * pa * w.i - p.g * qa * w.i - p.g * qa * z.i
    - p.h * q.e * wf - p.h * q.e * zf + p.i * pa * w.g + 2 * p.i * qc * wf
    + 2 * p.i * qc * zf + pa * q.b * w.l + pa * q.b * z.l + pa * q.g * w.i + pa * q.g * z.i
    + pa * w.g * z.i - pc * q.f * w.i - pc * q.f * z.i - 2 * pc * q.i * wf
    - 2 * pc * q.i * zf - 2 * pc * w.i * wf - 2 * pc * w.i * zf - 2 * pc * wf * z.i
    + q.b * qa * z.l - q.e * q.f * zh - q.e * qa * z.k - 2 * q.e * wf * zh
    - 2 * q.e * zf * zh + q.f * qc * z.i + q.g * qa * z.i - q.i * qa * z.g - qa * w.i * z.g
    + 2 * qc * w.i * zf + 2 * qc * wf * z.i + 2 * qc * z.i * zf - 2 * p.b * p.e * pa * wh
    - 2 * p.b * p.e * qa * wh + 2 * p.b * pa * pc * w.i - 2 * p.b * pa * qc * w.i
    - 2 * p.b * pa * qc * z.i + 2 * p.b * pc * qa * w.i - 2 * p.b * qa * qc * w.i
    - 2 * p.b * qa * qc * z.i + p.d * pa * q.e * w.g + 2 * p.d * pc * q.e * zf
    + 2 * p.d * q.e * qc * wf + 2 * p.d * q.e * qc * zf + 2 * p.e * pa * q.b * wh
    - p.e * pa * q.d * w.g - 2 * p.e * pc * q.d * zf - 2 * p.e * q.d * qc * wf
    - 2 * p.e * q.d * qc * zf + 2 * pa * pc * q.b * z.i + 2 * pc * q.b * qa * w.i
    + 2 * pc * q.b * qa * z.i + 2 * q.b * q.e * qa * zh - 2 * q.b * qa * qc * z.i, ?_⟩
  simp only [SqU6.gaTwoHandle, SqU6.gaTwoHandleX, SqU6.gaTwoChannel, SqU6.gaTwoPairO,
    SqU6.u6Comm3L, SqU6.u6Comm3R,
    hpa, hpc, hqa, hqc, hzf, hzh, hzj, hwf, hwh, hwj]
  ring

/-- **The handle shift's class-three left row is even**, which is what kills the cross-handle
term and the collection element. -/
theorem SqU6.gaTwoHandle_j_even {R : Type} [CommRing R] {p q z w : SqU6 R}
    (hpa : (2 : R) ∣ p.a) (hqa : (2 : R) ∣ q.a) (hzf : (2 : R) ∣ z.f) (hwf : (2 : R) ∣ w.f) :
    (2 : R) ∣ (SqU6.gaTwoHandle p q z w).j :=
  dvd_sub (SqU6.gaTwoPairJ_even hzf hqa) (SqU6.gaTwoPairJ_even hwf hpa)

/-- ⭐⭐ **The core shift's class-five row is even modulo the three channels.**  Every block is:
the Frobenius weights are even outright, each Fox pairing is `SqU6.gaTwoPairO_channel_even`, the
correction is `SqU6.gaTwoCorrO_even`, and the quadratic block is `SqU6.gaTwoQuadO_even`. -/
theorem SqU6.gaTwoCore_o_channel_even {R : Type} [CommRing R] {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hsc : (2 : R) ∣ s.c) (hxa : (2 : R) ∣ x.a) (hxc : (2 : R) ∣ x.c)
    (hya : (2 : R) ∣ y.a) (hyc : (2 : R) ∣ y.c) (h0f : (2 : R) ∣ z₀.f) (h0h : (2 : R) ∣ z₀.h)
    (h0j : (2 : R) ∣ z₀.j) (h1f : (2 : R) ∣ z₁.f) (h1h : (2 : R) ∣ z₁.h) (h1j : (2 : R) ∣ z₁.j)
    (h2f : (2 : R) ∣ z₂.f) (h2h : (2 : R) ∣ z₂.h) (h2j : (2 : R) ∣ z₂.j) :
    (2 : R) ∣ ((SqU6.gaTwoCore s x y z₀ z₁ z₂).o
      - (SqU6.gaTwoChannel z₀ x + SqU6.gaTwoChannel z₁ (sqFoxX6 s x y)
        + SqU6.gaTwoChannel z₂ y)) := by
  have hfa : (2 : R) ∣ (sqFoxX6 s x y).a := by
    rw [sqFoxX6_a]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxa 10) hsa) (Dvd.dvd.mul_left hya 8)
  have hfc : (2 : R) ∣ (sqFoxX6 s x y).c := by
    rw [sqFoxX6_c]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxc 10) hsc) (Dvd.dvd.mul_left hyc 8)
  have hrw : (SqU6.gaTwoCore s x y z₀ z₁ z₂).o
      - (SqU6.gaTwoChannel z₀ x + SqU6.gaTwoChannel z₁ (sqFoxX6 s x y)
        + SqU6.gaTwoChannel z₂ y)
      = -4 * z₁.o + 2 * z₂.o
        + (SqU6.gaTwoPairO z₀ x - SqU6.gaTwoChannel z₀ x)
        + (SqU6.gaTwoPairO z₁ (sqFoxX6 s x y) - SqU6.gaTwoChannel z₁ (sqFoxX6 s x y))
        + (SqU6.gaTwoPairO z₂ y - SqU6.gaTwoChannel z₂ y)
        + SqU6.gaTwoCorrO s x y z₀ z₁ z₂ + SqU6.gaTwoQuadO s x y z₀ z₁ z₂ := by
    simp only [SqU6.gaTwoCore]
    ring
  rw [hrw]
  refine dvd_add (dvd_add (dvd_add (dvd_add (dvd_add ⟨-2 * z₁.o + z₂.o, by ring⟩
    (SqU6.gaTwoPairO_channel_even hxa hxc h0f h0h h0j))
    (SqU6.gaTwoPairO_channel_even hfa hfc h1f h1h h1j))
    (SqU6.gaTwoPairO_channel_even hya hyc h2f h2h h2j))
    (SqU6.gaTwoCorrO_even hsa hsc hxa hxc hya hyc h0f h0h h0j h1f h1h h1j h2f h2h h2j))
    (SqU6.gaTwoQuadO_even hsa hsc hxa hxc hya hyc h0f h0h h0j h1f h1h h1j h2f h2h h2j)

/-- ⭐ **The handle block's summed class-five row is even modulo its channels**, cross-handle
term included. -/
theorem SqU6.gaTwoHandleSum_o_channel_even {R : Type} [CommRing R] {n : ℕ}
    {u v zu zv : Fin n → SqU6 R}
    (hua : ∀ k, (2 : R) ∣ (u k).a) (huc : ∀ k, (2 : R) ∣ (u k).c)
    (hva : ∀ k, (2 : R) ∣ (v k).a) (hvc : ∀ k, (2 : R) ∣ (v k).c)
    (hzu : ∀ k, (2 : R) ∣ (zu k).f ∧ (2 : R) ∣ (zu k).h ∧ (2 : R) ∣ (zu k).j)
    (hzv : ∀ k, (2 : R) ∣ (zv k).f ∧ (2 : R) ∣ (zv k).h ∧ (2 : R) ∣ (zv k).j) :
    (2 : R) ∣ ((SqU6.gaTwoHandleSum n u v zu zv).o
      - ∑ k : Fin n, (SqU6.gaTwoChannel (zu k) (v k) - SqU6.gaTwoChannel (zv k) (u k))) := by
  have hrw : (SqU6.gaTwoHandleSum n u v zu zv).o
      - ∑ k : Fin n, (SqU6.gaTwoChannel (zu k) (v k) - SqU6.gaTwoChannel (zv k) (u k))
      = (∑ k : Fin n, ((SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).o
          - (SqU6.gaTwoChannel (zu k) (v k) - SqU6.gaTwoChannel (zv k) (u k))))
        + sqCross (fun k => (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).j)
            (fun k => (u k).d * (v k).e - (v k).d * (u k).e)
        - sqCross (fun k => (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).l)
            (fun k => (u k).a * (v k).b - (v k).a * (u k).b) := by
    simp only [SqU6.gaTwoHandleSum, Finset.sum_sub_distrib]
    ring
  rw [hrw]
  refine dvd_sub (dvd_add (Finset.dvd_sum fun k _ =>
      SqU6.gaTwoHandle_o_channel_even (hua k) (huc k) (hva k) (hvc k)
        (hzu k).1 (hzu k).2.1 (hzu k).2.2 (hzv k).1 (hzv k).2.1 (hzv k).2.2)
    (sqCross_even_left fun k =>
      SqU6.gaTwoHandle_j_even (hua k) (hva k) (hzu k).1 (hzv k).1))
    (sqCross_even_right fun k =>
      dvd_sub (Dvd.dvd.mul_right (hua k) _) (Dvd.dvd.mul_right (hva k) _))

variable {R : Type} [CommRing R] {h : ℕ} {m z : Fin (sqRank h) → SqU6 R}

/-- **The class-five row of the shift, unpacked** from the three-factor product: the core
shift's row, the handle sum's row, the collection element's row, and one cross term. -/
theorem SqU6.gaTwoShift_o (m z : Fin (sqRank h) → SqU6 R) :
    (SqU6.gaTwoShift h m z).o
      = (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).o
        + ((SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
              (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))).o
          + (SqU6.gaTwoColl h m z).o)
        + (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f
          * (SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
              (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))).l := by
  rw [SqU6.gaTwoShift, SqU6.gaThree_mul (SqU6.gaTwoHandleSum_isGaThree _ _ _ _ _)
    (SqU6.gaTwoColl_isGaFour m z).isGaThree, SqU6.mul_o]
  simp only [SqU6.gaTwoCore_a, SqU6.gaTwoColl]
  ring

/-- ⭐ **The collection element's class-five row is even** on the achievable lattice: its four
blocks meet the core shift's even class-two rows, its even class-three left row, and the handle
block's even `(a, b)`-pairing. -/
theorem SqU6.gaTwoColl_o_even
    (ha : ∀ i, (2 : R) ∣ (m i).a)
    (hz : ∀ i, (2 : R) ∣ (z i).f ∧ (2 : R) ∣ (z i).h ∧ (2 : R) ∣ (z i).j) :
    (2 : R) ∣ (SqU6.gaTwoColl h m z).o := by
  have hcf : (2 : R) ∣ (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f :=
    ⟨-2 * (z 1).f + (z 2).f, by rw [SqU6.gaTwoCore_f]; ring⟩
  have hci : (2 : R) ∣ (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).i :=
    ⟨-2 * (z 1).i + (z 2).i, by rw [SqU6.gaTwoCore_i]; ring⟩
  have hfa : (2 : R) ∣ (sqFoxX6 (m 0) (m 1) (m 2)).a := by
    rw [sqFoxX6_a]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left (ha 1) 10) (ha 0)) (Dvd.dvd.mul_left (ha 2) 8)
  have hcj : (2 : R) ∣ (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).j := by
    have : (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).j
        = -4 * (z 1).j + 2 * (z 2).j + (SqU6.gaTwoPairJ (z 0) (m 1)
          + SqU6.gaTwoPairJ (z 1) (sqFoxX6 (m 0) (m 1) (m 2)) + SqU6.gaTwoPairJ (z 2) (m 2)) :=
      rfl
    rw [this]
    exact dvd_add ⟨-2 * (z 1).j + (z 2).j, by ring⟩
      (dvd_add (dvd_add (SqU6.gaTwoPairJ_even (hz 0).1 (ha 1))
        (SqU6.gaTwoPairJ_even (hz 1).1 hfa)) (SqU6.gaTwoPairJ_even (hz 2).1 (ha 2)))
  have hbf : (2 : R) ∣ sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)) :=
    sqU6BlockF_even (fun k => ha _) (fun k => ha _)
  simp only [SqU6.gaTwoColl]
  exact dvd_sub (dvd_add (dvd_sub (Dvd.dvd.mul_right hcf _) (Dvd.dvd.mul_left hbf _))
    (Dvd.dvd.mul_right hcj _)) (Dvd.dvd.mul_right hci _)

variable (h) in
/-- **The three-channel functional**: the only part of the class-five row that survives mod two
on the achievable lattice.  Each slot's dressing is read against the PERMUTED letter, exactly as
in the Fox form, and each handle against the opposite handle letter. -/
def SqU6.gaTwoShiftChan (m z : Fin (sqRank h) → SqU6 R) : R :=
  SqU6.gaTwoChannel (z 0) (m 1) + SqU6.gaTwoChannel (z 1) (sqFoxX6 (m 0) (m 1) (m 2))
    + SqU6.gaTwoChannel (z 2) (m 2)
    + ∑ k : Fin h, (SqU6.gaTwoChannel (z (sqHandleIdxU k)) (m (sqHandleIdxV k))
        - SqU6.gaTwoChannel (z (sqHandleIdxV k)) (m (sqHandleIdxU k)))

/-- ⭐⭐⭐ **THE `gamma_2`-LEVEL SOUNDNESS AT CLASS FIVE.**  At any marking all of whose slots
have an even `(1,2)`-column and an even `(3,4)`-column, every five-slot `gamma_2`-dressing whose
slots have even `f`, `h` and `j` moves the relator's class-five row by the three-channel
functional `SqU6.gaTwoShiftChan`, **modulo two**.  Everything else - the whole quadratic block
included - is even.

This is the statement `GradedFiveStageFour` could not make.  The hypotheses are exactly its
`stageN1` on the frame and `stageN2` on the dressing, and `stageN2_of_commutator` proves that
the honest `gamma_2` of an image subgroup with `stageN1` letters satisfies them, so the lattice
here is achievable, not declared. -/
theorem SqU6.gaTwoShift_o_channel_even
    (ha : ∀ i, (2 : R) ∣ (m i).a) (hc : ∀ i, (2 : R) ∣ (m i).c)
    (hz : ∀ i, (2 : R) ∣ (z i).f ∧ (2 : R) ∣ (z i).h ∧ (2 : R) ∣ (z i).j) :
    (2 : R) ∣ ((SqU6.gaTwoShift h m z).o - SqU6.gaTwoShiftChan h m z) := by
  have hcf : (2 : R) ∣ (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f :=
    ⟨-2 * (z 1).f + (z 2).f, by rw [SqU6.gaTwoCore_f]; ring⟩
  have hrw : (SqU6.gaTwoShift h m z).o - SqU6.gaTwoShiftChan h m z
      = ((SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).o
          - (SqU6.gaTwoChannel (z 0) (m 1)
            + SqU6.gaTwoChannel (z 1) (sqFoxX6 (m 0) (m 1) (m 2))
            + SqU6.gaTwoChannel (z 2) (m 2)))
        + ((SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
              (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))).o
            - ∑ k : Fin h, (SqU6.gaTwoChannel (z (sqHandleIdxU k)) (m (sqHandleIdxV k))
              - SqU6.gaTwoChannel (z (sqHandleIdxV k)) (m (sqHandleIdxU k))))
        + (SqU6.gaTwoColl h m z).o
        + (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f
          * (SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
              (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))).l := by
    rw [SqU6.gaTwoShift_o, SqU6.gaTwoShiftChan]
    ring
  rw [hrw]
  exact dvd_add (dvd_add (dvd_add
    (SqU6.gaTwoCore_o_channel_even (ha 0) (hc 0) (ha 1) (hc 1) (ha 2) (hc 2)
      (hz 0).1 (hz 0).2.1 (hz 0).2.2 (hz 1).1 (hz 1).2.1 (hz 1).2.2
      (hz 2).1 (hz 2).2.1 (hz 2).2.2)
    (SqU6.gaTwoHandleSum_o_channel_even (fun k => ha _) (fun k => hc _) (fun k => ha _)
      (fun k => hc _) (fun k => hz _) (fun k => hz _)))
    (SqU6.gaTwoColl_o_even ha hz)) (Dvd.dvd.mul_right hcf _)

/-- The shift's class-three right row: the Frobenius weights plus the class-three Fox pairings
and the summed handle pairings; the collection element does not reach it. -/
theorem SqU6.gaTwoShift_l (m z : Fin (sqRank h) → SqU6 R) :
    (SqU6.gaTwoShift h m z).l
      = (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).l
        + (SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
            (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))).l := by
  rw [SqU6.gaTwoShift, SqU6.gaThree_mul (SqU6.gaTwoHandleSum_isGaThree _ _ _ _ _)
    (SqU6.gaTwoColl_isGaFour m z).isGaThree, SqU6.mul_l]
  simp only [SqU6.gaTwoCore, SqU6.gaTwoColl]
  ring

/-- The shift's fourth class-two row: the Frobenius weights alone, hence even. -/
theorem SqU6.gaTwoShift_i (m z : Fin (sqRank h) → SqU6 R) :
    (SqU6.gaTwoShift h m z).i = -4 * (z 1).i + 2 * (z 2).i := by
  rw [SqU6.gaTwoShift, SqU6.gaThree_mul (SqU6.gaTwoHandleSum_isGaThree _ _ _ _ _)
    (SqU6.gaTwoColl_isGaFour m z).isGaThree, SqU6.mul_i]
  simp only [SqU6.gaTwoCore]
  ring

/-- ⭐ **The shift's class-three right row is even on the achievable lattice**: the pairing form
`SqU6.gaTwoPairL` meets the dressing's even `h` and the letter's even `(3,4)`-column. -/
theorem SqU6.gaTwoShift_l_even
    (hc : ∀ i, (2 : R) ∣ (m i).c)
    (hz : ∀ i, (2 : R) ∣ (z i).f ∧ (2 : R) ∣ (z i).h ∧ (2 : R) ∣ (z i).j) :
    (2 : R) ∣ (SqU6.gaTwoShift h m z).l := by
  have hpair : ∀ (w L : SqU6 R), (2 : R) ∣ w.h → (2 : R) ∣ L.c →
      (2 : R) ∣ SqU6.gaTwoPairL w L := by
    rintro w L ⟨wh, hwh⟩ ⟨Lc, hLc⟩
    exact ⟨wh * L.e - w.i * Lc, by rw [SqU6.gaTwoPairL, hwh, hLc]; ring⟩
  have hfc : (2 : R) ∣ (sqFoxX6 (m 0) (m 1) (m 2)).c := by
    rw [sqFoxX6_c]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left (hc 1) 10) (hc 0)) (Dvd.dvd.mul_left (hc 2) 8)
  have hcore : (2 : R) ∣ (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).l := by
    have hval : (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).l
        = -4 * (z 1).l + 2 * (z 2).l + (SqU6.gaTwoPairL (z 0) (m 1)
          + SqU6.gaTwoPairL (z 1) (sqFoxX6 (m 0) (m 1) (m 2)) + SqU6.gaTwoPairL (z 2) (m 2)) :=
      rfl
    rw [hval]
    exact dvd_add ⟨-2 * (z 1).l + (z 2).l, by ring⟩
      (dvd_add (dvd_add (hpair _ _ (hz 0).2.1 (hc 1)) (hpair _ _ (hz 1).2.1 hfc))
        (hpair _ _ (hz 2).2.1 (hc 2)))
  rw [SqU6.gaTwoShift_l]
  refine dvd_add hcore ?_
  have hsum : (SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k))
      (fun k => m (sqHandleIdxV k)) (fun k => z (sqHandleIdxU k))
      (fun k => z (sqHandleIdxV k))).l
      = ∑ k : Fin h, (SqU6.gaTwoHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
        (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).l := rfl
  rw [hsum]
  exact Finset.dvd_sum fun k _ =>
    dvd_sub (hpair _ _ (hz _).2.1 (hc _)) (hpair _ _ (hz _).2.1 (hc _))

/-- ⭐⭐⭐ **THE COMPLETE MOD-TWO TRANSPORT.**  On the achievable lattice the class-five residue
of a `gamma_2`-dressed frame differs from the undressed one by the three-channel functional
`SqU6.gaTwoShiftChan`, and by nothing else.  Every other block of the fifteen-coordinate
identity - the correction, the collection element, the cross-handle term, and the whole
**quadratic** block - is even.

This is the sharpest thing the wave can say: the `gamma_2` transport at class five is affine
mod two, so a `gamma_2`-level exclusion is exactly as hard as making the three channels
`z.m * L.e`, `z.i * L.j`, `z.l * L.f` vanish. -/
theorem SqU6.sqRelWord_gaTwoDress_o_channel
    (ha : ∀ i, (2 : R) ∣ (m i).a) (hc : ∀ i, (2 : R) ∣ (m i).c)
    (hzg : ∀ i, (z i).IsGaTwo)
    (hz : ∀ i, (2 : R) ∣ (z i).f ∧ (2 : R) ∣ (z i).h ∧ (2 : R) ∣ (z i).j) :
    (2 : R) ∣ ((sqRelWord (conFiveDress m z)).o - (sqRelWord m).o
      - SqU6.gaTwoShiftChan h m z) := by
  have hra : (2 : R) ∣ (sqRelWord m).a :=
    ⟨-2 * (m 1).a + (m 2).a, by rw [SqU6.sqRelWord_a]; ring⟩
  have hgi : (2 : R) ∣ (SqU6.gaTwoShift h m z).i := by
    rw [SqU6.gaTwoShift_i]
    exact ⟨-2 * (z 1).i + (z 2).i, by ring⟩
  have hge : (SqU6.gaTwoShift h m z).e = 0 := (SqU6.gaTwoShift_isGaTwo (m := m) (z := z)).2.2.2.2
  have hrw : (sqRelWord (conFiveDress m z)).o - (sqRelWord m).o - SqU6.gaTwoShiftChan h m z
      = ((SqU6.gaTwoShift h m z).o - SqU6.gaTwoShiftChan h m z)
        + (sqRelWord m).a * (SqU6.gaTwoShift h m z).n
        + (sqRelWord m).f * (SqU6.gaTwoShift h m z).l
        + (sqRelWord m).j * (SqU6.gaTwoShift h m z).i
        + (sqRelWord m).m * (SqU6.gaTwoShift h m z).e := by
    rw [SqU6.sqRelWord_gaTwoDress hzg, SqU6.mul_o]
    ring
  rw [hrw, hge, mul_zero, add_zero]
  exact dvd_add (dvd_add (dvd_add (SqU6.gaTwoShift_o_channel_even ha hc hz)
    (Dvd.dvd.mul_right hra _)) (Dvd.dvd.mul_left (SqU6.gaTwoShift_l_even hc hz) _))
    (Dvd.dvd.mul_left hgi _)

end Soundness

/-! ## 6 Achievability: the honest `gamma_2` of the image, and wave 60's point -/

section Achievable

variable {h : ℕ} {j : Fin h}

/-- ⭐ **The achievable `gamma_2`-dressings of a marking with even `(1,2)`- and `(3,4)`-columns
lie in `stageN2`.**  `GradedFiveStageFour` proves the two-step chain `forceLcs H 2 <= stageN3`
and this is its first step, named: `forceLcs H 1` is the honest `gamma_2` of the image subgroup,
not a declared lattice, and `stageN2_of_commutator` (imported) is the whole content. -/
theorem forceLcs_one_le_stageN2 {H : Subgroup (SqU6 gr3R)} (hH : H ≤ stageN1) :
    forceLcs H 1 ≤ stageN2 :=
  Subgroup.commutator_le.mpr fun _p hp _q hq => stageN2_of_commutator (hH hp) (hH hq)

/-- Every element of `stageN2` is `gamma_2`-shaped, so the identity applies to it. -/
theorem stageN2_isGaTwo {p : SqU6 gr3R} (hp : p ∈ stageN2) : p.IsGaTwo :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1⟩

/-- …and its three load-bearing coordinates are even. -/
theorem stageN2_even {p : SqU6 gr3R} (hp : p ∈ stageN2) :
    (2 : gr3R) ∣ p.f ∧ (2 : gr3R) ∣ p.h ∧ (2 : gr3R) ∣ p.j :=
  ⟨hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩

/-- Every slot of wave 60's binder point has an even `(1,2)`- and an even `(3,4)`-column, read
straight off its committed `stageImage_le_stageN1`. -/
theorem stageWit_ac_even {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c)
    (i : Fin (sqRank h)) :
    (2 : gr3R) ∣ (stageWit h j v i).a ∧ (2 : gr3R) ∣ (stageWit h j v i).c := by
  have hmem : stageWit h j v i ∈ stageImage h j v := Subgroup.subset_closure ⟨i, rfl⟩
  exact mem_stageN1.mp (stageImage_le_stageN1 hv hmem)

/-- ⭐⭐ **The `gamma_2`-level residual at wave 60's point, exactly.**  At the stage-four binder
point, if some achievable `gamma_2`-dressing of the five slots kills the dressed frame, then the
class-five residue is even **modulo the three-channel functional**.  Wave 60's stage-four
exclusion is the special case where the functional itself is even; one filtration step wider it
need not be, and this theorem says that is the ONLY thing in the way. -/
theorem stageWit_gaTwo_forced {v : SqU6 gr3R} {z : Fin (sqRank h) → SqU6 gr3R}
    (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c)
    (hz : ∀ i, z i ∈ forceLcs (stageImage h j v) 1)
    (hkill : sqRelWord (conFiveDress (stageWit h j v) z) = 1) :
    selPar ((sqRelWord (stageWit h j v)).o
      + SqU6.gaTwoShiftChan h (stageWit h j v) z) = 0 := by
  have hle := forceLcs_one_le_stageN2 (stageImage_le_stageN1 (h := h) (j := j) hv)
  have hac : ∀ i, (2 : gr3R) ∣ (stageWit h j v i).a ∧ (2 : gr3R) ∣ (stageWit h j v i).c :=
    fun i => stageWit_ac_even hv i
  have hmain := SqU6.sqRelWord_gaTwoDress_o_channel (m := stageWit h j v) (z := z)
    (fun i => (hac i).1) (fun i => (hac i).2)
    (fun i => stageN2_isGaTwo (hle (hz i))) (fun i => stageN2_even (hle (hz i)))
  rw [hkill, SqU6.one_o] at hmain
  obtain ⟨c, hc⟩ := hmain
  have hfin : (sqRelWord (stageWit h j v)).o + SqU6.gaTwoShiftChan h (stageWit h j v) z
      = 2 * (-c) := by linear_combination -hc
  rw [hfin, selPar_two_mul]

end Achievable

/-! ## 7 Kernel cross-checks

Wave 57's process finding was that two results of one wave can each be right while their
composition is vacuous, so the structural route of sections 2 to 4 and the machine route are
made to meet here: the same identity, at wave 60's binder point with a concrete five-slot
`gamma_2`-dressing, by `decide` on `ZMod 8`. -/

section CrossCheck

/-- A concrete five-slot `gamma_2`-dressing, live in every one of the ten coordinates. -/
def gaTwoProbe : Fin (sqRank 1) → SqU6 gr3R :=
  ![⟨0, 0, 0, 0, 0, 1, 0, 3, 0, 2, 0, 1, 5, 0, 3⟩,
    ⟨0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 3, 0, 0, 4, 1⟩,
    ⟨0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 2, 0, 1, 0⟩,
    ⟨0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 3, 0, 2⟩,
    ⟨0, 0, 0, 0, 0, 3, 0, 0, 1, 2, 0, 0, 0, 5, 4⟩]

theorem gaTwoProbe_isGaTwo : ∀ i, (gaTwoProbe i).IsGaTwo := by
  intro i
  fin_cases i <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⭐ **The translation identity, by kernel computation**, at wave 60's binder point and the
concrete dressing above: both sides of `SqU6.sqRelWord_gaTwoDress` evaluated by `decide`. -/
theorem gaTwoDress_decide_crosscheck :
    sqRelWord (conFiveDress (stageWit 1 0 stageX) gaTwoProbe)
      = sqRelWord (stageWit 1 0 stageX)
        * SqU6.gaTwoShift 1 (stageWit 1 0 stageX) gaTwoProbe := by decide

/-- …and the dressing is not a trivial probe: it moves the class-five row. -/
theorem gaTwoProbe_moves :
    (SqU6.gaTwoShift 1 (stageWit 1 0 stageX) gaTwoProbe) ≠ 1 := by decide

end CrossCheck


/-! ## 8 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every `decide` is
on `ZMod 8`, `SqU6 (ZMod 8)` or `Fin`-indexed tuples over them; there is no `native_decide`. -/

section AxiomPins

#print axioms SqU6.IsGaTwo
#print axioms SqU6.IsGaThree.isGaTwo
#print axioms SqU6.isGaTwo_one
#print axioms SqU6.commP_isGaTwo
#print axioms SqU6.handleWord_isGaTwo
#print axioms SqU6.gaTwoPairJ
#print axioms SqU6.gaTwoPairK
#print axioms SqU6.gaTwoPairL
#print axioms SqU6.gaTwoPairM
#print axioms SqU6.gaTwoPairN
#print axioms SqU6.gaTwoPairO
#print axioms SqU6.commP_gaTwo_eq
#print axioms SqU6.gaTwo_commP
#print axioms SqU6.gaTwo_past
#print axioms SqU6.gaThree_past_gaTwo
#print axioms SqU6.gaTwoCorrM
#print axioms SqU6.gaTwoCorrN
#print axioms SqU6.gaTwoCorrO
#print axioms SqU6.gaTwoQuadM
#print axioms SqU6.gaTwoQuadN
#print axioms SqU6.gaTwoQuadO
#print axioms SqU6.gaTwoCore
#print axioms SqU6.gaTwoCore_isGaTwo
#print axioms SqU6.gaTwoCore_a
#print axioms SqU6.gaTwoCore_f
#print axioms SqU6.gaTwoCore_g
#print axioms SqU6.gaTwoCore_h
#print axioms SqU6.gaTwoCore_i
#print axioms SqU6.sqWord_mul_gaTwo
#print axioms SqU6.gaTwoHandleX
#print axioms SqU6.gaTwoHandle
#print axioms SqU6.gaTwoHandle_isGaThree
#print axioms SqU6.gaTwoHandle_a
#print axioms SqU6.gaTwoHandle_b
#print axioms SqU6.gaTwoHandle_c
#print axioms SqU6.gaTwoHandle_d
#print axioms SqU6.gaTwoHandle_e
#print axioms SqU6.gaTwoHandle_f
#print axioms SqU6.gaTwoHandle_g
#print axioms SqU6.gaTwoHandle_h
#print axioms SqU6.gaTwoHandle_i
#print axioms SqU6.commP_mul_gaTwo
#print axioms SqU6.gaTwoHandleSum
#print axioms SqU6.gaTwoHandleSum_isGaThree
#print axioms SqU6.handleWord_mul_gaTwo_all
#print axioms SqU6.gaTwoColl
#print axioms SqU6.gaTwoColl_isGaFour
#print axioms SqU6.gaTwoShift
#print axioms SqU6.gaTwoShift_isGaTwo
#print axioms SqU6.sqRelWord_gaTwoDress
#print axioms sqFoxX6_c
#print axioms sqCross_even_left
#print axioms sqCross_even_right
#print axioms sqU6BlockF_even
#print axioms SqU6.gaTwoQuadO_even
#print axioms SqU6.gaTwoCorrO_even
#print axioms SqU6.gaTwoChannel
#print axioms SqU6.gaTwoPairO_channel_even
#print axioms SqU6.gaTwoPairJ_even
#print axioms SqU6.gaTwoHandle_o_channel_even
#print axioms SqU6.gaTwoHandle_j_even
#print axioms SqU6.gaTwoCore_o_channel_even
#print axioms SqU6.gaTwoHandleSum_o_channel_even
#print axioms SqU6.gaTwoShift_o
#print axioms SqU6.gaTwoColl_o_even
#print axioms SqU6.gaTwoShiftChan
#print axioms SqU6.gaTwoShift_o_channel_even
#print axioms SqU6.gaTwoShift_l
#print axioms SqU6.gaTwoShift_i
#print axioms SqU6.gaTwoShift_l_even
#print axioms SqU6.sqRelWord_gaTwoDress_o_channel
#print axioms forceLcs_one_le_stageN2
#print axioms stageN2_isGaTwo
#print axioms stageN2_even
#print axioms stageWit_ac_even
#print axioms stageWit_gaTwo_forced
#print axioms gaTwoProbe
#print axioms gaTwoProbe_isGaTwo
#print axioms gaTwoDress_decide_crosscheck
#print axioms gaTwoProbe_moves

end AxiomPins

end SqCore

end Dyadic

end GQ2
