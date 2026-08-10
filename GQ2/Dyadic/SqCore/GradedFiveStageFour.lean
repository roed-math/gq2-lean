/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveForce

/-!
# W60-STAGE4: the stage-four translation identity at class five, and the exclusion made
unconditional

`GradedFiveForce` discharged the sigma residual that `GradedSigmaFour` section 7 had carried
since wave 51, and volunteered its own limit:

> ⚠ The exclusion is against **stage-five** refinements, and the second headline below is that
> it is false one filtration step wider.

At its point the image's class-three layer contains the whole class-four layer of the carrier,
so the triple commutator `[[sigma, U], x1] = <m=5, n=6>` of the point's own letters is
`gamma_4`-shaped with an **odd** class-four coordinate and kills the dressed frame.  The
committed class-four point has no analogous hole, so the class-five statement was genuinely
weaker than the class-four one it imitates.  Both halves of that gap are closed here.

## ⭐⭐ Headline 1: the stage-four translation identity, and it is EASIER than its model

`sqRelWord_gaThreeDress`.  A five-slot `gamma_3`-dressing moves the relator by an explicit
`gamma_3`-element `gaThreeShift`, at every handle count and over any commutative ring.  Its
class-three rows move by the Frobenius weights `(-4, 2)` on the exponent slots alone; each
class-four row by the class-four graded Fox pairings `gaThreePairL`, `gaThreePairR` against the
permuted letters `(x0, 10 x0 - sigma - 8 x1, x1)`; and the class-five row by the Frobenius
weight, the class-five pairing `gaThreePair`, the correction `gaThreeCorr`, and one central
collection term pairing the handle block's two outer class-two rows against the shift's outer
class-three rows.

This is the object `GradedFiveDefect` deferred and `GradedFiveForce` said it did not build.
⭐ **The stated reason for the deferral does not survive.**  `GradedFiveDefect` deferred "the
`gamma_3`- and `gamma_2`-level transports at class five, **whose defect shifts are quadratic**
and not covered by the affine calculus here".  They are not quadratic.  The class-four
precedent `GradedGammaTwo` needs a genuinely quadratic block `gaTwoQuad`, whose coefficients
come from `gaTwo_swap`, the fact that `[gamma_2, gamma_2] = gamma_4` is non-trivial at class
four.  One class up `[gamma_3, gamma_3] <= gamma_6 = 1` (`SqU6.gaThree_comm`), so the shift is
**affine** in the dressings and the analogue of `gaTwoQuad` is identically zero.  Everything
else transposes **verbatim**: all nine blocks and all forty-four coefficients of `gaThreeCorr`
are `GradedGammaTwo.gaTwoCorr` under the dictionary `(e,f,g,h,i,j) -> (j,k,l,m,n,o)` on the
dressing and `(a,b,c,d,e,g) -> (a,b,.,e,f,i)` on the letter
(`scripts/w60_stage4/results/derive.txt` section 3c).

## ⭐⭐⭐ Headline 2: the class-five exclusion is now UNCONDITIONAL

`sqRelWord_stageWit_diag_ne_one`.  At a **new** binder point - letters
`x0 = <a=2, e=5>`, `x1 = <e=2, f=1, g=1, h=1, m=3, n=3>`,
`U = <a=6, b=7, c=4, d=1, e=3, g=5, h=5>`,
`V = <a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4>`, at **every** handle count and **every**
handle - the undressed frame kills the relator (`sqRelWord_stageWit_triv`), the `a0 = a1`
dressing leaves the **odd** class-five residue `1` (`sqRelWord_stageWit_diag`), and **no
achievable STAGE-FOUR refinement whatsoever** kills it.  The quantifier is one filtration step
wider than wave 59's, which is exactly the scope the committed class-four exclusion enjoys.

The point is not a lucky find; it is wave 59's point with one hypothesis added.  Wave 59's
soundness input is that every letter has an even `(3,4)`-column.  Add: **every letter has an
even `(1,2)`-column** too.  Wave 59's `forceU` fails it, at one coordinate, `a = 1`
(`forceU_not_stageN1`), and that coordinate is precisely the one producing its hole:
`[sigma, U].f = -U.a`, and the killing triple commutator's class-four coordinate is
`[sigma, U].f * x1.h`.

The chain that makes it a theorem is `forceLcs_two_le_stageN3`: at any marking whose slots have
both columns even, **every achievable `gamma_3`-dressing** - the honest `gamma_3` of the image
subgroup, not a declared lattice - has `j`, `l` and `m` even.  Two steps: a commutator of two
such letters is `gamma_2`-shaped with `f`, `h`, `j` even; pairing that against another such
letter gives a `gamma_3`-element with `j`, `l`, `m` even.  Wave 59's chain runs one step further
and lands in `gamma_4`; this one stops one step earlier, which is the step the exclusion was
missing.

⭐ **Why exactly those three coordinates, and no others** (`gaThreeShiftO_even`).  Every term of
the shift's class-five row is one dressing coordinate against a frame quantity.  The `o`-channel
carries the weights `(-4, 2)` and is even outright; the `n`-channel is `- z.n * L.a` and the
`k`-channel is `- z.k * (L.a * L.e)` plus blocks with even coefficients, so both are killed by
the frame's even `(1,2)`-columns; the `j`-, `l`- and `m`-channels meet columns that can be odd,
and are killed by the dressing.  So the soundness hypothesis is not padding: it is the exact
list of channels the frame does not already close.

## What is proved versus what is measured

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`): everything above, at every
handle count and every handle, over any commutative ring where the statement is ring-generic.
The exclusion, its soundness chain, the evenness theorem, both verdicts at the new point, the
class-four blindness of both dressings, the gauge audit, and the two wave-59 comparisons.

**MEASURED** (`scripts/w60_stage4/`, certified output in `results/`; `validate.txt` has 16 named
checks and 0 failures):

* the three emitted forms against honest `6 x 6` collection: `gaThreeHandle` at 1600 points,
  `gaThreeCore` at 1200, and the five-slot `gaThreeShift` at 1200, over `Z`, `Z/4`, `Z/8` and
  `Z/16` at handle counts `0` to `4`, with zero mismatches; and the `gamma_4` specialisation
  against `GradedFiveDefect.conFiveShift` at 300 more;
* that the class-four precedent's quadratic block is generically non-zero (400 of 400) and yet
  absent from the identity, which is what makes its vanishing a finding rather than a
  convention;
* **the census the exclusion is really about** (`results/witness_census.txt`): at the new point
  `gamma_3` of the image has order `8192`, and **0 of its 40960 single-slot dressings** kill the
  dressed frame, against wave 59's **1280 of 81920**; 4000 random five-slot achievable
  refinements kill nothing; and `24` of the `320` unrestricted `gamma_4`-shaped single-slot
  moves do kill, so achievability is load-bearing here too;
* that the `gamma_4`-shaped part of `gamma_3(im)` is `256` elements with **no odd** class-four
  coordinate, where wave 59's is the whole `512` with `256` odd;
* the search behind the point (`results/search_clean.txt`): `160` live class-five sigma points
  with both columns even, every one of them clean.  ⚠ This is a **confirmation of the chain, not
  evidence about its sharpness**: `forceLcs_two_le_stageN3` proves cleanness from the two
  hypotheses, so all 160 had to come out clean, and a live point violating them was not searched
  for.  What the run does establish is that the hypotheses are far from vacuous: live points
  satisfying them are common, one in roughly 430 random triples.

## Scope, honestly

* The exclusion is against `gamma_3`-dressings of all five slots.  **One filtration step wider
  again** - `gamma_2`-dressings, which disturb the class-three rows - is neither proved nor
  refuted here, and would need the `gamma_2`-level identity at class five.  That identity WILL
  carry a quadratic block: `[gamma_2, gamma_2] = gamma_4 <> 1` in the class-five carrier too.
* Like `GradedFour`, `GradedLift`, `GradedSigmaFour` and `GradedFiveForce`, this file works at
  the level of **marking tuples** in `SqU6 gr3R`: the hom layer of `GradedFive` is not consumed,
  so no statement here claims that a given tuple is the image of a continuous homomorphism on
  `D_sq h`.
* The soundness chain is **sufficient, not shown sharp**.  Wave 59's cross-lane finding was that
  the class-four soundness condition the campaign carries is strictly stronger than the sharp
  line; the same warning applies here and the sharp stage-four line is not computed.
* Nothing here retracts `GradedFiveForce`.  Its exclusion is true at its point with its
  quantifier, and its scope warning is true; `stage_vs_wave59_residues` checks the two points
  side by side.  What changes is that the campaign no longer has to carry the weaker statement.

## Contents

* **1** the `gamma_3`-calculus: `SqU6.IsGaThree` (`SqU6.IsGaFour` is `GradedFiveDefect`'s and is
  imported, not redefined), the pairing forms, the Fox letter, and ⭐ `SqU6.gaThree_comm`;
* **2** ⭐⭐ `SqU6.sqWord_mul_gaThree` and `SqU6.commP_mul_gaThree`, the core and handle shifts;
* **3** ⭐⭐ `sqRelWord_gaThreeDress`, the translation identity;
* **4** ⭐⭐ `gaThreeShiftO_even`, the evenness of the class-five row;
* **5** the witness point and its two verdicts; **6** the parity chain;
* **7** ⭐⭐⭐ the unconditional exclusion; **8** the wave-59 comparison; **9** axiom pins.

## Axiom hygiene

All **72** committed prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a
subset; no census axiom is reachable.  Every `decide` is on `ZMod 8` or on `Fin`-indexed tuples
over it; there is no `native_decide`.
-/

open Multiplicative

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The `gamma_3`-calculus on the class-five carrier -/

section GaThreeCalculus

variable {R : Type} [CommRing R]

/-- **A `gamma_3`-shaped element of the class-five carrier**: the nine coordinates of class
`<= 2` vanish, so `j`, `k`, `l`, `m`, `n` and `o` survive.  `SqU6.IsGaFour` (twelve vanishing
coordinates) is `GradedFiveDefect`'s and is imported, not redefined; there was no class-five
`gamma_3` predicate in the tree. -/
def SqU6.IsGaThree (z : SqU6 R) : Prop :=
  z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0 ∧ z.h = 0 ∧ z.i = 0

theorem SqU6.IsGaFour.isGaThree {z : SqU6 R} (hz : z.IsGaFour) : z.IsGaThree :=
  ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1, hz.2.2.2.2.2.2.1,
    hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.1⟩

@[simp] theorem SqU6.isGaThree_one : (1 : SqU6 R).IsGaThree :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The class-four LEFT pairing form**: the class-four commutator of a `gamma_3`-element
against a letter, `GradedGammaTwo.gaTwoPairL` one class up (`(e, f)` becomes `(j, k)` and the
letter's columns `(c, a)` become `(d, a)`). -/
def gaThreePairL (z L : SqU6 R) : R := z.j * L.d - z.k * L.a

/-- …and the RIGHT one, `gaTwoPairR` one class up. -/
def gaThreePairR (z L : SqU6 R) : R := z.k * L.e - z.l * L.b

/-- ⭐ **The class-five pairing form**: `GradedGammaTwo.gaTwoPair` one class up, under the
dictionary `(e, f, g, h, i) -> (j, k, l, m, n)` on the dressing and `(a, b, c, d, e, g) ->
(a, b, ., e, f, i)` on the letter.  Beyond the `gamma_4`-part `z.m * L.e - z.n * L.a` of the
committed `conFiveShift` it reads the dressing's class-three data against the letter's class-two
data and against products of its outer abelian columns. -/
def gaThreePair (z L : SqU6 R) : R :=
  z.m * L.e - z.n * L.a + z.j * L.i - z.l * L.f + z.l * (L.a * L.b) - z.k * (L.a * L.e)

/-- **The `x0`-slot Fox letter** `10 * x0 - sigma - 8 * x1`, columnwise: the same integer
combination the committed `conFiveShift` uses one filtration step up, and `GradedGammaTwo`'s
`sqFoxX` one class up. -/
def sqFoxX6 (s x y : SqU6 R) : SqU6 R :=
  ⟨10 * x.a - s.a - 8 * y.a, 10 * x.b - s.b - 8 * y.b, 10 * x.c - s.c - 8 * y.c,
    10 * x.d - s.d - 8 * y.d, 10 * x.e - s.e - 8 * y.e, 10 * x.f - s.f - 8 * y.f,
    10 * x.g - s.g - 8 * y.g, 10 * x.h - s.h - 8 * y.h, 10 * x.i - s.i - 8 * y.i,
    10 * x.j - s.j - 8 * y.j, 10 * x.k - s.k - 8 * y.k, 10 * x.l - s.l - 8 * y.l,
    10 * x.m - s.m - 8 * y.m, 10 * x.n - s.n - 8 * y.n, 10 * x.o - s.o - 8 * y.o⟩

@[simp] theorem sqFoxX6_a (s x y : SqU6 R) : (sqFoxX6 s x y).a = 10 * x.a - s.a - 8 * y.a := rfl

@[simp] theorem sqFoxX6_b (s x y : SqU6 R) : (sqFoxX6 s x y).b = 10 * x.b - s.b - 8 * y.b := rfl

@[simp] theorem sqFoxX6_d (s x y : SqU6 R) : (sqFoxX6 s x y).d = 10 * x.d - s.d - 8 * y.d := rfl

@[simp] theorem sqFoxX6_e (s x y : SqU6 R) : (sqFoxX6 s x y).e = 10 * x.e - s.e - 8 * y.e := rfl

@[simp] theorem sqFoxX6_f (s x y : SqU6 R) : (sqFoxX6 s x y).f = 10 * x.f - s.f - 8 * y.f := rfl

@[simp] theorem sqFoxX6_i (s x y : SqU6 R) : (sqFoxX6 s x y).i = 10 * x.i - s.i - 8 * y.i := rfl

/-- ⭐ **A `gamma_4`-shaped element commutes with anything whose two outermost abelian columns
vanish** - in particular with the handle word.  This is what lets the per-handle shifts collect
without a correction, and the class-five analogue of `GradedGammaTwo.mul_gaThree_swap`. -/
theorem SqU6.gaFour_comm {z b : SqU6 R} (hz : z.IsGaFour) (ha : b.a = 0) (he : b.e = 0) :
    z * b = b * z := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hz
  ext <;>
    simp only [SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f,
      SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m,
      SqU6.mul_n, SqU6.mul_o, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ha, he] <;>
    ring

/-- **Two `gamma_3`-elements commute**, because `[gamma_3, gamma_3] <= gamma_6 = 1` in a
carrier of class five.  ⭐ This is the one fact that makes the class-five stage-four identity
STRICTLY EASIER than its class-four model: at class four `[gamma_2, gamma_2] = gamma_4` is
non-trivial, and `GradedGammaTwo.gaTwo_swap` is where its quadratic block `gaTwoQuad` comes
from.  One class up there is no such block. -/
theorem SqU6.gaThree_comm {p q : SqU6 R} (hp : p.IsGaThree) (hq : q.IsGaThree) :
    p * q = q * p := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hp
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hq
  ext <;>
    simp only [SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f,
      SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m,
      SqU6.mul_n, SqU6.mul_o, p1, p2, p3, p4, p5, p6, p7, p8, p9,
      q1, q2, q3, q4, q5, q6, q7, q8, q9] <;>
    ring

/-- Two `gamma_3`-shaped elements multiply coordinatewise. -/
theorem SqU6.gaThree_mul {p q : SqU6 R} (hp : p.IsGaThree) (hq : q.IsGaThree) :
    p * q = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, p.j + q.j, p.k + q.k, p.l + q.l, p.m + q.m,
      p.n + q.n, p.o + q.o⟩ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hp
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hq
  ext <;>
    simp only [SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f,
      SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m,
      SqU6.mul_n, SqU6.mul_o, p1, p2, p3, p4, p5, p6, p7, p8, p9,
      q1, q2, q3, q4, q5, q6, q7, q8, q9] <;>
    ring

end GaThreeCalculus

/-! ## 2 The core word and the handle block under a `gamma_3`-dressing -/

section DressAction

variable {R : Type} [CommRing R]

/-- ⭐⭐ **The correction block** of the class-five stage-four shift: the part of the defect
reading the dressings' class-three data against products of the frame's own abelian columns,
beyond the graded Fox pairing.  It is `GradedGammaTwo.gaTwoCorr` transposed **verbatim**, all
nine blocks and all forty-four coefficients, under the dictionary of `gaThreePair`
(`scripts/w60_stage4/results/derive.txt` section 3c). -/
def gaThreeCorr (s x y z₀ z₁ z₂ : SqU6 R) : R :=
  z₀.j * (-(s.d * x.e) + s.e * x.d - 4 * (x.d * x.e) + 2 * (x.d * y.e) + y.d * y.e)
    + z₀.k * (8 * (x.a * x.e) - 2 * (x.a * y.e) - 2 * (x.e * y.a) - 2 * (y.a * y.e))
    + z₀.l * (s.a * x.b - s.b * x.a - 4 * (x.a * x.b) + 2 * (x.b * y.a) + y.a * y.b)
    + z₁.j * (3 * (s.d * x.e) - 2 * (s.d * y.e) + s.e * x.d - 20 * (x.d * x.e)
        + 20 * (x.d * y.e) - 4 * (y.d * y.e))
    + z₁.k * (2 * (s.a * s.e) - 14 * (s.a * x.e) + 10 * (s.a * y.e) - 14 * (s.e * x.a)
        + 10 * (s.e * y.a) + 130 * (x.a * x.e) - 100 * (x.a * y.e) - 100 * (x.e * y.a)
        + 80 * (y.a * y.e))
    + z₁.l * (-2 * (s.a * s.b) + 11 * (s.a * x.b) - 8 * (s.a * y.b) + 13 * (s.b * x.a)
        - 10 * (s.b * y.a) - 110 * (x.a * x.b) + 80 * (x.a * y.b) + 100 * (x.b * y.a)
        - 76 * (y.a * y.b))
    + z₂.j * (-2 * (s.d * y.e) + s.e * y.d)
    + z₂.k * (s.a * y.e + s.e * y.a)
    + z₂.l * (s.a * y.b - 2 * (s.b * y.a))

/-- **The core shift**: the `gamma_3`-element by which the core word moves under a three-slot
`gamma_3`-dressing.  Class-three rows: the Frobenius weights `(-4, 2)` on the exponent slots
alone.  Class-four rows: the Frobenius weights plus the class-four graded Fox pairings against
the permuted letters `(x0, 10 x0 - sigma - 8 x1, x1)`.  Class-five row: the Frobenius weight,
the class-five Fox pairings and the correction.  ⭐⭐ **There is no quadratic block**: the
object `GradedGammaTwo.gaTwoQuad` that the class-four transport had to carry is identically
zero one class up. -/
def gaThreeCore (s x y z₀ z₁ z₂ : SqU6 R) : SqU6 R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0,
    -4 * z₁.j + 2 * z₂.j,
    -4 * z₁.k + 2 * z₂.k,
    -4 * z₁.l + 2 * z₂.l,
    -4 * z₁.m + 2 * z₂.m
      + (gaThreePairL z₀ x + gaThreePairL z₁ (sqFoxX6 s x y) + gaThreePairL z₂ y),
    -4 * z₁.n + 2 * z₂.n
      + (gaThreePairR z₀ x + gaThreePairR z₁ (sqFoxX6 s x y) + gaThreePairR z₂ y),
    -4 * z₁.o + 2 * z₂.o
      + (gaThreePair z₀ x + gaThreePair z₁ (sqFoxX6 s x y) + gaThreePair z₂ y)
      + gaThreeCorr s x y z₀ z₁ z₂⟩

theorem gaThreeCore_isGaThree (s x y z₀ z₁ z₂ : SqU6 R) :
    (gaThreeCore s x y z₀ z₁ z₂).IsGaThree := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem gaThreeCore_j (s x y z₀ z₁ z₂ : SqU6 R) :
    (gaThreeCore s x y z₀ z₁ z₂).j = -4 * z₁.j + 2 * z₂.j := rfl

@[simp] theorem gaThreeCore_l (s x y z₀ z₁ z₂ : SqU6 R) :
    (gaThreeCore s x y z₀ z₁ z₂).l = -4 * z₁.l + 2 * z₂.l := rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 40000 in
/-- ⭐⭐ **The core word under `gamma_3`-dressings of its three slots.**  No closed form of the
word is consumed: componentwise expansion, exactly as `GradedGammaTwo.sqWord_mul_gaTwo` one
class down and `GradedFiveDefect.SqU6.sqWord_mul_gaFour` one filtration step narrower. -/
theorem SqU6.sqWord_mul_gaThree {z₀ z₁ z₂ : SqU6 R} (s x y : SqU6 R) (h₀ : z₀.IsGaThree)
    (h₁ : z₁.IsGaThree) (h₂ : z₂.IsGaThree) :
    sqWord (s * z₀) (x * z₁) (y * z₂) = sqWord s x y * gaThreeCore s x y z₀ z₁ z₂ := by
  obtain ⟨a0, b0, c0, d0, e0, f0, g0, hh0, i0⟩ := h₀
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, hh1, i1⟩ := h₁
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, hh2, i2⟩ := h₂
  ext <;>
    simp only [gaThreeCore, gaThreePair, gaThreePairL, gaThreePairR, gaThreeCorr, sqFoxX6,
      sqWord, conjP, commP, pow_succ, pow_zero, one_mul,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
      SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
      SqU6.inv_n, SqU6.inv_o,
      a0, b0, c0, d0, e0, f0, g0, hh0, i0, a1, b1, c1, d1, e1, f1, g1, hh1, i1,
      a2, b2, c2, d2, e2, f2, g2, hh2, i2] <;>
    ring

/-- **The handle shift**: the `gamma_4`-element by which one handle commutator moves under a
`gamma_3`-dressing of both its slots.  `GradedGammaTwo.gaTwoHandle` one class up, **minus its
quadratic term** `z.e * w.g - z.g * w.e`, which is the class-four commutator of the two
dressings and is zero one class up. -/
def gaThreeHandle (p q z w : SqU6 R) : SqU6 R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    gaThreePairL z q - gaThreePairL w p,
    gaThreePairR z q - gaThreePairR w p,
    gaThreePair z q - gaThreePair w p
      - (p.d * q.e - p.e * q.d) * (z.j + w.j) + (p.a * q.b - p.b * q.a) * (z.l + w.l)⟩

theorem gaThreeHandle_isGaFour (p q z w : SqU6 R) : (gaThreeHandle p q z w).IsGaFour :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⭐ **Dressing both arguments of a commutator by `gamma_3`-elements** moves it by the handle
shift.  Unlike the committed `gamma_4`-version the translation is not central: the commutator's
two class-four rows move as well. -/
theorem SqU6.commP_mul_gaThree {z w : SqU6 R} (p q : SqU6 R) (hz : z.IsGaThree) (hw : w.IsGaThree) :
    commP (p * z) (q * w) = commP p q * gaThreeHandle p q z w := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := hz
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hw
  ext <;>
    simp only [gaThreeHandle, gaThreePair, gaThreePairL, gaThreePairR, commP,
      SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
      SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
      SqU6.inv_n, SqU6.inv_o, z1, z2, z3, z4, z5, z6, z7, z8, z9,
      w1, w2, w3, w4, w5, w6, w7, w8, w9] <;>
    ring

/-- ⭐ **The handle block under an all-pair `gamma_3`-dressing**: the handle word moves by the
`gamma_4`-element summing the per-pair handle shifts.  The cross-handle coupling of the
class-five row does **not** move, because it reads only the commutators' class-`<= 3` rows,
which a `gamma_3`-dressing leaves alone. -/
theorem SqU6.handleWord_mul_gaThree_all : ∀ (n : ℕ) (u v zu zv : Fin n → SqU6 R),
    (∀ k, (zu k).IsGaThree) → (∀ k, (zv k).IsGaThree) →
    handleWord (fun k => u k * zu k) (fun k => v k * zv k)
      = handleWord u v
        * ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ∑ k : Fin n, (gaThreeHandle (u k) (v k) (zu k) (zv k)).m,
            ∑ k : Fin n, (gaThreeHandle (u k) (v k) (zu k) (zv k)).n,
            ∑ k : Fin n, (gaThreeHandle (u k) (v k) (zu k) (zv k)).o⟩
  | 0, u, v, zu, zv, _, _ => by
    simp only [handleWord_zero]
    ext <;> simp
  | n + 1, u, v, zu, zv, hzu, hzv => by
    have htail := SqU6.handleWord_mul_gaThree_all n (fun k => u k.succ) (fun k => v k.succ)
      (fun k => zu k.succ) (fun k => zv k.succ) (fun k => hzu _) (fun k => hzv _)
    rw [handleWord_succ, handleWord_succ, htail,
      SqU6.commP_mul_gaThree (u 0) (v 0) (hzu 0) (hzv 0)]
    rw [mul_assoc, ← mul_assoc (gaThreeHandle (u 0) (v 0) (zu 0) (zv 0)),
      SqU6.gaFour_comm (gaThreeHandle_isGaFour _ _ _ _)
        (SqU6.handleWord_a _ _) (SqU6.handleWord_e _ _),
      mul_assoc, ← mul_assoc]
    refine congrArg (fun t => commP (u 0) (v 0)
      * handleWord (fun k => u k.succ) (fun k => v k.succ) * t) ?_
    ext <;>
      simp only [gaThreeHandle, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e,
        SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l,
        SqU6.mul_m, SqU6.mul_n, SqU6.mul_o, Fin.sum_univ_succ] <;>
      ring

end DressAction

/-! ## 3 The five-slot `gamma_3`-dressing and the translation identity -/

section Transport

variable {R : Type} [CommRing R] {h : ℕ}

variable (h) in
/-- ⭐⭐ **The stage-four shift of the relator**: the core shift, times the summed handle
shifts, times the central collection term by which the core shift's class-three rows commute
past the handle word.  The last factor is even (the Frobenius weights are) and vanishes as soon
as the exponent slots are dressed by `gamma_4`.  `GradedGammaTwo.gaTwoShift` one class up. -/
def gaThreeShift (m z : Fin (sqRank h) → SqU6 R) : SqU6 R :=
  gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)
    * ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
          (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).m,
        ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
          (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).n,
        ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
          (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).o⟩
    * SqU6.liftO (sqU6BlockI (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
          * (-4 * (z 1).j + 2 * (z 2).j)
        - sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
          * (-4 * (z 1).l + 2 * (z 2).l))

variable {m z : Fin (sqRank h) → SqU6 R}

/-- The collection identity: a `gamma_3`-shaped element moves past a word with vanishing
abelian columns at the cost of one central factor, pairing the element's outer class-three
rows against the word's outer class-two rows. -/
private theorem gaThree_past {c b : SqU6 R} (hc : c.IsGaThree) (ha : b.a = 0) (hb : b.b = 0)
    (hcc : b.c = 0) (hd : b.d = 0) (he : b.e = 0) :
    c * b = b * c * SqU6.liftO (b.i * c.j - b.f * c.l) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
  ext <;>
    simp only [SqU6.liftO, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e,
      SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l,
      SqU6.mul_m, SqU6.mul_n, SqU6.mul_o, c1, c2, c3, c4, c5, c6, c7, c8, c9,
      ha, hb, hcc, hd, he] <;>
    ring

/-- ⭐⭐ **THE STAGE-FOUR TRANSLATION IDENTITY AT CLASS FIVE.**  A five-slot `gamma_3`-dressing
moves the relator by the explicit `gamma_3`-element `gaThreeShift`, at every handle count and
over any commutative ring.  This is the object `GradedFiveDefect` deferred ("the `gamma_3`- and
`gamma_2`-level transports at class five, whose defect shifts are quadratic and not covered by
the affine calculus here") and `GradedFiveForce` needed ("proving or refuting the forcing
against `gamma_3`-dressings in general needs the `gamma_3`-level translation identity, which
this file does not build").

⭐ **The deferral's stated reason does not survive**: the shift is **affine** in the dressings,
not quadratic.  The class-four transport's quadratic block comes from `[gamma_2, gamma_2] =
gamma_4 <> 1`, and one class up `[gamma_3, gamma_3] <= gamma_6 = 1`. -/
theorem sqRelWord_gaThreeDress (hz : ∀ i, (z i).IsGaThree) :
    sqRelWord (conFiveDress m z) = sqRelWord m * gaThreeShift h m z := by
  have hhand := SqU6.handleWord_mul_gaThree_all h (fun k => m (sqHandleIdxU k))
    (fun k => m (sqHandleIdxV k)) (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))
    (fun k => hz _) (fun k => hz _)
  have hpast := gaThree_past (c := gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2))
    (b := handleWord (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)))
    (gaThreeCore_isGaThree _ _ _ _ _ _) (SqU6.handleWord_a _ _) (SqU6.handleWord_b _ _)
    (SqU6.handleWord_c _ _) (SqU6.handleWord_d _ _) (SqU6.handleWord_e _ _)
  rw [SqU6.handleWord_blockI, SqU6.handleWord_f, gaThreeCore_j, gaThreeCore_l] at hpast
  rw [sqRelWord, sqRelWord]
  simp only [conFiveDress_apply]
  rw [SqU6.sqWord_mul_gaThree (m 0) (m 1) (m 2) (hz 0) (hz 1) (hz 2), hhand, gaThreeShift,
    mul_assoc (sqWord (m 0) (m 1) (m 2)) (gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)),
    ← mul_assoc (gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)), hpast]
  simp only [mul_assoc]
  rw [SqU6.liftO_comm]

end Transport

/-! ## 4 Evenness of the stage-four shift's class-five row -/

section Evenness

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐ **The class-five pairing form is even** as soon as the dressing's `j`, `l` and `m` are
even and the letter's first abelian column is.  The `n`-channel is closed by the letter, the
`k`-channel by the letter squared, the other three by the dressing: that is the whole
arithmetic of the stage-four exclusion. -/
theorem gaThreePair_even {z L : SqU6 R} (hj : (2 : R) ∣ z.j) (hl : (2 : R) ∣ z.l)
    (hm : (2 : R) ∣ z.m) (ha : (2 : R) ∣ L.a) : (2 : R) ∣ gaThreePair z L := by
  obtain ⟨j', hj⟩ := hj
  obtain ⟨l', hl⟩ := hl
  obtain ⟨m', hm⟩ := hm
  obtain ⟨a', ha⟩ := ha
  exact ⟨m' * L.e - z.n * a' + j' * L.i - l' * L.f + 2 * (l' * (a' * L.b)) - z.k * (a' * L.e),
    by rw [gaThreePair, hj, hl, hm, ha]; ring⟩

/-- …and so is the correction block.  Six of its nine coefficient blocks are killed by the
dressing's even `j` and `l`; the `z₀.k` and `z₁.k` blocks have even coefficients outright; and
the `z₂.k` block, `s.a * y.e + s.e * y.a`, is killed by the frame's even first columns. -/
theorem gaThreeCorr_even {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hxa : (2 : R) ∣ x.a) (hya : (2 : R) ∣ y.a)
    (h0j : (2 : R) ∣ z₀.j) (h0l : (2 : R) ∣ z₀.l) (h1j : (2 : R) ∣ z₁.j) (h1l : (2 : R) ∣ z₁.l)
    (h2j : (2 : R) ∣ z₂.j) (h2l : (2 : R) ∣ z₂.l) :
    (2 : R) ∣ gaThreeCorr s x y z₀ z₁ z₂ := by
  obtain ⟨sa, hsa⟩ := hsa
  obtain ⟨xa, hxa⟩ := hxa
  obtain ⟨ya, hya⟩ := hya
  obtain ⟨j0, h0j⟩ := h0j
  obtain ⟨l0, h0l⟩ := h0l
  obtain ⟨j1, h1j⟩ := h1j
  obtain ⟨l1, h1l⟩ := h1l
  obtain ⟨j2, h2j⟩ := h2j
  obtain ⟨l2, h2l⟩ := h2l
  refine ⟨j0 * (-(s.d * x.e) + s.e * x.d - 4 * (x.d * x.e) + 2 * (x.d * y.e) + y.d * y.e)
      + z₀.k * (8 * (xa * x.e) - x.a * y.e - x.e * y.a - y.a * y.e)
      + l0 * (s.a * x.b - s.b * x.a - 4 * (x.a * x.b) + 2 * (x.b * y.a) + y.a * y.b)
      + j1 * (3 * (s.d * x.e) - 2 * (s.d * y.e) + s.e * x.d - 20 * (x.d * x.e)
        + 20 * (x.d * y.e) - 4 * (y.d * y.e))
      + z₁.k * (s.a * s.e - 7 * (s.a * x.e) + 5 * (s.a * y.e) - 7 * (s.e * x.a)
        + 5 * (s.e * y.a) + 65 * (x.a * x.e) - 50 * (x.a * y.e) - 50 * (x.e * y.a)
        + 40 * (y.a * y.e))
      + l1 * (-2 * (s.a * s.b) + 11 * (s.a * x.b) - 8 * (s.a * y.b) + 13 * (s.b * x.a)
        - 10 * (s.b * y.a) - 110 * (x.a * x.b) + 80 * (x.a * y.b) + 100 * (x.b * y.a)
        - 76 * (y.a * y.b))
      + j2 * (-2 * (s.d * y.e) + s.e * y.d)
      + z₂.k * (sa * y.e + s.e * ya)
      + l2 * (s.a * y.b - 2 * (s.b * y.a)), ?_⟩
  rw [gaThreeCorr, h0j, h0l, h1j, h1l, h2j, h2l]
  rw [show s.a = 2 * sa from hsa, show x.a = 2 * xa from hxa, show y.a = 2 * ya from hya]
  ring

/-- ⭐ **The core shift's class-five row is even** under the two frame hypotheses and the
dressing hypotheses.  Every one of its four blocks is: the Frobenius weights `(-4, 2)` are
even, the three Fox pairings are `gaThreePair_even`, and the correction is
`gaThreeCorr_even`. -/
theorem gaThreeCore_o_even {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hxa : (2 : R) ∣ x.a) (hya : (2 : R) ∣ y.a)
    (h0 : (2 : R) ∣ z₀.j ∧ (2 : R) ∣ z₀.l ∧ (2 : R) ∣ z₀.m)
    (h1 : (2 : R) ∣ z₁.j ∧ (2 : R) ∣ z₁.l ∧ (2 : R) ∣ z₁.m)
    (h2 : (2 : R) ∣ z₂.j ∧ (2 : R) ∣ z₂.l ∧ (2 : R) ∣ z₂.m) :
    (2 : R) ∣ (gaThreeCore s x y z₀ z₁ z₂).o := by
  have hfox : (2 : R) ∣ (sqFoxX6 s x y).a := by
    rw [sqFoxX6_a]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxa 10) hsa) (Dvd.dvd.mul_left hya 8)
  have hfrob : (2 : R) ∣ (-4 * z₁.o + 2 * z₂.o) :=
    ⟨-2 * z₁.o + z₂.o, by ring⟩
  refine dvd_add (dvd_add hfrob (dvd_add (dvd_add ?_ ?_) ?_))
    (gaThreeCorr_even hsa hxa hya h0.1 h0.2.1 h1.1 h1.2.1 h2.1 h2.2.1)
  · exact gaThreePair_even h0.1 h0.2.1 h0.2.2 hxa
  · exact gaThreePair_even h1.1 h1.2.1 h1.2.2 hfox
  · exact gaThreePair_even h2.1 h2.2.1 h2.2.2 hya

/-- ⭐ **…and so is each handle shift's class-five row**: two Fox pairings and two blocks
carrying the dressings' even `j` and `l`. -/
theorem gaThreeHandle_o_even {p q z w : SqU6 R} (hpa : (2 : R) ∣ p.a) (hqa : (2 : R) ∣ q.a)
    (hz : (2 : R) ∣ z.j ∧ (2 : R) ∣ z.l ∧ (2 : R) ∣ z.m)
    (hw : (2 : R) ∣ w.j ∧ (2 : R) ∣ w.l ∧ (2 : R) ∣ w.m) :
    (2 : R) ∣ (gaThreeHandle p q z w).o := by
  refine dvd_add (dvd_sub (dvd_sub (gaThreePair_even hz.1 hz.2.1 hz.2.2 hqa)
    (gaThreePair_even hw.1 hw.2.1 hw.2.2 hpa)) ?_) ?_
  · exact Dvd.dvd.mul_left (dvd_add hz.1 hw.1) _
  · exact Dvd.dvd.mul_left (dvd_add hz.2.1 hw.2.1) _

variable (h) in
/-- The class-five row of `gaThreeShift`, unpacked from the three-factor product. -/
def gaThreeShiftO (m z : Fin (sqRank h) → SqU6 R) : R :=
  (gaThreeCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).o
    + ∑ k : Fin h, (gaThreeHandle (m (sqHandleIdxU k)) (m (sqHandleIdxV k))
        (z (sqHandleIdxU k)) (z (sqHandleIdxV k))).o
    + (sqU6BlockI (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        * (-4 * (z 1).j + 2 * (z 2).j)
      - sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
        * (-4 * (z 1).l + 2 * (z 2).l))

theorem gaThreeShift_o (m z : Fin (sqRank h) → SqU6 R) :
    (gaThreeShift h m z).o = gaThreeShiftO h m z := by
  simp only [gaThreeShift, gaThreeShiftO, SqU6.mul_o, SqU6.mul_a, SqU6.mul_f, SqU6.mul_j,
    SqU6.mul_m, SqU6.liftO, gaThreeCore]
  ring

/-- The shift's class-three right row: the Frobenius weights alone, hence even. -/
theorem gaThreeShift_l (m z : Fin (sqRank h) → SqU6 R) :
    (gaThreeShift h m z).l = -4 * (z 1).l + 2 * (z 2).l := by
  simp only [gaThreeShift, SqU6.mul_l, SqU6.mul_c, SqU6.mul_h, SqU6.liftO, gaThreeCore]
  ring

/-- The stage-four shift is itself `gamma_3`-shaped, being a product of three such. -/
theorem gaThreeShift_isGaThree {m z : Fin (sqRank h) → SqU6 R} :
    (gaThreeShift h m z).IsGaThree := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gaThreeShift, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e,
      SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.liftO, gaThreeCore] <;>
    ring

/-- ⭐⭐ **THE STAGE-FOUR SOUNDNESS.**  At any marking all of whose slots have an even
`(1,2)`-column, every five-slot `gamma_3`-dressing whose slots have even `j`, `l` and `m`
moves the relator's class-five row by an **even** amount.  This is the stage-four analogue of
`GradedFiveForce.forceLcs_three_le_forceN4`'s consequence, one filtration step wider, and it is
what turns the class-five exclusion from a stage-five statement into an unconditional one. -/
theorem gaThreeShiftO_even {m z : Fin (sqRank h) → SqU6 R}
    (ha : ∀ i, (2 : R) ∣ (m i).a)
    (hz : ∀ i, (2 : R) ∣ (z i).j ∧ (2 : R) ∣ (z i).l ∧ (2 : R) ∣ (z i).m) :
    (2 : R) ∣ gaThreeShiftO h m z := by
  refine dvd_add (dvd_add (gaThreeCore_o_even (ha 0) (ha 1) (ha 2) (hz 0) (hz 1) (hz 2)) ?_)
    (dvd_sub (Dvd.dvd.mul_left ⟨-2 * (z 1).j + (z 2).j, by ring⟩ _)
      (Dvd.dvd.mul_left ⟨-2 * (z 1).l + (z 2).l, by ring⟩ _))
  exact Finset.dvd_sum fun k _ =>
    gaThreeHandle_o_even (ha _) (ha _) (hz _) (hz _)

end Evenness

/-! ## 5 The stage-four witness point -/

section Point

/-- The `x0`-slot of the stage-four witness: `<a=2, e=5>`.  Same gauge shape as wave 59's
`forceX` - the `(1,2)`-column even, the fifth abelian column odd, every other gauge column
zero - and the odd fifth column is again the channel the residue runs on. -/
def stageX : SqU6 gr3R := ⟨2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x1`-slot: `<e=2, f=1, g=1, h=1, m=3, n=3>`, the layered solve of the fifteen rows
against the live block.  Its class-two coordinates `f` and `h` are odd, which is what makes the
`a0 = a1` residue odd on the gauge. -/
def stageY : SqU6 gr3R := ⟨0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 3, 3, 0⟩

/-- The `U`-letter: `<a=6, b=7, c=4, d=1, e=3, g=5, h=5>`.  ⚠ Its `(1,2)`-column is **even**,
and that single difference from wave 59's `forceU` (whose `a` is `1`) is the whole of this
file's improvement: `[[sigma, U], x1]` there is `gamma_4`-shaped with the odd class-four
coordinate `5`, and here the same commutator is even. -/
def stageU : SqU6 gr3R := ⟨6, 7, 4, 1, 3, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `V`-letter: `<a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4>`.  Its commutator with
`stageU` is the handle block, live, and live in the class-four row. -/
def stageV : SqU6 gr3R := ⟨6, 7, 6, 1, 3, 5, 3, 3, 4, 0, 0, 0, 0, 0, 0⟩

/-- **The stage-four class-five sigma-witness binder point**, at every handle count and every
handle, with the sigma slot dressed by `v`. -/
def stageWit (h : ℕ) (j : Fin h) (v : SqU6 gr3R) : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j (fiveSigMark gr3R * v) stageX stageY stageU stageV

/-- ⭐⭐ **The undressed frame kills the relator outright**, at every handle count and every
handle. -/
theorem sqRelWord_stageWit_triv (h : ℕ) (j : Fin h) : sqRelWord (stageWit h j 1) = 1 := by
  rw [stageWit, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐ **The `a0 = a1` dressing leaves the ODD class-five residue `1`**, at every handle count
and every handle: the fourteen lower rows die and the top row does not. -/
theorem sqRelWord_stageWit_diag (h : ℕ) (j : Fin h) :
    sqRelWord (stageWit h j stageX) = SqU6.liftO 1 := by
  rw [stageWit, sqRelWord_fiveTuple]
  decide

/-- ⭐ **The point's frame hypotheses**: every letter has an even `(1,2)`-column and an even
`(3,4)`-column.  Wave 59's point satisfies only the second. -/
theorem stage_letters_even :
    (stageX.a = 2 * 1 ∧ stageX.c = 2 * 0) ∧ (stageY.a = 2 * 0 ∧ stageY.c = 2 * 0)
      ∧ (stageU.a = 2 * 3 ∧ stageU.c = 2 * 2) ∧ (stageV.a = 2 * 3 ∧ stageV.c = 2 * 3)
      ∧ ((fiveSigMark gr3R).a = 2 * 0 ∧ (fiveSigMark gr3R).c = 2 * 0) := by decide

/-- ⭐ **The point sits on the committed class-two-forced gauge**, exactly as wave 59's does,
with the same single datum escaping it: the `x0`-slot's fifth abelian column is odd. -/
theorem stageX_gauge :
    stageX.a = 2 * 1 ∧ stageX.c = 2 * 0 ∧ stageX.d = 2 * 0 ∧ stageX.f = 2 * 0
      ∧ stageX.g = 2 * 0 ∧ stageY.a = 2 * 0 ∧ stageY.c = 2 * 0 ∧ stageY.d = 2 * 0
      ∧ stageX.b = 0 ∧ selPar stageX.e = 1 := by decide

/-- The handle block of the point is **live**, and live in the class-four row `x_{15}`. -/
theorem commP_stageUV_live : commP stageU stageV ≠ 1 ∧ selPar (commP stageU stageV).m = 1 := by
  refine ⟨?_, by decide⟩
  decide

/-- ⭐⭐ **The whole committed class-`<= 4` machinery cannot separate the two dressings**: both
`U_5`-quotients kill the class-four relator at both dressings, so the separation is purely
class five, exactly as at wave 59's point. -/
theorem stageWit_class_four_blind (h : ℕ) (j : Fin h) :
    (sqRelWord (fun i => SqU6.toU5L (stageWit h j 1 i)) = 1
        ∧ sqRelWord (fun i => SqU6.toU5R (stageWit h j 1 i)) = 1)
      ∧ (sqRelWord (fun i => SqU6.toU5L (stageWit h j stageX i)) = 1
        ∧ sqRelWord (fun i => SqU6.toU5R (stageWit h j stageX i)) = 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_stageWit_triv, map_one]
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_stageWit_triv, map_one]
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_stageWit_diag]
    decide
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_stageWit_diag]
    decide

/-- ⭐ **Wave 58's measured closed form, checked at the new point.**  The class-five response of
the `a0 = a1` dressing is `x_{12} y_{24} y_{46} + x_{56} y_{13} y_{35}` (mod 2); here the two
terms are `2 * 1 * 0` and `5 * 1 * 1`, so the escape again runs entirely on the channel carried
by the `x0`-slot's fifth abelian column. -/
theorem stageWit_w58_form_crosscheck (h : ℕ) (j : Fin h) :
    selPar (stageX.a * stageY.g * stageY.i + stageX.e * stageY.f * stageY.h)
      = selPar (sqRelWord (stageWit h j stageX)).o := by
  rw [sqRelWord_stageWit_diag]
  decide

end Point

/-! ## 6 The parity chain, and the unconditional exclusion -/

section Chain

/-- **`M_1`**: an even `(1,2)`-column and an even `(3,4)`-column.  Every letter of the new point
lies here; wave 59's `forceN1` asks only for the second, and its point fails the first. -/
def stageN1 : Subgroup (SqU6 gr3R) where
  carrier := {z | (2 : gr3R) ∣ z.a ∧ (2 : gr3R) ∣ z.c}
  mul_mem' := by
    rintro p q ⟨ha, hc⟩ ⟨ha', hc'⟩
    exact ⟨by rw [SqU6.mul_a]; exact dvd_add ha ha',
      by rw [SqU6.mul_c]; exact dvd_add hc hc'⟩
  one_mem' := ⟨by rw [SqU6.one_a]; exact dvd_zero _, by rw [SqU6.one_c]; exact dvd_zero _⟩
  inv_mem' := by
    rintro p ⟨ha, hc⟩
    exact ⟨by rw [SqU6.inv_a]; exact ha.neg_right, by rw [SqU6.inv_c]; exact hc.neg_right⟩

/-- **`M_2`**: a `gamma_2`-element with `f`, `h` and `j` even. -/
def stageN2 : Subgroup (SqU6 gr3R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0
    ∧ (2 : gr3R) ∣ z.f ∧ (2 : gr3R) ∣ z.h ∧ (2 : gr3R) ∣ z.j}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, ph, pj⟩ ⟨qa, qb, qc, qd, qe, qf, qh, qj⟩
    refine ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, ?_, ?_, ?_⟩
    · rw [SqU6.mul_f, pa, zero_mul, add_zero]; exact dvd_add pf qf
    · rw [SqU6.mul_h, pc, zero_mul, add_zero]; exact dvd_add ph qh
    · rw [SqU6.mul_j, pa, zero_mul, add_zero, qc, mul_zero, add_zero]; exact dvd_add pj qj
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, by rw [SqU6.one_f]; exact dvd_zero _,
    by rw [SqU6.one_h]; exact dvd_zero _, by rw [SqU6.one_j]; exact dvd_zero _⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, ph, pj⟩
    refine ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, ?_, ?_, ?_⟩
    · rw [SqU6.inv_f, pa, zero_mul, zero_sub]; exact pf.neg_right
    · rw [SqU6.inv_h, pc, zero_mul, zero_sub]; exact ph.neg_right
    · rw [SqU6.inv_j, pa, pb, pc]; simpa using pj.neg_right

/-- **`M_3`**: a `gamma_3`-element with `j`, `l` and `m` even.  ⭐ This is the lattice the
stage-four exclusion reads, and `gaThreeShiftO_even` is why exactly these three coordinates
appear: the `n`-channel and the `k`-channel are closed by the frame, the other three by the
dressing. -/
def stageN3 : Subgroup (SqU6 gr3R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
    ∧ z.h = 0 ∧ z.i = 0 ∧ (2 : gr3R) ∣ z.j ∧ (2 : gr3R) ∣ z.l ∧ (2 : gr3R) ∣ z.m}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pl, pm⟩
      ⟨qa, qb, qc, qd, qe, qf, qg, qh, qi, qj, ql, qm⟩
    refine ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, by rw [SqU6.mul_f, pf, qf, pa]; ring,
      by rw [SqU6.mul_g, pg, qg, pb]; ring, by rw [SqU6.mul_h, ph, qh, pc]; ring,
      by rw [SqU6.mul_i, pi, qi, pd]; ring, ?_, ?_, ?_⟩
    · rw [SqU6.mul_j, pa, zero_mul, add_zero, pf, zero_mul, add_zero]; exact dvd_add pj qj
    · rw [SqU6.mul_l, pc, zero_mul, add_zero, ph, zero_mul, add_zero]; exact dvd_add pl ql
    · rw [SqU6.mul_m, pa, zero_mul, add_zero, pf, zero_mul, add_zero, qd, mul_zero, add_zero]
      exact dvd_add pm qm
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by rw [SqU6.one_j]; exact dvd_zero _,
    by rw [SqU6.one_l]; exact dvd_zero _, by rw [SqU6.one_m]; exact dvd_zero _⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pl, pm⟩
    refine ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, by rw [SqU6.inv_f, pf, pa, pb]; ring,
      by rw [SqU6.inv_g, pg, pb, pc]; ring, by rw [SqU6.inv_h, ph, pc, pd]; ring,
      by rw [SqU6.inv_i, pi, pd, pe]; ring, ?_, ?_, ?_⟩
    · rw [SqU6.inv_j, pa, pb, pc, pf, pg]; simpa using pj.neg_right
    · rw [SqU6.inv_l, pc, pd, pe, ph, pi]; simpa using pl.neg_right
    · rw [SqU6.inv_m, pa, pb, pc, pd, pf, pg, ph]; simpa using pm.neg_right

theorem mem_stageN1 {z : SqU6 gr3R} : z ∈ stageN1 ↔ (2 : gr3R) ∣ z.a ∧ (2 : gr3R) ∣ z.c :=
  Iff.rfl

theorem mem_stageN2 {z : SqU6 gr3R} :
    z ∈ stageN2 ↔ z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0
      ∧ (2 : gr3R) ∣ z.f ∧ (2 : gr3R) ∣ z.h ∧ (2 : gr3R) ∣ z.j := Iff.rfl

theorem mem_stageN3 {z : SqU6 gr3R} :
    z ∈ stageN3 ↔ z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
      ∧ z.h = 0 ∧ z.i = 0 ∧ (2 : gr3R) ∣ z.j ∧ (2 : gr3R) ∣ z.l ∧ (2 : gr3R) ∣ z.m :=
  Iff.rfl

/-- Every element of `M_3` is `gamma_3`-shaped, so the stage-four identity applies to it. -/
theorem stageN3_isGaThree {z : SqU6 gr3R} (hz : z ∈ stageN3) : z.IsGaThree :=
  ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1, hz.2.2.2.2.2.2.1,
    hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.1⟩

/-- …and its three load-bearing coordinates are even. -/
theorem stageN3_even {z : SqU6 gr3R} (hz : z ∈ stageN3) :
    (2 : gr3R) ∣ z.j ∧ (2 : gr3R) ∣ z.l ∧ (2 : gr3R) ∣ z.m :=
  ⟨hz.2.2.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.2.2.2⟩

/-- ⭐ **Step one**: a commutator of two elements with even `(1,2)`- and `(3,4)`-columns is a
`gamma_2`-element with `f`, `h` and `j` even.  `f` is the `(a, b)`-pairing and `h` the
`(c, d)`-pairing, each meeting an even column; `j` is `u6Comm3L`, whose every monomial contains
one of `p.a`, `p.c`, `q.a`, `q.c`. -/
theorem stageN2_of_commutator {p q : SqU6 gr3R} (hp : p ∈ stageN1) (hq : q ∈ stageN1) :
    ⁅p, q⁆ ∈ stageN2 := by
  obtain ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩⟩ := mem_stageN1.mp hp
  obtain ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩ := mem_stageN1.mp hq
  rw [commutatorElement_eq_commP, mem_stageN2]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ⟨s₁ * q.b - p.b * t₁, ?_⟩, ⟨s₂ * q.d - p.d * t₂, ?_⟩,
    ⟨s₁ * q.g - p.g * t₁ - s₂ * q.f + t₂ * p.f
      - 2 * (s₁ * (q.b * t₂)) - 2 * (s₁ * (q.b * s₂)) + 2 * (t₂ * (p.b * t₁))
      + 2 * (p.b * (s₂ * t₁)), ?_⟩⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, hs₁, ht₁]
    ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, hs₂, ht₂]
    ring
  · simp only [SqU6.commP_j, SqU6.u6Comm3L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_f,
      SqU6.inv_g, hs₁, hs₂, ht₁, ht₂]
    ring

/-- ⭐ **Step two**: pairing such a `gamma_2`-element against an even-column letter gives a
`gamma_3`-element with `j`, `l` and `m` even.  The class-four coordinate is the one that
matters: `u6Comm4L` reduces on a `gamma_2`-element to `p.j * q.d - p.k * q.a + p.f * q.h
- p.h * q.f` plus terms carrying `q.a` or `q.c`, and each of the four meets an even entry. -/
theorem stageN3_of_commutator {p q : SqU6 gr3R} (hp : p ∈ stageN2) (hq : q ∈ stageN1) :
    ⁅p, q⁆ ∈ stageN3 := by
  obtain ⟨pa, pb, pc, pd, pe, ⟨f', hf⟩, ⟨h', hh⟩, ⟨j', hj⟩⟩ := mem_stageN2.mp hp
  obtain ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩ := mem_stageN1.mp hq
  rw [commutatorElement_eq_commP, mem_stageN3]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ?_, ?_, ?_, ?_, ⟨f' * q.c - p.g * t₁, ?_⟩,
    ⟨h' * q.e - p.i * t₂, ?_⟩, ?_⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, pa, pb]
    ring
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, pb, pc]
    ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, pc, pd]
    ring
  · simp only [SqU6.commP_i, SqU6.inv_d, SqU6.inv_e, pd, pe]
    ring
  · simp only [SqU6.commP_j, SqU6.u6Comm3L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_f,
      SqU6.inv_g, pa, pb, pc, hf, ht₁]
    ring
  · simp only [SqU6.commP_l, SqU6.u6Comm3R, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_h,
      SqU6.inv_i, pc, pd, pe, hh, ht₂]
    ring
  · refine ⟨j' * q.d + q.h * f' - h' * q.f - p.k * t₁
      + q.d * (p.g * t₁) - 2 * (t₂ * (q.d * f')), ?_⟩
    simp only [SqU6.commP_m, SqU6.u6Comm4L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d,
      SqU6.inv_f, SqU6.inv_g, SqU6.inv_h, SqU6.inv_j, SqU6.inv_k,
      pa, pb, pc, pd, hf, hh, hj, ht₁, ht₂]
    ring

/-- ⭐⭐ **THE STAGE-FOUR SOUNDNESS CHAIN, PROVED**: at any marking all of whose slots have an
even `(1,2)`-column and an even `(3,4)`-column, every achievable `gamma_3`-dressing - the honest
`gamma_3` of the image subgroup, not a declared lattice - has `j`, `l` and `m` even.  Wave 59's
chain runs one step further and lands in `gamma_4`; this one stops one step earlier, which is
exactly the filtration step the exclusion was missing. -/
theorem forceLcs_two_le_stageN3 {H : Subgroup (SqU6 gr3R)} (hH : H ≤ stageN1) :
    forceLcs H 2 ≤ stageN3 := by
  have h1 : forceLcs H 1 ≤ stageN2 :=
    Subgroup.commutator_le.mpr fun p hp q hq => stageN2_of_commutator (hH hp) (hH hq)
  exact Subgroup.commutator_le.mpr fun p hp q hq => stageN3_of_commutator (h1 hp) (hH hq)

end Chain

/-! ## 7 The exclusion, unconditional -/

section Forcing

variable {h : ℕ} {j : Fin h}

/-- **The image of the stage-four binder point**: the subgroup generated by the marking's slot
values.  `forceLcs (stageImage h j v) 2` is `gamma_3` of it, the achievable stage-four
dressings. -/
def stageImage (h : ℕ) (j : Fin h) (v : SqU6 gr3R) : Subgroup (SqU6 gr3R) :=
  Subgroup.closure (Set.range (stageWit h j v))

/-- Every slot of a one-handle-live tuple is one of its five letters or trivial. -/
private theorem stageTuple_cases {R : Type} [CommRing R] {hh : ℕ} {jj : Fin hh}
    (S X Y U V : SqU6 R) (i : Fin (sqRank hh)) :
    fiveTuple R hh jj S X Y U V i = S ∨ fiveTuple R hh jj S X Y U V i = X
      ∨ fiveTuple R hh jj S X Y U V i = Y ∨ fiveTuple R hh jj S X Y U V i = U
      ∨ fiveTuple R hh jj S X Y U V i = V ∨ fiveTuple R hh jj S X Y U V i = 1 := by
  simp only [fiveTuple]
  split_ifs <;> tauto

/-- ⭐ **The point's letters all lie in `M_1`**, which is the only input the chain needs. -/
theorem stageImage_le_stageN1 {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c) :
    stageImage h j v ≤ stageN1 := by
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := hv
  rw [stageImage, Subgroup.closure_le]
  rintro z ⟨i, rfl⟩
  simp only [stageWit]
  rcases stageTuple_cases (fiveSigMark gr3R * v) stageX stageY stageU stageV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1, SetLike.mem_coe, mem_stageN1]
  · exact ⟨⟨s, by rw [SqU6.mul_a, hs]; simp [fiveSigMark]⟩,
      ⟨t, by rw [SqU6.mul_c, ht]; simp [fiveSigMark]⟩⟩
  · exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  · exact ⟨⟨3, by decide⟩, ⟨2, by decide⟩⟩
  · exact ⟨⟨3, by decide⟩, ⟨3, by decide⟩⟩
  · exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- Every slot of the marking has an even `(1,2)`-column, which is what
`gaThreeShiftO_even` reads. -/
theorem stageWit_a_even {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a) (i : Fin (sqRank h)) :
    (2 : gr3R) ∣ (stageWit h j v i).a := by
  obtain ⟨s, hs⟩ := hv
  simp only [stageWit]
  rcases stageTuple_cases (fiveSigMark gr3R * v) stageX stageY stageU stageV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
  · exact ⟨s, by rw [SqU6.mul_a, hs]; simp [fiveSigMark]⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨0, by decide⟩

/-- ⭐⭐ **The stage-four selection bit is forced even.**  At the binder point, a sigma dressing
whose frame is killed by **any** achievable five-slot STAGE-FOUR refinement leaves an even
class-five residue.  This is `GradedFiveForce.fiveWit_sigma_forced` one filtration step wider,
and it is the statement wave 59 could not make. -/
theorem stageWit_sigma_forced {v : SqU6 gr3R} {z : Fin (sqRank h) → SqU6 gr3R}
    (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c)
    (hz : ∀ i, z i ∈ forceLcs (stageImage h j v) 2)
    (hkill : sqRelWord (conFiveDress (stageWit h j v) z) = 1) :
    selPar (sqRelWord (stageWit h j v)).o = 0 := by
  have hle := forceLcs_two_le_stageN3 (stageImage_le_stageN1 (h := h) (j := j) hv)
  have hga : ∀ i, (z i).IsGaThree := fun i => stageN3_isGaThree (hle (hz i))
  have heven : ∀ i, (2 : gr3R) ∣ (z i).j ∧ (2 : gr3R) ∣ (z i).l ∧ (2 : gr3R) ∣ (z i).m :=
    fun i => stageN3_even (hle (hz i))
  rw [sqRelWord_gaThreeDress hga] at hkill
  have ho := congrArg SqU6.o hkill
  rw [SqU6.mul_o, SqU6.one_o] at ho
  have hsh := gaThreeShift_isGaThree (h := h) (m := stageWit h j v) (z := z)
  obtain ⟨ca, hca⟩ : (2 : gr3R) ∣ (sqRelWord (stageWit h j v)).a :=
    ⟨-2 * (stageWit h j v 1).a + (stageWit h j v 2).a, by rw [SqU6.sqRelWord_a]; ring⟩
  obtain ⟨cl, hcl⟩ : (2 : gr3R) ∣ (gaThreeShift h (stageWit h j v) z).l := by
    rw [gaThreeShift_l]
    exact ⟨-2 * (z 1).l + (z 2).l, by ring⟩
  obtain ⟨co, hco⟩ : (2 : gr3R) ∣ (gaThreeShift h (stageWit h j v) z).o := by
    rw [gaThreeShift_o]
    exact gaThreeShiftO_even (stageWit_a_even hv.1) heven
  rw [hca, hcl, hco, hsh.2.2.2.2.1, hsh.2.2.2.2.2.2.2.2] at ho
  have hfin : (sqRelWord (stageWit h j v)).o
      = 2 * (-(co + ca * (gaThreeShift h (stageWit h j v) z).n
        + (sqRelWord (stageWit h j v)).f * cl)) := by
    linear_combination ho
  rw [hfin, selPar_two_mul]

/-- ⭐⭐⭐ **THE UNCONDITIONAL EXCLUSION: the sigma dressing `a0 = a1` is excluded at class five
against STAGE-FOUR refinements.**  No achievable `gamma_3`-dressing of the five slots kills the
dressed frame, at any handle count and any handle.  Wave 59 proved the stage-FIVE statement at a
point where this one is FALSE; here both hold, so the residual `GradedSigmaFour` section 7 named
is discharged with the same scope the committed class-four exclusion enjoys. -/
theorem sqRelWord_stageWit_diag_ne_one {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (stageImage h j stageX) 2) :
    sqRelWord (conFiveDress (stageWit h j stageX) z) ≠ 1 := by
  intro hc
  have hp := stageWit_sigma_forced ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ hz hc
  rw [sqRelWord_stageWit_diag, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- …while the undressed frame is killed outright, so the bit really does separate the two
dressings that `GradedSigmaFour` could not tell apart. -/
theorem stageWit_bit_separates (h : ℕ) (j : Fin h) :
    selPar (sqRelWord (stageWit h j 1)).o = 0
      ∧ selPar (sqRelWord (stageWit h j stageX)).o = 1 := by
  refine ⟨?_, ?_⟩
  · rw [sqRelWord_stageWit_triv]
    decide
  · rw [sqRelWord_stageWit_diag, SqU6.liftO_o]
    decide

/-- ⭐ **Achievability is load-bearing at the stage-four level too, and this is the witness.**
The *unrestricted* `gamma_4`-shaped move `<m = 1, n = 3>` on the sigma slot kills the dressed
frame outright: by `sqWord_mul_gaFour_sigma` its increment is
`1 * x_{56} - 3 * x_{12} = 5 - 6 = -1`, and the residue is `1`.  So the forcing above is not a
statement the lattice could be dropped from.  Stated at one handle, by kernel computation. -/
theorem stageWit_unrestricted_kill :
    sqRelWord (fun i => if (i : ℕ) = 0
      then stageWit 1 0 stageX i * ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0⟩
      else stageWit 1 0 stageX i) = 1 := by decide

/-- …and that move is **not** achievable: its class-four coordinate is odd, and every
achievable stage-four dressing is even there. -/
theorem stageWit_unrestricted_not_achievable :
    (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0⟩ : SqU6 gr3R) ∉ stageN3 := by
  intro hc
  obtain ⟨-, -, ⟨t, ht⟩⟩ := stageN3_even hc
  exact absurd ht (by revert t; decide)

end Forcing

/-! ## 8 The wave-59 point, and why it fails exactly one hypothesis -/

section WaveFiftyNine

/-- ⚠ **Wave 59's point fails `M_1`, at exactly one letter and one column.**  Its `U`-letter has
`a = 1`.  Every other letter of that point, and every column of `M_1` other than this one, is
even; so the stage-four chain misses it by a single odd entry. -/
theorem forceU_not_stageN1 : forceU ∉ stageN1 := by
  intro hc
  obtain ⟨⟨t, ht⟩, -⟩ := mem_stageN1.mp hc
  exact absurd ht (by revert t; decide)

/-- …and the wave-59 killing dressing is exactly what `M_3` forbids: the triple commutator
`[[sigma, U], x1] = <m=5, n=6>` has an **odd** class-four coordinate. -/
theorem fiveWit_gaThree_kill_not_stageN3 :
    commP (commP (fiveSigMark gr3R) forceU) forceY ∉ stageN3 := by
  intro hc
  obtain ⟨-, -, ⟨t, ht⟩⟩ := stageN3_even hc
  rw [show (commP (commP (fiveSigMark gr3R) forceU) forceY).m = 5 from by decide] at ht
  exact absurd ht (by revert t; decide)

/-- ⭐ **The composite check (doctrine iii).**  Wave 59's stage-FIVE exclusion and this file's
stage-FOUR one are about different points, and the two verdicts are consistent: at wave 59's
point a stage-four move kills, at this file's point none does, and the difference is the single
odd column above.  Both points carry the same class-five separation: an odd residue at the
`a0 = a1` dressing and a trivial one at the undressed frame. -/
theorem stage_vs_wave59_residues (h : ℕ) (j : Fin h) :
    selPar (sqRelWord (fiveWit h j forceX)).o = 1
      ∧ selPar (sqRelWord (stageWit h j stageX)).o = 1
      ∧ sqRelWord (fiveWit h j 1) = 1 ∧ sqRelWord (stageWit h j 1) = 1 := by
  refine ⟨?_, ?_, sqRelWord_fiveWit_triv h j, sqRelWord_stageWit_triv h j⟩
  · rw [sqRelWord_fiveWit_diag, liftC6_o]
    decide
  · rw [sqRelWord_stageWit_diag, SqU6.liftO_o]
    decide

/-- **Independent check of the two verdicts.**  Both relators at `h = 1`, taken straight from
`sqRelWord` by kernel computation, without going through `sqRelWord_fiveTuple` or the algebra of
sections 2 and 3.  Wave 57's process finding was that two results of one wave can each be right
while their composition is vacuous, so the structural route and the machine route are made to
meet here. -/
theorem stageWit_decide_crosscheck :
    sqRelWord (stageWit 1 0 1) = 1 ∧ sqRelWord (stageWit 1 0 stageX) = SqU6.liftO 1 := by decide


end WaveFiftyNine

/-! ## 9 Axiom pins -/

section AxiomPins

#print axioms SqU6.IsGaThree
#print axioms SqU6.IsGaFour.isGaThree
#print axioms SqU6.isGaThree_one
#print axioms gaThreePairL
#print axioms gaThreePairR
#print axioms gaThreePair
#print axioms sqFoxX6
#print axioms sqFoxX6_a
#print axioms sqFoxX6_b
#print axioms sqFoxX6_d
#print axioms sqFoxX6_e
#print axioms sqFoxX6_f
#print axioms sqFoxX6_i
#print axioms SqU6.gaFour_comm
#print axioms SqU6.gaThree_comm
#print axioms SqU6.gaThree_mul
#print axioms gaThreeCorr
#print axioms gaThreeCore
#print axioms gaThreeCore_isGaThree
#print axioms gaThreeCore_j
#print axioms gaThreeCore_l
#print axioms SqU6.sqWord_mul_gaThree
#print axioms gaThreeHandle
#print axioms gaThreeHandle_isGaFour
#print axioms SqU6.commP_mul_gaThree
#print axioms SqU6.handleWord_mul_gaThree_all
#print axioms gaThreeShift
#print axioms sqRelWord_gaThreeDress
#print axioms gaThreePair_even
#print axioms gaThreeCorr_even
#print axioms gaThreeCore_o_even
#print axioms gaThreeHandle_o_even
#print axioms gaThreeShiftO
#print axioms gaThreeShift_o
#print axioms gaThreeShift_l
#print axioms gaThreeShift_isGaThree
#print axioms gaThreeShiftO_even
#print axioms stageX
#print axioms stageY
#print axioms stageU
#print axioms stageV
#print axioms stageWit
#print axioms sqRelWord_stageWit_triv
#print axioms sqRelWord_stageWit_diag
#print axioms stage_letters_even
#print axioms stageX_gauge
#print axioms commP_stageUV_live
#print axioms stageWit_class_four_blind
#print axioms stageWit_w58_form_crosscheck
#print axioms stageN1
#print axioms stageN2
#print axioms stageN3
#print axioms mem_stageN1
#print axioms mem_stageN2
#print axioms mem_stageN3
#print axioms stageN3_isGaThree
#print axioms stageN3_even
#print axioms stageN2_of_commutator
#print axioms stageN3_of_commutator
#print axioms forceLcs_two_le_stageN3
#print axioms stageImage
#print axioms stageImage_le_stageN1
#print axioms stageWit_a_even
#print axioms stageWit_sigma_forced
#print axioms sqRelWord_stageWit_diag_ne_one
#print axioms stageWit_bit_separates
#print axioms stageWit_unrestricted_kill
#print axioms stageWit_unrestricted_not_achievable
#print axioms forceU_not_stageN1
#print axioms fiveWit_gaThree_kill_not_stageN3
#print axioms stage_vs_wave59_residues
#print axioms stageWit_decide_crosscheck

end AxiomPins

end SqCore

end Dyadic

end GQ2
