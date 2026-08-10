/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFourCleared

/-!
# W58-FIVE: the class-five carrier `U_6(R)`, its hom layer, and the end of handle blindness

Wave 57 located everything remaining on the `h >= 1` route at class five: the sigma residual of
`GradedSigmaFour` section 7 needs it, and `GradedFourCleared` proved that at class four the
handle block can be **live** but is **never visible** to the sigma forcing, so seeing a block
"requires a functional the sigma slot meets, and at class four there is none".  Nothing could
move until the carrier existed.  This file builds it and spends it.

## Headline 1: the class-five carrier

`SqU6 R = U_6(R)`, the unitriangular `6 x 6` group on fifteen coordinates

```text
        ⎡1 a f j m o⎤          a b c d e   abelian
        ⎢0 1 b g k n⎥          f g h i     class two
        ⎢0 0 1 c h l⎥          j k l       class three
        ⎢0 0 0 1 d i⎥          m n         class four
        ⎢0 0 0 0 1 e⎥          o           class five
        ⎣0 0 0 0 0 1⎦
```

with its group structure, the fifteen coordinate `simp` lemmas, commutator and conjugation
forms in closed form, the two `U_5`-quotients `toU5L`, `toU5R`, the centre `zHom6`, and the
fifteen power laws.  Every closed form was derived with exact integer arithmetic
(`scripts/w58_five/derive_u6.py`, `emit_lean.py`) and cross-validated against honest `6 x 6`
group collection before transcription (`validate_u6.py`: **39804 comparisons, zero
mismatches**, plus **9** named structural checks).

Three structural facts appear here that class four did not have.

* **Three interior columns.**  Four class-two rows, three class-three, two class-four and one
  class-five, so *fourteen* of the fifteen rows are `GradedFour` rows through the two
  `U_5`-quotients (`SqU6.toU5L_sqRelWord`, `SqU6.toU5R_sqRelWord`) and only the `(1,6)`-row is
  new.
* **`gamma_2` is non-abelian in three coordinates.**  At class four the only cross term inside
  `gamma_2` is `x.e * y.g` in the top coordinate; here `gamma_2` products carry `f * h` in `m`,
  `g * i` in `n`, and `f * l + j * i` in `o`.
* **The class-five commutator has four complementary pairings**, `a` against `n`, `f` against
  `l`, `j` against `i`, `m` against `e`.  The third of these pairs a **class-three** coordinate
  against a **class-two** one and has no class-four analogue, because at class four the
  class-three row is already the top row.  That single pairing is what headline 3 is about.

## Headline 2: the hom layer closes, and the hard step is named

The pro-2 layer (`equivProd`, `Finite`, `nat_card = (#R)^15`, the `⊥` topology,
`SqU6.isProP_two`), the fifteen power laws and the lift `sqU6Hom` transpose mechanically, with
one bookkeeping change: the class-five coordinate has **five** binomial layers (`SqU6.pow_o`
carries `C(n,2)` through `C(n,5)`) where class four had four and class three at most two.

⚠ **The `ℤ₂`-power lemma is not mechanical, and it is harder than at class four in a way that
is worth stating exactly.**  `GradedFourHom` needed six obstructions, the sixth failed at the
witness slot `sigFourX` (where `a*i + e*g + h*d = 2`), and the repair was that
`C(n,2) * (2w) = (n^2 - n) * w` is a polynomial in `n` over `ℤ`.  At class five:

* there are **ten** obstructions, one per non-abelian coordinate (3, 6, 10 as the class rises);
* the `C(n,3)`, `C(n,4)` and `C(n,5)` layers of the top coordinate are **not** independent.
  They are the exact identities

  ```text
  X3 = l * (a*b) + i * (a*g + c*f) + e * (a*k + d*j + f*h)
  X4 = (a*b) * (c*i + e*h) + d*e * (a*g + c*f)
  X5 = (a*b) * c*d*e
  ```

  so the four class-two obstructions, the three class-three ones **and the class-four one**
  control all three higher layers;
* therefore the class-four obstruction, which class four was allowed to leave merely **even**,
  is at class five one of the conditions that must vanish on the nose for the flat argument.
  An even class-four obstruction `2*wm` feeds `2 * e * wm` into the class-five `C(n,3)` layer,
  and `C(n,3) * (2w)` is **not** a polynomial in `n` over `ℤ`.  Class four's repair does not
  extend by itself.

⭐ `SqU6.zpowZtwo_of_evenFour` buys the even case back, and that is this file's non-mechanical
step.  What restores integrality is the next divisibility: `C(n,3) * (6w) = (n^3 - 3n^2 + 2n)*w`
is a polynomial over `ℤ`, so the class-five cubic layer only has to be divisible by `6`.  The
functional equation then forces a symmetric pair of conditions rather than one:
`g.e * wm = g.a * wn = 3 * w3`, and the powering picks up a genuine **cubic** term
`(pi u ^3 - 3 pi u ^2 + 2 pi u) * w3` that no class-four statement could produce.
`SqU6.zpowZtwo_of_flatTwo` (nine flat, top even) and `SqU6.zpowZtwo_of_flat` (all ten flat) are
its `wm = wn = w3 = 0` and `w2 = 0` cases.  ⭐ `fivePowBase` shows the strengthening is not
vacuous: a base whose class-four obstruction is `2`, so that neither flat lemma applies, and
whose class-five power law is genuinely cubic, `(g^n).o = C(n,3) * 2`.

## ⭐⭐ Headline 3: the wave-57 blindness mechanism breaks at class five

The class-four blindness has a mechanism, and the mechanism can be read off the multiplication
rule.  The relator is the core word times the handle block, and the block lies in `gamma_2`, so
the block enters the top row only through the cross terms of `mul`:

```text
class four   (relator).j = core.j + H.j + core.a * H.i + core.e * H.g
class five   (relator).o = core.o + H.o + core.a * H.n + core.f * H.l + core.j * H.i
```

(`SqU6.sqRelWord_m`, `SqU6.sqRelWord_o`).  A sigma dressing never moves `core.a`, and on the
`nu'`-gauge (`x0`, `x1` and the dressing all with vanishing `b`-column) it does not move
`core.f` either (`SqU6.sqWord_f_dress`).  At class four those are the only two coefficients the
block meets, so the block cancels out of the response: ⭐ `SqU6.sqRelWord_sigFiveDress_handle_blind_four`
recovers wave 57's theorem inside the class-five carrier, at an arbitrary sigma slot rather
than the committed one.

At class five there is a third coefficient, `core.j`, and the dressing **does** move it:
⭐ `SqU6.sqWord_j_dress` gives the closed form

```text
(sqWord (s*v) x y).j - (sqWord s x y).j
  = v.a*x.g - v.g*x.a + v.f*x.c - v.c*x.f - s.b*(v.a*x.c + v.c*x.a)
```

on the same gauge, and it is not identically zero.  Hence ⭐⭐
`SqU6.sqRelWord_sigFiveDress_handle_visible`: for two markings with the **same** core slots and
arbitrary different handle blocks, the difference of the two sigma responses is **exactly** the
class-three sigma response times the difference of the blocks' outermost class-two pairings
`H.i = sum_j (u_j.d * v_j.e - v_j.d * u_j.e)`.  The functional wave 57 said class four does not
have is therefore named: it is `H.i`, weighted by the class-three response.

**And the point is honest, not hypothetical.**  ⭐⭐ `sqRelWord_liveFiveMark`: the marking

```text
sigma = 1,  x0 = <g = 1>,  x1 = <g = 2, i = 3, n = 1>,  U = <d = 1>,  V = <e = 2>
```

kills **all fifteen** relator rows at **every** handle count and every handle
(`fiveTuple`/`sqRelWord_fiveTuple` carry it to general `h`), and its handle block is **live**,
of order four (`commP_fiveUV_ne_one`).  This is the campaign's first class-five point.  There,
⭐⭐ `liveFive_response` shows the handle block contributes `2` to the class-five sigma
response, and ⭐⭐ `liveFive_response_sees_block` shows the response differs by `2` from the
response at the same core slots with the block removed, while ⭐ `liveFive_class_four_blind`
shows the class-four row of the very same pair of markings does not move at all.

⚠ **What this does and does not settle.**  It settles that the wave-57 blindness *mechanism*
breaks: the block no longer contributes equally to the top row before and after a dressing.
It does **not** yet settle that the block carries information a class-five forcing can use.
Two markings that share their core slots and both kill the relator necessarily have the *same*
handle word, since the relator pins `handleWord = (sqWord)^{-1}`; so the comparison marking in
the certificate above is deliberately the one with the block removed, and that one is not
relator-killing.  Turning visibility into a forcing needs a class-five sigma witness and a
selection bit, which this file does not build.

## PROVED versus measured versus deferred

**PROVED**, with no live hypothesis: the whole of sections 1 to 4 (carrier, group structure,
coordinate API, commutator and conjugation forms, quotients, pro-2 layer, fifteen power laws,
the lift, all three `ℤ₂`-power lemmas, the gate `sqU6Balance`); in section 5 the handle block's
`gamma_2`-ness and its `i`-pairing, the five abelian relator rows, the two quotient transports,
the class-three row of the core word through the committed `sqU4Core`, both top-row splits, the
two dressing responses, the class-four blindness and the class-five visibility; in section 6
the live point at every handle count, all fifteen of its relator rows, the liveness of its
block, both response computations and the non-vacuity of `fivePowBase`.

**Measured, not proved** (`scripts/w58_five/results/`): the closed forms against honest `6 x 6`
collection (39804 comparisons, zero mismatches); the live point at handle counts `1` to `4`
independently of the Lean proof; the sweep of all `98` single-column `nu'`-trivial dressings at
the live point, of which `6` see the block at class five and `0` see it at class four; and the
powering polynomial at `279` flat and `673` even-class-four bases with `2648` bases falling
outside both, so the hypotheses genuinely bite.

**Deferred**, and named: the general closed form of the class-five defect `sqU6Defect` (the
analogue of `sqU4Defect`; `GradedFour` deferred `sqU5Defect` for the same reason, and the
fourteen lower rows are reachable through the quotients); the class-five sigma witness, the
selection bit and any forcing statement; the class-five reading of `GradedSigmaFour` section
7's residual; two live handles; and the class-five hom-level containment.

## Contents

* **1** `SqU6 R`, its group structure, componentwise `simp` lemmas, `DecidableEq`;
* **2** commutators (`u6Comm3L/M/R`, `u6Comm4L/R`, ⭐ `u6Comm5`), conjugation, the two
  `U_5`-quotients, the centre;
* **3** the pro-2 layer and the fifteen power laws, ⭐ `SqU6.pow_o` with five binomial layers;
* **4** the lift `sqU6Hom`, ⭐ `SqU6.zpowZtwo_of_evenFour` and its two flat corollaries, and
  the gate `sqU6Balance`;
* **5** the relator at class five: the handle block, the abelian rows, the quotient transports,
  ⭐⭐ `SqU6.sqRelWord_o`, the dressing responses, ⭐ the class-four blindness and ⭐⭐ the
  class-five visibility;
* **6** ⭐⭐ the live class-five point and the certificates, and ⭐ `fivePowBase`;
* **7** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8` or on `Fin`
arithmetic.  All **186** committed prints are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The class-five test group `SqU6 R` -/

section U6Group

/-- **The class-five test group** over `R`: the unitriangular `6 x 6` group, carried on the
fifteen strictly-upper entries. -/
@[ext]
structure SqU6 (R : Type) [CommRing R] where
  /-- The `(1,2)` entry: the first abelian coordinate. -/
  a : R
  /-- The `(2,3)` entry: the second abelian coordinate. -/
  b : R
  /-- The `(3,4)` entry: the third abelian coordinate. -/
  c : R
  /-- The `(4,5)` entry: the fourth abelian coordinate. -/
  d : R
  /-- The `(5,6)` entry: the fifth abelian coordinate. -/
  e : R
  /-- The `(1,3)` entry: the first class-two coordinate. -/
  f : R
  /-- The `(2,4)` entry: the second class-two coordinate. -/
  g : R
  /-- The `(3,5)` entry: the third class-two coordinate. -/
  h : R
  /-- The `(4,6)` entry: the fourth class-two coordinate. -/
  i : R
  /-- The `(1,4)` entry: the first class-three coordinate. -/
  j : R
  /-- The `(2,5)` entry: the second class-three coordinate. -/
  k : R
  /-- The `(3,6)` entry: the third class-three coordinate. -/
  l : R
  /-- The `(1,5)` entry: the first class-four coordinate. -/
  m : R
  /-- The `(2,6)` entry: the second class-four coordinate. -/
  n : R
  /-- The `(1,6)` entry: the class-five coordinate. -/
  o : R

namespace SqU6

variable {R : Type} [CommRing R]

instance : One (SqU6 R) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

instance : Mul (SqU6 R) :=
  ⟨fun p q => ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d, p.e + q.e,
    p.f + q.f + p.a * q.b, p.g + q.g + p.b * q.c, p.h + q.h + p.c * q.d,
    p.i + q.i + p.d * q.e,
    p.j + q.j + p.a * q.g + p.f * q.c, p.k + q.k + p.b * q.h + p.g * q.d,
    p.l + q.l + p.c * q.i + p.h * q.e,
    p.m + q.m + p.a * q.k + p.f * q.h + p.j * q.d,
    p.n + q.n + p.b * q.l + p.g * q.i + p.k * q.e,
    p.o + q.o + p.a * q.n + p.f * q.l + p.j * q.i + p.m * q.e⟩⟩

instance : Inv (SqU6 R) :=
  ⟨fun p => ⟨-p.a, -p.b, -p.c, -p.d, -p.e,
    p.a * p.b - p.f, p.b * p.c - p.g, p.c * p.d - p.h, p.d * p.e - p.i,
    -(p.a * p.b * p.c) + p.a * p.g + p.c * p.f - p.j,
    -(p.b * p.c * p.d) + p.b * p.h + p.d * p.g - p.k,
    -(p.c * p.d * p.e) + p.c * p.i + p.e * p.h - p.l,
    p.a * p.b * p.c * p.d - p.a * p.b * p.h - p.a * p.d * p.g + p.a * p.k
      - p.c * p.d * p.f + p.d * p.j + p.f * p.h - p.m,
    p.b * p.c * p.d * p.e - p.b * p.c * p.i - p.b * p.e * p.h + p.b * p.l
      - p.d * p.e * p.g + p.e * p.k + p.g * p.i - p.n,
    -(p.a * p.b * p.c * p.d * p.e) + p.a * p.b * p.c * p.i + p.a * p.b * p.e * p.h
      - p.a * p.b * p.l + p.a * p.d * p.e * p.g - p.a * p.e * p.k - p.a * p.g * p.i
      + p.a * p.n + p.c * p.d * p.e * p.f - p.c * p.f * p.i - p.d * p.e * p.j
      - p.e * p.f * p.h + p.e * p.m + p.f * p.l + p.i * p.j - p.o⟩⟩

@[simp] theorem one_a : (1 : SqU6 R).a = 0 := rfl
@[simp] theorem one_b : (1 : SqU6 R).b = 0 := rfl
@[simp] theorem one_c : (1 : SqU6 R).c = 0 := rfl
@[simp] theorem one_d : (1 : SqU6 R).d = 0 := rfl
@[simp] theorem one_e : (1 : SqU6 R).e = 0 := rfl
@[simp] theorem one_f : (1 : SqU6 R).f = 0 := rfl
@[simp] theorem one_g : (1 : SqU6 R).g = 0 := rfl
@[simp] theorem one_h : (1 : SqU6 R).h = 0 := rfl
@[simp] theorem one_i : (1 : SqU6 R).i = 0 := rfl
@[simp] theorem one_j : (1 : SqU6 R).j = 0 := rfl
@[simp] theorem one_k : (1 : SqU6 R).k = 0 := rfl
@[simp] theorem one_l : (1 : SqU6 R).l = 0 := rfl
@[simp] theorem one_m : (1 : SqU6 R).m = 0 := rfl
@[simp] theorem one_n : (1 : SqU6 R).n = 0 := rfl
@[simp] theorem one_o : (1 : SqU6 R).o = 0 := rfl

@[simp] theorem mul_a (p q : SqU6 R) : (p * q).a = p.a + q.a := rfl
@[simp] theorem mul_b (p q : SqU6 R) : (p * q).b = p.b + q.b := rfl
@[simp] theorem mul_c (p q : SqU6 R) : (p * q).c = p.c + q.c := rfl
@[simp] theorem mul_d (p q : SqU6 R) : (p * q).d = p.d + q.d := rfl
@[simp] theorem mul_e (p q : SqU6 R) : (p * q).e = p.e + q.e := rfl
@[simp] theorem mul_f (p q : SqU6 R) : (p * q).f = p.f + q.f + p.a * q.b := rfl
@[simp] theorem mul_g (p q : SqU6 R) : (p * q).g = p.g + q.g + p.b * q.c := rfl
@[simp] theorem mul_h (p q : SqU6 R) : (p * q).h = p.h + q.h + p.c * q.d := rfl
@[simp] theorem mul_i (p q : SqU6 R) : (p * q).i = p.i + q.i + p.d * q.e := rfl
@[simp] theorem mul_j (p q : SqU6 R) : (p * q).j = p.j + q.j + p.a * q.g + p.f * q.c := rfl
@[simp] theorem mul_k (p q : SqU6 R) : (p * q).k = p.k + q.k + p.b * q.h + p.g * q.d := rfl
@[simp] theorem mul_l (p q : SqU6 R) : (p * q).l = p.l + q.l + p.c * q.i + p.h * q.e := rfl

@[simp] theorem mul_m (p q : SqU6 R) :
    (p * q).m = p.m + q.m + p.a * q.k + p.f * q.h + p.j * q.d := rfl

@[simp] theorem mul_n (p q : SqU6 R) :
    (p * q).n = p.n + q.n + p.b * q.l + p.g * q.i + p.k * q.e := rfl

@[simp] theorem mul_o (p q : SqU6 R) :
    (p * q).o = p.o + q.o + p.a * q.n + p.f * q.l + p.j * q.i + p.m * q.e := rfl

@[simp] theorem inv_a (p : SqU6 R) : p⁻¹.a = -p.a := rfl
@[simp] theorem inv_b (p : SqU6 R) : p⁻¹.b = -p.b := rfl
@[simp] theorem inv_c (p : SqU6 R) : p⁻¹.c = -p.c := rfl
@[simp] theorem inv_d (p : SqU6 R) : p⁻¹.d = -p.d := rfl
@[simp] theorem inv_e (p : SqU6 R) : p⁻¹.e = -p.e := rfl
@[simp] theorem inv_f (p : SqU6 R) : p⁻¹.f = p.a * p.b - p.f := rfl
@[simp] theorem inv_g (p : SqU6 R) : p⁻¹.g = p.b * p.c - p.g := rfl
@[simp] theorem inv_h (p : SqU6 R) : p⁻¹.h = p.c * p.d - p.h := rfl
@[simp] theorem inv_i (p : SqU6 R) : p⁻¹.i = p.d * p.e - p.i := rfl

@[simp] theorem inv_j (p : SqU6 R) :
    p⁻¹.j = -(p.a * p.b * p.c) + p.a * p.g + p.c * p.f - p.j := rfl

@[simp] theorem inv_k (p : SqU6 R) :
    p⁻¹.k = -(p.b * p.c * p.d) + p.b * p.h + p.d * p.g - p.k := rfl

@[simp] theorem inv_l (p : SqU6 R) :
    p⁻¹.l = -(p.c * p.d * p.e) + p.c * p.i + p.e * p.h - p.l := rfl

@[simp] theorem inv_m (p : SqU6 R) :
    p⁻¹.m = p.a * p.b * p.c * p.d - p.a * p.b * p.h - p.a * p.d * p.g + p.a * p.k
      - p.c * p.d * p.f + p.d * p.j + p.f * p.h - p.m := rfl

@[simp] theorem inv_n (p : SqU6 R) :
    p⁻¹.n = p.b * p.c * p.d * p.e - p.b * p.c * p.i - p.b * p.e * p.h + p.b * p.l
      - p.d * p.e * p.g + p.e * p.k + p.g * p.i - p.n := rfl

@[simp] theorem inv_o (p : SqU6 R) :
    p⁻¹.o = -(p.a * p.b * p.c * p.d * p.e) + p.a * p.b * p.c * p.i + p.a * p.b * p.e * p.h
      - p.a * p.b * p.l + p.a * p.d * p.e * p.g - p.a * p.e * p.k - p.a * p.g * p.i
      + p.a * p.n + p.c * p.d * p.e * p.f - p.c * p.f * p.i - p.d * p.e * p.j
      - p.e * p.f * p.h + p.e * p.m + p.f * p.l + p.i * p.j - p.o := rfl

instance : Group (SqU6 R) where
  mul_assoc p q r := by
    ext <;> simp only [mul_a, mul_b, mul_c, mul_d, mul_e, mul_f, mul_g, mul_h, mul_i,
      mul_j, mul_k, mul_l, mul_m, mul_n, mul_o] <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by
    ext <;>
      simp only [mul_a, mul_b, mul_c, mul_d, mul_e, mul_f, mul_g, mul_h, mul_i,
        mul_j, mul_k, mul_l, mul_m, mul_n, mul_o,
        inv_a, inv_b, inv_c, inv_d, inv_e, inv_f, inv_g, inv_h, inv_i,
        inv_j, inv_k, inv_l, inv_m, inv_n, inv_o,
        one_a, one_b, one_c, one_d, one_e, one_f, one_g, one_h, one_i,
        one_j, one_k, one_l, one_m, one_n, one_o] <;> ring

/-- The fifteen coordinates of a `SqU6` element determine triviality. -/
theorem eq_one_iff {p : SqU6 R} :
    p = 1 ↔ p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.e = 0 ∧ p.f = 0 ∧ p.g = 0 ∧ p.h = 0 ∧
      p.i = 0 ∧ p.j = 0 ∧ p.k = 0 ∧ p.l = 0 ∧ p.m = 0 ∧ p.n = 0 ∧ p.o = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk, hl, hm, hn, ho⟩
    ext <;> simpa

instance instDecidableEq {R : Type} [CommRing R] [DecidableEq R] : DecidableEq (SqU6 R) :=
  fun _ _ => decidable_of_iff _ SqU6.ext_iff.symm

end SqU6

end U6Group

/-! ## 2 Commutators, conjugation, and the two `U_5`-quotients -/

section U6Calculus

namespace SqU6

variable {R : Type} [CommRing R]

@[simp] theorem commP_a (p q : SqU6 R) : (commP p q).a = 0 := by
  simp only [commP, mul_a, inv_a]; ring

@[simp] theorem commP_b (p q : SqU6 R) : (commP p q).b = 0 := by
  simp only [commP, mul_b, inv_b]; ring

@[simp] theorem commP_c (p q : SqU6 R) : (commP p q).c = 0 := by
  simp only [commP, mul_c, inv_c]; ring

@[simp] theorem commP_d (p q : SqU6 R) : (commP p q).d = 0 := by
  simp only [commP, mul_d, inv_d]; ring

@[simp] theorem commP_e (p q : SqU6 R) : (commP p q).e = 0 := by
  simp only [commP, mul_e, inv_e]; ring

/-- The first class-two pairing, on the `(a, b)`-columns. -/
@[simp] theorem commP_f (p q : SqU6 R) : (commP p q).f = p.a * q.b - p.b * q.a := by
  simp only [commP, mul_a, mul_f, inv_a, inv_b, inv_f]; ring

/-- The second class-two pairing, on the `(b, c)`-columns. -/
@[simp] theorem commP_g (p q : SqU6 R) : (commP p q).g = p.b * q.c - p.c * q.b := by
  simp only [commP, mul_b, mul_g, inv_b, inv_c, inv_g]; ring

/-- The third class-two pairing, on the `(c, d)`-columns. -/
@[simp] theorem commP_h (p q : SqU6 R) : (commP p q).h = p.c * q.d - p.d * q.c := by
  simp only [commP, mul_c, mul_h, inv_c, inv_d, inv_h]; ring

/-- The fourth class-two pairing, on the `(d, e)`-columns: new at class five, and the
one the class-five sigma reading meets (section 5). -/
@[simp] theorem commP_i (p q : SqU6 R) : (commP p q).i = p.d * q.e - p.e * q.d := by
  simp only [commP, mul_d, mul_i, inv_d, inv_e, inv_i]; ring

/-- **The left class-three commutator form**: `GradedFour`'s `u5Comm3L` in the coordinates
`(a, b, c, f, g, j)` of the first four columns. -/
def u6Comm3L (p q : SqU6 R) : R :=
  p.a * q.g - p.g * q.a + p.f * q.c - p.c * q.f
    + p.a * p.c * q.b - p.a * p.b * q.c + p.c * q.a * q.b - p.b * q.a * q.c

/-- **The middle class-three commutator form**, in the coordinates `(b, c, d, g, h, k)`. -/
def u6Comm3M (p q : SqU6 R) : R :=
  p.b * q.h - p.h * q.b + p.g * q.d - p.d * q.g
    + p.b * p.d * q.c - p.b * p.c * q.d + p.d * q.b * q.c - p.c * q.b * q.d

/-- **The right class-three commutator form**, in the coordinates `(c, d, e, h, i, l)`. -/
def u6Comm3R (p q : SqU6 R) : R :=
  p.c * q.i - p.i * q.c + p.h * q.e - p.e * q.h
    + p.c * p.e * q.d - p.c * p.d * q.e + p.e * q.c * q.d - p.d * q.c * q.e

@[simp] theorem commP_j (p q : SqU6 R) : (commP p q).j = u6Comm3L p q := by
  simp only [commP, u6Comm3L, mul_a, mul_f, mul_j,
    inv_a, inv_b, inv_c, inv_f, inv_g, inv_j]
  ring

@[simp] theorem commP_k (p q : SqU6 R) : (commP p q).k = u6Comm3M p q := by
  simp only [commP, u6Comm3M, mul_b, mul_g, mul_k,
    inv_b, inv_c, inv_d, inv_g, inv_h, inv_k]
  ring

@[simp] theorem commP_l (p q : SqU6 R) : (commP p q).l = u6Comm3R p q := by
  simp only [commP, u6Comm3R, mul_c, mul_h, mul_l,
    inv_c, inv_d, inv_e, inv_h, inv_i, inv_l]
  ring

/-- **The left class-four commutator form**: `GradedFour`'s `u5Comm4` in the coordinates
`(a, b, c, d, f, g, h, j, k, m)` of the first five columns. -/
def u6Comm4L (p q : SqU6 R) : R :=
  p.a * q.k - p.k * q.a + p.j * q.d - p.d * q.j + p.f * q.h - p.h * q.f
    + p.a * p.h * q.b - p.a * p.b * q.h + p.h * q.a * q.b - p.b * q.a * q.h
    + p.d * p.f * q.c - p.c * p.f * q.d + p.d * q.c * q.f - p.c * q.d * q.f
    + p.a * p.d * q.g + p.d * q.a * q.g - p.a * p.g * q.d - p.g * q.a * q.d
    + p.a * p.b * p.c * q.d - p.a * p.b * p.d * q.c + p.a * p.c * q.b * q.d
    - p.a * p.d * q.b * q.c + p.c * q.a * q.b * q.d - p.d * q.a * q.b * q.c

/-- **The right class-four commutator form**, in the coordinates of the last five columns. -/
def u6Comm4R (p q : SqU6 R) : R :=
  p.b * q.l - p.l * q.b + p.k * q.e - p.e * q.k + p.g * q.i - p.i * q.g
    + p.b * p.i * q.c - p.b * p.c * q.i + p.i * q.b * q.c - p.c * q.b * q.i
    + p.e * p.g * q.d - p.d * p.g * q.e + p.e * q.d * q.g - p.d * q.e * q.g
    + p.b * p.e * q.h + p.e * q.b * q.h - p.b * p.h * q.e - p.h * q.b * q.e
    + p.b * p.c * p.d * q.e - p.b * p.c * p.e * q.d + p.b * p.d * q.c * q.e
    - p.b * p.e * q.c * q.d + p.d * q.b * q.c * q.e - p.e * q.b * q.c * q.d

@[simp] theorem commP_m (p q : SqU6 R) : (commP p q).m = u6Comm4L p q := by
  simp only [commP, u6Comm4L, mul_a, mul_f, mul_j, mul_m,
    inv_a, inv_b, inv_c, inv_d, inv_f, inv_g, inv_h, inv_j, inv_k, inv_m]
  ring

@[simp] theorem commP_n (p q : SqU6 R) : (commP p q).n = u6Comm4R p q := by
  simp only [commP, u6Comm4R, mul_b, mul_g, mul_k, mul_n,
    inv_b, inv_c, inv_d, inv_e, inv_g, inv_h, inv_i, inv_k, inv_l, inv_n]
  ring

/-- **The class-five commutator form**, the `(1,6)`-coordinate of `[p, q]`.

Its linear head is the sum of the **four** complementary pairings

```text
p.a * q.n - p.n * q.a      abelian against class four
p.f * q.l - p.l * q.f      class two against class three
p.j * q.i - p.i * q.j      class three against class two
p.m * q.e - p.e * q.m      class four against abelian
```

(class four had three such pairings, class three two), followed by cubic, quartic and
quintic corrections in the lower columns.  The pairing `p.j * q.i - p.i * q.j`, which
couples a class-three coordinate against a class-two one, is the genuinely new one: it has
no class-four analogue, because at class four the class-three row is already the top row.
Section 5 is that observation cashed out. -/
def u6Comm5 (p q : SqU6 R) : R :=
  -(p.a * p.b * p.c * p.d * q.e) + p.a * p.b * p.c * p.e * q.d + p.a * p.b * p.c * q.i
    - p.a * p.b * p.d * q.c * q.e + p.a * p.b * p.e * q.c * q.d - p.a * p.b * p.e * q.h
    + p.a * p.b * p.h * q.e - p.a * p.b * p.i * q.c - p.a * p.b * q.l + p.a * p.c * q.b * q.i
    + p.a * p.d * p.g * q.e - p.a * p.d * q.b * q.c * q.e + p.a * p.d * q.e * q.g
    - p.a * p.e * p.g * q.d + p.a * p.e * q.b * q.c * q.d - p.a * p.e * q.b * q.h
    - p.a * p.e * q.d * q.g + p.a * p.e * q.k - p.a * p.g * q.i + p.a * p.h * q.b * q.e
    - p.a * p.i * q.b * q.c + p.a * p.i * q.g - p.a * p.k * q.e + p.a * p.l * q.b + p.a * q.n
    - p.b * q.a * q.l + p.c * p.d * p.f * q.e - p.c * p.e * p.f * q.d - p.c * p.f * q.i
    + p.c * q.a * q.b * q.i - p.c * q.f * q.i + p.d * p.f * q.c * q.e - p.d * p.j * q.e
    - p.d * q.a * q.b * q.c * q.e + p.d * q.a * q.e * q.g + p.d * q.c * q.e * q.f
    - p.d * q.e * q.j - p.e * p.f * q.c * q.d + p.e * p.f * q.h + p.e * p.j * q.d
    + p.e * q.a * q.b * q.c * q.d - p.e * q.a * q.b * q.h - p.e * q.a * q.d * q.g
    + p.e * q.a * q.k - p.e * q.c * q.d * q.f + p.e * q.d * q.j + p.e * q.f * q.h - p.e * q.m
    - p.f * p.h * q.e + p.f * p.i * q.c + p.f * q.l - p.g * q.a * q.i + p.h * q.a * q.b * q.e
    - p.h * q.e * q.f - p.i * q.a * q.b * q.c + p.i * q.a * q.g + p.i * q.c * q.f - p.i * q.j
    + p.j * q.i - p.k * q.a * q.e + p.l * q.a * q.b - p.l * q.f + p.m * q.e - p.n * q.a

@[simp] theorem commP_o (p q : SqU6 R) : (commP p q).o = u6Comm5 p q := by
  simp only [commP, u6Comm5, mul_a, mul_f, mul_j, mul_m, mul_o,
    inv_a, inv_b, inv_c, inv_d, inv_e, inv_f, inv_g, inv_h, inv_i,
    inv_j, inv_k, inv_l, inv_m, inv_n, inv_o]
  ring

@[simp] theorem conjP_a (p g : SqU6 R) : (conjP p g).a = p.a := by
  simp only [conjP, mul_a, inv_a]; ring

@[simp] theorem conjP_b (p g : SqU6 R) : (conjP p g).b = p.b := by
  simp only [conjP, mul_b, inv_b]; ring

@[simp] theorem conjP_c (p g : SqU6 R) : (conjP p g).c = p.c := by
  simp only [conjP, mul_c, inv_c]; ring

@[simp] theorem conjP_d (p g : SqU6 R) : (conjP p g).d = p.d := by
  simp only [conjP, mul_d, inv_d]; ring

@[simp] theorem conjP_e (p g : SqU6 R) : (conjP p g).e = p.e := by
  simp only [conjP, mul_e, inv_e]; ring

@[simp] theorem conjP_f (p g : SqU6 R) : (conjP p g).f = p.f + (g.b * p.a - g.a * p.b) := by
  simp only [conjP, mul_a, mul_f, inv_a, inv_f]; ring

@[simp] theorem conjP_g (p g : SqU6 R) : (conjP p g).g = p.g + (g.c * p.b - g.b * p.c) := by
  simp only [conjP, mul_b, mul_g, inv_b, inv_g]; ring

@[simp] theorem conjP_h (p g : SqU6 R) : (conjP p g).h = p.h + (g.d * p.c - g.c * p.d) := by
  simp only [conjP, mul_c, mul_h, inv_c, inv_h]; ring

@[simp] theorem conjP_i (p g : SqU6 R) : (conjP p g).i = p.i + (g.e * p.d - g.d * p.e) := by
  simp only [conjP, mul_d, mul_i, inv_d, inv_i]; ring

@[simp] theorem conjP_j (p g : SqU6 R) :
    (conjP p g).j = p.j + (g.a * g.b * p.c - g.a * g.c * p.b)
      + (g.c * p.f - g.a * p.g) + (g.g * p.a - g.f * p.c) := by
  simp only [conjP, mul_a, mul_f, mul_j, inv_a, inv_f, inv_j]
  ring

@[simp] theorem conjP_k (p g : SqU6 R) :
    (conjP p g).k = p.k + (g.b * g.c * p.d - g.b * g.d * p.c)
      + (g.d * p.g - g.b * p.h) + (g.h * p.b - g.g * p.d) := by
  simp only [conjP, mul_b, mul_g, mul_k, inv_b, inv_g, inv_k]
  ring

@[simp] theorem conjP_l (p g : SqU6 R) :
    (conjP p g).l = p.l + (g.c * g.d * p.e - g.c * g.e * p.d)
      + (g.e * p.h - g.c * p.i) + (g.i * p.c - g.h * p.e) := by
  simp only [conjP, mul_c, mul_h, mul_l, inv_c, inv_h, inv_l]
  ring

theorem conjP_m (p g : SqU6 R) :
    (conjP p g).m = p.m + (-(g.a * g.b * g.c * p.d) + g.a * g.b * g.d * p.c)
      + (g.a * g.b * p.h - g.a * g.d * p.g + g.c * g.f * p.d - g.d * g.f * p.c)
      + (g.a * g.g * p.d - g.a * g.h * p.b + g.d * p.j - g.f * p.h
        + g.h * p.f - g.j * p.d + g.k * p.a - g.a * p.k) := by
  simp only [conjP, mul_a, mul_f, mul_j, mul_m, inv_a, inv_f, inv_j, inv_m]
  ring

theorem conjP_n (p g : SqU6 R) :
    (conjP p g).n = p.n + (-(g.b * g.c * g.d * p.e) + g.b * g.c * g.e * p.d)
      + (g.b * g.c * p.i - g.b * g.e * p.h + g.d * g.g * p.e - g.e * g.g * p.d)
      + (g.b * g.h * p.e - g.b * g.i * p.c + g.e * p.k - g.g * p.i
        + g.i * p.g - g.k * p.e + g.l * p.b - g.b * p.l) := by
  simp only [conjP, mul_b, mul_g, mul_k, mul_n, inv_b, inv_g, inv_k, inv_n]
  ring

/-- Conjugation in class five: the `(1,6)`-coordinate moves by the mixed quintic shown. -/
theorem conjP_o (p g : SqU6 R) :
    (conjP p g).o = p.o
      + (g.a * g.b * g.c * g.d * p.e - g.a * g.b * g.c * g.e * p.d)
      + (-(g.a * g.b * g.c * p.i) + g.a * g.b * g.e * p.h - g.a * g.d * g.g * p.e
        + g.a * g.e * g.g * p.d - g.c * g.d * g.f * p.e + g.c * g.e * g.f * p.d)
      + (-(g.a * g.b * g.h * p.e) + g.a * g.b * g.i * p.c + g.a * g.b * p.l
        - g.a * g.e * p.k + g.a * g.g * p.i - g.a * g.i * p.g + g.a * g.k * p.e
        - g.a * g.l * p.b - g.a * p.n + g.c * g.f * p.i + g.d * g.j * p.e
        - g.e * g.f * p.h - g.e * g.j * p.d + g.e * p.m + g.f * g.h * p.e
        - g.f * g.i * p.c - g.f * p.l + g.i * p.j - g.j * p.i + g.l * p.f
        - g.m * p.e + g.n * p.a) := by
  simp only [conjP, mul_a, mul_f, mul_j, mul_m, mul_o,
    inv_a, inv_f, inv_j, inv_m, inv_o]
  ring

/-- **The left `U_5`-quotient**: forgetting the sixth column is a group hom onto `U_5` in
the coordinates `(a, b, c, d, f, g, h, j, k, m)`.  Every class-`<= 4` fact about the first
five columns of `U_6` is the corresponding `GradedFour` fact through this map. -/
def toU5L : SqU6 R →* SqU5 R where
  toFun p := ⟨p.a, p.b, p.c, p.d, p.f, p.g, p.h, p.j, p.k, p.m⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The right `U_5`-quotient**: forgetting the first row, coordinates
`(b, c, d, e, g, h, i, k, l, n)`. -/
def toU5R : SqU6 R →* SqU5 R where
  toFun p := ⟨p.b, p.c, p.d, p.e, p.g, p.h, p.i, p.k, p.l, p.n⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem toU5L_apply (p : SqU6 R) :
    toU5L p = ⟨p.a, p.b, p.c, p.d, p.f, p.g, p.h, p.j, p.k, p.m⟩ := rfl

@[simp] theorem toU5R_apply (p : SqU6 R) :
    toU5R p = ⟨p.b, p.c, p.d, p.e, p.g, p.h, p.i, p.k, p.l, p.n⟩ := rfl

/-- The class-five centre, as a monoid hom from the additive group of `R`. -/
def zHom6 : Multiplicative R →* SqU6 R where
  toFun z := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, toAdd z⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp] theorem zHom6_o (z : Multiplicative R) : (zHom6 z).o = toAdd z := rfl

/-- Central `(1,6)`-translations: multiplying by a `gamma_5`-element adds to the class-five
coordinate and moves nothing else. -/
theorem mul_center_o (p : SqU6 R) (w : R) :
    p * (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, w⟩ : SqU6 R)
      = ⟨p.a, p.b, p.c, p.d, p.e, p.f, p.g, p.h, p.i, p.j, p.k, p.l, p.m, p.n, p.o + w⟩ := by
  ext <;> simp

end SqU6

end U6Calculus

/-! ## 3 The class-five carrier as a pro-2 target, and the fifteen power laws -/

section U6ProP

namespace SqU6

variable {R : Type} [CommRing R]

/-- The underlying fifteen-tuple, as an equivalence. -/
def equivProd : SqU6 R ≃ R × R × R × R × R × R × R × R × R × R × R × R × R × R × R where
  toFun p := (p.a, p.b, p.c, p.d, p.e, p.f, p.g, p.h, p.i, p.j, p.k, p.l, p.m, p.n, p.o)
  invFun v := ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite R] : Finite (SqU6 R) := Finite.of_equiv _ equivProd.symm

/-- The cardinality of the class-five test group. -/
theorem nat_card [Finite R] : Nat.card (SqU6 R) = Nat.card R ^ 15 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

instance : TopologicalSpace (SqU6 R) := ⊥

instance : DiscreteTopology (SqU6 R) := ⟨rfl⟩

/-- **The class-five test group is pro-2** whenever the coefficient ring is a finite 2-ring:
its order is `(#R)^15`. -/
theorem isProP_two [Finite R] {mm : ℕ} (hR : Nat.card R = 2 ^ mm) : IsProP 2 (SqU6 R) :=
  isProP_of_isPGroup (IsPGroup.of_card (n := 15 * mm) (by rw [nat_card, hR, ← pow_mul, mul_comm]))

/-! ### The power laws

Five binomial layers now: the class-five coordinate carries `C(n,2)`, `C(n,3)`, `C(n,4)` and
`C(n,5)`, where class four had four layers and class three at most two. -/

private theorem choose_two_succ (n : ℕ) : ((n + 1).choose 2 : ℕ) = n.choose 2 + n := by
  rw [Nat.choose_succ_succ n 1, Nat.choose_one_right]
  show n + n.choose 2 = n.choose 2 + n
  omega

private theorem choose_three_succ (n : ℕ) :
    ((n + 1).choose 3 : ℕ) = n.choose 3 + n.choose 2 := by
  rw [Nat.choose_succ_succ n 2]
  show n.choose 2 + n.choose 3 = n.choose 3 + n.choose 2
  omega

private theorem choose_four_succ (n : ℕ) :
    ((n + 1).choose 4 : ℕ) = n.choose 4 + n.choose 3 := by
  rw [Nat.choose_succ_succ n 3]
  show n.choose 3 + n.choose 4 = n.choose 4 + n.choose 3
  omega

private theorem choose_five_succ (n : ℕ) :
    ((n + 1).choose 5 : ℕ) = n.choose 5 + n.choose 4 := by
  rw [Nat.choose_succ_succ n 4]
  show n.choose 4 + n.choose 5 = n.choose 5 + n.choose 4
  omega

@[simp] theorem pow_a (p : SqU6 R) (n : ℕ) : (p ^ n).a = n * p.a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_a, ih]; push_cast; ring

@[simp] theorem pow_b (p : SqU6 R) (n : ℕ) : (p ^ n).b = n * p.b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_b, ih]; push_cast; ring

@[simp] theorem pow_c (p : SqU6 R) (n : ℕ) : (p ^ n).c = n * p.c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_c, ih]; push_cast; ring

@[simp] theorem pow_d (p : SqU6 R) (n : ℕ) : (p ^ n).d = n * p.d := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_d, ih]; push_cast; ring

@[simp] theorem pow_e (p : SqU6 R) (n : ℕ) : (p ^ n).e = n * p.e := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_e, ih]; push_cast; ring

theorem pow_f (p : SqU6 R) (n : ℕ) :
    (p ^ n).f = n * p.f + (n.choose 2 : ℕ) * (p.a * p.b) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_f, ih, pow_a, choose_two_succ]; push_cast; ring

theorem pow_g (p : SqU6 R) (n : ℕ) :
    (p ^ n).g = n * p.g + (n.choose 2 : ℕ) * (p.b * p.c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_g, ih, pow_b, choose_two_succ]; push_cast; ring

theorem pow_h (p : SqU6 R) (n : ℕ) :
    (p ^ n).h = n * p.h + (n.choose 2 : ℕ) * (p.c * p.d) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_h, ih, pow_c, choose_two_succ]; push_cast; ring

theorem pow_i (p : SqU6 R) (n : ℕ) :
    (p ^ n).i = n * p.i + (n.choose 2 : ℕ) * (p.d * p.e) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_i, ih, pow_d, choose_two_succ]; push_cast; ring

/-- The first class-three power law: `SqU5.pow_h` through `toU5L`. -/
theorem pow_j (p : SqU6 R) (n : ℕ) :
    (p ^ n).j = n * p.j + (n.choose 2 : ℕ) * (p.a * p.g + p.f * p.c)
      + (n.choose 3 : ℕ) * (p.a * p.b * p.c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_j, ih, pow_a, pow_f, choose_two_succ, choose_three_succ]
    push_cast
    ring

theorem pow_k (p : SqU6 R) (n : ℕ) :
    (p ^ n).k = n * p.k + (n.choose 2 : ℕ) * (p.b * p.h + p.g * p.d)
      + (n.choose 3 : ℕ) * (p.b * p.c * p.d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_k, ih, pow_b, pow_g, choose_two_succ, choose_three_succ]
    push_cast
    ring

theorem pow_l (p : SqU6 R) (n : ℕ) :
    (p ^ n).l = n * p.l + (n.choose 2 : ℕ) * (p.c * p.i + p.h * p.e)
      + (n.choose 3 : ℕ) * (p.c * p.d * p.e) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_l, ih, pow_c, pow_h, choose_two_succ, choose_three_succ]
    push_cast
    ring

/-- The first class-four power law: `SqU5.pow_j` through `toU5L`. -/
theorem pow_m (p : SqU6 R) (n : ℕ) :
    (p ^ n).m = n * p.m + (n.choose 2 : ℕ) * (p.a * p.k + p.f * p.h + p.j * p.d)
      + (n.choose 3 : ℕ) * (p.a * p.b * p.h + p.a * p.d * p.g + p.c * p.d * p.f)
      + (n.choose 4 : ℕ) * (p.a * p.b * p.c * p.d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_m, ih, pow_a, pow_f, pow_j, choose_two_succ, choose_three_succ,
      choose_four_succ]
    push_cast
    ring

/-- …and the second, through `toU5R`. -/
theorem pow_n (p : SqU6 R) (n : ℕ) :
    (p ^ n).n = n * p.n + (n.choose 2 : ℕ) * (p.b * p.l + p.g * p.i + p.k * p.e)
      + (n.choose 3 : ℕ) * (p.b * p.c * p.i + p.b * p.e * p.h + p.d * p.e * p.g)
      + (n.choose 4 : ℕ) * (p.b * p.c * p.d * p.e) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_n, ih, pow_b, pow_g, pow_k, choose_two_succ, choose_three_succ,
      choose_four_succ]
    push_cast
    ring

/-- **The class-five power law**: the `(1,6)`-coordinate of `p^n` carries `C(n,2)` on the
four complementary products, `C(n,3)` on six cubic terms, `C(n,4)` on four quartic terms and
`C(n,5)` on the quintic abelian monomial.  A **fifth** binomial layer appears that class four
never saw. -/
theorem pow_o (p : SqU6 R) (n : ℕ) :
    (p ^ n).o = n * p.o + (n.choose 2 : ℕ) * (p.a * p.n + p.f * p.l + p.j * p.i + p.m * p.e)
      + (n.choose 3 : ℕ) * (p.a * p.b * p.l + p.a * p.e * p.k + p.a * p.g * p.i
          + p.c * p.f * p.i + p.d * p.e * p.j + p.e * p.f * p.h)
      + (n.choose 4 : ℕ) * (p.a * p.b * p.c * p.i + p.a * p.b * p.e * p.h
          + p.a * p.d * p.e * p.g + p.c * p.d * p.e * p.f)
      + (n.choose 5 : ℕ) * (p.a * p.b * p.c * p.d * p.e) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_o, ih, pow_a, pow_f, pow_j, pow_m, choose_two_succ, choose_three_succ,
      choose_four_succ, choose_five_succ]
    push_cast
    ring

end SqU6

end U6ProP

/-! ## 4 The lift, and `ℤ₂`-powers in the class-five carrier -/

section Lift

variable {R : Type} [CommRing R] [Finite R] {mm : ℕ} {h : ℕ}

/-- **The class-five test homomorphism** attached to a marking of `SqU6 R` killing the
relator: five characters of `D_sq(h)^ab`, four solutions of the class-two defect equations,
three of the class-three equations, two of the class-four equations and one of the class-five
equation, *is* a class-five quotient.  The verbatim transposition of `sqU5Hom`. -/
noncomputable def sqU6Hom (hR : Nat.card R = 2 ^ mm) (h : ℕ) (m : Fin (sqRank h) → SqU6 R)
    (hrel : sqRelWord m = 1) : ContinuousMonoidHom (DSq h : Type) (SqU6 R) :=
  sqLiftHom h (SqU6.isProP_two hR) m hrel

@[simp] theorem sqU6Hom_gen (hR : Nat.card R = 2 ^ mm) (m : Fin (sqRank h) → SqU6 R)
    (hrel : sqRelWord m = 1) (i : Fin (sqRank h)) :
    sqU6Hom hR h m hrel (sqGen h i) = m i :=
  sqLiftHom_gen _ _ _ _ i

/-- ⭐ **`ℤ₂`-powers in the class-five test group, with even class-four and class-five
obstructions.**

This is the class-five replacement for `SqU5.zpowZtwo_of_flatTwo`, and the step of the
`GradedFourHom` transposition that is **not** mechanical.  There are now **ten** obstructions,
one for each non-abelian coordinate, against six at class four and three at class three, and
the class-five coordinate carries **five** binomial layers.

Two things happen that class four did not have to face.

* The `C(n,3)`, `C(n,4)` and `C(n,5)` layers of the class-five coordinate are **not**
  independent conditions: they are exactly

  ```text
  X3 = l * (a*b) + i * (a*g + c*f) + e * (a*k + d*j + f*h)
  X4 = (a*b) * (c*i + e*h) + d*e * (a*g + c*f)
  X5 = (a*b) * c*d*e
  ```

  so the seven lower obstructions plus the **class-four** obstruction control all of them.
* Therefore an *even* class-four obstruction `2*wm` does not merely deform the class-four
  coordinate: it feeds `2 * e * wm` into the class-five `C(n,3)` layer, and `C(n,3) * (2*w)`
  is **not** a polynomial in `n` over `ℤ`.  Class four's repair (an even obstruction times
  `C(n,2)` is `(n^2 - n) * w`, which is) does not extend by itself.  What restores it is the
  next divisibility: `C(n,3) * (6*w) = (n^3 - 3n^2 + 2n) * w`, so the class-five cubic layer
  must be divisible by `6`, i.e. by `3` after the `2` is taken out.  That is the hypotheses
  `hwm`, `hwn`: both `g.e * wm` and `g.a * wn` are `3 * w3` for a common `w3`.

The two lemmas below are its `wm = wn = w3 = 0` and its `wm = wn = w2 = w3 = 0` cases. -/
theorem SqU6.zpowZtwo_of_evenFour (hQ : IsProP 2 (SqU6 R)) (pi : ℤ_[2] →+* R)
    (hpi : ∀ T : Set R, IsOpen (pi ⁻¹' T)) {g : SqU6 R} {wm wn w2 w3 : R}
    (hab : g.a * g.b = 0) (hbc : g.b * g.c = 0) (hcd : g.c * g.d = 0) (hde : g.d * g.e = 0)
    (hj : g.a * g.g + g.f * g.c = 0) (hk : g.b * g.h + g.g * g.d = 0)
    (hl : g.c * g.i + g.h * g.e = 0)
    (hm : g.a * g.k + g.f * g.h + g.j * g.d = 2 * wm)
    (hn : g.b * g.l + g.g * g.i + g.k * g.e = 2 * wn)
    (ho : g.a * g.n + g.f * g.l + g.j * g.i + g.m * g.e = 2 * w2)
    (hwm : g.e * wm = 3 * w3) (hwn : g.a * wn = 3 * w3) (u : ℤ_[2]) :
    zpowZtwo hQ g u
      = ⟨pi u * g.a, pi u * g.b, pi u * g.c, pi u * g.d, pi u * g.e,
          pi u * g.f, pi u * g.g, pi u * g.h, pi u * g.i,
          pi u * g.j, pi u * g.k, pi u * g.l,
          pi u * g.m + (pi u * pi u - pi u) * wm,
          pi u * g.n + (pi u * pi u - pi u) * wn,
          pi u * g.o + (pi u * pi u - pi u) * w2
            + (pi u * pi u * pi u - 3 * (pi u * pi u) + 2 * pi u) * w3⟩ := by
  set phi : Multiplicative ℤ_[2] →* SqU6 R :=
    { toFun := fun z => ⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c,
        pi (toAdd z) * g.d, pi (toAdd z) * g.e, pi (toAdd z) * g.f, pi (toAdd z) * g.g,
        pi (toAdd z) * g.h, pi (toAdd z) * g.i, pi (toAdd z) * g.j, pi (toAdd z) * g.k,
        pi (toAdd z) * g.l,
        pi (toAdd z) * g.m + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * wm,
        pi (toAdd z) * g.n + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * wn,
        pi (toAdd z) * g.o + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * w2
          + (pi (toAdd z) * pi (toAdd z) * pi (toAdd z) - 3 * (pi (toAdd z) * pi (toAdd z))
            + 2 * pi (toAdd z)) * w3⟩
      map_one' := by ext <;> simp
      map_mul' := fun z y => by
        have hadd : pi (toAdd (z * y)) = pi (toAdd z) + pi (toAdd y) := by
          rw [show toAdd (z * y) = toAdd z + toAdd y from rfl, map_add]
        ext
        · simp only [SqU6.mul_a]; rw [hadd]; ring
        · simp only [SqU6.mul_b]; rw [hadd]; ring
        · simp only [SqU6.mul_c]; rw [hadd]; ring
        · simp only [SqU6.mul_d]; rw [hadd]; ring
        · simp only [SqU6.mul_e]; rw [hadd]; ring
        · simp only [SqU6.mul_f]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hab
        · simp only [SqU6.mul_g]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hbc
        · simp only [SqU6.mul_h]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hcd
        · simp only [SqU6.mul_i]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hde
        · simp only [SqU6.mul_j]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hj
        · simp only [SqU6.mul_k]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hk
        · simp only [SqU6.mul_l]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hl
        · simp only [SqU6.mul_m]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hm
        · simp only [SqU6.mul_n]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hn
        · simp only [SqU6.mul_o]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * ho
            + (-(pi (toAdd z) * pi (toAdd y) * pi (toAdd y))
              + pi (toAdd z) * pi (toAdd y)) * hwn
            + (-(pi (toAdd z) * pi (toAdd z) * pi (toAdd y))
              + pi (toAdd z) * pi (toAdd y)) * hwm } with hphi
  have hcont : Continuous phi := by
    refine IsLocallyConstant.continuous fun s => ?_
    show IsOpen ((fun z : Multiplicative ℤ_[2] =>
      (⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c,
        pi (toAdd z) * g.d, pi (toAdd z) * g.e, pi (toAdd z) * g.f, pi (toAdd z) * g.g,
        pi (toAdd z) * g.h, pi (toAdd z) * g.i, pi (toAdd z) * g.j, pi (toAdd z) * g.k,
        pi (toAdd z) * g.l,
        pi (toAdd z) * g.m + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * wm,
        pi (toAdd z) * g.n + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * wn,
        pi (toAdd z) * g.o + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * w2
          + (pi (toAdd z) * pi (toAdd z) * pi (toAdd z) - 3 * (pi (toAdd z) * pi (toAdd z))
            + 2 * pi (toAdd z)) * w3⟩ : SqU6 R)) ⁻¹' s)
    have hfact : (fun z : Multiplicative ℤ_[2] =>
        (⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c,
          pi (toAdd z) * g.d, pi (toAdd z) * g.e, pi (toAdd z) * g.f, pi (toAdd z) * g.g,
          pi (toAdd z) * g.h, pi (toAdd z) * g.i, pi (toAdd z) * g.j, pi (toAdd z) * g.k,
          pi (toAdd z) * g.l,
          pi (toAdd z) * g.m + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * wm,
          pi (toAdd z) * g.n + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * wn,
          pi (toAdd z) * g.o + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * w2
            + (pi (toAdd z) * pi (toAdd z) * pi (toAdd z) - 3 * (pi (toAdd z) * pi (toAdd z))
              + 2 * pi (toAdd z)) * w3⟩ : SqU6 R)) ⁻¹' s
        = toAdd ⁻¹' (pi ⁻¹' {r : R | (⟨r * g.a, r * g.b, r * g.c, r * g.d, r * g.e, r * g.f,
            r * g.g, r * g.h, r * g.i, r * g.j, r * g.k, r * g.l,
            r * g.m + (r * r - r) * wm, r * g.n + (r * r - r) * wn,
            r * g.o + (r * r - r) * w2 + (r * r * r - 3 * (r * r) + 2 * r) * w3⟩ :
              SqU6 R) ∈ s}) := rfl
    rw [hfact]
    exact (hpi _).preimage continuous_toAdd
  have hone : phi (ofAdd (1 : ℤ_[2])) = g := by
    show (⟨pi 1 * g.a, pi 1 * g.b, pi 1 * g.c, pi 1 * g.d, pi 1 * g.e, pi 1 * g.f,
      pi 1 * g.g, pi 1 * g.h, pi 1 * g.i, pi 1 * g.j, pi 1 * g.k, pi 1 * g.l,
      pi 1 * g.m + (pi 1 * pi 1 - pi 1) * wm, pi 1 * g.n + (pi 1 * pi 1 - pi 1) * wn,
      pi 1 * g.o + (pi 1 * pi 1 - pi 1) * w2
        + (pi 1 * pi 1 * pi 1 - 3 * (pi 1 * pi 1) + 2 * pi 1) * w3⟩ : SqU6 R) = g
    rw [map_one]
    ext <;> ring
  have := zpowZtwoHom_unique hQ hcont u
  rw [hone] at this
  exact this.symm

/-- **`ℤ₂`-powers in the class-five test group, with an even class-five obstruction**: the
direct analogue of `SqU5.zpowZtwo_of_flatTwo`, with **nine** flat conditions instead of five.
Note what has moved: at class four the class-four obstruction was allowed to be merely even;
at class five it must vanish on the nose, because it also drives the class-five `C(n,3)`
layer.  `SqU6.zpowZtwo_of_evenFour` is the lemma that buys the even case back. -/
theorem SqU6.zpowZtwo_of_flatTwo (hQ : IsProP 2 (SqU6 R)) (pi : ℤ_[2] →+* R)
    (hpi : ∀ T : Set R, IsOpen (pi ⁻¹' T)) {g : SqU6 R} {w : R}
    (hab : g.a * g.b = 0) (hbc : g.b * g.c = 0) (hcd : g.c * g.d = 0) (hde : g.d * g.e = 0)
    (hj : g.a * g.g + g.f * g.c = 0) (hk : g.b * g.h + g.g * g.d = 0)
    (hl : g.c * g.i + g.h * g.e = 0)
    (hm : g.a * g.k + g.f * g.h + g.j * g.d = 0)
    (hn : g.b * g.l + g.g * g.i + g.k * g.e = 0)
    (ho : g.a * g.n + g.f * g.l + g.j * g.i + g.m * g.e = 2 * w) (u : ℤ_[2]) :
    zpowZtwo hQ g u
      = ⟨pi u * g.a, pi u * g.b, pi u * g.c, pi u * g.d, pi u * g.e,
          pi u * g.f, pi u * g.g, pi u * g.h, pi u * g.i,
          pi u * g.j, pi u * g.k, pi u * g.l, pi u * g.m, pi u * g.n,
          pi u * g.o + (pi u * pi u - pi u) * w⟩ := by
  rw [SqU6.zpowZtwo_of_evenFour hQ pi hpi hab hbc hcd hde hj hk hl (wm := 0) (wn := 0)
    (w3 := 0) (by rw [hm]; ring) (by rw [hn]; ring) ho (by ring) (by ring)]
  ext <;> ring

/-- **`ℤ₂`-powers in the class-five test group, flat base**: **ten** conditions, one for each
non-abelian coordinate, against six at class four and three at class three.  These are exactly
the conditions under which `n ↦ gⁿ` is `R`-linear, by `SqU6.pow_f` through `SqU6.pow_o`. -/
theorem SqU6.zpowZtwo_of_flat (hQ : IsProP 2 (SqU6 R)) (pi : ℤ_[2] →+* R)
    (hpi : ∀ T : Set R, IsOpen (pi ⁻¹' T)) {g : SqU6 R}
    (hab : g.a * g.b = 0) (hbc : g.b * g.c = 0) (hcd : g.c * g.d = 0) (hde : g.d * g.e = 0)
    (hj : g.a * g.g + g.f * g.c = 0) (hk : g.b * g.h + g.g * g.d = 0)
    (hl : g.c * g.i + g.h * g.e = 0)
    (hm : g.a * g.k + g.f * g.h + g.j * g.d = 0)
    (hn : g.b * g.l + g.g * g.i + g.k * g.e = 0)
    (ho : g.a * g.n + g.f * g.l + g.j * g.i + g.m * g.e = 0) (u : ℤ_[2]) :
    zpowZtwo hQ g u
      = ⟨pi u * g.a, pi u * g.b, pi u * g.c, pi u * g.d, pi u * g.e,
          pi u * g.f, pi u * g.g, pi u * g.h, pi u * g.i,
          pi u * g.j, pi u * g.k, pi u * g.l, pi u * g.m, pi u * g.n, pi u * g.o⟩ := by
  rw [SqU6.zpowZtwo_of_flatTwo hQ pi hpi hab hbc hcd hde hj hk hl hm hn (w := 0)
    (by rw [ho]; ring)]
  ext <;> ring

end Lift

/-! ### The class-five gate -/

section Gate

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐ **The class-five gate.**  Every frame of `D_sq h` that kills the relator has an image
tuple killing the relator in **every** class-five test group.  One `rw`, and it is what turns
tuple-level statements about `SqU6 R` into statements about continuous homomorphisms. -/
theorem sqU6Balance (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    sqRelWord (fun i => Phi (n i)) = 1 := by
  rw [← map_sqRelWord Phi n, hn, map_one]

/-- The gate at the standard frame. -/
theorem sqU6Balance_gen (Phi : ContinuousMonoidHom (DSq h : Type) (SqU6 R)) :
    sqRelWord (fun i => Phi (sqGen h i)) = 1 :=
  sqU6Balance Phi _ (dsq_relation h)

end Gate

/-! ## 5 The relator in the class-five carrier, and what the top row sees -/

section RelWord

variable {R : Type} [CommRing R] {h : ℕ}

/-- The abelian coordinates of a product of `gamma_2`-elements all vanish.  Unlike class
three, `gamma_2` is **not** abelian here: `SqU6.mul_m`, `SqU6.mul_n` and `SqU6.mul_o` keep
cross terms on `gamma_2`, so only the coordinates below class four are plain sums. -/
private theorem SqU6.prod_gaTwo_abelian (l : List (SqU6 R))
    (hl : ∀ p ∈ l, p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.e = 0) :
    l.prod.a = 0 ∧ l.prod.b = 0 ∧ l.prod.c = 0 ∧ l.prod.d = 0 ∧ l.prod.e = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons p t ih =>
    obtain ⟨hpa, hpb, hpc, hpd, hpe⟩ := hl p List.mem_cons_self
    obtain ⟨hta, htb, htc, htd, hte⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [List.prod_cons]
    exact ⟨by rw [SqU6.mul_a, hpa, hta, add_zero], by rw [SqU6.mul_b, hpb, htb, add_zero],
      by rw [SqU6.mul_c, hpc, htc, add_zero], by rw [SqU6.mul_d, hpd, htd, add_zero],
      by rw [SqU6.mul_e, hpe, hte, add_zero]⟩

/-- …and the fourth class-two coordinate is the plain sum. -/
private theorem SqU6.prod_gaTwo_i (l : List (SqU6 R))
    (hl : ∀ p ∈ l, p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.e = 0) :
    l.prod.i = (l.map SqU6.i).sum := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨hpa, hpb, hpc, hpd, hpe⟩ := hl p List.mem_cons_self
    have hti := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [List.prod_cons, SqU6.mul_i, hpd, zero_mul, add_zero, hti, List.map_cons,
      List.sum_cons]

@[simp] theorem SqU6.handleWord_a (u v : Fin h → SqU6 R) : (handleWord u v).a = 0 :=
  (SqU6.prod_gaTwo_abelian _ (by simp)).1

@[simp] theorem SqU6.handleWord_b (u v : Fin h → SqU6 R) : (handleWord u v).b = 0 :=
  (SqU6.prod_gaTwo_abelian _ (by simp)).2.1

@[simp] theorem SqU6.handleWord_c (u v : Fin h → SqU6 R) : (handleWord u v).c = 0 :=
  (SqU6.prod_gaTwo_abelian _ (by simp)).2.2.1

@[simp] theorem SqU6.handleWord_d (u v : Fin h → SqU6 R) : (handleWord u v).d = 0 :=
  (SqU6.prod_gaTwo_abelian _ (by simp)).2.2.2.1

@[simp] theorem SqU6.handleWord_e (u v : Fin h → SqU6 R) : (handleWord u v).e = 0 :=
  (SqU6.prod_gaTwo_abelian _ (by simp)).2.2.2.2

/-- ⭐ **The handle block's outermost class-two pairing.**  This is the invariant the
class-five top row meets, and the one nothing below class five can see. -/
theorem SqU6.handleWord_i (u v : Fin h → SqU6 R) :
    (handleWord u v).i = ∑ j, ((u j).d * (v j).e - (v j).d * (u j).e) := by
  rw [handleWord, SqU6.prod_gaTwo_i _ (by simp), Fin.sum_univ_def]
  simp [List.map_map, Function.comp_def, sub_eq_add_neg, mul_comm]

/-- The first abelian coordinate of the core word: the relator vector `-4x + 2y`. -/
@[simp] theorem SqU6.sqWord_a (s x y : SqU6 R) : (sqWord s x y).a = -4 * x.a + 2 * y.a := by
  simp only [sqWord, SqU6.mul_a, SqU6.inv_a, SqU6.conjP_a, SqU6.pow_a, SqU6.commP_a]
  push_cast
  ring

@[simp] theorem SqU6.sqWord_b (s x y : SqU6 R) : (sqWord s x y).b = -4 * x.b + 2 * y.b := by
  simp only [sqWord, SqU6.mul_b, SqU6.inv_b, SqU6.conjP_b, SqU6.pow_b, SqU6.commP_b]
  push_cast
  ring

@[simp] theorem SqU6.sqWord_c (s x y : SqU6 R) : (sqWord s x y).c = -4 * x.c + 2 * y.c := by
  simp only [sqWord, SqU6.mul_c, SqU6.inv_c, SqU6.conjP_c, SqU6.pow_c, SqU6.commP_c]
  push_cast
  ring

@[simp] theorem SqU6.sqWord_d (s x y : SqU6 R) : (sqWord s x y).d = -4 * x.d + 2 * y.d := by
  simp only [sqWord, SqU6.mul_d, SqU6.inv_d, SqU6.conjP_d, SqU6.pow_d, SqU6.commP_d]
  push_cast
  ring

@[simp] theorem SqU6.sqWord_e (s x y : SqU6 R) : (sqWord s x y).e = -4 * x.e + 2 * y.e := by
  simp only [sqWord, SqU6.mul_e, SqU6.inv_e, SqU6.conjP_e, SqU6.pow_e, SqU6.commP_e]
  push_cast
  ring

/-- The five abelian rows of the relator: the relator vector, exactly as at every lower
class. -/
@[simp] theorem SqU6.sqRelWord_a (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).a = -4 * (m 1).a + 2 * (m 2).a := by
  rw [sqRelWord, SqU6.mul_a, SqU6.sqWord_a, SqU6.handleWord_a, add_zero]

@[simp] theorem SqU6.sqRelWord_b (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).b = -4 * (m 1).b + 2 * (m 2).b := by
  rw [sqRelWord, SqU6.mul_b, SqU6.sqWord_b, SqU6.handleWord_b, add_zero]

@[simp] theorem SqU6.sqRelWord_c (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).c = -4 * (m 1).c + 2 * (m 2).c := by
  rw [sqRelWord, SqU6.mul_c, SqU6.sqWord_c, SqU6.handleWord_c, add_zero]

@[simp] theorem SqU6.sqRelWord_d (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).d = -4 * (m 1).d + 2 * (m 2).d := by
  rw [sqRelWord, SqU6.mul_d, SqU6.sqWord_d, SqU6.handleWord_d, add_zero]

@[simp] theorem SqU6.sqRelWord_e (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).e = -4 * (m 1).e + 2 * (m 2).e := by
  rw [sqRelWord, SqU6.mul_e, SqU6.sqWord_e, SqU6.handleWord_e, add_zero]

/-- ⭐ **The fourteen lower rows are `GradedFour`'s rows**, through the two `U_5`-quotients.
Nothing below the class-five coordinate is new: `toU5L` covers `(a,b,c,d,f,g,h,j,k,m)` and
`toU5R` covers `(b,c,d,e,g,h,i,k,l,n)`, and between them every coordinate but `o`. -/
theorem SqU6.toU5L_sqRelWord (m : Fin (sqRank h) → SqU6 R) :
    SqU6.toU5L (sqRelWord m) = sqRelWord (fun i => SqU6.toU5L (m i)) :=
  map_sqRelWord _ m

theorem SqU6.toU5R_sqRelWord (m : Fin (sqRank h) → SqU6 R) :
    SqU6.toU5R (sqRelWord m) = sqRelWord (fun i => SqU6.toU5R (m i)) :=
  map_sqRelWord _ m

/-- **The class-three quotient of the first four columns**, `toU4L ∘ toU5L` spelled out; it is
what lets the committed `sqU4Core` supply the class-three row of the class-five core word. -/
def SqU6.toU4LL : SqU6 R →* SqU4 R where
  toFun p := ⟨p.a, p.b, p.c, p.f, p.g, p.j⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem SqU6.toU4LL_apply (p : SqU6 R) :
    SqU6.toU4LL p = ⟨p.a, p.b, p.c, p.f, p.g, p.j⟩ := rfl

/-- The first class-two row of the core word. -/
theorem SqU6.sqWord_f (s x y : SqU6 R) :
    (sqWord s x y).f = -4 * x.f + 2 * y.f
      + (s.a * x.b - s.b * x.a + 10 * (x.a * x.b) - 8 * (x.a * y.b) + y.a * y.b) := by
  simp only [sqWord, SqU6.mul_a, SqU6.mul_f, SqU6.inv_a, SqU6.inv_b, SqU6.inv_f,
    SqU6.conjP_a, SqU6.conjP_b, SqU6.conjP_f, SqU6.pow_a, SqU6.pow_b, SqU6.pow_f,
    SqU6.commP_b, SqU6.commP_f]
  norm_num
  ring

/-- ⭐ **The class-three row of the core word is the committed class-three core**, through
`toU4LL`.  Nothing is re-derived: `GradedThree`'s `sqU4Core` is the class-three content at
every class above three. -/
theorem SqU6.sqWord_j (s x y : SqU6 R) :
    (sqWord s x y).j = -4 * x.j + 2 * y.j
      + sqU4Core (SqU6.toU4LL s) (SqU6.toU4LL x) (SqU6.toU4LL y) := by
  have hnat : SqU6.toU4LL (sqWord s x y)
      = sqWord (SqU6.toU4LL s) (SqU6.toU4LL x) (SqU6.toU4LL y) := map_sqWord _ s x y
  have hh := congrArg SqU4.f hnat
  rw [SqU4.sqWord_f] at hh
  exact hh

/-- ⭐⭐ **How the handle block enters the class-four row, and the only way it can.**  Through
its own class-four coordinate and through its class-three and third class-two coordinates,
paired against the core word's two outermost class-`<= 2` coordinates.  This is
`GradedFourCleared`'s `sqRelWord_mirTuple_j` for an arbitrary marking. -/
theorem SqU6.sqRelWord_m (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).m
      = (sqWord (m 0) (m 1) (m 2)).m
        + (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).m
        + (sqWord (m 0) (m 1) (m 2)).a
          * (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).k
        + (sqWord (m 0) (m 1) (m 2)).f
          * (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).h := by
  rw [sqRelWord, SqU6.mul_m, SqU6.handleWord_d, mul_zero, add_zero]

/-- ⭐⭐ **How the handle block enters the class-five row.**  Three couplings instead of two,
and the third is the new one: the core word's **class-three** coordinate paired against the
handle block's outermost class-two coordinate.  At class four the class-three coordinate is
already the top row, so this coupling has no class-four analogue; section 5's headline is
exactly this term refusing to vanish. -/
theorem SqU6.sqRelWord_o (m : Fin (sqRank h) → SqU6 R) :
    (sqRelWord m).o
      = (sqWord (m 0) (m 1) (m 2)).o
        + (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).o
        + (sqWord (m 0) (m 1) (m 2)).a
          * (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).n
        + (sqWord (m 0) (m 1) (m 2)).f
          * (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).l
        + (sqWord (m 0) (m 1) (m 2)).j
          * (handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i := by
  rw [sqRelWord, SqU6.mul_o, SqU6.handleWord_e, mul_zero, add_zero]

end RelWord

/-! ### The sigma dressing and its response -/

section SigmaFive

variable {R : Type} [CommRing R] {h : ℕ}

/-- **The sigma-dressed tuple** at class five: the marking with the sigma slot multiplied by
`v` on the right and every other slot untouched.  `GradedSigmaFour.sigFourDress` one level
up. -/
def sigFiveDress (m : Fin (sqRank h) → SqU6 R) (v : SqU6 R) : Fin (sqRank h) → SqU6 R :=
  fun i => if (i : ℕ) = 0 then m i * v else m i

variable {m m' : Fin (sqRank h) → SqU6 R} {v : SqU6 R}

@[simp] theorem sigFiveDress_zero : sigFiveDress m v 0 = m 0 * v := by
  simp only [sigFiveDress, sqVal_zero]
  norm_num

theorem sigFiveDress_ne {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 0) : sigFiveDress m v i = m i :=
  if_neg hi

theorem sigFiveDress_one : sigFiveDress m v 1 = m 1 :=
  sigFiveDress_ne (by rw [sqVal_one]; omega)

theorem sigFiveDress_two : sigFiveDress m v 2 = m 2 :=
  sigFiveDress_ne (by rw [sqVal_two]; omega)

theorem sigFiveDress_handleU (j : Fin h) :
    sigFiveDress m v (sqHandleIdxU j) = m (sqHandleIdxU j) :=
  sigFiveDress_ne (by rw [sqHandleIdxU_val]; omega)

theorem sigFiveDress_handleV (j : Fin h) :
    sigFiveDress m v (sqHandleIdxV j) = m (sqHandleIdxV j) :=
  sigFiveDress_ne (by rw [sqHandleIdxV_val]; omega)

/-- A sigma dressing does not move the first class-two row of the core word, on the
`nu'`-gauge.  This is the whole content of the class-four blindness theorem, and it stays
true at class five. -/
theorem SqU6.sqWord_f_dress (s v x y : SqU6 R) (hxb : x.b = 0) (hvb : v.b = 0) :
    (sqWord (s * v) x y).f = (sqWord s x y).f := by
  rw [SqU6.sqWord_f, SqU6.sqWord_f, SqU6.mul_a, SqU6.mul_b, hxb, hvb]
  ring

/-- ⭐ **A sigma dressing DOES move the class-three row of the core word**, on the same gauge,
and this is the closed form of the move.  The class-four blindness theorem had no use for this
row, because at class four it is the top row and the handle block cannot multiply into it. -/
theorem SqU6.sqWord_j_dress (s v x y : SqU6 R) (hxb : x.b = 0) (hyb : y.b = 0)
    (hvb : v.b = 0) :
    (sqWord (s * v) x y).j - (sqWord s x y).j
      = v.a * x.g - v.g * x.a + v.f * x.c - v.c * x.f
        - s.b * (v.a * x.c + v.c * x.a) := by
  rw [SqU6.sqWord_j, SqU6.sqWord_j, map_mul]
  simp only [SqU6.toU4LL_apply, sqU4Core, SqU4.mul_a, SqU4.mul_b, SqU4.mul_c, SqU4.mul_d,
    SqU4.mul_e, hxb, hyb, hvb]
  ring

/-- ⭐⭐ **The class-four row of the relator is blind to the handle block**, at class five as
at class four: the response of the `m`-row to a sigma dressing is a functional of the core
slots alone.  This is `GradedFourCleared.sqRelWord_sigFourDress_handle_blind` recovered inside
the class-five carrier, at an arbitrary sigma slot rather than the committed one, and it is
the control against which the next theorem is read. -/
theorem SqU6.sqRelWord_sigFiveDress_handle_blind_four
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hxb : (m 1).b = 0) (hvb : v.b = 0) :
    (sqRelWord (sigFiveDress m v)).m - (sqRelWord m).m
      = (sqRelWord (sigFiveDress m' v)).m - (sqRelWord m').m := by
  have key : ∀ mm : Fin (sqRank h) → SqU6 R, mm 1 = m 1 → mm 2 = m 2 →
      (sqRelWord (sigFiveDress mm v)).m - (sqRelWord mm).m
        = (sqWord (mm 0 * v) (m 1) (m 2)).m - (sqWord (mm 0) (m 1) (m 2)).m := by
    intro mm hm1 hm2
    rw [SqU6.sqRelWord_m, SqU6.sqRelWord_m, sigFiveDress_zero, sigFiveDress_one,
      sigFiveDress_two, funext (sigFiveDress_handleU (m := mm) (v := v)),
      funext (sigFiveDress_handleV (m := mm) (v := v)), hm1, hm2]
    rw [show (sqWord (mm 0 * v) (m 1) (m 2)).a = (sqWord (mm 0) (m 1) (m 2)).a by
      rw [SqU6.sqWord_a, SqU6.sqWord_a],
      SqU6.sqWord_f_dress _ _ _ _ hxb hvb]
    ring
  rw [key m rfl rfl, key m' h1 h2, h0]

/-- ⭐⭐ **The class-five response of the relator's top row**: the core word's own class-five
response, plus the **class-three** sigma response paired against the handle block's outermost
class-two coordinate.  The second summand is the class-five reading of the handle block. -/
theorem SqU6.sqRelWord_sigFiveDress_o
    (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    (sqRelWord (sigFiveDress m v)).o - (sqRelWord m).o
      = ((sqWord (m 0 * v) (m 1) (m 2)).o - (sqWord (m 0) (m 1) (m 2)).o)
        + (v.a * (m 1).g - v.g * (m 1).a + v.f * (m 1).c - v.c * (m 1).f
            - (m 0).b * (v.a * (m 1).c + v.c * (m 1).a))
          * (handleWord (fun j => m (sqHandleIdxU j))
              (fun j => m (sqHandleIdxV j))).i := by
  rw [SqU6.sqRelWord_o, SqU6.sqRelWord_o, sigFiveDress_zero, sigFiveDress_one,
    sigFiveDress_two, funext (sigFiveDress_handleU (m := m) (v := v)),
    funext (sigFiveDress_handleV (m := m) (v := v))]
  rw [show (sqWord (m 0 * v) (m 1) (m 2)).a = (sqWord (m 0) (m 1) (m 2)).a by
    rw [SqU6.sqWord_a, SqU6.sqWord_a], SqU6.sqWord_f_dress _ _ _ _ hxb hvb]
  linear_combination (handleWord (fun j => m (sqHandleIdxU j))
    (fun j => m (sqHandleIdxV j))).i * SqU6.sqWord_j_dress (m 0) v (m 1) (m 2) hxb hyb hvb

/-- ⭐⭐ **The sharp form: what the class-five top row sees of the handle block.**  For two
markings with the *same* core slots and *arbitrary, different* handle blocks, the difference
of the two sigma responses is exactly the class-three sigma response times the difference of
the blocks' outermost class-two pairings.  At class four the corresponding weight is the
class-two response, which the `nu'`-gauge kills, which is why the class-four bit is blind; at
class five the weight is the class-three response, which the gauge does **not** kill. -/
theorem SqU6.sqRelWord_sigFiveDress_handle_visible
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hxb : (m 1).b = 0) (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    ((sqRelWord (sigFiveDress m v)).o - (sqRelWord m).o)
        - ((sqRelWord (sigFiveDress m' v)).o - (sqRelWord m').o)
      = (v.a * (m 1).g - v.g * (m 1).a + v.f * (m 1).c - v.c * (m 1).f
          - (m 0).b * (v.a * (m 1).c + v.c * (m 1).a))
        * ((handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))).i
          - (handleWord (fun j => m' (sqHandleIdxU j)) (fun j => m' (sqHandleIdxV j))).i) := by
  rw [SqU6.sqRelWord_sigFiveDress_o hxb hyb hvb,
    SqU6.sqRelWord_sigFiveDress_o (m := m') (v := v) (by rw [h1]; exact hxb)
      (by rw [h2]; exact hyb) hvb, h0, h1, h2]
  ring

end SigmaFive

/-! ### The live class-five point, and the witness that the reading is not blind -/

section FiveWitness

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

variable (R h j) in
/-- **The one-handle-live class-five tuple**: the three core slots, the `j`-th handle pair
carrying `(U, V)`, every other handle letter `1`.  `GradedFourMirror.mirTuple` one level up. -/
def fiveTuple (S X Y U V : SqU6 R) : Fin (sqRank h) → SqU6 R :=
  fun i =>
    if (i : ℕ) = 0 then S else
    if (i : ℕ) = 1 then X else
    if (i : ℕ) = 2 then Y else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then U else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then V else 1

variable {S X Y U V : SqU6 R}

@[simp] theorem fiveTuple_zero : fiveTuple R h j S X Y U V 0 = S := by
  simp only [fiveTuple, sqVal_zero]; norm_num

@[simp] theorem fiveTuple_one : fiveTuple R h j S X Y U V 1 = X := by
  simp only [fiveTuple, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega)]
  norm_num

@[simp] theorem fiveTuple_two : fiveTuple R h j S X Y U V 2 = Y := by
  simp only [fiveTuple, sqVal_two, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  norm_num

@[simp] theorem fiveTuple_handleU : fiveTuple R h j S X Y U V (sqHandleIdxU j) = U := by
  simp only [fiveTuple]
  rw [if_neg (by rw [sqHandleIdxU_val]; omega), if_neg (by rw [sqHandleIdxU_val]; omega),
    if_neg (by rw [sqHandleIdxU_val]; omega)]
  simp

@[simp] theorem fiveTuple_handleV : fiveTuple R h j S X Y U V (sqHandleIdxV j) = V := by
  simp only [fiveTuple]
  rw [if_neg (by rw [sqHandleIdxV_val]; omega), if_neg (by rw [sqHandleIdxV_val]; omega),
    if_neg (by rw [sqHandleIdxV_val]; omega),
    if_neg (by rw [sqHandleIdxU_val, sqHandleIdxV_val]; omega)]
  simp

theorem fiveTuple_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    fiveTuple R h j S X Y U V (sqHandleIdxU j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [fiveTuple, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

theorem fiveTuple_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    fiveTuple R h j S X Y U V (sqHandleIdxV j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [fiveTuple, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- The handle block of a one-handle-live tuple **is** the single surviving commutator, at
every handle count. -/
theorem fiveTuple_handleWord :
    handleWord (fun j' => fiveTuple R h j S X Y U V (sqHandleIdxU j'))
        (fun j' => fiveTuple R h j S X Y U V (sqHandleIdxV j')) = commP U V := by
  rw [handleWord_eq_single _ _ j (fun j' hj' => by
    rw [fiveTuple_handleU_ne hj', fiveTuple_handleV_ne hj']
    simp [commP]), fiveTuple_handleU, fiveTuple_handleV]

/-- **The relator of a one-handle-live class-five tuple**, at every handle count: the core
word times the single surviving commutator. -/
theorem sqRelWord_fiveTuple :
    sqRelWord (fiveTuple R h j S X Y U V) = sqWord S X Y * commP U V := by
  rw [sqRelWord, fiveTuple_zero, fiveTuple_one, fiveTuple_two, fiveTuple_handleWord]

/-! ### The concrete point over `ZMod 8` -/

/-- The `x₀`-slot: the second class-two column alone.  It is on the `nu'`-gauge, and it is
what makes the class-three sigma response live. -/
def fiveX : SqU6 (ZMod 8) := ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x₁`-slot: `g = 2` is forced by the second class-two row, and `i = 3`, `n = 1` are the
staged solve of the remaining rows against the live block. -/
def fiveY : SqU6 (ZMod 8) := ⟨0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 1, 0⟩

/-- The `u`-letter of the live handle: the fourth abelian column alone. -/
def fiveU : SqU6 (ZMod 8) := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `v`-letter of the live handle: twice the fifth abelian column.  Its commutator with
`fiveU` has `i`-coordinate `2`, which is exactly the invariant the class-five top row meets. -/
def fiveV : SqU6 (ZMod 8) := ⟨0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The sigma dressing: the first abelian column alone, `nu'`-trivial. -/
def fiveDress : SqU6 (ZMod 8) := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- ⭐⭐ **The live class-five marking**, at every handle count and every handle. -/
def liveFiveMark (h : ℕ) (j : Fin h) : Fin (sqRank h) → SqU6 (ZMod 8) :=
  fiveTuple (ZMod 8) h j 1 fiveX fiveY fiveU fiveV

/-- The same core slots with the handle block removed.  It does **not** kill the relator: the
relator's own rows pin the block once the core slots are fixed. -/
def deadFiveMark (h : ℕ) (j : Fin h) : Fin (sqRank h) → SqU6 (ZMod 8) :=
  fiveTuple (ZMod 8) h j 1 fiveX fiveY 1 1

/-- ⭐⭐ **All fifteen relator rows die at the live point**, at every handle count and every
handle.  This is the campaign's first class-five point. -/
theorem sqRelWord_liveFiveMark (h : ℕ) (j : Fin h) : sqRelWord (liveFiveMark h j) = 1 := by
  rw [liveFiveMark, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐ …and the handle block there is **live**, of order four. -/
theorem commP_fiveUV_ne_one : commP fiveU fiveV ≠ 1 := by decide

theorem commP_fiveUV_i : (commP fiveU fiveV).i = 2 := by decide

/-- The invariant the class-five top row meets at the live point. -/
theorem liveFive_handleWord_i (h : ℕ) (j : Fin h) :
    (handleWord (fun j' => liveFiveMark h j (sqHandleIdxU j'))
      (fun j' => liveFiveMark h j (sqHandleIdxV j'))).i = 2 := by
  rw [liveFiveMark, fiveTuple_handleWord]
  decide

theorem deadFive_handleWord_i (h : ℕ) (j : Fin h) :
    (handleWord (fun j' => deadFiveMark h j (sqHandleIdxU j'))
      (fun j' => deadFiveMark h j (sqHandleIdxV j'))).i = 0 := by
  rw [deadFiveMark, fiveTuple_handleWord]
  decide

theorem liveFiveMark_gauge (h : ℕ) (j : Fin h) :
    deadFiveMark h j 0 = liveFiveMark h j 0 ∧ deadFiveMark h j 1 = liveFiveMark h j 1 ∧
      deadFiveMark h j 2 = liveFiveMark h j 2 ∧ (liveFiveMark h j 1).b = 0 ∧
      (liveFiveMark h j 2).b = 0 ∧ fiveDress.b = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide⟩ <;>
    simp only [liveFiveMark, deadFiveMark, fiveTuple_zero, fiveTuple_one, fiveTuple_two] <;>
    decide

/-- The class-three sigma response of the core word at the live point, in the shape
`SqU6.sqRelWord_sigFiveDress_o` produces it: the unit `1`. -/
theorem fiveDress_weight :
    fiveDress.a * fiveX.g - fiveDress.g * fiveX.a + fiveDress.f * fiveX.c
        - fiveDress.c * fiveX.f
        - (1 : SqU6 (ZMod 8)).b * (fiveDress.a * fiveX.c + fiveDress.c * fiveX.a) = 1 := by
  decide

/-- ⭐⭐ **The handle block contributes to the class-five sigma response at the live point.**
The response is the core word's own class-five response plus `2`, and the `2` is exactly the
class-three sigma response (`1`) times the block's outermost class-two pairing (`2`).  At class
four the analogous contribution is provably `0` for **every** marking on this gauge
(`SqU6.sqRelWord_sigFiveDress_handle_blind_four`); this is the class-five statement that
replaces it. -/
theorem liveFive_response (h : ℕ) (j : Fin h) :
    (sqRelWord (sigFiveDress (liveFiveMark h j) fiveDress)).o
        - (sqRelWord (liveFiveMark h j)).o
      = ((sqWord (1 * fiveDress) fiveX fiveY).o - (sqWord 1 fiveX fiveY).o) + 2 := by
  obtain ⟨-, -, -, hxb, hyb, hvb⟩ := liveFiveMark_gauge h j
  rw [SqU6.sqRelWord_sigFiveDress_o hxb hyb hvb, liveFive_handleWord_i]
  simp only [liveFiveMark, fiveTuple_zero, fiveTuple_one, fiveTuple_two]
  rw [fiveDress_weight]
  ring

/-- ⭐⭐ **The class-five sigma reading is NOT blind to the handle block.**  Wave 57 proved
that at class four the block can be live and is never visible: the sigma slot is not in the
block, the block contributes equally to every top row before and after any dressing, and the
selection bit is a difference of dressings, so the block cancels identically.  One level up
that mechanism breaks, and this is the certificate: two markings with identical core slots,
both on the `nu'`-gauge, differ in their class-five sigma responses by exactly `2`. -/
theorem liveFive_response_sees_block (h : ℕ) (j : Fin h) :
    ((sqRelWord (sigFiveDress (liveFiveMark h j) fiveDress)).o
        - (sqRelWord (liveFiveMark h j)).o)
      - ((sqRelWord (sigFiveDress (deadFiveMark h j) fiveDress)).o
        - (sqRelWord (deadFiveMark h j)).o) = 2 := by
  obtain ⟨h0, h1, h2, hxb, hyb, hvb⟩ := liveFiveMark_gauge h j
  rw [SqU6.sqRelWord_sigFiveDress_handle_visible h0 h1 h2 hxb hyb hvb,
    liveFive_handleWord_i, deadFive_handleWord_i]
  simp only [liveFiveMark, fiveTuple_zero, fiveTuple_one]
  rw [fiveDress_weight]
  decide

/-- **Independent check of the two section-6 claims.**  The relator of the live point and the
response difference, both taken straight from `sqRelWord` by kernel computation at `h = 1`,
without going through section 5's algebra or `sqRelWord_fiveTuple`.  Wave 57's process finding
was that two results of one wave can each be right while their composition is vacuous, so the
structural route and the machine route are made to meet here. -/
theorem liveFive_decide_crosscheck :
    sqRelWord (liveFiveMark 1 0) = 1 ∧
      ((sqRelWord (sigFiveDress (liveFiveMark 1 0) fiveDress)).o
          - (sqRelWord (liveFiveMark 1 0)).o)
        - ((sqRelWord (sigFiveDress (deadFiveMark 1 0) fiveDress)).o
          - (sqRelWord (deadFiveMark 1 0)).o) = 2 := by decide

/-- …stated as the negation of blindness. -/
theorem sqRelWord_sigFive_not_handle_blind (h : ℕ) (j : Fin h) :
    (sqRelWord (sigFiveDress (liveFiveMark h j) fiveDress)).o
        - (sqRelWord (liveFiveMark h j)).o
      ≠ (sqRelWord (sigFiveDress (deadFiveMark h j) fiveDress)).o
        - (sqRelWord (deadFiveMark h j)).o := by
  intro hcon
  have := liveFive_response_sees_block h j
  rw [hcon, sub_self] at this
  exact absurd this (by decide)

/-- ⭐ …while the class-four row of the very same pair of markings is blind, which is wave 57's
theorem recovered inside the class-five carrier. -/
theorem liveFive_class_four_blind (h : ℕ) (j : Fin h) :
    (sqRelWord (sigFiveDress (liveFiveMark h j) fiveDress)).m
        - (sqRelWord (liveFiveMark h j)).m
      = (sqRelWord (sigFiveDress (deadFiveMark h j) fiveDress)).m
        - (sqRelWord (deadFiveMark h j)).m := by
  obtain ⟨h0, h1, h2, hxb, -, hvb⟩ := liveFiveMark_gauge h j
  exact SqU6.sqRelWord_sigFiveDress_handle_blind_four h0 h1 h2 hxb hvb

/-! ### The strengthened powering lemma is not vacuous -/

/-- A base meeting `SqU6.zpowZtwo_of_evenFour` with a class-four obstruction equal to `2`.
Neither flat lemma applies to it, and its class-five power law is genuinely **cubic** in the
exponent: `(g^n).o = C(n,3) * 2`.  This is the class-five shape of the situation
`GradedFourHom` met at `sigFourX`, where the class-four obstruction was `2` rather than `0`. -/
def fivePowBase : SqU6 (ZMod 8) := ⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0⟩

/-- Its ten obstructions: the seven lower ones vanish, both class-four ones are `2`, the
class-five one vanishes, and `e * wm = a * wn = 3 * 3` with `wm = wn = 1`, `w3 = 3`. -/
theorem fivePowBase_hypotheses :
    fivePowBase.a * fivePowBase.b = 0 ∧ fivePowBase.b * fivePowBase.c = 0 ∧
      fivePowBase.c * fivePowBase.d = 0 ∧ fivePowBase.d * fivePowBase.e = 0 ∧
      fivePowBase.a * fivePowBase.g + fivePowBase.f * fivePowBase.c = 0 ∧
      fivePowBase.b * fivePowBase.h + fivePowBase.g * fivePowBase.d = 0 ∧
      fivePowBase.c * fivePowBase.i + fivePowBase.h * fivePowBase.e = 0 ∧
      fivePowBase.a * fivePowBase.k + fivePowBase.f * fivePowBase.h
        + fivePowBase.j * fivePowBase.d = 2 * 1 ∧
      fivePowBase.b * fivePowBase.l + fivePowBase.g * fivePowBase.i
        + fivePowBase.k * fivePowBase.e = 2 * 1 ∧
      fivePowBase.a * fivePowBase.n + fivePowBase.f * fivePowBase.l
        + fivePowBase.j * fivePowBase.i + fivePowBase.m * fivePowBase.e = 2 * 0 ∧
      fivePowBase.e * 1 = 3 * 3 ∧ fivePowBase.a * 1 = 3 * 3 := by decide

/-- …but its class-four obstruction does **not** vanish, so `SqU6.zpowZtwo_of_flat` and
`SqU6.zpowZtwo_of_flatTwo` are both inapplicable. -/
theorem fivePowBase_not_flat :
    fivePowBase.a * fivePowBase.k + fivePowBase.f * fivePowBase.h
      + fivePowBase.j * fivePowBase.d ≠ 0 := by decide

/-- …and the class-five `C(n,3)` layer it drives is `2`, not `0`: this is the layer that
`C(n,2)`-evenness alone could never produce. -/
theorem fivePowBase_cubic_layer :
    fivePowBase.a * fivePowBase.b * fivePowBase.l
        + fivePowBase.a * fivePowBase.e * fivePowBase.k
        + fivePowBase.a * fivePowBase.g * fivePowBase.i
        + fivePowBase.c * fivePowBase.f * fivePowBase.i
        + fivePowBase.d * fivePowBase.e * fivePowBase.j
        + fivePowBase.e * fivePowBase.f * fivePowBase.h = 2 := by decide

/-- The powers of the base really are cubic in the exponent. -/
theorem fivePowBase_pow_o (n : ℕ) : (fivePowBase ^ n).o = (n.choose 3 : ℕ) * 2 := by
  rw [SqU6.pow_o]
  norm_num [fivePowBase]

end FiveWitness


/-! ## 7 Axiom pins

Committed prints for every public declaration: all **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable. -/

section AxiomPins

#print axioms SqU6
#print axioms SqU6.one_a
#print axioms SqU6.one_b
#print axioms SqU6.one_c
#print axioms SqU6.one_d
#print axioms SqU6.one_e
#print axioms SqU6.one_f
#print axioms SqU6.one_g
#print axioms SqU6.one_h
#print axioms SqU6.one_i
#print axioms SqU6.one_j
#print axioms SqU6.one_k
#print axioms SqU6.one_l
#print axioms SqU6.one_m
#print axioms SqU6.one_n
#print axioms SqU6.one_o
#print axioms SqU6.mul_a
#print axioms SqU6.mul_b
#print axioms SqU6.mul_c
#print axioms SqU6.mul_d
#print axioms SqU6.mul_e
#print axioms SqU6.mul_f
#print axioms SqU6.mul_g
#print axioms SqU6.mul_h
#print axioms SqU6.mul_i
#print axioms SqU6.mul_j
#print axioms SqU6.mul_k
#print axioms SqU6.mul_l
#print axioms SqU6.mul_m
#print axioms SqU6.mul_n
#print axioms SqU6.mul_o
#print axioms SqU6.inv_a
#print axioms SqU6.inv_b
#print axioms SqU6.inv_c
#print axioms SqU6.inv_d
#print axioms SqU6.inv_e
#print axioms SqU6.inv_f
#print axioms SqU6.inv_g
#print axioms SqU6.inv_h
#print axioms SqU6.inv_i
#print axioms SqU6.inv_j
#print axioms SqU6.inv_k
#print axioms SqU6.inv_l
#print axioms SqU6.inv_m
#print axioms SqU6.inv_n
#print axioms SqU6.inv_o
#print axioms SqU6.eq_one_iff
#print axioms SqU6.instDecidableEq
#print axioms SqU6.commP_a
#print axioms SqU6.commP_b
#print axioms SqU6.commP_c
#print axioms SqU6.commP_d
#print axioms SqU6.commP_e
#print axioms SqU6.commP_f
#print axioms SqU6.commP_g
#print axioms SqU6.commP_h
#print axioms SqU6.commP_i
#print axioms SqU6.u6Comm3L
#print axioms SqU6.u6Comm3M
#print axioms SqU6.u6Comm3R
#print axioms SqU6.commP_j
#print axioms SqU6.commP_k
#print axioms SqU6.commP_l
#print axioms SqU6.u6Comm4L
#print axioms SqU6.u6Comm4R
#print axioms SqU6.commP_m
#print axioms SqU6.commP_n
#print axioms SqU6.u6Comm5
#print axioms SqU6.commP_o
#print axioms SqU6.conjP_a
#print axioms SqU6.conjP_b
#print axioms SqU6.conjP_c
#print axioms SqU6.conjP_d
#print axioms SqU6.conjP_e
#print axioms SqU6.conjP_f
#print axioms SqU6.conjP_g
#print axioms SqU6.conjP_h
#print axioms SqU6.conjP_i
#print axioms SqU6.conjP_j
#print axioms SqU6.conjP_k
#print axioms SqU6.conjP_l
#print axioms SqU6.conjP_m
#print axioms SqU6.conjP_n
#print axioms SqU6.conjP_o
#print axioms SqU6.toU5L
#print axioms SqU6.toU5R
#print axioms SqU6.toU5L_apply
#print axioms SqU6.toU5R_apply
#print axioms SqU6.zHom6
#print axioms SqU6.zHom6_o
#print axioms SqU6.mul_center_o
#print axioms SqU6.equivProd
#print axioms SqU6.nat_card
#print axioms SqU6.isProP_two
#print axioms SqU6.pow_a
#print axioms SqU6.pow_b
#print axioms SqU6.pow_c
#print axioms SqU6.pow_d
#print axioms SqU6.pow_e
#print axioms SqU6.pow_f
#print axioms SqU6.pow_g
#print axioms SqU6.pow_h
#print axioms SqU6.pow_i
#print axioms SqU6.pow_j
#print axioms SqU6.pow_k
#print axioms SqU6.pow_l
#print axioms SqU6.pow_m
#print axioms SqU6.pow_n
#print axioms SqU6.pow_o
#print axioms sqU6Hom
#print axioms sqU6Hom_gen
#print axioms SqU6.zpowZtwo_of_evenFour
#print axioms SqU6.zpowZtwo_of_flatTwo
#print axioms SqU6.zpowZtwo_of_flat
#print axioms sqU6Balance
#print axioms sqU6Balance_gen
#print axioms SqU6.handleWord_a
#print axioms SqU6.handleWord_b
#print axioms SqU6.handleWord_c
#print axioms SqU6.handleWord_d
#print axioms SqU6.handleWord_e
#print axioms SqU6.handleWord_i
#print axioms SqU6.sqWord_a
#print axioms SqU6.sqWord_b
#print axioms SqU6.sqWord_c
#print axioms SqU6.sqWord_d
#print axioms SqU6.sqWord_e
#print axioms SqU6.sqRelWord_a
#print axioms SqU6.sqRelWord_b
#print axioms SqU6.sqRelWord_c
#print axioms SqU6.sqRelWord_d
#print axioms SqU6.sqRelWord_e
#print axioms SqU6.toU5L_sqRelWord
#print axioms SqU6.toU5R_sqRelWord
#print axioms SqU6.toU4LL
#print axioms SqU6.toU4LL_apply
#print axioms SqU6.sqWord_f
#print axioms SqU6.sqWord_j
#print axioms SqU6.sqRelWord_m
#print axioms SqU6.sqRelWord_o
#print axioms sigFiveDress
#print axioms sigFiveDress_zero
#print axioms sigFiveDress_ne
#print axioms sigFiveDress_one
#print axioms sigFiveDress_two
#print axioms sigFiveDress_handleU
#print axioms sigFiveDress_handleV
#print axioms SqU6.sqWord_f_dress
#print axioms SqU6.sqWord_j_dress
#print axioms SqU6.sqRelWord_sigFiveDress_handle_blind_four
#print axioms SqU6.sqRelWord_sigFiveDress_o
#print axioms SqU6.sqRelWord_sigFiveDress_handle_visible
#print axioms fiveTuple
#print axioms fiveTuple_zero
#print axioms fiveTuple_one
#print axioms fiveTuple_two
#print axioms fiveTuple_handleU
#print axioms fiveTuple_handleV
#print axioms fiveTuple_handleU_ne
#print axioms fiveTuple_handleV_ne
#print axioms fiveTuple_handleWord
#print axioms sqRelWord_fiveTuple
#print axioms fiveX
#print axioms fiveY
#print axioms fiveU
#print axioms fiveV
#print axioms fiveDress
#print axioms liveFiveMark
#print axioms deadFiveMark
#print axioms sqRelWord_liveFiveMark
#print axioms commP_fiveUV_ne_one
#print axioms commP_fiveUV_i
#print axioms liveFive_handleWord_i
#print axioms deadFive_handleWord_i
#print axioms liveFiveMark_gauge
#print axioms fiveDress_weight
#print axioms liveFive_response
#print axioms liveFive_response_sees_block
#print axioms liveFive_decide_crosscheck
#print axioms sqRelWord_sigFive_not_handle_blind
#print axioms liveFive_class_four_blind
#print axioms fivePowBase
#print axioms fivePowBase_hypotheses
#print axioms fivePowBase_not_flat
#print axioms fivePowBase_cubic_layer
#print axioms fivePowBase_pow_o

end AxiomPins

end SqCore

end Dyadic

end GQ2
