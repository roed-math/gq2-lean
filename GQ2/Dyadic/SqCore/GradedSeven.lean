/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFive

/-!
# W65-SIX: the class-six test group `SqU7 = U_7`

The campaign's class-`N` test group is `U_{N+1}`: `SqHeis = U_3` is class two, `SqU4` class
three, `SqU5` class four and `SqU6` class five, carried on the fifteen strictly-upper entries of
a `6 x 6` unitriangular matrix with the class-five coordinate at `(1,6)`.  Class **six**
therefore needs a seventh index, and the tree had no such group: every class-six commutator
vanishes identically in `SqU6`, so a class-six statement written there is vacuous.

This file supplies the missing layer, and nothing else.  `SqU7 R` is the unitriangular `7 x 7`
group over a commutative ring `R`, carried on its twenty-one strictly-upper entries named after
their cells, `e12 ... e67` at class one up to the single class-six coordinate `e17`.

## Provenance of the coordinate law

⚠ Not hand-transcribed.  `scripts/w65_six/u7lib.py` implements `U_n(R)` as honest `n x n`
matrices with matrix multiplication and back-substitution inverse, generic in `n`;
`scripts/w65_six/derive_six.py` section 1 certifies its `n = 6` instance field by field against
the **committed** `SqU6` law of `GradedFive.lean` (all fifteen fields agree for both the product
and the inverse, symbolically over `Z[vars]`); and `scripts/w65_six/gen_seven.py` prints this
file from the `n = 7` instance of the same arithmetic.  So the law below is the law the campaign
already trusts, one index wider.

## What this file does NOT contain

⚠ No separation statement, no marking, no `sqWord` fact.  Those live in
`GQ2/Dyadic/SqCore/GradedSepSix.lean`, which is the only consumer.  This file is a carrier: the
group, its coordinate projections, and decidable equality.
-/

namespace GQ2

namespace Dyadic

namespace SqCore

/-! ## 1 The class-six test group `SqU7 R` -/

section U7Group

/-- **The class-six test group** over `R`: the unitriangular `7 x 7` group, carried on the
twenty-one strictly-upper entries `e<r><c>`, the `(r,c)` entry of the matrix. -/
@[ext]
structure SqU7 (R : Type) [CommRing R] where
  /-- The `(1,2)` entry: the first abelian coordinate. -/
  e12 : R
  /-- The `(2,3)` entry: the second abelian coordinate. -/
  e23 : R
  /-- The `(3,4)` entry: the third abelian coordinate. -/
  e34 : R
  /-- The `(4,5)` entry: the fourth abelian coordinate. -/
  e45 : R
  /-- The `(5,6)` entry: the fifth abelian coordinate. -/
  e56 : R
  /-- The `(6,7)` entry: the sixth abelian coordinate. -/
  e67 : R
  /-- The `(1,3)` entry: the first class-2 coordinate. -/
  e13 : R
  /-- The `(2,4)` entry: the second class-2 coordinate. -/
  e24 : R
  /-- The `(3,5)` entry: the third class-2 coordinate. -/
  e35 : R
  /-- The `(4,6)` entry: the fourth class-2 coordinate. -/
  e46 : R
  /-- The `(5,7)` entry: the fifth class-2 coordinate. -/
  e57 : R
  /-- The `(1,4)` entry: the first class-3 coordinate. -/
  e14 : R
  /-- The `(2,5)` entry: the second class-3 coordinate. -/
  e25 : R
  /-- The `(3,6)` entry: the third class-3 coordinate. -/
  e36 : R
  /-- The `(4,7)` entry: the fourth class-3 coordinate. -/
  e47 : R
  /-- The `(1,5)` entry: the first class-4 coordinate. -/
  e15 : R
  /-- The `(2,6)` entry: the second class-4 coordinate. -/
  e26 : R
  /-- The `(3,7)` entry: the third class-4 coordinate. -/
  e37 : R
  /-- The `(1,6)` entry: the first class-5 coordinate. -/
  e16 : R
  /-- The `(2,7)` entry: the second class-5 coordinate. -/
  e27 : R
  /-- The `(1,7)` entry: the class-six coordinate. -/
  e17 : R

namespace SqU7

variable {R : Type} [CommRing R]

instance : One (SqU7 R) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

instance : Mul (SqU7 R) :=
  ⟨fun p q => ⟨p.e12 + q.e12,
    p.e23 + q.e23,
    p.e34 + q.e34,
    p.e45 + q.e45,
    p.e56 + q.e56,
    p.e67 + q.e67,
    p.e13 + q.e13 + p.e12 * q.e23,
    p.e24 + q.e24 + p.e23 * q.e34,
    p.e35 + q.e35 + p.e34 * q.e45,
    p.e46 + q.e46 + p.e45 * q.e56,
    p.e57 + q.e57 + p.e56 * q.e67,
    p.e14 + q.e14 + p.e12 * q.e24 + p.e13 * q.e34,
    p.e25 + q.e25 + p.e23 * q.e35 + p.e24 * q.e45,
    p.e36 + q.e36 + p.e34 * q.e46 + p.e35 * q.e56,
    p.e47 + q.e47 + p.e45 * q.e57 + p.e46 * q.e67,
    p.e15 + q.e15 + p.e12 * q.e25 + p.e13 * q.e35 + p.e14 * q.e45,
    p.e26 + q.e26 + p.e23 * q.e36 + p.e24 * q.e46 + p.e25 * q.e56,
    p.e37 + q.e37 + p.e34 * q.e47 + p.e35 * q.e57 + p.e36 * q.e67,
    p.e16 + q.e16 + p.e12 * q.e26 + p.e13 * q.e36 + p.e14 * q.e46 + p.e15 * q.e56,
    p.e27 + q.e27 + p.e23 * q.e37 + p.e24 * q.e47 + p.e25 * q.e57 + p.e26 * q.e67,
    p.e17 + q.e17 + p.e12 * q.e27 + p.e13 * q.e37 + p.e14 * q.e47 + p.e15 * q.e57 + p.e16 *
      q.e67⟩⟩

instance : Inv (SqU7 R) :=
  ⟨fun p => ⟨-(p.e12),
    -(p.e23),
    -(p.e34),
    -(p.e45),
    -(p.e56),
    -(p.e67),
    -(p.e13) + p.e12 * p.e23,
    -(p.e24) + p.e23 * p.e34,
    -(p.e35) + p.e34 * p.e45,
    -(p.e46) + p.e45 * p.e56,
    -(p.e57) + p.e56 * p.e67,
    -(p.e14) + p.e12 * p.e24 + p.e13 * p.e34 - (p.e12 * p.e23 * p.e34),
    -(p.e25) + p.e23 * p.e35 + p.e24 * p.e45 - (p.e23 * p.e34 * p.e45),
    -(p.e36) + p.e34 * p.e46 + p.e35 * p.e56 - (p.e34 * p.e45 * p.e56),
    -(p.e47) + p.e45 * p.e57 + p.e46 * p.e67 - (p.e45 * p.e56 * p.e67),
    -(p.e15) + p.e12 * p.e25 + p.e13 * p.e35 + p.e14 * p.e45 - (p.e12 * p.e23 * p.e35) -
      (p.e12 * p.e24 * p.e45) - (p.e13 * p.e34 * p.e45) + p.e12 * p.e23 * p.e34 * p.e45,
    -(p.e26) + p.e23 * p.e36 + p.e24 * p.e46 + p.e25 * p.e56 - (p.e23 * p.e34 * p.e46) -
      (p.e23 * p.e35 * p.e56) - (p.e24 * p.e45 * p.e56) + p.e23 * p.e34 * p.e45 * p.e56,
    -(p.e37) + p.e34 * p.e47 + p.e35 * p.e57 + p.e36 * p.e67 - (p.e34 * p.e45 * p.e57) -
      (p.e34 * p.e46 * p.e67) - (p.e35 * p.e56 * p.e67) + p.e34 * p.e45 * p.e56 * p.e67,
    -(p.e16) + p.e12 * p.e26 + p.e13 * p.e36 + p.e14 * p.e46 + p.e15 * p.e56 - (p.e12 * p.e23
      * p.e36) - (p.e12 * p.e24 * p.e46) - (p.e12 * p.e25 * p.e56) - (p.e13 * p.e34 * p.e46) -
      (p.e13 * p.e35 * p.e56) - (p.e14 * p.e45 * p.e56) + p.e12 * p.e23 * p.e34 * p.e46 + p.e12
      * p.e23 * p.e35 * p.e56 + p.e12 * p.e24 * p.e45 * p.e56 + p.e13 * p.e34 * p.e45 * p.e56 -
      (p.e12 * p.e23 * p.e34 * p.e45 * p.e56),
    -(p.e27) + p.e23 * p.e37 + p.e24 * p.e47 + p.e25 * p.e57 + p.e26 * p.e67 - (p.e23 * p.e34
      * p.e47) - (p.e23 * p.e35 * p.e57) - (p.e23 * p.e36 * p.e67) - (p.e24 * p.e45 * p.e57) -
      (p.e24 * p.e46 * p.e67) - (p.e25 * p.e56 * p.e67) + p.e23 * p.e34 * p.e45 * p.e57 + p.e23
      * p.e34 * p.e46 * p.e67 + p.e23 * p.e35 * p.e56 * p.e67 + p.e24 * p.e45 * p.e56 * p.e67 -
      (p.e23 * p.e34 * p.e45 * p.e56 * p.e67),
    -(p.e17) + p.e12 * p.e27 + p.e13 * p.e37 + p.e14 * p.e47 + p.e15 * p.e57 + p.e16 * p.e67 -
      (p.e12 * p.e23 * p.e37) - (p.e12 * p.e24 * p.e47) - (p.e12 * p.e25 * p.e57) - (p.e12 *
      p.e26 * p.e67) - (p.e13 * p.e34 * p.e47) - (p.e13 * p.e35 * p.e57) - (p.e13 * p.e36 *
      p.e67) - (p.e14 * p.e45 * p.e57) - (p.e14 * p.e46 * p.e67) - (p.e15 * p.e56 * p.e67) +
      p.e12 * p.e23 * p.e34 * p.e47 + p.e12 * p.e23 * p.e35 * p.e57 + p.e12 * p.e23 * p.e36 *
      p.e67 + p.e12 * p.e24 * p.e45 * p.e57 + p.e12 * p.e24 * p.e46 * p.e67 + p.e12 * p.e25 *
      p.e56 * p.e67 + p.e13 * p.e34 * p.e45 * p.e57 + p.e13 * p.e34 * p.e46 * p.e67 + p.e13 *
      p.e35 * p.e56 * p.e67 + p.e14 * p.e45 * p.e56 * p.e67 - (p.e12 * p.e23 * p.e34 * p.e45 *
      p.e57) - (p.e12 * p.e23 * p.e34 * p.e46 * p.e67) - (p.e12 * p.e23 * p.e35 * p.e56 * p.e67)
      - (p.e12 * p.e24 * p.e45 * p.e56 * p.e67) - (p.e13 * p.e34 * p.e45 * p.e56 * p.e67) +
      p.e12 * p.e23 * p.e34 * p.e45 * p.e56 * p.e67⟩⟩

@[simp] theorem one_e12 : (1 : SqU7 R).e12 = 0 := rfl
@[simp] theorem one_e23 : (1 : SqU7 R).e23 = 0 := rfl
@[simp] theorem one_e34 : (1 : SqU7 R).e34 = 0 := rfl
@[simp] theorem one_e45 : (1 : SqU7 R).e45 = 0 := rfl
@[simp] theorem one_e56 : (1 : SqU7 R).e56 = 0 := rfl
@[simp] theorem one_e67 : (1 : SqU7 R).e67 = 0 := rfl
@[simp] theorem one_e13 : (1 : SqU7 R).e13 = 0 := rfl
@[simp] theorem one_e24 : (1 : SqU7 R).e24 = 0 := rfl
@[simp] theorem one_e35 : (1 : SqU7 R).e35 = 0 := rfl
@[simp] theorem one_e46 : (1 : SqU7 R).e46 = 0 := rfl
@[simp] theorem one_e57 : (1 : SqU7 R).e57 = 0 := rfl
@[simp] theorem one_e14 : (1 : SqU7 R).e14 = 0 := rfl
@[simp] theorem one_e25 : (1 : SqU7 R).e25 = 0 := rfl
@[simp] theorem one_e36 : (1 : SqU7 R).e36 = 0 := rfl
@[simp] theorem one_e47 : (1 : SqU7 R).e47 = 0 := rfl
@[simp] theorem one_e15 : (1 : SqU7 R).e15 = 0 := rfl
@[simp] theorem one_e26 : (1 : SqU7 R).e26 = 0 := rfl
@[simp] theorem one_e37 : (1 : SqU7 R).e37 = 0 := rfl
@[simp] theorem one_e16 : (1 : SqU7 R).e16 = 0 := rfl
@[simp] theorem one_e27 : (1 : SqU7 R).e27 = 0 := rfl
@[simp] theorem one_e17 : (1 : SqU7 R).e17 = 0 := rfl

@[simp] theorem mul_e12 (p q : SqU7 R) : (p * q).e12 = p.e12 + q.e12 := rfl
@[simp] theorem mul_e23 (p q : SqU7 R) : (p * q).e23 = p.e23 + q.e23 := rfl
@[simp] theorem mul_e34 (p q : SqU7 R) : (p * q).e34 = p.e34 + q.e34 := rfl
@[simp] theorem mul_e45 (p q : SqU7 R) : (p * q).e45 = p.e45 + q.e45 := rfl
@[simp] theorem mul_e56 (p q : SqU7 R) : (p * q).e56 = p.e56 + q.e56 := rfl
@[simp] theorem mul_e67 (p q : SqU7 R) : (p * q).e67 = p.e67 + q.e67 := rfl
@[simp] theorem mul_e13 (p q : SqU7 R) : (p * q).e13 = p.e13 + q.e13 + p.e12 * q.e23 := rfl
@[simp] theorem mul_e24 (p q : SqU7 R) : (p * q).e24 = p.e24 + q.e24 + p.e23 * q.e34 := rfl
@[simp] theorem mul_e35 (p q : SqU7 R) : (p * q).e35 = p.e35 + q.e35 + p.e34 * q.e45 := rfl
@[simp] theorem mul_e46 (p q : SqU7 R) : (p * q).e46 = p.e46 + q.e46 + p.e45 * q.e56 := rfl
@[simp] theorem mul_e57 (p q : SqU7 R) : (p * q).e57 = p.e57 + q.e57 + p.e56 * q.e67 := rfl
@[simp] theorem mul_e14 (p q : SqU7 R) :
    (p * q).e14 = p.e14 + q.e14 + p.e12 * q.e24 + p.e13 * q.e34 := rfl

@[simp] theorem mul_e25 (p q : SqU7 R) :
    (p * q).e25 = p.e25 + q.e25 + p.e23 * q.e35 + p.e24 * q.e45 := rfl

@[simp] theorem mul_e36 (p q : SqU7 R) :
    (p * q).e36 = p.e36 + q.e36 + p.e34 * q.e46 + p.e35 * q.e56 := rfl

@[simp] theorem mul_e47 (p q : SqU7 R) :
    (p * q).e47 = p.e47 + q.e47 + p.e45 * q.e57 + p.e46 * q.e67 := rfl

@[simp] theorem mul_e15 (p q : SqU7 R) :
    (p * q).e15 = p.e15 + q.e15 + p.e12 * q.e25 + p.e13 * q.e35 + p.e14 * q.e45 := rfl

@[simp] theorem mul_e26 (p q : SqU7 R) :
    (p * q).e26 = p.e26 + q.e26 + p.e23 * q.e36 + p.e24 * q.e46 + p.e25 * q.e56 := rfl

@[simp] theorem mul_e37 (p q : SqU7 R) :
    (p * q).e37 = p.e37 + q.e37 + p.e34 * q.e47 + p.e35 * q.e57 + p.e36 * q.e67 := rfl

@[simp] theorem mul_e16 (p q : SqU7 R) :
    (p * q).e16 = p.e16 + q.e16 + p.e12 * q.e26 + p.e13 * q.e36 + p.e14 * q.e46 + p.e15 * q.e56 :=
      rfl

@[simp] theorem mul_e27 (p q : SqU7 R) :
    (p * q).e27 = p.e27 + q.e27 + p.e23 * q.e37 + p.e24 * q.e47 + p.e25 * q.e57 + p.e26 * q.e67 :=
      rfl

@[simp] theorem mul_e17 (p q : SqU7 R) :
    (p * q).e17 = p.e17 + q.e17 + p.e12 * q.e27 + p.e13 * q.e37 + p.e14 * q.e47 + p.e15 * q.e57 +
      p.e16 * q.e67 := rfl


@[simp] theorem inv_e12 (p : SqU7 R) : p⁻¹.e12 = -(p.e12) := rfl
@[simp] theorem inv_e23 (p : SqU7 R) : p⁻¹.e23 = -(p.e23) := rfl
@[simp] theorem inv_e34 (p : SqU7 R) : p⁻¹.e34 = -(p.e34) := rfl
@[simp] theorem inv_e45 (p : SqU7 R) : p⁻¹.e45 = -(p.e45) := rfl
@[simp] theorem inv_e56 (p : SqU7 R) : p⁻¹.e56 = -(p.e56) := rfl
@[simp] theorem inv_e67 (p : SqU7 R) : p⁻¹.e67 = -(p.e67) := rfl
@[simp] theorem inv_e13 (p : SqU7 R) : p⁻¹.e13 = -(p.e13) + p.e12 * p.e23 := rfl
@[simp] theorem inv_e24 (p : SqU7 R) : p⁻¹.e24 = -(p.e24) + p.e23 * p.e34 := rfl
@[simp] theorem inv_e35 (p : SqU7 R) : p⁻¹.e35 = -(p.e35) + p.e34 * p.e45 := rfl
@[simp] theorem inv_e46 (p : SqU7 R) : p⁻¹.e46 = -(p.e46) + p.e45 * p.e56 := rfl
@[simp] theorem inv_e57 (p : SqU7 R) : p⁻¹.e57 = -(p.e57) + p.e56 * p.e67 := rfl
@[simp] theorem inv_e14 (p : SqU7 R) :
    p⁻¹.e14 = -(p.e14) + p.e12 * p.e24 + p.e13 * p.e34 - (p.e12 * p.e23 * p.e34) := rfl

@[simp] theorem inv_e25 (p : SqU7 R) :
    p⁻¹.e25 = -(p.e25) + p.e23 * p.e35 + p.e24 * p.e45 - (p.e23 * p.e34 * p.e45) := rfl

@[simp] theorem inv_e36 (p : SqU7 R) :
    p⁻¹.e36 = -(p.e36) + p.e34 * p.e46 + p.e35 * p.e56 - (p.e34 * p.e45 * p.e56) := rfl

@[simp] theorem inv_e47 (p : SqU7 R) :
    p⁻¹.e47 = -(p.e47) + p.e45 * p.e57 + p.e46 * p.e67 - (p.e45 * p.e56 * p.e67) := rfl

@[simp] theorem inv_e15 (p : SqU7 R) :
    p⁻¹.e15 = -(p.e15) + p.e12 * p.e25 + p.e13 * p.e35 + p.e14 * p.e45 - (p.e12 * p.e23 * p.e35) -
      (p.e12 * p.e24 * p.e45) - (p.e13 * p.e34 * p.e45) + p.e12 * p.e23 * p.e34 * p.e45 := rfl

@[simp] theorem inv_e26 (p : SqU7 R) :
    p⁻¹.e26 = -(p.e26) + p.e23 * p.e36 + p.e24 * p.e46 + p.e25 * p.e56 - (p.e23 * p.e34 * p.e46) -
      (p.e23 * p.e35 * p.e56) - (p.e24 * p.e45 * p.e56) + p.e23 * p.e34 * p.e45 * p.e56 := rfl

@[simp] theorem inv_e37 (p : SqU7 R) :
    p⁻¹.e37 = -(p.e37) + p.e34 * p.e47 + p.e35 * p.e57 + p.e36 * p.e67 - (p.e34 * p.e45 * p.e57) -
      (p.e34 * p.e46 * p.e67) - (p.e35 * p.e56 * p.e67) + p.e34 * p.e45 * p.e56 * p.e67 := rfl

@[simp] theorem inv_e16 (p : SqU7 R) :
    p⁻¹.e16 = -(p.e16) + p.e12 * p.e26 + p.e13 * p.e36 + p.e14 * p.e46 + p.e15 * p.e56 - (p.e12 *
      p.e23 * p.e36) - (p.e12 * p.e24 * p.e46) - (p.e12 * p.e25 * p.e56) - (p.e13 * p.e34 * p.e46) -
      (p.e13 * p.e35 * p.e56) - (p.e14 * p.e45 * p.e56) + p.e12 * p.e23 * p.e34 * p.e46 + p.e12 *
      p.e23 * p.e35 * p.e56 + p.e12 * p.e24 * p.e45 * p.e56 + p.e13 * p.e34 * p.e45 * p.e56 - (p.e12
      * p.e23 * p.e34 * p.e45 * p.e56) := rfl

@[simp] theorem inv_e27 (p : SqU7 R) :
    p⁻¹.e27 = -(p.e27) + p.e23 * p.e37 + p.e24 * p.e47 + p.e25 * p.e57 + p.e26 * p.e67 - (p.e23 *
      p.e34 * p.e47) - (p.e23 * p.e35 * p.e57) - (p.e23 * p.e36 * p.e67) - (p.e24 * p.e45 * p.e57) -
      (p.e24 * p.e46 * p.e67) - (p.e25 * p.e56 * p.e67) + p.e23 * p.e34 * p.e45 * p.e57 + p.e23 *
      p.e34 * p.e46 * p.e67 + p.e23 * p.e35 * p.e56 * p.e67 + p.e24 * p.e45 * p.e56 * p.e67 - (p.e23
      * p.e34 * p.e45 * p.e56 * p.e67) := rfl

@[simp] theorem inv_e17 (p : SqU7 R) :
    p⁻¹.e17 = -(p.e17) + p.e12 * p.e27 + p.e13 * p.e37 + p.e14 * p.e47 + p.e15 * p.e57 + p.e16 *
      p.e67 - (p.e12 * p.e23 * p.e37) - (p.e12 * p.e24 * p.e47) - (p.e12 * p.e25 * p.e57) - (p.e12 *
      p.e26 * p.e67) - (p.e13 * p.e34 * p.e47) - (p.e13 * p.e35 * p.e57) - (p.e13 * p.e36 * p.e67) -
      (p.e14 * p.e45 * p.e57) - (p.e14 * p.e46 * p.e67) - (p.e15 * p.e56 * p.e67) + p.e12 * p.e23 *
      p.e34 * p.e47 + p.e12 * p.e23 * p.e35 * p.e57 + p.e12 * p.e23 * p.e36 * p.e67 + p.e12 * p.e24
      * p.e45 * p.e57 + p.e12 * p.e24 * p.e46 * p.e67 + p.e12 * p.e25 * p.e56 * p.e67 + p.e13 *
      p.e34 * p.e45 * p.e57 + p.e13 * p.e34 * p.e46 * p.e67 + p.e13 * p.e35 * p.e56 * p.e67 + p.e14
      * p.e45 * p.e56 * p.e67 - (p.e12 * p.e23 * p.e34 * p.e45 * p.e57) - (p.e12 * p.e23 * p.e34 *
      p.e46 * p.e67) - (p.e12 * p.e23 * p.e35 * p.e56 * p.e67) - (p.e12 * p.e24 * p.e45 * p.e56 *
      p.e67) - (p.e13 * p.e34 * p.e45 * p.e56 * p.e67) + p.e12 * p.e23 * p.e34 * p.e45 * p.e56 *
      p.e67 := rfl


instance : Group (SqU7 R) where
  mul_assoc p q r := by
    ext <;> simp only [mul_e12, mul_e23, mul_e34, mul_e45, mul_e56, mul_e67, mul_e13, mul_e24,
      mul_e35, mul_e46, mul_e57, mul_e14, mul_e25, mul_e36, mul_e47, mul_e15, mul_e26,
      mul_e37, mul_e16, mul_e27, mul_e17] <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by
    ext <;>
      simp only [mul_e12, mul_e23, mul_e34, mul_e45, mul_e56, mul_e67, mul_e13, mul_e24,
      mul_e35, mul_e46, mul_e57, mul_e14, mul_e25, mul_e36, mul_e47, mul_e15, mul_e26,
      mul_e37, mul_e16, mul_e27, mul_e17, inv_e12, inv_e23, inv_e34, inv_e45, inv_e56,
      inv_e67, inv_e13, inv_e24, inv_e35, inv_e46, inv_e57, inv_e14, inv_e25, inv_e36,
      inv_e47, inv_e15, inv_e26, inv_e37, inv_e16, inv_e27, inv_e17, one_e12, one_e23,
      one_e34, one_e45, one_e56, one_e67, one_e13, one_e24, one_e35, one_e46, one_e57,
      one_e14, one_e25, one_e36, one_e47, one_e15, one_e26, one_e37, one_e16, one_e27, one_e17
      ] <;> ring

/-! ## 2 Finiteness, the discrete topology, and pro-`2`-ness

Transposed from `SqU6`'s block (`GradedFive.lean` section 3): the same six declarations with
`15` replaced by `21`.  They exist so that a relator-killing marking into `SqU7` classifies a
continuous homomorphism through `sqLiftHom`, which needs `IsProP 2`. -/

/-- The underlying twenty-one-tuple, as an equivalence. -/
def equivProd : SqU7 R ≃
    R × R × R × R × R × R × R × R × R × R × R × R × R × R × R × R × R × R × R × R × R where
  toFun p := (p.e12, p.e23, p.e34, p.e45, p.e56, p.e67, p.e13, p.e24, p.e35, p.e46, p.e57, p.e14,
    p.e25, p.e36, p.e47, p.e15, p.e26, p.e37, p.e16, p.e27, p.e17)
  invFun v := ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite R] : Finite (SqU7 R) := Finite.of_equiv _ equivProd.symm

/-- The cardinality of the class-six test group. -/
theorem nat_card [Finite R] : Nat.card (SqU7 R) = Nat.card R ^ 21 := by
  rw [Nat.card_congr equivProd,
    Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

instance : TopologicalSpace (SqU7 R) := ⊥

instance : DiscreteTopology (SqU7 R) := ⟨rfl⟩

/-- **The class-six test group is pro-2** whenever the coefficient ring is a finite 2-ring:
its order is `(#R)^21`. -/
theorem isProP_two [Finite R] {mm : ℕ} (hR : Nat.card R = 2 ^ mm) : IsProP 2 (SqU7 R) :=
  isProP_of_isPGroup (IsPGroup.of_card (n := 21 * mm) (by rw [nat_card, hR, ← pow_mul, mul_comm]))

/-- The twenty-one coordinates of a `SqU7` element determine triviality. -/
theorem eq_one_iff {p : SqU7 R} :
    p = 1 ↔ p.e12 = 0 ∧ p.e23 = 0 ∧ p.e34 = 0 ∧ p.e45 = 0 ∧ p.e56 = 0 ∧ p.e67 = 0 ∧ p.e13 = 0 ∧
      p.e24 = 0 ∧ p.e35 = 0 ∧ p.e46 = 0 ∧ p.e57 = 0 ∧ p.e14 = 0 ∧ p.e25 = 0 ∧ p.e36 = 0 ∧
      p.e47 = 0 ∧ p.e15 = 0 ∧ p.e26 = 0 ∧ p.e37 = 0 ∧ p.e16 = 0 ∧ p.e27 = 0 ∧ p.e17 = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  · rintro ⟨he12, he23, he34, he45, he56, he67, he13, he24, he35, he46, he57, he14, he25, he36,
      he47, he15, he26, he37, he16, he27, he17⟩
    ext <;> simpa

instance instDecidableEq {R : Type} [CommRing R] [DecidableEq R] : DecidableEq (SqU7 R) :=
  fun _ _ => decidable_of_iff _ SqU7.ext_iff.symm

end SqU7

end U7Group

end SqCore

end Dyadic

end GQ2
