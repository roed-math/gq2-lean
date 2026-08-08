/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedContain

/-!
# W52-LIFT: the class-four test group `U₅(R)` and the relator's tenth row

`GradedThree` built the class-three test group `SqU4 R = U₄(R)`; this file transposes its §1
and §2 one level up, to the unitriangular `5 × 5` group `SqU5 R = U₅(R)` on ten coordinates,
as the carrier for the W52 stage engine (`GradedLift.lean`).  The transposition was predicted
by `docs/dyadic/w50-selection-note.md` §5 ("`U₅(R)` (ten coordinates) is the mechanical next
test group") and every closed form below was derived and cross-validated numerically before
transcription (`scripts/w52_lift/derive_u5.py`).

Three structural facts appear at this level that class three did not have:

* **two interior columns.**  `U₅` has three adjacent column pairs `(a,b)`, `(b,c)`, `(c,d)`,
  hence *three* class-two rows, *two* class-three rows (the `(1,4)`- and `(2,5)`-coordinates,
  reached by the two `U₄`-quotients `toU4L`, `toU4R`), and one new class-four row `j`;
* **cross-handle coupling.**  Products of `γ₂`-elements are no longer coordinatewise in the
  top coordinate: `(x·y).j` picks up `x.e·y.g`, so the handle block of the relator couples
  *distinct* handles at class four (`SqU5.handleWord_j`); at `h = 1` the coupling vanishes;
* **the core `e`-row enters the top cross term.**  The relator's `j`-row reads the handle
  `g`-pairings against the *full* `e`-row of the core word, not only against the abelian
  relator vector (`sqU5Defect`).

## Contents

* **§1** `SqU5 R`, its group structure, componentwise `simp` lemmas, `DecidableEq`;
* **§2** commutator, conjugation and power formulas; the class-four commutator form
  `u5Comm4`; the two `U₄`-quotients `toU4L`, `toU4R` and the centre `zHom5`;
* **§3** the closed form of the relator: `sqU5CoreE/F/G/H/I/J`, `sqU5Defect`, and
  `SqU5.sqRelWord_a` … `SqU5.sqRelWord_j`;
* **§4** committed axiom prints (all std-3).

No pro-2/topology layer is built here: the stage engine consumes only the ring-level closed
forms, and the `IsProP`/`zpowZtwo` transposition from `GradedThree` §1/§3 is mechanical if a
later wave needs it.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The class-four test group `SqU5 R`

The unitriangular group of `5 × 5` matrices over a commutative ring, carried on the ten
strictly-upper entries

```text
⎡1 a e h j⎤
⎢0 1 b f i⎥
⎢0 0 1 c g⎥
⎢0 0 0 1 d⎥
⎣0 0 0 0 1⎦
```

so that multiplication is `(x·y)_{ik} = x_{ik} + y_{ik} + Σ_{i<m<k} x_{im}·y_{mk}`.  The four
outer coordinates `a, b, c, d` are abelian, `e, f, g` are class two, `h, i` are class three
and `j` is class four; `γ₂ = {a = b = c = d = 0}`, `γ₃ = γ₂ ∩ {e = f = g = 0}`,
`γ₄ = {only j} = the centre` when `R` is nondegenerate. -/

section U5Group

/-- **The class-four test group** over `R`: the unitriangular `5 × 5` group, carried on the ten
strictly-upper entries `(a, …, j) = (x₁₂, x₂₃, x₃₄, x₄₅, x₁₃, x₂₄, x₃₅, x₁₄, x₂₅, x₁₅)`. -/
@[ext]
structure SqU5 (R : Type) [CommRing R] where
  /-- The `(1,2)` entry: the first abelian coordinate. -/
  a : R
  /-- The `(2,3)` entry: the second abelian coordinate. -/
  b : R
  /-- The `(3,4)` entry: the third abelian coordinate. -/
  c : R
  /-- The `(4,5)` entry: the fourth abelian coordinate. -/
  d : R
  /-- The `(1,3)` entry: the first class-two coordinate. -/
  e : R
  /-- The `(2,4)` entry: the second class-two coordinate. -/
  f : R
  /-- The `(3,5)` entry: the third class-two coordinate. -/
  g : R
  /-- The `(1,4)` entry: the first class-three coordinate. -/
  h : R
  /-- The `(2,5)` entry: the second class-three coordinate. -/
  i : R
  /-- The `(1,5)` entry: the class-four coordinate. -/
  j : R

namespace SqU5

variable {R : Type} [CommRing R]

instance : One (SqU5 R) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

instance : Mul (SqU5 R) :=
  ⟨fun p q => ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d,
    p.e + q.e + p.a * q.b, p.f + q.f + p.b * q.c, p.g + q.g + p.c * q.d,
    p.h + q.h + p.a * q.f + p.e * q.c, p.i + q.i + p.b * q.g + p.f * q.d,
    p.j + q.j + p.a * q.i + p.e * q.g + p.h * q.d⟩⟩

instance : Inv (SqU5 R) :=
  ⟨fun p => ⟨-p.a, -p.b, -p.c, -p.d,
    p.a * p.b - p.e, p.b * p.c - p.f, p.c * p.d - p.g,
    -(p.a * p.b * p.c) + p.a * p.f + p.c * p.e - p.h,
    -(p.b * p.c * p.d) + p.b * p.g + p.d * p.f - p.i,
    p.a * p.b * p.c * p.d - p.a * p.b * p.g - p.a * p.d * p.f + p.a * p.i
      - p.c * p.d * p.e + p.d * p.h + p.e * p.g - p.j⟩⟩

@[simp] theorem one_a : (1 : SqU5 R).a = 0 := rfl
@[simp] theorem one_b : (1 : SqU5 R).b = 0 := rfl
@[simp] theorem one_c : (1 : SqU5 R).c = 0 := rfl
@[simp] theorem one_d : (1 : SqU5 R).d = 0 := rfl
@[simp] theorem one_e : (1 : SqU5 R).e = 0 := rfl
@[simp] theorem one_f : (1 : SqU5 R).f = 0 := rfl
@[simp] theorem one_g : (1 : SqU5 R).g = 0 := rfl
@[simp] theorem one_h : (1 : SqU5 R).h = 0 := rfl
@[simp] theorem one_i : (1 : SqU5 R).i = 0 := rfl
@[simp] theorem one_j : (1 : SqU5 R).j = 0 := rfl

@[simp] theorem mul_a (p q : SqU5 R) : (p * q).a = p.a + q.a := rfl
@[simp] theorem mul_b (p q : SqU5 R) : (p * q).b = p.b + q.b := rfl
@[simp] theorem mul_c (p q : SqU5 R) : (p * q).c = p.c + q.c := rfl
@[simp] theorem mul_d (p q : SqU5 R) : (p * q).d = p.d + q.d := rfl
@[simp] theorem mul_e (p q : SqU5 R) : (p * q).e = p.e + q.e + p.a * q.b := rfl
@[simp] theorem mul_f (p q : SqU5 R) : (p * q).f = p.f + q.f + p.b * q.c := rfl
@[simp] theorem mul_g (p q : SqU5 R) : (p * q).g = p.g + q.g + p.c * q.d := rfl
@[simp] theorem mul_h (p q : SqU5 R) : (p * q).h = p.h + q.h + p.a * q.f + p.e * q.c := rfl
@[simp] theorem mul_i (p q : SqU5 R) : (p * q).i = p.i + q.i + p.b * q.g + p.f * q.d := rfl
@[simp] theorem mul_j (p q : SqU5 R) :
    (p * q).j = p.j + q.j + p.a * q.i + p.e * q.g + p.h * q.d := rfl

@[simp] theorem inv_a (p : SqU5 R) : p⁻¹.a = -p.a := rfl
@[simp] theorem inv_b (p : SqU5 R) : p⁻¹.b = -p.b := rfl
@[simp] theorem inv_c (p : SqU5 R) : p⁻¹.c = -p.c := rfl
@[simp] theorem inv_d (p : SqU5 R) : p⁻¹.d = -p.d := rfl
@[simp] theorem inv_e (p : SqU5 R) : p⁻¹.e = p.a * p.b - p.e := rfl
@[simp] theorem inv_f (p : SqU5 R) : p⁻¹.f = p.b * p.c - p.f := rfl
@[simp] theorem inv_g (p : SqU5 R) : p⁻¹.g = p.c * p.d - p.g := rfl
@[simp] theorem inv_h (p : SqU5 R) :
    p⁻¹.h = -(p.a * p.b * p.c) + p.a * p.f + p.c * p.e - p.h := rfl
@[simp] theorem inv_i (p : SqU5 R) :
    p⁻¹.i = -(p.b * p.c * p.d) + p.b * p.g + p.d * p.f - p.i := rfl
@[simp] theorem inv_j (p : SqU5 R) :
    p⁻¹.j = p.a * p.b * p.c * p.d - p.a * p.b * p.g - p.a * p.d * p.f + p.a * p.i
      - p.c * p.d * p.e + p.d * p.h + p.e * p.g - p.j := rfl

instance : Group (SqU5 R) where
  mul_assoc p q r := by
    ext <;> simp only [mul_a, mul_b, mul_c, mul_d, mul_e, mul_f, mul_g, mul_h, mul_i,
      mul_j] <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by
    ext <;> simp only [mul_a, mul_b, mul_c, mul_d, mul_e, mul_f, mul_g, mul_h, mul_i, mul_j,
      inv_a, inv_b, inv_c, inv_d, inv_e, inv_f, inv_g, inv_h, inv_i, inv_j,
      one_a, one_b, one_c, one_d, one_e, one_f, one_g, one_h, one_i, one_j] <;> ring

/-- The ten coordinates of a `SqU5` element determine triviality. -/
theorem eq_one_iff {p : SqU5 R} :
    p = 1 ↔ p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.e = 0 ∧ p.f = 0 ∧ p.g = 0 ∧ p.h = 0 ∧
      p.i = 0 ∧ p.j = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨ha, hb, hc, hd, he, hf, hg, hh, hi, hj⟩
    ext <;> simpa

instance instDecidableEq {R : Type} [CommRing R] [DecidableEq R] : DecidableEq (SqU5 R) :=
  fun _ _ => decidable_of_iff _ SqU5.ext_iff.symm

end SqU5

end U5Group

end SqCore

end Dyadic

end GQ2
