/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.CommFrames
import GQ2.Dyadic.SqCore.EichRefutation

/-!
# W47 — the class-two layer of `D_sq h`, and the refutation engine it powers

Placeholder header; filled in once the sections land.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The class-two test group `SqHeis R`

The Heisenberg group of the standard pairing, carried on triples `(a, b, c)` over a commutative
ring `R`:

```text
(a, b, c) · (a', b', c') = (a + a', b + b', c + c' + a·b')
```

Its commutator subgroup is the centre `{(0, 0, ∗)}`, and `⁅p, q⁆ = (0, 0, p.a·q.b − q.a·p.b)`:
a class-two group whose commutator pairing is the **alternating form of rank ≤ 2** built from
the two abelian coordinates.  Those are exactly the functionals on `Λ²` that a refutation needs.
-/

section HeisGroup

/-- **The class-two test group** over `R`: triples `(a, b, c)` with the Heisenberg product
`(a, b, c)·(a', b', c') = (a + a', b + b', c + c' + a·b')`. -/
@[ext]
structure SqHeis (R : Type) [CommRing R] where
  /-- The first abelian coordinate. -/
  a : R
  /-- The second abelian coordinate. -/
  b : R
  /-- The central coordinate. -/
  c : R

namespace SqHeis

variable {R : Type} [CommRing R]

instance : One (SqHeis R) := ⟨⟨0, 0, 0⟩⟩

instance : Mul (SqHeis R) :=
  ⟨fun p q => ⟨p.a + q.a, p.b + q.b, p.c + q.c + p.a * q.b⟩⟩

instance : Inv (SqHeis R) :=
  ⟨fun p => ⟨-p.a, -p.b, -p.c + p.a * p.b⟩⟩

@[simp] theorem one_a : (1 : SqHeis R).a = 0 := rfl
@[simp] theorem one_b : (1 : SqHeis R).b = 0 := rfl
@[simp] theorem one_c : (1 : SqHeis R).c = 0 := rfl

@[simp] theorem mul_a (p q : SqHeis R) : (p * q).a = p.a + q.a := rfl
@[simp] theorem mul_b (p q : SqHeis R) : (p * q).b = p.b + q.b := rfl
@[simp] theorem mul_c (p q : SqHeis R) : (p * q).c = p.c + q.c + p.a * q.b := rfl

@[simp] theorem inv_a (p : SqHeis R) : p⁻¹.a = -p.a := rfl
@[simp] theorem inv_b (p : SqHeis R) : p⁻¹.b = -p.b := rfl
@[simp] theorem inv_c (p : SqHeis R) : p⁻¹.c = -p.c + p.a * p.b := rfl

instance : Group (SqHeis R) where
  mul_assoc p q r := by ext <;> simp <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by ext <;> simp

/-- The three coordinates of a `SqHeis` element determine it. -/
theorem eq_one_iff {p : SqHeis R} : p = 1 ↔ p.a = 0 ∧ p.b = 0 ∧ p.c = 0 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨ha, hb, hc⟩; ext <;> simpa

/-- **The first abelian coordinate is a character.** -/
def aHom : SqHeis R →* Multiplicative R where
  toFun p := ofAdd p.a
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The second abelian coordinate is a character.** -/
def bHom : SqHeis R →* Multiplicative R where
  toFun p := ofAdd p.b
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem aHom_apply (p : SqHeis R) : aHom p = ofAdd p.a := rfl
@[simp] theorem bHom_apply (p : SqHeis R) : bHom p = ofAdd p.b := rfl

/-- **The centre**, as a monoid hom from the additive group of `R`. -/
def zHom : Multiplicative R →* SqHeis R where
  toFun z := ⟨0, 0, toAdd z⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp] theorem zHom_a (z : Multiplicative R) : (zHom z).a = 0 := rfl
@[simp] theorem zHom_b (z : Multiplicative R) : (zHom z).b = 0 := rfl
@[simp] theorem zHom_c (z : Multiplicative R) : (zHom z).c = toAdd z := rfl

@[simp] theorem commP_a (p q : SqHeis R) : (commP p q).a = 0 := by
  simp only [commP, mul_a, inv_a]; ring

@[simp] theorem commP_b (p q : SqHeis R) : (commP p q).b = 0 := by
  simp only [commP, mul_b, inv_b]; ring

/-- ⭐ **The commutator pairing**: the central coordinate of `⁅p, q⁆` is the value of the
alternating form `(a, b) ∧ (a', b')` on the two abelian coordinates, and the abelian
coordinates of `⁅p, q⁆` vanish.  This is the class-two pairing the whole file runs on. -/
@[simp] theorem commP_c (p q : SqHeis R) : (commP p q).c = p.a * q.b - q.a * p.b := by
  simp only [commP, mul_a, mul_c, inv_a, inv_b, inv_c]; ring

@[simp] theorem conjP_a (p g : SqHeis R) : (conjP p g).a = p.a := by
  simp only [conjP, mul_a, inv_a]; ring

@[simp] theorem conjP_b (p g : SqHeis R) : (conjP p g).b = p.b := by
  simp only [conjP, mul_b, inv_b]; ring

/-- **Conjugation** moves only the central coordinate, and by the pairing. -/
@[simp] theorem conjP_c (p g : SqHeis R) :
    (conjP p g).c = p.c + (p.a * g.b - g.a * p.b) := by
  simp only [conjP, mul_a, mul_c, inv_a, inv_c]; ring

@[simp] theorem pow_a (p : SqHeis R) (n : ℕ) : (p ^ n).a = n * p.a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_a, ih]; push_cast; ring

@[simp] theorem pow_b (p : SqHeis R) (n : ℕ) : (p ^ n).b = n * p.b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_b, ih]; push_cast; ring

/-- The central coordinate of a power carries the binomial coefficient `C(n, 2)`. -/
theorem pow_c (p : SqHeis R) (n : ℕ) :
    (p ^ n).c = n * p.c + (n.choose 2 : ℕ) * (p.a * p.b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_c, ih, pow_a]
    have hchoose : ((n + 1).choose 2 : ℕ) = n.choose 2 + n := by
      rw [Nat.choose_succ_succ n 1, Nat.choose_one_right]
      show n + n.choose 2 = n.choose 2 + n
      omega
    rw [hchoose]
    push_cast
    ring

/-- The underlying triple, as an equivalence with `R × R × R`. -/
def equivProd : SqHeis R ≃ R × R × R where
  toFun p := (p.a, p.b, p.c)
  invFun v := ⟨v.1, v.2.1, v.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite R] : Finite (SqHeis R) := Finite.of_equiv _ equivProd.symm

/-- The cardinality of the test group. -/
theorem nat_card [Finite R] : Nat.card (SqHeis R) = Nat.card R ^ 3 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod]
  ring

end SqHeis

end HeisGroup

end SqCore

end Dyadic

end GQ2
