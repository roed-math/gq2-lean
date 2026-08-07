/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedTwo

/-!
# W48 — the class-three layer of `D_sq h`: the unitriangular test group `U₄(R)`

`GradedTwo` built the class-two test group `SqHeis R` and turned the class-two balance into a
gate.  This file does the same one level up: `SqU4 R = U₄(R)` is the unitriangular `4 × 4` group,
whose lower central series is `γ₂ = {a = b = c = 0}`, `γ₃ = {a = … = e = 0}`, and whose three
abelian columns are **three independent characters** — which is what a degree-three functional
`⁅⁅x̄, ȳ⁆, z̄⁆` needs and which no Heisenberg group supplies.

## Contents

* **§1** `SqU4 R`, its group and pro-2 structure, the commutator/conjugation/power formulas;
* **§2** the closed form of `sqWord`, `handleWord` and `sqRelWord`; `sqU4Defect`;
* **§3** `sqU4Hom` and `ℤ₂`-powers in the test group;
* **§4** the class-three gate `sqU4Balance`;
* **§5** validation against the class-two layer and against the committed `V`-family refutation;
* **§6** the class-three question for the arbitrary-dressing frame;
* **§7** stress pins, **§8** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3** (`propext`,
`Classical.choice`, `Quot.sound`).
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The class-three test group `SqU4 R`

The unitriangular group of `4 × 4` matrices over a commutative ring, carried on the six
strictly-upper entries

```text
⎡1 a d f⎤
⎢0 1 b e⎥
⎢0 0 1 c⎥
⎣0 0 0 1⎦
```

so that

```text
(a,b,c,d,e,f)·(a',b',c',d',e',f')
  = (a+a', b+b', c+c', d+d'+a·b', e+e'+b·c', f+f'+a·e'+d·c') .
```

`γ₂ = {a = b = c = 0}` is abelian, `γ₃ = {a = b = c = d = e = 0}` is the centre when `R` has no
extra degeneracy, and the commutator pairing is

```text
⁅p, q⁆ = (0, 0, 0, p.a q.b − p.b q.a, p.b q.c − p.c q.b, ⋯)
```

— *two* independent alternating forms in class two, and in class three the genuinely cubic
expression `u4Comm3`.  §1 of `GradedTwo.lean` transposes verbatim, exactly as its author
predicted.
-/

section U4Group

/-- **The class-three test group** over `R`: the unitriangular `4 × 4` group, carried on the six
strictly-upper entries `(a, b, c, d, e, f) = (x₁₂, x₂₃, x₃₄, x₁₃, x₂₄, x₁₄)`. -/
@[ext]
structure SqU4 (R : Type) [CommRing R] where
  /-- The `(1,2)` entry: the first abelian coordinate. -/
  a : R
  /-- The `(2,3)` entry: the second abelian coordinate. -/
  b : R
  /-- The `(3,4)` entry: the third abelian coordinate. -/
  c : R
  /-- The `(1,3)` entry: the first class-two coordinate. -/
  d : R
  /-- The `(2,4)` entry: the second class-two coordinate. -/
  e : R
  /-- The `(1,4)` entry: the class-three coordinate. -/
  f : R

namespace SqU4

variable {R : Type} [CommRing R]

instance : One (SqU4 R) := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

instance : Mul (SqU4 R) :=
  ⟨fun p q => ⟨p.a + q.a, p.b + q.b, p.c + q.c,
    p.d + q.d + p.a * q.b, p.e + q.e + p.b * q.c, p.f + q.f + p.a * q.e + p.d * q.c⟩⟩

instance : Inv (SqU4 R) :=
  ⟨fun p => ⟨-p.a, -p.b, -p.c, -p.d + p.a * p.b, -p.e + p.b * p.c,
    -p.f + p.a * p.e - p.a * p.b * p.c + p.c * p.d⟩⟩

@[simp] theorem one_a : (1 : SqU4 R).a = 0 := rfl
@[simp] theorem one_b : (1 : SqU4 R).b = 0 := rfl
@[simp] theorem one_c : (1 : SqU4 R).c = 0 := rfl
@[simp] theorem one_d : (1 : SqU4 R).d = 0 := rfl
@[simp] theorem one_e : (1 : SqU4 R).e = 0 := rfl
@[simp] theorem one_f : (1 : SqU4 R).f = 0 := rfl

@[simp] theorem mul_a (p q : SqU4 R) : (p * q).a = p.a + q.a := rfl
@[simp] theorem mul_b (p q : SqU4 R) : (p * q).b = p.b + q.b := rfl
@[simp] theorem mul_c (p q : SqU4 R) : (p * q).c = p.c + q.c := rfl
@[simp] theorem mul_d (p q : SqU4 R) : (p * q).d = p.d + q.d + p.a * q.b := rfl
@[simp] theorem mul_e (p q : SqU4 R) : (p * q).e = p.e + q.e + p.b * q.c := rfl
@[simp] theorem mul_f (p q : SqU4 R) : (p * q).f = p.f + q.f + p.a * q.e + p.d * q.c := rfl

@[simp] theorem inv_a (p : SqU4 R) : p⁻¹.a = -p.a := rfl
@[simp] theorem inv_b (p : SqU4 R) : p⁻¹.b = -p.b := rfl
@[simp] theorem inv_c (p : SqU4 R) : p⁻¹.c = -p.c := rfl
@[simp] theorem inv_d (p : SqU4 R) : p⁻¹.d = -p.d + p.a * p.b := rfl
@[simp] theorem inv_e (p : SqU4 R) : p⁻¹.e = -p.e + p.b * p.c := rfl
@[simp] theorem inv_f (p : SqU4 R) :
    p⁻¹.f = -p.f + p.a * p.e - p.a * p.b * p.c + p.c * p.d := rfl

instance : Group (SqU4 R) where
  mul_assoc p q r := by
    ext <;> simp only [mul_a, mul_b, mul_c, mul_d, mul_e, mul_f] <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by
    ext <;> simp only [mul_a, mul_b, mul_c, mul_d, mul_e, mul_f, inv_a, inv_b, inv_c,
      inv_d, inv_e, inv_f, one_a, one_b, one_c, one_d, one_e, one_f] <;> ring

/-- The six coordinates of a `SqU4` element determine it. -/
theorem eq_one_iff {p : SqU4 R} :
    p = 1 ↔ p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.e = 0 ∧ p.f = 0 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨ha, hb, hc, hd, he, hf⟩; ext <;> simpa

/-- **The first abelian coordinate is a character.** -/
def aHom : SqU4 R →* Multiplicative R where
  toFun p := ofAdd p.a
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The second abelian coordinate is a character.** -/
def bHom : SqU4 R →* Multiplicative R where
  toFun p := ofAdd p.b
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The third abelian coordinate is a character.** -/
def cHom : SqU4 R →* Multiplicative R where
  toFun p := ofAdd p.c
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem aHom_apply (p : SqU4 R) : aHom p = ofAdd p.a := rfl
@[simp] theorem bHom_apply (p : SqU4 R) : bHom p = ofAdd p.b := rfl
@[simp] theorem cHom_apply (p : SqU4 R) : cHom p = ofAdd p.c := rfl

/-- ⭐ **The two Heisenberg quotients.**  Dropping the third column gives the Heisenberg group on
`(a, b, d)`; this is what makes every class-two statement of `GradedTwo` a *consequence* of the
class-three one. -/
def toHeisAB : SqU4 R →* SqHeis R where
  toFun p := ⟨p.a, p.b, p.d⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- …and dropping the first column gives the Heisenberg group on `(b, c, e)`. -/
def toHeisBC : SqU4 R →* SqHeis R where
  toFun p := ⟨p.b, p.c, p.e⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem toHeisAB_apply (p : SqU4 R) : toHeisAB p = ⟨p.a, p.b, p.d⟩ := rfl
@[simp] theorem toHeisBC_apply (p : SqU4 R) : toHeisBC p = ⟨p.b, p.c, p.e⟩ := rfl

/-- **The class-three centre**, as a monoid hom from the additive group of `R`. -/
def zHom : Multiplicative R →* SqU4 R where
  toFun z := ⟨0, 0, 0, 0, 0, toAdd z⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp] theorem zHom_a (z : Multiplicative R) : (zHom z).a = 0 := rfl
@[simp] theorem zHom_b (z : Multiplicative R) : (zHom z).b = 0 := rfl
@[simp] theorem zHom_c (z : Multiplicative R) : (zHom z).c = 0 := rfl
@[simp] theorem zHom_d (z : Multiplicative R) : (zHom z).d = 0 := rfl
@[simp] theorem zHom_e (z : Multiplicative R) : (zHom z).e = 0 := rfl
@[simp] theorem zHom_f (z : Multiplicative R) : (zHom z).f = toAdd z := rfl

@[simp] theorem commP_a (p q : SqU4 R) : (commP p q).a = 0 := by
  simp only [commP, mul_a, inv_a]; ring

@[simp] theorem commP_b (p q : SqU4 R) : (commP p q).b = 0 := by
  simp only [commP, mul_b, inv_b]; ring

@[simp] theorem commP_c (p q : SqU4 R) : (commP p q).c = 0 := by
  simp only [commP, mul_c, inv_c]; ring

/-- ⭐ **The first class-two pairing**: the `(1,3)` coordinate of `⁅p, q⁆` is the alternating form
on the `(a, b)`-columns.  This is `SqHeis.commP_c` through `toHeisAB`. -/
@[simp] theorem commP_d (p q : SqU4 R) : (commP p q).d = p.a * q.b - p.b * q.a := by
  simp only [commP, mul_a, mul_d, inv_a, inv_b, inv_d]; ring

/-- ⭐ **The second class-two pairing**: the alternating form on the `(b, c)`-columns. -/
@[simp] theorem commP_e (p q : SqU4 R) : (commP p q).e = p.b * q.c - p.c * q.b := by
  simp only [commP, mul_b, mul_e, inv_b, inv_c, inv_e]; ring

/-- **The class-three commutator form** — the `(1,4)` coordinate of `⁅p, q⁆`.  Unlike the two
class-two pairings it is *not* alternating-bilinear: it is linear in the class-two coordinates
`d, e` and cubic in the abelian ones.  This is the whole new content of the class-three layer. -/
def u4Comm3 (p q : SqU4 R) : R :=
  p.a * q.e - p.e * q.a + p.d * q.c - p.c * q.d
    + p.a * p.c * q.b - p.a * p.b * q.c + p.c * q.a * q.b - p.b * q.a * q.c

@[simp] theorem commP_f (p q : SqU4 R) : (commP p q).f = u4Comm3 p q := by
  simp only [commP, u4Comm3, mul_a, mul_d, mul_f,
    inv_a, inv_b, inv_c, inv_d, inv_e, inv_f]
  ring

@[simp] theorem conjP_a (p g : SqU4 R) : (conjP p g).a = p.a := by
  simp only [conjP, mul_a, inv_a]; ring

@[simp] theorem conjP_b (p g : SqU4 R) : (conjP p g).b = p.b := by
  simp only [conjP, mul_b, inv_b]; ring

@[simp] theorem conjP_c (p g : SqU4 R) : (conjP p g).c = p.c := by
  simp only [conjP, mul_c, inv_c]; ring

@[simp] theorem conjP_d (p g : SqU4 R) : (conjP p g).d = p.d + (p.a * g.b - g.a * p.b) := by
  simp only [conjP, mul_a, mul_d, inv_a, inv_d]; ring

@[simp] theorem conjP_e (p g : SqU4 R) : (conjP p g).e = p.e + (p.b * g.c - g.b * p.c) := by
  simp only [conjP, mul_b, mul_e, inv_b, inv_e]; ring

/-- **Conjugation in class three**: the `(1,4)` coordinate moves by a cubic expression. -/
@[simp] theorem conjP_f (p g : SqU4 R) :
    (conjP p g).f = p.f + (g.e * p.a - g.a * p.e) + (g.c * p.d - g.d * p.c)
      + (g.a * g.b * p.c - g.a * g.c * p.b) := by
  simp only [conjP, mul_a, mul_d, mul_f, inv_a, inv_d, inv_f]
  ring

@[simp] theorem pow_a (p : SqU4 R) (n : ℕ) : (p ^ n).a = n * p.a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_a, ih]; push_cast; ring

@[simp] theorem pow_b (p : SqU4 R) (n : ℕ) : (p ^ n).b = n * p.b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_b, ih]; push_cast; ring

@[simp] theorem pow_c (p : SqU4 R) (n : ℕ) : (p ^ n).c = n * p.c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_c, ih]; push_cast; ring

private theorem choose_two_succ (n : ℕ) : ((n + 1).choose 2 : ℕ) = n.choose 2 + n := by
  rw [Nat.choose_succ_succ n 1, Nat.choose_one_right]
  show n + n.choose 2 = n.choose 2 + n
  omega

private theorem choose_three_succ (n : ℕ) :
    ((n + 1).choose 3 : ℕ) = n.choose 3 + n.choose 2 := by
  rw [Nat.choose_succ_succ n 2]
  show n.choose 2 + n.choose 3 = n.choose 3 + n.choose 2
  omega

theorem pow_d (p : SqU4 R) (n : ℕ) :
    (p ^ n).d = n * p.d + (n.choose 2 : ℕ) * (p.a * p.b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_d, ih, pow_a, choose_two_succ]
    push_cast
    ring

theorem pow_e (p : SqU4 R) (n : ℕ) :
    (p ^ n).e = n * p.e + (n.choose 2 : ℕ) * (p.b * p.c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_e, ih, pow_b, choose_two_succ]
    push_cast
    ring

/-- ⭐ **The class-three power law.**  The `(1,4)` coordinate of `pⁿ` carries `C(n,2)` on the
class-two coordinates and `C(n,3)` on the cubic abelian term.  This is the class-three shadow of
`SqHeis.pow_c`, and the reason a class-three attack cannot be linear in the dressings: for even
`n` the linear part `n·p.f` dies mod `2` while `C(n,2)` and `C(n,3)` need not. -/
theorem pow_f (p : SqU4 R) (n : ℕ) :
    (p ^ n).f = n * p.f + (n.choose 2 : ℕ) * (p.a * p.e + p.c * p.d)
      + (n.choose 3 : ℕ) * (p.a * p.b * p.c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_f, ih, pow_a, pow_d, choose_two_succ, choose_three_succ]
    push_cast
    ring

/-- The underlying six-tuple, as an equivalence. -/
def equivProd : SqU4 R ≃ R × R × R × R × R × R where
  toFun p := (p.a, p.b, p.c, p.d, p.e, p.f)
  invFun v := ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite R] : Finite (SqU4 R) := Finite.of_equiv _ equivProd.symm

/-- The cardinality of the class-three test group. -/
theorem nat_card [Finite R] : Nat.card (SqU4 R) = Nat.card R ^ 6 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod]
  ring

/-! ### The test group as a pro-2 target -/

instance : TopologicalSpace (SqU4 R) := ⊥

instance : DiscreteTopology (SqU4 R) := ⟨rfl⟩

/-- **The test group is pro-2** whenever the coefficient ring is a finite 2-ring: its order is
`(#R)⁶`. -/
theorem isProP_two [Finite R] {m : ℕ} (hR : Nat.card R = 2 ^ m) : IsProP 2 (SqU4 R) :=
  isProP_of_isPGroup (IsPGroup.of_card (n := 6 * m) (by rw [nat_card, hR, ← pow_mul, mul_comm]))

end SqU4

/-! ## §2 The relator in the class-three test group

The whole class-three computation, in closed form.  The three abelian coordinates see only the
relator vector `−4x̄₀ + 2x̄₁`; the two class-two coordinates are **exactly** the class-two defect
equations of the two Heisenberg quotients (`SqHeis.sqRelWord_c` through `toHeisAB` and
`toHeisBC`), which is the sense in which `GradedTwo` is a quotient of this file; and the
class-three coordinate carries the new content, `sqU4Defect`. -/

section RelWord

variable {R : Type} [CommRing R]

/-- A product of elements with vanishing abelian coordinates is central-in-`γ₂`, with the three
deeper coordinates the sums: `γ₂ = {a = b = c = 0}` is abelian. -/
private theorem SqU4.prod_of_central (l : List (SqU4 R))
    (hl : ∀ p ∈ l, p.a = 0 ∧ p.b = 0 ∧ p.c = 0) :
    l.prod = ⟨0, 0, 0, (l.map SqU4.d).sum, (l.map SqU4.e).sum, (l.map SqU4.f).sum⟩ := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨hpa, hpb, hpc⟩ := hl p List.mem_cons_self
    rw [List.prod_cons, ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]
    have hmul : p * (⟨0, 0, 0, (t.map SqU4.d).sum, (t.map SqU4.e).sum,
          (t.map SqU4.f).sum⟩ : SqU4 R)
        = ⟨p.a + 0, p.b + 0, p.c + 0, p.d + (t.map SqU4.d).sum + p.a * 0,
          p.e + (t.map SqU4.e).sum + p.b * 0,
          p.f + (t.map SqU4.f).sum + p.a * (t.map SqU4.e).sum + p.d * 0⟩ := rfl
    rw [hmul, hpa, hpb, hpc]
    simp

variable {h : ℕ}

@[simp] theorem SqU4.handleWord_a (u v : Fin h → SqU4 R) : (handleWord u v).a = 0 := by
  rw [handleWord, SqU4.prod_of_central _ (by simp)]

@[simp] theorem SqU4.handleWord_b (u v : Fin h → SqU4 R) : (handleWord u v).b = 0 := by
  rw [handleWord, SqU4.prod_of_central _ (by simp)]

@[simp] theorem SqU4.handleWord_c (u v : Fin h → SqU4 R) : (handleWord u v).c = 0 := by
  rw [handleWord, SqU4.prod_of_central _ (by simp)]

/-- The handle block contributes the sum of the first class-two handle pairings. -/
theorem SqU4.handleWord_d (u v : Fin h → SqU4 R) :
    (handleWord u v).d = ∑ j, ((u j).a * (v j).b - (v j).a * (u j).b) := by
  rw [handleWord, SqU4.prod_of_central _ (by simp), Fin.sum_univ_def]
  simp [List.map_map, Function.comp_def, sub_eq_add_neg, mul_comm]

/-- …and of the second. -/
theorem SqU4.handleWord_e (u v : Fin h → SqU4 R) :
    (handleWord u v).e = ∑ j, ((u j).b * (v j).c - (v j).b * (u j).c) := by
  rw [handleWord, SqU4.prod_of_central _ (by simp), Fin.sum_univ_def]
  simp [List.map_map, Function.comp_def, sub_eq_add_neg, mul_comm]

/-- ⭐ **The handle block in class three**: the sum of the cubic commutator forms. -/
theorem SqU4.handleWord_f (u v : Fin h → SqU4 R) :
    (handleWord u v).f = ∑ j, SqU4.u4Comm3 (u j) (v j) := by
  rw [handleWord, SqU4.prod_of_central _ (by simp), Fin.sum_univ_def]
  simp [List.map_map, Function.comp_def]

/-- The first abelian coordinate of the core word: the relator vector `−4x̄₀ + 2x̄₁`. -/
@[simp] theorem SqU4.sqWord_a (s x y : SqU4 R) :
    (sqWord s x y).a = -4 * x.a + 2 * y.a := by
  simp only [sqWord, SqU4.mul_a, SqU4.inv_a, SqU4.conjP_a, SqU4.pow_a, SqU4.commP_a]
  push_cast
  ring

/-- The second abelian coordinate of the core word. -/
@[simp] theorem SqU4.sqWord_b (s x y : SqU4 R) :
    (sqWord s x y).b = -4 * x.b + 2 * y.b := by
  simp only [sqWord, SqU4.mul_b, SqU4.inv_b, SqU4.conjP_b, SqU4.pow_b, SqU4.commP_b]
  push_cast
  ring

/-- The third abelian coordinate of the core word. -/
@[simp] theorem SqU4.sqWord_c (s x y : SqU4 R) :
    (sqWord s x y).c = -4 * x.c + 2 * y.c := by
  simp only [sqWord, SqU4.mul_c, SqU4.inv_c, SqU4.conjP_c, SqU4.pow_c, SqU4.commP_c]
  push_cast
  ring

/-- ⭐⭐ **The class-three content of the core word.**  Beyond the linear part `−4f(x₀) + 2f(x₁)`
the core word contributes a genuinely cubic expression in the three abelian columns, linear in
the two class-two columns.  Setting `y = x²`, `c = 0` and reading off the `(1,3)`-coordinate
recovers `SqHeis.sqWord_c`. -/
def sqU4Core (s x y : SqU4 R) : R :=
  -(s.a * s.b * x.c) + s.a * s.c * x.b
    + s.a * x.e - s.c * x.d + s.d * x.c - s.e * x.a
    - 4 * (s.a * x.b * x.c) + 3 * (s.b * x.a * x.c) + s.c * x.a * x.b
    + 2 * (s.a * x.b * y.c) - 2 * (s.b * x.a * y.c)
    + s.a * y.b * y.c - 2 * (s.b * y.a * y.c) + s.c * y.a * y.b
    - 20 * (x.a * x.b * x.c) + 20 * (x.a * x.b * y.c) - 4 * (x.a * y.b * y.c)
    + 10 * (x.a * x.e) - 8 * (x.a * y.e) + 10 * (x.c * x.d) - 8 * (x.d * y.c)
    + y.a * y.e + y.c * y.d

/-- ⭐⭐ **The class-three coordinate of the core word.** -/
theorem SqU4.sqWord_f (s x y : SqU4 R) :
    (sqWord s x y).f = -4 * x.f + 2 * y.f + sqU4Core s x y := by
  simp only [sqWord, sqU4Core, SqU4.mul_a, SqU4.mul_d, SqU4.mul_f,
    SqU4.inv_a, SqU4.inv_b, SqU4.inv_c, SqU4.inv_d, SqU4.inv_e, SqU4.inv_f,
    SqU4.conjP_a, SqU4.conjP_b, SqU4.conjP_c, SqU4.conjP_d, SqU4.conjP_e, SqU4.conjP_f,
    SqU4.pow_a, SqU4.pow_b, SqU4.pow_c, SqU4.pow_d, SqU4.pow_e, SqU4.pow_f,
    SqU4.commP_c, SqU4.commP_e, SqU4.commP_f, SqU4.u4Comm3]
  norm_num
  ring

/-- The abelian `a`-row of the relator. -/
@[simp] theorem SqU4.sqRelWord_a (m : Fin (sqRank h) → SqU4 R) :
    (sqRelWord m).a = -4 * (m 1).a + 2 * (m 2).a := by
  rw [sqRelWord, SqU4.mul_a, SqU4.sqWord_a, SqU4.handleWord_a, add_zero]

/-- The abelian `b`-row of the relator. -/
@[simp] theorem SqU4.sqRelWord_b (m : Fin (sqRank h) → SqU4 R) :
    (sqRelWord m).b = -4 * (m 1).b + 2 * (m 2).b := by
  rw [sqRelWord, SqU4.mul_b, SqU4.sqWord_b, SqU4.handleWord_b, add_zero]

/-- The abelian `c`-row of the relator. -/
@[simp] theorem SqU4.sqRelWord_c (m : Fin (sqRank h) → SqU4 R) :
    (sqRelWord m).c = -4 * (m 1).c + 2 * (m 2).c := by
  rw [sqRelWord, SqU4.mul_c, SqU4.sqWord_c, SqU4.handleWord_c, add_zero]

/-- ⭐ **The first class-two row of the relator is `GradedTwo`'s defect equation**, verbatim,
through the Heisenberg quotient `toHeisAB`.  Nothing is re-proved here: the class-two layer is a
quotient of the class-three one. -/
theorem SqU4.sqRelWord_d (m : Fin (sqRank h) → SqU4 R) :
    (sqRelWord m).d = -4 * (m 1).d + 2 * (m 2).d
      + sqHeisDefect h (fun i => SqU4.toHeisAB (m i)) := by
  have hnat : SqU4.toHeisAB (sqRelWord m) = sqRelWord (fun i => SqU4.toHeisAB (m i)) :=
    map_sqRelWord _ m
  have := congrArg SqHeis.c hnat
  rw [SqHeis.sqRelWord_c] at this
  exact this

/-- …and the second, through `toHeisBC`. -/
theorem SqU4.sqRelWord_e (m : Fin (sqRank h) → SqU4 R) :
    (sqRelWord m).e = -4 * (m 1).e + 2 * (m 2).e
      + sqHeisDefect h (fun i => SqU4.toHeisBC (m i)) := by
  have hnat : SqU4.toHeisBC (sqRelWord m) = sqRelWord (fun i => SqU4.toHeisBC (m i)) :=
    map_sqRelWord _ m
  have := congrArg SqHeis.c hnat
  rw [SqHeis.sqRelWord_c] at this
  exact this

variable (h) in
/-- ⭐⭐ **The class-three defect of a marking**: the class-three coordinate the relator would
have if the `(1,4)`-coordinates of the marking were all `0`.  Three pieces:

* `sqU4Core`, cubic in the abelian columns of the three core slots;
* a **cross term** `ρ_sq(a-row) · (handle `e`-pairing)` — new at class three, and the reason the
  class-three balance is not simply the class-two balance one column over;
* the sum of the cubic handle commutator forms `SqU4.u4Comm3`. -/
def sqU4Defect (m : Fin (sqRank h) → SqU4 R) : R :=
  sqU4Core (m 0) (m 1) (m 2)
    + (-4 * (m 1).a + 2 * (m 2).a) *
        (∑ j : Fin h, ((m (sqHandleIdxU j)).b * (m (sqHandleIdxV j)).c
          - (m (sqHandleIdxV j)).b * (m (sqHandleIdxU j)).c))
    + ∑ j : Fin h, SqU4.u4Comm3 (m (sqHandleIdxU j)) (m (sqHandleIdxV j))

/-- ⭐⭐ **The relator in the class-three test group, in closed form.**  As at class two, the
adjustable part is `−4f(x₀) + 2f(x₁)`, i.e. exactly `2R`, and the defect is what the marking
cannot touch. -/
theorem SqU4.sqRelWord_f (m : Fin (sqRank h) → SqU4 R) :
    (sqRelWord m).f = -4 * (m 1).f + 2 * (m 2).f + sqU4Defect h m := by
  rw [sqRelWord, SqU4.mul_f, SqU4.sqWord_f, SqU4.handleWord_f, SqU4.handleWord_e,
    SqU4.handleWord_c, SqU4.sqWord_a, mul_zero, add_zero, sqU4Defect]
  ring

/-- ⭐ **The relator identity in the class-three test group**, as six scalar equations. -/
theorem SqU4.sqRelWord_eq_one_iff (m : Fin (sqRank h) → SqU4 R) :
    sqRelWord m = 1 ↔ -4 * (m 1).a + 2 * (m 2).a = 0 ∧ -4 * (m 1).b + 2 * (m 2).b = 0 ∧
      -4 * (m 1).c + 2 * (m 2).c = 0 ∧
      -4 * (m 1).d + 2 * (m 2).d + sqHeisDefect h (fun i => SqU4.toHeisAB (m i)) = 0 ∧
      -4 * (m 1).e + 2 * (m 2).e + sqHeisDefect h (fun i => SqU4.toHeisBC (m i)) = 0 ∧
      -4 * (m 1).f + 2 * (m 2).f + sqU4Defect h m = 0 := by
  rw [SqU4.eq_one_iff, SqU4.sqRelWord_a, SqU4.sqRelWord_b, SqU4.sqRelWord_c, SqU4.sqRelWord_d,
    SqU4.sqRelWord_e, SqU4.sqRelWord_f]

end RelWord

end U4Group

end SqCore

end Dyadic

end GQ2
