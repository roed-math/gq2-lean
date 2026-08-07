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

instance instDecidableEq {R : Type} [CommRing R] [DecidableEq R] : DecidableEq (SqU4 R) :=
  fun _ _ => decidable_of_iff _ SqU4.ext_iff.symm

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

/-! ## §3 The lift: markings of the class-three test group classify class-three quotients -/

section Lift

variable {R : Type} [CommRing R] [Finite R] {mm : ℕ} {h : ℕ}

/-- ⭐ **The class-three test homomorphism** attached to a marking of `SqU4 R` killing the
relator: three characters of `D_sq(h)^ab`, two solutions of the class-two defect equations, and
one of the class-three equation, *is* a class-three quotient. -/
noncomputable def sqU4Hom (hR : Nat.card R = 2 ^ mm) (h : ℕ) (m : Fin (sqRank h) → SqU4 R)
    (hrel : sqRelWord m = 1) : ContinuousMonoidHom (DSq h : Type) (SqU4 R) :=
  sqLiftHom h (SqU4.isProP_two hR) m hrel

@[simp] theorem sqU4Hom_gen (hR : Nat.card R = 2 ^ mm) (m : Fin (sqRank h) → SqU4 R)
    (hrel : sqRelWord m = 1) (i : Fin (sqRank h)) :
    sqU4Hom hR h m hrel (sqGen h i) = m i :=
  sqLiftHom_gen _ _ _ _ i

/-- ⭐ **`ℤ₂`-powers in the class-three test group**, for a "flat" base — one whose two class-two
power corrections and whose cubic correction all vanish.  These are exactly the three conditions
under which `n ↦ gⁿ` is `R`-linear, by `SqU4.pow_d`, `SqU4.pow_e`, `SqU4.pow_f`. -/
theorem SqU4.zpowZtwo_of_flat (hQ : IsProP 2 (SqU4 R)) (pi : ℤ_[2] →+* R)
    (hpi : ∀ T : Set R, IsOpen (pi ⁻¹' T)) {g : SqU4 R} (hab : g.a * g.b = 0)
    (hbc : g.b * g.c = 0) (hae : g.a * g.e + g.c * g.d = 0) (u : ℤ_[2]) :
    zpowZtwo hQ g u
      = ⟨pi u * g.a, pi u * g.b, pi u * g.c, pi u * g.d, pi u * g.e, pi u * g.f⟩ := by
  set phi : Multiplicative ℤ_[2] →* SqU4 R :=
    { toFun := fun z => ⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c,
        pi (toAdd z) * g.d, pi (toAdd z) * g.e, pi (toAdd z) * g.f⟩
      map_one' := by ext <;> simp
      map_mul' := fun z w => by
        have hadd : pi (toAdd (z * w)) = pi (toAdd z) + pi (toAdd w) := by
          rw [show toAdd (z * w) = toAdd z + toAdd w from rfl, map_add]
        have h1 : pi (toAdd z) * pi (toAdd w) * (g.a * g.b) = 0 := by rw [hab, mul_zero]
        have h2 : pi (toAdd z) * pi (toAdd w) * (g.b * g.c) = 0 := by rw [hbc, mul_zero]
        have h3 : pi (toAdd z) * pi (toAdd w) * (g.a * g.e + g.c * g.d) = 0 := by
          rw [hae, mul_zero]
        ext
        · simp only [SqU4.mul_a]; rw [hadd]; ring
        · simp only [SqU4.mul_b]; rw [hadd]; ring
        · simp only [SqU4.mul_c]; rw [hadd]; ring
        · simp only [SqU4.mul_d]; rw [hadd]; linear_combination -h1
        · simp only [SqU4.mul_e]; rw [hadd]; linear_combination -h2
        · simp only [SqU4.mul_f]; rw [hadd]; linear_combination -h3 } with hphi
  have hcont : Continuous phi := by
    refine IsLocallyConstant.continuous fun s => ?_
    show IsOpen ((fun z : Multiplicative ℤ_[2] =>
      (⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c, pi (toAdd z) * g.d,
        pi (toAdd z) * g.e, pi (toAdd z) * g.f⟩ : SqU4 R)) ⁻¹' s)
    have hfact : (fun z : Multiplicative ℤ_[2] =>
        (⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c, pi (toAdd z) * g.d,
          pi (toAdd z) * g.e, pi (toAdd z) * g.f⟩ : SqU4 R)) ⁻¹' s
        = toAdd ⁻¹' (pi ⁻¹' {r : R | (⟨r * g.a, r * g.b, r * g.c, r * g.d, r * g.e,
            r * g.f⟩ : SqU4 R) ∈ s}) := rfl
    rw [hfact]
    exact (hpi _).preimage continuous_toAdd
  have hone : phi (ofAdd (1 : ℤ_[2])) = g := by
    show (⟨pi 1 * g.a, pi 1 * g.b, pi 1 * g.c, pi 1 * g.d, pi 1 * g.e, pi 1 * g.f⟩ : SqU4 R) = g
    rw [map_one]
    ext <;> simp
  have := zpowZtwoHom_unique hQ hcont u
  rw [hone] at this
  exact this.symm

end Lift

/-! ## §4 ⭐ The class-three gate

One lemma, exactly as at class two.  A frame killing the relator satisfies, in **every**
class-three test group, the six scalar equations of `SqU4.sqRelWord_eq_one_iff` at its own slot
images.  The first five reproduce the class-one and class-two gates; the sixth is new. -/

section Engine

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐⭐ **The class-three balance.**  Every frame that kills the relator obeys the class-three
defect equation in every class-three test group. -/
theorem sqU4Balance (Phi : ContinuousMonoidHom (DSq h : Type) (SqU4 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    -4 * (Phi (n 1)).a + 2 * (Phi (n 2)).a = 0 ∧ -4 * (Phi (n 1)).b + 2 * (Phi (n 2)).b = 0 ∧
      -4 * (Phi (n 1)).c + 2 * (Phi (n 2)).c = 0 ∧
      -4 * (Phi (n 1)).d + 2 * (Phi (n 2)).d
        + sqHeisDefect h (fun i => SqU4.toHeisAB (Phi (n i))) = 0 ∧
      -4 * (Phi (n 1)).e + 2 * (Phi (n 2)).e
        + sqHeisDefect h (fun i => SqU4.toHeisBC (Phi (n i))) = 0 ∧
      -4 * (Phi (n 1)).f + 2 * (Phi (n 2)).f + sqU4Defect h (fun i => Phi (n i)) = 0 := by
  have hkey := SqU4.sqRelWord_eq_one_iff (R := R) (h := h) fun i => Phi (n i)
  rw [← map_sqRelWord Phi n, hn, map_one] at hkey
  exact hkey.mp rfl

/-- The class-three defect equation alone, which is the one that carries new information. -/
theorem sqU4Defect_balance (Phi : ContinuousMonoidHom (DSq h : Type) (SqU4 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    -4 * (Phi (n 1)).f + 2 * (Phi (n 2)).f + sqU4Defect h (fun i => Phi (n i)) = 0 :=
  (sqU4Balance Phi n hn).2.2.2.2.2

/-- ⭐ **The class-two gate is the class-three gate composed with `toHeisAB`** — so nothing that
`GradedTwo` refutes is lost, and nothing it proves is re-proved. -/
theorem sqHeisBalance_of_sqU4 (Phi : ContinuousMonoidHom (DSq h : Type) (SqU4 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    -4 * (SqU4.toHeisAB (Phi (n 1))).c + 2 * (SqU4.toHeisAB (Phi (n 2))).c
      + sqHeisDefect h (fun i => SqU4.toHeisAB (Phi (n i))) = 0 :=
  (sqU4Balance Phi n hn).2.2.2.1

end Engine

/-! ## §5 Validation — the class-two gate is a *special case* of the class-three gate

`GradedTwo`'s gate was validated by re-deriving a committed refutation through it.  The
class-three gate is validated the other way round, and more strongly: the class-two test group
embeds in the class-three one as the `(a, b, d)`-columns, so `sqHeisBalance` is literally
`sqU4Balance`'s fourth clause at a marking in the image.  Nothing the class-two gate can see is
lost, and the class-two refutation of the `V`-family is reproduced statement for statement. -/

section Validation

variable {R : Type} [CommRing R] {h : ℕ}

/-- **The class-two test group sits inside the class-three one** as the `(a, b, d)`-columns: a
section of `SqU4.toHeisAB`. -/
def u4OfHeis : SqHeis R →* SqU4 R where
  toFun p := ⟨p.a, p.b, 0, p.c, 0, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp] theorem u4OfHeis_apply (p : SqHeis R) : u4OfHeis p = ⟨p.a, p.b, 0, p.c, 0, 0⟩ := rfl

@[simp] theorem toHeisAB_u4OfHeis (p : SqHeis R) : SqU4.toHeisAB (u4OfHeis p) = p := by
  ext <;> rfl

/-- The same embedding as a continuous monoid hom (both groups are discrete). -/
def u4OfHeisC : ContinuousMonoidHom (SqHeis R) (SqU4 R) where
  toFun p := u4OfHeis p
  map_one' := rfl
  map_mul' _ _ := u4OfHeis.map_mul _ _
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem u4OfHeisC_apply (p : SqHeis R) :
    u4OfHeisC p = (⟨p.a, p.b, 0, p.c, 0, 0⟩ : SqU4 R) := rfl

/-- ⭐ **The class-three gate reproduces the class-two gate**, statement for statement: push a
class-two test hom into `SqU4 R` and the fourth clause of `sqU4Balance` *is*
`sqHeisDefect_balance`.  This is the validation `GradedTwo` asked for. -/
theorem sqHeisDefect_balance_of_u4Balance
    (Phi : ContinuousMonoidHom (DSq h : Type) (SqHeis R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    -4 * (Phi (n 1)).c + 2 * (Phi (n 2)).c + sqHeisDefect h (fun i => Phi (n i)) = 0 := by
  have hbal := (sqU4Balance (u4OfHeisC.comp Phi) n hn).2.2.2.1
  simpa using hbal

/-- The gate's class-two verdict **matches** the committed one, statement for statement. -/
example (Phi : ContinuousMonoidHom (DSq h : Type) (SqHeis R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    -4 * (Phi (n 1)).c + 2 * (Phi (n 2)).c + sqHeisDefect h (fun i => Phi (n i)) = 0 :=
  sqHeisDefect_balance Phi n hn

/-- ⭐ …and therefore the committed `V`-family refutation is a class-three verdict too: its proof
consumes exactly `sqHeisDefect_balance`, which `sqHeisDefect_balance_of_u4Balance` supplies from
`sqU4Balance` alone. -/
example {h : ℕ} (hh : 0 < h) : ¬ SqEichRelWord h := not_sqEichRelWord_of_gate hh

end Validation

/-! ## §6 ⭐⭐ The class-three question for the arbitrary-dressing frame

The narrow question of W48-U4: *the class-two balance of the arbitrary-dressing frame is
under-determined — one dressing forced, three free.  Can the free dressings be chosen to kill
the class-three defect?*

§6 answers it, and the answer is governed by one arithmetic fact. -/

section TopParity

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐ **The class-three defect does not see the class-three coordinates.**  `sqU4Defect` is
built from the abelian and class-two columns alone. -/
theorem sqU4Defect_congr {m m' : Fin (sqRank h) → SqU4 R}
    (hlow : ∀ i, (m' i).a = (m i).a ∧ (m' i).b = (m i).b ∧ (m' i).c = (m i).c ∧
      (m' i).d = (m i).d ∧ (m' i).e = (m i).e) :
    sqU4Defect h m' = sqU4Defect h m := by
  simp only [sqU4Defect, sqU4Core, SqU4.u4Comm3, (hlow _).1, (hlow _).2.1, (hlow _).2.2.1,
    (hlow _).2.2.2.1, (hlow _).2.2.2.2]

/-- ⭐⭐ **The class-three coordinate of the relator sees only two slots.**  Two markings with
the same abelian and class-two columns have relators differing in the `(1,4)`-coordinate by
exactly `−4·Δf(x₀) + 2·Δf(x₁)` — the slot-exponent vector `(0, −4, 2, 0, 0)` again, one level up.
The `σ`-slot's and the handle slots' class-three coordinates **cancel out entirely**. -/
theorem sqU4_top_adjust {m m' : Fin (sqRank h) → SqU4 R}
    (hlow : ∀ i, (m' i).a = (m i).a ∧ (m' i).b = (m i).b ∧ (m' i).c = (m i).c ∧
      (m' i).d = (m i).d ∧ (m' i).e = (m i).e) :
    (sqRelWord m').f - (sqRelWord m).f
      = -4 * ((m' 1).f - (m 1).f) + 2 * ((m' 2).f - (m 2).f) := by
  rw [SqU4.sqRelWord_f, SqU4.sqRelWord_f, sqU4Defect_congr hlow]
  ring

/-- ⭐⭐ **The class-three equation is a parity condition, and nothing more.**  The set of values
the two exponent slots can contribute is exactly `2R`: `−4z₁ + 2z₂` ranges over `2R` and no
further.  So a frame passes the class-three gate iff its defect is **even**, and the class-three
layer carries exactly one bit of information per test hom. -/
theorem sqU4_top_range (z : R) :
    (∃ z₁ z₂ : R, -4 * z₁ + 2 * z₂ = 2 * z) ∧ ∀ z₁ z₂ : R, ∃ w : R, -4 * z₁ + 2 * z₂ = 2 * w :=
  ⟨⟨0, z, by ring⟩, fun z₁ z₂ => ⟨-2 * z₁ + z₂, by ring⟩⟩

end TopParity

/-! ### ⭐⭐ The answer, with a witness

Fix `h = 1` and the selected marking `ν'` with `ν'(u₀) = 0`, `ν'(v₀) = 1` — the handle is
genuinely **not** already cleared, so this is the case the whole clearing scheme is about.  The
class-three test hom is `sqU4Hom` at the marking `u4WitMark` over `ℤ/8`: the `b`-column is `ν'`
(so every `ν'`-trivial dressing has `b`-coordinate `0`), the `a`- and `c`-columns are two further
free characters, and `x₀ ↦ 1`, `σ ↦ ⟨0,1,0,0,0,0⟩` put the pivot `w = σ·x₀^{−c₀}` on the pure
`ν'`-column at every exponent `c₀`.

Three facts, all by `decide`:

* `sqRelWord_u4WitMark` — it is a marking, so it really is a class-three quotient of `D_sq 1`;
* `not_sqRelWord_u4WitBase` — the **undressed** frame `(σ, x₀, x₁, U, V)` fails there.  The gate
  is live: it refutes at class two (`d`-row `6`) *and* at class three (`f`-row `4`);
* `sqRelWord_u4WitFrame` — ⭐ the frame dressed by `a₁ = U⁻¹`, and by **nothing else**, kills the
  relator.  `ā₁ = −Ū = −ν'(v₀)·Ū + ν'(u₀)·V̄` is exactly the value the class-two balance forces
  (`GradedTwo.sqArbFrame_x0_dressing_forced`).

⭐ **So the answer to W48-U4's question is yes.**  The three free class-two dressings *can* be
chosen to kill the class-three defect — here they can be left trivial, and the dressing that
class two already forces does the class-three job as well.

⚠ **But the class-three layer is not vacuous.**  `u4WitBad` dresses the `x₁`-slot by `V` instead:
its two class-two defects stay in `2·ℤ/8`, so **class two accepts it**, while its class-three
defect is `7`, a unit — and by `sqU4_top_range` no choice of the two exponent slots' class-three
coordinates can repair that.  Class three kills dressings that class two admits; it just does not
kill *all* of them. -/

section Witness

/-- The class-three test marking over `ℤ/8` at a selected `ν'` with `ν'(u₀) = 0`, `ν'(v₀) = 1`.
The `b`-column is `ν'`; the `a`- and `c`-columns are the two free characters, `2` and `2` on `u₀`
and `1`, `1` on `v₀`; the `x₁`-slot's three deeper coordinates solve the relator. -/
def u4WitMark : Fin (sqRank 1) → SqU4 (ZMod 8) :=
  ![⟨0, 1, 0, 0, 0, 0⟩, 1, ⟨0, 0, 0, 7, 1, 5⟩, ⟨2, 0, 2, 0, 0, 0⟩, ⟨1, 1, 1, 0, 0, 0⟩]

/-- It really is a marking, so `sqU4Hom` turns it into a class-three quotient of `D_sq 1`. -/
theorem sqRelWord_u4WitMark : sqRelWord u4WitMark = 1 := by decide

/-- The **undressed** frame's slot images: `σ`, `x₀`, `x₁`, and the two cleared letters
`U = w^{−ν'(u₀)}u₀ = u₀`, `V = v₀·w^{−ν'(v₀)}`. -/
def u4WitBase : Fin (sqRank 1) → SqU4 (ZMod 8) :=
  ![⟨0, 1, 0, 0, 0, 0⟩, 1, ⟨0, 0, 0, 7, 1, 5⟩, ⟨2, 0, 2, 0, 0, 0⟩, ⟨1, 0, 1, 7, 0, 0⟩]

/-- ⚠ **The gate is live**: the undressed frame fails, at class two *and* at class three. -/
theorem not_sqRelWord_u4WitBase : sqRelWord u4WitBase ≠ 1 := by decide

/-- The exact failure: the relator is `⟨0,0,0,6,2,4⟩`. -/
theorem sqRelWord_u4WitBase_eq : sqRelWord u4WitBase = ⟨0, 0, 0, 6, 2, 4⟩ := by decide

/-- ⭐⭐ **The witness.**  The arbitrary-dressing frame with `a₁ = U⁻¹` — the class-two forced
dressing — and every other dressing trivial.  `U⁻¹ = ⟨6,0,6,0,0,0⟩` is the image of
`(sqEichU 1 ν' 0)⁻¹`, which lies in `ker λ ∩ ker ν'` by `toAdd_nuLam_sqEichU` and
`toAdd_nu_sqEichU`; the other four slots are undressed, so the frame is mod-2 independent for
free. -/
def u4WitFrame : Fin (sqRank 1) → SqU4 (ZMod 8) :=
  ![⟨0, 1, 0, 0, 0, 0⟩, ⟨6, 0, 6, 0, 0, 0⟩, ⟨0, 0, 0, 7, 1, 5⟩, ⟨2, 0, 2, 0, 0, 0⟩,
    ⟨1, 0, 1, 7, 0, 0⟩]

/-- ⭐⭐ **The class-three gate does not obstruct the arbitrary-dressing frame.**  At a live
class-three test hom, at a genuinely uncleared handle, the frame dressed by the class-two forced
value kills the relator outright — all six equations, class one, class two *and* class three. -/
theorem sqRelWord_u4WitFrame : sqRelWord u4WitFrame = 1 := by decide

/-- The dressed slot really is the undressed one times `U⁻¹`. -/
theorem u4WitFrame_one : u4WitFrame 1 = u4WitBase 1 * (u4WitBase 3)⁻¹ := by decide

/-- ⚠ **A dressing that class two accepts and class three rejects**: the `x₁`-slot dressed by
`V`, everything else undressed. -/
def u4WitBad : Fin (sqRank 1) → SqU4 (ZMod 8) :=
  ![⟨0, 1, 0, 0, 0, 0⟩, 1, ⟨1, 0, 1, 6, 1, 4⟩, ⟨2, 0, 2, 0, 0, 0⟩, ⟨1, 0, 1, 7, 0, 0⟩]

/-- Its two class-two defects are **even**, so both class-two equations are solvable in the
exponent slots: class two admits this dressing. -/
theorem u4WitBad_class_two_even :
    (∃ z : ZMod 8, sqHeisDefect 1 (fun i => SqU4.toHeisAB (u4WitBad i)) = 2 * z) ∧
      ∃ z : ZMod 8, sqHeisDefect 1 (fun i => SqU4.toHeisBC (u4WitBad i)) = 2 * z := by
  exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- ⚠⚠ …but its class-three defect is a **unit**, so by `sqU4_top_range` no choice of the
`x₀`- and `x₁`-slots' class-three coordinates repairs it.  The class-three layer is a genuine,
non-vacuous constraint on the dressings. -/
theorem u4WitBad_class_three_odd : ∀ z : ZMod 8, sqU4Defect 1 u4WitBad ≠ 2 * z := by decide

/-- The exact value of the class-three defect that kills it. -/
theorem u4WitBad_defect : sqU4Defect 1 u4WitBad = 7 := by decide

end Witness

end U4Group

end SqCore

end Dyadic

end GQ2
