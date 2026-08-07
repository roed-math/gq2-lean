/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.CommFrames
import GQ2.Dyadic.SqCore.EichRefutation

/-!
# W47 — the class-two layer of `D_sq h`, and the refutation engine it powers

`CommFrames`' Headline 3 is a hand computation in `gr₂ = γ₂/γ₃ ≅ Λ²(D_sq(h)^ab)`.  This file
makes it machine-checked, and turns it into a **gate**: a frame family is now refuted by a
computation rather than by a bespoke Heisenberg witness.

## What is built, and at what generality

The class-two layer is approached through its **functionals** rather than through `Λ²` itself.
A `ℤ₂`-valued functional on `Λ²A` is an alternating form on `A`, the rank-≤2 forms span, and a
rank-≤2 form is exactly what a homomorphism to a Heisenberg group records.  So §1 builds

```text
SqHeis R = {(a, b, c) : R³},   (a,b,c)·(a',b',c') = (a+a', b+b', c+c'+a·b')
⁅p, q⁆ = (0, 0, p.a·q.b − q.a·p.b)          -- the rank-≤2 alternating form
```

over any commutative ring, pro-2 whenever `#R` is a power of `2` (`SqHeis.isProP_two`), and §2
computes the relator there **in closed form**:

```text
(sqRelWord m).a = −4·(m 1).a + 2·(m 2).a                       -- the relator vector ρ_sq
(sqRelWord m).c = −4·(m 1).c + 2·(m 2).c + sqHeisDefect h m
sqHeisDefect h m = ⟨σ̄, x̄₀⟩ + 10·(x̄₀-column)² + (x̄₁-column)² − 8·⟨x̄₀, x̄₁⟩ + Σⱼ ⟨ūⱼ, v̄ⱼ⟩
```

⭐ **The hand computation survived contact with Lean unchanged** — `SqHeis.sqWord_c` is the
formula the docstring's balance was derived from, term for term, on the first attempt.

## ⚠ What is *not* built: `gr₂ ≅ Λ²(D^ab)` as an isomorphism

Only the **realization half** is here: enough class-two quotients to evaluate the balance.  The
identification `gr₂ ≅ Λ²A` itself reduces (by an elementary argument, `r̄ = 2·t̄` being a
non-torsion vector of `F^ab = ℤ₂ⁿ`, so `R ∩ γ₂F = ⁅R, F⁆` mod `γ₃F`, and `Λ²` right exact) to
`gr₂(F) ≅ Λ²(F^ab)` for the **free pro-2 group** `F` — Magnus/Witt, which mathlib does not have.
That is the whole cost of the missing direction, and it is not needed by anything below: the
balance and every refutation are *necessary* conditions, so they need class-two quotients to
exist, not to be exhaustive.

## ⚠ Finding — the realizability parity, and why the coefficients are `ℤ/4`

Not every rank-2 form is realized.  Solving the relator's central equation needs
`sqHeisDefect` to land in `2R`, which (after `−4x̄₀ + 2x̄₁ = 0` forces the `x₁`-column to be
twice the `x₀`-column) is exactly

```text
ω(σ̄ ∧ x̄₀) + Σⱼ ω(ūⱼ ∧ v̄ⱼ) ≡ 0   (mod 2)
```

— i.e. `ω` must kill, mod `2`, the class of `t²`, where `t = x₁x₀⁻²` carries the order-two
summand of `A`.  This is not an artefact of `SqHeis`: `t` maps into the centre, so its square
maps to an even central element in *any* Heisenberg quotient.  The way past it is to test with
`2·χ` instead of `χ` — always realizable, and harmless because `ℤ₂` is torsion-free.  ⭐ That is
why §5 and §6 run over `ℤ/4` and **not** over `ℤ/2`: mod `2` the factor `2·χ` is invisible, and
the gate would see nothing.

## Contents

* **§1** `SqHeis R`, its group and pro-2 structure, and the commutator pairing;
* **§2** the closed form of `sqWord`, `handleWord` and `sqRelWord`; `sqHeisDefect`;
* **§3** `sqHeisHom` (markings classify class-two quotients) and `ℤ₂`-powers in the test group;
* **§4** ⭐⭐ `sqHeisBalance` — **the gate**;
* **§5** ⭐ the validation: `not_sqRelWord_sqEichFrame_of_gate` re-derives `LamFrames`' `V`-family
  refutation through the gate, matching `EichRefutation`'s bespoke `D₄` witness;
* **§6** ⭐⭐ `sqArbFrame_x0_dressing_forced` — the forced `x₀`-slot, with its ⚠ gauge note;
* **§7** stress pins, **§8** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide` (the two `decide` calls are on `ℤ/4`).  Every
declaration prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`).
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

/-! ### The test group as a pro-2 target -/

instance : TopologicalSpace (SqHeis R) := ⊥

instance : DiscreteTopology (SqHeis R) := ⟨rfl⟩

/-- **The test group is pro-2** whenever the coefficient ring is a finite 2-ring: its order is
`(#R)³`. -/
theorem isProP_two [Finite R] {m : ℕ} (hR : Nat.card R = 2 ^ m) : IsProP 2 (SqHeis R) :=
  isProP_of_isPGroup (IsPGroup.of_card (n := 3 * m) (by rw [nat_card, hR, ← pow_mul, mul_comm]))

end SqHeis

/-! ## §2 The relator in the test group

The whole class-two computation, in closed form.  Everything below is a consequence of these
three coordinate formulas: the abelian coordinates see only the relator vector `−4x̄₀ + 2x̄₁`,
and the central coordinate is the **class-two defect** — an explicit quadratic expression in the
abelian coordinates of the marking. -/

section RelWord

variable {R : Type} [CommRing R]

/-- A product of elements with vanishing abelian coordinates is central, with the central
coordinate the sum. -/
private theorem SqHeis.prod_of_central (l : List (SqHeis R))
    (hl : ∀ p ∈ l, p.a = 0 ∧ p.b = 0) :
    l.prod = ⟨0, 0, (l.map SqHeis.c).sum⟩ := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨hpa, hpb⟩ := hl p List.mem_cons_self
    rw [List.prod_cons, ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]
    have hmul : p * (⟨0, 0, (t.map SqHeis.c).sum⟩ : SqHeis R)
        = ⟨p.a + 0, p.b + 0, p.c + (t.map SqHeis.c).sum + p.a * 0⟩ := rfl
    rw [hmul, hpa, hpb]
    simp

variable {h : ℕ}

@[simp] theorem SqHeis.handleWord_a (u v : Fin h → SqHeis R) : (handleWord u v).a = 0 := by
  rw [handleWord, SqHeis.prod_of_central _ (by simp)]

@[simp] theorem SqHeis.handleWord_b (u v : Fin h → SqHeis R) : (handleWord u v).b = 0 := by
  rw [handleWord, SqHeis.prod_of_central _ (by simp)]

/-- ⭐ **The handle block contributes exactly the sum of the handle pairings.** -/
theorem SqHeis.handleWord_c (u v : Fin h → SqHeis R) :
    (handleWord u v).c = ∑ j, ((u j).a * (v j).b - (v j).a * (u j).b) := by
  rw [handleWord, SqHeis.prod_of_central _ (by simp), Fin.sum_univ_def]
  simp [List.map_map, Function.comp_def]

/-- The abelian `a`-coordinate of the core word: the relator vector `−4x̄₀ + 2x̄₁`. -/
@[simp] theorem SqHeis.sqWord_a (s x y : SqHeis R) :
    (sqWord s x y).a = -4 * x.a + 2 * y.a := by
  simp only [sqWord, SqHeis.mul_a, SqHeis.inv_a, SqHeis.conjP_a, SqHeis.pow_a, SqHeis.commP_a]
  push_cast
  ring

/-- The abelian `b`-coordinate of the core word. -/
@[simp] theorem SqHeis.sqWord_b (s x y : SqHeis R) :
    (sqWord s x y).b = -4 * x.b + 2 * y.b := by
  simp only [sqWord, SqHeis.mul_b, SqHeis.inv_b, SqHeis.conjP_b, SqHeis.pow_b, SqHeis.commP_b]
  push_cast
  ring

/-- ⭐⭐ **The class-two content of the core word.**  Beyond the linear part `−4c(x₀) + 2c(x₁)`
the core word contributes the pairing `⟨σ̄, x̄₀⟩`, together with three terms quadratic in the
`x₀`- and `x₁`-columns alone. -/
theorem SqHeis.sqWord_c (s x y : SqHeis R) :
    (sqWord s x y).c = -4 * x.c + 2 * y.c + (s.a * x.b - x.a * s.b)
      + 10 * (x.a * x.b) + y.a * y.b - 8 * (x.a * y.b) := by
  simp only [sqWord, SqHeis.mul_a, SqHeis.mul_c, SqHeis.inv_a, SqHeis.inv_b,
    SqHeis.inv_c, SqHeis.conjP_a, SqHeis.conjP_b, SqHeis.conjP_c, SqHeis.pow_a, SqHeis.pow_b,
    SqHeis.pow_c, SqHeis.commP_c]
  norm_num
  ring

/-- The abelian `a`-row of the relator: the relator vector `−4x̄₀ + 2x̄₁`. -/
@[simp] theorem SqHeis.sqRelWord_a (m : Fin (sqRank h) → SqHeis R) :
    (sqRelWord m).a = -4 * (m 1).a + 2 * (m 2).a := by
  rw [sqRelWord, SqHeis.mul_a, SqHeis.sqWord_a, SqHeis.handleWord_a, add_zero]

/-- The abelian `b`-row of the relator. -/
@[simp] theorem SqHeis.sqRelWord_b (m : Fin (sqRank h) → SqHeis R) :
    (sqRelWord m).b = -4 * (m 1).b + 2 * (m 2).b := by
  rw [sqRelWord, SqHeis.mul_b, SqHeis.sqWord_b, SqHeis.handleWord_b, add_zero]

variable (h) in
/-- **The class-two defect of a marking**: the central coordinate the relator would have if the
central coordinates of the marking were all `0`.  The whole file is the study of this expression:
it is the pairing `⟨σ̄, x̄₀⟩` plus the handle pairings, plus three terms supported on the `x₀`-
and `x₁`-columns alone. -/
def sqHeisDefect (m : Fin (sqRank h) → SqHeis R) : R :=
  ((m 0).a * (m 1).b - (m 1).a * (m 0).b)
    + 10 * ((m 1).a * (m 1).b) + (m 2).a * (m 2).b - 8 * ((m 1).a * (m 2).b)
    + ∑ j : Fin h, ((m (sqHandleIdxU j)).a * (m (sqHandleIdxV j)).b
        - (m (sqHandleIdxV j)).a * (m (sqHandleIdxU j)).b)

/-- ⭐⭐ **The relator in the test group, in closed form.**  The central coordinate splits into
the linear part `−4c(x₀) + 2c(x₁)`, which the central coordinates of the marking can adjust
freely in `2R`, and the **defect**, which they cannot touch. -/
theorem SqHeis.sqRelWord_c (m : Fin (sqRank h) → SqHeis R) :
    (sqRelWord m).c = -4 * (m 1).c + 2 * (m 2).c + sqHeisDefect h m := by
  rw [sqRelWord, SqHeis.mul_c, SqHeis.sqWord_c, SqHeis.handleWord_c, SqHeis.handleWord_b,
    mul_zero, add_zero, sqHeisDefect]
  ring

/-- ⭐ **The relator identity in the test group**, as three scalar equations. -/
theorem SqHeis.sqRelWord_eq_one_iff (m : Fin (sqRank h) → SqHeis R) :
    sqRelWord m = 1 ↔ -4 * (m 1).a + 2 * (m 2).a = 0 ∧ -4 * (m 1).b + 2 * (m 2).b = 0 ∧
      -4 * (m 1).c + 2 * (m 2).c + sqHeisDefect h m = 0 := by
  rw [SqHeis.eq_one_iff, SqHeis.sqRelWord_a, SqHeis.sqRelWord_b, SqHeis.sqRelWord_c]

end RelWord

/-! ## §3 The lift: markings of the test group classify class-two quotients -/

section Lift

variable {R : Type} [CommRing R] [Finite R] {mm : ℕ} {h : ℕ}

/-- ⭐ **The class-two test homomorphism** attached to a marking of `SqHeis R` killing the
relator.  This is the whole refutation engine: an alternating form of rank ≤ 2 on `D_sq(h)^ab`,
together with a solution of the relator's central equation, *is* a class-two quotient. -/
noncomputable def sqHeisHom (hR : Nat.card R = 2 ^ mm) (h : ℕ) (m : Fin (sqRank h) → SqHeis R)
    (hrel : sqRelWord m = 1) : ContinuousMonoidHom (DSq h : Type) (SqHeis R) :=
  sqLiftHom h (SqHeis.isProP_two hR) m hrel

@[simp] theorem sqHeisHom_gen (hR : Nat.card R = 2 ^ mm) (m : Fin (sqRank h) → SqHeis R)
    (hrel : sqRelWord m = 1) (i : Fin (sqRank h)) :
    sqHeisHom hR h m hrel (sqGen h i) = m i :=
  sqLiftHom_gen _ _ _ _ i

/-- Naturality of the commutator. -/
theorem map_commP {G H : Type*} [Group G] [Group H] {F : Type*} [FunLike F G H]
    [MonoidHomClass F G H] (φ : F) (x y : G) : φ (commP x y) = commP (φ x) (φ y) := by
  simp [commP]

/-- ⭐ **The class-two pairing of a test hom**: a commutator in `D_sq h` is read off by the
alternating form built from the two abelian coordinates. -/
theorem sqHeisHom_commP_c (hR : Nat.card R = 2 ^ mm) (m : Fin (sqRank h) → SqHeis R)
    (hrel : sqRelWord m = 1) (x y : (DSq h : Type)) :
    (sqHeisHom hR h m hrel (commP x y)).c
      = (sqHeisHom hR h m hrel x).a * (sqHeisHom hR h m hrel y).b
        - (sqHeisHom hR h m hrel y).a * (sqHeisHom hR h m hrel x).b := by
  rw [map_commP, SqHeis.commP_c]

/-- ⭐ **`ℤ₂`-powers in the test group**, for a base whose two abelian coordinates have zero
product — the only case the frames need, and the case in which the binomial correction of
`SqHeis.pow_c` disappears.  `π` is any reduction `ℤ₂ → R` with open fibres (for `R = ℤ/2^k` it
is `PadicInt.toZModPow k`, whose fibres are open by `isOpen_preimage_toZModPow`). -/
theorem SqHeis.zpowZtwo_of_mul_ab_eq_zero (hQ : IsProP 2 (SqHeis R)) (pi : ℤ_[2] →+* R)
    (hpi : ∀ T : Set R, IsOpen (pi ⁻¹' T)) {g : SqHeis R} (hg : g.a * g.b = 0) (u : ℤ_[2]) :
    zpowZtwo hQ g u = ⟨pi u * g.a, pi u * g.b, pi u * g.c⟩ := by
  set phi : Multiplicative ℤ_[2] →* SqHeis R :=
    { toFun := fun z => ⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c⟩
      map_one' := by ext <;> simp
      map_mul' := fun z w => by
        have hadd : pi (toAdd (z * w)) = pi (toAdd z) + pi (toAdd w) := by
          rw [show toAdd (z * w) = toAdd z + toAdd w from rfl, map_add]
        have hz : pi (toAdd z) * pi (toAdd w) * (g.a * g.b) = 0 := by rw [hg, mul_zero]
        ext
        · simp only [SqHeis.mul_a]; rw [hadd]; ring
        · simp only [SqHeis.mul_b]; rw [hadd]; ring
        · simp only [SqHeis.mul_c]; rw [hadd]; linear_combination -hz } with hphi
  have hcont : Continuous phi := by
    refine IsLocallyConstant.continuous fun s => ?_
    show IsOpen ((fun z : Multiplicative ℤ_[2] =>
      (⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c⟩ : SqHeis R)) ⁻¹' s)
    have hfact : (fun z : Multiplicative ℤ_[2] =>
        (⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c⟩ : SqHeis R)) ⁻¹' s
        = toAdd ⁻¹' (pi ⁻¹' {r : R | (⟨r * g.a, r * g.b, r * g.c⟩ : SqHeis R) ∈ s}) := rfl
    rw [hfact]
    exact (hpi _).preimage continuous_toAdd
  have hone : phi (ofAdd (1 : ℤ_[2])) = g := by
    show (⟨pi 1 * g.a, pi 1 * g.b, pi 1 * g.c⟩ : SqHeis R) = g
    rw [map_one]
    ext <;> simp
  have := zpowZtwoHom_unique hQ hcont u
  rw [hone] at this
  exact this.symm

end Lift

/-! ## §4 ⭐ The refutation engine

One lemma.  A frame killing the relator satisfies, in **every** class-two test group, the three
scalar equations of `SqHeis.sqRelWord_eq_one_iff` at its own slot images.  Testing a frame family
is therefore a computation: evaluate the test hom on the family's slots, plug into
`sqHeisDefect`, and check the defect equation. -/

section Engine

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐⭐ **The class-two balance.**  Every frame that kills the relator obeys the defect equation
in every class-two test group.  This is the gate: a frame family is refuted by exhibiting one
test hom at which the equation fails. -/
theorem sqHeisBalance (Phi : ContinuousMonoidHom (DSq h : Type) (SqHeis R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    -4 * (Phi (n 1)).a + 2 * (Phi (n 2)).a = 0 ∧
      -4 * (Phi (n 1)).b + 2 * (Phi (n 2)).b = 0 ∧
        -4 * (Phi (n 1)).c + 2 * (Phi (n 2)).c + sqHeisDefect h (fun i => Phi (n i)) = 0 := by
  have hkey := SqHeis.sqRelWord_eq_one_iff (R := R) (h := h) fun i => Phi (n i)
  rw [← map_sqRelWord Phi n, hn, map_one] at hkey
  exact hkey.mp rfl

/-- The defect equation alone, which is the one that carries class-two information. -/
theorem sqHeisDefect_balance (Phi : ContinuousMonoidHom (DSq h : Type) (SqHeis R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    -4 * (Phi (n 1)).c + 2 * (Phi (n 2)).c + sqHeisDefect h (fun i => Phi (n i)) = 0 :=
  (sqHeisBalance Phi n hn).2.2

end Engine

/-! ## §5 Validation — the `V`-family refutation, re-derived through the gate

`EichRefutation` refutes `SqEichRelWord` by a bespoke `D₄` witness in which the cleared letter
`V` dies.  Here the same refutation comes out of §4's gate, at `ℤ/4` coefficients, with **no**
group-specific reasoning: the test hom is the alternating form dual to the cleared letter `Ū`,
the frame's slot images are computed, and the defect equation reads `−2 = 0` in `ℤ/4`.

The coefficient ring must be `ℤ/4` and not `ℤ/2`: the form realising the `Ū`-column is
`(2·χ) ∧ ν'`, whose factor `2` is forced (§6) and which is invisible mod 2. -/

section Validation

/-- The coefficient ring of the gate instance. -/
private abbrev gr2R : Type := ZMod (2 ^ 2)

/-- The reduction `ℤ₂ → ℤ/4`. -/
private noncomputable abbrev gr2Pi : ℤ_[2] →+* gr2R := PadicInt.toZModPow 2

private theorem gr2R_card : Nat.card gr2R = 2 ^ 2 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

private theorem isProP_two_gr2 : IsProP 2 (SqHeis gr2R) := SqHeis.isProP_two gr2R_card

private theorem gr2Pi_open (T : Set gr2R) : IsOpen (gr2Pi ⁻¹' T) :=
  isOpen_preimage_toZModPow 2 T

variable {h : ℕ} {j : Fin h}

variable (h j) in
/-- **The gate marking**: the alternating form `(2·χ_Ū) ∧ ν'` at the selected marking
`nuSel h j t 1`, with the central coordinate of the `x₁`-slot solving the relator's central
equation.  `σ ↦ (0,1,0)` puts `ν'` in the `b`-column, `x₀ ↦ 1` makes the pivot's `x₀`-leg
vanish for every exponent, and `u_j ↦ (2, t, 0)` is the `2·Ū`-dual. -/
private noncomputable def gr2Mark (t : ℤ_[2]) : Fin (sqRank h) → SqHeis gr2R :=
  fun i =>
    if (i : ℕ) = 0 then ⟨0, 1, 0⟩ else
    if (i : ℕ) = 2 then ⟨0, 0, -1⟩ else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then ⟨2, gr2Pi t, 0⟩ else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then ⟨0, 1, 0⟩ else 1

variable {t : ℤ_[2]}

@[simp] private theorem gr2Mark_zero : gr2Mark h j t 0 = ⟨0, 1, 0⟩ := by
  simp only [gr2Mark, sqVal_zero]
  norm_num

@[simp] private theorem gr2Mark_one : gr2Mark h j t 1 = 1 := by
  simp only [gr2Mark, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] private theorem gr2Mark_two : gr2Mark h j t 2 = ⟨0, 0, -1⟩ := by
  simp only [gr2Mark, sqVal_two, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega)]
  norm_num

@[simp] private theorem gr2Mark_handleU :
    gr2Mark h j t (sqHandleIdxU j) = ⟨2, gr2Pi t, 0⟩ := by
  simp only [gr2Mark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

@[simp] private theorem gr2Mark_handleV : gr2Mark h j t (sqHandleIdxV j) = ⟨0, 1, 0⟩ := by
  simp only [gr2Mark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

private theorem gr2Mark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    gr2Mark h j t (sqHandleIdxU j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [gr2Mark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem gr2Mark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    gr2Mark h j t (sqHandleIdxV j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [gr2Mark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The gate marking kills the relator: the handle pairing `2` is balanced by the `x₁`-slot's
central coordinate `−1`. -/
private theorem sqRelWord_gr2Mark : sqRelWord (gr2Mark h j t) = 1 := by
  rw [SqHeis.sqRelWord_eq_one_iff]
  refine ⟨by simp, by simp, ?_⟩
  rw [sqHeisDefect]
  rw [Finset.sum_eq_single j (fun j' _ hne => by
    rw [gr2Mark_handleU_ne hne, gr2Mark_handleV_ne hne]; simp) (fun hj => absurd
      (Finset.mem_univ j) hj)]
  simp only [gr2Mark_zero, gr2Mark_one, gr2Mark_two, gr2Mark_handleU, gr2Mark_handleV]
  norm_num

variable (h j t) in
/-- The gate's test homomorphism. -/
private noncomputable def gr2Hom : ContinuousMonoidHom (DSq h : Type) (SqHeis gr2R) :=
  sqHeisHom gr2R_card h (gr2Mark h j t) sqRelWord_gr2Mark

@[simp] private theorem gr2Hom_gen (i : Fin (sqRank h)) :
    gr2Hom h j t (sqGen h i) = gr2Mark h j t i :=
  sqHeisHom_gen _ _ _ i

/-- The pivot lands on the `ν'`-column generator, with no fact about `c₀` used. -/
private theorem gr2Hom_sqPivot : gr2Hom h j t (sqPivot h) = ⟨0, 1, 0⟩ := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_gr2, dsqX0, gr2Hom_gen, gr2Mark_one,
    zpowZtwo_one_base, inv_one, mul_one, dsqSigma, gr2Hom_gen, gr2Mark_zero]

/-- **The cleared `U` survives**, carrying the `2·Ū`-dual: the pivot power subtracted off is
exactly the `b`-coordinate the `u`-letter had. -/
private theorem gr2Hom_sqEichU : gr2Hom h j t (sqEichU h (nuSel h j t 1) j) = ⟨2, 0, 0⟩ := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr2, gr2Hom_sqPivot,
    nuSel_handleU, toAdd_ofAdd,
    SqHeis.zpowZtwo_of_mul_ab_eq_zero isProP_two_gr2 gr2Pi gr2Pi_open (by norm_num),
    gr2Hom_gen, gr2Mark_handleU]
  ext <;> simp

/-- **The cleared `V` dies**: the `v`-letter *is* the pivot's image at `ν'(v_j) = 1`. -/
private theorem gr2Hom_sqEichV : gr2Hom h j t (sqEichV h (nuSel h j t 1) j) = 1 := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr2, gr2Hom_sqPivot,
    nuSel_handleV, toAdd_ofAdd, zpowZtwo_one_exp, gr2Hom_gen, gr2Mark_handleV, mul_inv_cancel]

/-- Every `V`-dressing dies with `V`. -/
private theorem gr2Hom_dressV (x : (DSq h : Type)) (k : ℤ_[2]) :
    gr2Hom h j t (x * zpowZtwo (isProP_DSq h) (sqEichV h (nuSel h j t 1) j) k)
      = gr2Hom h j t x := by
  rw [map_mul, map_zpowZtwo (isProP_DSq h) isProP_two_gr2, gr2Hom_sqEichV, zpowZtwo_one_base,
    mul_one]

variable {e e' d : ℤ_[2]}

/-- ⭐ **The gate reproduces the known refutation.**  At a selected marking with `ν'(v_j) = 1`
the `V`-family's defect equation reads `−2 = 0` in `ℤ/4`, at every weight triple.  Compare
`EichRefutation.not_sqRelWord_sqEichFrame_nuSel_one`, proved there by a bespoke `D₄` witness. -/
theorem not_sqRelWord_sqEichFrame_of_gate (h : ℕ) (j : Fin h) (t e e' d : ℤ_[2]) :
    sqRelWord (sqEichFrame h (nuSel h j t 1) j e e' d) ≠ 1 := by
  intro hone
  have hbal := sqHeisDefect_balance (gr2Hom h j t) _ hone
  have hs0 : gr2Hom h j t (sqEichFrame h (nuSel h j t 1) j e e' d 0) = ⟨0, 1, 0⟩ := by
    rw [sqEichFrame_zero, gr2Hom_dressV, dsqSigma, gr2Hom_gen, gr2Mark_zero]
  have hs1 : gr2Hom h j t (sqEichFrame h (nuSel h j t 1) j e e' d 1) = 1 := by
    rw [sqEichFrame_one, gr2Hom_dressV, dsqX0, gr2Hom_gen, gr2Mark_one]
  have hs2 : gr2Hom h j t (sqEichFrame h (nuSel h j t 1) j e e' d 2) = ⟨0, 0, -1⟩ := by
    rw [sqEichFrame_two, gr2Hom_dressV, dsqX1, gr2Hom_gen, gr2Mark_two]
  have hsU : gr2Hom h j t (sqEichFrame h (nuSel h j t 1) j e e' d (sqHandleIdxU j))
      = ⟨2, 0, 0⟩ := by
    rw [sqEichFrame_handleU, gr2Hom_dressV, gr2Hom_sqEichU]
  have hsV : gr2Hom h j t (sqEichFrame h (nuSel h j t 1) j e e' d (sqHandleIdxV j)) = 1 := by
    rw [sqEichFrame_handleV, gr2Hom_sqEichV]
  rw [sqHeisDefect, Finset.sum_eq_single j (fun j' _ hne => by
      rw [sqEichFrame_handleU_ne hne, sqEichFrame_handleV_ne hne, gr2Hom_gen, gr2Hom_gen,
        gr2Mark_handleU_ne hne, gr2Mark_handleV_ne hne]
      simp) (fun hj => absurd (Finset.mem_univ j) hj)] at hbal
  rw [hs0, hs1, hs2, hsU, hsV] at hbal
  norm_num at hbal
  exact absurd hbal (by decide)

/-- ⚠ **`SqEichRelWord h` is false at every `h ≥ 1`**, through the gate.  This is
`EichRefutation.not_sqEichRelWord`, re-derived as a class-two computation. -/
theorem not_sqEichRelWord_of_gate {h : ℕ} (hh : 0 < h) : ¬ SqEichRelWord h := by
  intro H
  obtain ⟨e, e', d, hrel⟩ := H (nuSel h ⟨0, hh⟩ 0 1) ⟨0, hh⟩ nuSel_sigma nuSel_x0
  exact not_sqRelWord_sqEichFrame_of_gate h ⟨0, hh⟩ 0 e e' d hrel

/-- The gate's verdict **matches** the committed one, statement for statement. -/
example (h : ℕ) (j : Fin h) (t e e' d : ℤ_[2]) :
    sqRelWord (sqEichFrame h (nuSel h j t 1) j e e' d) ≠ 1 :=
  not_sqRelWord_sqEichFrame_nuSel_one h j t e e' d

end Validation

/-! ## §6 ⭐⭐ The class-two balance of the arbitrary-dressing frame, and the forced `x₀`-slot

This is the machine-checked form of `CommFrames`' Headline 3 ⭐ paragraph.  The test hom is the
alternating form `(2·χ) ∧ ν'`: the `b`-column **is** `ν'` (so every dressing, lying in
`ker ν'`, has `b`-coordinate `0`), and the `a`-column is twice a free functional `χ` on the
handle letters.  The factor `2` is not cosmetic — see the ⚠ at the end of §6. -/

section Forcing

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

/-- The projection of the test group onto its `b`-column: a continuous endomorphism, used to
compare two test homs through their `ν'`-columns alone. -/
private def bProj : ContinuousMonoidHom (SqHeis gr2R) (SqHeis gr2R) where
  toFun p := ⟨0, p.b, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp
  continuous_toFun := continuous_of_discreteTopology

/-- The `u`-row of the marking. -/
private noncomputable abbrev fT (h : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) : gr2R :=
  gr2Pi (toAdd (nu' (sqGen h (sqHandleIdxU j))))

/-- The `v`-row of the marking. -/
private noncomputable abbrev fS (h : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) : gr2R :=
  gr2Pi (toAdd (nu' (sqGen h (sqHandleIdxV j))))

variable (h j nu') in
/-- **The forcing marking**: the form `(2·χ) ∧ ν'` with `χ` given by the two free weights
`A, B` on the `j`-th handle.  The `x₁`-slot's central coordinate solves the relator's central
equation, which is possible **because** the `a`-column is even. -/
private noncomputable def fMark (A B : gr2R) : Fin (sqRank h) → SqHeis gr2R :=
  fun i =>
    if (i : ℕ) = 0 then ⟨0, 1, 0⟩ else
    if (i : ℕ) = 2 then ⟨0, 0, B * fT h nu' j - A * fS h nu' j⟩ else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then ⟨2 * A, fT h nu' j, 0⟩ else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then ⟨2 * B, fS h nu' j, 0⟩ else 1

variable {A B : gr2R}

@[simp] private theorem fMark_zero : fMark h nu' j A B 0 = ⟨0, 1, 0⟩ := by
  simp only [fMark, sqVal_zero]
  norm_num

@[simp] private theorem fMark_one : fMark h nu' j A B 1 = 1 := by
  simp only [fMark, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] private theorem fMark_two :
    fMark h nu' j A B 2 = ⟨0, 0, B * fT h nu' j - A * fS h nu' j⟩ := by
  simp only [fMark, sqVal_two, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega)]
  norm_num

@[simp] private theorem fMark_handleU :
    fMark h nu' j A B (sqHandleIdxU j) = ⟨2 * A, fT h nu' j, 0⟩ := by
  simp only [fMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

@[simp] private theorem fMark_handleV :
    fMark h nu' j A B (sqHandleIdxV j) = ⟨2 * B, fS h nu' j, 0⟩ := by
  simp only [fMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

private theorem fMark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    fMark h nu' j A B (sqHandleIdxU j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [fMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem fMark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    fMark h nu' j A B (sqHandleIdxV j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [fMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- ⭐ **The forcing marking kills the relator** — and the `x₁`-slot's central coordinate is
exactly what it takes.  This is the realizability of the form `(2·χ) ∧ ν'`. -/
private theorem sqRelWord_fMark : sqRelWord (fMark h nu' j A B) = 1 := by
  rw [SqHeis.sqRelWord_eq_one_iff]
  refine ⟨by simp, by simp, ?_⟩
  rw [sqHeisDefect, Finset.sum_eq_single j (fun j' _ hne => by
    rw [fMark_handleU_ne hne, fMark_handleV_ne hne]; simp)
    (fun hj => absurd (Finset.mem_univ j) hj)]
  simp only [fMark_zero, fMark_one, fMark_two, fMark_handleU, fMark_handleV,
    SqHeis.one_a, SqHeis.one_b, SqHeis.one_c]
  ring

variable (h nu' j) in
/-- The forcing test homomorphism. -/
private noncomputable def fHom (A B : gr2R) : ContinuousMonoidHom (DSq h : Type) (SqHeis gr2R) :=
  sqHeisHom gr2R_card h (fMark h nu' j A B) sqRelWord_fMark

@[simp] private theorem fHom_gen (i : Fin (sqRank h)) :
    fHom h nu' j A B (sqGen h i) = fMark h nu' j A B i :=
  sqHeisHom_gen _ _ _ i

/-- ⭐ **The `b`-column of the forcing hom is `ν'`.**  Both sides are continuous homs into the
test group after projecting away the other two columns, so it is enough to check on generators —
which is the definition of the marking, plus `ν'(x₁) = 2ν'(x₀)`. -/
private theorem fHom_b (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hcl : ∀ j' : Fin h, j' ≠ j → nu' (sqGen h (sqHandleIdxU j')) = 1 ∧
      nu' (sqGen h (sqHandleIdxV j')) = 1) (x : (DSq h : Type)) :
    (fHom h nu' j A B x).b = gr2Pi (toAdd (nu' x)) := by
  have hcomp : bProj.comp (fHom h nu' j A B)
      = bProj.comp ((zpowZtwoHom isProP_two_gr2 (⟨0, 1, 0⟩ : SqHeis gr2R)).comp nu') := by
    refine dsq_hom_ext _ _ fun i => ?_
    show bProj (fHom h nu' j A B (sqGen h i))
      = bProj (zpowZtwoHom isProP_two_gr2 (⟨0, 1, 0⟩ : SqHeis gr2R) (nu' (sqGen h i)))
    rw [fHom_gen, show zpowZtwoHom isProP_two_gr2 (⟨0, 1, 0⟩ : SqHeis gr2R) (nu' (sqGen h i))
      = zpowZtwo isProP_two_gr2 (⟨0, 1, 0⟩ : SqHeis gr2R) (toAdd (nu' (sqGen h i))) from rfl,
      SqHeis.zpowZtwo_of_mul_ab_eq_zero isProP_two_gr2 gr2Pi gr2Pi_open (by norm_num)]
    show (⟨0, (fMark h nu' j A B i).b, 0⟩ : SqHeis gr2R)
      = ⟨0, gr2Pi (toAdd (nu' (sqGen h i))) * 1, 0⟩
    rw [mul_one]
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · rw [show (sqGen h 0 : (DSq h : Type)) = dsqSigma h from rfl, hsigma, fMark_zero]
      simp
    · rw [show (sqGen h 1 : (DSq h : Type)) = dsqX0 h from rfl, hx0, fMark_one]
      simp
    · rw [show (sqGen h 2 : (DSq h : Type)) = dsqX1 h from rfl, toAdd_nu_dsqX1 nu', hx0,
        fMark_two]
      simp
    · by_cases hjj : j' = j
      · subst hjj; rw [fMark_handleU]
      · rw [fMark_handleU_ne hjj, (hcl j' hjj).1]
        simp
    · by_cases hjj : j' = j
      · subst hjj; rw [fMark_handleV]
      · rw [fMark_handleV_ne hjj, (hcl j' hjj).2]
        simp
  have hx := DFunLike.congr_fun hcomp x
  have hxb : (⟨0, (fHom h nu' j A B x).b, 0⟩ : SqHeis gr2R)
      = ⟨0, (zpowZtwo isProP_two_gr2 (⟨0, 1, 0⟩ : SqHeis gr2R) (toAdd (nu' x))).b, 0⟩ := hx
  rw [SqHeis.zpowZtwo_of_mul_ab_eq_zero isProP_two_gr2 gr2Pi gr2Pi_open (by norm_num)] at hxb
  have := congrArg SqHeis.b hxb
  simpa using this

/-- The pivot lands on the `ν'`-column generator. -/
private theorem fHom_sqPivot : fHom h nu' j A B (sqPivot h) = ⟨0, 1, 0⟩ := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_gr2, dsqX0, fHom_gen, fMark_one,
    zpowZtwo_one_base, inv_one, mul_one, dsqSigma, fHom_gen, fMark_zero]

/-- The cleared `U` carries the `2·χ(Ū)`-value, with the `ν'`-column subtracted off. -/
private theorem fHom_sqEichU : fHom h nu' j A B (sqEichU h nu' j) = ⟨2 * A, 0, 0⟩ := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr2, fHom_sqPivot,
    SqHeis.zpowZtwo_of_mul_ab_eq_zero isProP_two_gr2 gr2Pi gr2Pi_open (by norm_num),
    fHom_gen, fMark_handleU]
  ext <;> simp

/-- …and the cleared `V` likewise. -/
private theorem fHom_sqEichV :
    fHom h nu' j A B (sqEichV h nu' j) = ⟨2 * B, 0, -(2 * B * fS h nu' j)⟩ := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr2, fHom_sqPivot,
    SqHeis.zpowZtwo_of_mul_ab_eq_zero isProP_two_gr2 gr2Pi gr2Pi_open (by norm_num),
    fHom_gen, fMark_handleV]
  ext <;> simp

/-- ⭐⭐ **The `x₀`-slot dressing is forced.**  At every selected marking whose other handles are
already cleared, every dressing tuple killing the relator in the `x₁ = x₀²` gauge satisfies

```text
ā₁ = −ν'(v_j)·Ū + ν'(u_j)·V̄
```

tested against every alternating form `(2·χ) ∧ ν'`.  This is `CommFrames`' Headline 3 ⭐
paragraph, machine-checked: the `w̄`-column of `K ⊗ P` is reached by **no** dressing except the
`x₀`-slot's, and the balance there pins it to a non-zero value as soon as one of the two handle
rows is non-zero.

⚠ The gauge hypothesis `hsq : a 2 = a 1 ^ 2` is **not** decoration — see the ⚠ note below. -/
theorem sqArbFrame_x0_dressing_forced
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hcl : ∀ j' : Fin h, j' ≠ j → nu' (sqGen h (sqHandleIdxU j')) = 1 ∧
      nu' (sqGen h (sqHandleIdxV j')) = 1)
    {a : Fin (sqRank h) → (DSq h : Type)} (ha : ∀ i, nu' (a i) = 1) (hsq : a 2 = a 1 ^ 2)
    (hrel : sqRelWord (sqArbFrame h nu' j a) = 1) (A B : gr2R) :
    (fHom h nu' j A B (a 1)).a
      = -(fS h nu' j) * (fHom h nu' j A B (sqEichU h nu' j)).a
        + fT h nu' j * (fHom h nu' j A B (sqEichV h nu' j)).a := by
  have hab : ∀ i, (fHom h nu' j A B (a i)).b = 0 := by
    intro i
    rw [fHom_b hsigma hx0 hcl, ha i]
    simp
  have hbal := sqHeisDefect_balance (fHom h nu' j A B) _ hrel
  have hs0 : fHom h nu' j A B (sqArbFrame h nu' j a 0)
      = (⟨0, 1, 0⟩ : SqHeis gr2R) * fHom h nu' j A B (a 0) := by
    rw [sqArbFrame, sqArbBase_zero, map_mul, dsqSigma, fHom_gen, fMark_zero]
  have hs1 : fHom h nu' j A B (sqArbFrame h nu' j a 1) = fHom h nu' j A B (a 1) := by
    rw [sqArbFrame, sqArbBase_one, map_mul, dsqX0, fHom_gen, fMark_one, one_mul]
  have hs2 : fHom h nu' j A B (sqArbFrame h nu' j a 2)
      = (⟨0, 0, B * fT h nu' j - A * fS h nu' j⟩ : SqHeis gr2R) *
        (fHom h nu' j A B (a 1)) ^ 2 := by
    rw [sqArbFrame, sqArbBase_two, map_mul, dsqX1, fHom_gen, fMark_two, hsq, map_pow]
  have hsU : fHom h nu' j A B (sqArbFrame h nu' j a (sqHandleIdxU j))
      = (⟨2 * A, 0, 0⟩ : SqHeis gr2R) * fHom h nu' j A B (a (sqHandleIdxU j)) := by
    rw [sqArbFrame, sqArbBase_handleU, map_mul, fHom_sqEichU]
  have hsV : fHom h nu' j A B (sqArbFrame h nu' j a (sqHandleIdxV j))
      = (⟨2 * B, 0, -(2 * B * fS h nu' j)⟩ : SqHeis gr2R) *
        fHom h nu' j A B (a (sqHandleIdxV j)) := by
    rw [sqArbFrame, sqArbBase_handleV, map_mul, fHom_sqEichV]
  rw [sqHeisDefect, Finset.sum_eq_single j (fun j' _ hne => by
      rw [sqArbFrame, sqArbFrame, sqArbBase_handleU_ne hne, sqArbBase_handleV_ne hne,
        map_mul, map_mul, fHom_gen, fHom_gen, fMark_handleU_ne hne, fMark_handleV_ne hne]
      simp [hab]) (fun hj => absurd (Finset.mem_univ j) hj)] at hbal
  rw [hs0, hs1, hs2, hsU, hsV] at hbal
  simp only [SqHeis.mul_a, SqHeis.mul_b, SqHeis.mul_c, SqHeis.pow_a, SqHeis.pow_b, SqHeis.pow_c,
    hab] at hbal
  rw [fHom_sqEichU, fHom_sqEichV]
  push_cast at hbal
  linear_combination -hbal

/-- ⭐ The forced value is **non-zero** whenever a handle row is: the `x₀`-slot must be dressed
by the *handle* letters `U^{−s}V^{t}`, never by the core.  Here the `Ū`-dual instance `A = 1`,
`B = 0`. -/
theorem sqArbFrame_x0_dressing_forced_uDual
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hcl : ∀ j' : Fin h, j' ≠ j → nu' (sqGen h (sqHandleIdxU j')) = 1 ∧
      nu' (sqGen h (sqHandleIdxV j')) = 1)
    {a : Fin (sqRank h) → (DSq h : Type)} (ha : ∀ i, nu' (a i) = 1) (hsq : a 2 = a 1 ^ 2)
    (hrel : sqRelWord (sqArbFrame h nu' j a) = 1) :
    (fHom h nu' j 1 0 (a 1)).a = -(2 * fS h nu' j) := by
  rw [sqArbFrame_x0_dressing_forced hsigma hx0 hcl ha hsq hrel 1 0, fHom_sqEichU, fHom_sqEichV]
  ring

end Forcing

/-! ### ⚠ The gauge hypothesis is load-bearing

`CommFrames`' ⭐ paragraph counts **four** dressings (`ā₀`, `ā₁`, `ā₃`, `ā₄`) and never mentions
the `x₁`-slot's `ā₂`.  The frame has five slots, and the abelian row only says
`−4ā₁ + 2ā₂ = 0`, i.e. `ā₂ = 2ā₁ + τ` with `2τ = 0` — it does **not** say `a₂ = a₁²`.

The difference matters.  In the balance the `x₁`-slot enters through `−4c(a₁) + 2c(a₂)`, which is
`c` of the square `(a₂a₁⁻²)²`; the class of that square in `γ₂/γ₃` is well defined only modulo
`2·Λ²A`, and its `K ⊗ ⟨w̄⟩`-component is `−Σⱼ(sⱼŪⱼ − tⱼV̄ⱼ)` when `τ = t̄` — precisely `−Δ₀`
at one handle.  So **without the gauge the balance leaves two branches**, `ā₁ = −sŪ + tV̄` and
`ā₁ = 0`, rather than forcing the first.

⭐ In the gauge `a₂ = a₁²` the square is trivial and the forcing is exact; every Eichler family
of `LamFrames`/`UVFrames` is in that gauge (its `x₁`-slot weight is literally `2e'`), so the
`x₀`-slot forcing applies to all of them as stated.  The honest general statement is the
two-branch one, and `CommFrames`' "one of four dressings forced, three free" should be read as
"in the `x₁ = x₀²` gauge". -/

/-! ## §7 Stress pins -/

section StressTests

/-- Stress: the test group is not abelian — the pairing really is non-degenerate. -/
example : commP (⟨1, 0, 0⟩ : SqHeis (ZMod (2 ^ 2))) ⟨0, 1, 0⟩ = ⟨0, 0, 1⟩ := by
  ext <;> simp

/-- Stress: the class-two defect of the *standard* marking vanishes, as it must. -/
example (h : ℕ) : sqHeisDefect h (fun _ => (1 : SqHeis (ZMod (2 ^ 2)))) = 0 := by
  simp [sqHeisDefect]

/-- Stress: the gate is not vacuous — the trivial marking passes it. -/
example (h : ℕ) :
    sqRelWord (fun _ : Fin (sqRank h) => (1 : SqHeis (ZMod (2 ^ 2)))) = 1 := by
  rw [SqHeis.sqRelWord_eq_one_iff]
  refine ⟨by simp, by simp, ?_⟩
  simp [sqHeisDefect]

/-- Stress: the gate's verdict on the `V`-family agrees with the committed refutation. -/
example {h : ℕ} (hh : 0 < h) : ¬ SqEichRelWord h := not_sqEichRelWord_of_gate hh

/-- Stress: …and so does `EichRefutation`'s. -/
example {h : ℕ} (hh : 0 < h) : ¬ SqEichRelWord h := not_sqEichRelWord hh

/-- Stress: the forcing is a statement about a **non-zero** value — at `ν'(v_j) = 1` the
`x₀`-slot's `Ū`-dual coordinate is `−2 ≠ 0` in `ℤ/4`. -/
example : -(2 * (1 : ZMod (2 ^ 2))) ≠ 0 := by decide

end StressTests

/-! ## §8 Axiom pins

Committed prints: the whole file is **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable. -/

section AxiomPins

#print axioms SqHeis
#print axioms SqHeis.one_a
#print axioms SqHeis.one_b
#print axioms SqHeis.one_c
#print axioms SqHeis.mul_a
#print axioms SqHeis.mul_b
#print axioms SqHeis.mul_c
#print axioms SqHeis.inv_a
#print axioms SqHeis.inv_b
#print axioms SqHeis.inv_c
#print axioms SqHeis.eq_one_iff
#print axioms SqHeis.aHom
#print axioms SqHeis.bHom
#print axioms SqHeis.aHom_apply
#print axioms SqHeis.bHom_apply
#print axioms SqHeis.zHom
#print axioms SqHeis.zHom_a
#print axioms SqHeis.zHom_b
#print axioms SqHeis.zHom_c
#print axioms SqHeis.commP_a
#print axioms SqHeis.commP_b
#print axioms SqHeis.commP_c
#print axioms SqHeis.conjP_a
#print axioms SqHeis.conjP_b
#print axioms SqHeis.conjP_c
#print axioms SqHeis.pow_a
#print axioms SqHeis.pow_b
#print axioms SqHeis.pow_c
#print axioms SqHeis.equivProd
#print axioms SqHeis.nat_card
#print axioms SqHeis.isProP_two
#print axioms SqHeis.prod_of_central
#print axioms SqHeis.handleWord_a
#print axioms SqHeis.handleWord_b
#print axioms SqHeis.handleWord_c
#print axioms SqHeis.sqWord_a
#print axioms SqHeis.sqWord_b
#print axioms SqHeis.sqWord_c
#print axioms SqHeis.sqRelWord_a
#print axioms SqHeis.sqRelWord_b
#print axioms sqHeisDefect
#print axioms SqHeis.sqRelWord_c
#print axioms SqHeis.sqRelWord_eq_one_iff
#print axioms sqHeisHom
#print axioms sqHeisHom_gen
#print axioms map_commP
#print axioms sqHeisHom_commP_c
#print axioms SqHeis.zpowZtwo_of_mul_ab_eq_zero
#print axioms sqHeisBalance
#print axioms sqHeisDefect_balance
#print axioms gr2R
#print axioms gr2Pi
#print axioms gr2R_card
#print axioms isProP_two_gr2
#print axioms gr2Pi_open
#print axioms gr2Mark
#print axioms gr2Mark_zero
#print axioms gr2Mark_one
#print axioms gr2Mark_two
#print axioms gr2Mark_handleU
#print axioms gr2Mark_handleV
#print axioms gr2Mark_handleU_ne
#print axioms gr2Mark_handleV_ne
#print axioms sqRelWord_gr2Mark
#print axioms gr2Hom
#print axioms gr2Hom_gen
#print axioms gr2Hom_sqPivot
#print axioms gr2Hom_sqEichU
#print axioms gr2Hom_sqEichV
#print axioms gr2Hom_dressV
#print axioms not_sqRelWord_sqEichFrame_of_gate
#print axioms not_sqEichRelWord_of_gate
#print axioms bProj
#print axioms fT
#print axioms fS
#print axioms fMark
#print axioms fMark_zero
#print axioms fMark_one
#print axioms fMark_two
#print axioms fMark_handleU
#print axioms fMark_handleV
#print axioms fMark_handleU_ne
#print axioms fMark_handleV_ne
#print axioms sqRelWord_fMark
#print axioms fHom
#print axioms fHom_gen
#print axioms fHom_b
#print axioms fHom_sqPivot
#print axioms fHom_sqEichU
#print axioms fHom_sqEichV
#print axioms sqArbFrame_x0_dressing_forced
#print axioms sqArbFrame_x0_dressing_forced_uDual

end AxiomPins

/-! ## §9 Scoping note — what `gr₃` would need

Not attempted here.  The shape of the work, for whoever takes it:

1. **A class-three test object.**  `SqHeis R` is the rank-2 Heisenberg; the class-three analogue
   is the unitriangular group `U₄(R)`, whose lower central series has `gr₃` free of rank `2` on
   `⁅⁅x,y⁆,x⁆`, `⁅⁅x,y⁆,y⁆`.  ⚠ **Rank 2 is no longer enough**: a degree-three functional such as
   `⁅⁅x̄,ȳ⁆,z̄⁆` with three independent characters does not factor through any rank-2 abelian
   quotient, so the test family must include genuinely rank-3 markings — which `U₄(R)` supplies
   and a Heisenberg group does not.  §1's pattern (componentwise `simp` lemmas, `Finite` +
   `IsPGroup.of_card` for pro-2, `⊥` topology) transposes verbatim; the cost is that `conjP` and
   `commP` no longer collapse to a single coordinate, so §2's closed form gets three more
   coordinates, each cubic in the abelian columns and linear in the class-two ones.

2. **The realizability parity repeats, one level down.**  §2's obstruction was that the relator's
   central coordinate is only adjustable in `2R`, because the slot exponents are `(0, −4, 2, 0, 0)`
   and `gcd(4, 2) = 2`.  At class three the same exponents govern the top coordinate, so the
   adjustable subgroup is again `2R` while the defect is one degree higher; expect the test ring
   to have to be `ℤ/8` (or `ℤ/16`), and the `2·χ` trick of §6 to become `4·χ`.

3. ⚠ **Why the class-three lift is a second-order problem, and stays one.**  Dressing slot `i` by
   `b ∈ F_k` changes the relator by `b^{ε_i}` with `(ε_i) = (0, −4, 2, 0, 0)` — **all even**.  So
   in the elementary-abelian layer `F_k/F_{k+1}` every first-order variation dies, and the
   class-three balance is not linear in the new dressing data.  `SqHeis.pow_c` is the class-two
   shadow of exactly this: `(p^n).c = n·p.c + C(n,2)·(p.a·p.b)`, whose *linear* part `n·p.c`
   vanishes mod `2` for even `n` while the *quadratic* part `C(n,2)·p.a·p.b` does not.  A
   class-three attack therefore cannot be a slot-by-slot solve; it needs the quadratic term as
   the leading term, i.e. a genuine second-order (Bockstein-type) analysis.

4. **What would make it worth doing.**  `gr₂` is now a gate, but the class-two balance is
   *under*-determined (§6: one dressing forced, the rest free), so it cannot by itself produce a
   dressing.  `gr₃` is where the remaining freedom is either consumed or shown to be obstructed;
   until then the class-3 stall is a statement about the lift, not about `SqLamMarkTransitivity`.
-/

end HeisGroup

end SqCore

end Dyadic

end GQ2
