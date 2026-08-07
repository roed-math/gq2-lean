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
    (handleWord u v).c
      = (((List.finRange h).map fun j => (u j).a * (v j).b - (v j).a * (u j).b)).sum := by
  rw [handleWord, SqHeis.prod_of_central _ (by simp)]
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
    + (((List.finRange h).map fun j =>
        (m (sqHandleIdxU j)).a * (m (sqHandleIdxV j)).b
          - (m (sqHandleIdxV j)).a * (m (sqHandleIdxU j)).b)).sum

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

end HeisGroup

end SqCore

end Dyadic

end GQ2
