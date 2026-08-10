/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedSigmaFour
import GQ2.Dyadic.SqCore.GradedContainFour

/-!
# W54-HOM: the class-four hom layer

Placeholder docstring, rewritten at the end of the lane.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The class-four carrier as a pro-2 target -/

section U5ProP

namespace SqU5

variable {R : Type} [CommRing R]

/-- The underlying ten-tuple, as an equivalence. -/
def equivProd : SqU5 R ≃ R × R × R × R × R × R × R × R × R × R where
  toFun p := (p.a, p.b, p.c, p.d, p.e, p.f, p.g, p.h, p.i, p.j)
  invFun v := ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite R] : Finite (SqU5 R) := Finite.of_equiv _ equivProd.symm

/-- The cardinality of the class-four test group. -/
theorem nat_card [Finite R] : Nat.card (SqU5 R) = Nat.card R ^ 10 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

instance : TopologicalSpace (SqU5 R) := ⊥

instance : DiscreteTopology (SqU5 R) := ⟨rfl⟩

/-- **The class-four test group is pro-2** whenever the coefficient ring is a finite 2-ring:
its order is `(#R)^10`. -/
theorem isProP_two [Finite R] {m : ℕ} (hR : Nat.card R = 2 ^ m) : IsProP 2 (SqU5 R) :=
  isProP_of_isPGroup (IsPGroup.of_card (n := 10 * m) (by rw [nat_card, hR, ← pow_mul, mul_comm]))

/-! ### The power laws -/

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

@[simp] theorem pow_a (p : SqU5 R) (n : ℕ) : (p ^ n).a = n * p.a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_a, ih]; push_cast; ring

@[simp] theorem pow_b (p : SqU5 R) (n : ℕ) : (p ^ n).b = n * p.b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_b, ih]; push_cast; ring

@[simp] theorem pow_c (p : SqU5 R) (n : ℕ) : (p ^ n).c = n * p.c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_c, ih]; push_cast; ring

@[simp] theorem pow_d (p : SqU5 R) (n : ℕ) : (p ^ n).d = n * p.d := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_d, ih]; push_cast; ring

theorem pow_e (p : SqU5 R) (n : ℕ) :
    (p ^ n).e = n * p.e + (n.choose 2 : ℕ) * (p.a * p.b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_e, ih, pow_a, choose_two_succ]
    push_cast
    ring

theorem pow_f (p : SqU5 R) (n : ℕ) :
    (p ^ n).f = n * p.f + (n.choose 2 : ℕ) * (p.b * p.c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_f, ih, pow_b, choose_two_succ]
    push_cast
    ring

theorem pow_g (p : SqU5 R) (n : ℕ) :
    (p ^ n).g = n * p.g + (n.choose 2 : ℕ) * (p.c * p.d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_g, ih, pow_c, choose_two_succ]
    push_cast
    ring

/-- The first class-three power law: `C(n,2)` on the two class-two/abelian pairings of the
first four columns, `C(n,3)` on the cubic abelian term.  This is `SqU4.pow_f` through
`toU4L`. -/
theorem pow_h (p : SqU5 R) (n : ℕ) :
    (p ^ n).h = n * p.h + (n.choose 2 : ℕ) * (p.a * p.f + p.e * p.c)
      + (n.choose 3 : ℕ) * (p.a * p.b * p.c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_h, ih, pow_a, pow_e, choose_two_succ, choose_three_succ]
    push_cast
    ring

/-- …and the second, through `toU4R`. -/
theorem pow_i (p : SqU5 R) (n : ℕ) :
    (p ^ n).i = n * p.i + (n.choose 2 : ℕ) * (p.b * p.g + p.f * p.d)
      + (n.choose 3 : ℕ) * (p.b * p.c * p.d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_i, ih, pow_b, pow_f, choose_two_succ, choose_three_succ]
    push_cast
    ring

/-- **The class-four power law**: the `(1,5)`-coordinate of `p^n` carries `C(n,2)` on the
three "outermost times innermost" products, `C(n,3)` on the three cubic terms and `C(n,4)`
on the quartic abelian monomial.  A **fourth** binomial layer appears here that class three
never saw, and it is what forces the `ℤ₂`-power lemma of section 4 to be stated with an
even obstruction rather than a vanishing one. -/
theorem pow_j (p : SqU5 R) (n : ℕ) :
    (p ^ n).j = n * p.j + (n.choose 2 : ℕ) * (p.a * p.i + p.e * p.g + p.h * p.d)
      + (n.choose 3 : ℕ) * (p.a * p.b * p.g + p.a * p.f * p.d + p.e * p.c * p.d)
      + (n.choose 4 : ℕ) * (p.a * p.b * p.c * p.d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_j, ih, pow_a, pow_e, pow_h, choose_two_succ, choose_three_succ,
      choose_four_succ]
    push_cast
    ring

end SqU5

end U5ProP

/-! ## 2 The lift: markings of the class-four test group classify class-four quotients -/

section Lift

variable {R : Type} [CommRing R] [Finite R] {mm : ℕ} {h : ℕ}

/-- **The class-four test homomorphism** attached to a marking of `SqU5 R` killing the
relator: four characters of `D_sq(h)^ab`, three solutions of the class-two defect equations,
two of the class-three equations and one of the class-four equation, *is* a class-four
quotient.  The verbatim transposition of `GradedThree`'s `sqU4Hom`. -/
noncomputable def sqU5Hom (hR : Nat.card R = 2 ^ mm) (h : ℕ) (m : Fin (sqRank h) → SqU5 R)
    (hrel : sqRelWord m = 1) : ContinuousMonoidHom (DSq h : Type) (SqU5 R) :=
  sqLiftHom h (SqU5.isProP_two hR) m hrel

@[simp] theorem sqU5Hom_gen (hR : Nat.card R = 2 ^ mm) (m : Fin (sqRank h) → SqU5 R)
    (hrel : sqRelWord m = 1) (i : Fin (sqRank h)) :
    sqU5Hom hR h m hrel (sqGen h i) = m i :=
  sqLiftHom_gen _ _ _ _ i

/-- **`ℤ₂`-powers in the class-four test group, with an even class-four obstruction.**

At class three (`SqU4.zpowZtwo_of_flat`) the map `n ↦ gⁿ` is `R`-linear exactly when the
three power corrections of `SqU4.pow_d/_e/_f` vanish, and every use of that lemma in the
committed slices supplies vanishing.  Class four has **four** binomial layers
(`SqU5.pow_j`), and the layer that the class-four sigma witness actually meets does **not**
vanish: at the witness `x₀`-slot `sigFourX` the class-four obstruction
`a·i + e·g + h·d` equals `2`, not `0`, so the mechanical transposition of the class-three
lemma does not apply.  What saves the situation is arithmetic rather than geometry:
`C(n,2)·(2w) = (n² − n)·w` is a **polynomial in `n` with integer coefficients**, so it
still factors through the ring map `pi : ℤ₂ → R` even though `C(n,2)` alone does not.  This
lemma is that observation, and it is the one step of the class-three transposition that is
not mechanical.

The remaining five conditions must still vanish on the nose (`C(n,2)` and `C(n,3)` are not
polynomial in `n` over `ℤ` after division), and the `C(n,3)`/`C(n,4)` layers are killed by
those same five: `a·b = b·c = c·d = 0` already annihilates `a·b·g`, `a·f·d`, `e·c·d` and
`a·b·c·d` once `a·f + e·c = 0 = b·g + f·d` is imposed on top of them. -/
theorem SqU5.zpowZtwo_of_flatTwo (hQ : IsProP 2 (SqU5 R)) (pi : ℤ_[2] →+* R)
    (hpi : ∀ T : Set R, IsOpen (pi ⁻¹' T)) {g : SqU5 R} {w : R}
    (hab : g.a * g.b = 0) (hbc : g.b * g.c = 0) (hcd : g.c * g.d = 0)
    (hh : g.a * g.f + g.e * g.c = 0) (hi : g.b * g.g + g.f * g.d = 0)
    (hj : g.a * g.i + g.e * g.g + g.h * g.d = 2 * w) (u : ℤ_[2]) :
    zpowZtwo hQ g u
      = ⟨pi u * g.a, pi u * g.b, pi u * g.c, pi u * g.d, pi u * g.e, pi u * g.f, pi u * g.g,
          pi u * g.h, pi u * g.i, pi u * g.j + (pi u * pi u - pi u) * w⟩ := by
  set phi : Multiplicative ℤ_[2] →* SqU5 R :=
    { toFun := fun z => ⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c,
        pi (toAdd z) * g.d, pi (toAdd z) * g.e, pi (toAdd z) * g.f, pi (toAdd z) * g.g,
        pi (toAdd z) * g.h, pi (toAdd z) * g.i,
        pi (toAdd z) * g.j + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * w⟩
      map_one' := by ext <;> simp
      map_mul' := fun z y => by
        have hadd : pi (toAdd (z * y)) = pi (toAdd z) + pi (toAdd y) := by
          rw [show toAdd (z * y) = toAdd z + toAdd y from rfl, map_add]
        ext
        · simp only [SqU5.mul_a]; rw [hadd]; ring
        · simp only [SqU5.mul_b]; rw [hadd]; ring
        · simp only [SqU5.mul_c]; rw [hadd]; ring
        · simp only [SqU5.mul_d]; rw [hadd]; ring
        · simp only [SqU5.mul_e]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hab
        · simp only [SqU5.mul_f]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hbc
        · simp only [SqU5.mul_g]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hcd
        · simp only [SqU5.mul_h]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hh
        · simp only [SqU5.mul_i]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hi
        · simp only [SqU5.mul_j]; rw [hadd]
          linear_combination (-(pi (toAdd z) * pi (toAdd y))) * hj } with hphi
  have hcont : Continuous phi := by
    refine IsLocallyConstant.continuous fun s => ?_
    show IsOpen ((fun z : Multiplicative ℤ_[2] =>
      (⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c, pi (toAdd z) * g.d,
        pi (toAdd z) * g.e, pi (toAdd z) * g.f, pi (toAdd z) * g.g, pi (toAdd z) * g.h,
        pi (toAdd z) * g.i,
        pi (toAdd z) * g.j + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * w⟩ :
          SqU5 R)) ⁻¹' s)
    have hfact : (fun z : Multiplicative ℤ_[2] =>
        (⟨pi (toAdd z) * g.a, pi (toAdd z) * g.b, pi (toAdd z) * g.c, pi (toAdd z) * g.d,
          pi (toAdd z) * g.e, pi (toAdd z) * g.f, pi (toAdd z) * g.g, pi (toAdd z) * g.h,
          pi (toAdd z) * g.i,
          pi (toAdd z) * g.j + (pi (toAdd z) * pi (toAdd z) - pi (toAdd z)) * w⟩ :
            SqU5 R)) ⁻¹' s
        = toAdd ⁻¹' (pi ⁻¹' {r : R | (⟨r * g.a, r * g.b, r * g.c, r * g.d, r * g.e, r * g.f,
            r * g.g, r * g.h, r * g.i, r * g.j + (r * r - r) * w⟩ : SqU5 R) ∈ s}) := rfl
    rw [hfact]
    exact (hpi _).preimage continuous_toAdd
  have hone : phi (ofAdd (1 : ℤ_[2])) = g := by
    show (⟨pi 1 * g.a, pi 1 * g.b, pi 1 * g.c, pi 1 * g.d, pi 1 * g.e, pi 1 * g.f, pi 1 * g.g,
      pi 1 * g.h, pi 1 * g.i, pi 1 * g.j + (pi 1 * pi 1 - pi 1) * w⟩ : SqU5 R) = g
    rw [map_one]
    ext <;> simp
  have := zpowZtwoHom_unique hQ hcont u
  rw [hone] at this
  exact this.symm

/-- **`ℤ₂`-powers in the class-four test group, flat base**: the verbatim transposition of
`SqU4.zpowZtwo_of_flat`, with **six** conditions instead of three - one for each of the
three class-two coordinates, one for each of the two class-three coordinates, and one for
the class-four coordinate.  These are exactly the conditions under which `n ↦ gⁿ` is
`R`-linear, by `SqU5.pow_e` through `SqU5.pow_j`.  It is the `w = 0` case of
`SqU5.zpowZtwo_of_flatTwo`. -/
theorem SqU5.zpowZtwo_of_flat (hQ : IsProP 2 (SqU5 R)) (pi : ℤ_[2] →+* R)
    (hpi : ∀ T : Set R, IsOpen (pi ⁻¹' T)) {g : SqU5 R}
    (hab : g.a * g.b = 0) (hbc : g.b * g.c = 0) (hcd : g.c * g.d = 0)
    (hh : g.a * g.f + g.e * g.c = 0) (hi : g.b * g.g + g.f * g.d = 0)
    (hj : g.a * g.i + g.e * g.g + g.h * g.d = 0) (u : ℤ_[2]) :
    zpowZtwo hQ g u
      = ⟨pi u * g.a, pi u * g.b, pi u * g.c, pi u * g.d, pi u * g.e, pi u * g.f, pi u * g.g,
          pi u * g.h, pi u * g.i, pi u * g.j⟩ := by
  rw [SqU5.zpowZtwo_of_flatTwo hQ pi hpi hab hbc hcd hh hi (w := 0) (by rw [hj]; ring)]
  ext <;> simp

end Lift

end SqCore

end Dyadic

end GQ2
