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

/-! ## 3 The class-four gate, and the containment, at the hom level -/

section Engine

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐ **The class-four gate.**  Every frame of `D_sq h` that kills the relator has an image
tuple killing the relator in **every** class-four test group.  One `rw`, and it is what turns
tuple-level statements about `SqU5 R` into statements about continuous homomorphisms. -/
theorem sqU5Balance (Phi : ContinuousMonoidHom (DSq h : Type) (SqU5 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1) :
    sqRelWord (fun i => Phi (n i)) = 1 := by
  rw [← map_sqRelWord Phi n, hn, map_one]

/-- The gate at the standard frame: the marked generators already satisfy the relation
(`dsq_relation`), so every class-four test hom sends them to a relator-solution. -/
theorem sqU5Balance_gen (Phi : ContinuousMonoidHom (DSq h : Type) (SqU5 R)) :
    sqRelWord (fun i => Phi (sqGen h i)) = 1 :=
  sqU5Balance Phi _ (dsq_relation h)

variable {z : Fin (sqRank h) → SqU5 R}

/-- ⭐⭐ **The pure-artefact containment, at the hom level.**  `GradedContainFour`'s
`sqRelWord_conFourDress_of_rel` says: at a *tuple* killing the relator, the defect of any
five-slot `γ₃`-dressing is the explicit translation element, reading the dressing alone
through the graded Fox form.  Through the gate the hypothesis becomes a statement about the
group: at the image of **any** frame of `D_sq h` killing the relator, under **any** class-four
test hom, the `K`-dressing defect is a pure artefact.  This is the campaign's target shape
with the tuple hypothesis discharged. -/
theorem sqRelWord_conFourDress_of_hom (Phi : ContinuousMonoidHom (DSq h : Type) (SqU5 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1)
    (hz : ∀ i, (z i).IsGaThree) :
    sqRelWord (conFourDress (fun i => Phi (n i)) z)
      = ⟨0, 0, 0, 0, 0, 0, 0, -4 * (z 1).h + 2 * (z 2).h, -4 * (z 1).i + 2 * (z 2).i,
          -4 * (z 1).j + 2 * (z 2).j + conFourShift h (fun i => Phi (n i)) z⟩ :=
  sqRelWord_conFourDress_of_rel hz (sqU5Balance Phi n hn)

/-- …and the central form once the dressing survives stage three, at the hom level. -/
theorem sqRelWord_conFourDress_liftC_of_hom (Phi : ContinuousMonoidHom (DSq h : Type) (SqU5 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1)
    (hz : ∀ i, (z i).IsGaThree)
    (hh : -4 * (z 1).h + 2 * (z 2).h = 0) (hi : -4 * (z 1).i + 2 * (z 2).i = 0) :
    sqRelWord (conFourDress (fun i => Phi (n i)) z)
      = liftC (-4 * (z 1).j + 2 * (z 2).j + conFourShift h (fun i => Phi (n i)) z) :=
  sqRelWord_conFourDress_liftC hz (sqU5Balance Phi n hn) hh hi

/-- ⭐⭐ **The engine kill at the hom level, odd regime**: at the image of any frame killing
the relator, whose `j`-handle `V`-slot columns admit a unit pairing, every stage-surviving
`γ₃`-`K`-dressing of the image is killed by one explicit achievable engine move.  The
committed `conFour_contain_odd` with its tuple hypothesis discharged by the gate. -/
theorem conFour_contain_odd_of_hom {j : Fin h} {zh zi rr : R}
    (Phi : ContinuousMonoidHom (DSq h : Type) (SqU5 R))
    (n : Fin (sqRank h) → (DSq h : Type)) (hn : sqRelWord n = 1)
    (hz : ∀ i, (z i).IsGaThree)
    (hh : -4 * (z 1).h + 2 * (z 2).h = 0) (hi : -4 * (z 1).i + 2 * (z 2).i = 0)
    (hmu : rr * (zh * (Phi (n (sqHandleIdxV j))).d - zi * (Phi (n (sqHandleIdxV j))).a) = 1) :
    sqRelWord (selLift j (conFourDress (fun i => Phi (n i)) z) 1 1
      ⟨0, 0, 0, 0, 0, 0, 0,
        -(rr * (-4 * (z 1).j + 2 * (z 2).j
          + conFourShift h (fun i => Phi (n i)) z) * zh),
        -(rr * (-4 * (z 1).j + 2 * (z 2).j
          + conFourShift h (fun i => Phi (n i)) z) * zi), 0⟩ 1) = 1 :=
  conFour_contain_odd hz (sqU5Balance Phi n hn) hh hi hmu

end Engine

/-! ## 4 The class-four sigma witness as a homomorphism -/

section SigmaHom

/-- The class-four test group over `ℤ/8` is pro-2. -/
theorem isProP_two_gr5 : IsProP 2 (SqU5 gr3R) := SqU5.isProP_two gr3R_card

/-- ⭐ **The class-four sigma-witness test hom.**  `GradedSigmaFour`'s binder point
`sigFourWit 1` kills the relator (`sqRelWord_sigFourWit_triv`), so the committed lift turns
it into an honest continuous homomorphism `D_sq 1 → U_5(ℤ/8)`.  Every tuple statement of
`GradedSigmaFour` at that point is now a statement about this hom. -/
noncomputable def sigFourHom : ContinuousMonoidHom (DSq 1 : Type) (SqU5 gr3R) :=
  sqU5Hom gr3R_card 1 (sigFourWit 1) sqRelWord_sigFourWit_triv

@[simp] theorem sigFourHom_gen (i : Fin (sqRank 1)) :
    sigFourHom (sqGen 1 i) = sigFourWit 1 i :=
  sqU5Hom_gen _ _ _ i

@[simp] theorem sigFourHom_sigma : sigFourHom (dsqSigma 1) = sigFourMark gr3R := by
  rw [dsqSigma, sigFourHom_gen, sigFourWit_zero, mul_one]

@[simp] theorem sigFourHom_x0 : sigFourHom (dsqX0 1) = sigFourX := by
  rw [dsqX0, sigFourHom_gen, sigFourWit_one]

@[simp] theorem sigFourHom_x1 : sigFourHom (dsqX1 1) = sigFourY := by
  rw [dsqX1, sigFourHom_gen, sigFourWit_two]

@[simp] theorem sigFourHom_handleU : sigFourHom (sqGen 1 (sqHandleIdxU 0)) = sigFourU := by
  rw [sigFourHom_gen]
  simp only [sigFourWit, sqHandleIdxU_val]
  norm_num

@[simp] theorem sigFourHom_handleV : sigFourHom (sqGen 1 (sqHandleIdxV 0)) = sigFourV := by
  rw [sigFourHom_gen]
  simp only [sigFourWit, sqHandleIdxV_val]
  norm_num

/-! ### The pivot anchor

The class-three slice got its pivot image for free: the `x0`-slot image of `GradedSigma`'s
family is `⟨A1, 0, C1, 0, 0, 0⟩`, whose vanishing `b`-column kills all three obstructions of
`SqU4.zpowZtwo_of_flat`, so `sigHom_sqPivot` is a two-line `rw`.  At class four this fails:
the sigma witness's `x0`-slot `sigFourX` has `a·i = 2 ≠ 0`, so the flat lemma does **not**
apply and the pivot image needs the even-obstruction lemma of section 2.  This is the one
place where the class-three transposition is not mechanical, and the anchor below is the
proof that the replacement works. -/

/-- ⭐ **The `x0`-slot's `ℤ₂`-powers at the sigma witness**, through the even-obstruction
lemma: the class-four coordinate is the *quadratic* `π(u)² − π(u)`, not a linear multiple. -/
theorem sigFourX_zpowZtwo (u : ℤ_[2]) :
    zpowZtwo isProP_two_gr5 sigFourX u
      = ⟨2 * gr3Pi u, 0, 0, 0, 0, 0, 0, 0, gr3Pi u, gr3Pi u * gr3Pi u - gr3Pi u⟩ := by
  rw [SqU5.zpowZtwo_of_flatTwo isProP_two_gr5 gr3Pi gr3Pi_open (w := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)]
  ext <;> simp [sigFourX]
  ring

/-- ⭐⭐ **The pivot image at the sigma-witness hom**, in closed form: the
`sqPivotExp`-dependence returns only through the residue `c = gr3Pi sqPivotExp`, and the
class-four coordinate is the quadratic `c² + c` that the even-obstruction lemma produced.
The class-three anchor `sigHom_sqPivot` one level up. -/
theorem sigFourHom_sqPivot :
    sigFourHom (sqPivot 1)
      = ⟨-(2 * gr3Pi sqPivotExp), 1, 0, 0, 0, 0, 0, 0, -gr3Pi sqPivotExp,
          gr3Pi sqPivotExp * gr3Pi sqPivotExp + gr3Pi sqPivotExp⟩ := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq 1) isProP_two_gr5, sigFourHom_x0, sigFourX_zpowZtwo,
    sigFourHom_sigma]
  ext <;> simp [sigFourMark]
  ring

end SigmaHom

/-! ## 5 The sigma forcing on `sqArbFrame` -/

section ArbSigma

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

/-- At a row where the `u`-letter is already `ν'`-trivial the cleared letter **is** the
letter: no pivot power is subtracted. -/
theorem sqEichU_of_cleared (hu : nu' (sqGen h (sqHandleIdxU j)) = 1) :
    sqEichU h nu' j = sqGen h (sqHandleIdxU j) := by
  rw [sqEichU, hu, toAdd_one, zpowZtwo_zero_exp, inv_one, one_mul]

/-- …and likewise for the `v`-letter. -/
theorem sqEichV_of_cleared (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    sqEichV h nu' j = sqGen h (sqHandleIdxV j) := by
  rw [sqEichV, hv, toAdd_one, zpowZtwo_zero_exp, inv_one, mul_one]

/-- **The undressed frame at an already-cleared handle is the standard frame.**  This is the
exact price of the transposition: `sigFourWit`'s handle slots are the *raw* generator images,
so a frame whose image is `sigFourWit` must have trivial pivot powers in both handle slots. -/
theorem sqArbBase_of_cleared (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (i : Fin (sqRank h)) :
    sqArbBase h nu' j i = sqGen h i := by
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqArbBase_zero]; rfl
  · rw [sqArbBase_one]; rfl
  · rw [sqArbBase_two]; rfl
  · by_cases hjj : j' = j
    · subst hjj; rw [sqArbBase_handleU, sqEichU_of_cleared hu]
    · rw [sqArbBase_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj; rw [sqArbBase_handleV, sqEichV_of_cleared hv]
    · rw [sqArbBase_handleV_ne hjj]

variable (h) in
/-- **The sigma-only dressing** of the arbitrary-dressing frame: the sigma slot dressed by
`g`, every other slot standing.  This is `GradedSigma`'s `sigDressF`/`sigDressO` shape with
the dressing element left free. -/
noncomputable def sigArbDress (g : (DSq h : Type)) : Fin (sqRank h) → (DSq h : Type) :=
  fun i => if (i : ℕ) = 0 then g else 1

@[simp] theorem sigArbDress_zero (g : (DSq h : Type)) : sigArbDress h g 0 = g := by
  simp only [sigArbDress, sqVal_zero]
  norm_num

theorem sigArbDress_ne {g : (DSq h : Type)} {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 0) :
    sigArbDress h g i = 1 := if_neg hi

/-- The sigma-only dressing is `λ`-trivial slotwise as soon as its one entry is. -/
theorem nuLam_sigArbDress {g : (DSq h : Type)} (hg : nuLam h g = 1) (i : Fin (sqRank h)) :
    nuLam h (sigArbDress h g i) = 1 := by
  by_cases h0 : (i : ℕ) = 0
  · rw [show i = 0 from Fin.val_injective (by rw [h0, sqVal_zero]), sigArbDress_zero, hg]
  · rw [sigArbDress_ne h0, map_one]

/-- …and `ν'`-trivial slotwise likewise: it belongs to the class the residual quantifies
over. -/
theorem nu_sigArbDress {g : (DSq h : Type)} (hg : nu' g = 1) (i : Fin (sqRank h)) :
    nu' (sigArbDress h g i) = 1 := by
  by_cases h0 : (i : ℕ) = 0
  · rw [show i = 0 from Fin.val_injective (by rw [h0, sqVal_zero]), sigArbDress_zero, hg]
  · rw [sigArbDress_ne h0, map_one]

/-- ⭐⭐ **The frame identification**: at an already-cleared handle row, the sigma-witness hom
sends the arbitrary-dressing frame with a sigma-only dressing `g` to exactly the class-four
sigma witness at the dressing value `sigFourHom g`.  This is `GradedSigma`'s
`sigEscHom_frame_F`/`_O` one level up, and it is what makes every tuple verdict of
`GradedSigmaFour` §6 a verdict about `sqArbFrame`. -/
theorem sigFourHom_sqArbFrame
    {nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])}
    (hu : nu' (sqGen 1 (sqHandleIdxU 0)) = 1) (hv : nu' (sqGen 1 (sqHandleIdxV 0)) = 1)
    (g : (DSq 1 : Type)) :
    (fun i => sigFourHom (sqArbFrame 1 nu' 0 (sigArbDress 1 g) i))
      = sigFourWit (sigFourHom g) := by
  rw [sigFourWit_eq_dress]
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sqArbFrame, sqArbBase_of_cleared hu hv, sigArbDress_zero, map_mul, sigFourHom_gen,
      sigFourDress_zero]
  · rw [sqArbFrame, sqArbBase_of_cleared hu hv, sigArbDress_ne h0, mul_one, sigFourHom_gen,
      sigFourDress_ne h0]

/-- ⭐⭐ **The class-four selection bit on `sqArbFrame`.**  At an already-cleared handle row,
the parity of the class-four residue of the frame's image is the parity of the sigma
dressing's own `chi_a`-character.  The `sqArbFrame_x0_dressing_forced` conclusion one slot
over, at the hom level. -/
theorem sqArbFrame_sigma_bit
    {nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])}
    (hu : nu' (sqGen 1 (sqHandleIdxU 0)) = 1) (hv : nu' (sqGen 1 (sqHandleIdxV 0)) = 1)
    {g : (DSq 1 : Type)} (hgb : (sigFourHom g).b = 0) :
    selPar ((sqRelWord fun i => sigFourHom (sqArbFrame 1 nu' 0 (sigArbDress 1 g) i)).j)
      = selPar (sigFourHom g).a := by
  rw [sigFourHom_sqArbFrame hu hv g, sigFourWit_bit hgb]

/-- ⭐⭐ **The class-four sigma forcing on `sqArbFrame` itself.**  At an already-cleared handle
row, a sigma dressing whose frame image is killed by **any** achievable five-slot class-four
refinement has an **even** `chi_a`-character.  This is `sigFourWit_sigma_forced` transported
through the gate: the hypothesis is now about an honest frame of `D_sq 1` and an honest
continuous homomorphism, not about a tuple.

The two carried hypotheses are named exactly:

* `hu`, `hv` say the handle is already `ν'`-cleared.  They are **forced** by the shape of the
  witness, not a convenience: `sigFourWit`'s handle slots are the raw generator images, so a
  pivot power in either handle slot would move the frame image off `sigFourWit` and out of
  reach of the committed forcing theorem (see the section-4 pivot anchor for what the
  displaced image would be).
* `hgb` is the class-four form of "the dressing is `ν'`-trivial": the `b`-column of
  `sigFourHom` is the character sending `σ` to `1` and every other letter to `0`, so it
  vanishes on every dressing built from the non-`σ` letters, and is checked on the nose at
  the three instances below. -/
theorem sqArbFrame_sigma_forced
    {nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])}
    (hu : nu' (sqGen 1 (sqHandleIdxU 0)) = 1) (hv : nu' (sqGen 1 (sqHandleIdxV 0)) = 1)
    {g : (DSq 1 : Type)} (hgb : (sigFourHom g).b = 0)
    {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₀ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₀)
    (l₃ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₃)
    (l₄ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift 0
      (fun i => sigFourHom (sqArbFrame 1 nu' 0 (sigArbDress 1 g) i)) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sigFourHom g).a = 0 := by
  rw [sigFourHom_sqArbFrame hu hv g] at hkill
  exact sigFourWit_sigma_forced hgb hz₀ hw₁ hw₂ hz₃ hz₄ l₀ l₃ l₄ hkill

end ArbSigma

end SqCore

end Dyadic

end GQ2
