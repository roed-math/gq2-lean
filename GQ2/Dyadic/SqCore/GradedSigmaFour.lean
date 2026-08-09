/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedLift

/-!
# W53-SIGMA: the sigma-slot selection at class four, and the escape executed

W51-SIGMA (`GradedSigma`) built the sigma-sensitive **class-three** slice and found the
blindness recurring one level deeper, with an exact diagnosis: mod 2, under the gates, the whole
sigma-reading `sigRead` factors through the `x0`-slot's deviation `(1 + u1, v1, w1)` from its
class-two-forced value, so on the forced gauge every channel is even (`sigRead_gauge_even`,
`sigPar_sound_blind`).  That docstring priced the escape exactly:

> A slice that decides the sigma-slot on the forced gauge must break the
> `(1 + u1, v1, w1)`-factorisation, i.e. stop reading sigma through `sqWord`'s
> `x`-conjugations only - the note's next layer up (class four, or the universal quotient
> itself).

W52-LIFT then built the class-four carrier `SqU5` (`GradedFour`) and the stage engine
(`GradedLift`).  This file executes the escape on that engine.  Everything below was derived and
cross-validated numerically before transcription (`scripts/w53_sigma/`, certified outputs in
`scripts/w53_sigma/results/`).

## Headline: class four sees the sigma slot on the forced gauge; the factorisation is broken

* **The sigma-slot move exists at class four, and it pairs one column further out**
  (paragraphs 1-2).  Conjugating by a `gamma_3`-element is a central translation
  (`conjP_of_gaThree`), so dressing the sigma letter translates the core word by
  `z.h * x.d - z.i * x.a` (⭐⭐ `sqWord_mul_gaThree_sigma`): the dressing's class-three
  coordinates paired against the `x0`-slot's **outermost** abelian columns `(a, d)`, where class
  three paired against the *inner* columns `(a, c)` (`GradedSigma.sqRelWord_sigRefine`).  The
  five-slot translation identity ⭐⭐ `sqRelWord_sigLift` adds this move to `GradedLift`'s four.
* **The whole sigma-reading is one explicit polynomial** (paragraphs 3-4).  For an arbitrary
  `nu'`-trivial dressing value `v` at the plain class-four sigma marking `(0, 1, 0, 0, ...)`,
  the six class-`<= 2` rows are untouched and the four top rows move by `sigFourG`, `sigFourH`,
  `sigFourI` and ⭐⭐ `sigFourRead` (`sqWord_sigFour_low/g/h/i/j`), transferred verbatim to the
  relator by ⭐⭐ `sqRelWord_sigFourDress`.  Unlike class three this needs **no wider marking**:
  the plain marking already reads the sigma slot, and the statement is about an arbitrary
  dressing *value* rather than a parametrised dressing model.
* **⭐⭐ The factorisation is broken** (paragraph 5).  On the class-two-forced `x0`-gauge - the
  `x0`-slot's abelian columns `a, c, d` and its two lower class-two coordinates `e, f` all even,
  the `x1`-slot's abelian columns even - the reading collapses to

  ```text
  v.a * (x.g + x.i)  +  v.d * x.h  +  v.e * x.g        (mod 2)
  ```

  (`sigFourRead_gauge`, `sigFourRead_gauge_par`).  Every coefficient is a **deep** coordinate of
  the `x0`-slot: its third class-two coordinate `x.g` and its two class-three coordinates `x.h`,
  `x.i`.  None of the three is pinned by any lower row, and none of the three exists at class
  three.  On the same gauge the third class-two row and **both** class-three rows still move by
  even amounts only (`sigFourG_gauge_even`, `sigFourH_gauge_even`, `sigFourI_gauge_even`): the
  blindness is exactly one level thick, and the class-four row is the first that sees through
  it.
* **⭐⭐ The forcing, executed** (paragraph 6).  At the explicit binder point `sigFourWit` -
  one handle, cleared letters `U = (1,0,0,0,...)`, `V = (2,0,0,0,...)`, `x0`-slot the class-two
  forced value `V` corrected by one `gamma_3`-element (`sigFourX_eq`), `x1`-slot solving the
  nine lower rows - the class-four selection bit is `selPar v.a` **on the nose**
  (⭐⭐ `sigFourWit_bit`), and every sigma dressing killing the relator after **any** achievable
  five-slot refinement has even `chi_a`-character (⭐⭐ `sigFourWit_sigma_forced`).  The
  undressed frame kills the relator outright, the class-two forced dressing leaves the even
  residue `2` and dies to one explicit `gamma_4`-move, and the letter `U` leaves the **odd**
  residue `1` and survives nothing (`sqRelWord_sigFourWit_triv/_V/_V_complete/_U`,
  `sqRelWord_sigFourWit_U_ne_one`).  Soundness is a theorem, not a hypothesis: at this point
  every generator of the achievable lattice `selLamThree` has both class-three coordinates even
  (`sigFourWit_lamThree_even`), so no refinement of any shape can flip the bit
  (`sigFourWit_increment_even`).
* **The residual obstruction, named and measured** (paragraph 7).  The reading has exactly three
  live channels `v.a`, `v.d`, `v.e`, and on the forced gauge the depth sweep's forced sigma
  dressing `a0 = a1` has all three even, because they are then the `x0`-slot's own `a`-, `d`-
  and `e`-coordinates, which the gauge makes even.  So class four reads the sigma slot's three
  `F_2`-characters and **identifies `a0 = a1` with `a0 = 1`**
  (`sigFourRead_gauge_blind`, `sigFourRead_gauge_sigma_eq_x0`, `sigFourWit_blind_pair`).  The
  sweep's `a0 = a1` forcing is therefore still not a class-four slice statement: it needs class
  five (where the reading acquires channels the class-two gauge does not control) or the
  universal quotient.

So: **PROVED** that the level-deeper blindness of `GradedSigma` breaks at class four - the
sigma slot's `chi_a`-character is decided on the very gauge where class three is provably blind,
with an explicit witness and a soundness theorem - and **MEASURED** that what survives is
exactly the three-character quotient above, with the residual obstruction named.

## Scope

Like `GradedFour` and `GradedLift`, this file works on the class-four carrier at the level of
**marking tuples** in `SqU5 R`: the pro-2/topology layer (`IsProP`, `zpowZtwo`, an `sqU5Hom`)
is not built, so no statement here claims that a given tuple is the image of a continuous
homomorphism on `D_sq h`.  What is proved is exactly what the selection calculus needs: the
relator's rows as functions of the slot values, the translation identity for the achievable
dressings, and the verdicts at an explicit point.  Building the class-four hom layer (mechanical
from `GradedThree` paragraphs 1 and 3) is what would turn `sigFourWit_sigma_forced` into a
statement about `sqArbFrame` itself, exactly as `GradedSigma` paragraph 6 does at class three.

## Contents

* **1** the sigma-slot `gamma_3`-move: `conjP_of_gaThree`, `sqWord_mul_gaThree_sigma`;
* **2** the five-slot class-four refinement `sigLift` and its translation identity;
* **3** the reading: the marking `sigFourMark`, the four row-shift forms, and the four
  `sqWord`-level identities;
* **4** the transfer to the relator: `SqU5.handleWord_d`, `sigFourDress`,
  `sqRelWord_sigFourDress`;
* **5** the gauge collapse and the class-three comparison;
* **6** the witness binder point, its three verdicts, its soundness, the bit and the forcing;
* **7** the residual obstruction;
* **8** axiom pins (all std-3).

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8` or on
`Fin`-indexed tuples over it.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The sigma-slot move at class four -/

section SigmaMove

variable {R : Type} [CommRing R]

/-- Conjugating by a product is conjugating twice. -/
private theorem conjP_mul_right (p g k : SqU5 R) : conjP p (g * k) = conjP (conjP p g) k := by
  simp only [conjP, mul_inv_rev, mul_assoc]

/-- Sliding a central `liftC` factor to the right past one letter. -/
private theorem mul_liftC_mul (p q : SqU5 R) (w : R) : p * liftC w * q = p * q * liftC w := by
  rw [mul_assoc, ← liftC_comm, ← mul_assoc]

/-- ⭐ **Conjugation by a `gamma_3`-element is a central translation**: it moves only the
class-four coordinate, by the pairing of the conjugator's class-three coordinates against the
*outermost* abelian columns of the conjugand.  At class three the same statement pairs against
the *inner* columns; this one-column shift is the whole escape of this file. -/
theorem conjP_of_gaThree {z : SqU5 R} (hz : z.IsGaThree) (p : SqU5 R) :
    conjP p z = p * liftC (z.i * p.a - z.h * p.d) := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg⟩ := hz
  rw [mul_liftC_apply]
  ext <;>
    simp only [SqU5.conjP_a, SqU5.conjP_b, SqU5.conjP_c, SqU5.conjP_d, SqU5.conjP_e,
      SqU5.conjP_f, SqU5.conjP_g, SqU5.conjP_h, SqU5.conjP_i, SqU5.conjP_j,
      ha, hb, hc, hd, he, hf, hg] <;>
    ring

/-- ⭐⭐ **The sigma-slot `gamma_3`-move on the core word**: dressing the sigma letter by a
`gamma_3`-element translates the core word by the central element pairing the dressing's
class-three coordinates against the `x0`-slot's **outermost** abelian columns `(a, d)`.  The
`x1`-slot never enters: the second occurrence of sigma sits inside a commutator, which swallows
the central factor. -/
theorem sqWord_mul_gaThree_sigma {z : SqU5 R} (hz : z.IsGaThree) (s x y : SqU5 R) :
    sqWord (s * z) x y = sqWord s x y * liftC (z.h * x.d - z.i * x.a) := by
  have hx : conjP x (s * z) = conjP x s * liftC (z.i * x.a - z.h * x.d) := by
    rw [conjP_mul_right, conjP_of_gaThree hz, SqU5.conjP_a, SqU5.conjP_d]
  have hy : conjP y (s * z) = conjP y s * liftC (z.i * y.a - z.h * y.d) := by
    rw [conjP_mul_right, conjP_of_gaThree hz, SqU5.conjP_a, SqU5.conjP_d]
  have hneg : -(z.i * x.a - z.h * x.d) = z.h * x.d - z.i * x.a := by ring
  rw [sqWord, sqWord, hx, hy, commP_mul_liftC_right, mul_inv_rev, liftC_inv, hneg,
    ← liftC_comm, mul_liftC_mul, mul_liftC_mul, mul_liftC_mul]

end SigmaMove

/-! ## 2 The five-slot class-four refinement -/

section SigmaLift

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

variable (j) in
/-- **The five-slot class-four refinement**: dress the sigma slot by a `gamma_3`-element `z0`,
the two exponent slots by `gamma_4`-elements, and the two `j`-handle slots by
`gamma_3`-elements.  This is `GradedLift`'s `selLift` plus the sigma-slot move that the
committed four-slot calculus lacks - the class-four transposition of `GradedSigma`'s
`sigRefine`. -/
def sigLift (m : Fin (sqRank h) → SqU5 R) (z₀ w₁ w₂ z₃ z₄ : SqU5 R) :
    Fin (sqRank h) → SqU5 R :=
  fun i => if (i : ℕ) = 0 then m i * z₀ else selLift j m w₁ w₂ z₃ z₄ i

variable {m : Fin (sqRank h) → SqU5 R} {z₀ w₁ w₂ z₃ z₄ : SqU5 R}

@[simp] theorem sigLift_zero : sigLift j m z₀ w₁ w₂ z₃ z₄ 0 = m 0 * z₀ := by
  simp only [sigLift, sqVal_zero]
  norm_num

@[simp] theorem sigLift_one : sigLift j m z₀ w₁ w₂ z₃ z₄ 1 = m 1 * w₁ := by
  simp only [sigLift, sqVal_one]
  rw [if_neg (by omega), selLift_one]

@[simp] theorem sigLift_two : sigLift j m z₀ w₁ w₂ z₃ z₄ 2 = m 2 * w₂ := by
  simp only [sigLift, sqVal_two]
  rw [if_neg (by omega), selLift_two]

@[simp] theorem sigLift_handleU {j' : Fin h} :
    sigLift j m z₀ w₁ w₂ z₃ z₄ (sqHandleIdxU j')
      = if j' = j then m (sqHandleIdxU j') * z₃ else m (sqHandleIdxU j') := by
  simp only [sigLift, sqHandleIdxU_val]
  rw [if_neg (by omega), selLift_handleU]

@[simp] theorem sigLift_handleV {j' : Fin h} :
    sigLift j m z₀ w₁ w₂ z₃ z₄ (sqHandleIdxV j')
      = if j' = j then m (sqHandleIdxV j') * z₄ else m (sqHandleIdxV j') := by
  simp only [sigLift, sqHandleIdxV_val]
  rw [if_neg (by omega), selLift_handleV]

/-- ⭐⭐ **The five-slot translation identity at class four**: the refinement translates the
relator by a central element, affine-linear in the five dressings, with the sigma-slot move
reading the `x0`-slot's outermost abelian columns and the two handle moves reading each other's.
Every class-`<= 3` row is untouched, and no closed form of the relator is consumed. -/
theorem sqRelWord_sigLift (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree) :
    sqRelWord (sigLift j m z₀ w₁ w₂ z₃ z₄)
      = sqRelWord m * liftC ((z₀.h * (m 1).d - z₀.i * (m 1).a) + (-4 * w₁.j + 2 * w₂.j)
          + ((z₃.h * (m (sqHandleIdxV j)).d - z₃.i * (m (sqHandleIdxV j)).a)
            + ((m (sqHandleIdxU j)).a * z₄.i - (m (sqHandleIdxU j)).d * z₄.h))) := by
  set m' : Fin (sqRank h) → SqU5 R := fun i => if (i : ℕ) = 0 then m i * z₀ else m i with hm'
  have hm'0 : m' 0 = m 0 * z₀ := by simp only [hm', sqVal_zero]; norm_num
  have hm'ne : ∀ i : Fin (sqRank h), (i : ℕ) ≠ 0 → m' i = m i := fun i hi => if_neg hi
  have hm'1 : m' 1 = m 1 := hm'ne 1 (by rw [sqVal_one]; omega)
  have hm'2 : m' 2 = m 2 := hm'ne 2 (by rw [sqVal_two]; omega)
  have hm'U : ∀ j' : Fin h, m' (sqHandleIdxU j') = m (sqHandleIdxU j') := fun j' =>
    hm'ne _ (by rw [sqHandleIdxU_val]; omega)
  have hm'V : ∀ j' : Fin h, m' (sqHandleIdxV j') = m (sqHandleIdxV j') := fun j' =>
    hm'ne _ (by rw [sqHandleIdxV_val]; omega)
  have hstep : sigLift j m z₀ w₁ w₂ z₃ z₄ = selLift j m' w₁ w₂ z₃ z₄ := by
    funext i
    by_cases hi : (i : ℕ) = 0
    · have hi0 : i = 0 := Fin.val_injective (by rw [hi, sqVal_zero])
      subst hi0
      rw [sigLift_zero, selLift_zero, hm'0]
    · simp only [sigLift, if_neg hi, selLift]
      by_cases h1 : (i : ℕ) = 1
      · rw [if_pos h1, if_pos h1, hm'ne i hi]
      by_cases h2 : (i : ℕ) = 2
      · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2, hm'ne i hi]
      by_cases hU : i = sqHandleIdxU j
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, if_pos hU, if_pos hU, hm'ne i hi]
      by_cases hV : i = sqHandleIdxV j
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, if_neg hU, if_neg hU, if_pos hV,
          if_pos hV, hm'ne i hi]
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, if_neg hU, if_neg hU, if_neg hV,
          if_neg hV, hm'ne i hi]
  have hzero : sqRelWord m' = sqRelWord m * liftC (z₀.h * (m 1).d - z₀.i * (m 1).a) := by
    rw [sqRelWord, sqRelWord, hm'0, hm'1, hm'2]
    rw [funext hm'U, funext hm'V, sqWord_mul_gaThree_sigma hz₀]
    exact mul_liftC_mul _ _ _
  rw [hstep, sqRelWord_selLift hw₁ hw₂ hz₃ hz₄, hm'U, hm'V, hzero, mul_assoc,
    liftC_mul_liftC]
  exact congrArg (fun w : R => sqRelWord m * liftC w) (by ring)

end SigmaLift

/-! ## 3 The sigma reading at class four -/

section Reading

variable {R : Type} [CommRing R]

variable (R) in
/-- **The class-four sigma marking**: the `nu'`-column generator with every other coordinate
zero, i.e. `GradedLift.selLiftWit`'s slot `0`.  Unlike class three, the sigma slot needs **no**
free `a`- and `c`-weights here: the plain marking already reads the sigma slot. -/
def sigFourMark : SqU5 R := ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[simp] theorem sigFourMark_b : (sigFourMark R).b = 1 := rfl

/-- The shift of the third class-two row (the `(c, d)`-pairing, new at class four) under a
sigma-slot dressing: the dressing's outer abelian columns paired against the `x0`-slot's. -/
def sigFourG (v x : SqU5 R) : R := v.c * x.d - v.d * x.c

/-- The shift of the left class-three row. -/
def sigFourH (v x : SqU5 R) : R :=
  v.a * (x.f - x.c) - v.c * (x.a + x.e) + v.e * x.c - v.f * x.a

/-- The shift of the right class-three row. -/
def sigFourI (v x : SqU5 R) : R := v.d * (x.c - x.f) + v.f * x.d

/-- ⭐⭐ **The class-four sigma-reading functional**: the exact amount by which the class-four
residue moves when the sigma slot is dressed by `v`, with the `x0`-slot value `x` and the
`x1`-slot value `y` as coefficients.  Eight of the dressing's ten coordinates are read; the
`b`-column is `0` by `nu'`-triviality and the class-four coordinate `v.j` is invisible.

The three coefficients that matter on the class-two-forced gauge are the ones on `v.a`, `v.d`
and `v.e`: they carry the `x0`-slot's **deep** coordinates `x.g`, `x.h`, `x.i`, which class
three cannot express at all. -/
def sigFourRead (v x y : SqU5 R) : R :=
  v.a * (4 * (x.c * x.d) - 2 * (x.c * y.d) - 4 * (x.d * x.f) + 2 * (x.f * y.d)
      - x.g + x.i - y.c * y.d + y.d * y.f)
    + v.c * (3 * (x.a * x.d) - 2 * (x.a * y.d) + 3 * (x.d * x.e) - 2 * (x.e * y.d)
      - y.a * y.d - 2 * (y.d * y.e))
    + v.d * (x.a * x.f + x.c * x.e - x.h - y.a * y.c + y.a * y.f + y.c * y.e)
    + v.e * (-4 * (x.c * x.d) + 2 * (x.c * y.d) + x.g + y.c * y.d)
    + v.f * (3 * (x.a * x.d) - 2 * (x.a * y.d) - 2 * (y.a * y.d))
    + v.g * (-x.a - x.e)
    + v.h * x.d - v.i * x.a
    + (v.a * v.d * (x.f - x.c) - v.a * v.f * x.d - v.c * v.e * x.d + v.d * v.e * x.c)

variable {v x y : SqU5 R}

/-- ⭐ **A sigma-slot dressing moves no row below the third class-two row**: the six
class-`<= 2` coordinates of the core word are untouched, exactly as at class three. -/
theorem sqWord_sigFour_low (hvb : v.b = 0) (hxb : x.b = 0) (hyb : y.b = 0) :
    (sqWord (sigFourMark R * v) x y).a = (sqWord (sigFourMark R) x y).a ∧
    (sqWord (sigFourMark R * v) x y).b = (sqWord (sigFourMark R) x y).b ∧
    (sqWord (sigFourMark R * v) x y).c = (sqWord (sigFourMark R) x y).c ∧
    (sqWord (sigFourMark R * v) x y).d = (sqWord (sigFourMark R) x y).d ∧
    (sqWord (sigFourMark R * v) x y).e = (sqWord (sigFourMark R) x y).e ∧
    (sqWord (sigFourMark R * v) x y).f = (sqWord (sigFourMark R) x y).f := by
  obtain ⟨va, vb, vc, vd, ve, vf, vg, vh, vi, vj⟩ := v
  obtain ⟨xa, xb, xc, xd, xe, xf, xg, xh, xi, xj⟩ := x
  obtain ⟨ya, yb, yc, yd, ye, yf, yg, yh, yi, yj⟩ := y
  have hv : vb = 0 := hvb
  have hx : xb = 0 := hxb
  have hy : yb = 0 := hyb
  subst hv; subst hx; subst hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul, sigFourMark,
      SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, 
      SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d,
      SqU5.inv_e, SqU5.inv_f] <;>
    ring

/-- ⭐ **The third class-two row moves** - the first thing class three could not see: at class
three the sigma slot's `b`-column is the constant `1` and its dressing never touches a row
below the top, whereas here the `(c, d)`-pairing reads it. -/
theorem sqWord_sigFour_g (hvb : v.b = 0) (hxb : x.b = 0) (hyb : y.b = 0) :
    (sqWord (sigFourMark R * v) x y).g = (sqWord (sigFourMark R) x y).g + sigFourG v x := by
  obtain ⟨va, vb, vc, vd, ve, vf, vg, vh, vi, vj⟩ := v
  obtain ⟨xa, xb, xc, xd, xe, xf, xg, xh, xi, xj⟩ := x
  obtain ⟨ya, yb, yc, yd, ye, yf, yg, yh, yi, yj⟩ := y
  have hv : vb = 0 := hvb
  have hx : xb = 0 := hxb
  have hy : yb = 0 := hyb
  subst hv; subst hx; subst hy
  simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul, sigFourMark, sigFourG,
    SqU5.mul_c, SqU5.mul_d, SqU5.mul_g,
    SqU5.inv_c, SqU5.inv_d,
    SqU5.inv_g]
  ring

/-- The left class-three row's shift. -/
theorem sqWord_sigFour_h (hvb : v.b = 0) (hxb : x.b = 0) (hyb : y.b = 0) :
    (sqWord (sigFourMark R * v) x y).h = (sqWord (sigFourMark R) x y).h + sigFourH v x := by
  obtain ⟨va, vb, vc, vd, ve, vf, vg, vh, vi, vj⟩ := v
  obtain ⟨xa, xb, xc, xd, xe, xf, xg, xh, xi, xj⟩ := x
  obtain ⟨ya, yb, yc, yd, ye, yf, yg, yh, yi, yj⟩ := y
  have hv : vb = 0 := hvb
  have hx : xb = 0 := hxb
  have hy : yb = 0 := hyb
  subst hv; subst hx; subst hy
  simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul, sigFourMark, sigFourH,
    SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_e, SqU5.mul_f, 
    SqU5.mul_h, SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, 
    SqU5.inv_e, SqU5.inv_f, SqU5.inv_h]
  ring

/-- The right class-three row's shift. -/
theorem sqWord_sigFour_i (hvb : v.b = 0) (hxb : x.b = 0) (hyb : y.b = 0) :
    (sqWord (sigFourMark R * v) x y).i = (sqWord (sigFourMark R) x y).i + sigFourI v x := by
  obtain ⟨va, vb, vc, vd, ve, vf, vg, vh, vi, vj⟩ := v
  obtain ⟨xa, xb, xc, xd, xe, xf, xg, xh, xi, xj⟩ := x
  obtain ⟨ya, yb, yc, yd, ye, yf, yg, yh, yi, yj⟩ := y
  have hv : vb = 0 := hvb
  have hx : xb = 0 := hxb
  have hy : yb = 0 := hyb
  subst hv; subst hx; subst hy
  simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul, sigFourMark, sigFourI,
    SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_f, SqU5.mul_g,
    SqU5.mul_i, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d,
    SqU5.inv_f, SqU5.inv_g, SqU5.inv_i]
  ring

set_option maxHeartbeats 1000000 in
/-- ⭐⭐ **The class-four row's shift is `sigFourRead`**, exactly - the class-four transposition
of `GradedSigma.sqRelWord_sigTuple_sigma`, stated for an arbitrary `nu'`-trivial dressing value
rather than a parametrised dressing model. -/
theorem sqWord_sigFour_j (hvb : v.b = 0) (hxb : x.b = 0) (hyb : y.b = 0) :
    (sqWord (sigFourMark R * v) x y).j = (sqWord (sigFourMark R) x y).j + sigFourRead v x y := by
  obtain ⟨va, vb, vc, vd, ve, vf, vg, vh, vi, vj⟩ := v
  obtain ⟨xa, xb, xc, xd, xe, xf, xg, xh, xi, xj⟩ := x
  obtain ⟨ya, yb, yc, yd, ye, yf, yg, yh, yi, yj⟩ := y
  have hv : vb = 0 := hvb
  have hx : xb = 0 := hxb
  have hy : yb = 0 := hyb
  subst hv; subst hx; subst hy
  simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul, sigFourMark, sigFourRead,
    SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g,
    SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d,
    SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i, SqU5.inv_j]
  ring

/-- The `gamma_3` special case of the reading is the move of paragraph 1: only the
`(h, i)`-pairing against the outermost columns survives. -/
theorem sigFourRead_of_gaThree (hz : v.IsGaThree) (x y : SqU5 R) :
    sigFourRead v x y = v.h * x.d - v.i * x.a := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg⟩ := hz
  simp only [sigFourRead, ha, hc, hd, he, hf, hg]
  ring

end Reading

/-! ## 4 The reading at the relator level -/

section RelatorShift

variable {R : Type} [CommRing R] {h : ℕ}

/-- The handle block has no fourth abelian column: it is a product of commutators, and the
`d`-column of a commutator vanishes.  Read off the right `U_4`-quotient. -/
theorem SqU5.handleWord_d (u v : Fin h → SqU5 R) : (handleWord u v).d = 0 := by
  have h1 : SqU5.toU4R (handleWord u v)
      = handleWord (fun k => SqU5.toU4R (u k)) (fun k => SqU5.toU4R (v k)) :=
    map_handleWord _ u v
  have h2 := congrArg SqU4.c h1
  rw [SqU4.handleWord_c] at h2
  simpa using h2

/-- **The sigma-dressed tuple**: the marking with the sigma slot multiplied by `v` on the
right and every other slot untouched. -/
def sigFourDress (m : Fin (sqRank h) → SqU5 R) (v : SqU5 R) : Fin (sqRank h) → SqU5 R :=
  fun i => if (i : ℕ) = 0 then m i * v else m i

variable {m : Fin (sqRank h) → SqU5 R} {v : SqU5 R}

@[simp] theorem sigFourDress_zero : sigFourDress m v 0 = m 0 * v := by
  simp only [sigFourDress, sqVal_zero]
  norm_num

theorem sigFourDress_ne {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 0) : sigFourDress m v i = m i :=
  if_neg hi

/-- ⭐⭐ **The four top rows of the relator under a sigma-slot dressing**, at the plain
class-four sigma marking with `nu'`-trivial exponent slots.  The three class-`<= 2` abelian rows
and the first two class-two rows are untouched; the third class-two row and the two class-three
rows move by the explicit shifts; and the class-four row moves by `sigFourRead`.  The handle
block never sees the sigma slot, so the transfer from `sqWord` to `sqRelWord` is verbatim - the
only input is that the handle block's fourth abelian column vanishes. -/
theorem sqRelWord_sigFourDress (hm0 : m 0 = sigFourMark R) (hxb : (m 1).b = 0)
    (hyb : (m 2).b = 0) (hvb : v.b = 0) :
    (sqRelWord (sigFourDress m v)).g = (sqRelWord m).g + sigFourG v (m 1) ∧
    (sqRelWord (sigFourDress m v)).h = (sqRelWord m).h + sigFourH v (m 1) ∧
    (sqRelWord (sigFourDress m v)).i = (sqRelWord m).i + sigFourI v (m 1) ∧
    (sqRelWord (sigFourDress m v)).j = (sqRelWord m).j + sigFourRead v (m 1) (m 2) := by
  have hone : sigFourDress m v 1 = m 1 := sigFourDress_ne (by rw [sqVal_one]; omega)
  have htwo : sigFourDress m v 2 = m 2 := sigFourDress_ne (by rw [sqVal_two]; omega)
  have hU : ∀ j' : Fin h, sigFourDress m v (sqHandleIdxU j') = m (sqHandleIdxU j') :=
    fun j' => sigFourDress_ne (by rw [sqHandleIdxU_val]; omega)
  have hV : ∀ j' : Fin h, sigFourDress m v (sqHandleIdxV j') = m (sqHandleIdxV j') :=
    fun j' => sigFourDress_ne (by rw [sqHandleIdxV_val]; omega)
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := sqWord_sigFour_low (R := R) (v := v) (x := m 1)
    (y := m 2) hvb hxb hyb
  rw [sqRelWord, sqRelWord, sigFourDress_zero, hone, htwo, funext hU, funext hV, hm0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [SqU5.mul_g, SqU5.mul_g, sqWord_sigFour_g hvb hxb hyb, hc]
    ring
  · rw [SqU5.mul_h, SqU5.mul_h, sqWord_sigFour_h hvb hxb hyb, ha, he]
    ring
  · rw [SqU5.mul_i, SqU5.mul_i, sqWord_sigFour_i hvb hxb hyb, hb, hf]
    ring
  · rw [SqU5.mul_j, SqU5.mul_j, sqWord_sigFour_j hvb hxb hyb, ha, he,
      sqWord_sigFour_h hvb hxb hyb, SqU5.handleWord_d]
    ring

end RelatorShift

/-! ## 5 The gauge collapse -/

section Gauge

variable {R : Type} [CommRing R] {v x y : SqU5 R}

/-- The third class-two row's shift is **even** on the class-two-forced gauge. -/
theorem sigFourG_gauge_even {xc xd : R} (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd) :
    ∃ k : R, sigFourG v x = 2 * k :=
  ⟨v.c * xd - v.d * xc, by rw [sigFourG, hxc, hxd]; ring⟩

/-- ⭐⭐ **The two class-three rows' shifts are even on the gauge**: this is the class-three
blindness recurring, in the form this file's carrier can state it.  `GradedSigma`'s
`sigRead_gauge_even` is the same fact about the committed class-three slice. -/
theorem sigFourH_gauge_even {xa xc xe xf : R} (hxa : x.a = 2 * xa) (hxc : x.c = 2 * xc)
    (hxe : x.e = 2 * xe) (hxf : x.f = 2 * xf) : ∃ k : R, sigFourH v x = 2 * k :=
  ⟨v.a * (xf - xc) - v.c * (xa + xe) + v.e * xc - v.f * xa, by
    rw [sigFourH, hxa, hxc, hxe, hxf]; ring⟩

theorem sigFourI_gauge_even {xc xd xf : R} (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd)
    (hxf : x.f = 2 * xf) : ∃ k : R, sigFourI v x = 2 * k :=
  ⟨v.d * (xc - xf) + v.f * xd, by rw [sigFourI, hxc, hxd, hxf]; ring⟩

/-- ⭐⭐ **The gauge collapse of the class-four sigma reading** (the headline).  On the
class-two-forced `x0`-gauge - the `x0`-slot's abelian columns `a, c, d` and its two lower
class-two coordinates `e, f` all even, the `x1`-slot's abelian columns even - the whole reading
is

```text
v.a * (x.g + x.i)  +  v.d * x.h  +  v.e * x.g   (mod 2).
```

Every coefficient is a **deep** coordinate of the `x0`-slot: its third class-two coordinate
`x.g` and its two class-three coordinates `x.h`, `x.i`.  None of the three is pinned by any
lower row, and none of the three exists at class three: this is exactly the factorisation that
`GradedSigma`'s docstring said had to break. -/
theorem sigFourRead_gauge {xa xc xd xe xf ya yc yd : R}
    (hxa : x.a = 2 * xa) (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd) (hxe : x.e = 2 * xe)
    (hxf : x.f = 2 * xf) (hya : y.a = 2 * ya) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd) :
    ∃ k : R, sigFourRead v x y
      = v.a * (x.g + x.i) + v.d * x.h + v.e * x.g + 2 * k := by
  refine ⟨v.a * (8 * (xc * xd) - 4 * (xc * yd) - 8 * (xd * xf) + 4 * (xf * yd)
        - 2 * (yc * yd) + yd * y.f - x.g)
      + v.c * (6 * (xa * xd) - 4 * (xa * yd) + 6 * (xd * xe) - 4 * (xe * yd)
        - 2 * (ya * yd) - 2 * (yd * y.e))
      + v.d * (2 * (xa * xf) + 2 * (xc * xe) - x.h - 2 * (ya * yc) + ya * y.f + yc * y.e)
      + v.e * (-8 * (xc * xd) + 4 * (xc * yd) + 2 * (yc * yd))
      + v.f * (6 * (xa * xd) - 4 * (xa * yd) - 4 * (ya * yd))
      + v.g * (-xa - xe)
      + (v.h * xd - v.i * xa)
      + (v.a * v.d * (xf - xc) - v.a * v.f * xd - v.c * v.e * xd + v.d * v.e * xc), ?_⟩
  simp only [sigFourRead]
  rw [hxa, hxc, hxd, hxe, hxf, hya, hyc, hyd]
  ring

/-- ⭐⭐ **The gauge collapse as a parity statement over `Z/8`**: the class-four selection bit
moves by exactly the three-channel `F_2`-form. -/
theorem sigFourRead_gauge_par {v x y : SqU5 gr3R} {xa xc xd xe xf ya yc yd : gr3R}
    (hxa : x.a = 2 * xa) (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd) (hxe : x.e = 2 * xe)
    (hxf : x.f = 2 * xf) (hya : y.a = 2 * ya) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd) :
    selPar (sigFourRead v x y)
      = selPar (v.a * (x.g + x.i)) + selPar (v.d * x.h) + selPar (v.e * x.g) := by
  obtain ⟨k, hk⟩ := sigFourRead_gauge (v := v) hxa hxc hxd hxe hxf hya hyc hyd
  rw [hk, selPar_add, selPar_add, selPar_add, selPar_two_mul, add_zero]

end Gauge

/-! ## 6 The witness: the sigma slot decided on the forced gauge -/

section Witness

/-- The cleared `U`-letter of the witness binder point: abelian columns `(1, 0, 0)`, every
class-two and deeper coordinate zero. -/
def sigFourU : SqU5 gr3R := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The cleared `V`-letter: abelian columns `(2, 0, 0)`, everything deeper zero. -/
def sigFourV : SqU5 gr3R := ⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **The `x0` slot at the class-two-forced gauge.**  At the uncleared row type
`(T, S) = (1, 0)` the class-two forcing pins the `x0`-dressing to `U^{-S} V^{T} = V` **up to
`gamma_3`**, and this is such a value: `sigFourV` times the `gamma_3`-element with `i = 1`.
All three abelian columns and both lower class-two coordinates are even on the nose; the
class-three coordinate `i = 1` is the piece the class-two forcing leaves free, and it is
exactly the coefficient the class-four reading uses. -/
def sigFourX : SqU5 gr3R := ⟨2, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩

/-- The `x0` slot is the class-two forced value corrected by a `gamma_3`-element - the
freedom the class-two forcing does not touch. -/
theorem sigFourX_eq : sigFourX = sigFourV * (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 6⟩ : SqU5 gr3R) := by
  decide

/-- …and that correction is `gamma_3`-shaped. -/
theorem sigFourX_corr_gaThree :
    (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 6⟩ : SqU5 gr3R).IsGaThree :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `x1` slot: abelian columns zero, the deep coordinates solving the seven lower rows. -/
def sigFourY : SqU5 gr3R := ⟨0, 0, 0, 0, 1, 0, 4, 0, 2, 0⟩

/-- **The class-four sigma-witness binder point at one handle**, with the sigma slot dressed
by `v` and every other slot fixed. -/
def sigFourWit (v : SqU5 gr3R) : Fin (sqRank 1) → SqU5 gr3R :=
  fun i =>
    if (i : ℕ) = 0 then sigFourMark gr3R * v else
    if (i : ℕ) = 1 then sigFourX else
    if (i : ℕ) = 2 then sigFourY else
    if (i : ℕ) = 3 then sigFourU else sigFourV

@[simp] theorem sigFourWit_zero (v : SqU5 gr3R) :
    sigFourWit v 0 = sigFourMark gr3R * v := by
  simp only [sigFourWit, sqVal_zero]
  norm_num

@[simp] theorem sigFourWit_one (v : SqU5 gr3R) : sigFourWit v 1 = sigFourX := by
  simp only [sigFourWit, sqVal_one]
  norm_num

@[simp] theorem sigFourWit_two (v : SqU5 gr3R) : sigFourWit v 2 = sigFourY := by
  simp only [sigFourWit, sqVal_two]
  norm_num

/-- The dressed witness really is the sigma-dressing of the undressed one, so the general
reading of paragraph 4 applies to it. -/
theorem sigFourWit_eq_dress (v : SqU5 gr3R) :
    sigFourWit v = sigFourDress (sigFourWit 1) v := by
  funext i
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = 0 := Fin.val_injective (by rw [h0, sqVal_zero])
    subst hi
    rw [sigFourDress_zero, sigFourWit_zero, sigFourWit_zero, mul_one]
  · rw [sigFourDress_ne h0]
    simp only [sigFourWit, if_neg h0]

/-! ### The three verdicts

All seven class-`<= 2` rows and both class-three rows vanish at each of the three sigma
dressings below, so each is an honest stage-three survivor; only the class-four residue
differs, and it differs **by an odd amount** between the `V`-dressing and the `U`-dressing.
This is the separation the class-three slice provably cannot produce on this gauge
(`sigFourH_gauge_even`, and `GradedSigma.sigRead_gauge_even` for the committed slice). -/

/-- The undressed witness **kills the relator outright**: all ten rows vanish. -/
theorem sqRelWord_sigFourWit_triv : sqRelWord (sigFourWit 1) = 1 := by decide

/-- Dressing the sigma slot by the cleared `V`-letter - the class-two forced value at this row
type - leaves the **even** residue `2`, killed by one explicit `gamma_4`-move below. -/
theorem sqRelWord_sigFourWit_V : sqRelWord (sigFourWit sigFourV) = liftC 2 := by decide

/-- ⭐⭐ Dressing the sigma slot by the cleared `U`-letter leaves the **odd** residue `1`:
**the class-four slice separates two sigma dressings over the same class-two-forced
`x0`-gauge**, which the class-three slice provably cannot do. -/
theorem sqRelWord_sigFourWit_U : sqRelWord (sigFourWit sigFourU) = liftC 1 := by decide

/-- The forced-sigma frame's even residue dies by one `gamma_4`-move on the `x1` slot. -/
theorem sqRelWord_sigFourWit_V_complete :
    sqRelWord (sigLift 0 (sigFourWit sigFourV) 1 1 (liftC 7) 1 1) = 1 := by decide

/-! ### Soundness: every achievable increment is even

The witness point has `A = 1, B = 2, C = D = E = F = 0` in the naming of
`GradedLift.selLamThree`, so every generator of the achievable `gamma_3`-lattice has **both**
`(h, i)`-coordinates even.  Hence every five-slot refinement of paragraph 2 translates the
class-four residue by an even amount, whatever the slot: the parity of the residue is an
invariant of the whole refinement orbit at this point, and the separation above is a genuine
verdict rather than a gauge artefact. -/

/-- ⭐ **The achievable lattice is even at the witness point**, both coordinates. -/
theorem sigFourWit_lamThree_even {P Q R : gr3R} {z : SqU5 gr3R}
    (hz : selLamThree 1 2 0 0 0 0 1 0 P Q R z) :
    (∃ a : gr3R, z.h = 2 * a) ∧ (∃ b : gr3R, z.i = 2 * b) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, hh, hi⟩ := hz
  exact ⟨⟨r₆ * Q + 2 * (r₇ * Q), by rw [hh]; ring⟩,
    ⟨r₅ * R + r₆ * R, by rw [hi]; ring⟩⟩

/-- The five-slot increment at the witness point is even for every achievable dressing. -/
theorem sigFourWit_increment_even {P Q R : gr3R} {z₀ z₃ z₄ w₁ w₂ : SqU5 gr3R}
    (l₀ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₀)
    (l₃ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₃)
    (l₄ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₄) (v : SqU5 gr3R) :
    ∃ k : gr3R, (z₀.h * (sigFourWit v 1).d - z₀.i * (sigFourWit v 1).a)
        + (-4 * w₁.j + 2 * w₂.j)
        + ((z₃.h * (sigFourWit v (sqHandleIdxV 0)).d
            - z₃.i * (sigFourWit v (sqHandleIdxV 0)).a)
          + ((sigFourWit v (sqHandleIdxU 0)).a * z₄.i
            - (sigFourWit v (sqHandleIdxU 0)).d * z₄.h)) = 2 * k := by
  obtain ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩ := sigFourWit_lamThree_even l₀
  obtain ⟨⟨a₃, ha₃⟩, ⟨b₃, hb₃⟩⟩ := sigFourWit_lamThree_even l₃
  obtain ⟨⟨a₄, ha₄⟩, ⟨b₄, hb₄⟩⟩ := sigFourWit_lamThree_even l₄
  have hU : sigFourWit v (sqHandleIdxU 0) = sigFourU := by
    simp only [sigFourWit, sqHandleIdxU_val]
    norm_num
  have hV : sigFourWit v (sqHandleIdxV 0) = sigFourV := by
    simp only [sigFourWit, sqHandleIdxV_val]
    norm_num
  refine ⟨a₀ * (sigFourX).d - b₀ * (sigFourX).a + (-2 * w₁.j + w₂.j)
      + (a₃ * (sigFourV).d - b₃ * (sigFourV).a) + (b₄ - a₄ * (sigFourU).d), ?_⟩
  rw [sigFourWit_one, hU, hV, ha₀, hb₀, ha₃, hb₃, ha₄, hb₄]
  simp only [sigFourU, sigFourV, sigFourX]
  ring

/-! ### The bit, and the forcing -/

/-- ⭐⭐ **The class-four selection bit at the witness point is the sigma dressing's
`chi_a`-character, mod 2.**  Every `nu'`-trivial sigma dressing is read, and the whole reading
collapses to one coordinate: the parity of the residue is `selPar v.a`.  This is the
`sqArbFrame_x0_dressing_forced` conclusion one slot over - that theorem pins the `a`-column of
the `x0`-dressing, this one pins the `a`-column of the **sigma**-dressing. -/
theorem sigFourWit_bit {v : SqU5 gr3R} (hvb : v.b = 0) :
    selPar ((sqRelWord (sigFourWit v)).j) = selPar v.a := by
  have hm0 : sigFourWit (1 : SqU5 gr3R) 0 = sigFourMark gr3R := by
    rw [sigFourWit_zero, mul_one]
  have hxb : (sigFourWit (1 : SqU5 gr3R) 1).b = 0 := by rw [sigFourWit_one]; decide
  have hyb : (sigFourWit (1 : SqU5 gr3R) 2).b = 0 := by rw [sigFourWit_two]; decide
  obtain ⟨-, -, -, hj⟩ := sqRelWord_sigFourDress (m := sigFourWit 1) (v := v) hm0 hxb hyb hvb
  rw [sigFourWit_eq_dress v, hj, sqRelWord_sigFourWit_triv, sigFourWit_one, sigFourWit_two,
    SqU5.one_j, zero_add,
    sigFourRead_gauge_par (v := v) (x := sigFourX) (y := sigFourY) (xa := 1) (xc := 0)
      (xd := 0) (xe := 0) (xf := 0) (ya := 0) (yc := 0) (yd := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    show (sigFourX.g + sigFourX.i : gr3R) = 1 by decide,
    show (sigFourX.h : gr3R) = 0 by decide, show (sigFourX.g : gr3R) = 0 by decide,
    mul_one, mul_zero, mul_zero, selPar_zero, add_zero, add_zero]

/-- ⭐⭐ **The sigma-slot forcing at class four.**  At the witness binder point, a sigma
dressing whose frame is killed by **any** achievable five-slot refinement has an **even**
`chi_a`-character.  The class-two forced value `sigFourV` has `chi_a = 2`, even, and passes;
the letter `sigFourU` has `chi_a = 1`, odd, and is excluded outright.  This is the sigma-half
of the forced dressing, made visible by a slice - the escape `GradedSigma`'s docstring
priced. -/
theorem sigFourWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hvb : v.b = 0) (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₀ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₀)
    (l₃ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₃)
    (l₄ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₄)
    (hkill : sqRelWord (sigLift 0 (sigFourWit v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar v.a = 0 := by
  rw [sqRelWord_sigLift hz₀ hw₁ hw₂ hz₃ hz₄] at hkill
  obtain ⟨k, hk⟩ := sigFourWit_increment_even (w₁ := w₁) (w₂ := w₂) l₀ l₃ l₄ v
  rw [hk, mul_liftC_apply] at hkill
  have hj := congrArg SqU5.j hkill
  simp only [SqU5.one_j] at hj
  have hp := congrArg selPar hj
  rw [selPar_add, selPar_two_mul, add_zero, sigFourWit_bit hvb, selPar_zero] at hp
  exact hp

/-- ⭐⭐ **The odd sigma dressing is dead, robustly**: no achievable five-slot refinement
whatsoever kills the `sigFourU`-dressed frame. -/
theorem sqRelWord_sigFourWit_U_ne_one {z₀ w₁ w₂ z₃ z₄ : SqU5 gr3R} {P Q R : gr3R}
    (hz₀ : z₀.IsGaThree) (hw₁ : w₁.IsGaFour) (hw₂ : w₂.IsGaFour)
    (hz₃ : z₃.IsGaThree) (hz₄ : z₄.IsGaThree)
    (l₀ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₀)
    (l₃ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₃)
    (l₄ : selLamThree 1 2 0 0 0 0 1 0 P Q R z₄) :
    sqRelWord (sigLift 0 (sigFourWit sigFourU) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  intro hc
  have hpar := sigFourWit_sigma_forced (v := sigFourU) (by decide) hz₀ hw₁ hw₂ hz₃ hz₄
    l₀ l₃ l₄ hc
  rw [show (sigFourU.a : gr3R) = 1 from rfl] at hpar
  exact absurd hpar (by decide)

end Witness

/-! ## 7 The residual obstruction, named and measured -/

section Residual

variable {R : Type} [CommRing R] {v x y : SqU5 R}

/-- ⭐⭐ **What class four still cannot see.**  The gauge collapse leaves exactly three live
channels, `v.a`, `v.d` and `v.e`.  A sigma dressing whose three are even is read **evenly**:
the class-four slice identifies it with the trivial dressing, whatever its remaining seven
coordinates do. -/
theorem sigFourRead_gauge_blind {xa xc xd xe xf ya yc yd va vd ve : R}
    (hxa : x.a = 2 * xa) (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd) (hxe : x.e = 2 * xe)
    (hxf : x.f = 2 * xf) (hya : y.a = 2 * ya) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd)
    (hva : v.a = 2 * va) (hvd : v.d = 2 * vd) (hve : v.e = 2 * ve) :
    ∃ k : R, sigFourRead v x y = 2 * k := by
  obtain ⟨k, hk⟩ := sigFourRead_gauge (v := v) hxa hxc hxd hxe hxf hya hyc hyd
  exact ⟨va * (x.g + x.i) + vd * x.h + ve * x.g + k, by rw [hk, hva, hvd, hve]; ring⟩

/-- ⭐⭐ **The measured residual**: on the class-two-forced gauge the depth sweep's forced
sigma dressing `a0 = a1` is read **evenly**, exactly like the trivial dressing `a0 = 1` - its
three live channels are the `x0`-slot's own `a`-, `d`- and `e`-coordinates, and the gauge makes
all three even.  So class four decides the sigma slot's three `F_2`-characters and **not** the
sweep's `a0 = a1` forcing: that piece needs class five, or the universal quotient. -/
theorem sigFourRead_gauge_sigma_eq_x0 {xa xc xd xe xf ya yc yd : R}
    (hxa : x.a = 2 * xa) (hxc : x.c = 2 * xc) (hxd : x.d = 2 * xd) (hxe : x.e = 2 * xe)
    (hxf : x.f = 2 * xf) (hya : y.a = 2 * ya) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd) :
    ∃ k : R, sigFourRead x x y = 2 * k :=
  sigFourRead_gauge_blind hxa hxc hxd hxe hxf hya hyc hyd hxa hxd hxe

/-- The same statement at the witness point, as a parity: the sigma dressings `1`, `sigFourV`
and `sigFourX` are all read evenly there, and no refinement separates them. -/
theorem sigFourWit_blind_pair :
    selPar ((sqRelWord (sigFourWit 1)).j) = selPar ((sqRelWord (sigFourWit sigFourV)).j) ∧
    selPar ((sqRelWord (sigFourWit 1)).j) = selPar ((sqRelWord (sigFourWit sigFourX)).j) := by
  refine ⟨?_, ?_⟩ <;>
    rw [sigFourWit_bit (by decide), sigFourWit_bit (by decide)] <;> decide

end Residual

/-! ## 8 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every `decide` is
on `ZMod 8` or on `Fin`-indexed tuples over it. -/

section AxiomPins

#print axioms conjP_of_gaThree
#print axioms sqWord_mul_gaThree_sigma
#print axioms sigLift
#print axioms sigLift_zero
#print axioms sigLift_one
#print axioms sigLift_two
#print axioms sigLift_handleU
#print axioms sigLift_handleV
#print axioms sqRelWord_sigLift
#print axioms sigFourMark
#print axioms sigFourMark_b
#print axioms sigFourG
#print axioms sigFourH
#print axioms sigFourI
#print axioms sigFourRead
#print axioms sqWord_sigFour_low
#print axioms sqWord_sigFour_g
#print axioms sqWord_sigFour_h
#print axioms sqWord_sigFour_i
#print axioms sqWord_sigFour_j
#print axioms sigFourRead_of_gaThree
#print axioms SqU5.handleWord_d
#print axioms sigFourDress
#print axioms sigFourDress_zero
#print axioms sigFourDress_ne
#print axioms sqRelWord_sigFourDress
#print axioms sigFourG_gauge_even
#print axioms sigFourH_gauge_even
#print axioms sigFourI_gauge_even
#print axioms sigFourRead_gauge
#print axioms sigFourRead_gauge_par
#print axioms sigFourU
#print axioms sigFourV
#print axioms sigFourX
#print axioms sigFourX_eq
#print axioms sigFourX_corr_gaThree
#print axioms sigFourY
#print axioms sigFourWit
#print axioms sigFourWit_zero
#print axioms sigFourWit_one
#print axioms sigFourWit_two
#print axioms sigFourWit_eq_dress
#print axioms sqRelWord_sigFourWit_triv
#print axioms sqRelWord_sigFourWit_V
#print axioms sqRelWord_sigFourWit_U
#print axioms sqRelWord_sigFourWit_V_complete
#print axioms sigFourWit_lamThree_even
#print axioms sigFourWit_increment_even
#print axioms sigFourWit_bit
#print axioms sigFourWit_sigma_forced
#print axioms sqRelWord_sigFourWit_U_ne_one
#print axioms sigFourRead_gauge_blind
#print axioms sigFourRead_gauge_sigma_eq_x0
#print axioms sigFourWit_blind_pair

end AxiomPins

end SqCore

end Dyadic

end GQ2
