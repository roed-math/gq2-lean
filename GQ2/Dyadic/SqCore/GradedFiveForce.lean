/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import Mathlib.GroupTheory.Commutator.Basic
import GQ2.Dyadic.SqCore.GradedFive
import GQ2.Dyadic.SqCore.GradedSigmaFive

/-!
# W59-FORCE5: the sigma dressing `a0 = a1` excluded at class five

`GradedSigmaFour` section 7 named its own residual.  On the class-two-forced gauge the depth
sweep's forced sigma dressing `a0 = a1` - the dressing `v` equal to the `x0`-slot value - is
read **evenly** at class four (`sigFourRead_gauge_sigma_eq_x0`), so the class-four slice
identifies it with the trivial dressing:

> The sweep's `a0 = a1` forcing is therefore still not a class-four slice statement: it needs
> class five (where the reading acquires channels the class-two gauge does not control) or the
> universal quotient.

`GradedSigmaFive` sharpened the negative half: the class-four reading of the diagonal is even at
**every** relator-killing marking, gauge or no gauge, so there is no class-four channel to open
at all.  Wave 58's reconnaissance (`docs/dyadic/w58-sigma5-note.md` section 3.2) measured the
positive half on the class-five carrier and stated this file's theorem exactly.  Here it is
proved, on `GradedFive`'s committed carrier `SqU6`.

## ⭐⭐ Headline: the residual is DISCHARGED

`sqRelWord_fiveWit_diag_ne_one`.  At the binder point `fiveWit` - letters
`U = <a=1, c=2, d=3, f=3, g=2, h=2, i=2>`, `V = <d=1, e=2, f=3, g=2, h=3, i=3>`,
`x0 = <a=2, e=1>`, `x1 = <e=2, f=1, h=3, i=1, j=2, k=2, l=2, m=3, n=2, o=2>`, at **every**
handle count `h` and **every** handle `j` - the undressed frame kills the relator outright
(`sqRelWord_fiveWit_triv`), the `a0 = a1`-dressed frame leaves the **odd** class-five residue
`7` (`sqRelWord_fiveWit_diag`), and **no achievable five-slot class-five refinement whatsoever
kills it**.  So the sigma dressing `a0 = a1` is excluded at class five, which is the residual
`GradedSigmaFour` section 7 named.  ⚠ The exclusion is against **stage-five** refinements, and
the second headline below is that it is false one filtration step wider; do not quote the first
headline without the second.

Three things make the verdict a verdict rather than a gauge artefact.

* **It is genuinely class five.**  Both `U_5`-quotients of the marking kill the class-four
  relator at **both** dressings (`fiveWit_class_four_blind`), so the whole committed class-`<= 4`
  machinery cannot separate them; the class-four rows of the dressed relator vanish outright
  (`fiveWit_diag_class_four_rows`); and the class-four reading of the very same dressing is
  even by the committed `GradedSigmaFive.sigFourRead_diag_even`
  (`fiveWit_class_four_reading_even`).  The point sits on the committed class-two-forced gauge
  (`forceX_gauge`); the one datum escaping it is the `x0`-slot's fifth abelian column
  `x_{56} = 1`, a matrix entry `U_5` does not have.
* **⭐⭐ Soundness is a theorem, and a stronger one than class four's.**
  `forceLcs_three_le_forceN4`: at any marking all of whose slots have an even `(3,4)`-column,
  every achievable `gamma_4`-dressing is `gamma_4`-shaped with **even** class-four coordinates
  `x_{15}` and `x_{26}`.  Where `GradedSigmaFour.sigFourWit_lamThree_even` proves evenness for a
  *declared* lattice `selLamThree`, this proves it for the honest lower central series of the
  image subgroup, by a four-step chain of subgroups `N_1 >= ... >= N_4` (section 5): an even
  `(3,4)`-column forces the two middle class-two coordinates even, those force all three
  class-three coordinates even, and those force both class-four coordinates even.  The single
  input is that `forceU` is the only letter with a non-zero `c`-column and it is `2`.
* **Achievability is load-bearing, with a witness.**  The *unrestricted* `gamma_4`-move
  `<m = 1>` on the sigma slot kills the dressed frame outright (`fiveWit_unrestricted_kill`),
  and it is not achievable (`fiveWit_unrestricted_not_achievable`).  This is the class-five form
  of `GradedFourCleared`'s "8 of the 64 unrestricted `gamma_3`-moves kill the odd dressing".

## ⚠⚠ …and exactly how far the discharge reaches

**The exclusion is the stage-five one, and one filtration step wider it is FALSE.**  This is a
new finding, not in wave 58's note, and it is the more consequential half of this file.

`fiveWit_gaThree_kill`: the triple commutator `[[sigma, U], x1] = <m=5, n=6>` of the point's own
letters is `gamma_4`-**shaped** with an **odd** class-four coordinate.  Dressing the sigma slot
by it kills the `a0 = a1`-dressed frame outright, at every handle count and every handle.  It is
achievable at the `gamma_3` level (`fiveWit_gaThree_kill_mem`, a membership proof, not a census)
and not at the `gamma_4` level (`fiveWit_gaThree_kill_not_gaFour`).  The structural reason,
measured: at this point `gamma_3` of the image contains the **whole** of `gamma_4` of the
carrier - `|gamma_3(im)| = 16384 = 32 * 512` with `|gamma_4(carrier)| = 512` - so it contains
precisely the odd-`m` dressings that `gamma_4` of the image excludes.  `1280` of the `81920`
achievable single-slot `gamma_3`-moves kill the frame.

**The committed class-four point does not have this hole**: `0` of its `128` achievable
`gamma_2`-dressings kill the odd frame that `GradedSigmaFour.sqRelWord_sigFourWit_U_ne_one`
excludes (`scripts/w59_force5/results/scope_probe.txt` section B).  So this is a way in which
the class-five statement is **weaker than its class-four model**, not a general feature of the
stage convention, and whoever consumes the discharge must know it: the residual is discharged
against stage-five refinements, and a stage-four move rescues the dressing.

## The engine

* **1** the class-five central calculus: `liftC6`, the `gamma_4`- and `gamma_5`-shapes, and
  ⭐ `sqWord_mul_liftC6` (proved structurally: the class-five word cannot be normalised);
* **2** ⭐ `conjP_of_gaFour` (conjugation by a `gamma_4`-element is a central translation, the
  class-four coordinates paired against the *outermost* abelian columns `(a, e)`) and ⭐⭐
  `sqWord_mul_gaFour_sigma`, the sigma-slot move, `GradedSigmaFour`'s one class up with the
  column shifted one further out;
* **3** the five-slot refinement `fiveLift` and ⭐⭐ `sqRelWord_fiveLift`, the translation
  identity: the refinement translates the relator centrally by
  ```text
  (z0.m * x0.e - z0.n * x0.a) + (-4 * w1.o + 2 * w2.o)
    + (z3.m * V.e - z3.n * V.a) + (U.a * z4.n - U.e * z4.m)
  ```
  with every class-`<= 4` row untouched and no closed form of the relator consumed;
* **4** the binder point and its two verdicts;
* **5** the soundness chain;
* **6** ⭐⭐ the bit, the forcing `fiveWit_sigma_forced` and the exclusion;
* **7** cross-checks; **8** axiom pins.

## PROVED versus MEASURED

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`): everything above,
including the soundness, at **every** handle count and every handle.  Note in particular that
the general class-five reading `sigFiveRead` (135 terms) is **not** needed and **not** built:
the forcing runs on the translation identity plus two `decide`s.

**MEASURED** (`scripts/w59_force5/`, certified output in `results/verify_force5.txt`; 29 named
checks, 0 failures, on an independent `U_6` library built from honest 6 x 6 matrices and
cross-checked against wave 58's coordinate library on 9000 comparisons):

* that the proved bound is **sharp**: the achievable `gamma_4`-lattice at the point is
  **exactly** `{(2a, 2b)}`, computed twice - structurally, as the pairings of each level against
  the letters' abelian columns, and by honest closure of the image's lower central series
  (`|gamma_3| = 16384`, `|gamma_4| = 128`, `|gamma_5| = 4`, matching wave 58's census).  So
  `forceN4` excludes no achievable move by fiat, and the forcing is not vacuous;
* the translation identity of section 3, against honest collection at 3600 refinements of the
  point and 400 random markings;
* the exclusion sweep: 392 single-slot and 4000 random five-slot achievable refinements, the
  residue odd at every one, while 64 of 192 unrestricted `gamma_4`-moves flip it;
* the scope probes of the warning above, including the class-four comparison.

**Wave 58's measurements needed no correction; its conclusion needed a hypothesis.**  Every
measured claim of `w58-sigma5-note.md` section 3.2 that this file touches - the point's
coordinates, both relator values, the class-four blindness, the gauge audit, the soundness
census (`|gamma_4(im)| = 128`, all even), the closed form
`x_{12} y_{24} y_{46} + x_{56} y_{13} y_{35}` (`fiveWit_w58_form_crosscheck`), the evenness of
the block's `(4,6)` coordinate (`forceUV_block_reading`) - was re-derived independently here and
held.  What the note did not state is the scope of its step 4: "the sigma dressing `a0 = a1` is
excluded at class five" is true of stage-five refinements and false of stage-four ones, and the
note's own census only ever swept the former.

## Scope

The refinement class is `gamma_4`-dressings on the sigma and the two handle slots and
`gamma_5`-dressings on the two exponent slots, which is exactly
`GradedSigmaFour.sigFourWit_sigma_forced`'s class one level down.  One wider class is harmless
and **measured**: achievable `gamma_4`-dressings on all five slots kill nothing (640 single-slot
moves).  The next one wider is **not** harmless, and the warning above is that finding.
Proving or refuting the forcing against `gamma_3`-dressings in general needs the `gamma_3`-level
translation identity, which this file does not build; what it does build is one explicit
`gamma_3`-level counterexample.

Like `GradedFour`, `GradedLift` and `GradedSigmaFour`, this file works at the level of **marking
tuples** in `SqU6 gr3R`: the hom layer of `GradedFive` is not consumed, so no statement here
claims that a given tuple is the image of a continuous homomorphism on `D_sq h`.  Turning
`fiveWit_sigma_forced` into a statement about `sqArbFrame` is the class-five transposition of
`GradedFourCleared`, and it is not attempted here.

## Axiom hygiene

All **77** committed prints are **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a
subset; no census axiom is reachable.  Every `decide` is on `ZMod 8` or on `Fin`-indexed tuples
over it.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The class-five central calculus -/

section Filtration

variable {R : Type} [CommRing R]

/-- A `gamma_4`-shaped element of the class-five carrier: the twelve coordinates of class
`<= 3` vanish, so only `m`, `n` and `o` survive.  `GradedLift.SqU5.IsGaThree` is the shape
that dresses the sigma slot one class down. -/
def SqU6.IsGaFour (z : SqU6 R) : Prop :=
  z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0 ∧ z.h = 0 ∧ z.i = 0
    ∧ z.j = 0 ∧ z.k = 0 ∧ z.l = 0

/-- A `gamma_5`-shaped element: only the class-five coordinate may be non-zero.  These are
the central translations. -/
def SqU6.IsGaFive (z : SqU6 R) : Prop := z.IsGaFour ∧ z.m = 0 ∧ z.n = 0

theorem SqU6.IsGaFive.isGaFour {z : SqU6 R} (hz : z.IsGaFive) : z.IsGaFour := hz.1

@[simp] theorem SqU6.isGaFour_one : (1 : SqU6 R).IsGaFour :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem SqU6.isGaFive_one : (1 : SqU6 R).IsGaFive :=
  ⟨SqU6.isGaFour_one, rfl, rfl⟩

/-- **The central `(1,6)`-translation by `w`**: `GradedLift.liftC` one class up. -/
def liftC6 (w : R) : SqU6 R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, w⟩

@[simp] theorem liftC6_zero : liftC6 (0 : R) = 1 := rfl

@[simp] theorem liftC6_o (w : R) : (liftC6 w).o = w := rfl

theorem liftC6_isGaFive (w : R) : (liftC6 w).IsGaFive :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

@[simp] theorem liftC6_mul_liftC6 (v w : R) : liftC6 v * liftC6 w = liftC6 (v + w) := by
  ext <;> simp [liftC6]

@[simp] theorem liftC6_inv (w : R) : (liftC6 w)⁻¹ = liftC6 (-w) := by
  ext <;> simp [liftC6]

/-- `liftC6` is central. -/
theorem liftC6_comm (p : SqU6 R) (w : R) : p * liftC6 w = liftC6 w * p := by
  ext <;> simp [liftC6, add_comm]

/-- Multiplying on the right by `liftC6` translates the class-five coordinate and nothing
else. -/
theorem mul_liftC6_apply (p : SqU6 R) (w : R) :
    p * liftC6 w
      = ⟨p.a, p.b, p.c, p.d, p.e, p.f, p.g, p.h, p.i, p.j, p.k, p.l, p.m, p.n, p.o + w⟩ :=
  SqU6.mul_center_o p w

/-- A `gamma_5`-shaped element **is** a central translation. -/
theorem SqU6.IsGaFive.eq_liftC6 {z : SqU6 R} (hz : z.IsGaFive) : z = liftC6 z.o := by
  obtain ⟨⟨ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk, hl⟩, hm, hn⟩ := hz
  ext <;> simp [liftC6, ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk, hl, hm, hn]

/-- Conjugation fixes the centre. -/
theorem conjP_liftC6 (w : R) (g : SqU6 R) : conjP (liftC6 w) g = liftC6 w := by
  ext <;> simp [liftC6, SqU6.conjP_m, SqU6.conjP_n, SqU6.conjP_o]

/-- Sliding a central factor to the right past one letter. -/
theorem mul_liftC6_mul (p q : SqU6 R) (w : R) : p * liftC6 w * q = p * q * liftC6 w := by
  rw [mul_assoc, ← liftC6_comm, ← mul_assoc]

/-- Commutators ignore a central right factor in the left argument. -/
theorem commP_mul_liftC6_left (p q : SqU6 R) (w : R) : commP (p * liftC6 w) q = commP p q := by
  ext <;>
    simp only [SqU6.commP_a, SqU6.commP_b, SqU6.commP_c, SqU6.commP_d, SqU6.commP_e,
      SqU6.commP_f, SqU6.commP_g, SqU6.commP_h, SqU6.commP_i, SqU6.commP_j, SqU6.commP_k,
      SqU6.commP_l, SqU6.commP_m, SqU6.commP_n, SqU6.commP_o, SqU6.u6Comm3L, SqU6.u6Comm3M,
      SqU6.u6Comm3R, SqU6.u6Comm4L, SqU6.u6Comm4R, SqU6.u6Comm5, liftC6, SqU6.mul_a,
      SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g, SqU6.mul_h,
      SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n] <;>
    ring

/-- …and in the right argument. -/
theorem commP_mul_liftC6_right (p q : SqU6 R) (w : R) : commP p (q * liftC6 w) = commP p q := by
  ext <;>
    simp only [SqU6.commP_a, SqU6.commP_b, SqU6.commP_c, SqU6.commP_d, SqU6.commP_e,
      SqU6.commP_f, SqU6.commP_g, SqU6.commP_h, SqU6.commP_i, SqU6.commP_j, SqU6.commP_k,
      SqU6.commP_l, SqU6.commP_m, SqU6.commP_n, SqU6.commP_o, SqU6.u6Comm3L, SqU6.u6Comm3M,
      SqU6.u6Comm3R, SqU6.u6Comm4L, SqU6.u6Comm4R, SqU6.u6Comm5, liftC6, SqU6.mul_a,
      SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g, SqU6.mul_h,
      SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n] <;>
    ring

/-- Squares absorb a central factor with weight `2`. -/
private theorem sq_mul_liftC6 (p : SqU6 R) (w : R) :
    (p * liftC6 w) ^ 2 = p ^ 2 * liftC6 (2 * w) := by
  rw [pow_two, pow_two, mul_liftC6_mul p (p * liftC6 w) w, ← mul_assoc p p (liftC6 w),
    mul_assoc (p * p) (liftC6 w) (liftC6 w), liftC6_mul_liftC6]
  exact congrArg (fun t : R => p * p * liftC6 t) (by ring)

/-- Cubes absorb a central factor with weight `3`. -/
private theorem cube_mul_liftC6 (p : SqU6 R) (w : R) :
    (p * liftC6 w) ^ 3 = p ^ 3 * liftC6 (3 * w) := by
  have hp : p ^ 3 = p ^ 2 * p := pow_succ p 2
  rw [pow_succ, sq_mul_liftC6, mul_liftC6_mul (p ^ 2) (p * liftC6 w) (2 * w),
    ← mul_assoc (p ^ 2) p (liftC6 w), mul_assoc (p ^ 2 * p) (liftC6 w) (liftC6 (2 * w)),
    liftC6_mul_liftC6, hp]
  exact congrArg (fun t : R => p ^ 2 * p * liftC6 t) (by ring)

/-- Collecting the three central factors the exponent-slot dressing produces. -/
private theorem liftC6_collect (A B C D : SqU6 R) (a b c : R) :
    A * liftC6 a * (B * liftC6 b) * (C * liftC6 c) * D = A * B * C * D * liftC6 (a + b + c) := by
  rw [mul_liftC6_mul A (B * liftC6 b) a, ← mul_assoc A B (liftC6 b),
    mul_assoc (A * B) (liftC6 b) (liftC6 a), liftC6_mul_liftC6,
    mul_liftC6_mul (A * B) (C * liftC6 c) (b + a), ← mul_assoc (A * B) C (liftC6 c),
    mul_assoc (A * B * C) (liftC6 c) (liftC6 (b + a)), liftC6_mul_liftC6,
    mul_liftC6_mul (A * B * C) D (c + (b + a))]
  exact congrArg (fun t : R => A * B * C * D * liftC6 t) (by ring)

/-- Collecting the three central factors of the five-slot refinement. -/
private theorem liftC6_collect3 (A B : SqU6 R) (a b c : R) :
    A * liftC6 a * liftC6 c * (B * liftC6 b) = A * B * liftC6 (a + b + c) := by
  rw [mul_assoc A (liftC6 a) (liftC6 c), liftC6_mul_liftC6,
    mul_liftC6_mul A (B * liftC6 b) (a + c), ← mul_assoc A B (liftC6 b),
    mul_assoc (A * B) (liftC6 b) (liftC6 (a + c)), liftC6_mul_liftC6]
  exact congrArg (fun t : R => A * B * liftC6 t) (by ring)

/-- Conjugation distributes over a product. -/
theorem conjP_mul_left (p q g : SqU6 R) : conjP (p * q) g = conjP p g * conjP q g := by
  simp only [conjP]
  group

/-- Conjugating by a product is conjugating twice. -/
theorem conjP_mul_right_six (p g k : SqU6 R) : conjP p (g * k) = conjP (conjP p g) k := by
  simp only [conjP, mul_inv_rev, mul_assoc]

/-- ⭐ **The core word swallows exponent-slot central dressings with the relator weights**:
dressing the `x0`-slot by `liftC6 α` and the `x1`-slot by `liftC6 β` multiplies the core word
by `liftC6 (-4α + 2β)`.  `GradedLift.sqWord_mul_liftC` one class up, but proved structurally
rather than by expansion: the class-five word is far too large to normalise. -/
theorem sqWord_mul_liftC6 (s x y : SqU6 R) (α β : R) :
    sqWord s (x * liftC6 α) (y * liftC6 β) = sqWord s x y * liftC6 (-4 * α + 2 * β) := by
  have hx : conjP (x * liftC6 α) s = conjP x s * liftC6 α := by
    rw [conjP_mul_left, conjP_liftC6]
  have h1 : (conjP (x * liftC6 α) s)⁻¹ = (conjP x s)⁻¹ * liftC6 (-α) := by
    rw [hx, mul_inv_rev, liftC6_inv, ← liftC6_comm]
  have h3 : ((x * liftC6 α) ^ 3)⁻¹ = (x ^ 3)⁻¹ * liftC6 (-(3 * α)) := by
    rw [cube_mul_liftC6, mul_inv_rev, liftC6_inv, ← liftC6_comm]
  have h4 : commP (y * liftC6 β) (conjP (y * liftC6 β) s) = commP y (conjP y s) := by
    rw [conjP_mul_left, conjP_liftC6, commP_mul_liftC6_left, commP_mul_liftC6_right]
  rw [sqWord, sqWord, h1, h3, sq_mul_liftC6, h4, liftC6_collect]
  exact congrArg (fun t : R => (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s)
    * liftC6 t) (by ring)

end Filtration

/-! ## 2 The sigma-slot `gamma_4`-move and the five-slot class-five refinement -/

section SigmaMove

variable {R : Type} [CommRing R]

/-- ⭐ **Conjugation by a `gamma_4`-element is a central translation**, by the pairing of the
conjugator's class-four coordinates against the *outermost* abelian columns `(a, e)` of the
conjugand.  At class four the same statement pairs the class-three coordinates against
`(a, d)` (`GradedSigmaFour.conjP_of_gaThree`); the one-column shift is what gives the
class-five reading a channel the class-two gauge does not control. -/
theorem conjP_of_gaFour {z : SqU6 R} (hz : z.IsGaFour) (p : SqU6 R) :
    conjP p z = p * liftC6 (z.n * p.a - z.m * p.e) := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk, hl⟩ := hz
  rw [mul_liftC6_apply]
  ext <;>
    simp only [SqU6.conjP_a, SqU6.conjP_b, SqU6.conjP_c, SqU6.conjP_d, SqU6.conjP_e,
      SqU6.conjP_f, SqU6.conjP_g, SqU6.conjP_h, SqU6.conjP_i, SqU6.conjP_j, SqU6.conjP_k,
      SqU6.conjP_l, SqU6.conjP_m, SqU6.conjP_n, SqU6.conjP_o,
      ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk, hl] <;>
    ring

/-- ⭐⭐ **The sigma-slot `gamma_4`-move on the core word**: dressing the sigma letter by a
`gamma_4`-element translates the core word centrally, by the dressing's class-four coordinates
paired against the `x0`-slot's **outermost** abelian columns `(a, e)`.  The `x1`-slot never
enters: the second occurrence of sigma sits inside a commutator, which swallows the central
factor.  `GradedSigmaFour.sqWord_mul_gaThree_sigma` one class up. -/
theorem sqWord_mul_gaFour_sigma {z : SqU6 R} (hz : z.IsGaFour) (s x y : SqU6 R) :
    sqWord (s * z) x y = sqWord s x y * liftC6 (z.m * x.e - z.n * x.a) := by
  have hx : conjP x (s * z) = conjP x s * liftC6 (z.n * x.a - z.m * x.e) := by
    rw [conjP_mul_right_six, conjP_of_gaFour hz, SqU6.conjP_a, SqU6.conjP_e]
  have hy : conjP y (s * z) = conjP y s * liftC6 (z.n * y.a - z.m * y.e) := by
    rw [conjP_mul_right_six, conjP_of_gaFour hz, SqU6.conjP_a, SqU6.conjP_e]
  have hneg : -(z.n * x.a - z.m * x.e) = z.m * x.e - z.n * x.a := by ring
  rw [sqWord, sqWord, hx, hy, commP_mul_liftC6_right, mul_inv_rev, liftC6_inv, hneg,
    ← liftC6_comm, mul_liftC6_mul, mul_liftC6_mul, mul_liftC6_mul]

/-- ⭐ **Dressing both arguments of a commutator by `gamma_4`-elements translates it
centrally**, by the class-four coordinates paired against the other argument's outermost
abelian columns.  `GradedLift.commP_mul_gaThree` one class up. -/
theorem commP_mul_gaFour {z₃ z₄ : SqU6 R} (p q : SqU6 R) (hz₃ : z₃.IsGaFour)
    (hz₄ : z₄.IsGaFour) :
    commP (p * z₃) (q * z₄)
      = commP p q * liftC6 ((z₃.m * q.e - z₃.n * q.a) + (p.a * z₄.n - p.e * z₄.m)) := by
  obtain ⟨h3a, h3b, h3c, h3d, h3e, h3f, h3g, h3h, h3i, h3j, h3k, h3l⟩ := hz₃
  obtain ⟨h4a, h4b, h4c, h4d, h4e, h4f, h4g, h4h, h4i, h4j, h4k, h4l⟩ := hz₄
  rw [mul_liftC6_apply]
  ext <;>
    simp only [SqU6.commP_a, SqU6.commP_b, SqU6.commP_c, SqU6.commP_d, SqU6.commP_e,
      SqU6.commP_f, SqU6.commP_g, SqU6.commP_h, SqU6.commP_i, SqU6.commP_j, SqU6.commP_k,
      SqU6.commP_l, SqU6.commP_m, SqU6.commP_n, SqU6.commP_o, SqU6.u6Comm3L, SqU6.u6Comm3M,
      SqU6.u6Comm3R, SqU6.u6Comm4L, SqU6.u6Comm4R, SqU6.u6Comm5, SqU6.mul_a, SqU6.mul_b,
      SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i,
      SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
      h3a, h3b, h3c, h3d, h3e, h3f, h3g, h3h, h3i, h3j, h3k, h3l,
      h4a, h4b, h4c, h4d, h4e, h4f, h4g, h4h, h4i, h4j, h4k, h4l] <;>
    ring

end SigmaMove

/-! ## 3 The five-slot class-five refinement and its translation identity -/

section FiveLift

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

/-- One entry of a product over `Fin n` picking up a central right factor passes it to the
whole product.  (`GradedLift`'s copy is `private`, so this one is rebuilt here.) -/
private theorem prod_update_center_six {G : Type*} [Group G] (n : ℕ) :
    ∀ (F : Fin n → G) (jj : Fin n) (z : G), (∀ g : G, g * z = z * g) →
      ((List.finRange n).map fun k => if k = jj then F k * z else F k).prod
        = ((List.finRange n).map F).prod * z := by
  induction n with
  | zero => exact fun F jj z _ => jj.elim0
  | succ n ih =>
    intro F jj z hz
    rw [List.finRange_succ, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.map_map, List.map_map]
    cases jj using Fin.cases with
    | zero =>
      rw [if_pos rfl]
      have htail : (List.finRange n).map ((fun k => if k = 0 then F k * z else F k)
            ∘ Fin.succ) = (List.finRange n).map (F ∘ Fin.succ) := by
        refine List.map_congr_left fun k _ => ?_
        simp [Fin.succ_ne_zero]
      rw [htail, mul_assoc, ← hz ((List.finRange n).map (F ∘ Fin.succ)).prod, ← mul_assoc]
    | succ j' =>
      rw [if_neg (Fin.succ_ne_zero j').symm]
      have htail : (List.finRange n).map ((fun k => if k = Fin.succ j' then F k * z else F k)
            ∘ Fin.succ)
          = (List.finRange n).map fun k => if k = j' then (F ∘ Fin.succ) k * z
              else (F ∘ Fin.succ) k := by
        refine List.map_congr_left fun k _ => ?_
        simp only [Function.comp_apply, Fin.succ_inj]
      rw [htail, ih (F ∘ Fin.succ) j' z hz, ← mul_assoc]

/-- ⭐ **The handle block swallows one dressed handle pair centrally** at class five:
dressing the `j`-th handle pair by `gamma_4`-elements multiplies `handleWord` by the central
translation of `commP_mul_gaFour`. -/
theorem handleWord_mul_gaFour {z₃ z₄ : SqU6 R} (u v : Fin h → SqU6 R) (hz₃ : z₃.IsGaFour)
    (hz₄ : z₄.IsGaFour) :
    handleWord (fun k => if k = j then u k * z₃ else u k)
        (fun k => if k = j then v k * z₄ else v k)
      = handleWord u v
        * liftC6 ((z₃.m * (v j).e - z₃.n * (v j).a) + ((u j).a * z₄.n - (u j).e * z₄.m)) := by
  rw [handleWord, handleWord]
  have hmap : ((List.finRange h).map fun k => commP (if k = j then u k * z₃ else u k)
        (if k = j then v k * z₄ else v k))
      = (List.finRange h).map fun k => if k = j then (fun k' => commP (u k') (v k')) k
          * liftC6 ((z₃.m * (v j).e - z₃.n * (v j).a) + ((u j).a * z₄.n - (u j).e * z₄.m))
          else (fun k' => commP (u k') (v k')) k := by
    refine List.map_congr_left fun k _ => ?_
    by_cases hk : k = j
    · subst hk
      rw [if_pos rfl, if_pos rfl, if_pos rfl, commP_mul_gaFour _ _ hz₃ hz₄]
    · rw [if_neg hk, if_neg hk, if_neg hk]
  rw [hmap, prod_update_center_six h _ j _ (fun g => liftC6_comm g _)]

variable (j) in
/-- **The five-slot class-five refinement**: dress the sigma slot by a `gamma_4`-element `z₀`,
the two exponent slots by `gamma_5`-elements, and the two `j`-handle slots by
`gamma_4`-elements.  `GradedSigmaFour.sigLift` one class up, and the shape of refinement the
class-five census sweeps (`scripts/w59_force5/verify_force5.py` section 4). -/
def fiveLift (m : Fin (sqRank h) → SqU6 R) (z₀ w₁ w₂ z₃ z₄ : SqU6 R) :
    Fin (sqRank h) → SqU6 R :=
  fun i =>
    if (i : ℕ) = 0 then m i * z₀ else
    if (i : ℕ) = 1 then m i * w₁ else
    if (i : ℕ) = 2 then m i * w₂ else
    if i = sqHandleIdxU j then m i * z₃ else
    if i = sqHandleIdxV j then m i * z₄ else m i

variable {m : Fin (sqRank h) → SqU6 R} {z₀ w₁ w₂ z₃ z₄ : SqU6 R}

private theorem six_ne_handleU_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxU j := by
  intro hc
  rw [hc, sqHandleIdxU_val] at hi
  omega

private theorem six_ne_handleV_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxV j := by
  intro hc
  rw [hc, sqHandleIdxV_val] at hi
  omega

private theorem six_handleU_ne_handleV (j' : Fin h) : sqHandleIdxU j' ≠ sqHandleIdxV j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxU_val, sqHandleIdxV_val] at hv
  omega

private theorem six_handleV_ne_handleU (j' : Fin h) : sqHandleIdxV j' ≠ sqHandleIdxU j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxV_val, sqHandleIdxU_val] at hv
  omega

@[simp] theorem fiveLift_zero : fiveLift j m z₀ w₁ w₂ z₃ z₄ 0 = m 0 * z₀ := by
  simp only [fiveLift, sqVal_zero]
  norm_num

@[simp] theorem fiveLift_one : fiveLift j m z₀ w₁ w₂ z₃ z₄ 1 = m 1 * w₁ := by
  simp only [fiveLift, sqVal_one]
  rw [if_neg (by omega)]
  norm_num

@[simp] theorem fiveLift_two : fiveLift j m z₀ w₁ w₂ z₃ z₄ 2 = m 2 * w₂ := by
  simp only [fiveLift, sqVal_two]
  rw [if_neg (by omega), if_neg (by omega)]
  norm_num

@[simp] theorem fiveLift_handleU {j' : Fin h} :
    fiveLift j m z₀ w₁ w₂ z₃ z₄ (sqHandleIdxU j')
      = if j' = j then m (sqHandleIdxU j') * z₃ else m (sqHandleIdxU j') := by
  simp only [fiveLift, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (six_handleU_ne_handleV j')]
  by_cases hj : j' = j
  · subst hj
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hj, if_neg fun hc => hj (Fin.val_injective (by
      have hv := congrArg Fin.val hc
      rw [sqHandleIdxU_val, sqHandleIdxU_val] at hv
      omega))]

@[simp] theorem fiveLift_handleV {j' : Fin h} :
    fiveLift j m z₀ w₁ w₂ z₃ z₄ (sqHandleIdxV j')
      = if j' = j then m (sqHandleIdxV j') * z₄ else m (sqHandleIdxV j') := by
  simp only [fiveLift, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (six_handleV_ne_handleU j')]
  by_cases hj : j' = j
  · subst hj
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hj, if_neg fun hc => hj (Fin.val_injective (by
      have hv := congrArg Fin.val hc
      rw [sqHandleIdxV_val, sqHandleIdxV_val] at hv
      omega))]

/-- ⭐⭐ **The translation identity at class five**: the five-slot refinement translates the
relator by a **central** element, affine-linear in the five dressings, with the sigma-slot move
reading the `x0`-slot's outermost abelian columns `(a, e)` and the two handle moves reading each
other's.  Every class-`<= 4` row is untouched, and no closed form of the relator is consumed.
`GradedSigmaFour.sqRelWord_sigLift` one class up; certified against honest collection at
`4800` refinements of the witness point and `400` random markings
(`scripts/w59_force5/results/verify_force5.txt` section 3). -/
theorem sqRelWord_fiveLift (hz₀ : z₀.IsGaFour) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃.IsGaFour) (hz₄ : z₄.IsGaFour) :
    sqRelWord (fiveLift j m z₀ w₁ w₂ z₃ z₄)
      = sqRelWord m * liftC6 ((z₀.m * (m 1).e - z₀.n * (m 1).a) + (-4 * w₁.o + 2 * w₂.o)
          + ((z₃.m * (m (sqHandleIdxV j)).e - z₃.n * (m (sqHandleIdxV j)).a)
            + ((m (sqHandleIdxU j)).a * z₄.n - (m (sqHandleIdxU j)).e * z₄.m))) := by
  have hu : (fun j' => fiveLift j m z₀ w₁ w₂ z₃ z₄ (sqHandleIdxU j'))
      = fun k => if k = j then (fun j' => m (sqHandleIdxU j')) k * z₃
          else (fun j' => m (sqHandleIdxU j')) k := by
    funext k
    rw [fiveLift_handleU]
  have hv : (fun j' => fiveLift j m z₀ w₁ w₂ z₃ z₄ (sqHandleIdxV j'))
      = fun k => if k = j then (fun j' => m (sqHandleIdxV j')) k * z₄
          else (fun j' => m (sqHandleIdxV j')) k := by
    funext k
    rw [fiveLift_handleV]
  rw [sqRelWord, sqRelWord, fiveLift_zero, fiveLift_one, fiveLift_two, hu, hv,
    handleWord_mul_gaFour _ _ hz₃ hz₄, hw₁.eq_liftC6, hw₂.eq_liftC6, sqWord_mul_liftC6,
    sqWord_mul_gaFour_sigma hz₀]
  simp only [liftC6_o]
  rw [liftC6_collect3]
  exact congrArg (fun t : R => sqWord (m 0) (m 1) (m 2)
    * handleWord (fun j' => m (sqHandleIdxU j')) (fun j' => m (sqHandleIdxV j')) * liftC6 t)
    (by ring)

end FiveLift

/-! ## 4 The binder point of the class-five note, and its two verdicts -/

section Point

/-- **The class-five sigma marking** `E_23`: the unique lift of `GradedSigmaFour.sigFourMark`
along `toU5L`.  `nu'`-triviality of a dressing is again `v.b = 0`. -/
def fiveSigMark (R : Type) [CommRing R] : SqU6 R := ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[simp] theorem toU5L_fiveSigMark {R : Type} [CommRing R] :
    SqU6.toU5L (fiveSigMark R) = sigFourMark R := rfl

/-- The `U`-letter of the binder point: `<a=1, c=2, d=3, f=3, g=2, h=2, i=2>`. -/
def forceU : SqU6 gr3R := ⟨1, 0, 2, 3, 0, 3, 2, 2, 2, 0, 0, 0, 0, 0, 0⟩

/-- The `V`-letter: `<d=1, e=2, f=3, g=2, h=3, i=3>`.  Its commutator with `forceU` is the
handle block, **live**, and live in the class-four row. -/
def forceV : SqU6 gr3R := ⟨0, 0, 0, 1, 2, 3, 2, 3, 3, 0, 0, 0, 0, 0, 0⟩

/-- The `x0`-slot: `<a=2, e=1>`.  Every datum the committed class-two-forced gauge constrains
is even here; the fifth abelian column `e = x_{56}` is **odd**, and it is a matrix entry `U_5`
does not have. -/
def forceX : SqU6 gr3R := ⟨2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x1`-slot: `<e=2, f=1, h=3, i=1, j=2, k=2, l=2, m=3, n=2, o=2>`, the layered solve of
the fifteen rows against the live block. -/
def forceY : SqU6 gr3R := ⟨0, 0, 0, 0, 2, 1, 0, 3, 1, 2, 2, 2, 3, 2, 2⟩

/-- **The class-five sigma-witness binder point**, at every handle count and every handle,
with the sigma slot dressed by `v`. -/
def fiveWit (h : ℕ) (j : Fin h) (v : SqU6 gr3R) : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j (fiveSigMark gr3R * v) forceX forceY forceU forceV

/-- ⭐⭐ **The undressed frame kills the relator outright**: all fifteen rows vanish, at every
handle count and every handle. -/
theorem sqRelWord_fiveWit_triv (h : ℕ) (j : Fin h) : sqRelWord (fiveWit h j 1) = 1 := by
  rw [fiveWit, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐ **The `a0 = a1` dressing leaves the ODD class-five residue `7`**, at every handle count
and every handle: the fourteen lower rows die and the top row does not.  This is the
separation `GradedSigmaFour` section 7 said needs class five. -/
theorem sqRelWord_fiveWit_diag (h : ℕ) (j : Fin h) :
    sqRelWord (fiveWit h j forceX) = liftC6 7 := by
  rw [fiveWit, sqRelWord_fiveTuple]
  decide

/-- The handle block of the point is **live**, and live in the class-four row `x_{15}`, which
is what a dead block cannot supply (wave 58, section 3.3). -/
theorem commP_forceUV_live : commP forceU forceV ≠ 1 ∧ selPar (commP forceU forceV).m = 1 := by
  refine ⟨?_, by decide⟩
  decide

/-- ⭐ **The point sits on the committed class-two-forced gauge**, and the single datum
escaping it is the `x0`-slot's fifth abelian column.  In `toU5L`-coordinates the eight
evennesses are exactly the hypotheses of `GradedSigmaFour.sigFourRead_gauge`. -/
theorem forceX_gauge :
    forceX.a = 2 * 1 ∧ forceX.c = 2 * 0 ∧ forceX.d = 2 * 0 ∧ forceX.f = 2 * 0
      ∧ forceX.g = 2 * 0 ∧ forceY.a = 2 * 0 ∧ forceY.c = 2 * 0 ∧ forceY.d = 2 * 0
      ∧ forceX.b = 0 ∧ selPar forceX.e = 1 := by decide

/-- ⭐⭐ **The whole committed class-`<= 4` machinery cannot separate the two dressings**: both
`U_5`-quotients of the marking kill the class-four relator at both dressings.  The separation
of `sqRelWord_fiveWit_diag` is purely class five. -/
theorem fiveWit_class_four_blind (h : ℕ) (j : Fin h) :
    (sqRelWord (fun i => SqU6.toU5L (fiveWit h j 1 i)) = 1
        ∧ sqRelWord (fun i => SqU6.toU5R (fiveWit h j 1 i)) = 1)
      ∧ (sqRelWord (fun i => SqU6.toU5L (fiveWit h j forceX i)) = 1
        ∧ sqRelWord (fun i => SqU6.toU5R (fiveWit h j forceX i)) = 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_fiveWit_triv, map_one]
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_fiveWit_triv, map_one]
  · rw [← SqU6.toU5L_sqRelWord, sqRelWord_fiveWit_diag]
    decide
  · rw [← SqU6.toU5R_sqRelWord, sqRelWord_fiveWit_diag]
    decide

/-- …and the class-four **rows** of the dressed relator vanish outright: the residue lives in
the `(1,6)` entry alone. -/
theorem fiveWit_diag_class_four_rows (h : ℕ) (j : Fin h) :
    (sqRelWord (fiveWit h j forceX)).m = 0 ∧ (sqRelWord (fiveWit h j forceX)).n = 0 := by
  rw [sqRelWord_fiveWit_diag]
  exact ⟨rfl, rfl⟩

end Point

/-! ## 5 Soundness: every achievable `gamma_4`-dressing is even in `(m, n)` -/

section Achievable

/-- The repo commutator against mathlib's. -/
theorem commutatorElement_eq_commP (p q : SqU6 gr3R) : ⁅p, q⁆ = commP p⁻¹ q⁻¹ := by
  rw [commutatorElement_def, commP, inv_inv, inv_inv]

/-- **`N_1`**: an even `(3,4)`-column.  Every letter of the binder point lies here, and this
single constraint drives the whole chain. -/
def forceN1 : Subgroup (SqU6 gr3R) where
  carrier := {z | ∃ t : gr3R, z.c = 2 * t}
  mul_mem' := by
    rintro p q ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, by rw [SqU6.mul_c, hs, ht]; ring⟩
  one_mem' := ⟨0, by rw [SqU6.one_c]; ring⟩
  inv_mem' := by
    rintro p ⟨s, hs⟩
    exact ⟨-s, by rw [SqU6.inv_c, hs]; ring⟩

/-- **`N_2`**: a `gamma_2`-element whose two middle class-two coordinates are even. -/
def forceN2 : Subgroup (SqU6 gr3R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0
    ∧ (∃ t : gr3R, z.g = 2 * t) ∧ (∃ t : gr3R, z.h = 2 * t)}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, ⟨s, hs⟩, ⟨u, hu⟩⟩ ⟨qa, qb, qc, qd, qe, ⟨s', hs'⟩, ⟨u', hu'⟩⟩
    refine ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, ⟨s + s', by rw [SqU6.mul_g, hs, hs', pb]; ring⟩,
      ⟨u + u', by rw [SqU6.mul_h, hu, hu', pc]; ring⟩⟩
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, ⟨0, by rw [SqU6.one_g]; ring⟩,
    ⟨0, by rw [SqU6.one_h]; ring⟩⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, ⟨s, hs⟩, ⟨u, hu⟩⟩
    refine ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, ⟨-s, by rw [SqU6.inv_g, hs, pb, pc]; ring⟩,
      ⟨-u, by rw [SqU6.inv_h, hu, pc, pd]; ring⟩⟩

/-- **`N_3`**: a `gamma_3`-element whose three class-three coordinates are even. -/
def forceN3 : Subgroup (SqU6 gr3R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
    ∧ z.h = 0 ∧ z.i = 0
    ∧ (∃ t : gr3R, z.j = 2 * t) ∧ (∃ t : gr3R, z.k = 2 * t) ∧ (∃ t : gr3R, z.l = 2 * t)}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, ⟨s, hs⟩, ⟨u, hu⟩, ⟨w, hw⟩⟩
      ⟨qa, qb, qc, qd, qe, qf, qg, qh, qi, ⟨s', hs'⟩, ⟨u', hu'⟩, ⟨w', hw'⟩⟩
    refine ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, by rw [SqU6.mul_f, pf, qf, pa]; ring,
      by rw [SqU6.mul_g, pg, qg, pb]; ring, by rw [SqU6.mul_h, ph, qh, pc]; ring,
      by rw [SqU6.mul_i, pi, qi, pd]; ring,
      ⟨s + s', by rw [SqU6.mul_j, hs, hs', pa, pf]; ring⟩,
      ⟨u + u', by rw [SqU6.mul_k, hu, hu', pb, pg]; ring⟩,
      ⟨w + w', by rw [SqU6.mul_l, hw, hw', pc, ph]; ring⟩⟩
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨0, by rw [SqU6.one_j]; ring⟩,
    ⟨0, by rw [SqU6.one_k]; ring⟩, ⟨0, by rw [SqU6.one_l]; ring⟩⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, ⟨s, hs⟩, ⟨u, hu⟩, ⟨w, hw⟩⟩
    refine ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, by rw [SqU6.inv_f, pf, pa, pb]; ring,
      by rw [SqU6.inv_g, pg, pb, pc]; ring, by rw [SqU6.inv_h, ph, pc, pd]; ring,
      by rw [SqU6.inv_i, pi, pd, pe]; ring,
      ⟨-s, by rw [SqU6.inv_j, hs, pa, pb, pc, pf, pg]; ring⟩,
      ⟨-u, by rw [SqU6.inv_k, hu, pb, pc, pd, pg, ph]; ring⟩,
      ⟨-w, by rw [SqU6.inv_l, hw, pc, pd, pe, ph, pi]; ring⟩⟩

/-- **`N_4`**: a `gamma_4`-element whose two class-four coordinates are even.  This is the
lattice the class-five selection bit reads. -/
def forceN4 : Subgroup (SqU6 gr3R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
    ∧ z.h = 0 ∧ z.i = 0 ∧ z.j = 0 ∧ z.k = 0 ∧ z.l = 0
    ∧ (∃ t : gr3R, z.m = 2 * t) ∧ (∃ t : gr3R, z.n = 2 * t)}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl, ⟨s, hs⟩, ⟨u, hu⟩⟩
      ⟨qa, qb, qc, qd, qe, qf, qg, qh, qi, qj, qk, ql, ⟨s', hs'⟩, ⟨u', hu'⟩⟩
    refine ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, by rw [SqU6.mul_f, pf, qf, pa]; ring,
      by rw [SqU6.mul_g, pg, qg, pb]; ring, by rw [SqU6.mul_h, ph, qh, pc]; ring,
      by rw [SqU6.mul_i, pi, qi, pd]; ring, by rw [SqU6.mul_j, pj, qj, pa, pf]; ring,
      by rw [SqU6.mul_k, pk, qk, pb, pg]; ring, by rw [SqU6.mul_l, pl, ql, pc, ph]; ring,
      ⟨s + s', by rw [SqU6.mul_m, hs, hs', pa, pf, pj]; ring⟩,
      ⟨u + u', by rw [SqU6.mul_n, hu, hu', pb, pg, pk]; ring⟩⟩
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨0, by rw [SqU6.one_m]; ring⟩, ⟨0, by rw [SqU6.one_n]; ring⟩⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl, ⟨s, hs⟩, ⟨u, hu⟩⟩
    refine ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, by rw [SqU6.inv_f, pf, pa, pb]; ring,
      by rw [SqU6.inv_g, pg, pb, pc]; ring, by rw [SqU6.inv_h, ph, pc, pd]; ring,
      by rw [SqU6.inv_i, pi, pd, pe]; ring,
      by rw [SqU6.inv_j, pj, pa, pb, pc, pf, pg]; ring,
      by rw [SqU6.inv_k, pk, pb, pc, pd, pg, ph]; ring,
      by rw [SqU6.inv_l, pl, pc, pd, pe, ph, pi]; ring,
      ⟨-s, by rw [SqU6.inv_m, hs, pa, pb, pc, pd, pf, pg, ph, pj, pk]; ring⟩,
      ⟨-u, by rw [SqU6.inv_n, hu, pb, pc, pd, pe, pg, ph, pi, pk, pl]; ring⟩⟩

theorem mem_forceN1 {z : SqU6 gr3R} : z ∈ forceN1 ↔ ∃ t : gr3R, z.c = 2 * t := Iff.rfl

theorem mem_forceN2 {z : SqU6 gr3R} :
    z ∈ forceN2 ↔ z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0
      ∧ (∃ t : gr3R, z.g = 2 * t) ∧ (∃ t : gr3R, z.h = 2 * t) := Iff.rfl

theorem mem_forceN3 {z : SqU6 gr3R} :
    z ∈ forceN3 ↔ z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
      ∧ z.h = 0 ∧ z.i = 0
      ∧ (∃ t : gr3R, z.j = 2 * t) ∧ (∃ t : gr3R, z.k = 2 * t) ∧ (∃ t : gr3R, z.l = 2 * t) :=
  Iff.rfl

theorem mem_forceN4 {z : SqU6 gr3R} :
    z ∈ forceN4 ↔ z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
      ∧ z.h = 0 ∧ z.i = 0 ∧ z.j = 0 ∧ z.k = 0 ∧ z.l = 0
      ∧ (∃ t : gr3R, z.m = 2 * t) ∧ (∃ t : gr3R, z.n = 2 * t) := Iff.rfl

/-- Every element of `N_4` is `gamma_4`-shaped, so the translation identity applies to it. -/
theorem forceN4_isGaFour {z : SqU6 gr3R} (hz : z ∈ forceN4) : z.IsGaFour :=
  ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1, hz.2.2.2.2.2.2.1,
    hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.2.1,
    hz.2.2.2.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- …and its two class-four coordinates are even. -/
theorem forceN4_even {z : SqU6 gr3R} (hz : z ∈ forceN4) :
    (∃ t : gr3R, z.m = 2 * t) ∧ (∃ t : gr3R, z.n = 2 * t) :=
  ⟨hz.2.2.2.2.2.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- ⭐ **Step one**: a commutator of two elements with even `(3,4)`-columns is a
`gamma_2`-element whose two middle class-two coordinates are even.  The `g`-pairing is
`p.b * q.c - p.c * q.b` and the `h`-pairing is `p.c * q.d - p.d * q.c`; both meet the even
column. -/
theorem forceN2_of_commutator {p q : SqU6 gr3R} (hp : p ∈ forceN1) (hq : q ∈ forceN1) :
    ⁅p, q⁆ ∈ forceN2 := by
  obtain ⟨s, hs⟩ := mem_forceN1.mp hp
  obtain ⟨t, ht⟩ := mem_forceN1.mp hq
  rw [commutatorElement_eq_commP, mem_forceN2]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ⟨p.b * t - s * q.b, ?_⟩, ⟨s * q.d - p.d * t, ?_⟩⟩
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, hs, ht]
    ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, hs, ht]
    ring

/-- ⭐ **Step two**: pairing such a `gamma_2`-element against an even `(3,4)`-column gives a
`gamma_3`-element with all three class-three coordinates even.  The three pairings are
`-z.g * q.a + z.f * q.c`, `-z.h * q.b + z.g * q.d` and `-z.i * q.c + z.h * q.e`: the first and
the third meet the even column, the second meets an even coordinate on both terms. -/
theorem forceN3_of_commutator {p q : SqU6 gr3R} (hp : p ∈ forceN2) (hq : q ∈ forceN1) :
    ⁅p, q⁆ ∈ forceN3 := by
  obtain ⟨pa, pb, pc, pd, pe, ⟨s, hs⟩, ⟨u, hu⟩⟩ := mem_forceN2.mp hp
  obtain ⟨t, ht⟩ := mem_forceN1.mp hq
  rw [commutatorElement_eq_commP, mem_forceN3]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ?_, ?_, ?_, ?_, ⟨p.f * t - s * q.a, ?_⟩, ⟨s * q.d - u * q.b, ?_⟩,
    ⟨u * q.e - p.i * t, ?_⟩⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, pa, pb]
    ring
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, pb, pc]
    ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, pc, pd]
    ring
  · simp only [SqU6.commP_i, SqU6.inv_d, SqU6.inv_e, pd, pe]
    ring
  · simp only [SqU6.commP_j, SqU6.u6Comm3L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_f,
      SqU6.inv_g, pa, pb, pc, hs, ht]
    ring
  · simp only [SqU6.commP_k, SqU6.u6Comm3M, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_g,
      SqU6.inv_h, pb, pc, pd, hs, hu, ht]
    ring
  · simp only [SqU6.commP_l, SqU6.u6Comm3R, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_h,
      SqU6.inv_i, pc, pd, pe, hu, ht]
    ring

/-- ⭐ **Step three**: pairing such a `gamma_3`-element against **any** element gives a
`gamma_4`-element with both class-four coordinates even.  The two pairings are
`z.j * q.d - z.k * q.a` and `z.k * q.e - z.l * q.b`, and the evenness needs nothing of `q`:
the class-three evenness of step two carries the whole way. -/
theorem forceN4_of_commutator {p q : SqU6 gr3R} (hp : p ∈ forceN3) : ⁅p, q⁆ ∈ forceN4 := by
  obtain ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, ⟨s, hs⟩, ⟨u, hu⟩, ⟨w, hw⟩⟩ := mem_forceN3.mp hp
  rw [commutatorElement_eq_commP, mem_forceN4]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨s * q.d - u * q.a, ?_⟩,
    ⟨u * q.e - w * q.b, ?_⟩⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, pa, pb]
    ring
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, pb, pc]
    ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, pc, pd]
    ring
  · simp only [SqU6.commP_i, SqU6.inv_d, SqU6.inv_e, pd, pe]
    ring
  · simp only [SqU6.commP_j, SqU6.u6Comm3L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_f,
      SqU6.inv_g, pa, pb, pc, pf, pg]
    ring
  · simp only [SqU6.commP_k, SqU6.u6Comm3M, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_g,
      SqU6.inv_h, pb, pc, pd, pg, ph]
    ring
  · simp only [SqU6.commP_l, SqU6.u6Comm3R, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_h,
      SqU6.inv_i, pc, pd, pe, ph, pi]
    ring
  · simp only [SqU6.commP_m, SqU6.u6Comm4L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d,
      SqU6.inv_f, SqU6.inv_g, SqU6.inv_h, SqU6.inv_j, SqU6.inv_k,
      pa, pb, pc, pd, pf, pg, ph, hs, hu]
    ring
  · simp only [SqU6.commP_n, SqU6.u6Comm4R, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e,
      SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_k, SqU6.inv_l,
      pb, pc, pd, pe, pg, ph, pi, hu, hw]
    ring

/-- **The lower central series of a subgroup**, as subgroups of the ambient carrier:
`forceLcs H 0 = H` and `forceLcs H (n+1) = [forceLcs H n, H]`, so `forceLcs H 3` is
`gamma_4(H)`, the achievable `gamma_4`-dressings of a marking whose image is `H`. -/
def forceLcs (H : Subgroup (SqU6 gr3R)) : ℕ → Subgroup (SqU6 gr3R)
  | 0 => H
  | n + 1 => ⁅forceLcs H n, H⁆

/-- ⭐⭐ **Soundness, PROVED**: at any marking all of whose slots have an even `(3,4)`-column,
every achievable `gamma_4`-dressing is `gamma_4`-shaped with **even** class-four coordinates
`x_{15}` and `x_{26}`.  This is the class-five transposition of
`GradedSigmaFour.sigFourWit_lamThree_even`, and unlike that one it is not a statement about a
declared lattice but about the honest lower central series of the image: the census of
`scripts/w59_force5/` measures the same lattice by two independent routes and finds it
**exactly** the even one, so this bound is sharp. -/
theorem forceLcs_three_le_forceN4 {H : Subgroup (SqU6 gr3R)} (hH : H ≤ forceN1) :
    forceLcs H 3 ≤ forceN4 := by
  have h1 : forceLcs H 1 ≤ forceN2 :=
    Subgroup.commutator_le.mpr fun p hp q hq => forceN2_of_commutator (hH hp) (hH hq)
  have h2 : forceLcs H 2 ≤ forceN3 :=
    Subgroup.commutator_le.mpr fun p hp q hq => forceN3_of_commutator (h1 hp) (hH hq)
  exact Subgroup.commutator_le.mpr fun p hp _ _ => forceN4_of_commutator (h2 hp)

end Achievable

/-! ## 6 The bit, the forcing, and the exclusion -/

section Forcing

variable {h : ℕ} {j : Fin h}

/-- Every slot of a one-handle-live tuple is one of its five letters or trivial. -/
private theorem fiveTuple_cases {R : Type} [CommRing R] {hh : ℕ} {jj : Fin hh}
    (S X Y U V : SqU6 R) (i : Fin (sqRank hh)) :
    fiveTuple R hh jj S X Y U V i = S ∨ fiveTuple R hh jj S X Y U V i = X
      ∨ fiveTuple R hh jj S X Y U V i = Y ∨ fiveTuple R hh jj S X Y U V i = U
      ∨ fiveTuple R hh jj S X Y U V i = V ∨ fiveTuple R hh jj S X Y U V i = 1 := by
  simp only [fiveTuple]
  split_ifs <;> tauto

/-- **The image of the binder point**: the subgroup of the class-five carrier generated by the
marking's slot values.  Its lower central series is what the achievability census computes
(`scripts/w59_force5/verify_force5.py` section 2), and `forceLcs (forceImage h j v) 3` is the
set of achievable `gamma_4`-dressings there. -/
def forceImage (h : ℕ) (j : Fin h) (v : SqU6 gr3R) : Subgroup (SqU6 gr3R) :=
  Subgroup.closure (Set.range (fiveWit h j v))

/-- ⭐ **The point's letters all have an even `(3,4)`-column**, which is the only input the
soundness chain needs.  `forceU` is the one letter with a non-zero one, and it is `2`. -/
theorem forceImage_le_forceN1 {v : SqU6 gr3R} (hv : ∃ t : gr3R, v.c = 2 * t) :
    forceImage h j v ≤ forceN1 := by
  obtain ⟨t, ht⟩ := hv
  rw [forceImage, Subgroup.closure_le]
  rintro z ⟨i, rfl⟩
  simp only [fiveWit]
  rcases fiveTuple_cases (fiveSigMark gr3R * v) forceX forceY forceU forceV i with
    h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1, SetLike.mem_coe, mem_forceN1]
  · exact ⟨t, by rw [SqU6.mul_c, ht]; simp [fiveSigMark]⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩

/-- Reading the class-five residue off a killed frame: if `p * liftC6 w = 1` then `p.o = -w`. -/
private theorem o_of_mul_liftC6_eq_one {p : SqU6 gr3R} {w : gr3R} (hp : p * liftC6 w = 1) :
    p.o = -w := by
  have hq := congrArg SqU6.o hp
  rw [mul_liftC6_apply] at hq
  simp only [SqU6.one_o] at hq
  exact eq_neg_of_add_eq_zero_left hq

/-- ⭐⭐ **The class-five selection bit is forced even.**  At the binder point, a sigma dressing
whose frame is killed by **any** achievable five-slot refinement leaves an **even** class-five
residue.  This is `GradedSigmaFour.sigFourWit_sigma_forced` one class up, and its soundness
input is the theorem `forceLcs_three_le_forceN4` rather than a declared lattice. -/
theorem fiveWit_sigma_forced {v z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R} (hv : ∃ t : gr3R, v.c = 2 * t)
    (hz₀ : z₀ ∈ forceLcs (forceImage h j v) 3) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃ ∈ forceLcs (forceImage h j v) 3) (hz₄ : z₄ ∈ forceLcs (forceImage h j v) 3)
    (hkill : sqRelWord (fiveLift j (fiveWit h j v) z₀ w₁ w₂ z₃ z₄) = 1) :
    selPar (sqRelWord (fiveWit h j v)).o = 0 := by
  have hle := forceLcs_three_le_forceN4 (forceImage_le_forceN1 (h := h) (j := j) hv)
  obtain ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩ := forceN4_even (hle hz₀)
  obtain ⟨⟨a₃, ha₃⟩, ⟨b₃, hb₃⟩⟩ := forceN4_even (hle hz₃)
  obtain ⟨⟨a₄, ha₄⟩, ⟨b₄, hb₄⟩⟩ := forceN4_even (hle hz₄)
  rw [sqRelWord_fiveLift (forceN4_isGaFour (hle hz₀)) hw₁ hw₂ (forceN4_isGaFour (hle hz₃))
    (forceN4_isGaFour (hle hz₄))] at hkill
  have heven : (sqRelWord (fiveWit h j v)).o = 2 *
      (-((a₀ * (fiveWit h j v 1).e - b₀ * (fiveWit h j v 1).a) + (-2 * w₁.o + w₂.o)
        + ((a₃ * (fiveWit h j v (sqHandleIdxV j)).e
            - b₃ * (fiveWit h j v (sqHandleIdxV j)).a)
          + ((fiveWit h j v (sqHandleIdxU j)).a * b₄
            - (fiveWit h j v (sqHandleIdxU j)).e * a₄)))) := by
    rw [o_of_mul_liftC6_eq_one hkill, ha₀, hb₀, ha₃, hb₃, ha₄, hb₄]
    ring
  rw [heven, selPar_two_mul]

/-- ⭐⭐ **THE FORCING: the sigma dressing `a0 = a1` is EXCLUDED at class five.**  No achievable
five-slot refinement whatsoever kills the dressed frame, at any handle count and any handle.
This is the residual `GradedSigmaFour` section 7 named, discharged: class four identifies the
dressing with the trivial one (`GradedSigmaFive.sigFourRead_diag_even`, at *every* marking),
and class five separates them.  ⚠ Read with `fiveWit_gaThree_kill`: the quantifier is over
achievable `gamma_4`-dressings, and one filtration step wider the statement is false. -/
theorem sqRelWord_fiveWit_diag_ne_one {z₀ w₁ w₂ z₃ z₄ : SqU6 gr3R}
    (hz₀ : z₀ ∈ forceLcs (forceImage h j forceX) 3) (hw₁ : w₁.IsGaFive) (hw₂ : w₂.IsGaFive)
    (hz₃ : z₃ ∈ forceLcs (forceImage h j forceX) 3)
    (hz₄ : z₄ ∈ forceLcs (forceImage h j forceX) 3) :
    sqRelWord (fiveLift j (fiveWit h j forceX) z₀ w₁ w₂ z₃ z₄) ≠ 1 := by
  intro hc
  have hp := fiveWit_sigma_forced ⟨0, by decide⟩ hz₀ hw₁ hw₂ hz₃ hz₄ hc
  rw [sqRelWord_fiveWit_diag, liftC6_o] at hp
  exact absurd hp (by decide)

/-- …while the undressed frame is killed outright, so the bit really does separate the two
dressings that `GradedSigmaFour` could not tell apart. -/
theorem fiveWit_bit_separates (h : ℕ) (j : Fin h) :
    selPar (sqRelWord (fiveWit h j 1)).o = 0
      ∧ selPar (sqRelWord (fiveWit h j forceX)).o = 1 := by
  refine ⟨?_, ?_⟩
  · rw [sqRelWord_fiveWit_triv]
    decide
  · rw [sqRelWord_fiveWit_diag, liftC6_o]
    decide

/-- ⭐ **Achievability is load-bearing, and this is the witness.**  The *unrestricted*
`gamma_4`-move `<m = 1>` on the sigma slot kills the dressed frame outright: its increment is
`1 * x_{56} = 1`, and `7 + 1 = 0`.  So the forcing above is not a statement the lattice could
be dropped from.  Compare `GradedFourCleared`: "8 of the 64 unrestricted `gamma_3`-moves kill
the odd dressing". -/
theorem fiveWit_unrestricted_kill (h : ℕ) (j : Fin h) :
    sqRelWord (fiveLift j (fiveWit h j forceX)
      ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ 1 1 1 1) = 1 := by
  rw [sqRelWord_fiveLift ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    SqU6.isGaFive_one SqU6.isGaFive_one SqU6.isGaFour_one SqU6.isGaFour_one,
    sqRelWord_fiveWit_diag, liftC6_mul_liftC6]
  refine Eq.trans (congrArg liftC6 ?_) liftC6_zero
  simp only [fiveWit, fiveTuple_one, SqU6.one_m, SqU6.one_n, SqU6.one_o]
  ring_nf
  decide

/-- …and that move is **not** achievable: its class-four coordinate is odd, and every
achievable one is even. -/
theorem fiveWit_unrestricted_not_achievable :
    (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩ : SqU6 gr3R) ∉ forceN4 := by
  intro hc
  obtain ⟨⟨t, ht⟩, -⟩ := forceN4_even hc
  exact absurd ht (by revert t; decide)

/-! ### ⚠⚠ How far the exclusion reaches, and where it stops

The forcing above quantifies over `gamma_4`-dressings drawn from `gamma_4` of the image, which
is the exact transposition of the committed class-four convention.  It is **not** robust one
filtration step wider, and the following three declarations say so precisely: a triple
commutator of the point's own letters is `gamma_4`-**shaped** with an **odd** class-four
coordinate, so it lies in `gamma_3` of the image and not in `gamma_4` of it, and dressing the
sigma slot by it kills the `a0 = a1`-dressed frame outright.  Measured at the committed
class-four point, the analogous wider class kills nothing (`scripts/w59_force5/results/
scope_probe.txt` section B: `0` of `128` achievable `gamma_2`-dressings kill the odd frame that
`GradedSigmaFour.sqRelWord_sigFourWit_U_ne_one` excludes), so this is a way in which the
class-five statement is weaker than its class-four model rather than a general feature of the
stage convention. -/

/-- Every slot value of a marking lies in its image. -/
theorem mem_forceImage_slot (h : ℕ) (j : Fin h) (v : SqU6 gr3R) (i : Fin (sqRank h)) :
    fiveWit h j v i ∈ forceImage h j v :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- A repo commutator of two members lands in the commutator subgroup. -/
private theorem commP_mem_commutator {H K : Subgroup (SqU6 gr3R)} {p q : SqU6 gr3R}
    (hp : p ∈ H) (hq : q ∈ K) : commP p q ∈ ⁅H, K⁆ := by
  have hc := Subgroup.commutator_mem_commutator (H.inv_mem hp) (K.inv_mem hq)
  rwa [commutatorElement_eq_commP, inv_inv, inv_inv] at hc

/-- ⚠⚠ **The killing dressing is a triple commutator of the point's own letters**, hence
achievable at the `gamma_3` level. -/
theorem fiveWit_gaThree_kill_mem (h : ℕ) (j : Fin h) :
    commP (commP (fiveSigMark gr3R) forceU) forceY
      ∈ forceLcs (forceImage h j forceX) 2 := by
  have hzero : fiveSigMark gr3R * forceX ∈ forceImage h j forceX := by
    have := mem_forceImage_slot h j forceX 0
    rwa [fiveWit, fiveTuple_zero] at this
  have hX : forceX ∈ forceImage h j forceX := by
    have := mem_forceImage_slot h j forceX 1
    rwa [fiveWit, fiveTuple_one] at this
  have hY : forceY ∈ forceImage h j forceX := by
    have := mem_forceImage_slot h j forceX 2
    rwa [fiveWit, fiveTuple_two] at this
  have hU : forceU ∈ forceImage h j forceX := by
    have := mem_forceImage_slot h j forceX (sqHandleIdxU j)
    rwa [fiveWit, fiveTuple_handleU] at this
  have hS : fiveSigMark gr3R ∈ forceImage h j forceX := by
    have hmul := (forceImage h j forceX).mul_mem hzero ((forceImage h j forceX).inv_mem hX)
    rwa [mul_inv_cancel_right] at hmul
  exact commP_mem_commutator (commP_mem_commutator hS hU) hY

/-- ⚠⚠ **…and it kills the `a0 = a1`-dressed frame outright**, at every handle count and every
handle: its increment is `5 * x_{56} - 6 * x_{12} = 5 - 12 = 1`, and `7 + 1 = 0`. -/
theorem fiveWit_gaThree_kill (h : ℕ) (j : Fin h) :
    sqRelWord (fiveLift j (fiveWit h j forceX)
      (commP (commP (fiveSigMark gr3R) forceU) forceY) 1 1 1 1) = 1 := by
  have hz : (commP (commP (fiveSigMark gr3R) forceU) forceY).IsGaFour := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  rw [sqRelWord_fiveLift hz SqU6.isGaFive_one SqU6.isGaFive_one SqU6.isGaFour_one
    SqU6.isGaFour_one, sqRelWord_fiveWit_diag, liftC6_mul_liftC6]
  refine Eq.trans (congrArg liftC6 ?_) liftC6_zero
  simp only [fiveWit, fiveTuple_one, SqU6.one_m, SqU6.one_n, SqU6.one_o]
  ring_nf
  decide

/-- ⚠⚠ **…while being outside the achievable `gamma_4`-lattice**, which is exactly why the
forcing does not exclude it: its class-four coordinate is `5`. -/
theorem fiveWit_gaThree_kill_not_gaFour :
    commP (commP (fiveSigMark gr3R) forceU) forceY ∉ forceN4 := by
  intro hc
  obtain ⟨⟨t, ht⟩, -⟩ := forceN4_even hc
  rw [show (commP (commP (fiveSigMark gr3R) forceU) forceY).m = 5 from by decide] at ht
  exact absurd ht (by revert t; decide)

end Forcing

/-! ## 7 Cross-checks -/

section CrossChecks

/-- **Independent check of the two verdicts.**  The relators of both dressings at `h = 1`,
taken straight from `sqRelWord` by kernel computation, without going through
`sqRelWord_fiveTuple` or any of section 3's algebra.  Wave 57's process finding was that two
results of one wave can each be right while their composition is vacuous, so the structural
route and the machine route are made to meet here. -/
theorem fiveWit_decide_crosscheck :
    sqRelWord (fiveWit 1 0 1) = 1 ∧ sqRelWord (fiveWit 1 0 forceX) = liftC6 7 := by decide

/-- ⭐ **The class-four reading of the very same dressing is even**, by the committed
class-four theorem `GradedSigmaFive.sigFourRead_diag_even` applied through `toU5L`.  So the
two levels agree: class four cannot see the dressing, class five excludes it. -/
theorem fiveWit_class_four_reading_even :
    selPar (sigFourRead (SqU6.toU5L forceX) (SqU6.toU5L forceX) (SqU6.toU5L forceY)) = 0 := by
  obtain ⟨k, hk⟩ := sigFourRead_diag_even (x := SqU6.toU5L forceX) (y := SqU6.toU5L forceY)
    (ya := 0) (yc := 0) (yd := 0) (by decide) (by decide) (by decide)
  rw [hk, selPar_two_mul]

/-- ⭐ **Wave 58's measured closed form, checked at the point.**  The class-five response of the
`a0 = a1` dressing was measured to be `x_{12} y_{24} y_{46} + x_{56} y_{13} y_{35}` (mod 2) at
every relator-killing marking; here it evaluates to the residue's own parity, `1`.  The two
terms are `2 * 0 * 1` and `1 * 1 * 3`: the escape runs entirely on the second channel, the one
carried by the `x0`-slot's fifth abelian column. -/
theorem fiveWit_w58_form_crosscheck (h : ℕ) (j : Fin h) :
    selPar (forceX.a * forceY.g * forceY.i + forceX.e * forceY.f * forceY.h)
      = selPar (sqRelWord (fiveWit h j forceX)).o := by
  rw [sqRelWord_fiveWit_diag, liftC6_o]
  decide

/-- ⭐ **The class-five form of `GradedFourCleared`'s third headline: a live handle block
cannot break the soundness either.**  The block lies in `N_2`, so every dressing it generates
two steps down is even where the bit reads it; nothing about the point's soundness has to be
re-argued for the live block. -/
theorem forceUV_block_mem_forceN2 : commP forceU forceV ∈ forceN2 := by
  rw [mem_forceN2]
  exact ⟨by decide, by decide, by decide, by decide, by decide, ⟨0, by decide⟩,
    ⟨1, by decide⟩⟩

/-- ⭐ **The handle block is invisible to the bit and indispensable to the point.**  Its `(4,6)`
coordinate, which is what the class-five coupling term reads (wave 58 section 4.2), is **even**
here, so the block contributes nothing to the parity; its class-four coordinate is **odd**,
which is what a dead block cannot supply. -/
theorem forceUV_block_reading :
    selPar (commP forceU forceV).i = 0 ∧ selPar (commP forceU forceV).m = 1 := by decide

end CrossChecks

/-! ## 8 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every `decide` is
on `ZMod 8` or on `Fin`-indexed tuples over it; there is no `native_decide`. -/

section AxiomPins

#print axioms SqU6.IsGaFour
#print axioms SqU6.IsGaFive
#print axioms SqU6.IsGaFive.isGaFour
#print axioms SqU6.isGaFour_one
#print axioms SqU6.isGaFive_one
#print axioms liftC6
#print axioms liftC6_zero
#print axioms liftC6_o
#print axioms liftC6_isGaFive
#print axioms liftC6_mul_liftC6
#print axioms liftC6_inv
#print axioms liftC6_comm
#print axioms mul_liftC6_apply
#print axioms SqU6.IsGaFive.eq_liftC6
#print axioms conjP_liftC6
#print axioms mul_liftC6_mul
#print axioms commP_mul_liftC6_left
#print axioms commP_mul_liftC6_right
#print axioms conjP_mul_left
#print axioms conjP_mul_right_six
#print axioms sqWord_mul_liftC6
#print axioms conjP_of_gaFour
#print axioms sqWord_mul_gaFour_sigma
#print axioms commP_mul_gaFour
#print axioms handleWord_mul_gaFour
#print axioms fiveLift
#print axioms fiveLift_zero
#print axioms fiveLift_one
#print axioms fiveLift_two
#print axioms fiveLift_handleU
#print axioms fiveLift_handleV
#print axioms sqRelWord_fiveLift
#print axioms fiveSigMark
#print axioms toU5L_fiveSigMark
#print axioms forceU
#print axioms forceV
#print axioms forceX
#print axioms forceY
#print axioms fiveWit
#print axioms sqRelWord_fiveWit_triv
#print axioms sqRelWord_fiveWit_diag
#print axioms commP_forceUV_live
#print axioms forceX_gauge
#print axioms fiveWit_class_four_blind
#print axioms fiveWit_diag_class_four_rows
#print axioms commutatorElement_eq_commP
#print axioms forceN1
#print axioms forceN2
#print axioms forceN3
#print axioms forceN4
#print axioms mem_forceN1
#print axioms mem_forceN2
#print axioms mem_forceN3
#print axioms mem_forceN4
#print axioms forceN4_isGaFour
#print axioms forceN4_even
#print axioms forceN2_of_commutator
#print axioms forceN3_of_commutator
#print axioms forceN4_of_commutator
#print axioms forceLcs
#print axioms forceLcs_three_le_forceN4
#print axioms forceImage
#print axioms forceImage_le_forceN1
#print axioms fiveWit_sigma_forced
#print axioms sqRelWord_fiveWit_diag_ne_one
#print axioms fiveWit_bit_separates
#print axioms fiveWit_unrestricted_kill
#print axioms fiveWit_unrestricted_not_achievable
#print axioms mem_forceImage_slot
#print axioms fiveWit_gaThree_kill_mem
#print axioms fiveWit_gaThree_kill
#print axioms fiveWit_gaThree_kill_not_gaFour
#print axioms fiveWit_decide_crosscheck
#print axioms fiveWit_class_four_reading_even
#print axioms fiveWit_w58_form_crosscheck
#print axioms forceUV_block_mem_forceN2
#print axioms forceUV_block_reading

end AxiomPins

end SqCore

end Dyadic

end GQ2
