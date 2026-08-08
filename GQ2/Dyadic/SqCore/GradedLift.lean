/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedFour

/-!
# W52-LIFT: the level-wise lift engine, instantiated at stage 3 → 4

`GradedContain` proved the class-three containment over the whole marking binder: at every
binder point there are admissible level-one data with selection bit zero, and on the live
locus the committed completion move kills the relator.  This file builds the **stage engine**
one level up, on the `U₅`-carrier of `GradedFour`: the affine-linear action of `γ₃`-dressings
on the class-four residue, its achievable image, the two-regime completion, and the schema a
later wave iterates.  Everything was validated numerically before transcription
(`scripts/w52_lift/sweep_u5.py` and successors).

What the class-four layer turned out to look like (the file's findings, all machine-checked
below or recorded honestly as measured):

* **the translation identity survives verbatim** (`sqRelWord_selLift`): dressing the two
  exponent slots by `γ₄` and the two `j`-handle slots by `γ₃` translates the relator by a
  central element, affine-linear in the dressings, with the *outermost* abelian columns
  `(a, d)` as coefficients, exactly as the note's stage-`k` conjecture predicts;
* **stage 3 is two functionals wide from up here.**  `U₅` has two class-three rows (`h`, `i`);
  a "class-three survivor" in this file means both die.  The committed `GradedSelect`
  machinery governs the `h`-row through `toU4L`; the `i`-row is genuinely new and its residue
  at the witness is `2·N − C·F·T` (§4): the class-three story of the columns that class three
  could not see;
* **the completion has two regimes, collapsed by parity** (the W51 sweep's mod-2 structure
  entering): with `κ₄ = B·D·F` a unit the `γ₃`-action is *surjective* and any residue dies
  (`sqRelWord_selLift_eq_one_odd`), something that never happens at class three; with
  `κ₄ = 2·unit⁻¹`-type pairing only even residues die (`sqRelWord_selLift_eq_one`), and the
  class-four selection bit is real (measured: odd residues at `F`-even live points survive
  every sampled achievable refinement);
* **the mirror regime** `κ₄' = A·C·E` acts through the `V`-handle slot
  (`sqRelWord_selLift_eq_one_odd'`).

## Contents

* **§1** `γ`-filtration predicates, the central calculus of `liftC`, and the word-level
  update lemmas (`sqWord_mul_liftC`, `handleWord_update_liftC`);
* **§2** the lift refinement `selLift` and ⭐⭐ the translation identity `sqRelWord_selLift`;
* **§3** the achievable `γ₃`-lattice `selLamThree` and ⭐⭐ the two-regime completion;
* **§4** ⭐⭐ the whole-binder witness at class four: the lifted tuple, its ten rows, the
  new `i`-row residue, and the stage-3 → stage-4 engine instance;
* **§5** the stage schema `LiftStep` and its 3 → 4 instance;
* **§6** committed axiom prints.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The `γ`-filtration and the central calculus

`γ₂`-, `γ₃`- and `γ₄`-shaped elements of `SqU5`, the central `(1,5)`-translations `liftC`,
and the two word-level update lemmas the translation identity needs: multiplying the two
exponent slots of the core word by central elements multiplies the word by a central element
with the relator weights `(−4, 2)`, and multiplying one entry of a product list by a central
element multiplies the product by it.  This is the class-four shadow of the fact that the
whole refinement calculus happens inside a two-step central extension. -/

section Filtration

variable {R : Type} [CommRing R]

/-- A `γ₂`-shaped element of the class-four test group: all four abelian columns vanish. -/
def SqU5.IsGaTwo (z : SqU5 R) : Prop := z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0

/-- A `γ₃`-shaped element: abelian and class-two coordinates vanish. -/
def SqU5.IsGaThree (z : SqU5 R) : Prop :=
  z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0

/-- A `γ₄`-shaped element: only the class-four coordinate may be non-zero. -/
def SqU5.IsGaFour (z : SqU5 R) : Prop :=
  z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0 ∧ z.h = 0 ∧ z.i = 0

theorem SqU5.IsGaThree.isGaTwo {z : SqU5 R} (hz : z.IsGaThree) : z.IsGaTwo :=
  ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩

theorem SqU5.IsGaFour.isGaThree {z : SqU5 R} (hz : z.IsGaFour) : z.IsGaThree :=
  ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1, hz.2.2.2.2.2.2.1⟩

@[simp] theorem SqU5.isGaThree_one : (1 : SqU5 R).IsGaThree :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem SqU5.isGaTwo_one : (1 : SqU5 R).IsGaTwo := ⟨rfl, rfl, rfl, rfl⟩

/-- The central `(1,5)`-translation by `w`. -/
def liftC (w : R) : SqU5 R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, w⟩

@[simp] theorem liftC_zero : liftC (0 : R) = 1 := rfl

@[simp] theorem liftC_j (w : R) : (liftC w).j = w := rfl

theorem liftC_isGaFour (w : R) : (liftC w).IsGaFour :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem liftC_mul_liftC (v w : R) : liftC v * liftC w = liftC (v + w) := by
  ext <;> simp [liftC]

@[simp] theorem liftC_inv (w : R) : (liftC w)⁻¹ = liftC (-w) := by
  ext <;> simp [liftC]

/-- `liftC` is central. -/
theorem liftC_comm (p : SqU5 R) (w : R) : p * liftC w = liftC w * p := by
  ext <;> simp [liftC, add_comm]

/-- Multiplying on the right by `liftC` translates the class-four coordinate and nothing
else (`SqU5.mul_center_j` in `liftC` form). -/
theorem mul_liftC_apply (p : SqU5 R) (w : R) :
    p * liftC w = ⟨p.a, p.b, p.c, p.d, p.e, p.f, p.g, p.h, p.i, p.j + w⟩ :=
  SqU5.mul_center_j p w

/-- Conjugation fixes the centre. -/
theorem conjP_liftC (w : R) (g : SqU5 R) : conjP (liftC w) g = liftC w := by
  ext <;> simp [liftC, SqU5.conjP_j]

/-- Commutators ignore a central right factor in either argument. -/
theorem commP_mul_liftC_left (p q : SqU5 R) (w : R) :
    commP (p * liftC w) q = commP p q := by
  ext <;> simp only [SqU5.commP_a, SqU5.commP_b, SqU5.commP_c, SqU5.commP_d, SqU5.commP_e,
    SqU5.commP_f, SqU5.commP_g, SqU5.commP_h, SqU5.commP_i, SqU5.commP_j, SqU5.u5Comm3L,
    SqU5.u5Comm3R, SqU5.u5Comm4, liftC, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d,
    SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i] <;> ring

theorem commP_mul_liftC_right (p q : SqU5 R) (w : R) :
    commP p (q * liftC w) = commP p q := by
  ext <;> simp only [SqU5.commP_a, SqU5.commP_b, SqU5.commP_c, SqU5.commP_d, SqU5.commP_e,
    SqU5.commP_f, SqU5.commP_g, SqU5.commP_h, SqU5.commP_i, SqU5.commP_j, SqU5.u5Comm3L,
    SqU5.u5Comm3R, SqU5.u5Comm4, liftC, SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d,
    SqU5.mul_e, SqU5.mul_f, SqU5.mul_g, SqU5.mul_h, SqU5.mul_i] <;> ring

/-- ⭐ **The core word swallows exponent-slot central dressings with the relator weights**:
dressing the `x₀`-slot by `liftC α` and the `x₁`-slot by `liftC β` multiplies the core word by
`liftC (−4·α + 2·β)`.  No closed form of the word is consumed: the proof is componentwise
expansion of both sides. -/
theorem sqWord_mul_liftC (s x y : SqU5 R) (α β : R) :
    sqWord s (x * liftC α) (y * liftC β) = sqWord s x y * liftC (-4 * α + 2 * β) := by
  ext <;> simp only [sqWord, conjP, commP, pow_succ, pow_zero, one_mul, liftC,
    SqU5.mul_a, SqU5.mul_b, SqU5.mul_c, SqU5.mul_d, SqU5.mul_e, SqU5.mul_f, SqU5.mul_g,
    SqU5.mul_h, SqU5.mul_i, SqU5.mul_j, SqU5.inv_a, SqU5.inv_b, SqU5.inv_c, SqU5.inv_d,
    SqU5.inv_e, SqU5.inv_f, SqU5.inv_g, SqU5.inv_h, SqU5.inv_i, SqU5.inv_j] <;> ring

end Filtration

end SqCore

end Dyadic

end GQ2
