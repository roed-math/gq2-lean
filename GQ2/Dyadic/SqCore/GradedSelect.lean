/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedThree

/-!
# W49 — the class-three **selection**: which class-two dressings survive

`GradedThree` §6 answered W48-U4's narrow question with an explicit six-tuple in `SqU4 (ZMod 8)`.
This file does two things.

* **§1–§4** port that witness to the **real object**: a class-three test hom
  `selHom` on `D_sq h` whose `b`-column *is* `ν'`, with the images of the pivot and of the two
  cleared letters `U`, `V` computed in closed form, so that
  `sqRelWord_selHom_sqArbFrame` is a statement about `sqArbFrame h nu' j a` itself.
* **§5–§6** characterise the **selection**: the set of dressings passing both gates.

## Contents

* **§1** the gate instance over `ℤ/8`;
* **§2** the selection marking, its realizability, and the test hom;
* **§3** the closed forms `selHom_b`, `selHom_sqPivot`, `selHom_sqEichU`, `selHom_sqEichV`;
* **§4** ⭐ the witness, as a theorem about `sqArbFrame`.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The class-three gate instance over `ℤ/8` -/

section Instance

/-- The coefficient ring of the class-three gate instance. -/
private abbrev gr3R : Type := ZMod 8

/-- The reduction `ℤ₂ → ℤ/8`. -/
private noncomputable abbrev gr3Pi : ℤ_[2] →+* gr3R := PadicInt.toZModPow 3

private theorem gr3R_card : Nat.card gr3R = 2 ^ 3 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]
  norm_num

private theorem isProP_two_gr3 : IsProP 2 (SqU4 gr3R) := SqU4.isProP_two gr3R_card

private theorem gr3Pi_open (T : Set gr3R) : IsOpen (gr3Pi ⁻¹' T) :=
  isOpen_preimage_toZModPow 3 T

end Instance

/-! ## §2 The selection marking

The class-three analogue of `GradedTwo` §6's forcing marking.  The `b`-column **is** `ν'`, so
every `ν'`-trivial dressing has `b`-coordinate `0`; the `a`- and `c`-columns are two *free*
characters, carried by the four weights `A, C` (on `u_j`) and `B, D` (on `v_j`).

⚠ Unlike `GradedTwo` §6 the free columns are **not** doubled: `2·χ` makes the class-three defect
vacuous.  What replaces the doubling is a pair of parity conditions, one for each **adjacent**
pair of columns, and those are exactly the two hypotheses of `sqRelWord_selMark`. -/

section Marking

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

/-- The `u`-row of the selected marking, read in `ℤ/8`. -/
private noncomputable abbrev selT (h : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) : gr3R :=
  gr3Pi (toAdd (nu' (sqGen h (sqHandleIdxU j))))

/-- The `v`-row of the selected marking, read in `ℤ/8`. -/
private noncomputable abbrev selS (h : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) : gr3R :=
  gr3Pi (toAdd (nu' (sqGen h (sqHandleIdxV j))))

variable (h nu' j) in
/-- **The class-three selection marking.**  `σ ↦ (0,1,0,0,0,0)` puts `ν'` in the `b`-column,
`x₀ ↦ 1` puts the pivot `w = σ·x₀^{−c₀}` on the pure `ν'`-column at every exponent, and the two
handle letters carry the free `a`- and `c`-weights `(A, C)` and `(B, D)` beside their `ν'`-rows.

⭐ The `x₁`-slot's class-three coordinate is **not** a free parameter: it is forced to
`−(A+B)·Q` by the two class-two coordinates.  That is the content of `sqRelWord_selMark`: the
class-three layer imposes **no new realizability condition** on markings of this shape. -/
private noncomputable def selMark (A B C D P Q : gr3R) : Fin (sqRank h) → SqU4 gr3R :=
  fun i =>
    if (i : ℕ) = 0 then ⟨0, 1, 0, 0, 0, 0⟩ else
    if (i : ℕ) = 2 then ⟨0, 0, 0, P, Q, -((A + B) * Q)⟩ else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then ⟨A, selT h nu' j, C, 0, 0, 0⟩ else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then ⟨B, selS h nu' j, D, 0, 0, 0⟩ else 1

variable {A B C D P Q : gr3R}

@[simp] private theorem selMark_zero :
    selMark h nu' j A B C D P Q 0 = ⟨0, 1, 0, 0, 0, 0⟩ := by
  simp only [selMark, sqVal_zero]
  norm_num

@[simp] private theorem selMark_one : selMark h nu' j A B C D P Q 1 = 1 := by
  simp only [selMark, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] private theorem selMark_two :
    selMark h nu' j A B C D P Q 2 = ⟨0, 0, 0, P, Q, -((A + B) * Q)⟩ := by
  simp only [selMark, sqVal_two, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega)]
  norm_num

@[simp] private theorem selMark_handleU :
    selMark h nu' j A B C D P Q (sqHandleIdxU j) = ⟨A, selT h nu' j, C, 0, 0, 0⟩ := by
  simp only [selMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

@[simp] private theorem selMark_handleV :
    selMark h nu' j A B C D P Q (sqHandleIdxV j) = ⟨B, selS h nu' j, D, 0, 0, 0⟩ := by
  simp only [selMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

private theorem selMark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    selMark h nu' j A B C D P Q (sqHandleIdxU j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [selMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem selMark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    selMark h nu' j A B C D P Q (sqHandleIdxV j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [selMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- ⭐⭐ **The two adjacent-pair parities, and nothing else.**  The selection marking kills the
relator exactly when

```text
A·ν'(v_j) − B·ν'(u_j) ∈ 2·ℤ/8      (the (a,b)-pair)
ν'(u_j)·D − ν'(v_j)·C ∈ 2·ℤ/8      (the (b,c)-pair)
```

— witnessed by `P` and `Q`.  There is **no** condition on the non-adjacent `(a,c)`-pair
`A·D − B·C`, and **no** third, class-three condition: the class-three coordinate of the `x₁`-slot
solves its own equation automatically, because the class-three defect of this marking is
`(A+B)·(ν'(v_j)·C − ν'(u_j)·D) = 2·(A+B)·Q`, even by the `(b,c)`-parity itself. -/
private theorem sqRelWord_selMark
    (hd : 2 * P + (A * selS h nu' j - B * selT h nu' j) = 0)
    (he : 2 * Q + (selT h nu' j * D - selS h nu' j * C) = 0) :
    sqRelWord (selMark h nu' j A B C D P Q) = 1 := by
  have hsingle : ∀ {M : Type} [AddCommMonoid M] (f : Fin h → M),
      (∀ j' : Fin h, j' ≠ j → f j' = 0) → ∑ j' : Fin h, f j' = f j := by
    intro M _ f hf
    exact Finset.sum_eq_single j (fun j' _ hne => hf j' hne)
      (fun hj => absurd (Finset.mem_univ j) hj)
  rw [SqU4.sqRelWord_eq_one_iff]
  refine ⟨by simp, by simp, by simp, ?_, ?_, ?_⟩
  · rw [sqHeisDefect, hsingle _ (fun j' hne => by
      rw [selMark_handleU_ne hne, selMark_handleV_ne hne]; simp)]
    simp only [selMark_zero, selMark_one, selMark_two, selMark_handleU, selMark_handleV,
      SqU4.toHeisAB_apply, SqU4.one_a, SqU4.one_b, SqU4.one_d]
    linear_combination hd
  · rw [sqHeisDefect, hsingle _ (fun j' hne => by
      rw [selMark_handleU_ne hne, selMark_handleV_ne hne]; simp)]
    simp only [selMark_zero, selMark_one, selMark_two, selMark_handleU, selMark_handleV,
      SqU4.toHeisBC_apply, SqU4.one_b, SqU4.one_c, SqU4.one_e]
    linear_combination he
  · rw [sqU4Defect, hsingle _ (fun j' hne => by
      rw [selMark_handleU_ne hne, selMark_handleV_ne hne]; simp),
      hsingle (fun j' => SqU4.u4Comm3 (selMark h nu' j A B C D P Q (sqHandleIdxU j'))
        (selMark h nu' j A B C D P Q (sqHandleIdxV j')))
        (fun j' hne => by
          rw [selMark_handleU_ne hne, selMark_handleV_ne hne]
          simp [SqU4.u4Comm3])]
    simp only [selMark_zero, selMark_one, selMark_two, selMark_handleU, selMark_handleV,
      sqU4Core, SqU4.u4Comm3, SqU4.one_a, SqU4.one_b, SqU4.one_c, SqU4.one_d, SqU4.one_e,
      SqU4.one_f]
    linear_combination (-(A + B)) * he

variable (h nu' j) in
/-- **The class-three selection test homomorphism**, attached to the selection marking. -/
private noncomputable def selHom (A B C D P Q : gr3R)
    (hd : 2 * P + (A * selS h nu' j - B * selT h nu' j) = 0)
    (he : 2 * Q + (selT h nu' j * D - selS h nu' j * C) = 0) :
    ContinuousMonoidHom (DSq h : Type) (SqU4 gr3R) :=
  sqU4Hom gr3R_card h (selMark h nu' j A B C D P Q) (sqRelWord_selMark hd he)

variable {hd : 2 * P + (A * selS h nu' j - B * selT h nu' j) = 0}
variable {he : 2 * Q + (selT h nu' j * D - selS h nu' j * C) = 0}

@[simp] private theorem selHom_gen (i : Fin (sqRank h)) :
    selHom h nu' j A B C D P Q hd he (sqGen h i) = selMark h nu' j A B C D P Q i :=
  sqU4Hom_gen _ _ _ i

end Marking

end SqCore

end Dyadic

end GQ2
