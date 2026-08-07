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

/-! ## §3 The closed forms

The class-three transcription of `GradedTwo` §6's `fHom_b`, `fHom_sqPivot`, `fHom_sqEichU`,
`fHom_sqEichV`.  Everything is one `SqU4.zpowZtwo_of_flat` away from the class-two proofs; the
three flatness conditions of the `ν'`-column generator `⟨0,1,0,0,0,0⟩` all hold. -/

/-- The projection of the class-three test group onto its `b`-column, used to compare two test
homs through their `ν'`-columns alone. -/
private def bProj3 : ContinuousMonoidHom (SqU4 gr3R) (SqU4 gr3R) where
  toFun p := ⟨0, p.b, 0, 0, 0, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp
  continuous_toFun := continuous_of_discreteTopology

/-- The `ν'`-column generator is flat, so `ℤ₂`-powers of it are linear. -/
private theorem zpow_nuCol (u : ℤ_[2]) :
    zpowZtwo isProP_two_gr3 (⟨0, 1, 0, 0, 0, 0⟩ : SqU4 gr3R) u = ⟨0, gr3Pi u, 0, 0, 0, 0⟩ := by
  rw [SqU4.zpowZtwo_of_flat isProP_two_gr3 gr3Pi gr3Pi_open (by norm_num) (by norm_num)
    (by norm_num)]
  ext <;> simp

/-- ⭐ **The `b`-column of the selection hom is `ν'`.**  So every dressing in `ker ν'` has
`b`-coordinate `0` in the test group — the fact the whole selection argument turns on. -/
private theorem selHom_b (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hcl : ∀ j' : Fin h, j' ≠ j → nu' (sqGen h (sqHandleIdxU j')) = 1 ∧
      nu' (sqGen h (sqHandleIdxV j')) = 1) (x : (DSq h : Type)) :
    (selHom h nu' j A B C D P Q hd he x).b = gr3Pi (toAdd (nu' x)) := by
  have hcomp : bProj3.comp (selHom h nu' j A B C D P Q hd he)
      = bProj3.comp ((zpowZtwoHom isProP_two_gr3 (⟨0, 1, 0, 0, 0, 0⟩ : SqU4 gr3R)).comp nu') := by
    refine dsq_hom_ext _ _ fun i => ?_
    show bProj3 (selHom h nu' j A B C D P Q hd he (sqGen h i))
      = bProj3 (zpowZtwoHom isProP_two_gr3 (⟨0, 1, 0, 0, 0, 0⟩ : SqU4 gr3R) (nu' (sqGen h i)))
    rw [selHom_gen,
      show zpowZtwoHom isProP_two_gr3 (⟨0, 1, 0, 0, 0, 0⟩ : SqU4 gr3R) (nu' (sqGen h i))
        = zpowZtwo isProP_two_gr3 (⟨0, 1, 0, 0, 0, 0⟩ : SqU4 gr3R)
            (toAdd (nu' (sqGen h i))) from rfl, zpow_nuCol]
    show (⟨0, (selMark h nu' j A B C D P Q i).b, 0, 0, 0, 0⟩ : SqU4 gr3R)
      = ⟨0, gr3Pi (toAdd (nu' (sqGen h i))), 0, 0, 0, 0⟩
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
    · rw [show (sqGen h 0 : (DSq h : Type)) = dsqSigma h from rfl, hsigma, selMark_zero]
      simp
    · rw [show (sqGen h 1 : (DSq h : Type)) = dsqX0 h from rfl, hx0, selMark_one]
      simp
    · rw [show (sqGen h 2 : (DSq h : Type)) = dsqX1 h from rfl, toAdd_nu_dsqX1 nu', hx0,
        selMark_two]
      simp
    · by_cases hjj : j' = j
      · subst hjj; rw [selMark_handleU]
      · rw [selMark_handleU_ne hjj, (hcl j' hjj).1]
        simp
    · by_cases hjj : j' = j
      · subst hjj; rw [selMark_handleV]
      · rw [selMark_handleV_ne hjj, (hcl j' hjj).2]
        simp
  have hx := DFunLike.congr_fun hcomp x
  have hxb : (⟨0, (selHom h nu' j A B C D P Q hd he x).b, 0, 0, 0, 0⟩ : SqU4 gr3R)
      = ⟨0, (zpowZtwo isProP_two_gr3 (⟨0, 1, 0, 0, 0, 0⟩ : SqU4 gr3R) (toAdd (nu' x))).b,
          0, 0, 0, 0⟩ := hx
  rw [zpow_nuCol] at hxb
  have := congrArg SqU4.b hxb
  simpa using this

/-- The pivot lands on the pure `ν'`-column generator, at **every** exponent `c₀`. -/
private theorem selHom_sqPivot :
    selHom h nu' j A B C D P Q hd he (sqPivot h) = ⟨0, 1, 0, 0, 0, 0⟩ := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_gr3, dsqX0, selHom_gen, selMark_one,
    zpowZtwo_one_base, inv_one, mul_one, dsqSigma, selHom_gen, selMark_zero]

/-- ⭐ **The cleared `U` in the class-three test group.**  Its `ν'`-column is gone, its two free
columns survive, and it acquires a class-two `(2,4)`-coordinate `−ν'(u_j)·C`. -/
private theorem selHom_sqEichU :
    selHom h nu' j A B C D P Q hd he (sqEichU h nu' j)
      = ⟨A, 0, C, 0, -(selT h nu' j * C), 0⟩ := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr3, selHom_sqPivot,
    zpow_nuCol, selHom_gen, selMark_handleU]
  ext <;> simp

/-- ⭐ …and the cleared `V`, which acquires a `(1,3)`-coordinate `−B·ν'(v_j)`. -/
private theorem selHom_sqEichV :
    selHom h nu' j A B C D P Q hd he (sqEichV h nu' j)
      = ⟨B, 0, D, -(B * selS h nu' j), 0, 0⟩ := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr3, selHom_sqPivot,
    zpow_nuCol, selHom_gen, selMark_handleV]
  ext <;> simp

end Marking

end SqCore

end Dyadic

end GQ2
