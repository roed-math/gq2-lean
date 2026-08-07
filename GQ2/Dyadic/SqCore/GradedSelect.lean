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
abbrev gr3R : Type := ZMod 8

/-- The reduction `ℤ₂ → ℤ/8`. -/
noncomputable abbrev gr3Pi : ℤ_[2] →+* gr3R := PadicInt.toZModPow 3

theorem gr3R_card : Nat.card gr3R = 2 ^ 3 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]
  norm_num

theorem isProP_two_gr3 : IsProP 2 (SqU4 gr3R) := SqU4.isProP_two gr3R_card

theorem gr3Pi_open (T : Set gr3R) : IsOpen (gr3Pi ⁻¹' T) :=
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
noncomputable abbrev selT (h : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) : gr3R :=
  gr3Pi (toAdd (nu' (sqGen h (sqHandleIdxU j))))

/-- The `v`-row of the selected marking, read in `ℤ/8`. -/
noncomputable abbrev selS (h : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) : gr3R :=
  gr3Pi (toAdd (nu' (sqGen h (sqHandleIdxV j))))

variable (h nu' j) in
/-- **The class-three selection marking.**  `σ ↦ (0,1,0,0,0,0)` puts `ν'` in the `b`-column,
`x₀ ↦ 1` puts the pivot `w = σ·x₀^{−c₀}` on the pure `ν'`-column at every exponent, and the two
handle letters carry the free `a`- and `c`-weights `(A, C)` and `(B, D)` beside their `ν'`-rows.

⭐ The `x₁`-slot's class-three coordinate is **not** a free parameter: it is forced to
`−(A+B)·Q` by the two class-two coordinates.  That is the content of `sqRelWord_selMark`: the
class-three layer imposes **no new realizability condition** on markings of this shape. -/
noncomputable def selMark (A B C D P Q : gr3R) : Fin (sqRank h) → SqU4 gr3R :=
  fun i =>
    if (i : ℕ) = 0 then ⟨0, 1, 0, 0, 0, 0⟩ else
    if (i : ℕ) = 2 then ⟨0, 0, 0, P, Q, -((A + B) * Q)⟩ else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then ⟨A, selT h nu' j, C, 0, 0, 0⟩ else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then ⟨B, selS h nu' j, D, 0, 0, 0⟩ else 1

variable {A B C D P Q : gr3R}

@[simp] theorem selMark_zero :
    selMark h nu' j A B C D P Q 0 = ⟨0, 1, 0, 0, 0, 0⟩ := by
  simp only [selMark, sqVal_zero]
  norm_num

@[simp] theorem selMark_one : selMark h nu' j A B C D P Q 1 = 1 := by
  simp only [selMark, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] theorem selMark_two :
    selMark h nu' j A B C D P Q 2 = ⟨0, 0, 0, P, Q, -((A + B) * Q)⟩ := by
  simp only [selMark, sqVal_two, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega)]
  norm_num

@[simp] theorem selMark_handleU :
    selMark h nu' j A B C D P Q (sqHandleIdxU j) = ⟨A, selT h nu' j, C, 0, 0, 0⟩ := by
  simp only [selMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

@[simp] theorem selMark_handleV :
    selMark h nu' j A B C D P Q (sqHandleIdxV j) = ⟨B, selS h nu' j, D, 0, 0, 0⟩ := by
  simp only [selMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

theorem selMark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    selMark h nu' j A B C D P Q (sqHandleIdxU j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [selMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem selMark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
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
theorem sqRelWord_selMark
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
noncomputable def selHom (A B C D P Q : gr3R)
    (hd : 2 * P + (A * selS h nu' j - B * selT h nu' j) = 0)
    (he : 2 * Q + (selT h nu' j * D - selS h nu' j * C) = 0) :
    ContinuousMonoidHom (DSq h : Type) (SqU4 gr3R) :=
  sqU4Hom gr3R_card h (selMark h nu' j A B C D P Q) (sqRelWord_selMark hd he)

variable {hd : 2 * P + (A * selS h nu' j - B * selT h nu' j) = 0}
variable {he : 2 * Q + (selT h nu' j * D - selS h nu' j * C) = 0}

@[simp] theorem selHom_gen (i : Fin (sqRank h)) :
    selHom h nu' j A B C D P Q hd he (sqGen h i) = selMark h nu' j A B C D P Q i :=
  sqU4Hom_gen _ _ _ i

/-! ## §3 The closed forms

The class-three transcription of `GradedTwo` §6's `fHom_b`, `fHom_sqPivot`, `fHom_sqEichU`,
`fHom_sqEichV`.  Everything is one `SqU4.zpowZtwo_of_flat` away from the class-two proofs; the
three flatness conditions of the `ν'`-column generator `⟨0,1,0,0,0,0⟩` all hold. -/

/-- The projection of the class-three test group onto its `b`-column, used to compare two test
homs through their `ν'`-columns alone. -/
def bProj3 : ContinuousMonoidHom (SqU4 gr3R) (SqU4 gr3R) where
  toFun p := ⟨0, p.b, 0, 0, 0, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp
  continuous_toFun := continuous_of_discreteTopology

/-- The `ν'`-column generator is flat, so `ℤ₂`-powers of it are linear. -/
theorem zpow_nuCol (u : ℤ_[2]) :
    zpowZtwo isProP_two_gr3 (⟨0, 1, 0, 0, 0, 0⟩ : SqU4 gr3R) u = ⟨0, gr3Pi u, 0, 0, 0, 0⟩ := by
  rw [SqU4.zpowZtwo_of_flat isProP_two_gr3 gr3Pi gr3Pi_open (by norm_num) (by norm_num)
    (by norm_num)]
  ext <;> simp

/-- ⭐ **The `b`-column of the selection hom is `ν'`.**  So every dressing in `ker ν'` has
`b`-coordinate `0` in the test group — the fact the whole selection argument turns on. -/
theorem selHom_b (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
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
theorem selHom_sqPivot :
    selHom h nu' j A B C D P Q hd he (sqPivot h) = ⟨0, 1, 0, 0, 0, 0⟩ := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_gr3, dsqX0, selHom_gen, selMark_one,
    zpowZtwo_one_base, inv_one, mul_one, dsqSigma, selHom_gen, selMark_zero]

/-- ⭐ **The cleared `U` in the class-three test group.**  Its `ν'`-column is gone, its two free
columns survive, and it acquires a class-two `(2,4)`-coordinate `−ν'(u_j)·C`. -/
theorem selHom_sqEichU :
    selHom h nu' j A B C D P Q hd he (sqEichU h nu' j)
      = ⟨A, 0, C, 0, -(selT h nu' j * C), 0⟩ := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr3, selHom_sqPivot,
    zpow_nuCol, selHom_gen, selMark_handleU]
  ext <;> simp

/-- ⭐ …and the cleared `V`, which acquires a `(1,3)`-coordinate `−B·ν'(v_j)`. -/
theorem selHom_sqEichV :
    selHom h nu' j A B C D P Q hd he (sqEichV h nu' j)
      = ⟨B, 0, D, -(B * selS h nu' j), 0, 0⟩ := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_gr3, selHom_sqPivot,
    zpow_nuCol, selHom_gen, selMark_handleV]
  ext <;> simp

/-! ## §4 ⭐⭐ The witness, as a theorem about `sqArbFrame`

`GradedThree` §6 exhibited a six-tuple in `SqU4 (ZMod 8)` and checked slot by slot that it *is*
the image of the arbitrary-dressing frame.  Here the frame is the subject: `selDress` is a
dressing tuple in `ker λ ∩ ker ν'`, and `sqRelWord_selHom_sqArbFrame` says that the class-three
test hom sends `sqArbFrame h nu' j selDress` to a marking that kills the relator — at **every**
handle count, at **every** handle, and at **every** admissible pair of free characters. -/

/-- The generic collapse of a handle sum whose off-`j` terms vanish. -/
theorem sum_eq_at {M : Type} [AddCommMonoid M] (f : Fin h → M)
    (hf : ∀ j' : Fin h, j' ≠ j → f j' = 0) : ∑ j' : Fin h, f j' = f j :=
  Finset.sum_eq_single j (fun j' _ hne => hf j' hne)
    (fun hj => absurd (Finset.mem_univ j) hj)

variable (h nu' j) in
/-- ⭐ **The witness dressing**: the `x₀`-slot dressed by `U⁻¹`, every other slot left alone.
`Ū⁻¹ = −ν'(v_j)·Ū + ν'(u_j)·V̄` at `ν'(u_j) = 0`, `ν'(v_j) = 1` — exactly the value the class-two
balance forces (`sqArbFrame_x0_dressing_forced`). -/
noncomputable def selDress : Fin (sqRank h) → (DSq h : Type) :=
  fun i => if (i : ℕ) = 1 then (sqEichU h nu' j)⁻¹ else 1

theorem selDress_of_ne {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 1) : selDress h nu' j i = 1 :=
  if_neg hi

@[simp] theorem selDress_one : selDress h nu' j 1 = (sqEichU h nu' j)⁻¹ := by
  simp only [selDress, sqVal_one]
  norm_num

@[simp] theorem selDress_zero : selDress h nu' j 0 = 1 :=
  selDress_of_ne (by rw [sqVal_zero]; omega)

@[simp] theorem selDress_two : selDress h nu' j 2 = 1 :=
  selDress_of_ne (by rw [sqVal_two]; omega)

@[simp] theorem selDress_handleU (j' : Fin h) : selDress h nu' j (sqHandleIdxU j') = 1 :=
  selDress_of_ne (by rw [sqHandleIdxU_val]; omega)

@[simp] theorem selDress_handleV (j' : Fin h) : selDress h nu' j (sqHandleIdxV j') = 1 :=
  selDress_of_ne (by rw [sqHandleIdxV_val]; omega)

/-- ⭐ **The witness dressing is legal on the `λ`-row**: every slot is `λ`-trivial. -/
theorem nuLam_selDress (i : Fin (sqRank h)) : nuLam h (selDress h nu' j i) = 1 := by
  by_cases hi : (i : ℕ) = 1
  · rw [show i = 1 from Fin.val_injective (by rw [hi, sqVal_one]), selDress_one, map_inv,
      inv_eq_one]
    exact Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichU, toAdd_one])
  · rw [selDress_of_ne hi, map_one]

/-- ⭐ …and on the `ν'`-row: every slot is `ν'`-trivial, so the dressing lies in
`ker λ ∩ ker ν'` — the class `SqArbRelWord` quantifies over. -/
theorem nu_selDress (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (i : Fin (sqRank h)) :
    nu' (selDress h nu' j i) = 1 := by
  by_cases hi : (i : ℕ) = 1
  · rw [show i = 1 from Fin.val_injective (by rw [hi, sqVal_one]), selDress_one, map_inv,
      inv_eq_one]
    exact Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichU hsigma hx0, toAdd_one])
  · rw [selDress_of_ne hi, map_one]

/-! ### The five slot images of the dressed frame -/

/-- The `σ`-slot. -/
theorem selHom_sqArbFrame_zero :
    selHom h nu' j A B C D P Q hd he (sqArbFrame h nu' j (selDress h nu' j) 0)
      = ⟨0, 1, 0, 0, 0, 0⟩ := by
  rw [sqArbFrame, sqArbBase_zero, selDress_zero, mul_one, dsqSigma, selHom_gen, selMark_zero]

/-- The `x₁`-slot. -/
theorem selHom_sqArbFrame_two :
    selHom h nu' j A B C D P Q hd he (sqArbFrame h nu' j (selDress h nu' j) 2)
      = ⟨0, 0, 0, P, Q, -((A + B) * Q)⟩ := by
  rw [sqArbFrame, sqArbBase_two, selDress_two, mul_one, dsqX1, selHom_gen, selMark_two]

/-- The untouched handles die. -/
theorem selHom_sqArbFrame_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    selHom h nu' j A B C D P Q hd he
      (sqArbFrame h nu' j (selDress h nu' j) (sqHandleIdxU j')) = 1 := by
  rw [sqArbFrame, sqArbBase_handleU_ne hne, selDress_handleU, mul_one, selHom_gen,
    selMark_handleU_ne hne]

theorem selHom_sqArbFrame_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    selHom h nu' j A B C D P Q hd he
      (sqArbFrame h nu' j (selDress h nu' j) (sqHandleIdxV j')) = 1 := by
  rw [sqArbFrame, sqArbBase_handleV_ne hne, selDress_handleV, mul_one, selHom_gen,
    selMark_handleV_ne hne]

/-- ⭐ The **moved** handle letter `U`, at the canonical uncleared row. -/
theorem selHom_sqEichU_of_cleared (hu : selT h nu' j = 0) :
    selHom h nu' j A B C D P Q hd he (sqEichU h nu' j) = ⟨A, 0, C, 0, 0, 0⟩ := by
  rw [selHom_sqEichU, hu]; ext <;> simp

/-- ⭐ …and `V`. -/
theorem selHom_sqEichV_of_one (hv : selS h nu' j = 1) :
    selHom h nu' j A B C D P Q hd he (sqEichV h nu' j) = ⟨B, 0, D, -B, 0, 0⟩ := by
  rw [selHom_sqEichV, hv]; ext <;> simp

/-- ⭐ **The dressed `x₀`-slot** is the inverse of the `U`-slot: this is the whole dressing. -/
theorem selHom_sqArbFrame_one (hu : selT h nu' j = 0) :
    selHom h nu' j A B C D P Q hd he (sqArbFrame h nu' j (selDress h nu' j) 1)
      = ⟨-A, 0, -C, 0, 0, 0⟩ := by
  rw [sqArbFrame, sqArbBase_one, selDress_one, map_mul, dsqX0, selHom_gen, selMark_one,
    one_mul, map_inv, selHom_sqEichU_of_cleared hu]
  ext <;> simp

theorem selHom_sqArbFrame_handleU (hu : selT h nu' j = 0) :
    selHom h nu' j A B C D P Q hd he
      (sqArbFrame h nu' j (selDress h nu' j) (sqHandleIdxU j)) = ⟨A, 0, C, 0, 0, 0⟩ := by
  rw [sqArbFrame, sqArbBase_handleU, selDress_handleU, mul_one, selHom_sqEichU_of_cleared hu]

theorem selHom_sqArbFrame_handleV (hv : selS h nu' j = 1) :
    selHom h nu' j A B C D P Q hd he
      (sqArbFrame h nu' j (selDress h nu' j) (sqHandleIdxV j)) = ⟨B, 0, D, -B, 0, 0⟩ := by
  rw [sqArbFrame, sqArbBase_handleV, selDress_handleV, mul_one, selHom_sqEichV_of_one hv]

/-- ⭐⭐ **The class-three gate does not obstruct the arbitrary-dressing frame** — now a statement
about `sqArbFrame h nu' j a` itself, not about a tuple in a test group.

At a selected marking whose `j`-th handle is uncleared in the canonical way
(`ν'(u_j) ≡ 0`, `ν'(v_j) ≡ 1` mod `8`), the frame dressed by `selDress` — the class-two forced
value `U⁻¹`, and nothing else — kills the relator in **every** class-three quotient of the
selection family, at every admissible pair `(A, C)`, `(B, D)` of free characters.

⚠ This is a *necessary-condition* verdict: "not obstructed", never "proved".  The gate sees only
finite 2-group quotients, so it would return the same verdict for the discrete group, where
marking-transitivity is false. -/
theorem sqRelWord_selHom_sqArbFrame (hu : selT h nu' j = 0) (hv : selS h nu' j = 1) :
    sqRelWord (fun i => selHom h nu' j A B C D P Q hd he
      (sqArbFrame h nu' j (selDress h nu' j) i)) = 1 := by
  have h8 : (8 : gr3R) = 0 := by decide
  have hd' : 2 * P + A = 0 := by
    have hx := hd; rw [hu, hv] at hx; linear_combination hx
  have he' : 2 * Q - C = 0 := by
    have hx := he; rw [hu, hv] at hx; linear_combination hx
  have hs0 := selHom_sqArbFrame_zero (A := A) (B := B) (C := C) (D := D) (P := P) (Q := Q)
    (hd := hd) (he := he)
  have hs1 := selHom_sqArbFrame_one (B := B) (D := D) (P := P) (Q := Q) (hd := hd) (he := he) hu
  have hs2 := selHom_sqArbFrame_two (A := A) (B := B) (C := C) (D := D) (P := P) (Q := Q)
    (hd := hd) (he := he)
  have hsU := selHom_sqArbFrame_handleU (B := B) (D := D) (P := P) (Q := Q)
    (hd := hd) (he := he) hu
  have hsV := selHom_sqArbFrame_handleV (A := A) (C := C) (P := P) (Q := Q)
    (hd := hd) (he := he) hv
  have hsUne := fun (j' : Fin h) (hne : j' ≠ j) =>
    selHom_sqArbFrame_handleU_ne (A := A) (B := B) (C := C) (D := D) (P := P) (Q := Q)
      (hd := hd) (he := he) hne
  have hsVne := fun (j' : Fin h) (hne : j' ≠ j) =>
    selHom_sqArbFrame_handleV_ne (A := A) (B := B) (C := C) (D := D) (P := P) (Q := Q)
      (hd := hd) (he := he) hne
  rw [SqU4.sqRelWord_eq_one_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs1, hs2]
    linear_combination 4 * hd' - P * h8
  · rw [hs1, hs2]
    ring
  · rw [hs1, hs2]
    linear_combination (-4) * he' + Q * h8
  · rw [sqHeisDefect, sum_eq_at _ (fun j' hne => by rw [hsUne j' hne, hsVne j' hne]; simp)]
    simp only [hs0, hs1, hs2, hsU, hsV, SqU4.toHeisAB_apply]
    linear_combination hd'
  · rw [sqHeisDefect, sum_eq_at _ (fun j' hne => by rw [hsUne j' hne, hsVne j' hne]; simp)]
    simp only [hs0, hs1, hs2, hsU, hsV, SqU4.toHeisBC_apply]
    linear_combination he'
  · rw [sqU4Defect, sum_eq_at _ (fun j' hne => by rw [hsUne j' hne, hsVne j' hne]; simp),
      sum_eq_at (fun j' => SqU4.u4Comm3
        (selHom h nu' j A B C D P Q hd he
          (sqArbFrame h nu' j (selDress h nu' j) (sqHandleIdxU j')))
        (selHom h nu' j A B C D P Q hd he
          (sqArbFrame h nu' j (selDress h nu' j) (sqHandleIdxV j'))))
        (fun j' hne => by rw [hsUne j' hne, hsVne j' hne]; simp [SqU4.u4Comm3])]
    simp only [hs0, hs1, hs2, hsU, hsV, sqU4Core, SqU4.u4Comm3]
    linear_combination (4 * Q) * hd' - (3 * A + B) * he' + (A * Q - P * Q) * h8

end Marking

/-! ### ⭐ Non-vacuity, and the identification with `GradedThree` §6's committed witness

The hypotheses of `sqRelWord_selHom_sqArbFrame` are met by an explicit selected marking — the
bumped marking `nuSel h j 0 1`, i.e. `ν'(u_j) = 0`, `ν'(v_j) = 1`, every other row standard.  At
one handle, at the free weights `(A, C) = (2, 2)` on `u₀` and `(B, D) = (1, 1)` on `v₀`, the five
slot images are **exactly** `GradedThree.u4WitFrame`, so the committed six-tuple evidence and the
statement about `sqArbFrame` are the same fact. -/

section NonVacuous

variable {h : ℕ} {j : Fin h}

@[simp] theorem selT_nuSel : selT h (nuSel h j 0 1) j = 0 := by
  simp only [selT, nuSel_handleU, toAdd_ofAdd, map_zero]

@[simp] theorem selS_nuSel : selS h (nuSel h j 0 1) j = 1 := by
  simp only [selS, nuSel_handleV, toAdd_ofAdd, map_one]

/-- The `(a,b)`-parity of the witness weights: `A·ν'(v₀) − B·ν'(u₀) = 2 = 2·7` in `ℤ/8`. -/
theorem selWitD (h : ℕ) (j : Fin h) :
    2 * (7 : gr3R) + (2 * selS h (nuSel h j 0 1) j - 1 * selT h (nuSel h j 0 1) j) = 0 := by
  rw [selT_nuSel, selS_nuSel]; decide

/-- The `(b,c)`-parity of the witness weights: `ν'(u₀)·D − ν'(v₀)·C = −2 = −2·1`. -/
theorem selWitE (h : ℕ) (j : Fin h) :
    2 * (1 : gr3R) + (selT h (nuSel h j 0 1) j * 1 - selS h (nuSel h j 0 1) j * 2) = 0 := by
  rw [selT_nuSel, selS_nuSel]; decide

/-- ⭐ **The gate verdict at a concrete selected marking**, at every handle count and handle. -/
theorem sqRelWord_selHom_sqArbFrame_nuSel (h : ℕ) (j : Fin h) :
    sqRelWord (fun i => selHom h (nuSel h j 0 1) j 2 1 2 1 7 1 (selWitD h j) (selWitE h j)
      (sqArbFrame h (nuSel h j 0 1) j (selDress h (nuSel h j 0 1) j) i)) = 1 :=
  sqRelWord_selHom_sqArbFrame selT_nuSel selS_nuSel

/-- ⭐⭐ **The port is exact**: at one handle the five slot images of the dressed frame are
`GradedThree` §6's committed tuple `u4WitFrame`, entry for entry.  So `sqRelWord_u4WitFrame` is
now a theorem about `sqArbFrame 1 ν' 0 a` on `D_sq 1`, with `a₁ = (sqEichU 1 ν' 0)⁻¹`. -/
theorem selHom_sqArbFrame_eq_u4WitFrame :
    (fun i => selHom 1 (nuSel 1 0 0 1) 0 2 1 2 1 7 1 (selWitD 1 0) (selWitE 1 0)
      (sqArbFrame 1 (nuSel 1 0 0 1) 0 (selDress 1 (nuSel 1 0 0 1) 0) i)) = u4WitFrame := by
  funext i
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [selHom_sqArbFrame_zero]; decide
  · rw [selHom_sqArbFrame_one selT_nuSel]; decide
  · rw [selHom_sqArbFrame_two]; decide
  · rw [Subsingleton.elim j' 0, selHom_sqArbFrame_handleU selT_nuSel]; decide
  · rw [Subsingleton.elim j' 0, selHom_sqArbFrame_handleV selS_nuSel]; decide

/-- …and the relator identity of `GradedThree` §6 is recovered through the port. -/
example : sqRelWord (fun i => selHom 1 (nuSel 1 0 0 1) 0 2 1 2 1 7 1 (selWitD 1 0) (selWitE 1 0)
    (sqArbFrame 1 (nuSel 1 0 0 1) 0 (selDress 1 (nuSel 1 0 0 1) 0) i)) = 1 := by
  rw [selHom_sqArbFrame_eq_u4WitFrame]
  exact sqRelWord_u4WitFrame

end NonVacuous

/-! ## §5 The γ₂-dressing calculus: the class-three defect moves **linearly**

W48's finding 3 said it in prose; here it is as algebra.  Dressing a handle slot of a marking
tuple on the right by a `γ₂`-element `z` (one with `z.a = z.b = z.c = 0`) leaves **every**
class-`≤ 2` row of the relator unchanged — the abelian rows read only abelian columns, the two
Heisenberg defects read only abelian columns, and the two exponent slots are untouched — while
the class-three row moves by an **affine-linear** function of `(z.d, z.e)`:

```text
U_j-slot ↦ · z₃ :   Δf = z₃.d·(m V_j).c − z₃.e·(m V_j).a
V_j-slot ↦ · z₄ :   Δf = (m U_j).a·z₄.e − (m U_j).c·z₄.d
x₀-, x₁-slot ↦ · w (γ₃) :   Δf = −4·w.f  resp.  2·w.f
```

`sqRelWord_selRefine` packages the four moves at once: the relator is **translated by a central
element**, so the refinement action of `γ₂`-dressings on the class-three residue is a group
action by translations — the linear part the ticket asked for, in closed form.  Everything in
this section is over an arbitrary commutative ring. -/

section SelCalculus

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

/-- A `γ₂`-shaped element of the class-three test group: all three abelian columns vanish. -/
def SqU4.IsGaTwo (z : SqU4 R) : Prop := z.a = 0 ∧ z.b = 0 ∧ z.c = 0

/-- A `γ₃`-shaped element: only the class-three coordinate may be non-zero. -/
def SqU4.IsGaThree (z : SqU4 R) : Prop :=
  z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0

theorem SqU4.IsGaThree.isGaTwo {z : SqU4 R} (hz : z.IsGaThree) : z.IsGaTwo :=
  ⟨hz.1, hz.2.1, hz.2.2.1⟩

@[simp] theorem SqU4.isGaThree_one : (1 : SqU4 R).IsGaThree := ⟨rfl, rfl, rfl, rfl, rfl⟩

@[simp] theorem SqU4.isGaTwo_one : (1 : SqU4 R).IsGaTwo := ⟨rfl, rfl, rfl⟩

/-- Central `(1,4)`-translations: multiplying by `⟨0,0,0,0,0,w⟩` adds `w` to the class-three
coordinate and moves nothing else. -/
theorem SqU4.mul_center_f (p : SqU4 R) (w : R) :
    p * (⟨0, 0, 0, 0, 0, w⟩ : SqU4 R) = ⟨p.a, p.b, p.c, p.d, p.e, p.f + w⟩ := by
  ext <;> simp

/-- ⭐ Dressing the **left** argument of the cubic commutator form by a `γ₂`-element moves it
linearly, with the right argument's outer abelian columns as coefficients. -/
theorem SqU4.u4Comm3_mul_gaTwo_left {p q z : SqU4 R} (hz : z.IsGaTwo) :
    SqU4.u4Comm3 (p * z) q = SqU4.u4Comm3 p q + (z.d * q.c - z.e * q.a) := by
  obtain ⟨hza, hzb, hzc⟩ := hz
  simp only [SqU4.u4Comm3, SqU4.mul_a, SqU4.mul_b, SqU4.mul_c, SqU4.mul_d, SqU4.mul_e,
    hza, hzb, hzc]
  ring

/-- ⭐ …and the **right** argument, with the left argument's columns as coefficients. -/
theorem SqU4.u4Comm3_mul_gaTwo_right {p q z : SqU4 R} (hz : z.IsGaTwo) :
    SqU4.u4Comm3 p (q * z) = SqU4.u4Comm3 p q + (p.a * z.e - p.c * z.d) := by
  obtain ⟨hza, hzb, hzc⟩ := hz
  simp only [SqU4.u4Comm3, SqU4.mul_a, SqU4.mul_b, SqU4.mul_c, SqU4.mul_d, SqU4.mul_e,
    hza, hzb, hzc]
  ring

/-- The class-two defect reads only the two abelian columns of its tuple. -/
theorem sqHeisDefect_congr_ab {m m' : Fin (sqRank h) → SqHeis R}
    (hab : ∀ i, (m' i).a = (m i).a ∧ (m' i).b = (m i).b) :
    sqHeisDefect h m' = sqHeisDefect h m := by
  simp only [sqHeisDefect, (hab _).1, (hab _).2]

/-! ### Index disequalities -/

private theorem sel_ne_handleU_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxU j := by
  intro hc
  rw [hc, sqHandleIdxU_val] at hi
  omega

private theorem sel_ne_handleV_of_lt {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    i ≠ sqHandleIdxV j := by
  intro hc
  rw [hc, sqHandleIdxV_val] at hi
  omega

private theorem sel_handleV_ne_handleU (j' : Fin h) : sqHandleIdxV j' ≠ sqHandleIdxU j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxV_val, sqHandleIdxU_val] at hv
  omega

private theorem sel_handleU_ne_handleV (j' : Fin h) : sqHandleIdxU j' ≠ sqHandleIdxV j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxU_val, sqHandleIdxV_val] at hv
  omega

private theorem sel_handleU_ne_handleU {j' : Fin h} (hne : j' ≠ j) :
    sqHandleIdxU j' ≠ sqHandleIdxU j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxU_val, sqHandleIdxU_val] at hv
  exact hne (Fin.val_injective (by omega))

private theorem sel_handleV_ne_handleV {j' : Fin h} (hne : j' ≠ j) :
    sqHandleIdxV j' ≠ sqHandleIdxV j := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [sqHandleIdxV_val, sqHandleIdxV_val] at hv
  exact hne (Fin.val_injective (by omega))

/-! ### The refinement action -/

variable (j) in
/-- **The four-slot refinement**: dress the two exponent slots by `w₁`, `w₂` and the two
`j`-handle slots by `z₃`, `z₄`, all on the right; leave every other slot alone.  With `w`'s in
`γ₃` and `z`'s in `γ₂` this is exactly the action on markings of the dressings that the
class-`≤ 2` rows cannot see. -/
def selRefine (m : Fin (sqRank h) → SqU4 R) (w₁ w₂ z₃ z₄ : SqU4 R) :
    Fin (sqRank h) → SqU4 R :=
  fun i =>
    if (i : ℕ) = 1 then m i * w₁ else
    if (i : ℕ) = 2 then m i * w₂ else
    if i = sqHandleIdxU j then m i * z₃ else
    if i = sqHandleIdxV j then m i * z₄ else m i

variable {m : Fin (sqRank h) → SqU4 R} {w₁ w₂ z₃ z₄ : SqU4 R}

@[simp] theorem selRefine_one : selRefine j m w₁ w₂ z₃ z₄ 1 = m 1 * w₁ := by
  simp only [selRefine, sqVal_one]
  norm_num

@[simp] theorem selRefine_two : selRefine j m w₁ w₂ z₃ z₄ 2 = m 2 * w₂ := by
  simp only [selRefine, sqVal_two]
  norm_num

@[simp] theorem selRefine_handleU :
    selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxU j) = m (sqHandleIdxU j) * z₃ := by
  simp only [selRefine, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

@[simp] theorem selRefine_handleV :
    selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxV j) = m (sqHandleIdxV j) * z₄ := by
  simp only [selRefine, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (sel_handleV_ne_handleU j)]
  simp

@[simp] theorem selRefine_zero : selRefine j m w₁ w₂ z₃ z₄ 0 = m 0 := by
  simp only [selRefine, sqVal_zero]
  rw [if_neg (by omega), if_neg (by omega),
    if_neg (sel_ne_handleU_of_lt (by rw [sqVal_zero]; omega)),
    if_neg (sel_ne_handleV_of_lt (by rw [sqVal_zero]; omega))]

theorem selRefine_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxU j') = m (sqHandleIdxU j') := by
  simp only [selRefine, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (sel_handleU_ne_handleU hne),
    if_neg (sel_handleU_ne_handleV j')]

theorem selRefine_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxV j') = m (sqHandleIdxV j') := by
  simp only [selRefine, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (sel_handleV_ne_handleU j'),
    if_neg (sel_handleV_ne_handleV hne)]

/-- The refinement never touches an abelian column. -/
theorem selRefine_abc (hw₁ : w₁.IsGaTwo) (hw₂ : w₂.IsGaTwo) (hz₃ : z₃.IsGaTwo)
    (hz₄ : z₄.IsGaTwo) (i : Fin (sqRank h)) :
    (selRefine j m w₁ w₂ z₃ z₄ i).a = (m i).a ∧ (selRefine j m w₁ w₂ z₃ z₄ i).b = (m i).b ∧
      (selRefine j m w₁ w₂ z₃ z₄ i).c = (m i).c := by
  have habc : ∀ (p z : SqU4 R), z.IsGaTwo →
      (p * z).a = p.a ∧ (p * z).b = p.b ∧ (p * z).c = p.c := by
    intro p z hz
    exact ⟨by rw [SqU4.mul_a, hz.1, add_zero], by rw [SqU4.mul_b, hz.2.1, add_zero],
      by rw [SqU4.mul_c, hz.2.2, add_zero]⟩
  simp only [selRefine]
  split
  · exact habc _ _ hw₁
  split
  · exact habc _ _ hw₂
  split
  · exact habc _ _ hz₃
  split
  · exact habc _ _ hz₄
  exact ⟨rfl, rfl, rfl⟩

/-- ⭐⭐ **The class-three defect moves affine-linearly under the refinement action.**  The two
exponent-slot `γ₃`-dressings are invisible; the two handle-slot `γ₂`-dressings enter through
their `(d, e)`-coordinates, paired against the *other* handle letter's outer abelian columns.
This is W48's "genuine first-order freedom at class three", as an identity. -/
theorem sqU4Defect_selRefine (hw₁ : w₁.IsGaThree) (hw₂ : w₂.IsGaThree) (hz₃ : z₃.IsGaTwo)
    (hz₄ : z₄.IsGaTwo) :
    sqU4Defect h (selRefine j m w₁ w₂ z₃ z₄)
      = sqU4Defect h m
        + (z₃.d * (m (sqHandleIdxV j)).c - z₃.e * (m (sqHandleIdxV j)).a)
        + ((m (sqHandleIdxU j)).a * z₄.e - (m (sqHandleIdxU j)).c * z₄.d) := by
  obtain ⟨hw₁a, hw₁b, hw₁c, hw₁d, hw₁e⟩ := id hw₁
  obtain ⟨hw₂a, hw₂b, hw₂c, hw₂d, hw₂e⟩ := id hw₂
  have habc := selRefine_abc (m := m) (j := j) hw₁.isGaTwo hw₂.isGaTwo hz₃ hz₄
  simp only [sqU4Defect]
  have hcore : sqU4Core (selRefine j m w₁ w₂ z₃ z₄ 0) (selRefine j m w₁ w₂ z₃ z₄ 1)
      (selRefine j m w₁ w₂ z₃ z₄ 2) = sqU4Core (m 0) (m 1) (m 2) := by
    rw [selRefine_zero, selRefine_one, selRefine_two]
    simp only [sqU4Core, SqU4.mul_a, SqU4.mul_b, SqU4.mul_c, SqU4.mul_d, SqU4.mul_e,
      hw₁a, hw₁b, hw₁c, hw₁d, hw₁e, hw₂a, hw₂b, hw₂c, hw₂d, hw₂e]
    ring
  have hcrossSum : ∀ j' : Fin h,
      (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxU j')).b
          * (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxV j')).c
        - (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxV j')).b
          * (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxU j')).c
      = (m (sqHandleIdxU j')).b * (m (sqHandleIdxV j')).c
        - (m (sqHandleIdxV j')).b * (m (sqHandleIdxU j')).c := by
    intro j'
    rw [(habc _).2.1, (habc _).2.2, (habc _).2.1, (habc _).2.2]
  have hcommSum : ∑ j' : Fin h, SqU4.u4Comm3 (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxU j'))
        (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxV j'))
      = (∑ j' : Fin h, SqU4.u4Comm3 (m (sqHandleIdxU j')) (m (sqHandleIdxV j')))
        + ((z₃.d * (m (sqHandleIdxV j)).c - z₃.e * (m (sqHandleIdxV j)).a)
          + ((m (sqHandleIdxU j)).a * z₄.e - (m (sqHandleIdxU j)).c * z₄.d)) := by
    have hoffsum : ∀ j' ∈ Finset.univ.erase j,
        SqU4.u4Comm3 (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxU j'))
            (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxV j'))
          = SqU4.u4Comm3 (m (sqHandleIdxU j')) (m (sqHandleIdxV j')) := by
      intro j' hj'
      have hne : j' ≠ j := Finset.ne_of_mem_erase hj'
      rw [selRefine_handleU_ne hne, selRefine_handleV_ne hne]
    obtain ⟨hz₄a, hz₄b, hz₄c⟩ := id hz₄
    rw [← Finset.add_sum_erase _ (fun j' => SqU4.u4Comm3
        (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxU j'))
        (selRefine j m w₁ w₂ z₃ z₄ (sqHandleIdxV j'))) (Finset.mem_univ j),
      ← Finset.add_sum_erase _ (fun j' => SqU4.u4Comm3 (m (sqHandleIdxU j'))
        (m (sqHandleIdxV j'))) (Finset.mem_univ j),
      Finset.sum_congr rfl hoffsum, selRefine_handleU, selRefine_handleV,
      SqU4.u4Comm3_mul_gaTwo_left hz₃, SqU4.u4Comm3_mul_gaTwo_right hz₄, SqU4.mul_c,
      SqU4.mul_a, hz₄a, hz₄c]
    ring
  rw [hcore, Finset.sum_congr rfl fun j' _ => hcrossSum j', hcommSum, selRefine_one,
    selRefine_two]
  simp only [SqU4.mul_a, hw₁a, hw₂a]
  ring

/-- ⭐⭐ **The linear action on the relator.**  The refinement translates the relator by a
**central** element whose value is the affine-linear expression of the four dressings — the
class-`≤ 2` rows are untouched, and the class-three row moves by exactly

```text
−4·w₁.f + 2·w₂.f + (z₃.d·(m V).c − z₃.e·(m V).a) + ((m U).a·z₄.e − (m U).c·z₄.d).
```

So on any class-two-admissible tuple the entire achievable refinement orbit of the relator is a
coset of the translation subgroup this expression generates. -/
theorem sqRelWord_selRefine (hw₁ : w₁.IsGaThree) (hw₂ : w₂.IsGaThree) (hz₃ : z₃.IsGaTwo)
    (hz₄ : z₄.IsGaTwo) :
    sqRelWord (selRefine j m w₁ w₂ z₃ z₄)
      = sqRelWord m * ⟨0, 0, 0, 0, 0, -4 * w₁.f + 2 * w₂.f
          + (z₃.d * (m (sqHandleIdxV j)).c - z₃.e * (m (sqHandleIdxV j)).a)
          + ((m (sqHandleIdxU j)).a * z₄.e - (m (sqHandleIdxU j)).c * z₄.d)⟩ := by
  obtain ⟨hw₁a, hw₁b, hw₁c, hw₁d, hw₁e⟩ := id hw₁
  obtain ⟨hw₂a, hw₂b, hw₂c, hw₂d, hw₂e⟩ := id hw₂
  have habc := selRefine_abc (m := m) (j := j) hw₁.isGaTwo hw₂.isGaTwo hz₃ hz₄
  have habAB : ∀ i, (SqU4.toHeisAB (selRefine j m w₁ w₂ z₃ z₄ i)).a
        = (SqU4.toHeisAB (m i)).a
      ∧ (SqU4.toHeisAB (selRefine j m w₁ w₂ z₃ z₄ i)).b = (SqU4.toHeisAB (m i)).b :=
    fun i => ⟨(habc i).1, (habc i).2.1⟩
  have habBC : ∀ i, (SqU4.toHeisBC (selRefine j m w₁ w₂ z₃ z₄ i)).a
        = (SqU4.toHeisBC (m i)).a
      ∧ (SqU4.toHeisBC (selRefine j m w₁ w₂ z₃ z₄ i)).b = (SqU4.toHeisBC (m i)).b :=
    fun i => ⟨(habc i).2.1, (habc i).2.2⟩
  have hdef := sqU4Defect_selRefine (m := m) (j := j) hw₁ hw₂ hz₃ hz₄
  have h_a : (sqRelWord (selRefine j m w₁ w₂ z₃ z₄)).a = (sqRelWord m).a := by
    rw [SqU4.sqRelWord_a, SqU4.sqRelWord_a, selRefine_one, selRefine_two, SqU4.mul_a,
      SqU4.mul_a, hw₁a, hw₂a]
    ring
  have h_b : (sqRelWord (selRefine j m w₁ w₂ z₃ z₄)).b = (sqRelWord m).b := by
    rw [SqU4.sqRelWord_b, SqU4.sqRelWord_b, selRefine_one, selRefine_two, SqU4.mul_b,
      SqU4.mul_b, hw₁b, hw₂b]
    ring
  have h_c : (sqRelWord (selRefine j m w₁ w₂ z₃ z₄)).c = (sqRelWord m).c := by
    rw [SqU4.sqRelWord_c, SqU4.sqRelWord_c, selRefine_one, selRefine_two, SqU4.mul_c,
      SqU4.mul_c, hw₁c, hw₂c]
    ring
  have h_d : (sqRelWord (selRefine j m w₁ w₂ z₃ z₄)).d = (sqRelWord m).d := by
    rw [SqU4.sqRelWord_d, SqU4.sqRelWord_d, selRefine_one, selRefine_two,
      sqHeisDefect_congr_ab habAB, SqU4.mul_d, SqU4.mul_d, hw₁d, hw₂d, hw₁b, hw₂b]
    ring
  have h_e : (sqRelWord (selRefine j m w₁ w₂ z₃ z₄)).e = (sqRelWord m).e := by
    rw [SqU4.sqRelWord_e, SqU4.sqRelWord_e, selRefine_one, selRefine_two,
      sqHeisDefect_congr_ab habBC, SqU4.mul_e, SqU4.mul_e, hw₁e, hw₂e, hw₁c, hw₂c]
    ring
  have h_f : (sqRelWord (selRefine j m w₁ w₂ z₃ z₄)).f = (sqRelWord m).f
      + (-4 * w₁.f + 2 * w₂.f
        + (z₃.d * (m (sqHandleIdxV j)).c - z₃.e * (m (sqHandleIdxV j)).a)
        + ((m (sqHandleIdxU j)).a * z₄.e - (m (sqHandleIdxU j)).c * z₄.d)) := by
    rw [SqU4.sqRelWord_f, SqU4.sqRelWord_f, selRefine_one, selRefine_two, hdef, SqU4.mul_f,
      SqU4.mul_f, hw₁c, hw₂c, hw₁e, hw₂e]
    ring
  rw [SqU4.mul_center_f]
  exact SqU4.ext h_a h_b h_c h_d h_e h_f

end SelCalculus

end SqCore

end Dyadic

end GQ2
