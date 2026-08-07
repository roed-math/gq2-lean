/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.LamFrames

/-!
# W44 — the **two-letter** Eichler family

`SqCore/LamFrames.lean` reduced the whole `h ≥ 1` λ-row residual to one word equation per frame
family (§3's `SqClearingStep`), and `SqCore/EichRefutation.lean` killed the two one-letter
families and their disjunction.  Both refutations run on a single mechanism, and it is worth
stating in the form that names its own escape route.

## ⭐ The unifying lemma, and why a two-letter dressing escapes it

Both families dress their four moved slots by powers of **one** of the two cleared letters, and
that letter is one the frame moved.  If a test homomorphism `φ` kills that letter then *all four*
dressings lie in `ker φ` at once, the four dressed slots fall back to their undressed values, and
the `j`-th handle commutator collapses; what is left is the bare core word, which the relator says
is the inverse of that very commutator.  So the collapse needs **the dressings to lie in `ker φ`**,
and "powers of the letter that dies" hands that to the adversary for free.

A dressing by `U^a V^b` does **not**: killing `V` leaves `U^a`, killing `U` leaves `V^b`, and no
single `D₄`-marking can kill both while keeping `[u_j, v_j] ≠ 1` (that is exactly the obstruction
`EichRefutation` §3 records).  The mechanism of the two refutations therefore provably cannot
reach the family built here.

## The family

Over the same cleared letters `w = σ·x₀^{−c₀}`, `V = v_j·w^{−s}`, `U = w^{−t}·u_j`, put

```text
m = ( σ·U^f V^e , x₀·U^{f'} V^{e'} , x₁·U^{2f'} V^{2e'} , U·V^d , V·U^{d'} )
```

with every other letter left standing (`sqEichFrameUV`).  §1 gives the slot lemmas, §2 the rows —
which are *free*, exactly as `LamFrames` §5 predicted: the row proofs use only that both cleared
letters are `λ`-trivial and `ν'`-trivial, which is symmetric in the two and survives an arbitrary
product of their powers.

## §3 Surjectivity, and the 2-by-2 recovery

Here the two-letter dressing does cost something.  Neither cleared letter is a bare slot any more:
the `u`-slot is `U·V^d` and the `v`-slot is `V·U^{d'}`, so recovering `U` and `V` is a genuine
2-by-2 problem rather than a strip-off.  Mod `[G,G]G²` the recovery matrix is `!![1, d; d', 1]`,
whose determinant is `1 − d·d'` — a unit exactly when `d·d'` is **even**, i.e. when `d` and `d'`
are not both odd.

⚠ That condition is not an artefact of the proof: a `D₄` sweep over *every* marking of `D₄`
(not merely the two of `EichRefutation` §3) shows the relator identity fails at every weight tuple
with `d` and `d'` both odd — the frame is then not even injective on `H₁`.  At `d = d' = 0` the
two handle slots degenerate back to bare `U` and `V`, the recovery is a plain strip-off in the two
letters, and that is the sub-family `sqEichFrameUV h nu' j f f' e e' 0 0` on which §3 proves
surjectivity outright (`sqEichFrameUV_surjective_of_hom`).

## §4 The residual, again in one word equation

`SqEichRelWordUV` is the resulting bare word equation, and §4 plugs it into `SqClearingStep`, so
it discharges `SqLamMarkTransitivity h` at every `h` with no rows, no surjectivity and no
composition identity left over — the reusable half of `LamFrames` §3 accepting its third input.

## ⚠ The shape rule, and the retired candidate

A `D₄` sweep over all markings also pins the parities of the four core weights.  Writing
`t = ν'(u_j)` and `s = ν'(v_j)`, the surviving tuples are exactly

```text
f ≡ f' ≡ s   and   e ≡ e' ≡ t     (mod 2),     d·d' even
```

— the **`U`-weights track the `v`-row and the `V`-weights track the `u`-row**, crosswise.  Two
consequences worth recording:

* at the standard marking `t = s = 0` all four weights are even and `(0,0,0,0,0,0)` is the
  identity frame, as it must be (`sqEichFrameUV_nuSq_zero`);
* ⚠ at `nuSel h j 1 1` — the marking that killed both one-letter families — all four must be
  **odd**, so the smallest surviving tuple is `(f,f',e,e',d,d') = (1,1,1,1,0,0)`, i.e.
  `m = (σ·U·V, x₀·U·V, x₁·U²V², U, V)`.  The "`e` odd, `f` even" reading of the Eichler
  transvection is the shape at `s = 0`, and it does **not** survive at `s = 1`.

## Contents

* **§1** `sqEichFrameUV` and its slots;
* **§2** the rows (`sqEichFrameUV_nuLam`, `sqEichFrameUV_nu`), free from `LamFrames` §2a;
* **§3** surjectivity at `d = d' = 0`, and the clearing step;
* **§4** `SqEichRelWordUV` and the residual;
* **§5** the `γ₃`-rigidity of `d, d'`; **§6** stress pins; **§7** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3** (`propext`,
`Classical.choice`, `Quot.sound`).  Census unchanged at **11**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The two-letter frame -/

section UVFrame

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

/-- Rows through a single dressing: a character of a slot `g·x^k`. -/
private theorem toAdd_mul_zpowOne
    (φ : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (g x : (DSq h : Type))
    (k : ℤ_[2]) : toAdd (φ (g * zpowZtwo (isProP_DSq h) x k)) = toAdd (φ g) + k * toAdd (φ x) := by
  rw [map_mul, toAdd_mul, toAdd_map_zpowZtwo]

/-- Rows through a **two-letter** dressing: a character of a slot `g·x^k·y^l`. -/
private theorem toAdd_mul_zpowTwo
    (φ : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (g x y : (DSq h : Type))
    (k l : ℤ_[2]) :
    toAdd (φ (g * zpowZtwo (isProP_DSq h) x k * zpowZtwo (isProP_DSq h) y l))
      = toAdd (φ g) + k * toAdd (φ x) + l * toAdd (φ y) := by
  rw [toAdd_mul_zpowOne, toAdd_mul_zpowOne]

variable (h nu' j) in
/-- **The two-letter Eichler frame** at handle `j`:

```text
m = ( σ·U^f V^e , x₀·U^{f'} V^{e'} , x₁·U^{2f'} V^{2e'} , U·V^d , V·U^{d'} )
```

with every other letter left standing.  `LamFrames`' two families are the degenerate cases
`f = f' = d' = 0` and `e = e' = d = 0` — but only up to the placement of the free handle dressing,
which is why this is a genuinely wider family rather than a common refinement. -/
noncomputable def sqEichFrameUV (f f' e e' d d' : ℤ_[2]) : Fin (sqRank h) → (DSq h : Type) :=
  fun i =>
    if (i : ℕ) = 0 then
      dsqSigma h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) f *
        zpowZtwo (isProP_DSq h) (sqEichV h nu' j) e else
    if (i : ℕ) = 1 then
      dsqX0 h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) f' *
        zpowZtwo (isProP_DSq h) (sqEichV h nu' j) e' else
    if (i : ℕ) = 2 then
      dsqX1 h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) (2 * f') *
        zpowZtwo (isProP_DSq h) (sqEichV h nu' j) (2 * e') else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then
      sqEichU h nu' j * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) d else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then
      sqEichV h nu' j * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) d' else
    sqGen h i

variable {f f' e e' d d' : ℤ_[2]}

@[simp] theorem sqEichFrameUV_zero :
    sqEichFrameUV h nu' j f f' e e' d d' 0
      = dsqSigma h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) f *
          zpowZtwo (isProP_DSq h) (sqEichV h nu' j) e := by
  simp only [sqEichFrameUV, sqVal_zero]
  norm_num

@[simp] theorem sqEichFrameUV_one :
    sqEichFrameUV h nu' j f f' e e' d d' 1
      = dsqX0 h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) f' *
          zpowZtwo (isProP_DSq h) (sqEichV h nu' j) e' := by
  simp only [sqEichFrameUV, sqVal_one]
  norm_num

@[simp] theorem sqEichFrameUV_two :
    sqEichFrameUV h nu' j f f' e e' d d' 2
      = dsqX1 h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) (2 * f') *
          zpowZtwo (isProP_DSq h) (sqEichV h nu' j) (2 * e') := by
  simp only [sqEichFrameUV, sqVal_two]
  norm_num

@[simp] theorem sqEichFrameUV_handleU :
    sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxU j)
      = sqEichU h nu' j * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) d := by
  simp only [sqEichFrameUV]
  rw [if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega)]
  simp

@[simp] theorem sqEichFrameUV_handleV :
    sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxV j)
      = sqEichV h nu' j * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) d' := by
  simp only [sqEichFrameUV]
  rw [if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val, sqHandleIdxV_val]; omega)]
  simp

theorem sqEichFrameUV_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxU j') = sqGen h (sqHandleIdxU j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqEichFrameUV]
  rw [if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val, sqHandleIdxV_val]; omega)]

theorem sqEichFrameUV_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxV j') = sqGen h (sqHandleIdxV j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqEichFrameUV]
  rw [if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val, sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega)]

@[simp] theorem sqEichFrameUV_handleU_zero :
    sqEichFrameUV h nu' j f f' e e' 0 d' (sqHandleIdxU j) = sqEichU h nu' j := by
  rw [sqEichFrameUV_handleU, SectionThree.zpowZtwo_zero, mul_one]

@[simp] theorem sqEichFrameUV_handleV_zero :
    sqEichFrameUV h nu' j f f' e e' d 0 (sqHandleIdxV j) = sqEichV h nu' j := by
  rw [sqEichFrameUV_handleV, SectionThree.zpowZtwo_zero, mul_one]

/-- **`LamFrames` §2's `V`-family is the `f = f' = d' = 0` slice**, on the nose. -/
theorem sqEichFrameUV_eq_sqEichFrame :
    sqEichFrameUV h nu' j 0 0 e e' d 0 = sqEichFrame h nu' j e e' d := by
  refine funext fun i => ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqEichFrameUV_zero, sqEichFrame_zero, SectionThree.zpowZtwo_zero, mul_one]
  · rw [sqEichFrameUV_one, sqEichFrame_one, SectionThree.zpowZtwo_zero, mul_one]
  · rw [sqEichFrameUV_two, sqEichFrame_two, mul_zero, SectionThree.zpowZtwo_zero, mul_one]
  · by_cases hjj : j' = j
    · subst hjj; rw [sqEichFrameUV_handleU, sqEichFrame_handleU]
    · rw [sqEichFrameUV_handleU_ne hjj, sqEichFrame_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj; rw [sqEichFrameUV_handleV_zero, sqEichFrame_handleV]
    · rw [sqEichFrameUV_handleV_ne hjj, sqEichFrame_handleV_ne hjj]

/-- **`LamFrames` §5's transposed family is the `e = e' = d = 0` slice**, on the nose.  So the
two-letter family really is a common widening of the two, not a third thing beside them. -/
theorem sqEichFrameUV_eq_sqEichFrameT :
    sqEichFrameUV h nu' j f f' 0 0 0 d' = sqEichFrameT h nu' j f f' d' := by
  refine funext fun i => ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqEichFrameUV_zero, sqEichFrameT_zero, SectionThree.zpowZtwo_zero, mul_one]
  · rw [sqEichFrameUV_one, sqEichFrameT_one, SectionThree.zpowZtwo_zero, mul_one]
  · rw [sqEichFrameUV_two, sqEichFrameT_two, mul_zero, SectionThree.zpowZtwo_zero, mul_one]
  · by_cases hjj : j' = j
    · subst hjj; rw [sqEichFrameUV_handleU_zero, sqEichFrameT_handleU]
    · rw [sqEichFrameUV_handleU_ne hjj, sqEichFrameT_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj; rw [sqEichFrameUV_handleV, sqEichFrameT_handleV]
    · rw [sqEichFrameUV_handleV_ne hjj, sqEichFrameT_handleV_ne hjj]

/-! ## §2 The rows are free

`LamFrames` §5 said it and this section is the check: the row proofs of §2a use only that both
cleared letters are `λ`-trivial (`toAdd_nuLam_sqEichU`, `toAdd_nuLam_sqEichV`) and `ν'`-trivial at
a selected marking (`toAdd_nu_sqEichU`, `toAdd_nu_sqEichV`).  Both properties pass to an arbitrary
product of powers of the two, so every row of the two-letter frame is again a one-line
evaluation. -/

/-- **The λ-row of the two-letter frame is the standard one, unconditionally.** -/
theorem sqEichFrameUV_nuLam (i : Fin (sqRank h)) :
    nuLam h (sqEichFrameUV h nu' j f f' e e' d d' i) = nuLam h (sqGen h i) := by
  refine Multiplicative.toAdd.injective ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · show toAdd (nuLam h (sqEichFrameUV h nu' j f f' e e' d d' 0)) = toAdd (nuLam h (dsqSigma h))
    rw [sqEichFrameUV_zero, toAdd_mul_zpowTwo, toAdd_nuLam_sqEichU, toAdd_nuLam_sqEichV,
      mul_zero, mul_zero, add_zero, add_zero]
  · show toAdd (nuLam h (sqEichFrameUV h nu' j f f' e e' d d' 1)) = toAdd (nuLam h (dsqX0 h))
    rw [sqEichFrameUV_one, toAdd_mul_zpowTwo, toAdd_nuLam_sqEichU, toAdd_nuLam_sqEichV,
      mul_zero, mul_zero, add_zero, add_zero]
  · show toAdd (nuLam h (sqEichFrameUV h nu' j f f' e e' d d' 2)) = toAdd (nuLam h (dsqX1 h))
    rw [sqEichFrameUV_two, toAdd_mul_zpowTwo, toAdd_nuLam_sqEichU, toAdd_nuLam_sqEichV,
      mul_zero, mul_zero, add_zero, add_zero]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrameUV_handleU, toAdd_mul_zpowOne, toAdd_nuLam_sqEichV, mul_zero, add_zero,
        toAdd_nuLam_sqEichU, nuLam_handleU, toAdd_one]
    · rw [sqEichFrameUV_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrameUV_handleV, toAdd_mul_zpowOne, toAdd_nuLam_sqEichU, mul_zero, add_zero,
        toAdd_nuLam_sqEichV, nuLam_handleV, toAdd_one]
    · rw [sqEichFrameUV_handleV_ne hjj]

/-- The `σ`-row, with **no** hypothesis on the other handles. -/
theorem nu_sqEichFrameUV_zero (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrameUV h nu' j f f' e e' d d' 0) = ofAdd (1 : ℤ_[2]) := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrameUV_zero, toAdd_mul_zpowTwo, toAdd_nu_sqEichU hsigma hx0,
    toAdd_nu_sqEichV hsigma hx0, mul_zero, mul_zero, add_zero, add_zero, hsigma]

/-- The `x₀`-row. -/
theorem nu_sqEichFrameUV_one (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrameUV h nu' j f f' e e' d d' 1) = ofAdd (0 : ℤ_[2]) := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrameUV_one, toAdd_mul_zpowTwo, toAdd_nu_sqEichU hsigma hx0,
    toAdd_nu_sqEichV hsigma hx0, mul_zero, mul_zero, add_zero, add_zero, hx0]

/-- **Handle `j` is cleared**: its `u`-row vanishes. -/
theorem nu_sqEichFrameUV_handleU_self (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxU j)) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrameUV_handleU, toAdd_mul_zpowOne, toAdd_nu_sqEichV hsigma hx0,
    toAdd_nu_sqEichU hsigma hx0, mul_zero, add_zero, toAdd_one]

/-- **Handle `j` is cleared**: its `v`-row vanishes. -/
theorem nu_sqEichFrameUV_handleV_self (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrameUV h nu' j f f' e e' d d' (sqHandleIdxV j)) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrameUV_handleV, toAdd_mul_zpowOne, toAdd_nu_sqEichU hsigma hx0,
    toAdd_nu_sqEichV hsigma hx0, mul_zero, add_zero, toAdd_one]

/-- **The ν-row of the two-letter frame is the standard marking's**, at handle `j`. -/
theorem sqEichFrameUV_nu (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hoth : ∀ j' : Fin h, j' ≠ j →
      nu' (sqGen h (sqHandleIdxU j')) = 1 ∧ nu' (sqGen h (sqHandleIdxV j')) = 1)
    (i : Fin (sqRank h)) :
    nu' (sqEichFrameUV h nu' j f f' e e' d d' i) = nuSq h (sqGen h i) := by
  refine Multiplicative.toAdd.injective ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · show toAdd (nu' (sqEichFrameUV h nu' j f f' e e' d d' 0)) = toAdd (nuSq h (dsqSigma h))
    rw [nu_sqEichFrameUV_zero hsigma hx0, nuSq_sigma]
  · show toAdd (nu' (sqEichFrameUV h nu' j f f' e e' d d' 1)) = toAdd (nuSq h (dsqX0 h))
    rw [nu_sqEichFrameUV_one hsigma hx0, nuSq_x0]
  · show toAdd (nu' (sqEichFrameUV h nu' j f f' e e' d d' 2)) = toAdd (nuSq h (dsqX1 h))
    rw [sqEichFrameUV_two, toAdd_mul_zpowTwo, toAdd_nu_sqEichU hsigma hx0,
      toAdd_nu_sqEichV hsigma hx0, mul_zero, mul_zero, add_zero, add_zero, toAdd_nu_dsqX1, hx0,
      nuSq_x1]
    simp
  · by_cases hjj : j' = j
    · subst hjj
      rw [nu_sqEichFrameUV_handleU_self hsigma hx0, nuSq_handleU]
    · rw [sqEichFrameUV_handleU_ne hjj, (hoth j' hjj).1, nuSq_handleU]
  · by_cases hjj : j' = j
    · subst hjj
      rw [nu_sqEichFrameUV_handleV_self hsigma hx0, nuSq_handleV]
    · rw [sqEichFrameUV_handleV_ne hjj, (hoth j' hjj).2, nuSq_handleV]

/-! ## §3 Surjectivity: the 2-by-2 recovery, and where it degenerates

At `d = d' = 0` the two handle slots are the bare letters `U` and `V`, so a slot `a·U^k·V^l` peels
in two steps and §2b's argument runs with one extra layer.  Everything after the peel is
unchanged: the pivot is a word in `σ` and `x₀`, and the two handle letters return as
`v_j = V·w^{s}`, `u_j = w^{t}·U`. -/

/-- **Any endomorphism realizing the two-letter frame at `d = d' = 0` is surjective.**  Stated for
an arbitrary `Φ` rather than for `sqLiftHom`, so that it does not depend on the relator. -/
theorem sqEichFrameUV_surjective_of_hom (Φ : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hΦ : ∀ i, Φ (sqGen h i) = sqEichFrameUV h nu' j f f' e e' 0 0 i) : Function.Surjective Φ := by
  have hpow : ∀ (x : (DSq h : Type)) (k : ℤ_[2]),
      Φ (zpowZtwo (isProP_DSq h) x k) = zpowZtwo (isProP_DSq h) (Φ x) k :=
    fun x k => map_zpowZtwo (isProP_DSq h) (isProP_DSq h) Φ x k
  have hU : Φ (sqGen h (sqHandleIdxU j)) = sqEichU h nu' j := by
    rw [hΦ, sqEichFrameUV_handleU_zero]
  have hV : Φ (sqGen h (sqHandleIdxV j)) = sqEichV h nu' j := by
    rw [hΦ, sqEichFrameUV_handleV_zero]
  have hstrip : ∀ (a : (DSq h : Type)) (i : Fin (sqRank h)) (k l : ℤ_[2]),
      sqEichFrameUV h nu' j f f' e e' 0 0 i
          = a * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) k *
              zpowZtwo (isProP_DSq h) (sqEichV h nu' j) l →
        a ∈ Set.range Φ := by
    refine fun a i k l hi => ⟨sqGen h i *
      (zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxV j)) l)⁻¹ *
      (zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxU j)) k)⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv, hΦ, hi, hpow, hpow, hU, hV, mul_inv_cancel_right,
      mul_inv_cancel_right]
  obtain ⟨a, ha⟩ := hstrip (dsqSigma h) 0 f e sqEichFrameUV_zero
  obtain ⟨b, hb⟩ := hstrip (dsqX0 h) 1 f' e' sqEichFrameUV_one
  obtain ⟨c, hc⟩ := hstrip (dsqX1 h) 2 (2 * f') (2 * e') sqEichFrameUV_two
  have hw : Φ (a * (zpowZtwo (isProP_DSq h) b sqPivotExp)⁻¹) = sqPivot h := by
    rw [map_mul, map_inv, ha, hpow, hb, sqPivot, sqMixPivotElem]
  refine surjective_of_topGen_subset_range (dsq_topGen h) Φ ?_
  rintro _ ⟨i, rfl⟩
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · exact ⟨a, ha⟩
  · exact ⟨b, hb⟩
  · exact ⟨c, hc⟩
  · by_cases hjj : j' = j
    · subst hjj
      refine ⟨zpowZtwo (isProP_DSq h) (a * (zpowZtwo (isProP_DSq h) b sqPivotExp)⁻¹)
        (toAdd (nu' (sqGen h (sqHandleIdxU j')))) * sqGen h (sqHandleIdxU j'), ?_⟩
      rw [map_mul, hpow, hw, hU, pivotPow_mul_sqEichU]
    · exact ⟨sqGen h (sqHandleIdxU j'), by rw [hΦ, sqEichFrameUV_handleU_ne hjj]⟩
  · by_cases hjj : j' = j
    · subst hjj
      refine ⟨sqGen h (sqHandleIdxV j') *
        zpowZtwo (isProP_DSq h) (a * (zpowZtwo (isProP_DSq h) b sqPivotExp)⁻¹)
          (toAdd (nu' (sqGen h (sqHandleIdxV j')))), ?_⟩
      rw [map_mul, hV, hpow, hw, sqEichV_mul_pivotPow]
    · exact ⟨sqGen h (sqHandleIdxV j'), by rw [hΦ, sqEichFrameUV_handleV_ne hjj]⟩

/-- **The two-letter frame's lift is surjective as soon as it exists** (at `d = d' = 0`). -/
theorem sqEichFrameUV_surjective (hrel : sqRelWord (sqEichFrameUV h nu' j f f' e e' 0 0) = 1) :
    Function.Surjective (sqLiftHom h (isProP_DSq h) (sqEichFrameUV h nu' j f f' e e' 0 0) hrel) :=
  sqEichFrameUV_surjective_of_hom _ (sqLiftHom_gen h (isProP_DSq h) _ hrel)

/-- **The one-handle clearing step for the two-letter family** — the same five clauses as
`sqEichStep` and `sqEichStepT`, so `LamFrames` §3's induction accepts it unchanged. -/
theorem sqEichStepUV (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hrel : sqRelWord (sqEichFrameUV h nu' j f f' e e' 0 0) = 1) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
        nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧ nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1 ∧
          nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1 ∧
            ∀ j' : Fin h, j' ≠ j →
              nu' (Ψ (sqGen h (sqHandleIdxU j'))) = nu' (sqGen h (sqHandleIdxU j')) ∧
                nu' (Ψ (sqGen h (sqHandleIdxV j'))) = nu' (sqGen h (sqHandleIdxV j')) := by
  refine ⟨sqAutOfMark hrel (sqEichFrameUV_surjective hrel), fun x => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hext : (nuLam h).comp (autHom (sqAutOfMark hrel (sqEichFrameUV_surjective hrel)))
        = nuLam h :=
      dsq_hom_ext _ _ fun i => by
        show nuLam h (sqAutOfMark hrel (sqEichFrameUV_surjective hrel) (sqGen h i))
          = nuLam h (sqGen h i)
        rw [sqAutOfMark_gen, sqEichFrameUV_nuLam]
    exact DFunLike.congr_fun hext x
  · show nu' (sqAutOfMark hrel (sqEichFrameUV_surjective hrel) (sqGen h 0)) = ofAdd (1 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqEichFrameUV_zero hsigma hx0]
  · show nu' (sqAutOfMark hrel (sqEichFrameUV_surjective hrel) (sqGen h 1)) = ofAdd (0 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqEichFrameUV_one hsigma hx0]
  · rw [sqAutOfMark_gen, nu_sqEichFrameUV_handleU_self hsigma hx0]
  · rw [sqAutOfMark_gen, nu_sqEichFrameUV_handleV_self hsigma hx0]
  · exact fun j' hjj => ⟨by rw [sqAutOfMark_gen, sqEichFrameUV_handleU_ne hjj],
      by rw [sqAutOfMark_gen, sqEichFrameUV_handleV_ne hjj]⟩

end UVFrame

/-! ## §4 The residual, in the two-letter word equation -/

section UVReduction

variable {h : ℕ}

/-- **The two-letter relator identity**: at every selected marking and every handle, some
two-letter dressing weights `(f, f', e, e')` kill the relator.

Unlike `SqEichRelWord` and `SqEichRelWordT` this is **not** known to be false: the `D₄` mechanism
of `SqCore/EichRefutation.lean` collapses a frame only when *all* its dressings lie in the test
homomorphism's kernel, and a dressing `U^f V^e` with `f` and `e` both odd lies in no such kernel —
killing `V` leaves `U^f`, killing `U` leaves `V^e`, and no marking of `D₄` kills both while
keeping `[u_j, v_j] ≠ 1`. -/
def SqEichRelWordUV (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ f f' e e' : ℤ_[2], sqRelWord (sqEichFrameUV h nu' j f f' e e' 0 0) = 1

/-- The two-letter identity supplies a clearing step (§3). -/
theorem sqClearingStep_of_eichRelWordUV (H : SqEichRelWordUV h) : SqClearingStep h := by
  intro nu' j hsigma hx0
  obtain ⟨f, f', e, e', hrel⟩ := H nu' j hsigma hx0
  exact sqEichStepUV hsigma hx0 hrel

/-- **The residual, from the two-letter identity.**  No rows, no surjectivity, no inverse
substitution, no composition identity, and no restriction on `h`. -/
theorem sqLamMarkTransitivity_of_eichRelWordUV (H : SqEichRelWordUV h) :
    SqLamMarkTransitivity h :=
  sqLamMarkTransitivity_of_clearingStep (sqClearingStep_of_eichRelWordUV H)

/-- …and hence `SqLamNuClearHypothesis`, and the handle stratum at every unit exponent. -/
theorem sqHandleMixFixesCore_of_eichRelWordUV {c : ℤ_[2]} (hc : IsUnit c) (hh : 0 < h)
    (H : SqEichRelWordUV h) : SqHandleMixFixesCore h c :=
  sqHandleMixFixesCore_of_lamMarkTransitivity hc hh (sqLamMarkTransitivity_of_eichRelWordUV H)

/-- **The one-handle form**, the smallest open instance. -/
theorem sqLamMarkTransitivity_one_of_eichRelWordUV
    (H : ∀ nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma 1) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 1) = ofAdd (0 : ℤ_[2]) →
        ∃ f f' e e' : ℤ_[2], sqRelWord (sqEichFrameUV 1 nu' 0 f f' e e' 0 0) = 1) :
    SqLamMarkTransitivity 1 :=
  sqLamMarkTransitivity_of_eichRelWordUV fun nu' j hsigma hx0 => by
    rw [show j = 0 from Subsingleton.elim _ _]
    exact H nu' hsigma hx0

end UVReduction

/-! ## §5 The `d`-slots still only conjugate

`V^d` commutes with `V` and `U^{d'}` with `U`, so the moved handle commutator at general `(d, d')`
is a `γ₃`-perturbation of the `(0, 0)` one, exactly as in `LamFrames` §4/§5d.  ⚠ Combined with the
`D₄` shape rule (`d·d'` even) this is why §4 poses the identity at `d = d' = 0`: the two extra
parameters are invisible modulo `γ₃` and cost the surjectivity argument a 2-by-2 inversion. -/

section UVRigidity

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}
  {f f' e e' d d' : ℤ_[2]}

/-- **The `d'`-slot only conjugates**: at `d = 0` the frame's handle commutator is `[U, V]`
conjugated by `U^{d'}`, times a correction that is itself a commutator. -/
theorem sqEichFrameUV_handleComm_zero :
    commP (sqEichFrameUV h nu' j f f' e e' 0 d' (sqHandleIdxU j))
        (sqEichFrameUV h nu' j f f' e e' 0 d' (sqHandleIdxV j))
      = conjP (commP (sqEichU h nu' j) (sqEichV h nu' j))
          (zpowZtwo (isProP_DSq h) (sqEichU h nu' j) d') := by
  rw [sqEichFrameUV_handleU_zero, sqEichFrameUV_handleV,
    commP_mul_zpowZtwo_right (isProP_DSq h) (sqEichU h nu' j) (sqEichV h nu' j) d']

/-- **At `d = d' = 0` the handle block is the bare `[U, V]`.** -/
theorem sqEichFrameUV_handleComm :
    commP (sqEichFrameUV h nu' j f f' e e' 0 0 (sqHandleIdxU j))
        (sqEichFrameUV h nu' j f f' e e' 0 0 (sqHandleIdxV j))
      = commP (sqEichU h nu' j) (sqEichV h nu' j) := by
  rw [sqEichFrameUV_handleU_zero, sqEichFrameUV_handleV_zero]

end UVRigidity

/-! ## §6 Stress pins -/

section StressTests

/-- **The two-letter ansatz is satisfiable.**  At the standard marking both handle letters are
already cleared, so the frame at all-zero weights *is* the identity frame — and, per the `D₄`
shape rule, `t = s = 0` is exactly where all four core weights may be even. -/
theorem sqEichFrameUV_nuSq_zero (h : ℕ) (j : Fin h) :
    sqEichFrameUV h (nuSq h) j 0 0 0 0 0 0 = sqGen h := by
  have hV : sqEichV h (nuSq h) j = sqGen h (sqHandleIdxV j) := by
    rw [sqEichV, nuSq_handleV, toAdd_one, SectionThree.zpowZtwo_zero, inv_one, mul_one]
  have hU : sqEichU h (nuSq h) j = sqGen h (sqHandleIdxU j) := by
    rw [sqEichU, nuSq_handleU, toAdd_one, SectionThree.zpowZtwo_zero, inv_one, one_mul]
  refine funext fun i => ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqEichFrameUV_zero, SectionThree.zpowZtwo_zero, SectionThree.zpowZtwo_zero, mul_one,
      mul_one]; rfl
  · rw [sqEichFrameUV_one, SectionThree.zpowZtwo_zero, SectionThree.zpowZtwo_zero, mul_one,
      mul_one]; rfl
  · rw [sqEichFrameUV_two, mul_zero, SectionThree.zpowZtwo_zero, SectionThree.zpowZtwo_zero,
      mul_one, mul_one]; rfl
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrameUV_handleU_zero, hU]
    · rw [sqEichFrameUV_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrameUV_handleV_zero, hV]
    · rw [sqEichFrameUV_handleV_ne hjj]

/-- Stress: hence the two-letter relator identity is satisfiable. -/
example (h : ℕ) (j : Fin h) : sqRelWord (sqEichFrameUV h (nuSq h) j 0 0 0 0 0 0) = 1 := by
  rw [sqEichFrameUV_nuSq_zero]
  exact dsq_relation h

/-- Stress: `h = 0` runs through the two-letter reduction too. -/
example : SqLamMarkTransitivity 0 :=
  sqLamMarkTransitivity_of_eichRelWordUV fun _ j _ _ => absurd j.isLt (by omega)

example : SqEichRelWordUV 0 := fun _ j _ _ => absurd j.isLt (by omega)

/-- Stress: the `λ`-row is unconditional at **every** weight tuple, including the ones the `D₄`
sweep rules out — the rows never were the constraint. -/
example (h : ℕ) (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    (f f' e e' d d' : ℤ_[2]) (i : Fin (sqRank h)) :
    nuLam h (sqEichFrameUV h nu' j f f' e e' d d' i) = nuLam h (sqGen h i) :=
  sqEichFrameUV_nuLam i

/-- Stress: surjectivity is relator-free, exactly as for the two one-letter families. -/
example (h : ℕ) (j : Fin h) (Φ : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hΦ : ∀ i, Φ (sqGen h i) = sqEichFrameUV h (nuSq h) j 0 0 0 0 0 0 i) :
    Function.Surjective Φ := sqEichFrameUV_surjective_of_hom Φ hΦ

/-- Stress: the marking that killed both one-letter families is inside this binder too — the
two-letter family is asked the same question at the same place. -/
example (h : ℕ) (j : Fin h) (H : SqEichRelWordUV h) :
    ∃ f f' e e' : ℤ_[2], sqRelWord (sqEichFrameUV h (nuSel h j 1 1) j f f' e e' 0 0) = 1 :=
  H (nuSel h j 1 1) j nuSel_sigma nuSel_x0

/-- Stress: the frame characterization of `LamFrames` §1 is what all three families are aiming
at, and it is untouched. -/
example (h : ℕ) (H : SqLamMarkTransitivity h) : SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_lamMarkTransitivity H

end StressTests

/-! ## §7 Axiom pins

Committed prints: the whole file is **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable. -/

section AxiomPins

#print axioms sqEichFrameUV
#print axioms sqEichFrameUV_zero
#print axioms sqEichFrameUV_one
#print axioms sqEichFrameUV_two
#print axioms sqEichFrameUV_handleU
#print axioms sqEichFrameUV_handleV
#print axioms sqEichFrameUV_handleU_ne
#print axioms sqEichFrameUV_handleV_ne
#print axioms sqEichFrameUV_handleU_zero
#print axioms sqEichFrameUV_handleV_zero
#print axioms sqEichFrameUV_eq_sqEichFrame
#print axioms sqEichFrameUV_eq_sqEichFrameT
#print axioms sqEichFrameUV_nuLam
#print axioms nu_sqEichFrameUV_zero
#print axioms nu_sqEichFrameUV_one
#print axioms nu_sqEichFrameUV_handleU_self
#print axioms nu_sqEichFrameUV_handleV_self
#print axioms sqEichFrameUV_nu
#print axioms sqEichFrameUV_surjective_of_hom
#print axioms sqEichFrameUV_surjective
#print axioms sqEichStepUV
#print axioms SqEichRelWordUV
#print axioms sqClearingStep_of_eichRelWordUV
#print axioms sqLamMarkTransitivity_of_eichRelWordUV
#print axioms sqHandleMixFixesCore_of_eichRelWordUV
#print axioms sqLamMarkTransitivity_one_of_eichRelWordUV
#print axioms sqEichFrameUV_handleComm_zero
#print axioms sqEichFrameUV_handleComm
#print axioms sqEichFrameUV_nuSq_zero

end AxiomPins

end SqCore

end Dyadic

end GQ2
