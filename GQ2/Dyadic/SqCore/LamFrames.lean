/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.DsqDemushkin

/-!
# W44 — frames for the λ-row residual: the characterization, and the Eichler scaffold

`SqCore/DsqDemushkin.lean` §6b showed that **one relator-killing frame with a surjective lift
and the prescribed rows**, per selected marking, suffices for the whole `h ≥ 1` residual
(`sqLamMarkTransitivity_of_frames`).  This file does two things.

## Headline 1 — the frame form is a *characterization*, not merely a sufficient condition

```text
theorem sqLamMarkTransitivity_iff_frames :
    SqLamMarkTransitivity h ↔ ∀ ν' selected, ∃ m hrel, Surjective (lift m) ∧ λ-rows ∧ ν-rows
```

The converse is immediate — `m i := Ψ (g i)` — but it matters: it says the frame route loses
**nothing**, so a *refutation* may now be attempted at the word level, against an explicit
five-word existential, rather than against a quantifier over `Aut(D_sq h)`.

## Headline 2 — the Eichler frame: five explicit words, rows and surjectivity discharged

For a selected marking `ν'` with handle rows `ν'(u_j) = t`, `ν'(v_j) = s`, put

```text
w  = σ · x₀^{−c₀}          (the canonical pivot: λ(w) = 0, ν'(w) = 1)
V  = v_j · w^{−s}          (λ(V) = 0, ν'(V) = 0)
U  = w^{−t} · u_j          (λ(U) = 0, ν'(U) = 0)
```

and take the frame

```text
m = ( σ·V^e , x₀·V^{e'} , x₁·V^{2e'} , U·V^d , V )        (other letters unmoved)
```

Then **every row condition of `sqLamMarkTransitivity_of_frames` holds by evaluation**
(`sqEichFrame_nuLam`, `sqEichFrame_nu`) and **the lift is surjective as soon as it exists**
(`sqEichFrame_surjective`): the five words recover `V`, then `σ, x₀, x₁`, then `w`, then
`v_j = V·w^{s}` and `u_j = w^{t}·U`.  So the residual at one handle collapses to the *single*
relator identity

```text
sqRelWord (sqEichFrame h ν' j e e' d) = 1
```

with no rows, no surjectivity, no inverse substitution, and no composition identity
(`sqLamMarkTransitivity_one_of_eichRelWord`).  That is the smallest form the residual has
taken.

## Why *this* frame shape, and what it costs

The row conditions alone do not pin the frame; the mod-2 cup form does.  Writing `T` for the
induced map on `H_1`, `sqLamMarkTransitivity` needs `T` to fix `λ`, to carry `ν'` to `ν_sq`,
**and** to be an isometry of `sqGram` (`PivotClimb` §2 — that clause is automatic for an
automorphism, hence *necessary* for a frame).  Dualising `sqGram`, the isometry must fix
`w_λ = σ̄ + x̄₀` and carry `w_ν = x̄₀` to `w_{ν'} = x̄₀ + v̄_j`, and Witt's theorem for the
non-alternating form leaves a stabiliser of order two.  The resulting mod-2 map

```text
σ̄ ↦ σ̄ + v̄_j ,  x̄₀ ↦ x̄₀ + v̄_j ,  t̄ ↦ t̄ ,  ū_j ↦ ū_j + σ̄ + x̄₀ ,  v̄_j ↦ v̄_j
```

is exactly an **Eichler transvection** `E(v̄_j, m)` of the hyperbolic plane `⟨ū_j, v̄_j⟩` at
`m = −σ̄ + c₀x̄₀ = −w̄`, which is what `sqEichFrame` realises at the group level; the exponents
`e, e'` must be **odd** for that reason (`sqEichFrame` accepts them as parameters and does not
impose it — the relator identity will).

## What this file does **not** settle

The relator identity is **open**, and this file adds no evidence either way.  The bare frame
above is the *leading term*; the class-two balance of `docs/dyadic/eichler-reduction-note.md`
already prices its first correction (`e' = 1`, `e = 2 + c₀`), and the weight-4 miss recorded
there is against the same shape.  What §3 buys is that the obligation is now a **single closed
equation in `D_sq h`**, so a correction may be inserted in any slot without re-proving a single
row.

## Contents

* **§1** `sqFrames_of_lamMarkTransitivity` and `sqLamMarkTransitivity_iff_frames`;
* **§2** `sqEichPivotPow`, `sqEichV`, `sqEichU`, `sqEichFrame` and their rows;
* **§3** surjectivity of the frame's lift, and the residual reduced to the relator identity;
* **§4** stress pins, **§5** committed axiom prints.

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

/-! ## §1 The frame form is a characterization

`DsqDemushkin` §6b proved that frames *suffice*.  They are also *necessary*: the images of the
standard generators under a correcting automorphism are a frame.  So nothing is lost by
searching for words instead of automorphisms — and a refutation may target the words. -/

section Characterization

variable {h : ℕ}

/-- **The converse of `sqLamMarkTransitivity_of_frames`**: a correcting automorphism *is* a
frame, read at the standard generators. -/
theorem sqFrames_of_lamMarkTransitivity (H : SqLamMarkTransitivity h)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    ∃ (m : Fin (sqRank h) → (DSq h : Type)) (hrel : sqRelWord m = 1),
      Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel) ∧
        (∀ i, nuLam h (m i) = nuLam h (sqGen h i)) ∧
          ∀ i, nu' (m i) = nuSq h (sqGen h i) := by
  obtain ⟨Ψ, hlam, hval⟩ := H nu' hsigma hx0
  have hrel : sqRelWord (fun i => Ψ (sqGen h i)) = 1 := by
    have := map_sqRelWord (autHom Ψ) (sqGen h)
    rw [dsq_relation h, map_one] at this
    exact this.symm
  refine ⟨fun i => Ψ (sqGen h i), hrel, ?_, fun i => hlam _, fun i => hval _⟩
  have hEq : sqLiftHom h (isProP_DSq h) (fun i => Ψ (sqGen h i)) hrel = autHom Ψ :=
    dsq_hom_ext _ _ fun i => sqLiftHom_gen _ _ _ _ i
  rw [hEq]
  exact fun y => ⟨Ψ.symm y, Ψ.apply_symm_apply y⟩

/-- **The frame form of the residual is an equivalence.**  Combined with
`sqHandleMixFixesCore_iff_lam`, the whole `h ≥ 1` handle stratum is *exactly* a five-word
existential. -/
theorem sqLamMarkTransitivity_iff_frames :
    SqLamMarkTransitivity h ↔
      ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
        nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
          ∃ (m : Fin (sqRank h) → (DSq h : Type)) (hrel : sqRelWord m = 1),
            Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel) ∧
              (∀ i, nuLam h (m i) = nuLam h (sqGen h i)) ∧
                ∀ i, nu' (m i) = nuSq h (sqGen h i) :=
  ⟨fun H nu' hs hx => sqFrames_of_lamMarkTransitivity H nu' hs hx,
    sqLamMarkTransitivity_of_frames⟩

/-- The same statement for `SqLamNuClearHypothesis`, the name the L row carries. -/
theorem sqLamNuClearHypothesis_iff_frames :
    SqLamNuClearHypothesis h ↔
      ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
        nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
          ∃ (m : Fin (sqRank h) → (DSq h : Type)) (hrel : sqRelWord m = 1),
            Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel) ∧
              (∀ i, nuLam h (m i) = nuLam h (sqGen h i)) ∧
                ∀ i, nu' (m i) = nuSq h (sqGen h i) :=
  (sqLamMarkTransitivity_iff h).symm.trans sqLamMarkTransitivity_iff_frames

end Characterization

/-! ## §2 The Eichler frame, and its rows

At a selected marking the canonical pivot `w = σ·x₀^{−c₀}` has `λ(w) = 0` and `ν'(w) = 1`
(`toAdd_nuLam_sqPivot`, `toAdd_nu_sqPivot_selected`), so it is the unique available lever for
moving a `ν'`-row without disturbing the `λ`-row.  Subtracting the right multiple of `w` from
each handle letter kills its `ν'`-row outright; the core letters then take `V`-dressings, which
cost nothing on either row.  Every row of the frame is therefore a one-line evaluation. -/

section EichlerFrame

variable {h : ℕ}

/-- Rows through a `V`-dressing: a character of a slot `g·V^k`. -/
private theorem toAdd_mul_zpow (f : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (g x : (DSq h : Type)) (k : ℤ_[2]) :
    toAdd (f (g * zpowZtwo (isProP_DSq h) x k)) = toAdd (f g) + k * toAdd (f x) := by
  rw [map_mul, toAdd_mul, toAdd_map_zpowZtwo]

/-- **The pivot row at a selected marking**: `ν'(w) = ν'(σ) − c₀·ν'(x₀) = 1`. -/
theorem toAdd_nu_sqPivot_selected
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) : toAdd (nu' (sqPivot h)) = 1 := by
  rw [sqPivot, toAdd_nu_sqMixPivotElem, hsigma, hx0, toAdd_ofAdd, toAdd_ofAdd, mul_zero, sub_zero]

variable (h) in
/-- **The cleared `v`-letter** `V_j = v_j · w^{−ν'(v_j)}`: the handle letter with its `ν'`-row
subtracted off along the pivot. -/
noncomputable def sqEichV (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (j : Fin h) : (DSq h : Type) :=
  sqGen h (sqHandleIdxV j) *
    (zpowZtwo (isProP_DSq h) (sqPivot h) (toAdd (nu' (sqGen h (sqHandleIdxV j)))))⁻¹

variable (h) in
/-- **The cleared `u`-letter** `U_j = w^{−ν'(u_j)} · u_j`.  (The pivot power is written on the
left: the relator meets `u_j` first inside `[u_j, v_j]`.) -/
noncomputable def sqEichU (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (j : Fin h) : (DSq h : Type) :=
  (zpowZtwo (isProP_DSq h) (sqPivot h) (toAdd (nu' (sqGen h (sqHandleIdxU j)))))⁻¹ *
    sqGen h (sqHandleIdxU j)

variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

@[simp] theorem toAdd_nuLam_sqEichV : toAdd (nuLam h (sqEichV h nu' j)) = 0 := by
  rw [sqEichV, map_mul, toAdd_mul, map_inv, toAdd_inv, toAdd_map_zpowZtwo, toAdd_nuLam_sqPivot,
    nuLam_handleV, toAdd_one, mul_zero, neg_zero, add_zero]

@[simp] theorem toAdd_nuLam_sqEichU : toAdd (nuLam h (sqEichU h nu' j)) = 0 := by
  rw [sqEichU, map_mul, toAdd_mul, map_inv, toAdd_inv, toAdd_map_zpowZtwo, toAdd_nuLam_sqPivot,
    nuLam_handleU, toAdd_one, mul_zero, neg_zero, zero_add]

theorem toAdd_nu_sqEichV (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) : toAdd (nu' (sqEichV h nu' j)) = 0 := by
  rw [sqEichV, map_mul, toAdd_mul, map_inv, toAdd_inv, toAdd_map_zpowZtwo,
    toAdd_nu_sqPivot_selected nu' hsigma hx0, mul_one, add_neg_cancel]

theorem toAdd_nu_sqEichU (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) : toAdd (nu' (sqEichU h nu' j)) = 0 := by
  rw [sqEichU, map_mul, toAdd_mul, map_inv, toAdd_inv, toAdd_map_zpowZtwo,
    toAdd_nu_sqPivot_selected nu' hsigma hx0, mul_one, neg_add_cancel]

variable (h nu' j) in
/-- **The Eichler frame** at handle `j`, with `V`-dressings of weight `e, e', 2e', d`:

```text
m = ( σ·V^e , x₀·V^{e'} , x₁·V^{2e'} , U·V^d , V )
```

with every other letter left standing.  The `2e'` on the `x₁`-slot is forced by the `L_sq`
core's own row `ν(x₁) = 2ν(x₀)`, which the frame must respect slot by slot. -/
noncomputable def sqEichFrame (e e' d : ℤ_[2]) : Fin (sqRank h) → (DSq h : Type) :=
  fun i =>
    if (i : ℕ) = 0 then dsqSigma h * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) e else
    if (i : ℕ) = 1 then dsqX0 h * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) e' else
    if (i : ℕ) = 2 then dsqX1 h * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) (2 * e') else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then
      sqEichU h nu' j * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) d else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then sqEichV h nu' j else
    sqGen h i

variable {e e' d : ℤ_[2]}

@[simp] theorem sqEichFrame_zero :
    sqEichFrame h nu' j e e' d 0 = dsqSigma h * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) e := by
  simp only [sqEichFrame, sqVal_zero]
  norm_num

@[simp] theorem sqEichFrame_one :
    sqEichFrame h nu' j e e' d 1 = dsqX0 h * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) e' := by
  simp only [sqEichFrame, sqVal_one]
  norm_num

@[simp] theorem sqEichFrame_two :
    sqEichFrame h nu' j e e' d 2
      = dsqX1 h * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) (2 * e') := by
  simp only [sqEichFrame, sqVal_two]
  norm_num

@[simp] theorem sqEichFrame_handleU :
    sqEichFrame h nu' j e e' d (sqHandleIdxU j)
      = sqEichU h nu' j * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) d := by
  simp only [sqEichFrame]
  rw [if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega)]
  simp

@[simp] theorem sqEichFrame_handleV :
    sqEichFrame h nu' j e e' d (sqHandleIdxV j) = sqEichV h nu' j := by
  simp only [sqEichFrame]
  rw [if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val, sqHandleIdxV_val]; omega)]
  simp

theorem sqEichFrame_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    sqEichFrame h nu' j e e' d (sqHandleIdxU j') = sqGen h (sqHandleIdxU j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqEichFrame]
  rw [if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val, sqHandleIdxV_val]; omega)]

theorem sqEichFrame_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    sqEichFrame h nu' j e e' d (sqHandleIdxV j') = sqGen h (sqHandleIdxV j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqEichFrame]
  rw [if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val, sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega)]

/-- **The λ-row of the Eichler frame is the standard one, unconditionally.**  Both `U` and `V`
are `λ`-trivial, and so is every `V`-dressing. -/
theorem sqEichFrame_nuLam (i : Fin (sqRank h)) :
    nuLam h (sqEichFrame h nu' j e e' d i) = nuLam h (sqGen h i) := by
  refine Multiplicative.toAdd.injective ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · show toAdd (nuLam h (sqEichFrame h nu' j e e' d 0)) = toAdd (nuLam h (dsqSigma h))
    rw [sqEichFrame_zero, toAdd_mul_zpow, toAdd_nuLam_sqEichV, mul_zero, add_zero]
  · show toAdd (nuLam h (sqEichFrame h nu' j e e' d 1)) = toAdd (nuLam h (dsqX0 h))
    rw [sqEichFrame_one, toAdd_mul_zpow, toAdd_nuLam_sqEichV, mul_zero, add_zero]
  · show toAdd (nuLam h (sqEichFrame h nu' j e e' d 2)) = toAdd (nuLam h (dsqX1 h))
    rw [sqEichFrame_two, toAdd_mul_zpow, toAdd_nuLam_sqEichV, mul_zero, add_zero]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrame_handleU, toAdd_mul_zpow, toAdd_nuLam_sqEichV, mul_zero, add_zero,
        toAdd_nuLam_sqEichU, nuLam_handleU, toAdd_one]
    · rw [sqEichFrame_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrame_handleV, toAdd_nuLam_sqEichV, nuLam_handleV, toAdd_one]
    · rw [sqEichFrame_handleV_ne hjj]

/-- **The ν-row of the Eichler frame is the standard marking's**, at handle `j`.  The other
handles are untouched, so their rows must already vanish — vacuous at `h = 1`. -/
theorem sqEichFrame_nu (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hoth : ∀ j' : Fin h, j' ≠ j →
      nu' (sqGen h (sqHandleIdxU j')) = 1 ∧ nu' (sqGen h (sqHandleIdxV j')) = 1)
    (i : Fin (sqRank h)) : nu' (sqEichFrame h nu' j e e' d i) = nuSq h (sqGen h i) := by
  refine Multiplicative.toAdd.injective ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · show toAdd (nu' (sqEichFrame h nu' j e e' d 0)) = toAdd (nuSq h (dsqSigma h))
    rw [sqEichFrame_zero, toAdd_mul_zpow, toAdd_nu_sqEichV hsigma hx0, mul_zero, add_zero,
      hsigma, nuSq_sigma]
  · show toAdd (nu' (sqEichFrame h nu' j e e' d 1)) = toAdd (nuSq h (dsqX0 h))
    rw [sqEichFrame_one, toAdd_mul_zpow, toAdd_nu_sqEichV hsigma hx0, mul_zero, add_zero,
      hx0, nuSq_x0]
  · show toAdd (nu' (sqEichFrame h nu' j e e' d 2)) = toAdd (nuSq h (dsqX1 h))
    rw [sqEichFrame_two, toAdd_mul_zpow, toAdd_nu_sqEichV hsigma hx0, mul_zero, add_zero,
      toAdd_nu_dsqX1, hx0, nuSq_x1]
    simp
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrame_handleU, toAdd_mul_zpow, toAdd_nu_sqEichV hsigma hx0, mul_zero, add_zero,
        toAdd_nu_sqEichU hsigma hx0, nuSq_handleU, toAdd_one]
    · rw [sqEichFrame_handleU_ne hjj, (hoth j' hjj).1, nuSq_handleU]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrame_handleV, toAdd_nu_sqEichV hsigma hx0, nuSq_handleV, toAdd_one]
    · rw [sqEichFrame_handleV_ne hjj, (hoth j' hjj).2, nuSq_handleV]

end EichlerFrame

end SqCore

end Dyadic

end GQ2
