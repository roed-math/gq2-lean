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
`v_j = V·w^{s}` and `u_j = w^{t}·U`.  So the whole residual collapses to the *single* relator
identity

```text
sqRelWord (sqEichFrame h ν' j e e' d) = 1        (`SqEichRelWord h`)
```

with no rows, no surjectivity, no inverse substitution, and no composition identity
(`sqLamMarkTransitivity_of_eichRelWord`, and `sqLamMarkTransitivity_one_of_eichRelWord` at one
handle).  That is the smallest form the residual has taken.

**Scope.**  `sqEichFrame_nu` reads *all* rows off a single frame and therefore carries a
hypothesis `hoth` — the other handles' rows already vanish — so one Eichler frame clears exactly
one handle.  That hypothesis is **not** needed for the reduction: §2c reads the same rows without
it and records that the frame leaves every other handle row *where it was*, so the markings
`ν'∘Ψ_j` can be cleared one handle at a time and the frames composed (§3's induction on the
number of uncleared handles).  `SqEichRelWord h` — the relator identity at every selected marking
and every handle — therefore discharges the residual at **every** `h`, not only at `h = 1`.  What
a one-handle solution has to supply for the general case is nothing extra: the marking produced
by a clearing step is again selected, so the same equation is being asked again.

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

The relator identity is **open**, and this file adds no evidence either way beyond one
satisfiability pin: at the *standard* marking the Eichler frame at `(e, e', d) = (0, 0, 0)` is
literally the identity frame (`sqEichFrame_nuSq_zero`), so the ansatz is not empty.  The bare
frame above is the *leading term*; the class-two balance of
`docs/dyadic/eichler-reduction-note.md` already prices its first correction (`e' = 1`,
`e = 2 + c₀`).  What §3 buys is that the obligation is now a **single closed equation in
`D_sq h`**, so a correction may be inserted in any slot without re-proving a single row.

## Contents

* **§1** `sqFrames_of_lamMarkTransitivity` and `sqLamMarkTransitivity_iff_frames`;
* **§2** `sqEichV`, `sqEichU`, `sqEichFrame` and their rows (§2a), surjectivity of any
  endomorphism realizing the frame (§2b), and the one-handle clearing step (§2c);
* **§3** `SqEichRelWord` and the residual reduced to it, at every `h`;
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

/-- The `σ`-row of the Eichler frame, with **no** hypothesis on the other handles. -/
theorem nu_sqEichFrame_zero (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrame h nu' j e e' d 0) = ofAdd (1 : ℤ_[2]) := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrame_zero, toAdd_mul_zpow, toAdd_nu_sqEichV hsigma hx0, mul_zero, add_zero, hsigma]

/-- The `x₀`-row of the Eichler frame. -/
theorem nu_sqEichFrame_one (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrame h nu' j e e' d 1) = ofAdd (0 : ℤ_[2]) := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrame_one, toAdd_mul_zpow, toAdd_nu_sqEichV hsigma hx0, mul_zero, add_zero, hx0]

/-- **Handle `j` is cleared**: its `u`-row vanishes on the frame. -/
theorem nu_sqEichFrame_handleU_self (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrame h nu' j e e' d (sqHandleIdxU j)) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrame_handleU, toAdd_mul_zpow, toAdd_nu_sqEichV hsigma hx0,
    toAdd_nu_sqEichU hsigma hx0, mul_zero, add_zero, toAdd_one]

/-- **Handle `j` is cleared**: its `v`-row vanishes on the frame. -/
theorem nu_sqEichFrame_handleV_self (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrame h nu' j e e' d (sqHandleIdxV j)) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrame_handleV, toAdd_nu_sqEichV hsigma hx0, toAdd_one]

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
    rw [nu_sqEichFrame_zero hsigma hx0, nuSq_sigma]
  · show toAdd (nu' (sqEichFrame h nu' j e e' d 1)) = toAdd (nuSq h (dsqX0 h))
    rw [nu_sqEichFrame_one hsigma hx0, nuSq_x0]
  · show toAdd (nu' (sqEichFrame h nu' j e e' d 2)) = toAdd (nuSq h (dsqX1 h))
    rw [sqEichFrame_two, toAdd_mul_zpow, toAdd_nu_sqEichV hsigma hx0, mul_zero, add_zero,
      toAdd_nu_dsqX1, hx0, nuSq_x1]
    simp
  · by_cases hjj : j' = j
    · subst hjj
      rw [nu_sqEichFrame_handleU_self hsigma hx0, nuSq_handleU]
    · rw [sqEichFrame_handleU_ne hjj, (hoth j' hjj).1, nuSq_handleU]
  · by_cases hjj : j' = j
    · subst hjj
      rw [nu_sqEichFrame_handleV_self hsigma hx0, nuSq_handleV]
    · rw [sqEichFrame_handleV_ne hjj, (hoth j' hjj).2, nuSq_handleV]

/-! ### §2b Surjectivity of the frame's lift

The five words regenerate `D_sq h`.  `V` is a slot outright, so every `V`-dressing strips off
and `σ, x₀, x₁, U` come back; the pivot `w = σ·x₀^{−c₀}` is then a word in `σ` and `x₀`; and the
two handle letters return as `v_j = V·w^{s}` and `u_j = w^{t}·U`.  Every other letter is a slot.
Nothing here uses the relator: surjectivity is a property of the five words. -/

/-- `V` recovers `v_j`, by construction. -/
theorem sqEichV_mul_pivotPow :
    sqEichV h nu' j *
        zpowZtwo (isProP_DSq h) (sqPivot h) (toAdd (nu' (sqGen h (sqHandleIdxV j))))
      = sqGen h (sqHandleIdxV j) := by
  rw [sqEichV, inv_mul_cancel_right]

/-- `U` recovers `u_j`, by construction. -/
theorem pivotPow_mul_sqEichU :
    zpowZtwo (isProP_DSq h) (sqPivot h) (toAdd (nu' (sqGen h (sqHandleIdxU j)))) *
        sqEichU h nu' j = sqGen h (sqHandleIdxU j) := by
  rw [sqEichU, mul_inv_cancel_left]

/-- **Any endomorphism realizing the Eichler frame is surjective.**  Stated for an arbitrary
`Φ` rather than for `sqLiftHom`, so that it does not depend on the relator identity. -/
theorem sqEichFrame_surjective_of_hom (Φ : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hΦ : ∀ i, Φ (sqGen h i) = sqEichFrame h nu' j e e' d i) : Function.Surjective Φ := by
  have hpow : ∀ (x : (DSq h : Type)) (k : ℤ_[2]),
      Φ (zpowZtwo (isProP_DSq h) x k) = zpowZtwo (isProP_DSq h) (Φ x) k :=
    fun x k => map_zpowZtwo (isProP_DSq h) (isProP_DSq h) Φ x k
  have hV : Φ (sqGen h (sqHandleIdxV j)) = sqEichV h nu' j := by
    rw [hΦ, sqEichFrame_handleV]
  have hstrip : ∀ (a : (DSq h : Type)) (i : Fin (sqRank h)) (k : ℤ_[2]),
      sqEichFrame h nu' j e e' d i = a * zpowZtwo (isProP_DSq h) (sqEichV h nu' j) k →
        a ∈ Set.range Φ := by
    refine fun a i k hi => ⟨sqGen h i *
      (zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxV j)) k)⁻¹, ?_⟩
    rw [map_mul, map_inv, hΦ, hi, hpow, hV, mul_inv_cancel_right]
  obtain ⟨a, ha⟩ := hstrip (dsqSigma h) 0 e sqEichFrame_zero
  obtain ⟨b, hb⟩ := hstrip (dsqX0 h) 1 e' sqEichFrame_one
  obtain ⟨c, hc⟩ := hstrip (dsqX1 h) 2 (2 * e') sqEichFrame_two
  obtain ⟨g, hg⟩ := hstrip (sqEichU h nu' j) (sqHandleIdxU j) d sqEichFrame_handleU
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
        (toAdd (nu' (sqGen h (sqHandleIdxU j')))) * g, ?_⟩
      rw [map_mul, hpow, hw, hg, pivotPow_mul_sqEichU]
    · exact ⟨sqGen h (sqHandleIdxU j'), by rw [hΦ, sqEichFrame_handleU_ne hjj]⟩
  · by_cases hjj : j' = j
    · subst hjj
      refine ⟨sqGen h (sqHandleIdxV j') *
        zpowZtwo (isProP_DSq h) (a * (zpowZtwo (isProP_DSq h) b sqPivotExp)⁻¹)
          (toAdd (nu' (sqGen h (sqHandleIdxV j')))), ?_⟩
      rw [map_mul, hV, hpow, hw, sqEichV_mul_pivotPow]
    · exact ⟨sqGen h (sqHandleIdxV j'), by rw [hΦ, sqEichFrame_handleV_ne hjj]⟩

/-- **The Eichler frame's lift is surjective as soon as it exists.**  So the relator identity is
the *only* input the frame form still needs. -/
theorem sqEichFrame_surjective (hrel : sqRelWord (sqEichFrame h nu' j e e' d) = 1) :
    Function.Surjective (sqLiftHom h (isProP_DSq h) (sqEichFrame h nu' j e e' d) hrel) :=
  sqEichFrame_surjective_of_hom _ (sqLiftHom_gen h (isProP_DSq h) _ hrel)

/-! ### §2c The clearing step

With the relator identity in hand at `(ν', j)` the frame is an automorphism (`sqAutOfMark`,
using §2b for surjectivity), it fixes `λ` pointwise, and it carries `ν'` to a marking that is
again **selected**, has handle `j` **cleared**, and leaves every *other* handle row exactly where
it was.  That last clause is what makes the handles clearable one at a time. -/

/-- **The one-handle clearing step.** -/
theorem sqEichStep (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hrel : sqRelWord (sqEichFrame h nu' j e e' d) = 1) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
        nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧ nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1 ∧
          nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1 ∧
            ∀ j' : Fin h, j' ≠ j →
              nu' (Ψ (sqGen h (sqHandleIdxU j'))) = nu' (sqGen h (sqHandleIdxU j')) ∧
                nu' (Ψ (sqGen h (sqHandleIdxV j'))) = nu' (sqGen h (sqHandleIdxV j')) := by
  refine ⟨sqAutOfMark hrel (sqEichFrame_surjective hrel), fun x => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hext : (nuLam h).comp (autHom (sqAutOfMark hrel (sqEichFrame_surjective hrel)))
        = nuLam h :=
      dsq_hom_ext _ _ fun i => by
        show nuLam h (sqAutOfMark hrel (sqEichFrame_surjective hrel) (sqGen h i))
          = nuLam h (sqGen h i)
        rw [sqAutOfMark_gen, sqEichFrame_nuLam]
    exact DFunLike.congr_fun hext x
  · show nu' (sqAutOfMark hrel (sqEichFrame_surjective hrel) (sqGen h 0)) = ofAdd (1 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqEichFrame_zero hsigma hx0]
  · show nu' (sqAutOfMark hrel (sqEichFrame_surjective hrel) (sqGen h 1)) = ofAdd (0 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqEichFrame_one hsigma hx0]
  · rw [sqAutOfMark_gen, nu_sqEichFrame_handleU_self hsigma hx0]
  · rw [sqAutOfMark_gen, nu_sqEichFrame_handleV_self hsigma hx0]
  · exact fun j' hjj => ⟨by rw [sqAutOfMark_gen, sqEichFrame_handleU_ne hjj],
      by rw [sqAutOfMark_gen, sqEichFrame_handleV_ne hjj]⟩

end EichlerFrame

/-! ## §3 The residual, reduced to the relator identity

`sqEichRelWord h` below is the *bare* word equation: at every selected marking and every handle,
some `(e, e', d)` kills the relator.  It implies the whole `h ≥ 1` residual.

The passage from one handle to `h` of them is the composition of `h` clearing steps: the marking
`ν'∘Ψ_j` produced by §2c is again selected and has one more handle cleared, so the induction runs
on the number of **uncleared** handles, taken in index order.  No new hypothesis is needed for
that — the `hoth` clause of `sqEichFrame_nu` is an artefact of reading all rows off a *single*
frame, and disappears once the frames are composed. -/

section Reduction

variable {h : ℕ}

/-- **The Eichler relator identity**, as a statement about words: at every selected marking and
every handle, some `V`-dressing weights `(e, e', d)` kill the relator.  This is the last
mathematical content of the `h ≥ 1` residual. -/
def SqEichRelWord (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ e e' d : ℤ_[2], sqRelWord (sqEichFrame h nu' j e e' d) = 1

/-- The clearing induction: a selected marking whose handles from index `n` on are already
cleared is corrected onto `ν_sq`.  `n = h` is the general case, `n = 0` the base. -/
private theorem sqLamMarkTransitivity_aux (H : SqEichRelWord h) (n : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])) (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hcl : ∀ j' : Fin h, n ≤ (j' : ℕ) →
      nu' (sqGen h (sqHandleIdxU j')) = 1 ∧ nu' (sqGen h (sqHandleIdxV j')) = 1) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ ∀ x, nu' (Ψ x) = nuSq h x := by
  induction n generalizing nu' with
  | zero =>
    exact ⟨ContinuousMulEquiv.refl _, fun _ => rfl,
      nu_eq_nuSq_of_core nu' hsigma hx0 (fun j' => (hcl j' (Nat.zero_le _)).1)
        (fun j' => (hcl j' (Nat.zero_le _)).2)⟩
  | succ n ih =>
    by_cases hn : n < h
    · obtain ⟨e, e', d, hrel⟩ := H nu' ⟨n, hn⟩ hsigma hx0
      obtain ⟨Ψ₁, hlam₁, hs₁, hx₁, hU₁, hV₁, hoth₁⟩ := sqEichStep hsigma hx0 hrel
      have hcl₁ : ∀ j' : Fin h, n ≤ (j' : ℕ) →
          (nu'.comp (autHom Ψ₁)) (sqGen h (sqHandleIdxU j')) = 1 ∧
            (nu'.comp (autHom Ψ₁)) (sqGen h (sqHandleIdxV j')) = 1 := by
        intro j' hj'
        by_cases hjj : j' = (⟨n, hn⟩ : Fin h)
        · subst hjj
          exact ⟨hU₁, hV₁⟩
        · have hlt : n + 1 ≤ (j' : ℕ) := by
            rcases Nat.lt_or_ge (j' : ℕ) (n + 1) with hgt | hge
            · exact absurd (Fin.val_injective (by omega : (j' : ℕ) = n)) hjj
            · exact hge
          exact ⟨((hoth₁ j' hjj).1).trans (hcl j' hlt).1,
            ((hoth₁ j' hjj).2).trans (hcl j' hlt).2⟩
      obtain ⟨Ψ₂, hlam₂, hval₂⟩ := ih (nu'.comp (autHom Ψ₁)) hs₁ hx₁ hcl₁
      refine ⟨Ψ₂.trans Ψ₁, fun x => ?_, fun x => ?_⟩
      · show nuLam h (Ψ₁ (Ψ₂ x)) = nuLam h x
        rw [hlam₁, hlam₂]
      · exact hval₂ x
    · exact ih nu' hsigma hx0 fun j' hj' => hcl j' (by have := j'.isLt; omega)

/-- **The residual, in one word equation.**  The relator identity at every selected marking and
every handle discharges `SqLamMarkTransitivity h` — no rows, no surjectivity, no inverse
substitution, no composition identity, and no restriction on `h`. -/
theorem sqLamMarkTransitivity_of_eichRelWord (H : SqEichRelWord h) : SqLamMarkTransitivity h :=
  fun nu' hsigma hx0 =>
    sqLamMarkTransitivity_aux H h nu' hsigma hx0 fun j' hj' =>
      absurd j'.isLt (by omega)

/-- …and hence `SqLamNuClearHypothesis`, and the handle stratum at every unit exponent. -/
theorem sqHandleMixFixesCore_of_eichRelWord {c : ℤ_[2]} (hc : IsUnit c) (hh : 0 < h)
    (H : SqEichRelWord h) : SqHandleMixFixesCore h c :=
  sqHandleMixFixesCore_of_lamMarkTransitivity hc hh (sqLamMarkTransitivity_of_eichRelWord H)

/-- **The one-handle form**, the smallest open instance: at `h = 1` the handle index is forced,
so the whole residual is the single family of word equations
`sqRelWord (sqEichFrame 1 ν' 0 e e' d) = 1`. -/
theorem sqLamMarkTransitivity_one_of_eichRelWord
    (H : ∀ nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma 1) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 1) = ofAdd (0 : ℤ_[2]) →
        ∃ e e' d : ℤ_[2], sqRelWord (sqEichFrame 1 nu' 0 e e' d) = 1) :
    SqLamMarkTransitivity 1 :=
  sqLamMarkTransitivity_of_eichRelWord fun nu' j hsigma hx0 => by
    rw [show j = 0 from Subsingleton.elim _ _]
    exact H nu' hsigma hx0

end Reduction

/-! ## §4 Stress pins -/

section StressTests

/-- **The Eichler ansatz is satisfiable.**  At the standard marking both handle letters are
already cleared, so the frame at `(e, e', d) = (0, 0, 0)` *is* the identity frame — the relator
identity is not an empty demand. -/
theorem sqEichFrame_nuSq_zero (h : ℕ) (j : Fin h) : sqEichFrame h (nuSq h) j 0 0 0 = sqGen h := by
  have hV : sqEichV h (nuSq h) j = sqGen h (sqHandleIdxV j) := by
    rw [sqEichV, nuSq_handleV, toAdd_one, SectionThree.zpowZtwo_zero, inv_one, mul_one]
  have hU : sqEichU h (nuSq h) j = sqGen h (sqHandleIdxU j) := by
    rw [sqEichU, nuSq_handleU, toAdd_one, SectionThree.zpowZtwo_zero, inv_one, one_mul]
  refine funext fun i => ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqEichFrame_zero, SectionThree.zpowZtwo_zero, mul_one]; rfl
  · rw [sqEichFrame_one, SectionThree.zpowZtwo_zero, mul_one]; rfl
  · rw [sqEichFrame_two, mul_zero, SectionThree.zpowZtwo_zero, mul_one]; rfl
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrame_handleU, SectionThree.zpowZtwo_zero, mul_one, hU]
    · rw [sqEichFrame_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrame_handleV, hV]
    · rw [sqEichFrame_handleV_ne hjj]

/-- Stress: hence the relator identity itself is satisfiable. -/
example (h : ℕ) (j : Fin h) : sqRelWord (sqEichFrame h (nuSq h) j 0 0 0) = 1 := by
  rw [sqEichFrame_nuSq_zero]
  exact dsq_relation h

/-- Stress: `h = 0` runs through the new reduction too — the word equation is vacuous there,
and the residual is a theorem, as `sqLamMarkTransitivity_zero` already says. -/
example : SqLamMarkTransitivity 0 :=
  sqLamMarkTransitivity_of_eichRelWord fun _ j _ _ => absurd j.isLt (by omega)

/-- Stress: the reduction is not vacuous in the other direction either — the residual *implies*
the frame form (§1), so the two sides of `sqLamMarkTransitivity_iff_frames` are both live. -/
example (H : SqLamMarkTransitivity 1) : SqNuClearHypothesis 1 :=
  sqNuClearHypothesis_of_lamMarkTransitivity H

/-- **The smallest open instance, in word form**: at one handle, carrying the marking
`(1, 0, 0, 1, 0)` onto `ν_sq` is now the assertion that *some* `(e, e', d)` kills the relator on
the Eichler frame over `nuSel 1 0 1 0`. -/
example (H : SqEichRelWord 1) :
    ∃ e e' d : ℤ_[2], sqRelWord (sqEichFrame 1 (nuSel 1 0 1 0) 0 e e' d) = 1 :=
  H (nuSel 1 0 1 0) 0 nuSel_sigma nuSel_x0

/-- Stress: surjectivity is genuinely independent of the relator — it is a statement about the
five words, and holds for the identity frame at the standard marking with no relator input. -/
example (h : ℕ) (j : Fin h) (Φ : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hΦ : ∀ i, Φ (sqGen h i) = sqEichFrame h (nuSq h) j 0 0 0 i) : Function.Surjective Φ :=
  sqEichFrame_surjective_of_hom Φ hΦ

/-- Stress: the `λ`-row of the frame is unconditional — no marking hypothesis at all. -/
example (h : ℕ) (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    (e e' d : ℤ_[2]) (i : Fin (sqRank h)) :
    nuLam h (sqEichFrame h nu' j e e' d i) = nuLam h (sqGen h i) := sqEichFrame_nuLam i

end StressTests

/-! ## §5 Axiom pins

Committed prints: the whole file is **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable. -/

section AxiomPins

#print axioms sqFrames_of_lamMarkTransitivity
#print axioms sqLamMarkTransitivity_iff_frames
#print axioms sqLamNuClearHypothesis_iff_frames
#print axioms toAdd_nu_sqPivot_selected
#print axioms sqEichV
#print axioms sqEichU
#print axioms sqEichFrame
#print axioms sqEichFrame_nuLam
#print axioms nu_sqEichFrame_zero
#print axioms nu_sqEichFrame_one
#print axioms nu_sqEichFrame_handleU_self
#print axioms nu_sqEichFrame_handleV_self
#print axioms sqEichFrame_nu
#print axioms sqEichV_mul_pivotPow
#print axioms pivotPow_mul_sqEichU
#print axioms sqEichFrame_surjective_of_hom
#print axioms sqEichFrame_surjective
#print axioms sqEichStep
#print axioms SqEichRelWord
#print axioms sqLamMarkTransitivity_of_eichRelWord
#print axioms sqHandleMixFixesCore_of_eichRelWord
#print axioms sqLamMarkTransitivity_one_of_eichRelWord
#print axioms sqEichFrame_nuSq_zero

end AxiomPins

end SqCore

end Dyadic

end GQ2
