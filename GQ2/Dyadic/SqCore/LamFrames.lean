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
handle).  ⚠ **That equation is false** — see "The relator identity is **false**" below; the
reduction is what survives, the ansatz is not.

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

## ⚠ The relator identity is **false**

`SqEichRelWord h` is **refuted** at every `h ≥ 1` in `SqCore/EichRefutation.lean`
(`not_sqEichRelWord`), with the explicit witness `ν' = nuSel h j 0 1`: at that selected marking
*no* `(e, e', d)` kills the relator.  So §3's implication
`sqLamMarkTransitivity_of_eichRelWord` is a true theorem with a **false hypothesis** for `h ≥ 1`,
and this file's contribution to the residual is §1 (the characterization) plus the machinery — the
surjectivity criterion of §2b and the clearing-step composition of §2c — not the ansatz itself.

Three facts here point at the same conclusion, and are worth keeping:

* the ansatz *is* satisfiable somewhere — at the standard marking the Eichler frame at
  `(e, e', d) = (0, 0, 0)` is literally the identity frame (`sqEichFrame_nuSq_zero`);
* ⚠ it is **rigid** — §4 shows the `d`-slot only *conjugates*
  (`sqEichFrame_handleComm`, `sqRelWord_sqEichFrame_one_d`), so `d` is invisible modulo `γ₃`,
  the class-two balance of `docs/dyadic/eichler-reduction-note.md` fixes `(e, e')` outright
  (`e' = 1`, `e = 2 + c₀` at `ν'(u_j) = 1`), and from class three on the five-word ansatz has a
  single parameter acting by conjugation;
* ⚠ it is **asymmetric** — the four moved slots are dressed by powers of `V` and by nothing else,
  so the frame can subtract pivot from `u_j` but has no `U`-dressing with which to clear a
  `v_j`-row.  That is exactly what the refutation exploits.

What §3 still buys is that the obligation is a **single closed equation in `D_sq h`** for any such
family: a widened ansatz inherits §2a's rows verbatim and needs only its own surjectivity check.

## Headline 3 — the transposed family, and the mix

§5 builds `sqEichFrameT`, the same construction with the two cleared letters exchanged
(`mᵀ = (σ·U^f, x₀·U^{f'}, x₁·U^{2f'}, U, V·U^d)`), and the "verbatim" claim above is exact: the
row proofs of §2a use only that both `U` and `V` are `λ`-trivial and `ν'`-trivial, and §2b's
recovery argument is symmetric in the two letters.  §3's induction is factored through
`SqClearingStep` — the five clauses `sqEichStep` actually delivers — so both families feed it, and
because the family is chosen *inside* the induction, so does the **disjunction**
`SqEichRelWordMix` (§6): at each selected marking and handle, either family may be the one that
kills the relator.

⚠ **`SqEichRelWordMix h` is also false for `h ≥ 1`** (`SqCore/EichRefutation.lean`,
`not_sqEichRelWordMix`), and the two families die for *different* reasons at *different* markings:
`sqEichFrame` at any marking with `ν'(v_j) ≠ 0`, `sqEichFrameT` at any marking with `ν'(u_j) ≠ 0`.
The refutation's own Heisenberg homomorphism does **not** transpose
(`refHom_sqRelWord_sqEichFrameT_survives`) — a second one is needed, and the two together kill the
mix at `nuSel h j 1 1`.  What that says about the *residual* is nothing: §1 quantifies over all
frames, and the wider repair named in §4 — dressing the four moved slots by arbitrary `λ`-trivial,
`ν'`-trivial elements rather than by powers of one letter — is untouched by this mechanism,
because it is precisely the "the dressings all die with the dressing letter" step that fails
there.

## Contents

* **§1** `sqFrames_of_lamMarkTransitivity` and `sqLamMarkTransitivity_iff_frames`;
* **§2** `sqEichV`, `sqEichU`, `sqEichFrame` and their rows (§2a), surjectivity of any
  endomorphism realizing the frame (§2b), and the one-handle clearing step (§2c);
* **§3** `SqClearingStep`, the clearing induction, and `SqEichRelWord` reduced through it;
* **§4** the shape of the relator identity: `sqEichFrame_handleComm`,
  `sqRelWord_sqEichFrame_one`, `sqRelWord_sqEichFrame_one_d`;
* **§5** the transposed family `sqEichFrameT`: rows (§5a), surjectivity (§5b), the clearing step
  (§5c), and the same `γ₃`-rigidity (§5d);
* **§6** `SqEichRelWordT`, `SqEichRelWordMix`, and the residual reduced to either;
* **§7** stress pins, **§8** committed axiom prints.

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

/-- **A clearing step**, family-agnostically: at every selected marking and every handle there is
a `λ`-preserving automorphism which keeps the marking selected, clears that handle's two rows and
**leaves every other handle's rows exactly where they were**.

This is precisely the conclusion of `sqEichStep`, extracted so that the induction below does not
mention any particular frame family: *any* family with these five clauses discharges the
residual, and two families may be mixed handle by handle. -/
def SqClearingStep (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
          nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧ nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1 ∧
            nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1 ∧
              ∀ j' : Fin h, j' ≠ j →
                nu' (Ψ (sqGen h (sqHandleIdxU j'))) = nu' (sqGen h (sqHandleIdxU j')) ∧
                  nu' (Ψ (sqGen h (sqHandleIdxV j'))) = nu' (sqGen h (sqHandleIdxV j'))

/-- **The Eichler relator identity**, as a statement about words: at every selected marking and
every handle, some `V`-dressing weights `(e, e', d)` kill the relator.

⚠ **This is false for `h ≥ 1`** (`SqCore/EichRefutation.lean`, `not_sqEichRelWord`).  It is kept
because the implication below is the reusable half — any *other* frame family with the same rows
plugs into the same reduction — and because a named false hypothesis is easier to keep track of
than an unnamed one. -/
def SqEichRelWord (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ e e' d : ℤ_[2], sqRelWord (sqEichFrame h nu' j e e' d) = 1

/-- The clearing induction: a selected marking whose handles from index `n` on are already
cleared is corrected onto `ν_sq`.  `n = h` is the general case, `n = 0` the base. -/
private theorem sqLamMarkTransitivity_aux (H : SqClearingStep h) (n : ℕ)
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
    · obtain ⟨Ψ₁, hlam₁, hs₁, hx₁, hU₁, hV₁, hoth₁⟩ := H nu' ⟨n, hn⟩ hsigma hx0
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

/-- **The residual, from a clearing step.**  This is the reusable half of §3: the induction
composes `h` clearing steps in index order, and cares about nothing except the five clauses of
`SqClearingStep`. -/
theorem sqLamMarkTransitivity_of_clearingStep (H : SqClearingStep h) : SqLamMarkTransitivity h :=
  fun nu' hsigma hx0 =>
    sqLamMarkTransitivity_aux H h nu' hsigma hx0 fun j' hj' =>
      absurd j'.isLt (by omega)

/-- The Eichler relator identity supplies a clearing step (§2c). -/
theorem sqClearingStep_of_eichRelWord (H : SqEichRelWord h) : SqClearingStep h := by
  intro nu' j hsigma hx0
  obtain ⟨e, e', d, hrel⟩ := H nu' j hsigma hx0
  exact sqEichStep hsigma hx0 hrel

/-- **The residual, in one word equation.**  The relator identity at every selected marking and
every handle discharges `SqLamMarkTransitivity h` — no rows, no surjectivity, no inverse
substitution, no composition identity, and no restriction on `h`. -/
theorem sqLamMarkTransitivity_of_eichRelWord (H : SqEichRelWord h) : SqLamMarkTransitivity h :=
  sqLamMarkTransitivity_of_clearingStep (sqClearingStep_of_eichRelWord H)

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

/-! ## §4 The shape of the relator identity: the `d`-slot only conjugates

`V^d` commutes with `V`, so the moved handle commutator is the `d = 0` one **conjugated** by
`V^d` (`sqEichFrame_handleComm`), and at one handle the entire `d`-dependence of the relator is
the single commutator `[[U, V], V^d]` (`sqRelWord_sqEichFrame_one_d`).

⚠ **This is a rigidity statement, and it is bad news for the ansatz as written.**  `[U, V]` is
already a commutator, so `[[U, V], V^d]` lies in the *third* term of the lower central series:
`d` is invisible modulo `γ₃`.  That is exactly why the class-two balance of
`docs/dyadic/eichler-reduction-note.md` forces `e` and `e'` (its `a₀ = −k`, `a₂ = 2a₀`,
`a₁ = −k(2+c)`) and leaves its `a_u` — our `d` — undetermined: `a_u` enters `Δ₂` only through
`[ρ̄, v̄]`, and its `v̄`-component pairs `v̄` with itself.  Counting what is left:

* class two fixes `(e, e')` outright — the balance is rigid, not a family;
* from class three on the ansatz has **one** parameter, `d`, and it acts only by conjugation;
* the `x₁`-slot's weight `2e'` is not free either: the rows permit any `V`-power there
  (`λ(V) = ν'(V) = 0`), so `2e'` is again the class-two balance's `a₂ = 2a₀` and not a row
  condition, the module docstring's `L_sq`-row gloss notwithstanding.

So the five-word Eichler ansatz is a **zero-parameter** ansatz beyond class three, and every
class from four up has to come out right by itself.  It does not:
`SqCore/EichRefutation.lean` refutes it outright, and by a mechanism cruder than any of this —
the frame's `v`-slot is the letter it moved, so killing `V` kills all four dressings at once.  A
refutation of *this* frame says little about the residual (§1 quantifies over all frames); the
useful conclusion is that the natural widening — dressing the four moved slots by arbitrary
`λ`-trivial, `ν'`-trivial elements rather than by `V`-powers — costs nothing on any row and is
where the parameters have to come from. -/

section RelWordShape

variable {h : ℕ}

/-- A `ℤ₂`-power of `x` commutes with `x`.  (Local restatement: `ZtwoPowering` is upstream.) -/
theorem commute_zpowZtwo_self (x : (DSq h : Type)) (k : ℤ_[2]) :
    Commute (zpowZtwo (isProP_DSq h) x k) x := by
  have hx : zpowZtwo (isProP_DSq h) x 1 = x := zpowZtwo_one_exp _ x
  show zpowZtwo (isProP_DSq h) x k * x = x * zpowZtwo (isProP_DSq h) x k
  calc zpowZtwo (isProP_DSq h) x k * x
      = zpowZtwo (isProP_DSq h) x k * zpowZtwo (isProP_DSq h) x 1 := by rw [hx]
    _ = zpowZtwo (isProP_DSq h) x (k + 1) := (zpowZtwo_add _ x k 1).symm
    _ = zpowZtwo (isProP_DSq h) x (1 + k) := by rw [add_comm]
    _ = zpowZtwo (isProP_DSq h) x 1 * zpowZtwo (isProP_DSq h) x k := zpowZtwo_add _ x 1 k
    _ = x * zpowZtwo (isProP_DSq h) x k := by rw [hx]

variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}
  {e e' d : ℤ_[2]}

/-- **The `d`-slot only conjugates**: the frame's handle commutator at `j` is `[U, V]`
conjugated by `V^d`. -/
theorem sqEichFrame_handleComm :
    commP (sqEichFrame h nu' j e e' d (sqHandleIdxU j))
        (sqEichFrame h nu' j e e' d (sqHandleIdxV j))
      = conjP (commP (sqEichU h nu' j) (sqEichV h nu' j))
          (zpowZtwo (isProP_DSq h) (sqEichV h nu' j) d) := by
  rw [sqEichFrame_handleU, sqEichFrame_handleV, commP_mul_left,
    commP_eq_one_of_commute (commute_zpowZtwo_self _ _), mul_one]

/-- At one handle the handle block is a single commutator. -/
private theorem handleWord_one {G : Type*} [Group G] (u v : Fin 1 → G) :
    handleWord u v = commP (u 0) (v 0) := by
  rw [handleWord, ← List.ofFn_eq_map]
  simp

/-- **The relator of the Eichler frame at one handle, unpacked.** -/
theorem sqRelWord_sqEichFrame_one
    (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])) (e e' d : ℤ_[2]) :
    sqRelWord (sqEichFrame 1 nu' 0 e e' d)
      = sqWord (dsqSigma 1 * zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) e)
            (dsqX0 1 * zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) e')
            (dsqX1 1 * zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) (2 * e'))
          * conjP (commP (sqEichU 1 nu' 0) (sqEichV 1 nu' 0))
              (zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) d) := by
  rw [sqRelWord, handleWord_one, sqEichFrame_zero, sqEichFrame_one, sqEichFrame_two,
    sqEichFrame_handleComm]

/-- **The whole `d`-dependence of the relator is one commutator** — and it is a commutator *of a
commutator*, hence a `γ₃`-element: `d` is invisible modulo `γ₃`. -/
theorem sqRelWord_sqEichFrame_one_d
    (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])) (e e' d : ℤ_[2]) :
    sqRelWord (sqEichFrame 1 nu' 0 e e' d)
      = sqRelWord (sqEichFrame 1 nu' 0 e e' 0) *
          commP (commP (sqEichU 1 nu' 0) (sqEichV 1 nu' 0))
            (zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) d) := by
  rw [sqRelWord_sqEichFrame_one, sqRelWord_sqEichFrame_one, SectionThree.zpowZtwo_zero]
  simp only [conjP, commP, inv_one, one_mul, mul_one]
  group

/-- **The relator identity at one handle, as an equation about the core word alone**: the dressed
core must be the `V^d`-conjugate of `[V, U]`.  Nothing else is left. -/
theorem sqRelWord_sqEichFrame_one_eq_one_iff
    (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])) (e e' d : ℤ_[2]) :
    sqRelWord (sqEichFrame 1 nu' 0 e e' d) = 1 ↔
      sqWord (dsqSigma 1 * zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) e)
          (dsqX0 1 * zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) e')
          (dsqX1 1 * zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) (2 * e'))
        = conjP (commP (sqEichV 1 nu' 0) (sqEichU 1 nu' 0))
            (zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) d) := by
  have hconj : conjP (commP (sqEichV 1 nu' 0) (sqEichU 1 nu' 0))
      (zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) d)
      = (conjP (commP (sqEichU 1 nu' 0) (sqEichV 1 nu' 0))
          (zpowZtwo (isProP_DSq 1) (sqEichV 1 nu' 0) d))⁻¹ := by
    simp only [conjP, commP]
    group
  rw [sqRelWord_sqEichFrame_one, hconj, mul_eq_one_iff_eq_inv]

end RelWordShape

/-! ## §5 The transposed family: dressing by `U`

`sqEichFrame` is **asymmetric** — its four moved slots are dressed by powers of `V`, the very
letter it moved in order to clear the `v_j`-row, and that is exactly what
`SqCore/EichRefutation.lean` exploits.  The transposed family exchanges the two letters
throughout:

```text
mᵀ = ( σ·U^f , x₀·U^{f'} , x₁·U^{2f'} , U , V·U^d )        (other letters unmoved)
```

Everything in §2 transposes **verbatim**, and for a reason worth stating: the row proofs use only
that both cleared letters are `λ`-trivial (`toAdd_nuLam_sqEichU`, `toAdd_nuLam_sqEichV`) and
`ν'`-trivial at a selected marking (`toAdd_nu_sqEichU`, `toAdd_nu_sqEichV`), which is symmetric in
`U` and `V`; and §2b's recovery argument is symmetric too, with `U` now the bare slot off which
every dressing strips.  So the transposed family again reduces to a single relator identity, and
§3's composition accepts it through `SqClearingStep`. -/

section TransposedFrame

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

variable (h nu' j) in
/-- **The transposed Eichler frame** at handle `j`, with `U`-dressings of weight `f, f', 2f', d`:

```text
mᵀ = ( σ·U^f , x₀·U^{f'} , x₁·U^{2f'} , U , V·U^d )
```

`sqEichFrame` with the roles of the two cleared letters exchanged: the bare slot is now the
`u`-slot, and the `v`-slot carries the free dressing. -/
noncomputable def sqEichFrameT (f f' d : ℤ_[2]) : Fin (sqRank h) → (DSq h : Type) :=
  fun i =>
    if (i : ℕ) = 0 then dsqSigma h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) f else
    if (i : ℕ) = 1 then dsqX0 h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) f' else
    if (i : ℕ) = 2 then dsqX1 h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) (2 * f') else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then sqEichU h nu' j else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then
      sqEichV h nu' j * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) d else
    sqGen h i

variable {f f' d : ℤ_[2]}

@[simp] theorem sqEichFrameT_zero :
    sqEichFrameT h nu' j f f' d 0 = dsqSigma h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) f := by
  simp only [sqEichFrameT, sqVal_zero]
  norm_num

@[simp] theorem sqEichFrameT_one :
    sqEichFrameT h nu' j f f' d 1 = dsqX0 h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) f' := by
  simp only [sqEichFrameT, sqVal_one]
  norm_num

@[simp] theorem sqEichFrameT_two :
    sqEichFrameT h nu' j f f' d 2
      = dsqX1 h * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) (2 * f') := by
  simp only [sqEichFrameT, sqVal_two]
  norm_num

@[simp] theorem sqEichFrameT_handleU :
    sqEichFrameT h nu' j f f' d (sqHandleIdxU j) = sqEichU h nu' j := by
  simp only [sqEichFrameT]
  rw [if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega)]
  simp

@[simp] theorem sqEichFrameT_handleV :
    sqEichFrameT h nu' j f f' d (sqHandleIdxV j)
      = sqEichV h nu' j * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) d := by
  simp only [sqEichFrameT]
  rw [if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val, sqHandleIdxV_val]; omega)]
  simp

theorem sqEichFrameT_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    sqEichFrameT h nu' j f f' d (sqHandleIdxU j') = sqGen h (sqHandleIdxU j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqEichFrameT]
  rw [if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val, sqHandleIdxV_val]; omega)]

theorem sqEichFrameT_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    sqEichFrameT h nu' j f f' d (sqHandleIdxV j') = sqGen h (sqHandleIdxV j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqEichFrameT]
  rw [if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxU_val, sqHandleIdxV_val]; omega),
    if_neg (by simp only [sqHandleIdxV_val]; omega)]

/-! ### §5a The rows transpose verbatim -/

/-- **The λ-row of the transposed frame is the standard one, unconditionally.** -/
theorem sqEichFrameT_nuLam (i : Fin (sqRank h)) :
    nuLam h (sqEichFrameT h nu' j f f' d i) = nuLam h (sqGen h i) := by
  refine Multiplicative.toAdd.injective ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · show toAdd (nuLam h (sqEichFrameT h nu' j f f' d 0)) = toAdd (nuLam h (dsqSigma h))
    rw [sqEichFrameT_zero, toAdd_mul_zpow, toAdd_nuLam_sqEichU, mul_zero, add_zero]
  · show toAdd (nuLam h (sqEichFrameT h nu' j f f' d 1)) = toAdd (nuLam h (dsqX0 h))
    rw [sqEichFrameT_one, toAdd_mul_zpow, toAdd_nuLam_sqEichU, mul_zero, add_zero]
  · show toAdd (nuLam h (sqEichFrameT h nu' j f f' d 2)) = toAdd (nuLam h (dsqX1 h))
    rw [sqEichFrameT_two, toAdd_mul_zpow, toAdd_nuLam_sqEichU, mul_zero, add_zero]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrameT_handleU, toAdd_nuLam_sqEichU, nuLam_handleU, toAdd_one]
    · rw [sqEichFrameT_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrameT_handleV, toAdd_mul_zpow, toAdd_nuLam_sqEichU, mul_zero, add_zero,
        toAdd_nuLam_sqEichV, nuLam_handleV, toAdd_one]
    · rw [sqEichFrameT_handleV_ne hjj]

/-- The `σ`-row of the transposed frame, with **no** hypothesis on the other handles. -/
theorem nu_sqEichFrameT_zero (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrameT h nu' j f f' d 0) = ofAdd (1 : ℤ_[2]) := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrameT_zero, toAdd_mul_zpow, toAdd_nu_sqEichU hsigma hx0, mul_zero, add_zero, hsigma]

/-- The `x₀`-row of the transposed frame. -/
theorem nu_sqEichFrameT_one (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrameT h nu' j f f' d 1) = ofAdd (0 : ℤ_[2]) := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrameT_one, toAdd_mul_zpow, toAdd_nu_sqEichU hsigma hx0, mul_zero, add_zero, hx0]

/-- **Handle `j` is cleared**: its `u`-row vanishes on the transposed frame. -/
theorem nu_sqEichFrameT_handleU_self (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrameT h nu' j f f' d (sqHandleIdxU j)) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrameT_handleU, toAdd_nu_sqEichU hsigma hx0, toAdd_one]

/-- **Handle `j` is cleared**: its `v`-row vanishes on the transposed frame. -/
theorem nu_sqEichFrameT_handleV_self (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    nu' (sqEichFrameT h nu' j f f' d (sqHandleIdxV j)) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichFrameT_handleV, toAdd_mul_zpow, toAdd_nu_sqEichU hsigma hx0,
    toAdd_nu_sqEichV hsigma hx0, mul_zero, add_zero, toAdd_one]

/-- **The ν-row of the transposed frame is the standard marking's**, at handle `j`. -/
theorem sqEichFrameT_nu (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hoth : ∀ j' : Fin h, j' ≠ j →
      nu' (sqGen h (sqHandleIdxU j')) = 1 ∧ nu' (sqGen h (sqHandleIdxV j')) = 1)
    (i : Fin (sqRank h)) : nu' (sqEichFrameT h nu' j f f' d i) = nuSq h (sqGen h i) := by
  refine Multiplicative.toAdd.injective ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · show toAdd (nu' (sqEichFrameT h nu' j f f' d 0)) = toAdd (nuSq h (dsqSigma h))
    rw [nu_sqEichFrameT_zero hsigma hx0, nuSq_sigma]
  · show toAdd (nu' (sqEichFrameT h nu' j f f' d 1)) = toAdd (nuSq h (dsqX0 h))
    rw [nu_sqEichFrameT_one hsigma hx0, nuSq_x0]
  · show toAdd (nu' (sqEichFrameT h nu' j f f' d 2)) = toAdd (nuSq h (dsqX1 h))
    rw [sqEichFrameT_two, toAdd_mul_zpow, toAdd_nu_sqEichU hsigma hx0, mul_zero, add_zero,
      toAdd_nu_dsqX1, hx0, nuSq_x1]
    simp
  · by_cases hjj : j' = j
    · subst hjj
      rw [nu_sqEichFrameT_handleU_self hsigma hx0, nuSq_handleU]
    · rw [sqEichFrameT_handleU_ne hjj, (hoth j' hjj).1, nuSq_handleU]
  · by_cases hjj : j' = j
    · subst hjj
      rw [nu_sqEichFrameT_handleV_self hsigma hx0, nuSq_handleV]
    · rw [sqEichFrameT_handleV_ne hjj, (hoth j' hjj).2, nuSq_handleV]

/-! ### §5b Surjectivity, with `U` as the bare slot

The recovery argument of §2b is symmetric in the two cleared letters: `U` is now a slot outright,
so every `U`-dressing strips off and `σ, x₀, x₁, V` come back; the pivot is a word in `σ` and
`x₀`; and the two handle letters return as `u_j = w^{t}·U` and `v_j = V·w^{s}`. -/

/-- **Any endomorphism realizing the transposed frame is surjective.** -/
theorem sqEichFrameT_surjective_of_hom (Φ : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hΦ : ∀ i, Φ (sqGen h i) = sqEichFrameT h nu' j f f' d i) : Function.Surjective Φ := by
  have hpow : ∀ (x : (DSq h : Type)) (k : ℤ_[2]),
      Φ (zpowZtwo (isProP_DSq h) x k) = zpowZtwo (isProP_DSq h) (Φ x) k :=
    fun x k => map_zpowZtwo (isProP_DSq h) (isProP_DSq h) Φ x k
  have hU : Φ (sqGen h (sqHandleIdxU j)) = sqEichU h nu' j := by
    rw [hΦ, sqEichFrameT_handleU]
  have hstrip : ∀ (a : (DSq h : Type)) (i : Fin (sqRank h)) (k : ℤ_[2]),
      sqEichFrameT h nu' j f f' d i = a * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) k →
        a ∈ Set.range Φ := by
    refine fun a i k hi => ⟨sqGen h i *
      (zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxU j)) k)⁻¹, ?_⟩
    rw [map_mul, map_inv, hΦ, hi, hpow, hU, mul_inv_cancel_right]
  obtain ⟨a, ha⟩ := hstrip (dsqSigma h) 0 f sqEichFrameT_zero
  obtain ⟨b, hb⟩ := hstrip (dsqX0 h) 1 f' sqEichFrameT_one
  obtain ⟨c, hc⟩ := hstrip (dsqX1 h) 2 (2 * f') sqEichFrameT_two
  obtain ⟨g, hg⟩ := hstrip (sqEichV h nu' j) (sqHandleIdxV j) d sqEichFrameT_handleV
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
    · exact ⟨sqGen h (sqHandleIdxU j'), by rw [hΦ, sqEichFrameT_handleU_ne hjj]⟩
  · by_cases hjj : j' = j
    · subst hjj
      refine ⟨g * zpowZtwo (isProP_DSq h) (a * (zpowZtwo (isProP_DSq h) b sqPivotExp)⁻¹)
        (toAdd (nu' (sqGen h (sqHandleIdxV j')))), ?_⟩
      rw [map_mul, hg, hpow, hw, sqEichV_mul_pivotPow]
    · exact ⟨sqGen h (sqHandleIdxV j'), by rw [hΦ, sqEichFrameT_handleV_ne hjj]⟩

/-- **The transposed frame's lift is surjective as soon as it exists.** -/
theorem sqEichFrameT_surjective (hrel : sqRelWord (sqEichFrameT h nu' j f f' d) = 1) :
    Function.Surjective (sqLiftHom h (isProP_DSq h) (sqEichFrameT h nu' j f f' d) hrel) :=
  sqEichFrameT_surjective_of_hom _ (sqLiftHom_gen h (isProP_DSq h) _ hrel)

/-! ### §5c The transposed clearing step -/

/-- **The one-handle clearing step for the transposed family** — the same five clauses, so the
two families are interchangeable inputs to §3's composition. -/
theorem sqEichStepT (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hrel : sqRelWord (sqEichFrameT h nu' j f f' d) = 1) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
        nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧ nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1 ∧
          nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1 ∧
            ∀ j' : Fin h, j' ≠ j →
              nu' (Ψ (sqGen h (sqHandleIdxU j'))) = nu' (sqGen h (sqHandleIdxU j')) ∧
                nu' (Ψ (sqGen h (sqHandleIdxV j'))) = nu' (sqGen h (sqHandleIdxV j')) := by
  refine ⟨sqAutOfMark hrel (sqEichFrameT_surjective hrel), fun x => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hext : (nuLam h).comp (autHom (sqAutOfMark hrel (sqEichFrameT_surjective hrel)))
        = nuLam h :=
      dsq_hom_ext _ _ fun i => by
        show nuLam h (sqAutOfMark hrel (sqEichFrameT_surjective hrel) (sqGen h i))
          = nuLam h (sqGen h i)
        rw [sqAutOfMark_gen, sqEichFrameT_nuLam]
    exact DFunLike.congr_fun hext x
  · show nu' (sqAutOfMark hrel (sqEichFrameT_surjective hrel) (sqGen h 0)) = ofAdd (1 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqEichFrameT_zero hsigma hx0]
  · show nu' (sqAutOfMark hrel (sqEichFrameT_surjective hrel) (sqGen h 1)) = ofAdd (0 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqEichFrameT_one hsigma hx0]
  · rw [sqAutOfMark_gen, nu_sqEichFrameT_handleU_self hsigma hx0]
  · rw [sqAutOfMark_gen, nu_sqEichFrameT_handleV_self hsigma hx0]
  · exact fun j' hjj => ⟨by rw [sqAutOfMark_gen, sqEichFrameT_handleU_ne hjj],
      by rw [sqAutOfMark_gen, sqEichFrameT_handleV_ne hjj]⟩

/-! ### §5d The rigidity transposes too

`U^d` commutes with `U`, so the `d`-slot again only conjugates and is invisible modulo `γ₃`.  The
transposed family is a **zero-parameter** ansatz beyond class three for exactly the same reason as
the original. -/

/-- **The `d`-slot only conjugates**, transposed. -/
theorem sqEichFrameT_handleComm :
    commP (sqEichFrameT h nu' j f f' d (sqHandleIdxU j))
        (sqEichFrameT h nu' j f f' d (sqHandleIdxV j))
      = conjP (commP (sqEichU h nu' j) (sqEichV h nu' j))
          (zpowZtwo (isProP_DSq h) (sqEichU h nu' j) d) := by
  rw [sqEichFrameT_handleU, sqEichFrameT_handleV,
    commP_mul_zpowZtwo_right (isProP_DSq h) (sqEichU h nu' j) (sqEichV h nu' j) d]

end TransposedFrame

section TransposedShape

/-- **The relator of the transposed frame at one handle, unpacked.** -/
theorem sqRelWord_sqEichFrameT_one
    (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])) (f f' d : ℤ_[2]) :
    sqRelWord (sqEichFrameT 1 nu' 0 f f' d)
      = sqWord (dsqSigma 1 * zpowZtwo (isProP_DSq 1) (sqEichU 1 nu' 0) f)
            (dsqX0 1 * zpowZtwo (isProP_DSq 1) (sqEichU 1 nu' 0) f')
            (dsqX1 1 * zpowZtwo (isProP_DSq 1) (sqEichU 1 nu' 0) (2 * f'))
          * conjP (commP (sqEichU 1 nu' 0) (sqEichV 1 nu' 0))
              (zpowZtwo (isProP_DSq 1) (sqEichU 1 nu' 0) d) := by
  rw [sqRelWord, handleWord_one, sqEichFrameT_zero, sqEichFrameT_one, sqEichFrameT_two,
    sqEichFrameT_handleComm]

/-- **The whole `d`-dependence of the transposed relator is one `γ₃`-commutator**, exactly as in
§4: the transposed parameter buys no class-two freedom either. -/
theorem sqRelWord_sqEichFrameT_one_d
    (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])) (f f' d : ℤ_[2]) :
    sqRelWord (sqEichFrameT 1 nu' 0 f f' d)
      = sqRelWord (sqEichFrameT 1 nu' 0 f f' 0) *
          commP (commP (sqEichU 1 nu' 0) (sqEichV 1 nu' 0))
            (zpowZtwo (isProP_DSq 1) (sqEichU 1 nu' 0) d) := by
  rw [sqRelWord_sqEichFrameT_one, sqRelWord_sqEichFrameT_one, SectionThree.zpowZtwo_zero]
  simp only [conjP, commP, inv_one, one_mul, mul_one]
  group

end TransposedShape

/-! ## §6 The two families, mixed

Both families deliver the *same* clearing step, so §3's induction accepts either at each handle —
and, since the choice is made handle by handle inside the induction, it accepts a **disjunction**.
`SqEichRelWordMix` is therefore strictly weaker than either `SqEichRelWord` or `SqEichRelWordT`,
and still discharges the whole `h ≥ 1` residual. -/

section Mixed

variable {h : ℕ}

/-- **The transposed relator identity**: at every selected marking and every handle, some
`U`-dressing weights `(f, f', d)` kill the relator. -/
def SqEichRelWordT (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ f f' d : ℤ_[2], sqRelWord (sqEichFrameT h nu' j f f' d) = 1

/-- **The mixed identity**: at every selected marking and every handle, *one of the two* families
kills the relator.  The family may be chosen per marking and per handle. -/
def SqEichRelWordMix (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      (∃ e e' d : ℤ_[2], sqRelWord (sqEichFrame h nu' j e e' d) = 1) ∨
        ∃ f f' d : ℤ_[2], sqRelWord (sqEichFrameT h nu' j f f' d) = 1

theorem sqEichRelWordMix_of_eichRelWord (H : SqEichRelWord h) : SqEichRelWordMix h :=
  fun nu' j hsigma hx0 => Or.inl (H nu' j hsigma hx0)

theorem sqEichRelWordMix_of_eichRelWordT (H : SqEichRelWordT h) : SqEichRelWordMix h :=
  fun nu' j hsigma hx0 => Or.inr (H nu' j hsigma hx0)

/-- The mixed identity supplies a clearing step: whichever disjunct holds, §2c or §5c applies. -/
theorem sqClearingStep_of_eichRelWordMix (H : SqEichRelWordMix h) : SqClearingStep h := by
  intro nu' j hsigma hx0
  rcases H nu' j hsigma hx0 with ⟨e, e', d, hrel⟩ | ⟨f, f', d, hrel⟩
  · exact sqEichStep hsigma hx0 hrel
  · exact sqEichStepT hsigma hx0 hrel

/-- **The residual, from the mixed identity.**  This is the weakest word-level hypothesis the two
Eichler families jointly support. -/
theorem sqLamMarkTransitivity_of_eichRelWordMix (H : SqEichRelWordMix h) :
    SqLamMarkTransitivity h :=
  sqLamMarkTransitivity_of_clearingStep (sqClearingStep_of_eichRelWordMix H)

/-- The transposed identity supplies a clearing step. -/
theorem sqClearingStep_of_eichRelWordT (H : SqEichRelWordT h) : SqClearingStep h :=
  sqClearingStep_of_eichRelWordMix (sqEichRelWordMix_of_eichRelWordT H)

/-- **The residual, from the transposed identity alone.** -/
theorem sqLamMarkTransitivity_of_eichRelWordT (H : SqEichRelWordT h) : SqLamMarkTransitivity h :=
  sqLamMarkTransitivity_of_clearingStep (sqClearingStep_of_eichRelWordT H)

/-- …and hence the handle stratum at every unit exponent, from the mixed identity. -/
theorem sqHandleMixFixesCore_of_eichRelWordMix {c : ℤ_[2]} (hc : IsUnit c) (hh : 0 < h)
    (H : SqEichRelWordMix h) : SqHandleMixFixesCore h c :=
  sqHandleMixFixesCore_of_lamMarkTransitivity hc hh (sqLamMarkTransitivity_of_eichRelWordMix H)

end Mixed

/-! ## §7 Stress pins -/

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

/-- **The transposed ansatz is satisfiable too.**  At the standard marking the transposed frame at
`(f, f', d) = (0, 0, 0)` is again the identity frame, so §5's relator identity is not an empty
demand either. -/
theorem sqEichFrameT_nuSq_zero (h : ℕ) (j : Fin h) : sqEichFrameT h (nuSq h) j 0 0 0 = sqGen h := by
  have hV : sqEichV h (nuSq h) j = sqGen h (sqHandleIdxV j) := by
    rw [sqEichV, nuSq_handleV, toAdd_one, SectionThree.zpowZtwo_zero, inv_one, mul_one]
  have hU : sqEichU h (nuSq h) j = sqGen h (sqHandleIdxU j) := by
    rw [sqEichU, nuSq_handleU, toAdd_one, SectionThree.zpowZtwo_zero, inv_one, one_mul]
  refine funext fun i => ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqEichFrameT_zero, SectionThree.zpowZtwo_zero, mul_one]; rfl
  · rw [sqEichFrameT_one, SectionThree.zpowZtwo_zero, mul_one]; rfl
  · rw [sqEichFrameT_two, mul_zero, SectionThree.zpowZtwo_zero, mul_one]; rfl
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrameT_handleU, hU]
    · rw [sqEichFrameT_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqEichFrameT_handleV, SectionThree.zpowZtwo_zero, mul_one, hV]
    · rw [sqEichFrameT_handleV_ne hjj]

/-- Stress: hence the transposed relator identity is satisfiable. -/
example (h : ℕ) (j : Fin h) : sqRelWord (sqEichFrameT h (nuSq h) j 0 0 0) = 1 := by
  rw [sqEichFrameT_nuSq_zero]
  exact dsq_relation h

/-- Stress: the mixed hypothesis is genuinely weaker — *either* family implies it. -/
example (h : ℕ) (H : SqEichRelWord h) : SqEichRelWordMix h := sqEichRelWordMix_of_eichRelWord H

example (h : ℕ) (H : SqEichRelWordT h) : SqEichRelWordMix h := sqEichRelWordMix_of_eichRelWordT H

/-- Stress: `h = 0` runs through the mixed reduction too. -/
example : SqLamMarkTransitivity 0 :=
  sqLamMarkTransitivity_of_eichRelWordMix fun _ j _ _ => absurd j.isLt (by omega)

/-- Stress: the transposed `λ`-row is unconditional as well — the row proofs really do use only
`λ`- and `ν'`-triviality of the dressing letter, which both letters have. -/
example (h : ℕ) (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    (f f' d : ℤ_[2]) (i : Fin (sqRank h)) :
    nuLam h (sqEichFrameT h nu' j f f' d i) = nuLam h (sqGen h i) := sqEichFrameT_nuLam i

/-- Stress: surjectivity of the transposed frame is likewise relator-free. -/
example (h : ℕ) (j : Fin h) (Φ : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hΦ : ∀ i, Φ (sqGen h i) = sqEichFrameT h (nuSq h) j 0 0 0 i) : Function.Surjective Φ :=
  sqEichFrameT_surjective_of_hom Φ hΦ

end StressTests

/-! ## §8 Axiom pins

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
#print axioms SqClearingStep
#print axioms sqLamMarkTransitivity_of_clearingStep
#print axioms SqEichRelWord
#print axioms sqClearingStep_of_eichRelWord
#print axioms sqLamMarkTransitivity_of_eichRelWord
#print axioms sqHandleMixFixesCore_of_eichRelWord
#print axioms sqLamMarkTransitivity_one_of_eichRelWord
#print axioms commute_zpowZtwo_self
#print axioms sqEichFrame_handleComm
#print axioms sqRelWord_sqEichFrame_one
#print axioms sqRelWord_sqEichFrame_one_d
#print axioms sqRelWord_sqEichFrame_one_eq_one_iff
#print axioms sqEichFrameT
#print axioms sqEichFrameT_nuLam
#print axioms nu_sqEichFrameT_zero
#print axioms nu_sqEichFrameT_one
#print axioms nu_sqEichFrameT_handleU_self
#print axioms nu_sqEichFrameT_handleV_self
#print axioms sqEichFrameT_nu
#print axioms sqEichFrameT_surjective_of_hom
#print axioms sqEichFrameT_surjective
#print axioms sqEichStepT
#print axioms sqEichFrameT_handleComm
#print axioms sqRelWord_sqEichFrameT_one
#print axioms sqRelWord_sqEichFrameT_one_d
#print axioms SqEichRelWordT
#print axioms SqEichRelWordMix
#print axioms sqClearingStep_of_eichRelWordMix
#print axioms sqLamMarkTransitivity_of_eichRelWordMix
#print axioms sqClearingStep_of_eichRelWordT
#print axioms sqLamMarkTransitivity_of_eichRelWordT
#print axioms sqHandleMixFixesCore_of_eichRelWordMix
#print axioms sqEichFrame_nuSq_zero
#print axioms sqEichFrameT_nuSq_zero

end AxiomPins

end SqCore

end Dyadic

end GQ2
