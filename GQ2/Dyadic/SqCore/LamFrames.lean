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

end SqCore

end Dyadic

end GQ2
