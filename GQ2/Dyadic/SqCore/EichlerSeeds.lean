/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.EichlerReduction

/-!
# The `L_sq` Eichler seeds: the forced rows of the four-slot scaffold

**Lane SQ, the P2 residue** — companion to `GQ2/Dyadic/SqCore/EichlerReduction.lean` and to
`docs/dyadic/eichler-reduction-note.md`.

`SqEichlerSeed h c j k` (`EichlerReduction.lean` §4) carries `ν`-fields for the σ- and
`x₀`-slots but **none** for the `x₁`-slot, on the ground that "the forced row makes it
automatic" (the seed's docstring).  This file proves that claim, and sharpens it: the
`x₁`-correction's row is not merely invisible but *determined*, by the abelian collapse of the
relator alone.

## The forced row

Applying any continuous `ℤ₂`-marking to a relator-killing four-slot substitution and using the
abelian collapse `sqRelWord_comm` (`ρ_sq = −4x̄₀ + 2x̄₁`) twice — once at the substituted
marking, once at `sqGen` (`dsq_relation`) — the `x₀`- and `x₁`-rows of the ambient group cancel
and what survives is

```
2·ν'(β₂) = 4·ν'(β₀)   in ℤ₂ ,   hence   ν'(β₂) = 2·ν'(β₀)
```

(`ℤ₂` is a domain, so the `2` cancels).  This is `sqEichlerSub_toAdd_nu_beta2`, and it holds
for **every** marking — no `v_j`-row hypothesis, no χ-hypothesis, no unit parameter.  Two
consequences:

* `SqEichlerSeed.nu_beta2` — the missing field is a theorem: a seed's `x₁`-correction is
  invisible to every marking meeting the `v_j`-row hypothesis.  So `sqEichlerMoveAt_of_seed`
  could carry the `x₁`-row clause too, at no cost to the search.
* `sqEichlerSub_nu_beta2_eq_two_beta0` records the *quantitative* form, which is the degree-one
  line of the class-two balance table of `EichlerReduction.lean` §3 (`−4a₀ + 2a₂ = 0`,
  i.e. `a₂ = 2a₀`).  That line of the table is therefore **not** an input to the search: it is
  forced, and any search that imposes it is imposing a consequence rather than a constraint.

By contrast the σ-slot field `nu_beta1` is *not* derivable this way: `σ` does not occur in the
abelianized relator (`ρ_sq` has no `σ̄`-coordinate), so the relator says nothing about `ν'(β₁)`
and the seed must carry that field.  The asymmetry between `nu_beta0`/`nu_beta1` (carried) and
the `x₁`-row (forced) is exactly the `−4x̄₀ + 2x̄₁` shape of the collapse.

## Axiom hygiene

Everything here prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`); the file
consumes only `EichlerReduction`'s scaffold and the h-generic collapse lemmas.  Census
unchanged at **11**.  §3 commits the prints.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The abelian collapse of a relator-killing marking

One lemma, stated for an arbitrary marking rather than for the scaffold, so that both uses —
the substituted marking and `sqGen` itself — go through the same computation. -/

section Collapse

variable {h : ℕ}

/-- **The additive form of the abelian collapse**: any `ℤ₂`-marking of a marking killing the
`L_sq` relator satisfies the row relation `4·ν'(m 1) = 2·ν'(m 2)` — the additive shape of
`ρ_sq = −4x̄₀ + 2x̄₁`. -/
theorem toAdd_nu_sqRelWord_eq_one (nu' : ContinuousMonoidHom (DSq h : Type)
    (Multiplicative ℤ_[2])) {m : Fin (sqRank h) → (DSq h : Type)} (hrel : sqRelWord m = 1) :
    (2 : ℤ_[2]) * toAdd (nu' (m 2)) = 4 * toAdd (nu' (m 1)) := by
  have hval : ((nu' (m 1)) ^ 4)⁻¹ * (nu' (m 2)) ^ 2 = 1 := by
    have h1 : nu' (sqRelWord m) = 1 := by rw [hrel, map_one]
    rwa [map_sqRelWord, sqRelWord_comm] at h1
  have hadd := congrArg Multiplicative.toAdd hval
  rw [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_one] at hadd
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hadd
  linear_combination hadd

/-- **The forced `x₁`-row of the four-slot scaffold**: if the substitution kills the relator,
the `x₁`-correction's row is exactly twice the `x₀`-correction's row, against **every**
marking.  This is the degree-one line `−4a₀ + 2a₂ = 0` of the class-two balance
(`EichlerReduction.lean` §3), proved rather than posited. -/
theorem sqEichlerSub_toAdd_nu_beta2 {j : Fin h} {β₁ β₀ β₂ ρ : (DSq h : Type)}
    (hrel : sqRelWord (sqEichlerSub h j β₁ β₀ β₂ ρ) = 1)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' β₂) = 2 * toAdd (nu' β₀) := by
  have hsub := toAdd_nu_sqRelWord_eq_one nu' hrel
  have hgen := toAdd_nu_sqRelWord_eq_one nu' (dsq_relation h)
  simp only [sqEichlerSub_one, sqEichlerSub_two, map_mul, toAdd_mul] at hsub
  have hx0 : (sqGen h 1 : (DSq h : Type)) = dsqX0 h := rfl
  have hx1 : (sqGen h 2 : (DSq h : Type)) = dsqX1 h := rfl
  rw [hx0, hx1] at hgen
  have h2 : (2 : ℤ_[2]) ≠ 0 := by simp
  refine mul_left_cancel₀ h2 ?_
  linear_combination hsub - hgen

end Collapse

/-! ## §2 The missing seed field, as a theorem

`SqEichlerSeed` carries `nu_beta0` and `nu_beta1` but no `x₁`-row field.  §1 supplies it: the
`x₁`-correction is invisible to exactly the markings the `x₀`-correction is invisible to. -/

section SeedRows

variable {h : ℕ} {c k : ℤ_[2]} {j : Fin h}

/-- **The `x₁`-row of a seed is forced**: a seed's `x₁`-correction is invisible to every
marking meeting the `v_j`-row hypothesis — the field `SqEichlerSeed` deliberately omits.  (The
`v_j`-row hypothesis enters only through `nu_beta0`; the relator does the rest.) -/
theorem SqEichlerSeed.nu_beta2 (S : SqEichlerSeed h c j k)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) : nu' S.beta2 = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichlerSub_toAdd_nu_beta2 S.rel_fwd nu', S.nu_beta0 nu' hv]
  simp

/-- The same for the inverse substitution of a seed. -/
theorem SqEichlerSeed.nu_beta2Inv_eq_two (S : SqEichlerSeed h c j k)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' S.beta2Inv) = 2 * toAdd (nu' S.beta0Inv) :=
  sqEichlerSub_toAdd_nu_beta2 S.rel_bwd nu'

/-- **The seed's move, with the `x₁`-row clause added.**  `sqEichlerMoveAt_of_seed` states the
σ-, `x₀`-, `u`- and `v`-rows; §1 shows the `x₁`-row comes for free, so a seed in fact fixes the
whole core row-frame, not just the two rows the target statement names. -/
theorem SqEichlerSeed.nu_x1 (S : SqEichlerSeed h c j k)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    nu' (S.equiv (dsqX1 h)) = nu' (dsqX1 h) := by
  show nu' (S.equiv (sqGen h 2)) = nu' (dsqX1 h)
  rw [S.equiv_gen, sqEichlerSub_two, map_mul, S.nu_beta2 nu' hv, mul_one]

end SeedRows

/-! ## §3 Stress pins and axiom pins -/

section Pins

/-- The forced row is a statement about the scaffold, not about seeds: it needs only
`rel_fwd`. -/
example {h : ℕ} {j : Fin h} {β₁ β₀ β₂ ρ : (DSq h : Type)}
    (hrel : sqRelWord (sqEichlerSub h j β₁ β₀ β₂ ρ) = 1)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hz : nu' β₀ = 1) : nu' β₂ = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichlerSub_toAdd_nu_beta2 hrel nu', hz]
  simp

/-- At one handle, the canonical exponent: a seed fixes the `x₁`-row too. -/
example (S : SqEichlerSeed 1 sqPivotExp 0 1)
    (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2]))
    (hv : nu' (sqGen 1 (sqHandleIdxV 0)) = 1) :
    nu' (S.equiv (dsqX1 1)) = nu' (dsqX1 1) := S.nu_x1 nu' hv

#print axioms toAdd_nu_sqRelWord_eq_one
#print axioms sqEichlerSub_toAdd_nu_beta2
#print axioms SqEichlerSeed.nu_beta2
#print axioms SqEichlerSeed.nu_x1

end Pins

end SqCore

end Dyadic

end GQ2
