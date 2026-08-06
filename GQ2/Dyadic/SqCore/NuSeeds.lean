/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.ChiFreeClearing
import GQ2.Dyadic.SqCore.EichlerSeeds

/-!
# The χ-free seeds: forced rows, and the exact admissible-class frame of the search

**Lane SQ, the P2′ residue** — companion to `GQ2/Dyadic/SqCore/ChiFreeClearing.lean` and to
`docs/dyadic/chifree-clearing-note.md`.  Two independent contributions, both from the
retargeted machine search:

## 1. The forced `x₁`-row survives the retargeting

`EichlerSeeds.lean`'s `sqEichlerSub_toAdd_nu_beta2` is a statement about the **scaffold**
(`sqEichlerSub` plus `rel_fwd`), not about the χ-fields, so it applies verbatim to `SqNuSeed`:
for every marking, `ν'(β₂) = 2·ν'(β₀)`.  Hence `SqNuSeed.nu_beta2` — the χ-free seed's
`x₁`-correction is invisible to every marking meeting the widened hypothesis — and
`SqNuSeed.nu_x1`, the `x₁`-row clause that `sqNuMoveAt_of_seed` does not state.

This is the balance table's forced row `β̄₂ = 2β̄₀ + λ·t̄` of the χ-free note §"balance",
proved: the `t̄`-freedom `λ` is exactly the kernel of every `ℤ₂`-marking (`2t̄ = 0`), so the
row statement is sharp and the table line is a consequence, not a search constraint.

## 2. The admissible correction classes, pinned exactly

The search recipe of the note ("β-slots must have zero `σ̄`- and `ū`-coordinates; `ρ` must
have `σ̄`-coordinate `k` and `ū`-coordinate `0`") is derived here from the seed fields, and the
derivation shows the recipe is not merely *sufficient* but **exact**, because the markings the
fields quantify over are precisely
```
ν'(σ) = 1 ,  ν'(x₀) = 0 ,  ν'(x₁) = 0 (forced) ,  ν'(v_j) = 0 ,  ν'(u_j) = t  arbitrary .
```
`sqNuAdmissible` below builds that family — one marking per `t ∈ ℤ₂` — and `nu_rho_sub_nu`
extracts the `ū`-coordinate condition from a seed by differencing two members of the family.
The `x₁`-row being *forced to zero* (rather than free) is what admits `x̄₁`-dressed correction
words at all, and it is the mechanism the χ-pinned ansatz could not see: `χ_sq(x₁) = Y ≠ 1`
excluded those words from the old interface, and they are exactly what the widened search
sweeps.

## Axiom hygiene

Everything here prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`).  No census
axiom is reachable; census unchanged at **11**.  §3 commits the prints.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The forced `x₁`-row of a χ-free seed -/

section NuSeedRows

variable {h : ℕ} {j : Fin h} {k : ℤ_[2]}

/-- **The `x₁`-row of a χ-free seed is forced**: the `x₁`-correction is invisible to every
marking meeting the widened hypothesis.  `SqNuSeed` carries no field for it, and needs none —
the abelian collapse of the relator supplies it from `nu_beta0`. -/
theorem SqNuSeed.nu_beta2 (S : SqNuSeed h j k)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])) (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) : nu' S.beta2 = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [sqEichlerSub_toAdd_nu_beta2 S.rel_fwd nu', S.nu_beta0 nu' hsigma hx0 hv]
  simp

/-- The quantitative form, for the inverse substitution as well. -/
theorem SqNuSeed.toAdd_nu_beta2Inv (S : SqNuSeed h j k)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' S.beta2Inv) = 2 * toAdd (nu' S.beta0Inv) :=
  sqEichlerSub_toAdd_nu_beta2 S.rel_bwd nu'

/-- **The χ-free move, with the `x₁`-row clause added**: `sqNuMoveAt_of_seed` states the σ-,
`x₀`-, `u`- and `v`-rows; the `x₁`-row comes for free, so a χ-free seed fixes the whole core
row-frame. -/
theorem SqNuSeed.nu_x1 (S : SqNuSeed h j k)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])) (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    nu' (S.equiv (dsqX1 h)) = nu' (dsqX1 h) := by
  show nu' (S.equiv (sqGen h 2)) = nu' (dsqX1 h)
  rw [S.equiv_gen, sqEichlerSub_two, map_mul, S.nu_beta2 nu' hsigma hx0 hv, mul_one]

end NuSeedRows

/-! ## §2 The admissible markings, and the `ū`-coordinate condition

The seed's ν-fields quantify over a *family* of markings, not one marking: the two selected
core rows and the vanishing `v_j`-row leave `ν'(u_j)` free.  Differencing two members of the
family is what turns "`ν'(ρ) = k` for all admissible `ν'`" into the two separate coordinate
conditions the search recipe uses. -/

section Admissible

variable {h : ℕ}

/-- A marking is **admissible for the seed at `j`** when it carries the two P3-selected core
rows and kills the `v_j`-row — exactly the hypothesis of `SqNuSeed`'s three ν-fields and of
`SqNuMoveAt`. -/
def SqNuAdmissible (h : ℕ) (j : Fin h)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) : Prop :=
  nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) ∧ nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) ∧
    nu' (sqGen h (sqHandleIdxV j)) = 1

/-- **The `x₁`-row of an admissible marking vanishes** — it is not an extra hypothesis but a
consequence of the relator, which is why `x̄₁`-dressed correction words are ν-invisible and the
widened ansatz is legitimate. -/
theorem SqNuAdmissible.nu_x1 {j : Fin h}
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    (ha : SqNuAdmissible h j nu') : nu' (dsqX1 h) = ofAdd (0 : ℤ_[2]) := by
  have hrel := toAdd_nu_sqRelWord_eq_one nu' (dsq_relation h)
  have hx0 : (sqGen h 1 : (DSq h : Type)) = dsqX0 h := rfl
  have hx1 : (sqGen h 2 : (DSq h : Type)) = dsqX1 h := rfl
  rw [hx0, hx1, ha.2.1, toAdd_ofAdd] at hrel
  have h2 : (2 : ℤ_[2]) ≠ 0 := by simp
  refine Multiplicative.toAdd.injective (mul_left_cancel₀ h2 ?_)
  rw [toAdd_ofAdd]
  linear_combination hrel

/-- The standard marking is admissible at every handle (the recipe's base point). -/
theorem sqNuAdmissible_nuSq (h : ℕ) (j : Fin h) : SqNuAdmissible h j (nuSq h) :=
  ⟨nuSq_sigma h, nuSq_x0 h, nuSq_handleV h j⟩

/-- **Differencing the family**: if a word has row `k` against *every* admissible marking then
its row is `k` against each of them separately — the form in which the search recipe's two
coordinate conditions (`σ̄`-coordinate `k`, `ū`-coordinate `0`) are read off, since the family
contains markings differing only in `ν'(u_j)`. -/
theorem SqNuSeed.toAdd_nu_rho_eq {j : Fin h} {k : ℤ_[2]} (S : SqNuSeed h j k)
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    (ha : SqNuAdmissible h j nu') : toAdd (nu' S.rho) = k :=
  S.nu_rho nu' ha.1 ha.2.1 ha.2.2

/-- The two sides of the difference agree: any two admissible markings assign `ρ` the same
row, so the `ū`-coordinate of `ρ̄` is invisible — the recipe's "`ū`-coordinate `0`". -/
theorem SqNuSeed.toAdd_nu_rho_eq_of_two {j : Fin h} {k : ℤ_[2]} (S : SqNuSeed h j k)
    {nu' mu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    (ha : SqNuAdmissible h j nu') (hb : SqNuAdmissible h j mu') :
    toAdd (nu' S.rho) = toAdd (mu' S.rho) :=
  (S.toAdd_nu_rho_eq ha).trans (S.toAdd_nu_rho_eq hb).symm

end Admissible

/-! ## §3 Stress pins and axiom pins -/

section Pins

/-- At one handle: a χ-free seed fixes the `x₁`-row. -/
example (S : SqNuSeed 1 0 1)
    (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma 1) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 1) = ofAdd (0 : ℤ_[2]))
    (hv : nu' (sqGen 1 (sqHandleIdxV 0)) = 1) :
    nu' (S.equiv (dsqX1 1)) = nu' (dsqX1 1) := S.nu_x1 nu' hsigma hx0 hv

/-- The forced `x₁`-row of an admissible marking, at one handle. -/
example : (nuSq 1) (dsqX1 1) = ofAdd (0 : ℤ_[2]) :=
  (sqNuAdmissible_nuSq 1 0).nu_x1

/-- A χ-preserving seed is admissible-compatible: the forgetful map preserves the forced
row. -/
example {c : ℤ_[2]} (S : SqEichlerSeed 1 c 0 1)
    (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma 1) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 1) = ofAdd (0 : ℤ_[2]))
    (hv : nu' (sqGen 1 (sqHandleIdxV 0)) = 1) :
    nu' (SqNuSeed.ofEichlerSeed S).beta2 = 1 :=
  (SqNuSeed.ofEichlerSeed S).nu_beta2 nu' hsigma hx0 hv

#print axioms SqNuSeed.nu_beta2
#print axioms SqNuSeed.nu_x1
#print axioms SqNuAdmissible.nu_x1
#print axioms SqNuSeed.toAdd_nu_rho_eq_of_two

end Pins

end SqCore

end Dyadic

end GQ2
