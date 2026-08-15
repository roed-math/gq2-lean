/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.ChiFreeClearing
import GQ2.Dyadic.SqCore.EichlerSeeds

/-!
# The χ-free seeds: forced rows, and the admissible-marking frame of the search

**Lane SQ, the P2′ residue** — companion to `GQ2/Dyadic/SqCore/ChiFreeClearing.lean` and to
`docs/dyadic/chifree-clearing-note.md`.  Two independent contributions.  Only the second is
from the retargeted machine search; the first is inherited from `EichlerSeeds.lean`'s scaffold
lemma, which predates the retargeting (item 1 below says so):

## 1. The forced `x₁`-row survives the retargeting

`EichlerSeeds.lean`'s `sqEichlerSub_toAdd_nu_beta2` is a statement about the **scaffold**
(`sqEichlerSub` plus `rel_fwd`), not about the χ-fields, so it applies verbatim to `SqNuSeed`:
for every marking, `ν'(β₂) = 2·ν'(β₀)`.  Hence `SqNuSeed.nu_beta2` — the χ-free seed's
`x₁`-correction is invisible to every marking meeting the widened hypothesis — and
`SqNuSeed.nu_x1`, the `x₁`-row clause that `sqNuMoveAt_of_seed` does not state.

This is the balance table's forced row `β̄₂ = 2β̄₀ + λ·t̄` of the χ-free note §"balance",
proved in the form the table needs: `sqEichlerSub_toAdd_nu_beta2` puts no condition on the
marking at all, so the `λ·t̄` term is invisible whatever the coefficient `λ` is, and the table
line is a consequence of the relator rather than a search constraint.

## 2. The admissible markings the seed fields quantify over

The search recipe of the note ("β-slots must have zero `σ̄`- and `ū`-coordinates; `ρ` must
have `σ̄`-coordinate `k` and `ū`-coordinate `0`") is read here off the seed fields.  Only the
*sufficient* direction is established below: none of §2's declarations is a necessity claim.
The hypothesis the fields quantify over pins three rows and forces a fourth, and leaves
everything else alone:
```
ν'(σ) = 1 ,  ν'(x₀) = 0 ,  ν'(x₁) = 0 (forced) ,  ν'(v_j) = 0 ,
ν'(u_j) free ,  and ν'(u_i), ν'(v_i) free for every handle i ≠ j .
```
`SqNuAdmissible` below is the name of that hypothesis, a `Prop` **on** markings rather than a
construction of any: the only marking exhibited in this file is the standard `nuSq h`, via
`sqNuAdmissible_nuSq`.  `SqNuSeed.toAdd_nu_rho_eq` unbundles the seed's `nu_rho` against one
admissible marking and `SqNuSeed.toAdd_nu_rho_eq_of_two` transports it between two of them
through the constant `k`.

The `x₁`-row being *forced to zero* (rather than free) is what admits `x̄₁`-dressed correction
words at all, and it is the mechanism the χ-pinned ansatz could not see: `χ_sq(x₁) = Y ≠ 1`
excluded those words from the old interface, and they are exactly what the widened search
sweeps.

## The frame here has since been widened

Read this file beside `GQ2/Dyadic/SqCore/NuSeedWide.lean`, which landed the same day.  The
four-slot scaffold used throughout below, `sqEichlerSub`, fixes the `v_j`-slot **literally**,
which is a restriction of the *search* and not of the target; `NuSeedWide.lean` releases that
slot, giving `SqNuSeedW` a fifth substitution slot with its own `ν`-field `SqNuSeedW.nu_rhoV`,
embedding the family below at `ρ_v = 1` via `SqNuSeedW.ofNuSeed`, and recording that the
class-4 obstruction of the banked report is an artifact of the search's linearization rather
than an invariant of the group.  Nothing proved here is affected; it is the ansatz that has
moved on.

## Axiom hygiene

Everything here prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`).  No census
axiom is reachable; census unchanged at **11**.  §3 commits the prints for four of the eight
declarations.
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

/-! ## §2 The admissible markings, and the `ρ`-row against them

The seed's ν-fields quantify over a *family* of markings, not one marking: the two selected
core rows and the vanishing `v_j`-row leave `ν'(u_j)` free, and leave both rows of every
handle `i ≠ j` untouched.  The two `ρ`-declarations below unbundle that quantifier, one
against a single admissible marking and one between two of them.  Neither forms a difference
of markings, and neither produces the search recipe's `ū`-coordinate condition: that step also
needs two admissible markings differing in `ν'(u_j)`, which nothing here exhibits. -/

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

/-- **Unbundling the seed's `ρ`-field**: if a word has row `k` against *every* admissible
marking then its row is `k` against any single one, with the seed's three hypotheses packed
into `SqNuAdmissible`.  This is the shape in which the search recipe's `σ̄`-coordinate
condition is used; the recipe's `ū`-coordinate condition needs, in addition, two admissible
markings differing in `ν'(u_j)`, which this file does not supply. -/
theorem SqNuSeed.toAdd_nu_rho_eq {j : Fin h} {k : ℤ_[2]} (S : SqNuSeed h j k)
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}
    (ha : SqNuAdmissible h j nu') : toAdd (nu' S.rho) = k :=
  S.nu_rho nu' ha.1 ha.2.1 ha.2.2

/-- **Transitivity through `k`**: any two admissible markings assign `ρ` the same row.  This
gives the recipe's "`ū`-coordinate `0`" only once the family is known to contain two
admissible markings differing in `ν'(u_j)`; that is expected but is not proved here, the sole
admissible marking exhibited in this file being `nuSq h`. -/
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
