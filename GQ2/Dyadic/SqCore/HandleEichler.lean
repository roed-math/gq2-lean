/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.PivotCoreMoves

/-!
# W42 — the `L_sq` handle stratum, cut to its irreducible form

**Lane SQ, the P2 residue.**  `SqCore/HandleMixFixesCore.lean` refuted `SqHandleMixFixesCore h c`
at every `c` missing the canonical exponent modulo `2`, and pinned the survivor:

```text
SqHandleMixFixesCore h c  ↔  IsUnit c ∧ SqHandleMixFixesCore h sqPivotExp        (h ≥ 1)
```

This file removes the *other* two parameters.  The surviving statement is a `∀`-quantifier over
**all** markings with a unit pivot row, carrying five clauses and an `IsUnit` hypothesis; the
headline here is that all of that collapses:

```text
theorem sqHandleMixFixesCore_sqPivotExp_iff :
    SqHandleMixFixesCore h sqPivotExp ↔ SqChiNuClearHypothesis h
```

where `SqChiNuClearHypothesis h` is `ChiFreeClearing`'s χ-free target **with the χ-clause put
back**, verbatim:

```text
∀ ν', ν'(σ) = 1 → ν'(x₀) = 0 → ∃ Ψ, (∀ x, χ_sq (Ψ x) = χ_sq x) ∧ ∀ x, ν'(Ψ x) = ν_sq x .
```

No exponent parameter, no `IsUnit` hypothesis, two clauses instead of five, and a marking
quantifier over the `2h`-parameter family of **P3-selected** markings instead of the
`(2 + 2h)`-parameter family of unit-pivot ones.  Combined with §3 of the predecessor:

```text
theorem sqHandleMixFixesCore_iff_chiNuClearHypothesis (hh : 0 < h) :
    SqHandleMixFixesCore h c ↔ IsUnit c ∧ SqChiNuClearHypothesis h
```

— the binder is now *exactly* an exponent condition plus one parameter-free statement.  This is
the right cut for three reasons:

1. it is the **only** difference between the certificate route and the realization bypass: the
   two targets `SqChiNuClearHypothesis h` and `SqNuClearHypothesis h`
   (`SqCore/ChiFreeClearing.lean`) are now literally the same statement up to the χ-clause on
   `Ψ` (`sqNuClearHypothesis_of_chiNuClearHypothesis`), so the search harnesses of
   `docs/dyadic/eichler-reduction-note.md` and `docs/dyadic/chifree-clearing-note.md` are aimed
   at one target with one optional filter, not at two;
2. the ν-hypotheses of a residual seed may now be **widened** to the selected rows on the same
   footing as `SqNuSeed`'s — the widening the χ-free lane already took (chifree note, Route 3)
   is legitimate on the χ-pinned lane too, and the widened class-two balance (that note's §2) is
   underdetermined where the pinned one was rigid;
3. it removes the last place where the pivot exponent `c` could re-enter: at the selected rows
   the pivot row is `1` for *every* `c` (`ChiFreeClearing` §2), which is what makes the cut an
   equivalence rather than an implication.

## The engine: λ is an **exact** invariant of χ-preserving maps (§1)

`PivotClimb`'s §3 gets the χ-exponent row `λ = (c₀, 1, 2, 0, 0)` (`nuLam`) invariant *modulo 2*
under `Aut_χ`.  Here it is invariant on the nose, as a `ℤ₂`-valued functional:

```text
theorem nuLam_of_chi_preserving (hchi : ∀ x, χ_sq (Ψ x) = χ_sq x) : nuLam h (Ψ x) = nuLam h x
```

The proof is `χ_sq² = X^{2λ}` (`chiSq_sq_eq_lam`) plus injectivity of `u ↦ X^u`, which is
available because `X` has **exact level two** (`rootXUnit_sub_one_eq`, `SqCore/PivotLemma.lean`)
— `zpowZtwo_injective_of_exact_level`.  Mod-2 invariance is *not* enough for the cut: the
normalisation of §2 rescales by a 2-adic unit and shifts by an arbitrary 2-adic multiple of `λ`.

## The χ-clause itself, reduced to two rows (§4)

`χ_sq = sign · X^λ` (`chiSq_eq_sqSign_mul_xPowLam`), where `sign` is the `±1`-character carried
by the torsion class `t = x̄₁ − 2x̄₀`.  Hence χ-preservation **is** the pair of row conditions
`λ ∘ Ψ = λ` and `sign ∘ Ψ = sign` (`chiSq_preserving_iff`), and a seed's four `chi_*` fields
become "the correction word has zero `λ`-row and even `x₁`-degree" (`chiSq_eq_one_iff`) — two
linear conditions on an abelianized class, testable by a search harness without touching `ℤ₂ˣ`.

## The normalisation: the λ-twist (§2)

`SqHandleMixFixesCore`'s five clauses are affine in the marking — three ask a row to vanish, two
ask a row to be preserved — and `λ`'s handle rows vanish.  So the whole binder is invariant under

```text
ν' ↦ e·(ν' − s·λ) ,        e ∈ ℤ₂ˣ , s ∈ ℤ₂          (`nuTwist`)
```

and at `s = ν'(x₀)`, `e = ν'(w)⁻¹` the twist lands on `ν'(σ) = 1`, `ν'(x₀) = 0` exactly
(`nuTwist_sigma_eq_one`, `nuTwist_x0_eq_zero`).  §1 is what transports the conclusion back: the
correcting automorphism moves `λ` not at all, so the `λ`-part of the twist cancels on both sides
of every clause.

## What this file does **not** settle

`SqChiNuClearHypothesis h` at `h ≥ 1` is **open**, and this file adds no evidence either way.
Recorded for the next pass, none of it formalised here:

* the mod-2 cup form raises **no** obstruction (`PivotClimb`'s §2 invariance is an isometry
  statement; a selected marking and `ν_sq` have the same cup-square `0` and the same pairing
  `1` with `λ̄`, so no `𝔽₂`-level invariant separates them — the chifree note's check);
* the class-two balance is solvable, with the χ-pinned solution rigid
  (`docs/dyadic/eichler-reduction-note.md`) and the widened one underdetermined
  (`docs/dyadic/chifree-clearing-note.md`);
* the cut's own shape says what a refutation would have to look like: an invariant of the
  `Aut_χ`-action on `Hom(D_sq h, ℤ₂)` separating `ν_sq` from `ν_sq·δ_{u_j}`.  The two known
  invariants — the mod-2 Gram and the exact λ-row of §1 — agree on that pair, so a refutation
  needs a genuinely new one.

## Contents

* **§1** `zpowZtwo_rootXUnit_injective`, `nuLam_eq_of_chiSq_eq`, `nuLam_of_chi_preserving`;
* **§2** `nuTwist` and its rows, `nuTwist_sigma_eq_one`, `nuTwist_x0_eq_zero`;
* **§3** `SqChiNuClearHypothesis`, the two halves of the cut, the combined pinning, and the
  pricing corollaries from the existing Eichler supply;
* **§4** `sqSign`, `chiSq_eq_sqSign_mul_xPowLam`, and the reduction of the χ-clause to two rows
  (`chiSq_eq_iff`, `chiSq_eq_one_iff`, `chiSq_preserving_iff`);
* **§5** stress pins, **§6** committed axiom prints.

## Axiom hygiene

Every declaration prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no census
axiom is reachable.  Census unchanged at **11**.  §6 commits the prints.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The χ-exponent row is an **exact** invariant of χ-preserving maps -/

section LamInvariance

/-- `u ↦ X^u` is injective on `ℤ₂`-exponents: `X = rootXUnit` has exact level two
(`rootXUnit_sub_one_eq`, `SqCore/PivotLemma.lean`), which is exactly
`zpowZtwo_injective_of_exact_level`'s hypothesis. -/
theorem zpowZtwo_rootXUnit_injective :
    Function.Injective (zpowZtwo isProP_two_unitsPadicInt rootXUnit) := by
  obtain ⟨a, ha⟩ := rootXUnit_sub_one_eq
  exact zpowZtwo_injective_of_exact_level rootXUnit a ha

/-- `X^{2t}` determines `t`: the composite of `zpowZtwo_rootXUnit_injective` with the
torsion-freeness of `ℤ₂`. -/
theorem toAdd_eq_of_xPowLamSq_eq {t₁ t₂ : ℤ_[2]}
    (hx : zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 2) t₁
      = zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 2) t₂) : t₁ = t₂ := by
  have hrw : ∀ t : ℤ_[2], zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 2) t
      = zpowZtwo isProP_two_unitsPadicInt rootXUnit (2 * t) := by
    intro t
    rw [← zpowZtwo_unit_two rootXUnit, zpowZtwo_zpowZtwo]
  rw [hrw, hrw] at hx
  have h2 := zpowZtwo_rootXUnit_injective hx
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0) h2

/-- **λ is a function of χ**: two elements of `D_sq` with the same orientation value have the
same χ-exponent row.  This is the `ℤ₂`-level sharpening of `PivotClimb`'s §3 (which only gets
the row modulo `2`): `χ_sq² = X^{2λ}` (`chiSq_sq_eq_lam`) and `X` has infinite order. -/
theorem nuLam_eq_of_chiSq_eq {h : ℕ} {x y : (DSq h : Type)} (hchi : chiSq h x = chiSq h y) :
    nuLam h x = nuLam h y := by
  refine Multiplicative.toAdd.injective ?_
  have hx := chiSq_sq_eq_lam h x
  have hy := chiSq_sq_eq_lam h y
  rw [hchi, hy] at hx
  rw [xPowLamSq_apply, xPowLamSq_apply] at hx
  exact (toAdd_eq_of_xPowLamSq_eq hx).symm

/-- **The exact λ-invariance**: every χ-preserving self-map of `D_sq` preserves the χ-exponent
row `λ` on the nose, as a `ℤ₂`-valued functional — not merely modulo `2`.

This is the engine of §2: it is what makes the `SqHandleMixFixesCore` binder invariant under
the `ℤ₂`-affine reparametrisations `ν' ↦ e·(ν' − s·λ)` of a marking. -/
theorem nuLam_of_chi_preserving {h : ℕ}
    {Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)}
    (hchi : ∀ x, chiSq h (Ψ x) = chiSq h x) (x : (DSq h : Type)) :
    nuLam h (Ψ x) = nuLam h x :=
  nuLam_eq_of_chiSq_eq (hchi x)

/-- The additive form of `nuLam_of_chi_preserving`, the shape §2's algebra consumes. -/
theorem toAdd_nuLam_of_chi_preserving {h : ℕ}
    {Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)}
    (hchi : ∀ x, chiSq h (Ψ x) = chiSq h x) (x : (DSq h : Type)) :
    toAdd (nuLam h (Ψ x)) = toAdd (nuLam h x) :=
  congrArg toAdd (nuLam_of_chi_preserving hchi x)

/-- The λ-row of the canonical pivot vanishes: `λ(w) = c₀ − c₀·1 = 0`.  (So the pivot row of a
marking is unchanged by the λ-twist of §2.) -/
@[simp] theorem toAdd_nuLam_sqPivot (h : ℕ) : toAdd (nuLam h (sqPivot h)) = 0 := by
  rw [sqPivot, toAdd_nu_sqMixPivotElem, nuLam_sigma, nuLam_x0, toAdd_ofAdd, toAdd_ofAdd,
    mul_one, sub_self]

end LamInvariance

/-! ## §2 The λ-twist of a marking

`SqHandleMixFixesCore`'s five clauses are *affine* in the marking: three of them ask a row to
vanish and two ask a row to be preserved, and the χ-exponent row `λ` is preserved by the
correcting automorphism exactly (§1).  So the whole binder is invariant under the two-parameter
reparametrisation `ν' ↦ e·(ν' − s·λ)` with `e ∈ ℤ₂ˣ` — which is enough freedom to normalise the
two core rows to the P3-selected values `ν'(σ) = 1`, `ν'(x₀) = 0`. -/

section Twist

variable {h : ℕ}

/-- **The λ-twist** `ν' ↦ e·(ν' − s·λ)` of a marking of `D_sq`: rescale by `e` after
subtracting `s` times the χ-exponent row `λ = (c₀, 1, 2, 0, 0)` (`nuLam`). -/
noncomputable def nuTwist (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (e s : ℤ_[2]) : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  ⟨{ toFun := fun x => ofAdd (e * (toAdd (nu' x) - s * toAdd (nuLam h x)))
     map_one' := by simp
     map_mul' := fun x y => by
       simp only [map_mul, toAdd_mul, ← ofAdd_add]
       ring_nf },
   continuous_ofAdd.comp
     (((continuous_toAdd.comp nu'.continuous_toFun).sub
       ((continuous_toAdd.comp (nuLam h).continuous_toFun).const_smul s)).const_smul e)⟩

@[simp] theorem toAdd_nuTwist (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (e s : ℤ_[2]) (x : (DSq h : Type)) :
    toAdd (nuTwist nu' e s x) = e * (toAdd (nu' x) - s * toAdd (nuLam h x)) := rfl

/-- The σ-row of the λ-twist: `e·(ν'(σ) − s·c₀)`. -/
theorem toAdd_nuTwist_sigma (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (e s : ℤ_[2]) : toAdd (nuTwist nu' e s (dsqSigma h))
      = e * (toAdd (nu' (dsqSigma h)) - s * sqPivotExp) := by
  rw [toAdd_nuTwist, nuLam_sigma, toAdd_ofAdd]

/-- The `x₀`-row of the λ-twist: `e·(ν'(x₀) − s)`. -/
theorem toAdd_nuTwist_x0 (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (e s : ℤ_[2]) : toAdd (nuTwist nu' e s (dsqX0 h))
      = e * (toAdd (nu' (dsqX0 h)) - s) := by
  rw [toAdd_nuTwist, nuLam_x0, toAdd_ofAdd, mul_one]

/-- The handle rows of `λ` vanish, so the λ-twist rescales every handle row. -/
theorem toAdd_nuTwist_handleU (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (e s : ℤ_[2]) (j : Fin h) :
    toAdd (nuTwist nu' e s (sqGen h (sqHandleIdxU j)))
      = e * toAdd (nu' (sqGen h (sqHandleIdxU j))) := by
  rw [toAdd_nuTwist, nuLam_handleU, toAdd_one, mul_zero, sub_zero]

/-- The handle rows of `λ` vanish, so the λ-twist rescales every handle row. -/
theorem toAdd_nuTwist_handleV (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (e s : ℤ_[2]) (j : Fin h) :
    toAdd (nuTwist nu' e s (sqGen h (sqHandleIdxV j)))
      = e * toAdd (nu' (sqGen h (sqHandleIdxV j))) := by
  rw [toAdd_nuTwist, nuLam_handleV, toAdd_one, mul_zero, sub_zero]

/-- **The normalising twist**: at a marking whose pivot row `d = ν'(σ) − c₀·ν'(x₀)` is a unit,
the twist with `s = ν'(x₀)` and `e = d⁻¹` lands exactly on the P3-selected core rows. -/
theorem nuTwist_sigma_eq_one
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) {e : ℤ_[2]}
    (he : e * toAdd (nu' (sqPivot h)) = 1) :
    nuTwist nu' e (toAdd (nu' (dsqX0 h))) (dsqSigma h) = ofAdd (1 : ℤ_[2]) := by
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_nuTwist_sigma, toAdd_ofAdd, ← he, sqPivot, toAdd_nu_sqMixPivotElem]
  ring

/-- The companion `x₀`-row of the normalising twist: it vanishes for every scale. -/
theorem nuTwist_x0_eq_zero
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (e : ℤ_[2]) :
    nuTwist nu' e (toAdd (nu' (dsqX0 h))) (dsqX0 h) = ofAdd (0 : ℤ_[2]) := by
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_nuTwist_x0, toAdd_ofAdd, sub_self, mul_zero]

end Twist

/-! ## §3 The sharp cut: the binder **is** the χ-free target plus a χ-clause -/

section Cut

variable {h : ℕ}

/-- **The χ-preserving clearing hypothesis**: `ChiFreeClearing`'s `SqNuClearHypothesis` with the
χ-clause restored on the correcting automorphism.  Two clauses, no exponent parameter, no
`IsUnit` hypothesis, and the marking quantifier restricted to the two P3-selected core rows. -/
def SqChiNuClearHypothesis (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ x) = chiSq h x) ∧ ∀ x, nu' (Ψ x) = nuSq h x

/-- The easy half: the one-binder handle stratum, at **any** exponent, gives the χ-preserving
clearing hypothesis — the selected rows make the pivot row `1` for every `c`. -/
theorem sqChiNuClearHypothesis_of_fixesCore {c : ℤ_[2]} (H : SqHandleMixFixesCore h c) :
    SqChiNuClearHypothesis h :=
  fun nu' hsigma hx0 => sqMarkedMatching_of_fixesCore H nu' hsigma hx0

/-- Forgetting the χ-clause lands on `ChiFreeClearing`'s target. -/
theorem sqNuClearHypothesis_of_chiNuClearHypothesis (H : SqChiNuClearHypothesis h) :
    SqNuClearHypothesis h :=
  fun nu' hsigma hx0 => (H nu' hsigma hx0).imp fun _ hΨ => hΨ.2

/-- **The hard half — the normalisation.**  The λ-twist of §2 moves an *arbitrary* marking with
unit pivot row onto the P3-selected rows, and §1's exact λ-invariance carries the five clauses
back.  So the binder's two-parameter core quantifier is redundant. -/
theorem sqHandleMixFixesCore_of_chiNuClearHypothesis (H : SqChiNuClearHypothesis h) :
    SqHandleMixFixesCore h sqPivotExp := by
  intro nu' hpiv
  obtain ⟨w, hw⟩ := hpiv
  set e : ℤ_[2] := ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hedef
  have hne : e ≠ 0 := Units.ne_zero w⁻¹
  have hprod : e * toAdd (nu' (sqPivot h)) = 1 := by
    rw [sqPivot, ← hw, hedef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set s : ℤ_[2] := toAdd (nu' (dsqX0 h)) with hsdef
  obtain ⟨Ψ, hchi, hval⟩ :=
    H (nuTwist nu' e s) (nuTwist_sigma_eq_one nu' hprod) (nuTwist_x0_eq_zero nu' e)
  have key : ∀ x : (DSq h : Type), toAdd (nuSq h x)
      = e * (toAdd (nu' (Ψ x)) - s * toAdd (nuLam h x)) := by
    intro x
    rw [← hval x, toAdd_nuTwist, toAdd_nuLam_of_chi_preserving hchi x]
  have hpivval : toAdd (nu' (sqPivot h)) = toAdd (nu' (dsqSigma h)) - sqPivotExp * s := by
    rw [sqPivot, toAdd_nu_sqMixPivotElem]
  rw [hpivval] at hprod
  refine ⟨Ψ, hchi, fun j => ?_, fun j => ?_, ?_, ?_⟩
  · refine Multiplicative.toAdd.injective ?_
    have hk := key (sqGen h (sqHandleIdxU j))
    rw [nuSq_handleU, toAdd_one, nuLam_handleU, toAdd_one, mul_zero, sub_zero] at hk
    rw [toAdd_one]
    exact (mul_eq_zero.mp hk.symm).resolve_left hne
  · refine Multiplicative.toAdd.injective ?_
    have hk := key (sqGen h (sqHandleIdxV j))
    rw [nuSq_handleV, toAdd_one, nuLam_handleV, toAdd_one, mul_zero, sub_zero] at hk
    rw [toAdd_one]
    exact (mul_eq_zero.mp hk.symm).resolve_left hne
  · refine Multiplicative.toAdd.injective ?_
    have hk := key (dsqSigma h)
    rw [nuSq_sigma, toAdd_ofAdd, nuLam_sigma, toAdd_ofAdd] at hk
    have hcancel := mul_left_cancel₀ hne (hk.symm.trans hprod.symm)
    linear_combination hcancel
  · refine Multiplicative.toAdd.injective ?_
    have hk := key (dsqX0 h)
    rw [nuSq_x0, toAdd_ofAdd, nuLam_x0, toAdd_ofAdd, mul_one] at hk
    have hzero := (mul_eq_zero.mp hk.symm).resolve_left hne
    linear_combination hzero

/-- **THE CUT** (the headline of this file): at the canonical exponent the one-binder handle
stratum is *exactly* the χ-preserving clearing hypothesis. -/
theorem sqHandleMixFixesCore_sqPivotExp_iff :
    SqHandleMixFixesCore h sqPivotExp ↔ SqChiNuClearHypothesis h :=
  ⟨sqChiNuClearHypothesis_of_fixesCore, sqHandleMixFixesCore_of_chiNuClearHypothesis⟩

/-- **The complete pinning** of the binder at `h ≥ 1`, combining `HandleMixFixesCore` §3's
exponent normalisation with the cut: an exponent condition and one parameter-free statement. -/
theorem sqHandleMixFixesCore_iff_chiNuClearHypothesis (hh : 0 < h) {c : ℤ_[2]} :
    SqHandleMixFixesCore h c ↔ IsUnit c ∧ SqChiNuClearHypothesis h := by
  rw [sqHandleMixFixesCore_iff hh, sqHandleMixFixesCore_sqPivotExp_iff]

/-- At `h = 0` the cut statement is a theorem, exactly as the binder is. -/
theorem sqChiNuClearHypothesis_zero : SqChiNuClearHypothesis 0 :=
  sqChiNuClearHypothesis_of_fixesCore (sqHandleMixFixesCore_zero 0)

/-! ### Pricing the cut against the existing residual supply

The three producers `HandleMixFixesCore`/`EichlerReduction` already carry, restated at the cut so
that the search's target is unambiguous. -/

/-- The cut, from the χ-Eichler family. -/
theorem sqChiNuClearHypothesis_of_eichler {c : ℤ_[2]} (hE : SqHandleEichler h c) :
    SqChiNuClearHypothesis h :=
  sqChiNuClearHypothesis_of_fixesCore (sqHandleMixFixesCore_of_eichler hE)

/-- The cut, from the χ-Eichler moves on the unit slice. -/
theorem sqChiNuClearHypothesis_of_unit_moves {c : ℤ_[2]}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), IsUnit k → SqEichlerMoveAt h c j k) :
    SqChiNuClearHypothesis h :=
  sqChiNuClearHypothesis_of_fixesCore (sqHandleMixFixesCore_of_unit_moves H)

/-- The cut, from `SqEichlerSeed`s on the unit slice — the residual word-level search. -/
theorem sqChiNuClearHypothesis_of_seeds {c : ℤ_[2]}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), IsUnit k → Nonempty (SqEichlerSeed h c j k)) :
    SqChiNuClearHypothesis h :=
  sqChiNuClearHypothesis_of_fixesCore (sqHandleMixFixesCore_of_seeds H)

end Cut

/-! ## §4 The χ-clause, decomposed into two rows

`χ_sq` is the product of a **sign character** (the `±1`-part, carried entirely by the torsion
class `t = x̄₁ − 2x̄₀`, `χ_sq(t) = −1`) and the `X`-power of the χ-exponent row `λ`.  So the
χ-clause of §3's cut — and the four `chi_*` fields of a residual `SqEichlerSeed` — are
equivalent to **two linear row conditions**: the `λ`-row is preserved (a `ℤ₂`-condition) and the
sign row is preserved (an `𝔽₂`-condition on the `x₁`-degree).  That is the form a search harness
can test directly. -/

section SignCharacter

/-- The relator dies at the sign row `(1, 1, −1)`: abelianized it is `(1⁴)⁻¹·(−1)² = 1`. -/
theorem sqRelWord_sqSignMark (h : ℕ) :
    sqRelWord (sqMark (h := h) (1 : ℤ_[2]ˣ) (1 : ℤ_[2]ˣ) (-1 : ℤ_[2]ˣ)) = 1 := by
  rw [sqRelWord_sqMark, sqWord_comm]
  simp

/-- **The sign character** of the `L_sq` core: `σ, x₀, u_j, v_j ↦ 1` and `x₁ ↦ −1`.  It is the
`±1`-part of `χ_sq`, and its kernel is the index-2 subgroup detecting the torsion class. -/
noncomputable def sqSign (h : ℕ) : ContinuousMonoidHom (DSq h : Type) ℤ_[2]ˣ :=
  sqLiftHom h isProP_two_unitsPadicInt (sqMark (1 : ℤ_[2]ˣ) (1 : ℤ_[2]ˣ) (-1 : ℤ_[2]ˣ))
    (sqRelWord_sqSignMark h)

@[simp] theorem sqSign_sigma (h : ℕ) : sqSign h (dsqSigma h) = 1 :=
  (sqLiftHom_gen _ _ _ _ 0).trans (sqMark_zero _ _ _)

@[simp] theorem sqSign_x0 (h : ℕ) : sqSign h (dsqX0 h) = 1 :=
  (sqLiftHom_gen _ _ _ _ 1).trans (sqMark_one _ _ _)

@[simp] theorem sqSign_x1 (h : ℕ) : sqSign h (dsqX1 h) = -1 :=
  (sqLiftHom_gen _ _ _ _ 2).trans (sqMark_two _ _ _)

@[simp] theorem sqSign_handleU {h : ℕ} (j : Fin h) : sqSign h (sqGen h (sqHandleIdxU j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleU _ _ _ j)

@[simp] theorem sqSign_handleV {h : ℕ} (j : Fin h) : sqSign h (sqGen h (sqHandleIdxV j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleV _ _ _ j)

/-- `X^λ`, packaged as a character of `D_sq` (the unsquared companion of `xPowLamSq`). -/
noncomputable def xPowLam (h : ℕ) : ContinuousMonoidHom (DSq h : Type) ℤ_[2]ˣ :=
  (zpowZtwoHom isProP_two_unitsPadicInt rootXUnit).comp (nuLam h)

theorem xPowLam_apply (h : ℕ) (x : (DSq h : Type)) :
    xPowLam h x = zpowZtwo isProP_two_unitsPadicInt rootXUnit (toAdd (nuLam h x)) := rfl

/-- **The orientation, factored**: `χ_sq = sign · X^λ`.  Generator by generator: `S = X^{c₀}`
(the pivot exponent's defining relation), `X = X^1`, `Y = (−1)·X²`, and the handle letters are
trivial on both sides. -/
theorem chiSq_eq_sqSign_mul_xPowLam (h : ℕ) : chiSq h = sqSign h * xPowLam h := by
  refine dsq_hom_ext _ _ fun i => ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · show chiSq h (dsqSigma h) = sqSign h (dsqSigma h) * xPowLam h (dsqSigma h)
    rw [chiSq_sigma, sqSign_sigma, xPowLam_apply, nuLam_sigma, toAdd_ofAdd,
      zpowZtwo_rootXUnit_sqPivotExp, one_mul]
  · show chiSq h (dsqX0 h) = sqSign h (dsqX0 h) * xPowLam h (dsqX0 h)
    rw [chiSq_x0, sqSign_x0, xPowLam_apply, nuLam_x0, toAdd_ofAdd, zpowZtwo_one_exp, one_mul]
  · show chiSq h (dsqX1 h) = sqSign h (dsqX1 h) * xPowLam h (dsqX1 h)
    rw [chiSq_x1, sqSign_x1, xPowLam_apply, nuLam_x1, toAdd_ofAdd, zpowZtwo_unit_two,
      neg_one_mul, YvalUnit_eq_neg_sq]
  · show chiSq h (sqGen h (sqHandleIdxU j))
      = sqSign h (sqGen h (sqHandleIdxU j)) * xPowLam h (sqGen h (sqHandleIdxU j))
    rw [chiSq_handleU, sqSign_handleU, xPowLam_apply, nuLam_handleU, toAdd_one, one_mul,
      zpowZtwo_zero_exp]
  · show chiSq h (sqGen h (sqHandleIdxV j))
      = sqSign h (sqGen h (sqHandleIdxV j)) * xPowLam h (sqGen h (sqHandleIdxV j))
    rw [chiSq_handleV, sqSign_handleV, xPowLam_apply, nuLam_handleV, toAdd_one, one_mul,
      zpowZtwo_zero_exp]

/-- **The χ-clause is exactly two row conditions.**  `λ` is the `ℤ₂`-row (§1), `sign` is the
`±1`-row. -/
theorem chiSq_eq_iff (h : ℕ) (x y : (DSq h : Type)) :
    chiSq h x = chiSq h y ↔ nuLam h x = nuLam h y ∧ sqSign h x = sqSign h y := by
  have hfac : ∀ z : (DSq h : Type), chiSq h z = sqSign h z * xPowLam h z :=
    fun z => DFunLike.congr_fun (chiSq_eq_sqSign_mul_xPowLam h) z
  have hxp : ∀ z w : (DSq h : Type), nuLam h z = nuLam h w → xPowLam h z = xPowLam h w := by
    intro z w hzw
    rw [xPowLam_apply, xPowLam_apply, hzw]
  constructor
  · intro hc
    have hl := nuLam_eq_of_chiSq_eq hc
    refine ⟨hl, ?_⟩
    have h1 := hfac x
    rw [hc, hfac y, hxp x y hl] at h1
    exact (mul_right_cancel h1).symm
  · rintro ⟨hl, hs⟩
    rw [hfac x, hfac y, hs, hxp x y hl]

/-- The seed-facing form: a correction word is χ-trivial iff its `λ`-row vanishes **and** its
sign is `+1` (equivalently, its `x₁`-degree is even).  This replaces each `chi_*` field of a
residual seed by two linear conditions on the word's abelianized class. -/
theorem chiSq_eq_one_iff (h : ℕ) (g : (DSq h : Type)) :
    chiSq h g = 1 ↔ nuLam h g = 1 ∧ sqSign h g = 1 := by
  simpa using chiSq_eq_iff h g 1

/-- The automorphism form: preserving `χ_sq` is preserving the two rows. -/
theorem chiSq_preserving_iff {h : ℕ}
    (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) :
    (∀ x, chiSq h (Ψ x) = chiSq h x) ↔
      (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ ∀ x, sqSign h (Ψ x) = sqSign h x := by
  constructor
  · intro hc
    exact ⟨fun x => ((chiSq_eq_iff h (Ψ x) x).mp (hc x)).1,
      fun x => ((chiSq_eq_iff h (Ψ x) x).mp (hc x)).2⟩
  · rintro ⟨hl, hs⟩ x
    exact (chiSq_eq_iff h (Ψ x) x).mpr ⟨hl x, hs x⟩

end SignCharacter

/-! ## §5 Stress pins

The lane idiom: the cut restated at `h = 1`, its hypothesis pinned non-vacuous, and the two
`h ≥ 1` refutations of `HandleMixFixesCore` §2–§3 restated through it — so that a later
reshaping of the cut cannot silently become vacuous, nor silently re-admit a refuted
exponent. -/

section StressTests

/-- The cut's marking hypothesis is met by the standard marking at every handle count: the
quantifier of `SqChiNuClearHypothesis` is **never** vacuous. -/
theorem sqChiNuClearHypothesis_nonvacuous (h : ℕ) :
    nuSq h (dsqSigma h) = ofAdd (1 : ℤ_[2]) ∧ nuSq h (dsqX0 h) = ofAdd (0 : ℤ_[2]) :=
  ⟨nuSq_sigma h, nuSq_x0 h⟩

/-- Stress: the cut is an equivalence at one handle, not merely a sufficient condition. -/
example : SqHandleMixFixesCore 1 sqPivotExp ↔ SqChiNuClearHypothesis 1 :=
  sqHandleMixFixesCore_sqPivotExp_iff

/-- Stress: the exponent normalisation survives the cut — at one handle the binder at a general
exponent is "unit" plus the parameter-free cut. -/
example {c : ℤ_[2]} : SqHandleMixFixesCore 1 c ↔ IsUnit c ∧ SqChiNuClearHypothesis 1 :=
  sqHandleMixFixesCore_iff_chiNuClearHypothesis (by omega)

/-- Stress: `HandleMixFixesCore` §2's refutation is **not** reached by the cut — its witness has
pivot row `c₀ − c₀ = 0` at the canonical exponent, so it fails the binder's own hypothesis
there (and, after the twist of §2, it is not a selected marking either). -/
example : toAdd (nuWitness 1 (sqMixPivotElem 1 sqPivotExp)) = 0 := by
  rw [toAdd_nuWitness_sqMixPivotElem, sub_self]

/-- Stress: the refuted exponent `c = 0` stays refuted through the cut. -/
example : ¬ SqHandleMixFixesCore 1 0 := not_sqHandleMixFixesCore_zero (by omega)

/-- Stress: the cut prices into `ChiFreeClearing`'s χ-free target, which is what the realization
bypass consumes. -/
example (H : SqChiNuClearHypothesis 1) : SqNuClearHypothesis 1 :=
  sqNuClearHypothesis_of_chiNuClearHypothesis H

/-- Stress: `h = 0` is a theorem on both sides of the cut. -/
example : SqChiNuClearHypothesis 0 := sqChiNuClearHypothesis_zero

/-- Stress: the λ-row is genuinely `ℤ₂`-valued data — `λ(σ) = c₀` is the canonical exponent,
not a mod-2 residue, which is what makes §2's twist available at unit scale. -/
example (h : ℕ) : toAdd (nuLam h (dsqSigma h)) = sqPivotExp := by
  rw [nuLam_sigma, toAdd_ofAdd]

/-- Stress: the sign character of §4 is non-trivial, so the χ-clause does **not** collapse to
the λ-row alone — the `x₁`-parity is a second, independent condition. -/
example (h : ℕ) : sqSign h (dsqX1 h) ≠ 1 := by
  rw [sqSign_x1]
  exact negOne_ne_one_unitsPadicInt

/-- Stress: the seed-facing χ-test, at the shape a residual `SqEichlerSeed`'s `chi_*` field
meets it — two linear row conditions in place of a `ℤ₂ˣ`-valued equation. -/
example {h : ℕ} (g : (DSq h : Type)) (hl : nuLam h g = 1) (hs : sqSign h g = 1) :
    chiSq h g = 1 := (chiSq_eq_one_iff h g).mpr ⟨hl, hs⟩

end StressTests

/-! ## §6 Axiom pins

Committed prints: the whole file is **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable.  Census unchanged at **11**. -/

section AxiomPins

#print axioms zpowZtwo_rootXUnit_injective
#print axioms nuLam_eq_of_chiSq_eq
#print axioms nuLam_of_chi_preserving
#print axioms nuTwist
#print axioms sqChiNuClearHypothesis_of_fixesCore
#print axioms sqNuClearHypothesis_of_chiNuClearHypothesis
#print axioms sqHandleMixFixesCore_of_chiNuClearHypothesis
#print axioms sqHandleMixFixesCore_sqPivotExp_iff
#print axioms sqHandleMixFixesCore_iff_chiNuClearHypothesis
#print axioms sqChiNuClearHypothesis_zero
#print axioms sqChiNuClearHypothesis_of_seeds
#print axioms sqSign
#print axioms chiSq_eq_sqSign_mul_xPowLam
#print axioms chiSq_eq_iff
#print axioms chiSq_eq_one_iff
#print axioms chiSq_preserving_iff

end AxiomPins
