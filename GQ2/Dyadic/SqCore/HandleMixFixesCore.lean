/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.Certificate

/-!
# P2 — the `L_sq` handle stratum: the exponent is forced, and the residual obligation

**Package P2** of the dyadic campaign (lane SQ).  The target was
`SqCore.SqHandleMixFixesCore h c` (`GQ2/Dyadic/SqCore/Certificate.lean`), the one-binder
handle stratum of the `L_sq` marked-matching certificate, for `h ≥ 1`.  This file lands what is
provable and **refutes what is not**.

## Headline (a refutation, with witness)

`SqHandleMixFixesCore h c` is stated for an arbitrary `c : ℤ_[2]`, and its *conclusion* does not
mention `c` at all — `c` enters only through the hypothesis `ν'(σ·x₀^{−c}) ∈ ℤ₂ˣ`.  That makes
the binder strictly stronger for smaller `c`-hypotheses, and at `h ≥ 1` it breaks:

```text
theorem not_sqHandleMixFixesCore : 0 < h → IsUnit (sqPivotExp − c) → ¬ SqHandleMixFixesCore h c
```

so in particular **`SqHandleMixFixesCore h 0` is false** at every `h ≥ 1` (`sqPivotExp` is a
unit, so `sqPivotExp − 0` is), and more generally the binder forces `c` to be a *unit*:

```text
theorem isUnit_of_sqHandleMixFixesCore : 0 < h → SqHandleMixFixesCore h c → IsUnit c
```

Together with the exponent-normalisation of §3 (`c ≡ c' (2)` makes the two binders *equivalent*,
because the hypothesis is a mod-2 condition and the conclusion is `c`-free) this pins the binder
completely:

```text
theorem sqHandleMixFixesCore_iff (hh : 0 < h) :
    SqHandleMixFixesCore h c ↔ IsUnit c ∧ SqHandleMixFixesCore h sqPivotExp
```

**Consequence for the adapter.**  `GQ2/Dyadic/LabuteInterface.lean`'s
`marked_matching_certificate_KTwoSq_of_fixesCore` quantifies over a free `c : ℤ_[2]`.  At `h ≥ 1`
that quantifier is only inhabited at units, and — by §3 — every unit gives the *same* binder as
the canonical `sqPivotExp`.  The adapter should therefore be instantiated at `sqPivotExp`
(`SqCore/Certificate.lean` §1), where the pivot is also the χ-trivial one (`chiSq_sqPivot`);
any other instantiation is either unsatisfiable (non-unit `c`) or a redundant restatement.

The witness is explicit: the marking
`ν' : (σ, x₀, x₁, u_j, v_j) ↦ (c₀, 1, 2, 1, 0)` with `c₀ = sqPivotExp`.  It satisfies the
relator (`−4·1 + 2·2 = 0`) and has `ν'(σ·x₀^{−c}) = c₀ − c`, a unit exactly when `c ≢ c₀ (2)`;
but its two core rows are *proportional to the χ-exponent row* `λ = (c₀, 1, 2, 0, 0)`, so a
correction fixing both core rows and killing the handle rows would force `ν'∘Ψ = λ`, hence
`χ_sq² = X^{2λ}` **everywhere**, hence `X² = χ_sq(u₀)² = 1` — false, `X ≡ 5 (16)`.

## What ports from the `M`/`N` lane, and what does not (§4, and the finding)

§4 lands the part of `HandleMix`'s move set that the `L_sq` word *does* support: the two exact
intra-handle transvections

```text
τ_{v_j}(k) : u_j ↦ v_j^k·u_j        τ_{u_j}(k) : v_j ↦ u_j^k·v_j
```

as honest continuous automorphisms of `D_sq` (`sqTauUEquiv`, `sqTauVEquiv`), χ-preserving on the
nose (`chiSq_sqTauUEquiv`), fixing the two marked core letters **literally**, and steering each
handle plane by `SL₂(ℤ₂)`.  `sq_normalize_handle` is the consequence the clearing recipe needs:
every handle plane can be brought to the shape `(·, 0)`, with the core rows untouched.

What does **not** port is HM2's mixing element `Φ_j`, and the reason is now sharper than
MC5's §6 note (*"the `L_sq` core has no literal core commutator `[y,z]` disjoint-lettered from
the prefix"*).  Two independent walls:

1. **Word shape.**  `handlemixlift-spike.md` §6.1 needs `P = W·[y,z]·∏[u_j,v_j]` with `W`
   missing at least one of `y, z`.  The `L_sq` relator is
   `(x₀^σ)⁻¹x₀⁻³x₁²·[x₁,x₁^σ]·∏[u_j,v_j]`; its core commutator's second letter `x₁^σ` is not a
   letter at all, and rewriting `(x₀^σ)⁻¹x₀⁻³ = [σ,x₀]·x₀⁻⁴` exposes the *other* commutator
   `[σ,x₀]` — whose two letters both occur again (`x₀⁻⁴`, and `σ` inside `[x₁,[x₁,σ]]`, the
   collapsed form of `[x₁,x₁^σ]`).  Both readings fail §6.1.
2. **Orientation.**  Even granting a change of variables to §6.1 shape, the direction §6.1's
   Eichler unipotents add to `ū_j` is the frame class of the letter of `[y,z]` that lies **in**
   `W` — the "pivot".  For `M`/`N`/the collector that letter has `χ = 1`.  For `L_sq` the
   χ-trivial core direction is `w̄ = σ̄ − c₀x̄₀` (`chiSq_sqPivot`), which is a *combination*, not
   a letter of the given presentation; the two letters of the frame's hyperbolic plane have
   `χ_sq(σ) = S` and `χ_sq(x₀) = X`, both of infinite order.  So a `Φ_j` ported letter-for-letter
   is **not** χ-preserving, independently of wall 1.  §6's `sqCore_no_clearBlind_letter` pins the
   second wall in Lean: *no* core letter of this presentation is χ-trivial, so HM5's
   `IsClearBlind` has no witness at any candidate pivot slot of the `L_sq` word.

## The residual obligation, isolated (§5)

§5 states the single remaining word-level input as `SqHandleEichler h c` — one continuous
automorphism per `(handle index, 2-adic parameter)`, acting on the rows of *any* marking whose
`v_j`-row already vanishes by

```text
ν'(Ψ u_j) = ν'(u_j)·ν'(w)^k ,   ν'(Ψ σ) = ν'(σ) ,   ν'(Ψ x₀) = ν'(x₀) ,   other rows fixed
```

(the `v_j`-row hypothesis is what makes the Eichler element's compensating core shift — a
multiple of `v̄_j`, forced by the mod-2 cup form — invisible to `ν'`; without it no such Ψ can
exist, which is why the hypothesis is *in* the statement).  Then

```text
theorem sqHandleMixFixesCore_of_eichler : SqHandleEichler h c → SqHandleMixFixesCore h c
```

is a theorem: §4's `SL₂` normalisation puts every handle plane into the `(g, 0)` shape and the
Eichler move kills `g`, handle by handle, with the two core rows never moving.  So the whole
`L_sq` handle stratum is now **one** explicitly-shaped automorphism family away, at the canonical
exponent — and, by §2–§3 (`not_sqHandleEichler`), at *no other* exponent.

## Contents

* **§1** the two witness markings `ν' = (c₀,1,2,1,0)` and `λ = (c₀,1,2,0,0)` on `D_sq`;
* **§2** `chiSq_sq_eq_lam` (`χ_sq² = X^{2λ}`) and the refutation `not_sqHandleMixFixesCore`;
* **§3** the exponent normalisation, `isUnit_of_sqHandleMixFixesCore`, `sqHandleMixFixesCore_iff`;
* **§4** the two intra-handle transvections as automorphisms, and `sq_normalize_handle`;
* **§5** `SqHandleEichler`, the residual obligation, and `sqHandleMixFixesCore_of_eichler`;
* **§6** wall 2 in Lean (`sqCore_no_clearBlind_letter`) and the certificate-facing corollaries;
* **§7** stress pins, **§8** committed axiom prints.

## Axiom hygiene

Every declaration prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no census
axiom is reachable (in particular no `B8`/`peripheralCyclotomicAction` and no `B3c`
`dyadicOrientation` — the `h`-generic `χ_sq`/`ν_sq` layer and `SqCore/PivotLemma.lean` are all
that is consumed, exactly as the `M`/`N` handle stratum needed no `B8`).  Census unchanged
at **11**.  §8 commits the prints.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 Witness markings on `D_sq`

Two `ℤ₂`-markings that the refutation of §2 compares: the **χ-exponent row**
`λ = (c₀, 1, 2, 0, 0)` (the unique marking with `χ_sq² = X^{2λ}`, §2) and the **witness**
`ν' = (c₀, 1, 2, 1, 0)`, which differs from it only on the first letter of each handle pair. -/

section Markings

/-- The witness marking of the refutation: `σ ↦ c₀`, `x₀ ↦ 1`, `x₁ ↦ 2`, every `u_j ↦ 1`, every
`v_j ↦ 0`.  The `x₁`-row is the forced row `2·ν'(x₀)` (`toAdd_nu_dsqX1`), so the relator dies. -/
noncomputable def sqWitnessMark (h : ℕ) : Fin (sqRank h) → Multiplicative ℤ_[2] :=
  fun i =>
    if (i : ℕ) = 0 then ofAdd sqPivotExp else
    if (i : ℕ) = 1 then ofAdd (1 : ℤ_[2]) else
    if (i : ℕ) = 2 then ofAdd (2 : ℤ_[2]) else
    if (i : ℕ) % 2 = 1 then ofAdd (1 : ℤ_[2]) else 1

@[simp] theorem sqWitnessMark_zero (h : ℕ) :
    sqWitnessMark h 0 = ofAdd sqPivotExp := by
  simp only [sqWitnessMark, sqVal_zero]
  norm_num

@[simp] theorem sqWitnessMark_one (h : ℕ) :
    sqWitnessMark h 1 = ofAdd (1 : ℤ_[2]) := by
  simp only [sqWitnessMark, sqVal_one]
  norm_num

@[simp] theorem sqWitnessMark_two (h : ℕ) :
    sqWitnessMark h 2 = ofAdd (2 : ℤ_[2]) := by
  simp only [sqWitnessMark, sqVal_two]
  norm_num

@[simp] theorem sqWitnessMark_handleU {h : ℕ} (j : Fin h) :
    sqWitnessMark h (sqHandleIdxU j) = ofAdd (1 : ℤ_[2]) := by
  simp only [sqWitnessMark, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

@[simp] theorem sqWitnessMark_handleV {h : ℕ} (j : Fin h) :
    sqWitnessMark h (sqHandleIdxV j) = 1 := by
  simp only [sqWitnessMark, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The witness marking kills the relator: the abelian collapse is `(x₀⁴)⁻¹x₁²`, i.e.
`−4·1 + 2·2 = 0`. -/
theorem sqRelWord_sqWitnessMark (h : ℕ) : sqRelWord (sqWitnessMark h) = 1 := by
  rw [sqRelWord_comm, sqWitnessMark_one, sqWitnessMark_two]
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, toAdd_one]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- **The witness marking**, as a continuous `ℤ₂`-marking of `D_sq`. -/
noncomputable def nuWitness (h : ℕ) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  sqLiftHom h PropOneOne.isProP_two_multPadicInt (sqWitnessMark h) (sqRelWord_sqWitnessMark h)

@[simp] theorem nuWitness_sigma (h : ℕ) : nuWitness h (dsqSigma h) = ofAdd sqPivotExp :=
  (sqLiftHom_gen _ _ _ _ 0).trans (sqWitnessMark_zero h)

@[simp] theorem nuWitness_x0 (h : ℕ) : nuWitness h (dsqX0 h) = ofAdd (1 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 1).trans (sqWitnessMark_one h)

@[simp] theorem nuWitness_x1 (h : ℕ) : nuWitness h (dsqX1 h) = ofAdd (2 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 2).trans (sqWitnessMark_two h)

@[simp] theorem nuWitness_handleU {h : ℕ} (j : Fin h) :
    nuWitness h (sqGen h (sqHandleIdxU j)) = ofAdd (1 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqWitnessMark_handleU j)

@[simp] theorem nuWitness_handleV {h : ℕ} (j : Fin h) :
    nuWitness h (sqGen h (sqHandleIdxV j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqWitnessMark_handleV j)

/-- **The pivot row of the witness** at exponent `c`: `ν'(σ·x₀^{−c}) = c₀ − c`. -/
theorem toAdd_nuWitness_sqMixPivotElem (h : ℕ) (c : ℤ_[2]) :
    toAdd (nuWitness h (sqMixPivotElem h c)) = sqPivotExp - c := by
  rw [toAdd_nu_sqMixPivotElem, nuWitness_sigma, nuWitness_x0, toAdd_ofAdd, toAdd_ofAdd, mul_one]

/-- The χ-exponent marking `λ = (c₀, 1, 2, 0, 0)` — the row for which `χ_sq² = X^{2λ}`. -/
theorem sqRelWord_sqLamMark (h : ℕ) :
    sqRelWord (sqMark (h := h) (ofAdd sqPivotExp) (ofAdd (1 : ℤ_[2])) (ofAdd (2 : ℤ_[2]))) = 1 := by
  rw [sqRelWord_sqMark, sqWord_comm]
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, toAdd_one]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- **The χ-exponent marking** `λ`, as a continuous `ℤ₂`-marking of `D_sq`. -/
noncomputable def nuLam (h : ℕ) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  sqLiftHom h PropOneOne.isProP_two_multPadicInt
    (sqMark (ofAdd sqPivotExp) (ofAdd (1 : ℤ_[2])) (ofAdd (2 : ℤ_[2]))) (sqRelWord_sqLamMark h)

@[simp] theorem nuLam_sigma (h : ℕ) : nuLam h (dsqSigma h) = ofAdd sqPivotExp :=
  (sqLiftHom_gen _ _ _ _ 0).trans (sqMark_zero _ _ _)

@[simp] theorem nuLam_x0 (h : ℕ) : nuLam h (dsqX0 h) = ofAdd (1 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 1).trans (sqMark_one _ _ _)

@[simp] theorem nuLam_x1 (h : ℕ) : nuLam h (dsqX1 h) = ofAdd (2 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ 2).trans (sqMark_two _ _ _)

@[simp] theorem nuLam_handleU {h : ℕ} (j : Fin h) :
    nuLam h (sqGen h (sqHandleIdxU j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleU _ _ _ j)

@[simp] theorem nuLam_handleV {h : ℕ} (j : Fin h) :
    nuLam h (sqGen h (sqHandleIdxV j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleV _ _ _ j)

end Markings

/-! ## §2 The refutation

The engine is the identity `χ_sq² = X^{2λ}` (`chiSq_sq_eq_lam`): the orientation of the `L_sq`
core is, up to the `ℤ/2`-torsion character on `t = x̄₁ − 2x̄₀`, the `X`-power of the χ-exponent
row.  A correction that fixed both core rows of the witness and killed every handle row would
force `ν'∘Ψ` to *be* `λ`, hence would put `X²` at the value `χ_sq(u₀)² = 1`. -/

section Refutation

/-- `x ↦ x²` on `ℤ₂ˣ`, as a continuous monoid hom (the target is commutative). -/
noncomputable def unitsSquareHom : ContinuousMonoidHom ℤ_[2]ˣ ℤ_[2]ˣ :=
  ⟨powMonoidHom 2, continuous_pow 2⟩

@[simp] theorem unitsSquareHom_apply (u : ℤ_[2]ˣ) : unitsSquareHom u = u ^ 2 := rfl

/-- `X^{2λ}`, packaged as a continuous character of `D_sq`. -/
noncomputable def xPowLamSq (h : ℕ) : ContinuousMonoidHom (DSq h : Type) ℤ_[2]ˣ :=
  (zpowZtwoHom isProP_two_unitsPadicInt (rootXUnit ^ 2)).comp (nuLam h)

theorem xPowLamSq_apply (h : ℕ) (x : (DSq h : Type)) :
    xPowLamSq h x = zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 2) (toAdd (nuLam h x)) := rfl

/-- `u² = u^{(2 : ℤ₂)}` on `ℤ₂ˣ` — the numeral bridge for the `zpowZtwo` composition law. -/
theorem zpowZtwo_unit_two (u : ℤ_[2]ˣ) :
    zpowZtwo isProP_two_unitsPadicInt u (2 : ℤ_[2]) = u ^ 2 := by
  have h := zpowZtwo_natCast isProP_two_unitsPadicInt u 2
  norm_num at h
  exact h

/-- `S² = X^{2c₀}`: the `σ`-row of `chiSq_sq_eq_lam`. -/
theorem zpowZtwo_rootXUnit_sq_pivotExp :
    zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 2) sqPivotExp = SvalUnit ^ 2 := by
  rw [← zpowZtwo_unit_two rootXUnit, zpowZtwo_zpowZtwo, mul_comm (2 : ℤ_[2]) sqPivotExp,
    ← zpowZtwo_zpowZtwo, zpowZtwo_rootXUnit_sqPivotExp, zpowZtwo_unit_two]

/-- **The orientation is the `X`-power of the χ-exponent row, up to torsion**:
`χ_sq(x)² = X^{2λ(x)}` for every `x`.  The `x₁`-row is where the torsion sits — `Y = −X²`, and
squaring kills the sign (`YvalUnit_sq_eq`). -/
theorem chiSq_sq_eq_lam (h : ℕ) (x : (DSq h : Type)) :
    (chiSq h x) ^ 2 = xPowLamSq h x := by
  have hext : unitsSquareHom.comp (chiSq h) = xPowLamSq h := by
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · show (chiSq h (dsqSigma h)) ^ 2 = xPowLamSq h (dsqSigma h)
      rw [chiSq_sigma, xPowLamSq_apply, nuLam_sigma, toAdd_ofAdd,
        zpowZtwo_rootXUnit_sq_pivotExp]
    · show (chiSq h (dsqX0 h)) ^ 2 = xPowLamSq h (dsqX0 h)
      rw [chiSq_x0, xPowLamSq_apply, nuLam_x0, toAdd_ofAdd,
        zpowZtwo_one_exp]
    · show (chiSq h (dsqX1 h)) ^ 2 = xPowLamSq h (dsqX1 h)
      rw [chiSq_x1, xPowLamSq_apply, nuLam_x1, toAdd_ofAdd, zpowZtwo_unit_two, YvalUnit_sq_eq,
        ← pow_mul]
    · show (chiSq h (sqGen h (sqHandleIdxU j))) ^ 2 = xPowLamSq h (sqGen h (sqHandleIdxU j))
      rw [chiSq_handleU, xPowLamSq_apply, nuLam_handleU, one_pow]
      exact (zpowZtwo_zero_exp isProP_two_unitsPadicInt _).symm
    · show (chiSq h (sqGen h (sqHandleIdxV j))) ^ 2 = xPowLamSq h (sqGen h (sqHandleIdxV j))
      rw [chiSq_handleV, xPowLamSq_apply, nuLam_handleV, one_pow]
      exact (zpowZtwo_zero_exp isProP_two_unitsPadicInt _).symm
  exact DFunLike.congr_fun hext x

/-- `X² ≠ 1` — the mod-16 pin (`X ≡ 5`, `5² = 25 ≡ 9`). -/
theorem rootXUnit_sq_ne_one : (rootXUnit ^ 2 : ℤ_[2]ˣ) ≠ 1 := by
  intro hx
  have hval : (rootX : ℤ_[2]) ^ 2 = 1 := by
    have := congrArg (fun u : ℤ_[2]ˣ => (u : ℤ_[2])) hx
    simpa [Units.val_pow_eq_pow_val, val_rootXUnit] using this
  have h16 : PadicInt.toZModPow 4 ((rootX : ℤ_[2]) ^ 2) = PadicInt.toZModPow 4 1 := by
    rw [hval]
  rw [map_pow, rootX_toZModPow_four, map_one] at h16
  exact absurd h16 (by decide)

/-- **THE REFUTATION**: at `h ≥ 1`, the one-binder handle stratum is **false** whenever the
exponent `c` misses the canonical one modulo `2` — in particular at every non-unit `c`, and at
`c = 0`.

*Witness*: `ν' = (c₀, 1, 2, 1, 0)` (§1).  Its pivot row is `c₀ − c`, a unit by hypothesis, so
the binder applies; but the correction it produces would fix both core rows and kill the handle
rows, forcing `ν'∘Ψ = λ` and hence `χ_sq(x)² = X^{2λ(x)}` at `x = Ψ⁻¹(u₀)`, where the left side
is `χ_sq(u₀)² = 1` and the right side is `X²`. -/
theorem not_sqHandleMixFixesCore {h : ℕ} (hh : 0 < h) {c : ℤ_[2]}
    (hc : IsUnit (sqPivotExp - c)) : ¬ SqHandleMixFixesCore h c := by
  intro H
  have hpiv : IsUnit (toAdd (nuWitness h (sqMixPivotElem h c))) := by
    rw [toAdd_nuWitness_sqMixPivotElem]
    exact hc
  obtain ⟨Ψ, hchi, hU, hV, hsig, hx0⟩ := H (nuWitness h) hpiv
  -- the transported marking is the χ-exponent row `λ`
  have hmu : (nuWitness h).comp (autHom Ψ) = nuLam h := by
    refine dsq_hom_ext _ _ fun i => ?_
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · show nuWitness h (Ψ (dsqSigma h)) = nuLam h (dsqSigma h)
      rw [hsig, nuWitness_sigma, nuLam_sigma]
    · show nuWitness h (Ψ (dsqX0 h)) = nuLam h (dsqX0 h)
      rw [hx0, nuWitness_x0, nuLam_x0]
    · show nuWitness h (Ψ (dsqX1 h)) = nuLam h (dsqX1 h)
      refine Multiplicative.toAdd.injective ?_
      have hrow := toAdd_nu_dsqX1 ((nuWitness h).comp (autHom Ψ))
      rw [show ((nuWitness h).comp (autHom Ψ)) (dsqX1 h) = nuWitness h (Ψ (dsqX1 h)) from rfl,
        show ((nuWitness h).comp (autHom Ψ)) (dsqX0 h) = nuWitness h (Ψ (dsqX0 h)) from rfl,
        hx0, nuWitness_x0, toAdd_ofAdd, mul_one] at hrow
      rw [hrow, nuLam_x1, toAdd_ofAdd]
    · show nuWitness h (Ψ (sqGen h (sqHandleIdxU j))) = nuLam h (sqGen h (sqHandleIdxU j))
      rw [hU j, nuLam_handleU]
    · show nuWitness h (Ψ (sqGen h (sqHandleIdxV j))) = nuLam h (sqGen h (sqHandleIdxV j))
      rw [hV j, nuLam_handleV]
  -- evaluate the orientation identity at `Ψ⁻¹(u₀)`
  set j0 : Fin h := ⟨0, hh⟩ with hj0
  set y : (DSq h : Type) := Ψ.symm (sqGen h (sqHandleIdxU j0)) with hy
  have hchiy : chiSq h y = 1 := by
    have := hchi y
    rw [hy, Ψ.apply_symm_apply, chiSq_handleU] at this
    exact this.symm
  have hlamy : nuLam h y = ofAdd (1 : ℤ_[2]) := by
    have hval := DFunLike.congr_fun hmu y
    rw [show ((nuWitness h).comp (autHom Ψ)) y = nuWitness h (Ψ y) from rfl, hy,
      Ψ.apply_symm_apply, nuWitness_handleU] at hval
    exact hval.symm
  have hkey := chiSq_sq_eq_lam h y
  rw [hchiy, one_pow, xPowLamSq_apply, hlamy, toAdd_ofAdd, zpowZtwo_one_exp] at hkey
  exact rootXUnit_sq_ne_one hkey.symm

end Refutation

/-! ## §3 The exponent is forced

`SqHandleMixFixesCore h c`'s conclusion is `c`-free, and its hypothesis
`IsUnit (ν'(σ) − c·ν'(x₀))` only sees `c` modulo `2`.  So the binder is a function of `c mod 2`
— and §2 kills the even class. -/

section Normalization

/-- In `ℤ₂`, being a unit is exactly being odd. -/
theorem isUnit_iff_not_two_dvd {x : ℤ_[2]} : IsUnit x ↔ ¬ (2 : ℤ_[2]) ∣ x := by
  refine ⟨fun hu hdvd => ?_, isUnit_of_not_two_dvd⟩
  exact not_isUnit_two (isUnit_of_dvd_unit hdvd hu)

/-- Two odd `2`-adics differ by an even one. -/
theorem two_dvd_sub_of_isUnit {a b : ℤ_[2]} (ha : IsUnit a) (hb : IsUnit b) :
    (2 : ℤ_[2]) ∣ a - b := by
  obtain ⟨s, hs⟩ := two_dvd_sub_one_of_isUnit ha
  obtain ⟨t, ht⟩ := two_dvd_sub_one_of_isUnit hb
  exact ⟨s - t, by linear_combination hs - ht⟩

/-- Congruent exponents give **equivalent** binders: the pivot rows differ by a multiple of
`2`. -/
theorem sqHandleMixFixesCore_congr (h : ℕ) {c c' : ℤ_[2]} (hcc : (2 : ℤ_[2]) ∣ c - c') :
    SqHandleMixFixesCore h c ↔ SqHandleMixFixesCore h c' := by
  have key : ∀ d d' : ℤ_[2], (2 : ℤ_[2]) ∣ d - d' →
      SqHandleMixFixesCore h d → SqHandleMixFixesCore h d' := by
    intro d d' hdd H nu' hpiv
    refine H nu' ?_
    rw [toAdd_nu_sqMixPivotElem] at hpiv ⊢
    obtain ⟨t, ht⟩ := hdd
    rw [isUnit_iff_not_two_dvd] at hpiv ⊢
    intro hdvd
    refine hpiv ?_
    obtain ⟨s, hs⟩ := hdvd
    exact ⟨s + t * toAdd (nu' (dsqX0 h)), by linear_combination hs + toAdd (nu' (dsqX0 h)) * ht⟩
  exact ⟨key c c' hcc, key c' c (by
    obtain ⟨t, ht⟩ := hcc
    exact ⟨-t, by linear_combination -ht⟩)⟩

/-- **The exponent must be a unit** at `h ≥ 1`. -/
theorem isUnit_of_sqHandleMixFixesCore {h : ℕ} (hh : 0 < h) {c : ℤ_[2]}
    (H : SqHandleMixFixesCore h c) : IsUnit c := by
  by_contra hcu
  rw [isUnit_iff_not_two_dvd, not_not] at hcu
  refine not_sqHandleMixFixesCore hh ?_ H
  rw [isUnit_iff_not_two_dvd]
  intro hdvd
  obtain ⟨s, hs⟩ := hdvd
  obtain ⟨t, ht⟩ := hcu
  refine (isUnit_iff_not_two_dvd.mp isUnit_sqPivotExp) ⟨s + t, ?_⟩
  linear_combination hs + ht

/-- **The sharp form**: at `h ≥ 1` the one-binder handle stratum at any exponent is exactly
"`c` is a unit" plus the canonical-exponent statement. -/
theorem sqHandleMixFixesCore_iff {h : ℕ} (hh : 0 < h) {c : ℤ_[2]} :
    SqHandleMixFixesCore h c ↔ IsUnit c ∧ SqHandleMixFixesCore h sqPivotExp := by
  constructor
  · intro H
    have hcu := isUnit_of_sqHandleMixFixesCore hh H
    exact ⟨hcu, (sqHandleMixFixesCore_congr h
      (two_dvd_sub_of_isUnit hcu isUnit_sqPivotExp)).mp H⟩
  · rintro ⟨hcu, H⟩
    exact (sqHandleMixFixesCore_congr h
      (two_dvd_sub_of_isUnit isUnit_sqPivotExp hcu)).mp H

/-- The refutation, at the shape a consumer meets it: `c = 0` (the bare `σ`-pivot) is
**unavailable** at every positive handle count. -/
theorem not_sqHandleMixFixesCore_zero {h : ℕ} (hh : 0 < h) :
    ¬ SqHandleMixFixesCore h 0 := by
  refine not_sqHandleMixFixesCore hh ?_
  rw [sub_zero]
  exact isUnit_sqPivotExp

end Normalization

/-! ## §4 What ports: the two intra-handle transvections

`HandleMix.lean`'s `handleWord_tau_u`/`handleWord_tau_v` are family-agnostic — they only need
the relator's handle block — so the `L_sq` relator supports memo §5.1's two exact transvections
at every 2-adic exponent.  Unlike HM2's `Φ_j`, these touch **no** core letter, which is exactly
why they survive the `L_sq` orientation (wall 2 of the module docstring) and why they fix the two
core rows of `SqHandleMixFixesCore` on the nose. -/

section Transvections

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {h : ℕ}

/-! ### Index bookkeeping for `Fin (sqRank h)` -/

theorem sqHandleIdxU_injective : Function.Injective (sqHandleIdxU (h := h)) := by
  intro i j hij
  have h1 : (3 + 2 * (i : ℕ)) = 3 + 2 * (j : ℕ) := by
    rw [← sqHandleIdxU_val i, ← sqHandleIdxU_val j, hij]
  exact Fin.ext (by omega)

theorem sqHandleIdxV_injective : Function.Injective (sqHandleIdxV (h := h)) := by
  intro i j hij
  have h1 : (4 + 2 * (i : ℕ)) = 4 + 2 * (j : ℕ) := by
    rw [← sqHandleIdxV_val i, ← sqHandleIdxV_val j, hij]
  exact Fin.ext (by omega)

/-- The two letters of a handle pair never collide: `3 + 2i` is odd, `4 + 2j` is even. -/
theorem sqHandleIdxU_ne_sqHandleIdxV (i j : Fin h) :
    (sqHandleIdxU i : Fin (sqRank h)) ≠ sqHandleIdxV j := by
  intro hij
  have h1 : (3 + 2 * (i : ℕ)) = 4 + 2 * (j : ℕ) := by
    rw [← sqHandleIdxU_val i, ← sqHandleIdxV_val j, hij]
  omega

/-- Handle letters are never core letters. -/
theorem sqHandleIdxU_ne_of_val_lt (j : Fin h) {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    (sqHandleIdxU j : Fin (sqRank h)) ≠ i := by
  intro hij
  rw [← hij, sqHandleIdxU_val] at hi
  omega

theorem sqHandleIdxV_ne_of_val_lt (j : Fin h) {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    (sqHandleIdxV j : Fin (sqRank h)) ≠ i := by
  intro hij
  rw [← hij, sqHandleIdxV_val] at hi
  omega

/-! ### The two substitutions -/

/-- **`τ_{v_j}(k)` on `L_sq` markings**: `u_j ↦ v_j^k·u_j`, exact for every 2-adic `k`. -/
noncomputable def sqTauUMark (hP : IsProP 2 P) (j : Fin h) (k : ℤ_[2])
    (m : Fin (sqRank h) → P) : Fin (sqRank h) → P :=
  Function.update m (sqHandleIdxU j) (zpowZtwo hP (m (sqHandleIdxV j)) k * m (sqHandleIdxU j))

/-- **`τ_{u_j}(k)` on `L_sq` markings**: `v_j ↦ u_j^k·v_j`. -/
noncomputable def sqTauVMark (hP : IsProP 2 P) (j : Fin h) (k : ℤ_[2])
    (m : Fin (sqRank h) → P) : Fin (sqRank h) → P :=
  Function.update m (sqHandleIdxV j) (zpowZtwo hP (m (sqHandleIdxU j)) k * m (sqHandleIdxV j))

variable (hP : IsProP 2 P) (j : Fin h) (k l : ℤ_[2]) (m : Fin (sqRank h) → P)

@[simp] theorem sqTauUMark_self :
    sqTauUMark hP j k m (sqHandleIdxU j)
      = zpowZtwo hP (m (sqHandleIdxV j)) k * m (sqHandleIdxU j) := Function.update_self _ _ _

theorem sqTauUMark_of_ne {i : Fin (sqRank h)} (hi : i ≠ sqHandleIdxU j) :
    sqTauUMark hP j k m i = m i := Function.update_of_ne hi _ _

@[simp] theorem sqTauVMark_self :
    sqTauVMark hP j k m (sqHandleIdxV j)
      = zpowZtwo hP (m (sqHandleIdxU j)) k * m (sqHandleIdxV j) := Function.update_self _ _ _

theorem sqTauVMark_of_ne {i : Fin (sqRank h)} (hi : i ≠ sqHandleIdxV j) :
    sqTauVMark hP j k m i = m i := Function.update_of_ne hi _ _

theorem sqTauUMark_core {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    sqTauUMark hP j k m i = m i :=
  sqTauUMark_of_ne _ _ _ _ (Ne.symm (sqHandleIdxU_ne_of_val_lt j hi))

theorem sqTauVMark_core {i : Fin (sqRank h)} (hi : (i : ℕ) < 3) :
    sqTauVMark hP j k m i = m i :=
  sqTauVMark_of_ne _ _ _ _ (Ne.symm (sqHandleIdxV_ne_of_val_lt j hi))

@[simp] theorem sqTauUMark_handleV (i : Fin h) :
    sqTauUMark hP j k m (sqHandleIdxV i) = m (sqHandleIdxV i) :=
  sqTauUMark_of_ne _ _ _ _ (Ne.symm (sqHandleIdxU_ne_sqHandleIdxV j i))

@[simp] theorem sqTauVMark_handleU (i : Fin h) :
    sqTauVMark hP j k m (sqHandleIdxU i) = m (sqHandleIdxU i) :=
  sqTauVMark_of_ne _ _ _ _ (sqHandleIdxU_ne_sqHandleIdxV i j)

theorem sqTauUMark_handleU_of_ne {i : Fin h} (hi : i ≠ j) :
    sqTauUMark hP j k m (sqHandleIdxU i) = m (sqHandleIdxU i) :=
  sqTauUMark_of_ne _ _ _ _ fun hc => hi (sqHandleIdxU_injective hc)

theorem sqTauVMark_handleV_of_ne {i : Fin h} (hi : i ≠ j) :
    sqTauVMark hP j k m (sqHandleIdxV i) = m (sqHandleIdxV i) :=
  sqTauVMark_of_ne _ _ _ _ fun hc => hi (sqHandleIdxV_injective hc)

/-! ### One-parameter group laws, naturality, and the relator -/

theorem sqTauUMark_sqTauUMark :
    sqTauUMark hP j k (sqTauUMark hP j l m) = sqTauUMark hP j (k + l) m := by
  funext i
  by_cases hi : i = sqHandleIdxU j
  · subst hi
    rw [sqTauUMark_self, sqTauUMark_handleV, sqTauUMark_self, sqTauUMark_self,
      zpowZtwo_add, mul_assoc]
  rw [sqTauUMark_of_ne _ _ _ _ hi, sqTauUMark_of_ne _ _ _ _ hi, sqTauUMark_of_ne _ _ _ _ hi]

theorem sqTauVMark_sqTauVMark :
    sqTauVMark hP j k (sqTauVMark hP j l m) = sqTauVMark hP j (k + l) m := by
  funext i
  by_cases hi : i = sqHandleIdxV j
  · subst hi
    rw [sqTauVMark_self, sqTauVMark_handleU, sqTauVMark_self, sqTauVMark_self,
      zpowZtwo_add, mul_assoc]
  rw [sqTauVMark_of_ne _ _ _ _ hi, sqTauVMark_of_ne _ _ _ _ hi, sqTauVMark_of_ne _ _ _ _ hi]

@[simp] theorem sqTauUMark_zero : sqTauUMark hP j 0 m = m := by
  funext i
  by_cases hi : i = sqHandleIdxU j
  · subst hi
    rw [sqTauUMark_self, zpowZtwo_zero_exp, one_mul]
  rw [sqTauUMark_of_ne _ _ _ _ hi]

@[simp] theorem sqTauVMark_zero : sqTauVMark hP j 0 m = m := by
  funext i
  by_cases hi : i = sqHandleIdxV j
  · subst hi
    rw [sqTauVMark_self, zpowZtwo_zero_exp, one_mul]
  rw [sqTauVMark_of_ne _ _ _ _ hi]

theorem map_sqTauUMark {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hQ : IsProP 2 Q) (f : ContinuousMonoidHom P Q) (i : Fin (sqRank h)) :
    f (sqTauUMark hP j k m i) = sqTauUMark hQ j k (fun i => f (m i)) i := by
  by_cases hi : i = sqHandleIdxU j
  · subst hi
    rw [sqTauUMark_self, sqTauUMark_self, map_mul, map_zpowZtwo hP hQ]
  · rw [sqTauUMark_of_ne _ _ _ _ hi, sqTauUMark_of_ne _ _ _ _ hi]

theorem map_sqTauVMark {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hQ : IsProP 2 Q) (f : ContinuousMonoidHom P Q) (i : Fin (sqRank h)) :
    f (sqTauVMark hP j k m i) = sqTauVMark hQ j k (fun i => f (m i)) i := by
  by_cases hi : i = sqHandleIdxV j
  · subst hi
    rw [sqTauVMark_self, sqTauVMark_self, map_mul, map_zpowZtwo hP hQ]
  · rw [sqTauVMark_of_ne _ _ _ _ hi, sqTauVMark_of_ne _ _ _ _ hi]

/-- **`τ_{v_j}(k)` fixes the `L_sq` relator on the nose** — the core word is untouched and
`handleWord_tau_u` closes the handle block. -/
theorem sqRelWord_sqTauUMark : sqRelWord (sqTauUMark hP j k m) = sqRelWord m := by
  have hU : (fun i => sqTauUMark hP j k m (sqHandleIdxU i))
      = Function.update (fun i => m (sqHandleIdxU i)) j
          (zpowZtwo hP (m (sqHandleIdxV j)) k * m (sqHandleIdxU j)) := by
    funext i
    by_cases hij : i = j
    · subst hij
      rw [sqTauUMark_self, Function.update_self]
    · rw [sqTauUMark_handleU_of_ne _ _ _ _ hij, Function.update_of_ne hij]
  have hV : (fun i => sqTauUMark hP j k m (sqHandleIdxV i)) = fun i => m (sqHandleIdxV i) := by
    funext i
    exact sqTauUMark_handleV _ _ _ _ i
  rw [sqRelWord, sqRelWord, hU, hV, sqTauUMark_core _ _ _ _ (by rw [sqVal_zero]; omega),
    sqTauUMark_core _ _ _ _ (by rw [sqVal_one]; omega),
    sqTauUMark_core _ _ _ _ (by rw [sqVal_two]; omega),
    handleWord_tau_u hP (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i)) j k]

/-- **`τ_{u_j}(k)` fixes the `L_sq` relator on the nose.** -/
theorem sqRelWord_sqTauVMark : sqRelWord (sqTauVMark hP j k m) = sqRelWord m := by
  have hV : (fun i => sqTauVMark hP j k m (sqHandleIdxV i))
      = Function.update (fun i => m (sqHandleIdxV i)) j
          (zpowZtwo hP (m (sqHandleIdxU j)) k * m (sqHandleIdxV j)) := by
    funext i
    by_cases hij : i = j
    · subst hij
      rw [sqTauVMark_self, Function.update_self]
    · rw [sqTauVMark_handleV_of_ne _ _ _ _ hij, Function.update_of_ne hij]
  have hU : (fun i => sqTauVMark hP j k m (sqHandleIdxU i)) = fun i => m (sqHandleIdxU i) := by
    funext i
    exact sqTauVMark_handleU _ _ _ _ i
  rw [sqRelWord, sqRelWord, hU, hV, sqTauVMark_core _ _ _ _ (by rw [sqVal_zero]; omega),
    sqTauVMark_core _ _ _ _ (by rw [sqVal_one]; omega),
    sqTauVMark_core _ _ _ _ (by rw [sqVal_two]; omega),
    handleWord_tau_v hP (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i)) j k]

end Transvections

/-! ### The two automorphism families -/

section TauEquiv

variable {h : ℕ}

/-- Generators decide a left inverse on `D_sq`. -/
theorem dsq_leftInverse (f g : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hgen : ∀ i, f (g (sqGen h i)) = sqGen h i) : Function.LeftInverse f g := by
  have hext : f.comp g = ContinuousMonoidHom.id (DSq h : Type) := dsq_hom_ext _ _ hgen
  exact fun x => DFunLike.congr_fun hext x

/-- A one-parameter family of substitutions with `S k ∘ S l = S (k+l)` and `S 0 = id` is a family
of *automorphisms* (HM4's `dmParamEquiv`, at the `L_sq` core). -/
noncomputable def sqParamEquiv
    (L : ℤ_[2] → ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (S : ℤ_[2] → (Fin (sqRank h) → (DSq h : Type)) → Fin (sqRank h) → (DSq h : Type))
    (hL : ∀ k i, L k (sqGen h i) = S k (sqGen h) i)
    (hnat : ∀ (k : ℤ_[2]) (f : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
      (m : Fin (sqRank h) → (DSq h : Type)) i, f (S k m i) = S k (fun i => f (m i)) i)
    (hadd : ∀ (k l : ℤ_[2]) m, S k (S l m) = S (k + l) m) (hzero : ∀ m, S 0 m = m)
    (k : ℤ_[2]) : ContinuousMulEquiv (DSq h : Type) (DSq h : Type) :=
  continuousMulEquivOfBijective (L k) (Function.bijective_iff_has_inverse.mpr
    ⟨L (-k),
      dsq_leftInverse (L (-k)) (L k) fun i => by
        have hg : (fun i => L (-k) (sqGen h i)) = S (-k) (sqGen h) := funext (hL (-k))
        rw [hL, hnat, hg, hadd, add_neg_cancel, hzero],
      dsq_leftInverse (L k) (L (-k)) fun i => by
        have hg : (fun i => L k (sqGen h i)) = S k (sqGen h) := funext (hL k)
        rw [hL, hnat, hg, hadd, neg_add_cancel, hzero]⟩)

/-- `τ_{v_j}(k)` on `D_sq`, as a continuous endomorphism. -/
noncomputable def sqTauUHom (h : ℕ) (j : Fin h) (k : ℤ_[2]) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h) (sqTauUMark (isProP_DSq h) j k (sqGen h))
    (by rw [sqRelWord_sqTauUMark]; exact dsq_relation h)

/-- `τ_{u_j}(k)` on `D_sq`, as a continuous endomorphism. -/
noncomputable def sqTauVHom (h : ℕ) (j : Fin h) (k : ℤ_[2]) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h) (sqTauVMark (isProP_DSq h) j k (sqGen h))
    (by rw [sqRelWord_sqTauVMark]; exact dsq_relation h)

@[simp] theorem sqTauUHom_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (sqRank h)) :
    sqTauUHom h j k (sqGen h i) = sqTauUMark (isProP_DSq h) j k (sqGen h) i :=
  sqLiftHom_gen _ _ _ _ _

@[simp] theorem sqTauVHom_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (sqRank h)) :
    sqTauVHom h j k (sqGen h i) = sqTauVMark (isProP_DSq h) j k (sqGen h) i :=
  sqLiftHom_gen _ _ _ _ _

/-- **`τ_{v_j}(k)` as a continuous automorphism of `D_sq`**, for every `k : ℤ_[2]`. -/
noncomputable def sqTauUEquiv (h : ℕ) (j : Fin h) (k : ℤ_[2]) :
    ContinuousMulEquiv (DSq h : Type) (DSq h : Type) :=
  sqParamEquiv (sqTauUHom h j) (sqTauUMark (isProP_DSq h) j) (sqTauUHom_gen j)
    (fun k f m i => map_sqTauUMark (isProP_DSq h) j k m (isProP_DSq h) f i)
    (fun k l m => sqTauUMark_sqTauUMark _ j k l m) (fun m => sqTauUMark_zero _ j m) k

/-- **`τ_{u_j}(k)` as a continuous automorphism of `D_sq`**. -/
noncomputable def sqTauVEquiv (h : ℕ) (j : Fin h) (k : ℤ_[2]) :
    ContinuousMulEquiv (DSq h : Type) (DSq h : Type) :=
  sqParamEquiv (sqTauVHom h j) (sqTauVMark (isProP_DSq h) j) (sqTauVHom_gen j)
    (fun k f m i => map_sqTauVMark (isProP_DSq h) j k m (isProP_DSq h) f i)
    (fun k l m => sqTauVMark_sqTauVMark _ j k l m) (fun m => sqTauVMark_zero _ j m) k

@[simp] theorem sqTauUEquiv_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (sqRank h)) :
    sqTauUEquiv h j k (sqGen h i) = sqTauUMark (isProP_DSq h) j k (sqGen h) i :=
  sqTauUHom_gen j k i

@[simp] theorem sqTauVEquiv_gen (j : Fin h) (k : ℤ_[2]) (i : Fin (sqRank h)) :
    sqTauVEquiv h j k (sqGen h i) = sqTauVMark (isProP_DSq h) j k (sqGen h) i :=
  sqTauVHom_gen j k i

/-! ### The rows the clearing recipe consumes

Every `τ` fixes the three core letters and all but one handle letter **literally** — the
strongest form, and the one that composes without bookkeeping. -/

section TauRows

variable {h : ℕ} (j : Fin h) (k : ℤ_[2])

@[simp] theorem sqTauUEquiv_sigma : sqTauUEquiv h j k (dsqSigma h) = dsqSigma h := by
  show sqTauUEquiv h j k (sqGen h 0) = sqGen h 0
  rw [sqTauUEquiv_gen, sqTauUMark_core _ _ _ _ (by rw [sqVal_zero]; omega)]

@[simp] theorem sqTauUEquiv_x0 : sqTauUEquiv h j k (dsqX0 h) = dsqX0 h := by
  show sqTauUEquiv h j k (sqGen h 1) = sqGen h 1
  rw [sqTauUEquiv_gen, sqTauUMark_core _ _ _ _ (by rw [sqVal_one]; omega)]

@[simp] theorem sqTauVEquiv_sigma : sqTauVEquiv h j k (dsqSigma h) = dsqSigma h := by
  show sqTauVEquiv h j k (sqGen h 0) = sqGen h 0
  rw [sqTauVEquiv_gen, sqTauVMark_core _ _ _ _ (by rw [sqVal_zero]; omega)]

@[simp] theorem sqTauVEquiv_x0 : sqTauVEquiv h j k (dsqX0 h) = dsqX0 h := by
  show sqTauVEquiv h j k (sqGen h 1) = sqGen h 1
  rw [sqTauVEquiv_gen, sqTauVMark_core _ _ _ _ (by rw [sqVal_one]; omega)]

@[simp] theorem sqTauUEquiv_handleV (i : Fin h) :
    sqTauUEquiv h j k (sqGen h (sqHandleIdxV i)) = sqGen h (sqHandleIdxV i) := by
  rw [sqTauUEquiv_gen, sqTauUMark_handleV]

theorem sqTauUEquiv_handleU_of_ne {i : Fin h} (hi : i ≠ j) :
    sqTauUEquiv h j k (sqGen h (sqHandleIdxU i)) = sqGen h (sqHandleIdxU i) := by
  rw [sqTauUEquiv_gen, sqTauUMark_handleU_of_ne _ _ _ _ hi]

@[simp] theorem sqTauVEquiv_handleU (i : Fin h) :
    sqTauVEquiv h j k (sqGen h (sqHandleIdxU i)) = sqGen h (sqHandleIdxU i) := by
  rw [sqTauVEquiv_gen, sqTauVMark_handleU]

theorem sqTauVEquiv_handleV_of_ne {i : Fin h} (hi : i ≠ j) :
    sqTauVEquiv h j k (sqGen h (sqHandleIdxV i)) = sqGen h (sqHandleIdxV i) := by
  rw [sqTauVEquiv_gen, sqTauVMark_handleV_of_ne _ _ _ _ hi]

/-- **`τ_{v_j}(k)` preserves the orientation**: `χ_sq` is trivial on the whole handle plane, so
the only moved slot picks up `χ_sq(v_j)^k = 1`.  (This is `IsClearBlind` restricted to the part
of the `L_sq` frame where it *is* true — see wall 2 of the module docstring.) -/
theorem chiSq_sqTauUEquiv (x : (DSq h : Type)) :
    chiSq h (sqTauUEquiv h j k x) = chiSq h x := by
  have hext : (chiSq h).comp (autHom (sqTauUEquiv h j k)) = chiSq h := by
    refine dsq_hom_ext _ _ fun i => ?_
    show chiSq h (sqTauUEquiv h j k (sqGen h i)) = chiSq h (sqGen h i)
    rw [sqTauUEquiv_gen]
    by_cases hi : i = sqHandleIdxU j
    · subst hi
      rw [sqTauUMark_self, map_mul,
        map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), chiSq_handleV,
        zpowZtwo_one_base, one_mul]
    · rw [sqTauUMark_of_ne _ _ _ _ hi]
  exact DFunLike.congr_fun hext x

/-- **`τ_{u_j}(k)` preserves the orientation.** -/
theorem chiSq_sqTauVEquiv (x : (DSq h : Type)) :
    chiSq h (sqTauVEquiv h j k x) = chiSq h x := by
  have hext : (chiSq h).comp (autHom (sqTauVEquiv h j k)) = chiSq h := by
    refine dsq_hom_ext _ _ fun i => ?_
    show chiSq h (sqTauVEquiv h j k (sqGen h i)) = chiSq h (sqGen h i)
    rw [sqTauVEquiv_gen]
    by_cases hi : i = sqHandleIdxV j
    · subst hi
      rw [sqTauVMark_self, map_mul,
        map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), chiSq_handleU,
        zpowZtwo_one_base, one_mul]
    · rw [sqTauVMark_of_ne _ _ _ _ hi]
  exact DFunLike.congr_fun hext x

/-- The moved `ν`-row of `τ_{u_j}(k)`: `ν'(v_j) ↦ ν'(v_j) + k·ν'(u_j)`. -/
theorem toAdd_nu_sqTauVEquiv_self
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' (sqTauVEquiv h j k (sqGen h (sqHandleIdxV j))))
      = k * toAdd (nu' (sqGen h (sqHandleIdxU j)))
        + toAdd (nu' (sqGen h (sqHandleIdxV j))) := by
  rw [sqTauVEquiv_gen, sqTauVMark_self, map_mul, toAdd_mul,
    toAdd_map_zpowZtwo (isProP_DSq h) nu' _ k]

/-- The moved `ν`-row of `τ_{v_j}(k)`: `ν'(u_j) ↦ ν'(u_j) + k·ν'(v_j)`. -/
theorem toAdd_nu_sqTauUEquiv_self
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    toAdd (nu' (sqTauUEquiv h j k (sqGen h (sqHandleIdxU j))))
      = k * toAdd (nu' (sqGen h (sqHandleIdxV j)))
        + toAdd (nu' (sqGen h (sqHandleIdxU j))) := by
  rw [sqTauUEquiv_gen, sqTauUMark_self, map_mul, toAdd_mul,
    toAdd_map_zpowZtwo (isProP_DSq h) nu' _ k]

end TauRows

/-! ### Handle-local automorphisms, and the `SL₂` normalisation -/

section Normalize

variable {h : ℕ}

/-- **A handle-local move**: χ-preserving, and fixing the two marked core letters and every
handle letter outside `j` **literally**.  Both `τ` families have this shape, and it is closed
under composition. -/
def IsSqHandleLocal (h : ℕ) (j : Fin h)
    (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) : Prop :=
  (∀ x, chiSq h (Ψ x) = chiSq h x)
    ∧ Ψ (dsqSigma h) = dsqSigma h
    ∧ Ψ (dsqX0 h) = dsqX0 h
    ∧ (∀ i : Fin h, i ≠ j → Ψ (sqGen h (sqHandleIdxU i)) = sqGen h (sqHandleIdxU i))
    ∧ (∀ i : Fin h, i ≠ j → Ψ (sqGen h (sqHandleIdxV i)) = sqGen h (sqHandleIdxV i))

theorem isSqHandleLocal_tauU (j : Fin h) (k : ℤ_[2]) :
    IsSqHandleLocal h j (sqTauUEquiv h j k) :=
  ⟨chiSq_sqTauUEquiv j k, sqTauUEquiv_sigma j k, sqTauUEquiv_x0 j k,
    fun _ hi => sqTauUEquiv_handleU_of_ne j k hi, fun i _ => sqTauUEquiv_handleV j k i⟩

theorem isSqHandleLocal_tauV (j : Fin h) (k : ℤ_[2]) :
    IsSqHandleLocal h j (sqTauVEquiv h j k) :=
  ⟨chiSq_sqTauVEquiv j k, sqTauVEquiv_sigma j k, sqTauVEquiv_x0 j k,
    fun i _ => sqTauVEquiv_handleU j k i, fun _ hi => sqTauVEquiv_handleV_of_ne j k hi⟩

theorem isSqHandleLocal_trans {j : Fin h}
    {Ψ₁ Ψ₂ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)}
    (h₁ : IsSqHandleLocal h j Ψ₁) (h₂ : IsSqHandleLocal h j Ψ₂) :
    IsSqHandleLocal h j (Ψ₂.trans Ψ₁) := by
  obtain ⟨c₁, s₁, x₁, u₁, v₁⟩ := h₁
  obtain ⟨c₂, s₂, x₂, u₂, v₂⟩ := h₂
  exact ⟨fun x => (c₁ (Ψ₂ x)).trans (c₂ x),
    show Ψ₁ (Ψ₂ (dsqSigma h)) = dsqSigma h by rw [s₂, s₁],
    show Ψ₁ (Ψ₂ (dsqX0 h)) = dsqX0 h by rw [x₂, x₁],
    fun i hi => show Ψ₁ (Ψ₂ _) = _ by rw [u₂ i hi, u₁ i hi],
    fun i hi => show Ψ₁ (Ψ₂ _) = _ by rw [v₂ i hi, v₁ i hi]⟩

/-- A handle-local move fixes the clearing pivot `w = σ·x₀^{−c}` literally. -/
theorem sqMixPivotElem_of_isSqHandleLocal {j : Fin h}
    {Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)} (hΨ : IsSqHandleLocal h j Ψ)
    (c : ℤ_[2]) : Ψ (sqMixPivotElem h c) = sqMixPivotElem h c := by
  show (autHom Ψ) (sqMixPivotElem h c) = sqMixPivotElem h c
  rw [sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) (isProP_DSq h) (autHom Ψ) (dsqX0 h) c]
  rw [show (autHom Ψ) (dsqSigma h) = Ψ (dsqSigma h) from rfl, hΨ.2.1,
    show (autHom Ψ) (dsqX0 h) = Ψ (dsqX0 h) from rfl, hΨ.2.2.1]

/-- **`SL₂` normalisation of one handle plane**: `τ`-moves alone bring the `v_j`-row to `0`,
without touching the two core rows or any other handle.  (Divisibility in `ℤ₂` is total, so one
or two elementary transvections suffice; this is the `L_sq` form of memo §5.1's intra-handle
`SL₂(ℤ₂)`.) -/
theorem sq_normalize_handle (h : ℕ) (j : Fin h)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      IsSqHandleLocal h j Ψ ∧ nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1 := by
  have hkill : ∀ mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      toAdd (mu (sqGen h (sqHandleIdxU j))) ∣ toAdd (mu (sqGen h (sqHandleIdxV j))) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        IsSqHandleLocal h j Ψ ∧ mu (Ψ (sqGen h (sqHandleIdxV j))) = 1 := by
    intro mu ⟨t, ht⟩
    refine ⟨sqTauVEquiv h j (-t), isSqHandleLocal_tauV j (-t), ?_⟩
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_nu_sqTauVEquiv_self, ht, toAdd_one]
    ring
  rcases (ValuationRing.iff_dvd_total.mp (inferInstance : ValuationRing ℤ_[2])).total
    (toAdd (nu' (sqGen h (sqHandleIdxU j)))) (toAdd (nu' (sqGen h (sqHandleIdxV j)))) with
    hdvd | ⟨s, hs⟩
  · exact hkill nu' hdvd
  · -- the `v_j`-row divides the `u_j`-row: one `τ_{v_j}` move equalises them first
    set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
      nu'.comp (autHom (sqTauUEquiv h j (1 - s))) with hmu
    have hu : toAdd (mu (sqGen h (sqHandleIdxU j)))
        = toAdd (nu' (sqGen h (sqHandleIdxV j))) := by
      show toAdd (nu' (sqTauUEquiv h j (1 - s) (sqGen h (sqHandleIdxU j)))) = _
      rw [toAdd_nu_sqTauUEquiv_self]
      linear_combination hs
    have hv : toAdd (mu (sqGen h (sqHandleIdxV j)))
        = toAdd (nu' (sqGen h (sqHandleIdxV j))) := by
      show toAdd (nu' (sqTauUEquiv h j (1 - s) (sqGen h (sqHandleIdxV j)))) = _
      rw [sqTauUEquiv_handleV]
    obtain ⟨Ψ₂, hloc₂, hkill₂⟩ := hkill mu ⟨1, by rw [hu, hv, mul_one]⟩
    exact ⟨Ψ₂.trans (sqTauUEquiv h j (1 - s)),
      isSqHandleLocal_trans (isSqHandleLocal_tauU j (1 - s)) hloc₂, hkill₂⟩

end Normalize

/-! ## §5 The residual obligation, and the reduction

One explicitly-shaped automorphism family — the Eichler unipotent of the plane pair
`(⟨w̄⟩, ⟨ū_j, v̄_j⟩)` — closes the whole `L_sq` handle stratum. -/

section Eichler

/-- **The single residual word-level input** (a `def`, never an axiom).  For every handle index
`j`, every 2-adic parameter `k`, and every marking whose `v_j`-row already vanishes, a
χ-preserving continuous automorphism of `D_sq` that

* fixes the two marked core rows,
* shifts the `u_j`-row by `k·ν'(w)`, `w = σ·x₀^{−c}` the clearing pivot, and
* fixes every other handle row.

The `v_j`-row hypothesis is not decoration.  The frame computation behind the shape (mod-2 cup
form; recorded here, not formalised) says the Eichler unipotent of the plane pair
`(⟨w̄⟩, ⟨ū_j, v̄_j⟩)` must shift the core plane by a multiple of `v̄_j` — a pure transvection
`ū_j ↦ ū_j + k·w̄` with everything else fixed is *not* an isometry for odd `k`.  So without the
`v_j`-row hypothesis the two core rows must move, which is exactly what MC5's weaker
`SqHandleMixHypothesis` tolerates and `SqHandleMixFixesCore` does not.  §4's
`sq_normalize_handle` supplies the hypothesis, at no cost to the core rows. -/
def SqHandleEichler (h : ℕ) (c : ℤ_[2]) : Prop :=
  ∀ (j : Fin h) (k : ℤ_[2]) (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])),
    nu' (sqGen h (sqHandleIdxV j)) = 1 →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ x) = chiSq h x)
          ∧ nu' (Ψ (dsqSigma h)) = nu' (dsqSigma h)
          ∧ nu' (Ψ (dsqX0 h)) = nu' (dsqX0 h)
          ∧ toAdd (nu' (Ψ (sqGen h (sqHandleIdxU j))))
              = toAdd (nu' (sqGen h (sqHandleIdxU j))) + k * toAdd (nu' (sqMixPivotElem h c))
          ∧ (∀ i : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV i)))
              = nu' (sqGen h (sqHandleIdxV i)))
          ∧ (∀ i : Fin h, i ≠ j → nu' (Ψ (sqGen h (sqHandleIdxU i)))
              = nu' (sqGen h (sqHandleIdxU i)))

/-- At `h = 0` the residual obligation is vacuous. -/
theorem sqHandleEichler_zero (c : ℤ_[2]) : SqHandleEichler 0 c := fun j => absurd j.2 (by omega)

/-- The residual obligation is never *vacuously* quantified: the standard marking meets its
`v_j`-row hypothesis at every handle (the `L_sq` mirror of `sqHandleMix_hypothesis_nonvacuous`).
So `SqHandleEichler` is a genuine statement about automorphisms, not an empty one. -/
theorem sqHandleEichler_hypothesis_nonvacuous (h : ℕ) (j : Fin h) :
    nuSq h (sqGen h (sqHandleIdxV j)) = 1 := nuSq_handleV h j

variable {h : ℕ} {c : ℤ_[2]}

/-- **One handle, cleared**: normalise the plane with §4's `τ`-moves, then spend one Eichler
move.  Both core rows survive, and no other handle is touched. -/
theorem sq_clear_one_handle (hE : SqHandleEichler h c) (j : Fin h)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hw : IsUnit (toAdd (nu' (sqMixPivotElem h c)))) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (Ψ x) = chiSq h x)
        ∧ nu' (Ψ (dsqSigma h)) = nu' (dsqSigma h)
        ∧ nu' (Ψ (dsqX0 h)) = nu' (dsqX0 h)
        ∧ nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1
        ∧ nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1
        ∧ (∀ i : Fin h, i ≠ j →
            nu' (Ψ (sqGen h (sqHandleIdxU i))) = nu' (sqGen h (sqHandleIdxU i))
            ∧ nu' (Ψ (sqGen h (sqHandleIdxV i))) = nu' (sqGen h (sqHandleIdxV i))) := by
  obtain ⟨Ψ₁, hloc, hv₁⟩ := sq_normalize_handle h j nu'
  set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Ψ₁) with hmudef
  have hmupiv : mu (sqMixPivotElem h c) = nu' (sqMixPivotElem h c) := by
    show nu' (Ψ₁ (sqMixPivotElem h c)) = _
    rw [sqMixPivotElem_of_isSqHandleLocal hloc]
  obtain ⟨d, hd⟩ := hw.exists_right_inv
  obtain ⟨Ψ₂, hchi₂, hs₂, hx₂, hu₂, hv₂, hother₂⟩ :=
    hE j (-(toAdd (mu (sqGen h (sqHandleIdxU j))) * d)) mu (by
      show nu' (Ψ₁ (sqGen h (sqHandleIdxV j))) = 1
      exact hv₁)
  refine ⟨Ψ₂.trans Ψ₁, fun x => (hloc.1 (Ψ₂ x)).trans (hchi₂ x), ?_, ?_, ?_, ?_, ?_⟩
  · show mu (Ψ₂ (dsqSigma h)) = nu' (dsqSigma h)
    rw [hs₂]
    show nu' (Ψ₁ (dsqSigma h)) = _
    rw [hloc.2.1]
  · show mu (Ψ₂ (dsqX0 h)) = nu' (dsqX0 h)
    rw [hx₂]
    show nu' (Ψ₁ (dsqX0 h)) = _
    rw [hloc.2.2.1]
  · show mu (Ψ₂ (sqGen h (sqHandleIdxU j))) = 1
    refine Multiplicative.toAdd.injective ?_
    rw [hu₂, hmupiv, toAdd_one]
    linear_combination (-(toAdd (mu (sqGen h (sqHandleIdxU j))))) * hd
  · show mu (Ψ₂ (sqGen h (sqHandleIdxV j))) = 1
    rw [hv₂ j]
    show nu' (Ψ₁ (sqGen h (sqHandleIdxV j))) = 1
    exact hv₁
  · intro i hi
    refine ⟨?_, ?_⟩
    · show mu (Ψ₂ (sqGen h (sqHandleIdxU i))) = nu' (sqGen h (sqHandleIdxU i))
      rw [hother₂ i hi]
      show nu' (Ψ₁ (sqGen h (sqHandleIdxU i))) = _
      rw [hloc.2.2.2.1 i hi]
    · show mu (Ψ₂ (sqGen h (sqHandleIdxV i))) = nu' (sqGen h (sqHandleIdxV i))
      rw [hv₂ i]
      show nu' (Ψ₁ (sqGen h (sqHandleIdxV i))) = _
      rw [hloc.2.2.2.2 i hi]

/-- The clearing recipe, run over the handles of index `< n`. -/
theorem sq_clear_upto (hE : SqHandleEichler h c) :
    ∀ (n : ℕ) (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])),
      IsUnit (toAdd (nu' (sqMixPivotElem h c))) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ x) = chiSq h x)
          ∧ nu' (Ψ (dsqSigma h)) = nu' (dsqSigma h)
          ∧ nu' (Ψ (dsqX0 h)) = nu' (dsqX0 h)
          ∧ (∀ i : Fin h, (i : ℕ) < n → nu' (Ψ (sqGen h (sqHandleIdxU i))) = 1
              ∧ nu' (Ψ (sqGen h (sqHandleIdxV i))) = 1)
          ∧ (∀ i : Fin h, n ≤ (i : ℕ) →
              nu' (Ψ (sqGen h (sqHandleIdxU i))) = nu' (sqGen h (sqHandleIdxU i))
              ∧ nu' (Ψ (sqGen h (sqHandleIdxV i))) = nu' (sqGen h (sqHandleIdxV i))) := by
  intro n
  induction n with
  | zero =>
    intro nu' _
    exact ⟨ContinuousMulEquiv.refl _, fun _ => rfl, rfl, rfl,
      fun i hi => absurd hi (by omega), fun i _ => ⟨rfl, rfl⟩⟩
  | succ n ih =>
    intro nu' hw
    obtain ⟨Ψ₁, hchi₁, hs₁, hx₁, hclr₁, hfix₁⟩ := ih nu' hw
    by_cases hn : n < h
    · set j : Fin h := ⟨n, hn⟩ with hjdef
      set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
        nu'.comp (autHom Ψ₁) with hmudef
      have hmupiv : toAdd (mu (sqMixPivotElem h c)) = toAdd (nu' (sqMixPivotElem h c)) := by
        rw [toAdd_nu_sqMixPivotElem mu c, toAdd_nu_sqMixPivotElem nu' c]
        rw [show mu (dsqSigma h) = nu' (Ψ₁ (dsqSigma h)) from rfl, hs₁,
          show mu (dsqX0 h) = nu' (Ψ₁ (dsqX0 h)) from rfl, hx₁]
      obtain ⟨Ψ₂, hchi₂, hs₂, hx₂, hu₂, hv₂, hother₂⟩ :=
        sq_clear_one_handle hE j mu (by rw [hmupiv]; exact hw)
      have hne : ∀ i : Fin h, (i : ℕ) ≠ n → i ≠ j := by
        intro i hi hc
        exact hi (by rw [hc, hjdef])
      refine ⟨Ψ₂.trans Ψ₁, fun x => (hchi₁ (Ψ₂ x)).trans (hchi₂ x), ?_, ?_, ?_, ?_⟩
      · show mu (Ψ₂ (dsqSigma h)) = nu' (dsqSigma h)
        rw [hs₂]
        exact hs₁
      · show mu (Ψ₂ (dsqX0 h)) = nu' (dsqX0 h)
        rw [hx₂]
        exact hx₁
      · intro i hi
        by_cases hij : (i : ℕ) = n
        · have : i = j := by rw [hjdef]; exact Fin.ext hij
          subst this
          exact ⟨hu₂, hv₂⟩
        · obtain ⟨hUi, hVi⟩ := hother₂ i (hne i hij)
          refine ⟨?_, ?_⟩
          · show mu (Ψ₂ (sqGen h (sqHandleIdxU i))) = 1
            rw [hUi]
            exact (hclr₁ i (by omega)).1
          · show mu (Ψ₂ (sqGen h (sqHandleIdxV i))) = 1
            rw [hVi]
            exact (hclr₁ i (by omega)).2
      · intro i hi
        obtain ⟨hUi, hVi⟩ := hother₂ i (hne i (by omega))
        refine ⟨?_, ?_⟩
        · show mu (Ψ₂ (sqGen h (sqHandleIdxU i))) = _
          rw [hUi]
          exact (hfix₁ i (by omega)).1
        · show mu (Ψ₂ (sqGen h (sqHandleIdxV i))) = _
          rw [hVi]
          exact (hfix₁ i (by omega)).2
    · refine ⟨Ψ₁, hchi₁, hs₁, hx₁, fun i hi => hclr₁ i ?_, fun i hi => hfix₁ i (by omega)⟩
      have := i.isLt
      omega

/-- **THE REDUCTION**: the single Eichler family discharges the whole `L_sq` handle stratum. -/
theorem sqHandleMixFixesCore_of_eichler (hE : SqHandleEichler h c) :
    SqHandleMixFixesCore h c := by
  intro nu' hw
  obtain ⟨Ψ, hchi, hs, hx, hclr, _⟩ := sq_clear_upto hE h nu' hw
  exact ⟨Ψ, hchi, fun j => (hclr j j.isLt).1, fun j => (hclr j j.isLt).2, hs, hx⟩

/-- **The residual obligation inherits the exponent constraint**: `SqHandleEichler h c` implies
`SqHandleMixFixesCore h c`, so §2 refutes it too at every `c` congruent to `sqPivotExp + 1`
modulo `2`.  Pose the Eichler family at `sqPivotExp`, or not at all. -/
theorem not_sqHandleEichler {h : ℕ} (hh : 0 < h) {c : ℤ_[2]} (hc : IsUnit (sqPivotExp - c)) :
    ¬ SqHandleEichler h c :=
  fun hE => not_sqHandleMixFixesCore hh hc (sqHandleMixFixesCore_of_eichler hE)

end Eichler

/-! ## §6 The `L_sq` core has no clear-blind letter, and the certificate-facing payoff -/

section Payoff

variable {h : ℕ} {c : ℤ_[2]}

/-- `χ_sq(x₀) = X ≢ 1` — the second core letter is not clear-blind either. -/
theorem chiSq_x0_ne_one (h : ℕ) : chiSq h (dsqX0 h) ≠ 1 := by
  rw [chiSq_x0]
  intro hx
  have hval : (rootX : ℤ_[2]) = 1 := by
    have := congrArg (fun u : ℤ_[2]ˣ => (u : ℤ_[2])) hx
    simpa [val_rootXUnit] using this
  have h16 : PadicInt.toZModPow 4 (rootX : ℤ_[2]) = PadicInt.toZModPow 4 1 := by rw [hval]
  rw [rootX_toZModPow_four, map_one] at h16
  exact absurd h16 (by decide)

/-- `χ_sq(x₁) = Y ≢ 1` — nor is the third. -/
theorem chiSq_x1_ne_one (h : ℕ) : chiSq h (dsqX1 h) ≠ 1 := by
  rw [chiSq_x1]
  intro hx
  have hval : (Yval : ℤ_[2]) = 1 := by
    have := congrArg (fun u : ℤ_[2]ˣ => (u : ℤ_[2])) hx
    simpa [val_YvalUnit] using this
  have h16 : PadicInt.toZModPow 4 (Yval : ℤ_[2]) = PadicInt.toZModPow 4 1 := by rw [hval]
  rw [Yval_toZModPow_four, map_one] at h16
  exact absurd h16 (by decide)

/-- **Wall 2, in Lean**: *no* core letter of the `L_sq` presentation is χ-trivial, so HM5's
`IsClearBlind` has no witness at any candidate pivot slot of this word.  The only χ-trivial core
direction is the *combination* `w = σ·x₀^{−c₀}` (`chiSq_sqPivot`), which is why the residual
obligation must be posed as an Eichler unipotent of `⟨w̄⟩` rather than as a letter-for-letter
port of HM2's `Φ_j`. -/
theorem sqCore_no_clearBlind_letter (h : ℕ) :
    chiSq h (dsqSigma h) ≠ 1 ∧ chiSq h (dsqX0 h) ≠ 1 ∧ chiSq h (dsqX1 h) ≠ 1 :=
  ⟨chiSq_sigma_ne_one h, chiSq_x0_ne_one h, chiSq_x1_ne_one h⟩

/-- **The one-binder marked-matching reduction, on the Eichler family alone.** -/
theorem sqMarkedMatching_of_eichler (hE : SqHandleEichler h c)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2])) (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    ∃ u : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, chiSq h (u x) = chiSq h x) ∧ ∀ x, nu' (u x) = nuSq h x :=
  sqMarkedMatching_of_fixesCore (sqHandleMixFixesCore_of_eichler hE) nu' hsigma hx0

/-- MC5's weaker (pivot-row) binder also follows from the Eichler family. -/
theorem sqHandleMixHypothesis_of_eichler (hE : SqHandleEichler h c) :
    SqHandleMixHypothesis h c :=
  sqHandleMixHypothesis_of_fixesCore (sqHandleMixFixesCore_of_eichler hE)

/-- **The abstract-slot certificate production on the Eichler family alone**: with the residual
obligation discharged the `L_sq` certificate needs only the abstract isomorphism, the orientation
matching, continuity, and the packet's `markedDataEq` rows. -/
theorem marked_matching_certificate_sq_of_eichler {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (h : ℕ) (c : ℤ_[2])
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) G)
    (horient : ∀ x, chiG (f x) = chiSq h x)
    (hcont : Continuous fun x : (DSq h : Type) => nuG (f x))
    (hE : SqHandleEichler h c)
    (hsigma : nuG (f (dsqSigma h)) = ofAdd (1 : ℤ_[2]))
    (hx0 : nuG (f (dsqX0 h)) = ofAdd (0 : ℤ_[2])) :
    Nonempty (MarkedCoreCertificateSq h chiG nuG) :=
  marked_matching_certificate_sq_of_fixesCore h c chiG nuG f horient hcont
    (sqHandleMixFixesCore_of_eichler hE) hsigma hx0

end Payoff

/-! ## §7 Stress pins

`h = 1` (the smallest instance with a non-empty handle plane) and `h = 0` (where every binder in
sight is a theorem), per the lane idiom: a later reshaping of the general statements cannot
silently become vacuous. -/

section StressTests

/-- The `L_sq` rank at one handle is `5`; the handle pair sits at slots `3`, `4`. -/
example : sqRank 1 = 5 := by decide

example : sqHandleIdxU (0 : Fin 1) = (3 : Fin (sqRank 1)) := by decide

example : sqHandleIdxV (0 : Fin 1) = (4 : Fin (sqRank 1)) := by decide

/-- **The refutation at one handle**, written out: the bare `σ`-pivot is unavailable. -/
example : ¬ SqHandleMixFixesCore 1 0 := not_sqHandleMixFixesCore_zero (by omega)

/-- The refutation is not an artefact of `c = 0`: every non-unit exponent dies. -/
example {c : ℤ_[2]} (hc : ¬ IsUnit c) : ¬ SqHandleMixFixesCore 1 c :=
  fun H => hc (isUnit_of_sqHandleMixFixesCore (by omega) H)

/-- **The sharp form at one handle.** -/
example {c : ℤ_[2]} :
    SqHandleMixFixesCore 1 c ↔ IsUnit c ∧ SqHandleMixFixesCore 1 sqPivotExp :=
  sqHandleMixFixesCore_iff (by omega)

/-- At `h = 0` the target is a theorem (`SqCore/Certificate.lean`), so nothing above is
vacuously true by accident. -/
example (c : ℤ_[2]) : SqHandleMixFixesCore 0 c := sqHandleMixFixesCore_zero c

/-- The witness marking is a genuine marking: its pivot row at the canonical exponent is `0`,
which is exactly why it does *not* refute the canonical-exponent binder. -/
example : toAdd (nuWitness 1 (sqMixPivotElem 1 sqPivotExp)) = 0 := by
  rw [toAdd_nuWitness_sqMixPivotElem, sub_self]

/-- …while at `c = 0` the same marking's pivot row is the unit `c₀`. -/
example : toAdd (nuWitness 1 (sqMixPivotElem 1 0)) = sqPivotExp := by
  rw [toAdd_nuWitness_sqMixPivotElem, sub_zero]

/-- The `τ` families exist at one handle and fix the two core letters literally. -/
example (k : ℤ_[2]) : sqTauUEquiv 1 0 k (dsqSigma 1) = dsqSigma 1 := sqTauUEquiv_sigma 0 k

example (k : ℤ_[2]) : sqTauVEquiv 1 0 k (dsqX0 1) = dsqX0 1 := sqTauVEquiv_x0 0 k

/-- …and preserve the orientation. -/
example (k : ℤ_[2]) (x : (DSq 1 : Type)) : chiSq 1 (sqTauUEquiv 1 0 k x) = chiSq 1 x :=
  chiSq_sqTauUEquiv 0 k x

/-- The `SL₂` normalisation is available at one handle for every marking. -/
example (nu' : ContinuousMonoidHom (DSq 1 : Type) (Multiplicative ℤ_[2])) :
    ∃ Ψ : ContinuousMulEquiv (DSq 1 : Type) (DSq 1 : Type),
      IsSqHandleLocal 1 0 Ψ ∧ nu' (Ψ (sqGen 1 (sqHandleIdxV 0))) = 1 :=
  sq_normalize_handle 1 0 nu'

/-- **The reduction at one handle**, written out. -/
example {c : ℤ_[2]} (hE : SqHandleEichler 1 c) : SqHandleMixFixesCore 1 c :=
  sqHandleMixFixesCore_of_eichler hE

/-- …and the residual obligation is itself refuted off the canonical exponent. -/
example : ¬ SqHandleEichler 1 0 :=
  not_sqHandleEichler (by omega) (by rw [sub_zero]; exact isUnit_sqPivotExp)

/-- No `L_sq` core letter is clear-blind — wall 2, at one handle. -/
example : chiSq 1 (dsqSigma 1) ≠ 1 ∧ chiSq 1 (dsqX0 1) ≠ 1 ∧ chiSq 1 (dsqX1 1) ≠ 1 :=
  sqCore_no_clearBlind_letter 1

/-- …whereas the *combination* `w` is (this is the whole point of the corrected pivot). -/
example : chiSq 1 (sqPivot 1) = 1 := chiSq_sqPivot 1

end StressTests

/-! ## §8 Axiom pins

Committed prints for the headline declarations (the `GQ2/ProPCompletionFunctor.lean` idiom):
the whole file is **std-3**, with no census axiom reachable — in particular no `B8`
(`peripheralCyclotomicAction`) and no `B3c` (`dyadicOrientation`), exactly as for the `M`/`N`
handle stratum.  Census unchanged at **11**. -/

section AxiomPins

#print axioms not_sqHandleMixFixesCore
#print axioms sqHandleMixFixesCore_iff
#print axioms chiSq_sq_eq_lam
#print axioms sq_normalize_handle
#print axioms sqHandleMixFixesCore_of_eichler
#print axioms not_sqHandleEichler
#print axioms marked_matching_certificate_sq_of_eichler

end AxiomPins

end TauEquiv

end SqCore

end Dyadic

end GQ2
