/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.OrientedTameBundle
import GQ2.UnitFiltrationCounts
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Literal quadratic fields over `ℚ₂`  (dyadic campaign, ticket AS-F)

The five instance files `GQ2/Dyadic/Instances/{SqrtNeg2,Sqrt2,Sqrt5,Sqrt10,SqrtNeg10}.lean`
state packet Thm. 1.1 at a **supplied** quadratic `K : IntermediateField ℚ_[2] ℚ̄₂`, with the
row's arithmetic entering through binders (`hdeg : finrank ℚ_[2] K = 2`, `hqK`, the ramified-`i`
witness, `ramifiedData`).  Until this file no *concrete* quadratic extension of `ℚ₂` existed in
the repo — AS2 and AS3 both recorded that finding — so the headlines had no demonstrated
instantiation.

This file supplies the field objects and the binders that literal arithmetic discharges.

## Main definitions

* `GQ2.Dyadic.Fields.quadField a` — `ℚ₂(√a) = ℚ_[2]⟮√a⟯` as an `IntermediateField ℚ_[2] ℚ̄₂`,
  for any `a : ℚ_[2]`, with the square root chosen in `ℚ̄₂` by `IsAlgClosed.exists_pow_nat_eq`.
  It carries a `FiniteDimensional` instance **unconditionally** (`√a` is a root of the monic
  `X² − a`, hence integral); only the *degree* needs `¬ IsSquare a`.
* `GQ2.Dyadic.Fields.KSqrtNegTwo`, `KSqrtTwo`, `KSqrtFive`, `KSqrtTen`, `KSqrtNegTen` — the
  campaign's five rows, as literal objects.

## Main results

* `GQ2.Dyadic.Fields.finrank_quadField` — `finrank ℚ_[2] (quadField a) = 2` when `a` is not a
  square, and the five named instances `finrank_KSqrtNegTwo` … `finrank_KSqrtNegTen`.
  **This discharges the `hdeg` binder of all five instance headlines.**
* `GQ2.Dyadic.Fields.not_isSquare_of_odd_valuation` — the odd-valuation non-square criterion,
  and `not_isSquare_five` (the mod-`8` criterion, through `GQ2.DyadicSquares`).

## What this file does *not* do

`qOf K FF = q`, the ramified-`i` witness and `ramifiedData` are **not** here; see the AS-F
report for the precise obstruction in each case.  In particular `qOf` is pinned only through
`DyadicUnitFiltration.f`, whose bridge to `Nat.card (ResidueField K)` runs through
`GQ2.UnitFiltrationCounts.card_gradeZero` / `card_gradeI`, both `private`.

No `sorry`, no new axiom; everything here is std-3.
-/

namespace GQ2.Dyadic.Fields

open Polynomial IntermediateField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The 2-adic non-square criteria

Both criteria are about `ℚ_[2]` alone; they are the only arithmetic input to the degree
computation of §3. -/

section NonSquare

/-- `v(-1) = 0`: `(-1)² = 1`. -/
theorem valuation_neg_one : (-1 : ℚ_[2]).valuation = 0 := by
  have h : ((-1 : ℚ_[2]) * (-1 : ℚ_[2])).valuation = (1 : ℚ_[2]).valuation := by norm_num
  rw [Padic.valuation_mul (by norm_num) (by norm_num), Padic.valuation_one] at h
  omega

/-- `v(-x) = v(x)`. -/
theorem valuation_neg (x : ℚ_[2]) : (-x).valuation = x.valuation := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [show -x = (-1 : ℚ_[2]) * x by ring, Padic.valuation_mul (by norm_num) hx,
      valuation_neg_one, zero_add]

/-- **An element of odd valuation is not a square.**  This is the only input the four ramified
rows (`√−2`, `√2`, `√10`, `√−10`) need. -/
theorem not_isSquare_of_odd_valuation {a : ℚ_[2]} (ha : a ≠ 0) (hodd : Odd a.valuation) :
    ¬ IsSquare a := by
  rintro ⟨b, hb⟩
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hb; exact ha hb
  have := Padic.valuation_mul (p := 2) hb0 hb0
  rw [← hb] at this
  obtain ⟨k, hk⟩ := hodd
  omega

theorem valuation_two : (2 : ℚ_[2]).valuation = 1 := by
  rw [Padic.valuation_ofNat, padicValNat.self (by norm_num), Nat.cast_one]

theorem valuation_five : (5 : ℚ_[2]).valuation = 0 := by
  rw [Padic.valuation_ofNat, padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.cast_zero]

theorem valuation_ten : (10 : ℚ_[2]).valuation = 1 := by
  rw [show (10 : ℚ_[2]) = 2 * 5 by norm_num,
    Padic.valuation_mul (by norm_num) (by norm_num), valuation_two, valuation_five, add_zero]

theorem not_isSquare_two : ¬ IsSquare (2 : ℚ_[2]) :=
  not_isSquare_of_odd_valuation (by norm_num) (by rw [valuation_two]; exact ⟨0, by ring⟩)

theorem not_isSquare_neg_two : ¬ IsSquare (-2 : ℚ_[2]) :=
  not_isSquare_of_odd_valuation (by norm_num)
    (by rw [valuation_neg, valuation_two]; exact ⟨0, by ring⟩)

theorem not_isSquare_ten : ¬ IsSquare (10 : ℚ_[2]) :=
  not_isSquare_of_odd_valuation (by norm_num) (by rw [valuation_ten]; exact ⟨0, by ring⟩)

theorem not_isSquare_neg_ten : ¬ IsSquare (-10 : ℚ_[2]) :=
  not_isSquare_of_odd_valuation (by norm_num)
    (by rw [valuation_neg, valuation_ten]; exact ⟨0, by ring⟩)

/-- **`5` is not a square in `ℚ₂`** — the `√5` row is the one field of the five whose defining
element is a *unit*, so the valuation criterion says nothing and the mod-`8` criterion is used
instead: a square of a `2`-adic integer is `≡ 0, 1, 4 (mod 8)`, and `5` is none of these. -/
theorem not_isSquare_five : ¬ IsSquare (5 : ℚ_[2]) := by
  rintro ⟨b, hb⟩
  have hb1 : ‖b‖ ≤ 1 := by
    have h5 : ‖(5 : ℚ_[2])‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation (by norm_num), valuation_five]; norm_num
    have : ‖b‖ * ‖b‖ = 1 := by rw [← norm_mul, ← hb, h5]
    nlinarith [norm_nonneg b]
  set bz : ℤ_[2] := ⟨b, hb1⟩ with hbz
  have hcoe : bz * bz = (5 : ℤ_[2]) := by
    apply Subtype.ext
    push_cast [hbz]
    exact hb.symm
  have himg := congrArg (PadicInt.toZModPow (p := 2) 3) hcoe
  rw [map_mul, map_ofNat] at himg
  revert himg
  exact (by decide : ∀ x : ZMod (2 ^ 3), x * x ≠ 5) _

end NonSquare

/-! ## §2 `ℚ₂(√a)` as a literal object

`√a` is chosen in `ℚ̄₂` by algebraic closedness.  Note that `quadField a` is defined — and is
finite-dimensional — for **every** `a`, including squares (where it collapses to `ℚ₂`); only the
degree computation `finrank = 2` consumes `¬ IsSquare a`. -/

section Construction

variable (a : ℚ_[2])

/-- A chosen square root of `a` inside `ℚ̄₂`. -/
noncomputable def sqrtIn : ℚ̄₂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ_[2] ℚ̄₂ a) two_pos)

@[simp] theorem sqrtIn_sq : sqrtIn a ^ 2 = algebraMap ℚ_[2] ℚ̄₂ a :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ_[2] ℚ̄₂ a) two_pos)

/-- The defining polynomial `X² − a`. -/
noncomputable def quadPoly : ℚ_[2][X] := X ^ 2 - C a

theorem quadPoly_monic : (quadPoly a).Monic := monic_X_pow_sub_C a two_ne_zero

theorem quadPoly_natDegree : (quadPoly a).natDegree = 2 := by
  unfold quadPoly; compute_degree!

theorem aeval_sqrtIn : aeval (sqrtIn a) (quadPoly a) = 0 := by
  simp [quadPoly]

theorem sqrtIn_isIntegral : IsIntegral ℚ_[2] (sqrtIn a) :=
  ⟨quadPoly a, quadPoly_monic a, aeval_sqrtIn a⟩

variable {a}

theorem quadPoly_irreducible (ha : ¬ IsSquare a) : Irreducible (quadPoly a) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by simp [quadPoly_natDegree]) fun x hx => ha ⟨x, ?_⟩
  have hx' : x ^ 2 - a = 0 := by simpa [quadPoly, IsRoot] using hx
  linear_combination -hx'

theorem minpoly_sqrtIn (ha : ¬ IsSquare a) : minpoly ℚ_[2] (sqrtIn a) = quadPoly a :=
  (minpoly.eq_of_irreducible_of_monic (quadPoly_irreducible ha) (aeval_sqrtIn a)
    (quadPoly_monic a)).symm

variable (a)

/-- **`ℚ₂(√a)`**, the literal quadratic extension of `ℚ₂` inside `ℚ̄₂`. -/
noncomputable def quadField : IntermediateField ℚ_[2] ℚ̄₂ := ℚ_[2]⟮sqrtIn a⟯

theorem sqrtIn_mem_quadField : sqrtIn a ∈ quadField a :=
  IntermediateField.mem_adjoin_simple_self _ _

instance : FiniteDimensional ℚ_[2] (quadField a) :=
  IntermediateField.adjoin.finiteDimensional (sqrtIn_isIntegral a)

variable {a}

/-- **The `hdeg` binder, discharged.**  `[ℚ₂(√a) : ℚ₂] = 2` whenever `a` is not a square. -/
theorem finrank_quadField (ha : ¬ IsSquare a) : Module.finrank ℚ_[2] (quadField a) = 2 := by
  rw [quadField, IntermediateField.adjoin.finrank (sqrtIn_isIntegral a), minpoly_sqrtIn ha,
    quadPoly_natDegree]

end Construction

/-! ## §3 The campaign's five rows -/

section Rows

/-- `ℚ₂(√−2)` — the pilot row (AS2, compact `N₂`). -/
noncomputable abbrev KSqrtNegTwo : IntermediateField ℚ_[2] ℚ̄₂ := quadField (-2)

/-- `ℚ₂(√2)` — AS3's compact-`M` row. -/
noncomputable abbrev KSqrtTwo : IntermediateField ℚ_[2] ℚ̄₂ := quadField 2

/-- `ℚ₂(√5)` — AS3's unramified row (`q_K = 4`). -/
noncomputable abbrev KSqrtFive : IntermediateField ℚ_[2] ℚ̄₂ := quadField 5

/-- `ℚ₂(√10)` — AS3's procyclic row. -/
noncomputable abbrev KSqrtTen : IntermediateField ℚ_[2] ℚ̄₂ := quadField 10

/-- `ℚ₂(√−10)` — AS3's procyclic row, packet Cor. 8.2. -/
noncomputable abbrev KSqrtNegTen : IntermediateField ℚ_[2] ℚ̄₂ := quadField (-10)

theorem finrank_KSqrtNegTwo : Module.finrank ℚ_[2] KSqrtNegTwo = 2 :=
  finrank_quadField not_isSquare_neg_two

theorem finrank_KSqrtTwo : Module.finrank ℚ_[2] KSqrtTwo = 2 :=
  finrank_quadField not_isSquare_two

theorem finrank_KSqrtFive : Module.finrank ℚ_[2] KSqrtFive = 2 :=
  finrank_quadField not_isSquare_five

theorem finrank_KSqrtTen : Module.finrank ℚ_[2] KSqrtTen = 2 :=
  finrank_quadField not_isSquare_ten

theorem finrank_KSqrtNegTen : Module.finrank ℚ_[2] KSqrtNegTen = 2 :=
  finrank_quadField not_isSquare_neg_ten

end Rows

end GQ2.Dyadic.Fields
