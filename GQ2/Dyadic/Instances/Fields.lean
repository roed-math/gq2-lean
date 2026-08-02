/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.SqrtNeg2
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
  and `not_isSquare_five` (the mod-`8` criterion, through `PadicInt.toZModPow`).
* `GQ2.Dyadic.Fields.qOf_quadField` — for `v(a)` **odd**, `q_K = 2` at *every*
  `DyadicUnitFiltration` on `ℚ₂(√a)`, with the four named instances `qOf_KSqrtNegTwo`,
  `qOf_KSqrtTwo`, `qOf_KSqrtTen`, `qOf_KSqrtNegTen`.  **This discharges the `hqK`/`params_qK`
  binder at the four ramified rows.**  The proof does not go through the residue field at all:
  §4's separation lemma (`‖x‖ = ‖y√a‖` forces `2v(x) = 2v(y) + v(a)`, impossible for `v(a)`
  odd) collapses the unit filtration at depth `1`, and `DyadicUnitFiltration.card_gr_zero`
  then reads `2^f − 1 = 1`.

* `GQ2.Dyadic.Fields.not_hasEqualNormValueGroups_quadField` — **the ramified-`i` binder**, with
  the single uniform witness `z = 1 + √a + i` and the four named instances
  `not_hasEqualNormValueGroups_KSqrtNegTwo`, `…_KSqrtTwo`, `…_KSqrtTen`, `…_KSqrtNegTen`.
  `‖z‖⁴ = ‖2‖³` is an odd power of `‖2‖`, while `exists_norm_sq_eq` shows the value group of
  `ℚ₂(√a)` only supplies even ones — so `ℚ₂(√a)(i)/ℚ₂(√a)` is ramified.
* `GQ2.Dyadic.Fields.sqrtNegTwo_candidate_equiv_galK_literal` — **packet Thm. 1.1 at the
  literal `ℚ₂(√−2)`** (§8), i.e. `SqrtNeg2.sqrtNegTwo_candidate_equiv_galK` with `K`, `hdeg`,
  `params`, `params_qK` and `ramified` all supplied.  What survives in the binder list is
  exactly the non-arithmetic residue: the AX3/AX4 bundles, the G-Lab pack and the analytic
  clauses.

## What this file does *not* do

`ramifiedData` (LG5's `RamifiedCertificate`) and `q_K = 4` at the unramified `√5` row are
**not** here; see the AS-F report for the precise obstruction in each case.  One of them is
worth recording in place: the `√5` row needs `#(U⁰/U¹) = 3`, i.e. the residue field itself,
whose bridge to `DyadicUnitFiltration.f` runs through `GQ2.UnitFiltrationCounts.card_gradeZero`
and `card_gradeI` — both `private`, hence unusable outside that file.

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

/-! ## §4 The value group of `ℚ₂(√a)`, and `q_K = 2` at the ramified rows

Everything in this section assumes `v(a)` is **odd** — true at `−2`, `2`, `10`, `−10` and false
at `5`.  The point of the hypothesis is the separation lemma below: `‖x‖` and `‖y√a‖` can never
agree for nonzero `x, y ∈ ℚ₂`, because agreement would force `2 v(x) = 2 v(y) + v(a)`.
Everything else — the exact norm of a sum, the shape of the unit group, and finally `f = 1` —
follows from that one parity statement. -/

section Ramified

open IsUltrametricDist

/-- The spectral norm on `ℚ̄₂` extends the `2`-adic norm on `ℚ₂`. -/
theorem norm_algebraMap (x : ℚ_[2]) :
    ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[2], spectralNorm_extends]

/-- Equal `2`-adic norms means equal valuations. -/
theorem valuation_eq_of_norm_eq {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) (h : ‖x‖ = ‖y‖) :
    x.valuation = y.valuation := by
  rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy] at h
  have := (zpow_right_inj₀ (a := (2 : ℝ)) (by norm_num) (by norm_num)).mp h
  omega

variable {a : ℚ_[2]}

theorem norm_sqrtIn_sq (a : ℚ_[2]) : ‖sqrtIn a‖ ^ 2 = ‖a‖ := by
  rw [← norm_pow, sqrtIn_sq, norm_algebraMap]

theorem ne_zero_of_odd_valuation (hodd : Odd a.valuation) : a ≠ 0 := by
  rintro rfl
  rw [Padic.valuation_zero] at hodd
  exact (Int.not_odd_iff_even.mpr ⟨0, rfl⟩) hodd

/-- **The separation lemma.**  When `v(a)` is odd, `‖x‖ = ‖y·√a‖` is impossible for nonzero
`x, y ∈ ℚ₂`: squaring turns it into `2 v(x) = 2 v(y) + v(a)`. -/
theorem norm_ne_norm_mul_sqrtIn (hodd : Odd a.valuation) {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖
      ≠ ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ := by
  have ha := ne_zero_of_odd_valuation hodd
  intro h
  rw [norm_algebraMap, norm_mul, norm_algebraMap] at h
  have hsq : ‖x ^ 2‖ = ‖y ^ 2 * a‖ := by
    rw [norm_pow, norm_mul, norm_pow, h, mul_pow, norm_sqrtIn_sq]
  have hv := valuation_eq_of_norm_eq (pow_ne_zero 2 hx) (mul_ne_zero (pow_ne_zero 2 hy) ha) hsq
  rw [Padic.valuation_pow, Padic.valuation_mul (pow_ne_zero 2 hy) ha, Padic.valuation_pow] at hv
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **The exact norm of `x + y√a`.**  A consequence of the separation lemma and the ultrametric
"all triangles are isosceles" identity. -/
theorem norm_add_mul_sqrtIn (hodd : Odd a.valuation) {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)
        + (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖
      = max ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖
          ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ :=
  norm_add_eq_max_of_norm_ne_norm (norm_ne_norm_mul_sqrtIn hodd hx hy)

/-- **`{1, √a}` spans.**  Every element of `ℚ₂(√a)` is `x + y√a` with `x, y ∈ ℚ₂` — read off the
power basis of `ℚ_[2]⟮√a⟯`, whose dimension is `deg (minpoly) = 2`. -/
theorem exists_repr (ha : ¬ IsSquare a) {z : AlgebraicClosure ℚ_[2]} (hz : z ∈ quadField a) :
    ∃ x y : ℚ_[2], z = algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x
      + algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y * sqrtIn a := by
  have hz' : z ∈ ℚ_[2]⟮sqrtIn a⟯ := hz
  obtain ⟨f, hfdeg, hfeq⟩ :=
    (IntermediateField.adjoin.powerBasis (sqrtIn_isIntegral a)).exists_eq_aeval ⟨z, hz'⟩
  rw [IntermediateField.adjoin.powerBasis_dim, minpoly_sqrtIn ha, quadPoly_natDegree] at hfdeg
  obtain ⟨c₁, c₀, rfl⟩ :=
    Polynomial.exists_eq_X_add_C_of_natDegree_le_one (by omega : f.natDegree ≤ 1)
  refine ⟨c₀, c₁, ?_⟩
  have := congrArg (Subtype.val : ℚ_[2]⟮sqrtIn a⟯ → AlgebraicClosure ℚ_[2]) hfeq
  rw [← IntermediateField.coe_val, ← Polynomial.aeval_algHom_apply] at this
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.coe_val,
    IntermediateField.AdjoinSimple.coe_gen] at this
  simpa [add_comm] using this

/-- **`ℤ₂ˣ ⊆ 1 + 2ℤ₂`.**  A `2`-adic number of norm `1` is `≡ 1 (mod 2)`, since `ZMod 2` has a
single unit.  This is what makes the residue field of a *ramified* quadratic extension `𝔽₂`. -/
theorem norm_sub_one_le_norm_two {x : ℚ_[2]} (hx : ‖x‖ = 1) : ‖x - 1‖ ≤ ‖(2 : ℚ_[2])‖ := by
  set xz : ℤ_[2] := ⟨x, le_of_eq hx⟩ with hxz
  have hxzu : IsUnit xz := PadicInt.isUnit_iff.mpr hx
  have h1 : PadicInt.toZModPow (p := 2) 1 xz = 1 :=
    (by decide : ∀ z : ZMod (2 ^ 1), IsUnit z → z = 1) _ (hxzu.map _)
  have hker : xz - 1 ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 1} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, h1, sub_self]
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (xz - 1) 1).mpr hker
  rw [PadicInt.norm_def] at hnorm
  have hcoe : ((xz - 1 : ℤ_[2]) : ℚ_[2]) = x - 1 := by rw [PadicInt.coe_sub, PadicInt.coe_one]
  rw [hcoe] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by push_cast; ring, Padic.norm_p]
  norm_num

/-- **The unit filtration of a ramified quadratic field collapses at depth `1`.**  Every
norm-one unit of `ℚ₂(√a)` already lies in `U^{(1)}`: writing `u = x + y√a`, the parity
separation forces `‖x‖ = 1` and `‖y√a‖ < 1`, and then `u − 1 = (x − 1) + y√a` has both summands
of norm at most `‖π‖`. -/
theorem normUnits_le_depthUnits (hodd : Odd a.valuation) (ha : ¬ IsSquare a)
    (FF : DyadicUnitFiltration (quadField a)) :
    normUnits (quadField a) ≤ depthUnits (quadField a) FF.π 1 := by
  have hπ2 : ‖(2 : AlgebraicClosure ℚ_[2])‖ ≤ ‖FF.π‖ := by
    refine FF.hπ_max 2 ?_ norm_two_lt_one
    simp
  intro u hu
  have hu1 : ‖((u : ↥(quadField a)) : AlgebraicClosure ℚ_[2])‖ = 1 := hu
  refine ⟨hu1, ?_⟩
  rw [pow_one]
  obtain ⟨x, y, hxy⟩ := exists_repr ha (u : ↥(quadField a)).2
  -- the `y ≠ 0, ‖y√a‖ = 1` configuration is forbidden by the parity of `v(a)`
  have hbad : ∀ y : ℚ_[2], y ≠ 0 →
      ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ ≠ 1 := by
    intro y hy hcon
    have ha0 := ne_zero_of_odd_valuation hodd
    rw [norm_mul, norm_algebraMap] at hcon
    have hsq : ‖y ^ 2 * a‖ = ‖(1 : ℚ_[2])‖ := by
      rw [norm_mul, norm_pow, ← norm_sqrtIn_sq a, ← mul_pow, hcon, one_pow, norm_one]
    have hv := valuation_eq_of_norm_eq (mul_ne_zero (pow_ne_zero 2 hy) ha0) one_ne_zero hsq
    rw [Padic.valuation_mul (pow_ne_zero 2 hy) ha0, Padic.valuation_pow,
      Padic.valuation_one] at hv
    obtain ⟨k, hk⟩ := hodd
    omega
  -- in every case `‖x‖ = 1` and `‖y√a‖ ≤ ‖π‖`
  have hmain : ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖ = 1 ∧
      ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ ≤ ‖FF.π‖ := by
    rcases eq_or_ne y 0 with rfl | hy
    · refine ⟨by rw [← hu1, hxy]; simp, ?_⟩
      simp only [map_zero, zero_mul, norm_zero]
      exact le_trans (norm_nonneg _) hπ2
    rcases eq_or_ne x 0 with rfl | hx
    · exact absurd (by rw [← hu1, hxy]; simp) (hbad y hy)
    · have hmax : max ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖
          ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ = 1 := by
        rw [← norm_add_mul_sqrtIn hodd hx hy, ← hxy]; exact hu1
      have hne := norm_ne_norm_mul_sqrtIn hodd hx hy
      have hyx : ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ ≠ 1 := hbad y hy
      have hx1 : ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖ = 1 := by
        rcases max_cases ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖
          ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ with ⟨he, -⟩ | ⟨he, -⟩
        · rw [he] at hmax; exact hmax
        · rw [he] at hmax; exact absurd hmax hyx
      refine ⟨hx1, FF.hπ_max _ ?_ ?_⟩
      · exact (quadField a).mul_mem ((quadField a).algebraMap_mem y) (sqrtIn_mem_quadField a)
      · rcases lt_or_eq_of_le (le_max_right ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖
          ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ |>.trans_eq hmax) with h | h
        · exact h
        · exact absurd h hyx
  obtain ⟨hx1, hyπ⟩ := hmain
  have hsub : ((u : ↥(quadField a)) : AlgebraicClosure ℚ_[2]) - 1
      = algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) (x - 1)
        + (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a := by
    rw [hxy, map_sub, map_one]; ring
  rw [hsub]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hyπ)
  rw [norm_algebraMap]
  refine (norm_sub_one_le_norm_two (by rwa [norm_algebraMap] at hx1)).trans ?_
  rw [← norm_algebraMap (2 : ℚ_[2]), map_ofNat]
  exact hπ2

/-- **The `hqK` binder at the four ramified rows, discharged.**  For `v(a)` odd the residue
degree of `ℚ₂(√a)` is `1`, so `q_K = 2` — for *every* `DyadicUnitFiltration` on the field, since
the graded count `#(U⁰/U¹) = 2^f − 1` pins `f`. -/
theorem qOf_quadField (hodd : Odd a.valuation) (ha : ¬ IsSquare a)
    (FF : DyadicUnitFiltration (quadField a)) : qOf (quadField a) FF = 2 := by
  have htop : (depthUnits (quadField a) FF.π 1).subgroupOf (normUnits (quadField a)) = ⊤ :=
    Subgroup.subgroupOf_eq_top.mpr (normUnits_le_depthUnits hodd ha FF)
  have hcard := FF.card_gr_zero
  rw [htop] at hcard
  have hone : Nat.card (↥(normUnits (quadField a)) ⧸ (⊤ : Subgroup ↥(normUnits (quadField a))))
      = 1 := Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
  rw [hone] at hcard
  have h2le : 2 ≤ 2 ^ FF.f := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ FF.f := Nat.pow_le_pow_right (by norm_num) FF.hf_pos
  have hf : (2 : ℕ) ^ FF.f = 2 ^ 1 := by rw [pow_one]; omega
  rw [qOf_eq, Nat.pow_right_injective (le_refl 2) hf, pow_one]

end Ramified

/-! ## §5 `q_K = 2` at the four ramified rows -/

section RowsQ

theorem qOf_KSqrtNegTwo (FF : DyadicUnitFiltration KSqrtNegTwo) : qOf KSqrtNegTwo FF = 2 :=
  qOf_quadField (by rw [valuation_neg, valuation_two]; exact ⟨0, by ring⟩) not_isSquare_neg_two FF

theorem qOf_KSqrtTwo (FF : DyadicUnitFiltration KSqrtTwo) : qOf KSqrtTwo FF = 2 :=
  qOf_quadField (by rw [valuation_two]; exact ⟨0, by ring⟩) not_isSquare_two FF

theorem qOf_KSqrtTen (FF : DyadicUnitFiltration KSqrtTen) : qOf KSqrtTen FF = 2 :=
  qOf_quadField (by rw [valuation_ten]; exact ⟨0, by ring⟩) not_isSquare_ten FF

theorem qOf_KSqrtNegTen (FF : DyadicUnitFiltration KSqrtNegTen) : qOf KSqrtNegTen FF = 2 :=
  qOf_quadField (by rw [valuation_neg, valuation_ten]; exact ⟨0, by ring⟩) not_isSquare_neg_ten FF

end RowsQ

/-! ## §6 The ramified-`i` witness

The instance headlines carry a binder `ramified : ∀ δi, δi² = −1 → ¬ HasEqualNormValueGroups K δi`
— packet §8's statement that `K(i)/K` is *ramified*, phrased as "the value group grows".  At
every ramified row it is a theorem, with an explicit witness.

⚠ A remark on the search: the first witness found here was a scaled `ζ₈ − 1`
(`w = (−1 + i)/√−2` is a primitive `8`-th root of unity, `z = √−2·(w − 1)`), and that witness
is **not** uniform — `ζ₈ ∈ K(i)` needs `√2 ∈ K(i)`, which fails at `√±10`.  The `1 + √a + i`
below has no such restriction and covers all four ramified rows at once. -/

section RamifiedI

variable {a : ℚ_[2]}

/-- A nonnegative real with `r² = 1` is `1`. -/
theorem eq_one_of_sq_eq_one {r : ℝ} (hr : 0 ≤ r) (h : r ^ 2 = 1) : r = 1 := by
  have hfac : (r - 1) * (r + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h' <;> linarith

/-- **The value group of `ℚ₂(√a)` is a square root of that of `ℚ₂`.**  For `v(a)` odd, every
nonzero `z ∈ ℚ₂(√a)` has `‖z‖² = ‖c‖` for some `c ∈ ℚ₂ˣ`. -/
theorem exists_norm_sq_eq (hodd : Odd a.valuation) (ha : ¬ IsSquare a)
    {z : AlgebraicClosure ℚ_[2]} (hz : z ∈ quadField a) (hz0 : z ≠ 0) :
    ∃ c : ℚ_[2], c ≠ 0 ∧ ‖z‖ ^ 2 = ‖c‖ := by
  have ha0 := ne_zero_of_odd_valuation hodd
  obtain ⟨x, y, hxy⟩ := exists_repr ha hz
  have hx2 : ∀ x : ℚ_[2], x ≠ 0 →
      ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖ ^ 2 = ‖x ^ 2‖ := by
    intro x _; rw [norm_algebraMap, norm_pow]
  have hy2 : ∀ y : ℚ_[2],
      ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ ^ 2 = ‖y ^ 2 * a‖ := by
    intro y
    rw [norm_mul, mul_pow, norm_algebraMap, norm_sqrtIn_sq, norm_mul, norm_pow]
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x ≠ 0 := by rintro rfl; rw [hxy] at hz0; simp at hz0
    exact ⟨x ^ 2, pow_ne_zero 2 hx, by rw [hxy]; simp⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨y ^ 2 * a, mul_ne_zero (pow_ne_zero 2 hy) ha0, by rw [hxy]; simpa using hy2 y⟩
  · rw [hxy, norm_add_mul_sqrtIn hodd hx hy]
    rcases max_cases ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x)‖
      ‖(algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) y) * sqrtIn a‖ with ⟨he, -⟩ | ⟨he, -⟩
    · exact ⟨x ^ 2, pow_ne_zero 2 hx, by rw [he]; exact hx2 x hx⟩
    · exact ⟨y ^ 2 * a, mul_ne_zero (pow_ne_zero 2 hy) ha0, by rw [he]; exact hy2 y⟩

/-- **The ramified-`i` binder**, discharged uniformly at every row with `‖a‖ = ‖2‖` and
`‖a² − 4‖ < ‖2‖³`.  The witness is `z = 1 + √a + i`.  Squaring,

`z² = (a + 2i) + 2√a(1 + i) =: A + B`,   `‖A‖² = ‖4a‖ = ‖2‖³`,   `‖B‖² = ‖2‖⁴`,

so `A` dominates and `‖z‖⁴ = ‖A‖² = ‖2‖³` — an **odd** power of `‖2‖`.  But `exists_norm_sq_eq`
says `‖v‖² ∈ ‖ℚ₂ˣ‖` for every `v ∈ ℚ₂(√a)ˣ`, so `‖v‖⁴` is always an even power.  Hence `z`'s
norm is outside the value group, i.e. `ℚ₂(√a)(i)/ℚ₂(√a)` is ramified.

The hypothesis `‖a² − 4‖ < ‖2‖³` is what makes `‖A‖² = ‖(a² − 4) + 4ai‖` collapse onto its
second summand; it holds at `a = ±2` (where `a² − 4 = 0`) and at `a = ±10` (where
`a² − 4 = 96`, of valuation `5`). -/
theorem not_hasEqualNormValueGroups_quadField (hodd : Odd a.valuation) (ha : ¬ IsSquare a)
    (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) (hsmall : ‖a ^ 2 - 4‖ < ‖(2 : ℚ_[2])‖ ^ 3)
    (δi : AlgebraicClosure ℚ_[2]) (hδ : δi ^ 2 = -1) :
    ¬ GQ2.HasEqualNormValueGroups (quadField a) δi := by
  set α : AlgebraicClosure ℚ_[2] := algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) a with hα
  set s : AlgebraicClosure ℚ_[2] := sqrtIn a with hs
  have hs2 : s ^ 2 = α := sqrtIn_sq a
  have hnorm2 : ‖(2 : AlgebraicClosure ℚ_[2])‖ = ‖(2 : ℚ_[2])‖ := by
    rw [← norm_algebraMap (2 : ℚ_[2]), map_ofNat]
  have h2pos : (0 : ℝ) < ‖(2 : AlgebraicClosure ℚ_[2])‖ := norm_pos_iff.mpr two_ne_zero
  have h2lt1 : ‖(2 : AlgebraicClosure ℚ_[2])‖ < 1 := GQ2.norm_two_lt_one
  have hnα : ‖α‖ = ‖(2 : AlgebraicClosure ℚ_[2])‖ := by rw [hα, norm_algebraMap, hna, hnorm2]
  have hsn : ‖s‖ ^ 2 = ‖(2 : AlgebraicClosure ℚ_[2])‖ := by
    rw [hs, norm_sqrtIn_sq, ← hnα, hα, norm_algebraMap]
  have hδn : ‖δi‖ = 1 := by
    refine eq_one_of_sq_eq_one (norm_nonneg _) ?_
    rw [← norm_pow, hδ, norm_neg, norm_one]
  have h1δ : ‖1 + δi‖ ^ 2 = ‖(2 : AlgebraicClosure ℚ_[2])‖ := by
    rw [← norm_pow, show (1 + δi) ^ 2 = 2 * δi by linear_combination hδ, norm_mul, hδn, mul_one]
  -- `A = a + 2i` has `‖A‖² = ‖4a‖ = ‖2‖³`
  have hA2 : (α + 2 * δi) ^ 2 = (α ^ 2 - 4) + 4 * α * δi := by linear_combination 4 * hδ
  have hsmall' : ‖α ^ 2 - 4‖ < ‖(2 : AlgebraicClosure ℚ_[2])‖ ^ 3 := by
    rw [show α ^ 2 - 4 = algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) (a ^ 2 - 4) by
      rw [map_sub, map_pow, map_ofNat, hα], norm_algebraMap, hnorm2]
    exact hsmall
  have hbig : ‖4 * α * δi‖ = ‖(2 : AlgebraicClosure ℚ_[2])‖ ^ 3 := by
    rw [norm_mul, norm_mul, hδn, mul_one, hnα,
      show (4 : AlgebraicClosure ℚ_[2]) = 2 ^ 2 by norm_num, norm_pow]
    ring
  have hnA2 : ‖α + 2 * δi‖ ^ 2 = ‖(2 : AlgebraicClosure ℚ_[2])‖ ^ 3 := by
    rw [← norm_pow, hA2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by
      rw [hbig]; exact ne_of_lt hsmall'), hbig]
    exact max_eq_right (le_of_lt (hbig ▸ hsmall'))
  -- `B = 2√a(1 + i)` has `‖B‖² = ‖2‖⁴`, so `B` is dominated by `A`
  have hnB2 : ‖2 * s * (1 + δi)‖ ^ 2 = ‖(2 : AlgebraicClosure ℚ_[2])‖ ^ 4 := by
    rw [norm_mul, norm_mul, mul_pow, mul_pow, hsn, h1δ]; ring
  have ht43 : ‖(2 : AlgebraicClosure ℚ_[2])‖ ^ 4 < ‖(2 : AlgebraicClosure ℚ_[2])‖ ^ 3 := by
    nlinarith [h2pos, h2lt1, pow_pos h2pos 3]
  have hBA : ‖2 * s * (1 + δi)‖ < ‖α + 2 * δi‖ := by
    have hlt : ‖2 * s * (1 + δi)‖ ^ 2 < ‖α + 2 * δi‖ ^ 2 := by rw [hnA2, hnB2]; exact ht43
    nlinarith [hlt, norm_nonneg (α + 2 * δi), norm_nonneg (2 * s * (1 + δi))]
  -- the witness `z = 1 + √a + i`
  set z : AlgebraicClosure ℚ_[2] := 1 + s + δi with hz
  have hz2 : z ^ 2 = (α + 2 * δi) + 2 * s * (1 + δi) := by rw [hz]; linear_combination hs2 + hδ
  have hzn : ‖z‖ ^ 4 = ‖(2 : AlgebraicClosure ℚ_[2])‖ ^ 3 := by
    have h : ‖z‖ ^ 2 = ‖α + 2 * δi‖ := by
      rw [← norm_pow, hz2,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hBA),
        max_eq_left (le_of_lt hBA)]
    calc ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = ‖α + 2 * δi‖ ^ 2 := by rw [h]
      _ = ‖(2 : AlgebraicClosure ℚ_[2])‖ ^ 3 := hnA2
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzn
    have hpos : (0 : ℝ) < ‖(2 : AlgebraicClosure ℚ_[2])‖ ^ 3 := by positivity
    rw [← hzn] at hpos
    norm_num at hpos
  -- refute: `‖z‖⁴` is an odd power of `‖2‖`, the value group only supplies even ones
  intro H
  obtain ⟨v, hv0, hvn⟩ := H z hz0
    ⟨⟨1 + s, (quadField a).add_mem (one_mem _) (sqrtIn_mem_quadField a)⟩, 1, by
      rw [hz]; push_cast; ring⟩
  have hv0' : ((v : ↥(quadField a)) : AlgebraicClosure ℚ_[2]) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨c, hc0, hc⟩ := exists_norm_sq_eq hodd ha v.2 hv0'
  have hc4 : ‖c‖ ^ 2 = ‖(2 : ℚ_[2])‖ ^ 3 := by
    have hv4 : ‖c‖ ^ 2 = ‖((v : ↥(quadField a)) : AlgebraicClosure ℚ_[2])‖ ^ 4 := by
      rw [← hc]; ring
    rw [hv4, ← hvn, hzn, hnorm2]
  have hkey : ‖c ^ 2‖ = ‖(8 : ℚ_[2])‖ := by
    rw [norm_pow, hc4, show (8 : ℚ_[2]) = 2 ^ 3 by norm_num, norm_pow]
  have hval := valuation_eq_of_norm_eq (pow_ne_zero 2 hc0) (by norm_num) hkey
  rw [Padic.valuation_pow, show (8 : ℚ_[2]) = 2 ^ 3 by norm_num, Padic.valuation_pow,
    valuation_two] at hval
  omega

end RamifiedI

/-! ## §7 The ramified-`i` witness at the four ramified rows -/

section RowsRamified

theorem valuation_three : (3 : ℚ_[2]).valuation = 0 := by
  rw [Padic.valuation_ofNat, padicValNat.eq_zero_of_not_dvd (by norm_num), Nat.cast_zero]

theorem norm_eq_of_valuation_eq {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x.valuation = y.valuation) : ‖x‖ = ‖y‖ := by
  rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy, h]

theorem norm_three : ‖(3 : ℚ_[2])‖ = 1 := by
  rw [Padic.norm_eq_zpow_neg_valuation (by norm_num), valuation_three]; norm_num

theorem norm_two_alg : ‖(2 : AlgebraicClosure ℚ_[2])‖ = ‖(2 : ℚ_[2])‖ := by
  rw [← norm_algebraMap (2 : ℚ_[2]), map_ofNat]

theorem norm_two_lt_one' : ‖(2 : ℚ_[2])‖ < 1 := norm_two_alg ▸ GQ2.norm_two_lt_one

theorem norm_two_pow_five_lt : ‖(2 : ℚ_[2])‖ ^ 5 < ‖(2 : ℚ_[2])‖ ^ 3 := by
  have hp : (0 : ℝ) < ‖(2 : ℚ_[2])‖ := norm_pos_iff.mpr two_ne_zero
  nlinarith [hp, norm_two_lt_one', pow_pos hp 3, pow_pos hp 4]

/-- The `a² − 4` side condition at `a = ±2`, where it is vacuous (`a² − 4 = 0`). -/
private theorem small_two {a : ℚ_[2]} (h : a ^ 2 - 4 = 0) : ‖a ^ 2 - 4‖ < ‖(2 : ℚ_[2])‖ ^ 3 := by
  rw [h, norm_zero]
  have hp : (0 : ℝ) < ‖(2 : ℚ_[2])‖ := norm_pos_iff.mpr two_ne_zero
  positivity

/-- The `a² − 4` side condition at `a = ±10`, where `a² − 4 = 96 = 2⁵·3`. -/
private theorem small_ten {a : ℚ_[2]} (h : a ^ 2 - 4 = 2 ^ 5 * 3) :
    ‖a ^ 2 - 4‖ < ‖(2 : ℚ_[2])‖ ^ 3 := by
  rw [h, norm_mul, norm_pow, norm_three, mul_one]
  exact norm_two_pow_five_lt

theorem not_hasEqualNormValueGroups_KSqrtNegTwo (δi : AlgebraicClosure ℚ_[2])
    (hδ : δi ^ 2 = -1) : ¬ GQ2.HasEqualNormValueGroups KSqrtNegTwo δi :=
  not_hasEqualNormValueGroups_quadField
    (by rw [valuation_neg, valuation_two]; exact ⟨0, by ring⟩) not_isSquare_neg_two
    (by rw [show (-2 : ℚ_[2]) = -(2 : ℚ_[2]) by norm_num, norm_neg]) (small_two (by ring)) δi hδ

theorem not_hasEqualNormValueGroups_KSqrtTwo (δi : AlgebraicClosure ℚ_[2])
    (hδ : δi ^ 2 = -1) : ¬ GQ2.HasEqualNormValueGroups KSqrtTwo δi :=
  not_hasEqualNormValueGroups_quadField
    (by rw [valuation_two]; exact ⟨0, by ring⟩) not_isSquare_two rfl (small_two (by ring)) δi hδ

theorem not_hasEqualNormValueGroups_KSqrtTen (δi : AlgebraicClosure ℚ_[2])
    (hδ : δi ^ 2 = -1) : ¬ GQ2.HasEqualNormValueGroups KSqrtTen δi :=
  not_hasEqualNormValueGroups_quadField
    (by rw [valuation_ten]; exact ⟨0, by ring⟩) not_isSquare_ten
    (norm_eq_of_valuation_eq (by norm_num) (by norm_num) (by rw [valuation_ten, valuation_two]))
    (small_ten (by norm_num)) δi hδ

theorem not_hasEqualNormValueGroups_KSqrtNegTen (δi : AlgebraicClosure ℚ_[2])
    (hδ : δi ^ 2 = -1) : ¬ GQ2.HasEqualNormValueGroups KSqrtNegTen δi :=
  not_hasEqualNormValueGroups_quadField
    (by rw [valuation_neg, valuation_ten]; exact ⟨0, by ring⟩) not_isSquare_neg_ten
    (by rw [show (-10 : ℚ_[2]) = -(10 : ℚ_[2]) by norm_num, norm_neg]
        exact norm_eq_of_valuation_eq (by norm_num) (by norm_num)
          (by rw [valuation_ten, valuation_two]))
    (small_ten (by norm_num)) δi hδ

end RowsRamified

/-! ## §8 Packet Thm. 1.1 at the *literal* `ℚ₂(√−2)`

The payoff.  `SqrtNeg2.sqrtNegTwo_candidate_equiv_galK` is stated over a supplied quadratic `K`
with `hdeg`, `params`/`params_qK` and `ramified` as binders.  Here every one of those is
**discharged by the arithmetic of the literal field**: `K := KSqrtNegTwo`, `hdeg` is
`finrank_KSqrtNegTwo`, the field parameters are the literal `pilotParams = (n, f, q_K) =
(2, 1, 2)` with `params_qK` supplied by `qOf_KSqrtNegTwo`, and `ramified` by
`not_hasEqualNormValueGroups_KSqrtNegTwo`.

What remains in the binder list is therefore exactly the **non-arithmetic** residue: the AX3/AX4
bundles `(B, FF, T)` (i.e. the census axioms B5-K/B10-K, which is where local class field theory
would enter and where Mathlib has nothing), the G-Lab pack, and the four analytic clauses.  No
`hdeg`, no `q_K`, no ramification hypothesis survives. -/

section Literal

open GQ2.Dyadic.MarkedCore GQ2.Dyadic.Count

/-- `(n, f, q_K) = (2, 1, 2)` — the numerical parameters of every ramified quadratic row,
as a literal `FieldParameters`. -/
def pilotParams : FieldParameters where
  n := 2
  f := 1
  qK := 2
  qK_eq := by norm_num
  one_le_n := by norm_num
  one_le_f := le_refl 1
  f_dvd_n := one_dvd 2

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec KSqrtNegTwo}
  {FF : DyadicUnitFiltration KSqrtNegTwo}

set_option maxHeartbeats 800000 in
/-- **Packet Thm. 1.1 at the literal field `ℚ₂(√−2)`.**

`Γ_{R_{N,2,0}} = ⟨σ, τ, x₀, x₁, x₂ ∣ τ^σ = τ², x₀⁶[x₀,x₁]·x₂^{-σ}(x₂τ)^{ω₂} = 1⟩ ≅ G_K`
for `K = ℚ₂(√−2)`, the actual field of the pilot row — not merely for "some supplied quadratic
`K` with the right arithmetic".

Every arithmetic binder of `SqrtNeg2.sqrtNegTwo_candidate_equiv_galK` is discharged here; the
surviving hypotheses are the AX3/AX4 bundles and the analytic clauses, none of which mention
the field's arithmetic. -/
theorem sqrtNegTwo_candidate_equiv_galK_literal (T : OrientedTameQuotientK B FF)
    (fLab : ContinuousMulEquiv ((DN 2 0) : Type)
      ((maxProPQuotient 2 (GalK KSqrtNegTwo)) : Type))
    (piAb : ((maxProPQuotient 2 (GalK KSqrtNegTwo)) : Type) →* GalKab KSqrtNegTwo)
    (hpiAb : Continuous piAb)
    (hpiNu : ∀ g : GalK KSqrtNegTwo,
      B.nu_ur (piAb (maxProPMk 2 (GalK KSqrtNegTwo) g)) = B.nu_ur (toAbK KSqrtNegTwo g))
    (horient : ∀ x, chiCycKAb KSqrtNegTwo (piAb (fLab x)) = chiN 2 0 x)
    (hScal : NScalingHypothesis 2 0)
    (hpair : IsUnit (Multiplicative.toAdd (B.nu_ur (piAb (fLab (dnSigma 2 0)))))
      ∨ IsUnit (Multiplicative.toAdd (B.nu_ur (piAb (fLab (dnX2 2 0))))))
    (hexact : ExactLiftingSemantics (galKProfinite KSqrtNegTwo) 2 (qOf KSqrtNegTwo FF)
      SqrtNeg2.pilotP SqrtNeg2.pilotNuP (standardNumerics 2))
    (hstokes : StokesDualityCertificate (galKProfinite KSqrtNegTwo) 2 (qOf KSqrtNegTwo FF)
      SqrtNeg2.pilotP SqrtNeg2.pilotNuP (standardNumerics 2) (smulZmod2GalK KSqrtNegTwo))
    (hsimp : SqrtNeg2.PilotHsimp (qOf KSqrtNegTwo FF))
    (hsplit : SqrtNeg2.PilotStageSep (qOf KSqrtNegTwo FF))
    (hZcount : SqrtNeg2.PilotStageZ (qOf KSqrtNegTwo FF))
    (hdet : SqrtNeg2.PilotDet (qOf KSqrtNegTwo FF) (qOf_ne_zero KSqrtNegTwo FF)
      (even_qOf KSqrtNegTwo FF))
    (ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq pilotParams.qK) D)
      (rho : ContinuousMonoidHom ↥(GalKsub KSqrtNegTwo) D),
      (∃ v : V, c (tqTau pilotParams.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate pilotParams (GalKsub KSqrtNegTwo) V c rho)) :
    Nonempty (ContinuousMulEquiv ((candidateGroup 2 (qOf KSqrtNegTwo FF) Count.pilotW : Type))
      (GalK KSqrtNegTwo)) :=
  SqrtNeg2.sqrtNegTwo_candidate_equiv_galK T finrank_KSqrtNegTwo fLab piAb hpiAb hpiNu horient
    hScal hpair hexact hstokes hsimp hsplit hZcount hdet pilotParams rfl
    (qOf_KSqrtNegTwo FF).symm
    (fun δi hδ => not_hasEqualNormValueGroups_KSqrtNegTwo δi hδ) ramifiedData

end Literal

end GQ2.Dyadic.Fields
