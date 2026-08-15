/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcCertificate
import GQ2.Dyadic.GaussZ.FinalDK

/-!
# W80-ROWDATA: the procyclic rows' arithmetic, and the determinant wiring

Two independent tickets, both bookkeeping against committed statements.

**A.** Wave 79 reduced each of the two procyclic quadratic rows to one named `Prop`,
`MpcRowData_sqrt{Ten,NegTen}`, which is `B.r = 1` together with three congruences of the
transported marking.  This module discharges what the tree can carry and names, exactly, what it
cannot.

**B.** `GaussZ/FinalDK.lean` carries the `K` clone of the (83)-evaluation bridge; what was owed
was the wiring of its output into the `determinant` field of `KSupply`.

Declaration prefix `mpcRow`, namespace `GQ2.Dyadic.Instances.MpcRow`.
-/

namespace GQ2.Dyadic.Instances.MpcRow

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcCert GQ2.Dyadic.FieldUnimod GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Fields GQ2.Dyadic.LSquare

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## §1 The level at the two procyclic fields is at most one

Wave 78 §2.3 argued `B.r = 1` at `ℚ₂(√10)` and `ℚ₂(√−10)` twice, and neither argument was
formalized.  The `≤` half is formalizable exactly as §3 of `FieldUnimodularity` does the `= 0`
case, and with the same witness the unramified row uses: the **scalar `2`**.

At a ramified quadratic `K = ℚ₂(√a)` the scalar `2` has two properties at once:

* `N_{K/ℚ₂}(2) = 2^{[K:ℚ₂]}`, whose unit part is `1` **on the nose**, so `rec_K(2) ∈ ker χ_K`
  (`fieldUni_norm_twoUnit`, at every `K`);
* `2 = (a/2)⁻¹ · (√a)²` is a **square** of the uniformizer times a spectral unit, so
  `ν_ur(rec_K 2) = ofAdd(−2)`, of 2-adic valuation exactly `1`.

`nu_ker_chi_le` then puts `−2` in `2^{B.r} ℤ₂`, and `mpcCert_le_of_two_pow_eq` reads off
`B.r ≤ 1`.  Contrast `fieldUni_level_sqrtNegTwo`, where the witness has `ν`-value `−1` and the
same argument gives `B.r = 0`: the whole difference between the two pairs of ramified rows is
whether the field carries an element of odd valuation whose norm is a power of `2` on the nose.
-/

section Cofactor

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- The coercion of a unit decomposition `x = u · π^n` down to `ℚ̄₂`. -/
theorem mpcRow_val_of_decomp {x u pi : (↥K)ˣ} {n : ℕ} (hx : x = u * pi ^ (n : ℤ)) :
    ((x : ↥K) : ℚ̄₂) = ((u : ↥K) : ℚ̄₂) * ((pi : ↥K) : ℚ̄₂) ^ n := by
  rw [hx, zpow_natCast]
  push_cast
  ring

/-- **The cofactor of a power decomposition is a spectral unit** when the norms match: if
`x = u · π^n` and `‖x‖ = ‖π‖^n`, then `‖u‖ = 1`.  This is how the two rows below avoid ever
naming the scalar `a/2`. -/
theorem mpcRow_norm_cofactor {x u pi : (↥K)ˣ} {n : ℕ} (hx : x = u * pi ^ (n : ℤ))
    (hpi : ((pi : ↥K) : ℚ̄₂) ≠ 0) (h : ‖((x : ↥K) : ℚ̄₂)‖ = ‖((pi : ↥K) : ℚ̄₂)‖ ^ n) :
    ‖((u : ↥K) : ℚ̄₂)‖ = 1 := by
  have hval := mpcRow_val_of_decomp hx
  rw [hval, norm_mul, norm_pow] at h
  have hne : ‖((pi : ↥K) : ℚ̄₂)‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hpi)
  field_simp at h
  exact h

end Cofactor

section LevelUpper

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {Rec : LocalReciprocity}

/-- **The level from one element of `ν`-valuation exactly one**: the `r ≤ 1` companion of
`fieldUni_level_eq_zero_of_decomp`, whose witness is a *square* of the uniformizer rather than
the uniformizer itself. -/
theorem mpcRow_level_le_one_of_decomp (B : MarkedRecip Rec K) (x u pi : (↥K)ˣ)
    (hchi : chiCycKAb K (B.recip x) = 1) (hx : x = u * pi ^ ((2 : ℕ) : ℤ))
    (hu : ‖((u : ↥K) : ℚ̄₂)‖ = 1) (hpi : ‖((pi : ↥K) : ℚ̄₂)‖ < 1)
    (hmax : ∀ z : ↥K, z ≠ 0 → ‖(z : ℚ̄₂)‖ < 1 → ‖(z : ℚ̄₂)‖ ≤ ‖((pi : ↥K) : ℚ̄₂)‖) :
    B.r ≤ 1 := by
  obtain ⟨y, hy⟩ := B.nu_ker_chi_le _ hchi
  rw [B.nu_ur_recip_of_decomp x u pi ((2 : ℕ) : ℤ) hx hu hpi hmax] at hy
  refine mpcCert_le_of_two_pow_eq (γ := (-1 : ℤ_[2])) (y := y) isUnit_one.neg ?_
  rw [← hy, toAdd_ofAdd]
  push_cast
  ring

end LevelUpper

section QuadLevel

variable {Rec : LocalReciprocity} {a : ℚ_[2]}

/-- `‖(2 : ℚ̄₂)‖ = ‖(2 : ℚ₂)‖`: the spectral norm extends the 2-adic one. -/
theorem mpcRow_norm_two_alg : ‖(2 : ℚ̄₂)‖ = ‖(2 : ℚ_[2])‖ := by
  rw [show (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 by rw [map_ofNat]]
  exact GQ2.Dyadic.Fields.norm_algebraMap 2

/-- **`2` is a square of the uniformizer times a spectral unit** at a ramified quadratic field:
the decomposition witness of `mpcRow_level_le_one_of_decomp`. -/
def mpcRow_cofactor (ha : ¬ IsSquare a) : (↥(quadField a))ˣ :=
  fieldUni_twoUnit (quadField a) * ((fieldUni_rootUnit ha) ^ ((2 : ℕ) : ℤ))⁻¹

theorem mpcRow_two_decomp (ha : ¬ IsSquare a) :
    fieldUni_twoUnit (quadField a)
      = mpcRow_cofactor ha * (fieldUni_rootUnit ha) ^ ((2 : ℕ) : ℤ) :=
  (mul_inv_cancel_right _ _).symm

/-- `‖2/(√a)²‖ = 1` when `‖a‖ = ‖2‖`: the cofactor is spectral. -/
theorem mpcRow_norm_cofactor_eq_one (ha : ¬ IsSquare a) (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) :
    ‖((mpcRow_cofactor ha : ↥(quadField a)) : ℚ̄₂)‖ = 1 := by
  refine mpcRow_norm_cofactor (mpcRow_two_decomp ha) ?_ ?_
  · rw [fieldUni_rootUnit_val]
    intro h
    have := norm_sqrtIn_sq a
    rw [h, norm_zero, hna] at this
    rw [fieldUni_norm_two] at this
    norm_num at this
  · rw [fieldUni_twoUnit_val, fieldUni_rootUnit_val, mpcRow_norm_two_alg, ← hna]
    exact (norm_sqrtIn_sq a).symm

/-- **THE LEVEL AT A RAMIFIED QUADRATIC FIELD IS AT MOST ONE.**  The uniform statement behind
both procyclic rows: at `K = ℚ₂(√a)` with `v(a)` odd and `‖a‖ = ‖2‖`, the marked level satisfies
`B.r ≤ 1`.  (It is `0` exactly when the field also carries an element of *odd* valuation whose
norm is a power of `2` with unit part `1`; that is what separates `ℚ₂(√±2)` from `ℚ₂(√±10)`.) -/
theorem mpcRow_level_le_one_quadField (ha : ¬ IsSquare a) (hodd : Odd a.valuation)
    (hna : ‖a‖ = ‖(2 : ℚ_[2])‖) (B : MarkedRecip Rec (quadField a)) : B.r ≤ 1 := by
  refine mpcRow_level_le_one_of_decomp B (fieldUni_twoUnit (quadField a)) (mpcRow_cofactor ha)
    (fieldUni_rootUnit ha) ?_ (mpcRow_two_decomp ha) (mpcRow_norm_cofactor_eq_one ha hna)
    (fieldUni_rootUnit_lt_one ha hna) (fieldUni_rootUnit_max ha hodd hna)
  rw [fieldUni_chi_recip_of_norm B _ 1 _ fieldUni_norm_twoUnit, inv_one]

end QuadLevel

/-! ### §1.1 The two rows -/

section Rows

variable {Rec : LocalReciprocity}

theorem mpcRow_valuation_ten_odd : Odd (10 : ℚ_[2]).valuation := by
  rw [valuation_ten]
  exact ⟨0, by ring⟩

theorem mpcRow_valuation_neg_ten_odd : Odd (-10 : ℚ_[2]).valuation := by
  rw [valuation_neg, valuation_ten]
  exact ⟨0, by ring⟩

theorem mpcRow_norm_ten : ‖(10 : ℚ_[2])‖ = ‖(2 : ℚ_[2])‖ :=
  norm_eq_of_valuation_eq (by norm_num) (by norm_num) (by rw [valuation_ten, valuation_two])

theorem mpcRow_norm_neg_ten : ‖(-10 : ℚ_[2])‖ = ‖(2 : ℚ_[2])‖ := by
  rw [norm_neg]
  exact mpcRow_norm_ten

/-- **`B.r ≤ 1` AT `ℚ₂(√10)`**, over the field's own bundle and nothing else. -/
theorem mpcRow_level_le_one_sqrtTen (B : MarkedRecip Rec KSqrtTen) : B.r ≤ 1 :=
  mpcRow_level_le_one_quadField not_isSquare_ten mpcRow_valuation_ten_odd mpcRow_norm_ten B

/-- **`B.r ≤ 1` AT `ℚ₂(√−10)`**, over the field's own bundle and nothing else. -/
theorem mpcRow_level_le_one_sqrtNegTen (B : MarkedRecip Rec KSqrtNegTen) : B.r ≤ 1 :=
  mpcRow_level_le_one_quadField not_isSquare_neg_ten mpcRow_valuation_neg_ten_odd
    mpcRow_norm_neg_ten B

end Rows

end

end GQ2.Dyadic.Instances.MpcRow
