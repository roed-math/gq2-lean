/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenRangePolish

/-!
# W77-FIELD: the branch identification at the five committed quadratic model fields

## The ticket

`docs/dyadic/w74-critical-path.md` §3 item 1 asks for the *branch identification, per field*:

`range chiCycKTwo = imChiN alpha` (respectively `imChiM alpha`) at the row's depth,

for the five rows of `Main.lean`'s frozen quadratic table.  The row cores are

| row | field | core | image asked for |
| --- | --- | --- | --- |
| `sqrtNegTwo` | `ℚ₂(√−2)` | `DN 2 0` | `imChiN 2` |
| `sqrtTwo` | `ℚ₂(√2)` | `DM 3 0` | `imChiM 3` |
| `sqrtFive` | `ℚ₂(√5)` | `DM 2 0` | `imChiM 2` |
| `sqrtTen` | `ℚ₂(√10)` | `DM 2 0` | `imChiM 2` |
| `sqrtNegTen` | `ℚ₂(√−10)` | `DM 2 0` | `imChiM 2` |

## Status found at lane start, and what this file adds

Two of the five were already closed, at waves 67 and 68, and the memo's "smallest genuinely-open
item" is therefore open only on the three `DM 2 0` rows:

* `ℚ₂(√−2)`: `EvenRangeModel.hrangeFinal_sqrtNegTwo`, over the field's own bundle;
* `ℚ₂(√2)`: `EvenRangePolish.hrangeFinal_sqrtTwo'`, over the field's own bundle.

§0 records those two verbatim so the five rows can be read in one place.  §1 to §4 close the
remaining three.

## The argument for the three `DM 2 0` rows

All three want the *same* image, `imChiM 2`, and `imChiM 2 = ⊤`: a `2`-adic unit is `≡ 1` or
`≡ −1` modulo `4` always.  So the content is that the cyclotomic character is **surjective** at
each of `ℚ₂(√5)`, `ℚ₂(√10)`, `ℚ₂(√−10)`.

The committed classification (`evenRange_range_eq`) already says the range is `imChiM α` or
`imChiN α` for some `α ≥ 2`, and wave 67's degree bound (`evenRangeF_imChi{M,N}_depth_le` at
`e = m = 1`) caps `α` at `3` on `M` and at `2` on `N`.  So at a quadratic field the range is one
of exactly three subgroups: `imChiN 2`, `imChiM 3`, `imChiM 2`.  Reading the first two modulo `8`,

`imChiN 2 ⊆ {1, nUnit 2} = {1, 3}`,     `imChiM 3 = {1, −1} = {1, 7}`,

so **one cyclotomic value `≡ 5 (mod 8)` excludes both** and pins the range at `imChiM 2`.  That is
§2's criterion, and it is strictly cheaper than the route the two closed fields took: it needs no
`−1 ∈ range` (the `M`-branch entry condition) and no `5 ∉ range` (the depth-`3` exclusion), one
membership in place of two.

§1 produces the value.  The bundle's norm clause gives `χ_K(rec_K x) = N_{K/ℚ₂}(x)⁻¹` on the unit
part, and `χ(rec 2) = 1` at the uniformizer, so an element of `K` whose norm is `2^e · u` carries
the cyclotomic value `u⁻¹`.  Inverting is harmless modulo `8`, since `5⁻¹ ≡ 5` and `3⁻¹ ≡ 3`.  The
three witnesses are

| field | `x` | `N(x)` | value | mod `8` |
| --- | --- | --- | --- | --- |
| `ℚ₂(√5)` | `1 + 2√5` | `−19` | `(−19)⁻¹` | `5` |
| `ℚ₂(√10)` | `2 + √10` | `−6 = 2 · (−3)` | `(−3)⁻¹` | `5` |
| `ℚ₂(√−10)` | `√−10` | `10 = 2 · 5` | `5⁻¹` | `5` |

and the norms are `evenPolish_norm_quadElt`'s `t² − a u²` at `(a, t, u) = (5, 1, 2)`, `(10, 2, 1)`,
`(−10, 0, 1)`.  Two of the three are **not** unit norms, which is not an accident: at `ℚ₂(√10)`
and `ℚ₂(√−10)` the unit norms are exactly the units `≡ ±1 (mod 8)` (Hilbert symbol `(u, ±10)₂`),
so no unit-norm witness of the kind wave 68 used at `ℚ₂(√2)` exists there, and the uniformizer
clause `chiCyc_recip_uniformizer` is doing real work.

## What is carried, and what is not

Nothing here is carried at `ℚ₂(√10)` and `ℚ₂(√−10)`: those two close over the field's own
reciprocity bundle and the standing instance binders, exactly like the two fields of §0.

`ℚ₂(√5)` is different, and the difference is recorded honestly in §3.  It is the one **unramified**
field of the five, and the classification's ramification input
(`¬ HasEqualNormValueGroups K δi`) is supplied in the tree only by
`Fields.not_hasEqualNormValueGroups_quadField`, whose hypothesis is `Odd a.valuation`.  That
hypothesis holds at `−2, 2, 10, −10` and fails at `5`.  So the `ℚ₂(√5)` identity is landed as an
implication over a named binder, `FieldIdSqrtFiveRamified`, and §3 says precisely what that binder
is and why it is true; it is not asserted.

## Numbering

0. the two fields already closed, restated;
1. the cyclotomic value `≡ 5 (mod 8)` at each of the three `DM 2 0` fields;
2. the criterion: one such value pins the range at `imChiM 2` at a quadratic field;
3. `ℚ₂(√10)` and `ℚ₂(√−10)`: the range identity and the oriented endpoint, over the field's bundle;
4. `ℚ₂(√5)`: the same, over the named ramification binder;
5. the composite: the five rows side by side;
6. axiom pins.
-/

namespace GQ2.Dyadic.FieldBranchId

open Polynomial IntermediateField
open GQ2 GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.Fields GQ2.Dyadic.EvenRangeModel GQ2.Dyadic.EvenRangePolish

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §0 The two fields already closed

Restated here, unchanged, so that §5 can read the five rows in one place.  `ℚ₂(√−2)` is wave 67's
(`EvenRangeModelFields.lean` §7) and `ℚ₂(√2)` is wave 68's (`EvenRangePolish.lean` §3). -/

section AlreadyClosed

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **The `sqrtNegTwo` row's branch identification**, wave 67's, restated. -/
theorem fieldId_hrange_sqrtNegTwo (B : MarkedRecip R KSqrtNegTwo) :
    MonoidHom.range (chiCycKTwo (K := KSqrtNegTwo)).toMonoidHom = imChiN 2 :=
  hrangeFinal_sqrtNegTwo B

/-- **The `sqrtTwo` row's branch identification**, wave 68's, restated. -/
theorem fieldId_hrange_sqrtTwo (B : MarkedRecip R KSqrtTwo) :
    MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom = imChiM 3 :=
  hrangeFinal_sqrtTwo' B

end AlreadyClosed

/-! ## §1 The criterion: one cyclotomic value `≡ 5 (mod 8)`

At a quadratic field the committed classification plus wave 67's degree bound leave exactly three
possibilities for the range, `imChiN 2`, `imChiM 3` and `imChiM 2`.  Modulo `8` the first two are
`{1, 3}` and `{1, 7}` (`imChiN 2`'s upper bound is `evenRange_mem_imChiN_dvd` at `α = 2`, whose
modulus is `2^{α+1} = 8`, and its generator `nUnit 2 = −(1 + 2²)⁻¹` is `≡ 3`).  So a single value
`≡ 5 (mod 8)` rules both out. -/

section Criterion

/-- The `N`-image generator at depth `2` is `≡ 3 (mod 8)`: `nUnit 2 · 5 = −1`. -/
theorem fieldId_toZModPow_nUnit_two :
    PadicInt.toZModPow 3 ((nUnit 2 : ℤ_[2]ˣ) : ℤ_[2]) = 3 := by
  have h := congrArg (PadicInt.toZModPow (p := 2) 3) (nUnit_mul (α := 2) (by omega))
  simp only [map_mul, map_add, map_one, map_pow, map_ofNat, map_neg] at h
  revert h
  generalize PadicInt.toZModPow (p := 2) 3 ((nUnit 2 : ℤ_[2]ˣ) : ℤ_[2]) = y
  revert y
  decide

/-- Inverting does not move the residue `5` modulo `8`, since `5 · 5 = 1`. -/
theorem fieldId_toZModPow_inv {u : ℤ_[2]ˣ}
    (hu : PadicInt.toZModPow 3 ((u : ℤ_[2]ˣ) : ℤ_[2]) = 5) :
    PadicInt.toZModPow 3 ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
  have hmul : ((u : ℤ_[2]ˣ) : ℤ_[2]) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h := congrArg (PadicInt.toZModPow (p := 2) 3) hmul
  rw [map_mul, map_one, hu] at h
  revert h
  generalize PadicInt.toZModPow (p := 2) 3 ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = y
  revert y
  decide

/-- **`imChiN 2` carries no residue `5`.**  Its two residues modulo `8` are `1` and
`nUnit 2 ≡ 3`. -/
theorem fieldId_notMem_imChiN_two {w : ℤ_[2]ˣ}
    (hw : PadicInt.toZModPow 3 ((w : ℤ_[2]ˣ) : ℤ_[2]) = 5) : w ∉ imChiN 2 := by
  intro hmem
  rcases evenRange_mem_imChiN_dvd (le_refl 2) hmem with h | h
  · have hz := evenRange_toZModPow_eq_one_iff.mpr h
    rw [hw] at hz
    exact absurd hz (by decide)
  · have hz := evenRange_toZModPow_eq_iff.mpr h
    rw [hw, fieldId_toZModPow_nUnit_two] at hz
    exact absurd hz (by decide)

/-- **`imChiM 3` carries no residue `5`.**  Its two residues modulo `8` are `1` and `−1 ≡ 7`. -/
theorem fieldId_notMem_imChiM_three {w : ℤ_[2]ˣ}
    (hw : PadicInt.toZModPow 3 ((w : ℤ_[2]ˣ) : ℤ_[2]) = 5) : w ∉ imChiM 3 := by
  intro hmem
  rcases (evenRange_mem_imChiM_iff (by omega)).mp hmem with h | h
  · have hz := evenRange_toZModPow_eq_one_iff.mpr h
    rw [hw] at hz
    exact absurd hz (by decide)
  · have hd : (2 : ℤ_[2]) ^ 3 ∣ ((w : ℤ_[2]ˣ) : ℤ_[2]) - (-1 : ℤ_[2]) := by
      rw [sub_neg_eq_add]; exact h
    have hz := evenRange_toZModPow_eq_iff.mpr hd
    rw [hw, map_neg, map_one] at hz
    exact absurd hz (by decide)

end Criterion

/-! ## §2 The range identity at a quadratic field from one residue-`5` value

Two entry points, differing only in how the committed classification is started: the
ramification binder (`evenRange_range_eq`) or the `M`-branch entry condition
(`evenRange_range_eq_imChiM`).  Both then run the same three-way exclusion.  Which one a field
uses is decided by which input the tree supplies there, and §3/§4 record that per field. -/

section QuadraticIdentity

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **THE CRITERION.**  At a quadratic field, if the range is `imChiM α` or `imChiN α` for some
`α ≥ 2` and it contains a unit `≡ 5 (mod 8)`, then it is `imChiM 2` (`= ⊤`).  The degree bounds
`α` by `3` on `M` and by `2` on `N`; the residue kills `imChiM 3` and `imChiN 2`. -/
theorem fieldId_range_eq_imChiM_two_of_classify (B : MarkedRecip R K)
    (hdeg : Module.finrank ℚ_[2] K = 2)
    (hcl : ∃ alpha : ℕ, 2 ≤ alpha ∧
      (MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha ∨
        MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha))
    {w : ℤ_[2]ˣ} (hmem : w ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hw : PadicInt.toZModPow 3 ((w : ℤ_[2]ˣ) : ℤ_[2]) = 5) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2 := by
  obtain ⟨alpha, halpha, hr | hr⟩ := hcl
  · have hle := evenRangeF_imChiM_depth_le B (e := 1) (m := 1) odd_one
      (by rw [hdeg]; norm_num) halpha hr
    have hne : alpha ≠ 3 := by
      rintro rfl
      exact fieldId_notMem_imChiM_three hw (hr ▸ hmem)
    obtain rfl : alpha = 2 := by omega
    exact hr
  · exfalso
    have hle := evenRangeF_imChiN_depth_le B (e := 1) (m := 1) odd_one
      (by rw [hdeg]; norm_num) halpha hr
    obtain rfl : alpha = 2 := by omega
    exact fieldId_notMem_imChiN_two hw (hr ▸ hmem)

/-- **The criterion, ramified entry.**  For a quadratic `K` with `K(i)/K` ramified. -/
theorem fieldId_range_eq_imChiM_two_of_ram (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hdeg : Module.finrank ℚ_[2] K = 2)
    {w : ℤ_[2]ˣ} (hmem : w ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hw : PadicInt.toZModPow 3 ((w : ℤ_[2]ˣ) : ℤ_[2]) = 5) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2 :=
  fieldId_range_eq_imChiM_two_of_classify B hdeg
    (evenRange_range_eq B deltaI hdeltaI hram) hmem hw

/-- **The criterion, `M`-branch entry.**  For a quadratic `K` carrying the value `−1`.  This is
the route the *unramified* field `ℚ₂(√5)` takes, where the tree supplies no ramification fact. -/
theorem fieldId_range_eq_imChiM_two_of_negOne (B : MarkedRecip R K)
    (hdeg : Module.finrank ℚ_[2] K = 2)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    {w : ℤ_[2]ˣ} (hmem : w ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hw : PadicInt.toZModPow 3 ((w : ℤ_[2]ˣ) : ℤ_[2]) = 5) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2 := by
  obtain ⟨alpha, halpha, hr⟩ := evenRange_range_eq_imChiM B hneg
  exact fieldId_range_eq_imChiM_two_of_classify B hdeg ⟨alpha, halpha, Or.inl hr⟩ hmem hw

end QuadraticIdentity

/-! ## §3 Cyclotomic values from norms, including at a uniformizer

`EvenRangePolish` §2 read `χ_K(rec_K x) = N_{K/ℚ₂}(x)⁻¹` off the bundle's norm clause and the
base bundle's clause (c) on **units**.  Two of the three fields here need the same reading at an
element whose norm is `2` times a unit, so the base bundle's other cyclotomic clause,
`chiCyc_recip_uniformizer : χ(rec 2) = 1`, enters as well.  That clause is not decoration: at
`ℚ₂(√10)` and `ℚ₂(√−10)` the *unit* norms are exactly the units `≡ ±1 (mod 8)`, so no unit-norm
element of either field carries a residue-`5` value. -/

section NormValues

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

open GQ2.Dyadic.LSquare

/-- **The value carried by an element of known norm.**  If `N_{K/ℚ₂}(x) = u · 2^e` with `u` a
`2`-adic unit, then `u⁻¹` is a cyclotomic value on `G_K(2)`. -/
theorem fieldId_inv_mem_range_of_norm (B : MarkedRecip R K) (x : (↥K)ˣ) (u : ℤ_[2]ˣ) (e : ℕ)
    (hx : normUnitsK K x = unitEmbed u * uniformizer ^ e) :
    u⁻¹ ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom := by
  rw [range_chiCycKTwo_eq_chiCycKAb]
  refine ⟨B.recip x, ?_⟩
  rw [← chiCycAb_inclAbK, B.norm_compat, hx]
  simp only [map_mul, map_pow, R.chiCyc_recip_unit, R.chiCyc_recip_uniformizer, one_pow, mul_one]

end NormValues

/-! ## §4 The three `DM 2 0` fields

Each field supplies one element and one norm.  The norms are `evenPolish_norm_quadElt`'s
`N(t + u√a) = t² − a u²` at `(a, t, u) = (5, 1, 2)`, `(10, 2, 1)`, `(−10, 0, 1)`.

`ℚ₂(√10)` and `ℚ₂(√−10)` are ramified and take §2's ramified entry.  `ℚ₂(√5)` is the unramified
row (`Fields.lean:243`'s own docstring says so, `q_K = 4`) and the tree's ramification supplier
`Fields.not_hasEqualNormValueGroups_quadField` has the hypothesis `Odd a.valuation`, false at
`a = 5`; so that field takes the `M`-branch entry instead, on the strength of `N(2 + √5) = −1`.
Nothing is carried either way. -/

section Witnesses

/-- The unit `−19 = N(1 + 2√5)`. -/
noncomputable def fieldId_unitNegNineteen : ℤ_[2]ˣ := -(isUnit_one_add_two_mul (9 : ℤ_[2])).unit

@[simp] theorem fieldId_unitNegNineteen_val :
    ((fieldId_unitNegNineteen : ℤ_[2]ˣ) : ℤ_[2]) = -19 := by
  rw [fieldId_unitNegNineteen, Units.val_neg, IsUnit.unit_spec]
  norm_num

/-- The unit `−3`, the unit part of `N(2 + √10) = −6`. -/
noncomputable def fieldId_unitNegThree : ℤ_[2]ˣ := -(isUnit_one_add_two_mul (1 : ℤ_[2])).unit

@[simp] theorem fieldId_unitNegThree_val :
    ((fieldId_unitNegThree : ℤ_[2]ˣ) : ℤ_[2]) = -3 := by
  rw [fieldId_unitNegThree, Units.val_neg, IsUnit.unit_spec]
  norm_num

/-- The unit `5`, the unit part of `N(√−10) = 10`. -/
noncomputable def fieldId_unitFive : ℤ_[2]ˣ := (isUnit_one_add_two_mul (2 : ℤ_[2])).unit

@[simp] theorem fieldId_unitFive_val : ((fieldId_unitFive : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
  rw [fieldId_unitFive, IsUnit.unit_spec]
  norm_num

/-- `−19 ≡ 5 (mod 8)`. -/
theorem fieldId_toZModPow_unitNegNineteen :
    PadicInt.toZModPow 3 ((fieldId_unitNegNineteen : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
  rw [fieldId_unitNegNineteen_val]
  simp only [map_neg, map_ofNat]
  decide

/-- `−3 ≡ 5 (mod 8)`. -/
theorem fieldId_toZModPow_unitNegThree :
    PadicInt.toZModPow 3 ((fieldId_unitNegThree : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
  rw [fieldId_unitNegThree_val]
  simp only [map_neg, map_ofNat]
  decide

/-- `5 ≡ 5 (mod 8)`. -/
theorem fieldId_toZModPow_unitFive :
    PadicInt.toZModPow 3 ((fieldId_unitFive : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
  rw [fieldId_unitFive_val]
  simp only [map_ofNat]

/-- **`1 + 2√5`**, as a unit of `ℚ₂(√5)`. -/
noncomputable def fieldId_eltSqrtFive : (↥KSqrtFive)ˣ :=
  Units.mk0 (evenPolish_quadElt 5 1 2) (evenPolish_quadElt_ne_zero not_isSquare_five two_ne_zero)

/-- **`2 + √5`**, as a unit of `ℚ₂(√5)`; its norm is `−1`. -/
noncomputable def fieldId_eltSqrtFiveNegOne : (↥KSqrtFive)ˣ :=
  Units.mk0 (evenPolish_quadElt 5 2 1) (evenPolish_quadElt_ne_zero not_isSquare_five one_ne_zero)

/-- **`2 + √10`**, as a unit of `ℚ₂(√10)`. -/
noncomputable def fieldId_eltSqrtTen : (↥KSqrtTen)ˣ :=
  Units.mk0 (evenPolish_quadElt 10 2 1) (evenPolish_quadElt_ne_zero not_isSquare_ten one_ne_zero)

/-- **`√−10`**, as a unit of `ℚ₂(√−10)`. -/
noncomputable def fieldId_eltSqrtNegTen : (↥KSqrtNegTen)ˣ :=
  Units.mk0 (evenPolish_quadElt (-10) 0 1)
    (evenPolish_quadElt_ne_zero not_isSquare_neg_ten one_ne_zero)

/-- `N_{ℚ₂(√5)/ℚ₂}(1 + 2√5) = 1 − 20 = −19`. -/
theorem fieldId_norm_eltSqrtFive :
    normUnitsK KSqrtFive fieldId_eltSqrtFive = unitEmbed fieldId_unitNegNineteen * uniformizer ^ 0 := by
  apply Units.ext
  rw [Units.val_mul, normUnitsK_val, unitEmbed_val, fieldId_unitNegNineteen_val]
  show Algebra.norm ℚ_[2] (evenPolish_quadElt 5 1 2)
    = algebraMap ℤ_[2] ℚ_[2] (-19 : ℤ_[2]) * ((uniformizer : ℚ_[2]ˣ) : ℚ_[2]) ^ 0
  rw [evenPolish_norm_quadElt not_isSquare_five two_ne_zero]
  simp only [map_neg, map_ofNat]
  norm_num

/-- `N_{ℚ₂(√5)/ℚ₂}(2 + √5) = 4 − 5 = −1`. -/
theorem fieldId_norm_eltSqrtFiveNegOne :
    normUnitsK KSqrtFive fieldId_eltSqrtFiveNegOne = unitEmbed (-1 : ℤ_[2]ˣ) * uniformizer ^ 0 := by
  apply Units.ext
  rw [Units.val_mul, normUnitsK_val, unitEmbed_val]
  show Algebra.norm ℚ_[2] (evenPolish_quadElt 5 2 1)
    = algebraMap ℤ_[2] ℚ_[2] ((-1 : ℤ_[2]ˣ) : ℤ_[2]) * ((uniformizer : ℚ_[2]ˣ) : ℚ_[2]) ^ 0
  rw [evenPolish_norm_quadElt not_isSquare_five one_ne_zero]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  norm_num

/-- `N_{ℚ₂(√10)/ℚ₂}(2 + √10) = 4 − 10 = −6 = (−3) · 2`. -/
theorem fieldId_norm_eltSqrtTen :
    normUnitsK KSqrtTen fieldId_eltSqrtTen = unitEmbed fieldId_unitNegThree * uniformizer ^ 1 := by
  apply Units.ext
  rw [Units.val_mul, normUnitsK_val, unitEmbed_val, fieldId_unitNegThree_val]
  show Algebra.norm ℚ_[2] (evenPolish_quadElt 10 2 1)
    = algebraMap ℤ_[2] ℚ_[2] (-3 : ℤ_[2]) * ((uniformizer : ℚ_[2]ˣ) : ℚ_[2]) ^ 1
  rw [evenPolish_norm_quadElt not_isSquare_ten one_ne_zero]
  simp only [map_neg, map_ofNat, uniformizer_val]
  norm_num

/-- `N_{ℚ₂(√−10)/ℚ₂}(√−10) = 0 + 10 = 5 · 2`. -/
theorem fieldId_norm_eltSqrtNegTen :
    normUnitsK KSqrtNegTen fieldId_eltSqrtNegTen = unitEmbed fieldId_unitFive * uniformizer ^ 1 := by
  apply Units.ext
  rw [Units.val_mul, normUnitsK_val, unitEmbed_val, fieldId_unitFive_val]
  show Algebra.norm ℚ_[2] (evenPolish_quadElt (-10) 0 1)
    = algebraMap ℤ_[2] ℚ_[2] (5 : ℤ_[2]) * ((uniformizer : ℚ_[2]ˣ) : ℚ_[2]) ^ 1
  rw [evenPolish_norm_quadElt not_isSquare_neg_ten one_ne_zero]
  simp only [map_ofNat, uniformizer_val]
  norm_num

end Witnesses

end GQ2.Dyadic.FieldBranchId
