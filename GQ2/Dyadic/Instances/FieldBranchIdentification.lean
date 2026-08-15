/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenRangePolish
import GQ2.Dyadic.GeneralAssembly
import GQ2.Dyadic.GeneralCertificates
import GQ2.Dyadic.MarkedCore.MScalingHandles

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
`(−10, 0, 1)`.  Two of the three are **not** unit norms, and the uniformizer clause
`chiCyc_recip_uniformizer` is therefore doing real work.  (Why no unit-norm witness exists at
`ℚ₂(√10)` and `ℚ₂(√−10)`: the Hilbert symbol `(u, ±10)₂ = (−1)^{ω(u)}` makes the unit norms there
exactly the units `≡ ±1 (mod 8)`, all of which lie in `imChiM 3`.  That is a hand computation
recorded to explain the choice of witness; **nothing below depends on it**, the witnesses being
exhibited outright.)

## What is carried, and what is not

**Nothing is carried at any of the three.**  Each closes over the field's own reciprocity bundle
and the standing instance binders, exactly like the two fields of §0.

One asymmetry is worth recording because it decides which entry point each field uses.  The
classification `evenRange_range_eq` needs a ramification input, `¬ HasEqualNormValueGroups K δi`,
and the tree's only supplier is `Fields.not_hasEqualNormValueGroups_quadField`, whose hypothesis
is `Odd a.valuation`.  That holds at `−10` and `10` and **fails at `5`**: `ℚ₂(√5)` is the
unramified row (`Fields.lean:243`, `q_K = 4`), and the tree carries no
`not_hasEqualNormValueGroups_KSqrtFive`.  So `ℚ₂(√5)` cannot use that entry.  It does not need
to: the *other* committed entry, `evenRange_range_eq_imChiM`, takes `−1 ∈ range χ` in place of the
ramification binder, and `N(2 + √5) = 4 − 5 = −1` supplies it from the same bundle clause as
everything else here.  The `ℚ₂(√5)` row therefore costs one extra element, not one extra binder.

## Numbering

0. the two fields already closed, restated;
1. the criterion's arithmetic: the residues modulo `8` of `imChiN 2` and `imChiM 3`;
2. the criterion itself, in its two entry forms;
3. cyclotomic values from norms, including at an element of odd valuation;
4. the three fields' elements, units and norms;
5. the three range identities and the three oriented endpoints;
6. the composition into the `KTwoM`/`KTwoN` producer spelling;
7. the five rows' branch data, one clause each;
8. axiom pins.
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
`chiCyc_recip_uniformizer : χ(rec 2) = 1`, enters as well.  That clause is not decoration: by the
hand computation recorded in the header (Hilbert symbol, **not** formalized and **not** used
below), no unit-norm element of `ℚ₂(√10)` or `ℚ₂(√−10)` carries a residue-`5` value. -/

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

/-! ## §5 The three range identities and the three oriented endpoints

Each is one application of §2 to the field's own witness.  `ℚ₂(√10)` and `ℚ₂(√−10)` are ramified
and use the ramified entry with `Fields.not_hasEqualNormValueGroups_KSqrt{Ten,NegTen}`; `ℚ₂(√5)`
is unramified and uses the `M`-branch entry with `N(2 + √5) = −1`.  All three then compose with
`EvenParity.parityFinal_orientedEquivM_of_range` at `(α, h) = (2, 0)`. -/

section Endpoints

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **`−1` IS A CYCLOTOMIC VALUE AT `ℚ₂(√5)`**, from the field's own bundle: `N(2 + √5) = −1`. -/
theorem fieldId_neg_one_mem_sqrtFive (B : MarkedRecip R KSqrtFive) :
    (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := KSqrtFive)).toMonoidHom := by
  have h := fieldId_inv_mem_range_of_norm B fieldId_eltSqrtFiveNegOne (-1 : ℤ_[2]ˣ) 0
    fieldId_norm_eltSqrtFiveNegOne
  simpa using h

/-- **`hrange` AT `ℚ₂(√5)`, PROVED.**  The cyclotomic image on `G_K(2)` for `K = ℚ₂(√5)` is
`imChiM 2`, the image the `sqrtFive` row's core `DM 2 0` asks for.  Over the field's own
reciprocity bundle and the standing instance binders; **no ramification input**, which matters
because `ℚ₂(√5)` is the unramified row and the tree supplies none there. -/
theorem fieldId_hrange_sqrtFive (B : MarkedRecip R KSqrtFive) :
    MonoidHom.range (chiCycKTwo (K := KSqrtFive)).toMonoidHom = imChiM 2 :=
  fieldId_range_eq_imChiM_two_of_negOne B finrank_KSqrtFive (fieldId_neg_one_mem_sqrtFive B)
    (fieldId_inv_mem_range_of_norm B fieldId_eltSqrtFive fieldId_unitNegNineteen 0
      fieldId_norm_eltSqrtFive)
    (fieldId_toZModPow_inv fieldId_toZModPow_unitNegNineteen)

/-- **`hrange` AT `ℚ₂(√10)`, PROVED.**  Over the field's own reciprocity bundle and the standing
instance binders. -/
theorem fieldId_hrange_sqrtTen (B : MarkedRecip R KSqrtTen) :
    MonoidHom.range (chiCycKTwo (K := KSqrtTen)).toMonoidHom = imChiM 2 :=
  fieldId_range_eq_imChiM_two_of_ram B _
    GQ2.Dyadic.EvenParity.evenParity_sqrtIn_neg_one_sq
    (not_hasEqualNormValueGroups_KSqrtTen _
      GQ2.Dyadic.EvenParity.evenParity_sqrtIn_neg_one_sq)
    finrank_KSqrtTen
    (fieldId_inv_mem_range_of_norm B fieldId_eltSqrtTen fieldId_unitNegThree 1
      fieldId_norm_eltSqrtTen)
    (fieldId_toZModPow_inv fieldId_toZModPow_unitNegThree)

/-- **`hrange` AT `ℚ₂(√−10)`, PROVED.**  Over the field's own reciprocity bundle and the standing
instance binders. -/
theorem fieldId_hrange_sqrtNegTen (B : MarkedRecip R KSqrtNegTen) :
    MonoidHom.range (chiCycKTwo (K := KSqrtNegTen)).toMonoidHom = imChiM 2 :=
  fieldId_range_eq_imChiM_two_of_ram B _
    GQ2.Dyadic.EvenParity.evenParity_sqrtIn_neg_one_sq
    (not_hasEqualNormValueGroups_KSqrtNegTen _
      GQ2.Dyadic.EvenParity.evenParity_sqrtIn_neg_one_sq)
    finrank_KSqrtNegTen
    (fieldId_inv_mem_range_of_norm B fieldId_eltSqrtNegTen fieldId_unitFive 1
      fieldId_norm_eltSqrtNegTen)
    (fieldId_toZModPow_inv fieldId_toZModPow_unitFive)

/-- **THE `sqrtFive` ROW'S CLASSIFICATION DATUM.**  `G_K(2)` for `K = ℚ₂(√5)` is
oriented-isomorphic to the `M` core at depth `2` and handle count `0`, over the field's
reciprocity bundle and the standing instance binders alone. -/
theorem fieldId_orientedEquivM_sqrtFive [T2Space (GalK KSqrtFive)] (B : MarkedRecip R KSqrtFive) :
    Nonempty (OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := KSqrtFive))) :=
  GQ2.Dyadic.EvenParity.parityFinal_orientedEquivM_of_range (le_refl 2)
    (fieldId_hrange_sqrtFive B) (by rw [finrank_KSqrtFive])

/-- **THE `sqrtTen` ROW'S CLASSIFICATION DATUM.** -/
theorem fieldId_orientedEquivM_sqrtTen [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen) :
    Nonempty (OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := KSqrtTen))) :=
  GQ2.Dyadic.EvenParity.parityFinal_orientedEquivM_of_range (le_refl 2)
    (fieldId_hrange_sqrtTen B) (by rw [finrank_KSqrtTen])

/-- **THE `sqrtNegTen` ROW'S CLASSIFICATION DATUM.** -/
theorem fieldId_orientedEquivM_sqrtNegTen [T2Space (GalK KSqrtNegTen)]
    (B : MarkedRecip R KSqrtNegTen) :
    Nonempty (OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := KSqrtNegTen))) :=
  GQ2.Dyadic.EvenParity.parityFinal_orientedEquivM_of_range (le_refl 2)
    (fieldId_hrange_sqrtNegTen B) (by rw [finrank_KSqrtNegTen])

end Endpoints

/-! ## §6 The composition into the producer spelling

The critical-path memo's §1.5 point: the even route delivers
`OrientedContinuousMulEquiv (chi{M,N} alpha h) chiCycKTwo`, which is *definitionally* the
`(f, horient)` pair the direct `G_K(2)` producers `marked_matching_certificate_KTwo{M,N}`
consume, and `GeneralAssembly.genAsm_branch_of_even{M,N}` already packages that into a
`GenAsmBranch`.  With §5's identity supplying the `alpha` pin, the composition goes through at
each of the five fields, and this section records exactly what is left over at each.

Three of `genAsm_branch_of_evenM`'s six remaining inputs are discharged here:

* `hdeg`, from the field's `finrank`;
* `hMix`, from `MarkedCore.mMixHypothesis`, which is unconditional at `alpha >= 2`;
* the marking triple `nuP`/`hnuP`/`hnuIota`, from the canonical `Ztwo` marking.  The tree
  carried `SelectedCoreLeavesRN.nNuZtwo` for the `N` core and `LSquareCore.lNu` for the `L` core
  but **no `M` counterpart**; §6.1 builds it, the same three lines.

What is left at each field is then **one clause**, and it is the same clause the memo's §1.2 and
§1.3 tables call marked-data pair unimodularity: `hpivot` on the `M` rows (`nu_ur` is a unit at
the image of `C_0`), `hpair` on the pilot (at the image of `sigma` or of `x_2`).  That clause is
arithmetic about `K` and the bundle, not classification, and it is not attacked here. -/

section Producer

open MarkedCore

/-- **The canonical `Ztwo` marking of the compact-`M` core**, the `M` counterpart of
`SelectedCoreLeavesRN.nNuZtwo` (`CertificateSupplyRN.lean:223`, the *file* name the two earlier
spellings of this citation used as a namespace): `nuM` read back through the boundary seam
`ztwoIota`.  It
introduces no new orientation. -/
noncomputable def fieldId_mNuZtwo (alpha h : ℕ) (halpha : 1 ≤ alpha) :
    ContinuousMonoidHom (DM alpha h : Type) Ztwo :=
  ⟨(ztwoIota.symm.toMulEquiv.toMonoidHom).comp (nuM alpha h halpha).toMonoidHom,
    ztwoIota.symm.continuous_toFun.comp (nuM alpha h halpha).continuous_toFun⟩

@[simp] theorem fieldId_mNuZtwo_apply (alpha h : ℕ) (halpha : 1 ≤ alpha) (x : (DM alpha h : Type)) :
    fieldId_mNuZtwo alpha h halpha x = ztwoIota.symm (nuM alpha h halpha x) := rfl

/-- The seam inverts. -/
theorem fieldId_ztwoIota_mNuZtwo (alpha h : ℕ) (halpha : 1 ≤ alpha) (x : (DM alpha h : Type)) :
    ztwoIota (fieldId_mNuZtwo alpha h halpha x) = nuM alpha h halpha x :=
  ztwoIota.apply_symm_apply _

/-- The marking takes `ztwoOne` at the pivot `C_0`. -/
theorem fieldId_mNuZtwo_dmC (alpha h : ℕ) (halpha : 1 ≤ alpha) :
    fieldId_mNuZtwo alpha h halpha (dmC alpha h) = ztwoOne := by
  rw [fieldId_mNuZtwo_apply, nuM_dmC, ← ztwoIota_ztwoOne]
  exact ztwoIota.symm_apply_apply ztwoOne

/-- The marking is onto: `D_M` is compact and `ztwoOne` is in the image. -/
theorem fieldId_mNuZtwo_surjective (alpha h : ℕ) (halpha : 1 ≤ alpha) :
    Function.Surjective (fieldId_mNuZtwo alpha h halpha) :=
  GQ2.Dyadic.Instances.NuWitness.surjective_of_ztwoOne_mem_range _
    ⟨_, fieldId_mNuZtwo_dmC alpha h halpha⟩

/-- The seam inverts for the `N` core too, at the tree's canonical marking. -/
theorem fieldId_ztwoIota_nNuZtwo (alpha h : ℕ) (x : (DN alpha h : Type)) :
    ztwoIota (GQ2.Dyadic.SelectedCoreLeavesRN.nNuZtwo alpha h x) = nuN alpha h x :=
  ztwoIota.apply_symm_apply _

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K}

/-- **The `M` branch datum from an oriented equivalence at `alpha >= 2`**, with the marking
triple and `hMix` discharged.  Only the pivot clause remains. -/
theorem fieldId_genAsmBranch_of_orientedM (alpha h : ℕ) (halpha : 2 ≤ alpha)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.M0 alpha h).degree)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (hpivot : IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dmC alpha h))))) :
    ∃ G : GenAsmBranch K B, G.pres = .M0 alpha h :=
  genAsm_branch_of_evenM alpha h (by omega) hdeg (fieldId_mNuZtwo alpha h (by omega))
    (fieldId_mNuZtwo_surjective alpha h (by omega))
    (fieldId_ztwoIota_mNuZtwo alpha h (by omega)) e (mMixHypothesis alpha h halpha) hpivot

/-- **The `N` branch datum from an oriented equivalence**, with the marking triple discharged at
the tree's canonical `N` marking.  Only the marked-pair clause remains. -/
theorem fieldId_genAsmBranch_of_orientedN (alpha h : ℕ)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.N0 alpha h).degree)
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)))
    (hpair : IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnSigma alpha h)))) ∨
      IsUnit (Multiplicative.toAdd (nuUrKTwo B (e.1 (dnX2 alpha h))))) :
    ∃ G : GenAsmBranch K B, G.pres = .N0 alpha h :=
  genAsm_branch_of_evenN alpha h hdeg (GQ2.Dyadic.SelectedCoreLeavesRN.nNuZtwo alpha h)
    (GQ2.Dyadic.genCertNNuZtwo_surjective alpha h) (fieldId_ztwoIota_nNuZtwo alpha h) e hpair

end Producer

/-! ## §7 The five rows' branch data, one clause each

A chosen oriented equivalence per field (`Nonempty.some` on §5's output, respectively on wave
67's and wave 68's), and the branch datum over the single remaining clause at that equivalence.
`ℚ₂(√2)` sits at `alpha = 3` and the other four at `alpha = 2`; `mMixHypothesis` covers both. -/

section Rows

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- A chosen oriented equivalence at `ℚ₂(√−2)`. -/
noncomputable def fieldId_chosenEquivN_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) :
    OrientedContinuousMulEquiv (chiN 2 0) (chiCycKTwo (K := KSqrtNegTwo)) :=
  (GQ2.Dyadic.EvenRangeModel.hrangeFinal_orientedEquivN_sqrtNegTwo B).some

/-- A chosen oriented equivalence at `ℚ₂(√2)`. -/
noncomputable def fieldId_chosenEquivM_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (B : MarkedRecip R KSqrtTwo) :
    OrientedContinuousMulEquiv (chiM 3 0) (chiCycKTwo (K := KSqrtTwo)) :=
  (hrangeFinal_orientedEquivM_sqrtTwo' B).some

/-- A chosen oriented equivalence at `ℚ₂(√5)`. -/
noncomputable def fieldId_chosenEquivM_sqrtFive [T2Space (GalK KSqrtFive)]
    (B : MarkedRecip R KSqrtFive) :
    OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := KSqrtFive)) :=
  (fieldId_orientedEquivM_sqrtFive B).some

/-- A chosen oriented equivalence at `ℚ₂(√10)`. -/
noncomputable def fieldId_chosenEquivM_sqrtTen [T2Space (GalK KSqrtTen)]
    (B : MarkedRecip R KSqrtTen) :
    OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := KSqrtTen)) :=
  (fieldId_orientedEquivM_sqrtTen B).some

/-- A chosen oriented equivalence at `ℚ₂(√−10)`. -/
noncomputable def fieldId_chosenEquivM_sqrtNegTen [T2Space (GalK KSqrtNegTen)]
    (B : MarkedRecip R KSqrtNegTen) :
    OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := KSqrtNegTen)) :=
  (fieldId_orientedEquivM_sqrtNegTen B).some

/-- **THE PILOT ROW'S BRANCH DATUM**, over the marked-pair clause alone. -/
theorem fieldId_genAsmBranch_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo)
    (hpair : IsUnit (Multiplicative.toAdd
        (nuUrKTwo B ((fieldId_chosenEquivN_sqrtNegTwo B).1 (dnSigma 2 0)))) ∨
      IsUnit (Multiplicative.toAdd
        (nuUrKTwo B ((fieldId_chosenEquivN_sqrtNegTwo B).1 (dnX2 2 0))))) :
    ∃ G : GenAsmBranch KSqrtNegTwo B, G.pres = .N0 2 0 :=
  fieldId_genAsmBranch_of_orientedN 2 0 (by rw [finrank_KSqrtNegTwo]; rfl)
    (fieldId_chosenEquivN_sqrtNegTwo B) hpair

/-- **THE `sqrtTwo` ROW'S BRANCH DATUM**, over the pivot clause alone. -/
theorem fieldId_genAsmBranch_sqrtTwo [T2Space (GalK KSqrtTwo)] (B : MarkedRecip R KSqrtTwo)
    (hpivot : IsUnit (Multiplicative.toAdd
      (nuUrKTwo B ((fieldId_chosenEquivM_sqrtTwo B).1 (dmC 3 0))))) :
    ∃ G : GenAsmBranch KSqrtTwo B, G.pres = .M0 3 0 :=
  fieldId_genAsmBranch_of_orientedM 3 0 (by omega) (by rw [finrank_KSqrtTwo]; rfl)
    (fieldId_chosenEquivM_sqrtTwo B) hpivot

/-- **THE `sqrtFive` ROW'S BRANCH DATUM**, over the pivot clause alone. -/
theorem fieldId_genAsmBranch_sqrtFive [T2Space (GalK KSqrtFive)] (B : MarkedRecip R KSqrtFive)
    (hpivot : IsUnit (Multiplicative.toAdd
      (nuUrKTwo B ((fieldId_chosenEquivM_sqrtFive B).1 (dmC 2 0))))) :
    ∃ G : GenAsmBranch KSqrtFive B, G.pres = .M0 2 0 :=
  fieldId_genAsmBranch_of_orientedM 2 0 (le_refl 2) (by rw [finrank_KSqrtFive]; rfl)
    (fieldId_chosenEquivM_sqrtFive B) hpivot

/-- **THE `sqrtTen` ROW'S BRANCH DATUM**, over the pivot clause alone. -/
theorem fieldId_genAsmBranch_sqrtTen [T2Space (GalK KSqrtTen)] (B : MarkedRecip R KSqrtTen)
    (hpivot : IsUnit (Multiplicative.toAdd
      (nuUrKTwo B ((fieldId_chosenEquivM_sqrtTen B).1 (dmC 2 0))))) :
    ∃ G : GenAsmBranch KSqrtTen B, G.pres = .M0 2 0 :=
  fieldId_genAsmBranch_of_orientedM 2 0 (le_refl 2) (by rw [finrank_KSqrtTen]; rfl)
    (fieldId_chosenEquivM_sqrtTen B) hpivot

/-- **THE `sqrtNegTen` ROW'S BRANCH DATUM**, over the pivot clause alone. -/
theorem fieldId_genAsmBranch_sqrtNegTen [T2Space (GalK KSqrtNegTen)]
    (B : MarkedRecip R KSqrtNegTen)
    (hpivot : IsUnit (Multiplicative.toAdd
      (nuUrKTwo B ((fieldId_chosenEquivM_sqrtNegTen B).1 (dmC 2 0))))) :
    ∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .M0 2 0 :=
  fieldId_genAsmBranch_of_orientedM 2 0 (le_refl 2) (by rw [finrank_KSqrtNegTen]; rfl)
    (fieldId_chosenEquivM_sqrtNegTen B) hpivot

end Rows

/-! ## §8 Axiom pins

Every declaration of this file, printed beside the committed even-route endpoints it consumes.
Two sets appear, and both are already committed.

* The **range identities** of §5 and everything they rest on are at the standard three,
  `propext, Classical.choice, Quot.sound`, matching `evenRange_range_eq`,
  `evenRange_range_eq_imChiM` and the two §0 restatements.  So the branch identification itself
  costs no arithmetic axiom at any of the five fields.
* The **oriented endpoints** are at the even route's endpoint set, the standard three plus
  `hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
  `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` and
  `Foundations.absGalQ2_localEulerCharacteristic`.  That is exactly the set of
  `EvenParity.parityFinal_orientedEquivM_of_range`, the committed endpoint they call: the three
  new endpoints add nothing to it.
* The **`M`-row branch data** of §7 carry one axiom more, `peripheralCyclotomicAction`, and it
  enters at exactly one place: `MarkedCore.mMixHypothesis`, the committed unconditional discharge
  of the `M` producer's `hMix` binder, whose own set is the standard three plus that axiom.  It
  is pinned below beside `fieldId_genAsmBranch_of_orientedM` so the inheritance is visible.  The
  pilot's `N` branch datum does not carry it, the `N` producer having no `hMix`. -/

section AxiomPins

-- §0 the two fields already closed, restated
#print axioms fieldId_hrange_sqrtNegTwo
#print axioms fieldId_hrange_sqrtTwo

-- §1 the residues modulo `8`
#print axioms fieldId_toZModPow_nUnit_two
#print axioms fieldId_toZModPow_inv
#print axioms fieldId_notMem_imChiN_two
#print axioms fieldId_notMem_imChiM_three

-- §2 the criterion
#print axioms fieldId_range_eq_imChiM_two_of_classify
#print axioms fieldId_range_eq_imChiM_two_of_ram
#print axioms fieldId_range_eq_imChiM_two_of_negOne

-- §3 values from norms
#print axioms fieldId_inv_mem_range_of_norm

-- §4 the units, elements and norms
#print axioms fieldId_unitNegNineteen_val
#print axioms fieldId_unitNegThree_val
#print axioms fieldId_unitFive_val
#print axioms fieldId_toZModPow_unitNegNineteen
#print axioms fieldId_toZModPow_unitNegThree
#print axioms fieldId_toZModPow_unitFive
#print axioms fieldId_norm_eltSqrtFive
#print axioms fieldId_norm_eltSqrtFiveNegOne
#print axioms fieldId_norm_eltSqrtTen
#print axioms fieldId_norm_eltSqrtNegTen

-- §5 the three range identities and the three endpoints
#print axioms fieldId_neg_one_mem_sqrtFive
#print axioms fieldId_hrange_sqrtFive
#print axioms fieldId_hrange_sqrtTen
#print axioms fieldId_hrange_sqrtNegTen
#print axioms fieldId_orientedEquivM_sqrtFive
#print axioms fieldId_orientedEquivM_sqrtTen
#print axioms fieldId_orientedEquivM_sqrtNegTen

-- §6 the producer composition
#print axioms fieldId_ztwoIota_mNuZtwo
#print axioms fieldId_mNuZtwo_dmC
#print axioms fieldId_mNuZtwo_surjective
#print axioms fieldId_ztwoIota_nNuZtwo
#print axioms fieldId_genAsmBranch_of_orientedM
#print axioms fieldId_genAsmBranch_of_orientedN

-- §7 the five rows' branch data
#print axioms fieldId_genAsmBranch_sqrtNegTwo
#print axioms fieldId_genAsmBranch_sqrtTwo
#print axioms fieldId_genAsmBranch_sqrtFive
#print axioms fieldId_genAsmBranch_sqrtTen
#print axioms fieldId_genAsmBranch_sqrtNegTen

-- the committed endpoints consumed, for the side-by-side
#print axioms GQ2.Dyadic.MarkedCore.mMixHypothesis
#print axioms GQ2.Dyadic.genAsm_branch_of_evenM
#print axioms GQ2.Dyadic.genAsm_branch_of_evenN
#print axioms GQ2.Dyadic.EvenParity.parityFinal_orientedEquivM_of_range
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq
#print axioms GQ2.Dyadic.EvenCyclotomicRange.evenRange_range_eq_imChiM
#print axioms GQ2.Dyadic.EvenRangeModel.hrangeFinal_sqrtNegTwo
#print axioms GQ2.Dyadic.EvenRangePolish.hrangeFinal_sqrtTwo'

end AxiomPins

end GQ2.Dyadic.FieldBranchId
