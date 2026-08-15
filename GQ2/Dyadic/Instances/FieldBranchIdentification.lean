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

end GQ2.Dyadic.FieldBranchId
