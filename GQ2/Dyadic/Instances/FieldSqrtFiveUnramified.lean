/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.FieldUnimodularity

/-!
# W79-HOUSE: `ℚ₂(√5)` is unramified, and the `√5` row loses its clause

## The ticket

`docs/dyadic/w78-unimod-note.md` §6 item 1.  Wave 78 reduced the `ℚ₂(√5)` row of the frozen
five to exactly one named `Prop`, `fieldUni_TwoIsUniformizer KSqrtFive`: that `2` is a
uniformizer of `ℚ₂(√5)`, i.e. that the field is unramified over `ℚ₂`.  The note recorded that
the tree does not carry that fact, since all of `Fields.lean` §4's value-group work runs under
`Odd a.valuation`, which is false at `a = 5`, and `Fields.lean:243`'s `q_K = 4` is a docstring
remark with no theorem behind it.

## What this file establishes

`fieldFive_twoIsUniformizer : fieldUni_TwoIsUniformizer KSqrtFive`, hence
`fieldFive_genAsmBranch_sqrtFive`, the `ℚ₂(√5)` branch datum **with no clause at all**.  That
puts the third of the five frozen quadratic rows on the same footing as `ℚ₂(√−2)` and `ℚ₂(√2)`.

## The argument

The whole content is that the **value group does not grow**: every `z ∈ ℚ₂(√5)` has
`‖z‖ ∈ ‖ℚ₂ˣ‖`, so there is nothing strictly between `‖2‖` and `1` for `‖z‖` to be.

* `norm_algebra_eq_norm_pow_finrank` (`OddDegreeRamifiedI.lean:33`, no Galois hypothesis) gives
  `‖N_{K/ℚ₂}(z)‖ = ‖z‖²`, since `[K : ℚ₂] = 2`.
* `evenPolish_norm_quadElt` (`EvenRangePolish.lean:188`) gives `N(t + u√5) = t² − 5u²`, and
  `fieldFive_norm_quadElt` extends it across the `u = 0` boundary the committed statement
  excludes.
* So it is enough that `‖t² − 5u²‖` is a **square** in `‖ℚ₂ˣ‖`, and that is
  `fieldFive_exists_sq`.  Dividing by `u`, it reduces to `fieldFive_exists_sq_sub_five`: for
  every `s`, `‖s² − 5‖ = ‖d‖²` for some `d ≠ 0`.  Three cases, and only the middle one is
  arithmetic:
  - `‖s‖ < 1`: `‖s²‖ < 1 = ‖5‖`, so `‖s² − 5‖ = ‖5‖ = ‖1‖²`;
  - `‖s‖ > 1`: `‖s²‖ > ‖5‖`, so `‖s² − 5‖ = ‖s‖²`;
  - `‖s‖ = 1`: `s² ≡ 1 (mod 8)`, so `s² − 5 = (s² − 1) − 4` has `‖s² − 1‖ ≤ ‖8‖ < ‖4‖`, whence
    `‖s² − 5‖ = ‖4‖ = ‖2‖²`.

The `≡ 1 (mod 8)` step is `fieldFive_sq_sub_one_le_eight`, by `decide` over `ZMod 8` in the idiom
of `Fields.not_isSquare_five` and `Fields.norm_sub_one_le_norm_two`.  **This is the same mod-`8`
fact that makes `5` a non-square**, used one step further: there it says `5` is not `1` mod `8`,
here it says the gap between them is exactly `4`.  That the gap is `4` rather than `8` is
precisely why `ℚ₂(√5)` is unramified and not ramified.

## Scope

`fieldUni_TwoIsUniformizer` is stated for a general `K` and this file discharges it at
`KSqrtFive` only.  Nothing else is touched; the module is a leaf with one consumer statement
(`fieldFive_genAsmBranch_sqrtFive`) restating wave 78's row without its hypothesis.
-/

namespace GQ2.Dyadic.FieldSqrtFive

open GQ2 GQ2.Dyadic.Fields GQ2.Dyadic.EvenRangePolish GQ2.Dyadic.FieldUnimod
open GQ2.Dyadic.MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 Two `ℚ₂` facts

`‖5‖ = 1` and "a nonzero element of norm `< 1` has norm at most `‖2‖`".  The second is the
statement that `ℚ₂`'s value group is `2^ℤ`; it is what the whole file transports to `ℚ₂(√5)`. -/

section Base

/-- `‖5‖ = 1`: `5` is a `2`-adic unit. -/
theorem fieldFive_norm_five : ‖(5 : ℚ_[2])‖ = 1 := by
  rw [Padic.norm_eq_zpow_neg_valuation (by norm_num : (5 : ℚ_[2]) ≠ 0), valuation_five]
  norm_num

/-- `‖2‖ = 2⁻¹`, spelled as a `zpow` so it composes with `Padic.norm_eq_zpow_neg_valuation`. -/
theorem fieldFive_norm_two_zpow : ‖(2 : ℚ_[2])‖ = (2 : ℝ) ^ (-(1 : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by norm_num : (2 : ℚ_[2]) ≠ 0), valuation_two]
  norm_num

/-- **The value group of `ℚ₂` is discrete at the top.**  A nonzero `c` of norm `< 1` has
`‖c‖ ≤ ‖2‖`: there is nothing strictly between. -/
theorem fieldFive_norm_le_two {c : ℚ_[2]} (hc : c ≠ 0) (h : ‖c‖ < 1) : ‖c‖ ≤ ‖(2 : ℚ_[2])‖ := by
  rw [Padic.norm_eq_zpow_neg_valuation hc] at h ⊢
  rw [fieldFive_norm_two_zpow]
  have hone : (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := by norm_num
  rw [hone] at h
  have hlt : -c.valuation < (0 : ℤ) :=
    (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

/-- **`s² ≡ 1 (mod 8)` at a unit.**  The `decide` is over `ZMod 8`: the four units square to
`1`.  This is `Fields.not_isSquare_five`'s mod-`8` input, kept as an inequality rather than
turned into a non-membership. -/
theorem fieldFive_sq_sub_one_le_eight {s : ℚ_[2]} (hs : ‖s‖ = 1) :
    ‖s ^ 2 - 1‖ ≤ (2 : ℝ) ^ (-(3 : ℤ)) := by
  set sz : ℤ_[2] := ⟨s, le_of_eq hs⟩ with hsz
  have hsu : IsUnit sz := PadicInt.isUnit_iff.mpr hs
  have himg : PadicInt.toZModPow (p := 2) 3 (sz ^ 2 - 1) = 0 := by
    rw [map_sub, map_pow, map_one]
    exact (by decide : ∀ x : ZMod (2 ^ 3), IsUnit x → x ^ 2 - 1 = 0) _ (hsu.map _)
  have hker : sz ^ 2 - 1 ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, himg]
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (sz ^ 2 - 1) 3).mpr hker
  rw [PadicInt.norm_def] at hnorm
  have hcoe : (((sz ^ 2 - 1 : ℤ_[2])) : ℚ_[2]) = s ^ 2 - 1 := by
    rw [PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_one]
  rw [hcoe] at hnorm
  exact hnorm

end Base

/-! ## §2 `‖s² − 5‖` is a square in the value group

The one lemma with arithmetic in it.  All three cases land on a `d` with `‖s² − 5‖ = ‖d‖²`, and
the unit case is the one that decides ramification: the answer is `‖2‖²`, one step of the value
group, not the half step a ramified field would produce. -/

section SqSubFive

open IsUltrametricDist

/-- **`‖s² − 5‖` is a square.**  `d = 1` below `1`, `d = s` above, and `d = 2` at a unit, that
last by the mod-`8` gap `s² − 5 ≡ −4`. -/
theorem fieldFive_exists_sq_sub_five (s : ℚ_[2]) :
    ∃ d : ℚ_[2], d ≠ 0 ∧ ‖s ^ 2 - 5‖ = ‖d‖ ^ 2 := by
  have h5 : ‖(5 : ℚ_[2])‖ = 1 := fieldFive_norm_five
  have hsq : ‖s ^ 2‖ = ‖s‖ ^ 2 := norm_pow s 2
  have hs0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  rcases lt_trichotomy ‖s‖ 1 with hlt | heq | hgt
  · -- below `1`: the constant `5` wins the ultrametric comparison
    refine ⟨1, one_ne_zero, ?_⟩
    have hA : ‖s ^ 2‖ < ‖(-5 : ℚ_[2])‖ := by
      rw [hsq, norm_neg, h5]; nlinarith
    rw [sub_eq_add_neg, norm_add_eq_max_of_norm_ne_norm hA.ne, max_eq_right hA.le,
      norm_neg, h5, norm_one, one_pow]
  · -- at a unit: `s² − 5 = (s² − 1) − 4`, and `‖s² − 1‖ ≤ ‖8‖ < ‖4‖`
    refine ⟨2, two_ne_zero, ?_⟩
    have hgap : ‖s ^ 2 - 1‖ ≤ (2 : ℝ) ^ (-(3 : ℤ)) := fieldFive_sq_sub_one_le_eight heq
    have hstep : (2 : ℝ) ^ (-(3 : ℤ)) < (2 : ℝ) ^ (-(2 : ℤ)) := by
      apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
      omega
    have h4 : ‖(4 : ℚ_[2])‖ = (2 : ℝ) ^ (-(2 : ℤ)) := by
      rw [show (4 : ℚ_[2]) = 2 * 2 by norm_num, norm_mul, fieldFive_norm_two_zpow,
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have hA : ‖s ^ 2 - 1‖ < ‖(-4 : ℚ_[2])‖ := by
      rw [norm_neg, h4]; linarith
    have hrw : s ^ 2 - 5 = s ^ 2 - 1 + (-4 : ℚ_[2]) := by ring
    rw [hrw, norm_add_eq_max_of_norm_ne_norm hA.ne, max_eq_right hA.le, norm_neg, h4,
      fieldFive_norm_two_zpow, ← zpow_natCast ((2 : ℝ) ^ (-(1 : ℤ))) 2, ← zpow_mul]
    norm_num
  · -- above `1`: the square wins
    refine ⟨s, ?_, ?_⟩
    · intro h0
      rw [h0, norm_zero] at hgt
      linarith
    · have hA : ‖(-5 : ℚ_[2])‖ < ‖s ^ 2‖ := by
        rw [hsq, norm_neg, h5]; nlinarith
      rw [sub_eq_add_neg, norm_add_eq_max_of_norm_ne_norm hA.ne', max_eq_left hA.le, hsq]

/-- **`‖t² − 5u²‖` is a square**, for `(t, u) ≠ (0, 0)`: divide through by `u` and apply
`fieldFive_exists_sq_sub_five`. -/
theorem fieldFive_exists_sq {t u : ℚ_[2]} (h : t ≠ 0 ∨ u ≠ 0) :
    ∃ c : ℚ_[2], c ≠ 0 ∧ ‖t ^ 2 - 5 * u ^ 2‖ = ‖c‖ ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · have ht : t ≠ 0 := by tauto
    exact ⟨t, ht, by rw [show t ^ 2 - 5 * (0 : ℚ_[2]) ^ 2 = t ^ 2 by ring, norm_pow]⟩
  · obtain ⟨d, hd, hdnorm⟩ := fieldFive_exists_sq_sub_five (t / u)
    refine ⟨u * d, mul_ne_zero hu hd, ?_⟩
    have hrw : t ^ 2 - 5 * u ^ 2 = u ^ 2 * ((t / u) ^ 2 - 5) := by
      field_simp
    rw [hrw, norm_mul, hdnorm, norm_pow, norm_mul, mul_pow]

end SqSubFive

/-! ## §3 The norm form at `ℚ₂(√5)`, across the `u = 0` boundary

`evenPolish_norm_quadElt` carries `u ≠ 0` because its minimal polynomial argument does.  The
formula itself is true at `u = 0` as well, where the element is a scalar and `Algebra.norm` is
the `[K : ℚ₂]`-th power; both sides read `t²`. -/

section NormForm

/-- **`N(t + u√5) = t² − 5u²`, with no `u ≠ 0`.** -/
theorem fieldFive_norm_quadElt (t u : ℚ_[2]) :
    Algebra.norm ℚ_[2] (evenPolish_quadElt 5 t u) = t ^ 2 - 5 * u ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · have hscal : evenPolish_quadElt 5 t 0 = algebraMap ℚ_[2] ↥(quadField (5 : ℚ_[2])) t := by
      apply Subtype.ext
      rw [evenPolish_quadElt_val]
      simp
    rw [hscal, Algebra.norm_algebraMap, finrank_KSqrtFive]
    ring
  · exact evenPolish_norm_quadElt not_isSquare_five hu

end NormForm

/-! ## §4 The unramifiedness Prop, discharged

Assembly.  `‖z‖² = ‖N(z)‖ = ‖c‖²` with `c ∈ ℚ₂`, so `‖z‖ = ‖c‖` lies in `ℚ₂`'s value group, and
§1's discreteness finishes. -/

section Main

/-- **`2` IS A UNIFORMIZER OF `ℚ₂(√5)`**, i.e. the field is unramified over `ℚ₂`.  This is
`docs/dyadic/w78-unimod-note.md` §6 item 1, and it is the last input the `√5` row carried. -/
theorem fieldFive_twoIsUniformizer : fieldUni_TwoIsUniformizer KSqrtFive := by
  intro z hz hlt
  obtain ⟨t, u, htu⟩ := exists_repr not_isSquare_five z.2
  have hzq : z = evenPolish_quadElt 5 t u := Subtype.ext htu
  have hN : Algebra.norm ℚ_[2] z = t ^ 2 - 5 * u ^ 2 := by
    rw [hzq]; exact fieldFive_norm_quadElt t u
  have hbridge : ‖(Algebra.norm ℚ_[2] z : ℚ_[2])‖ = ‖((z : ↥KSqrtFive) : ℚ̄₂)‖ ^ 2 := by
    rw [GQ2.Dyadic.norm_algebra_eq_norm_pow_finrank KSqrtFive z, finrank_KSqrtFive]
  have htu0 : t ≠ 0 ∨ u ≠ 0 := by
    rcases eq_or_ne u 0 with rfl | hu
    · refine Or.inl fun ht0 => hz (Subtype.ext ?_)
      rw [htu, ht0]
      simp
    · exact Or.inr hu
  obtain ⟨c, hc, hcnorm⟩ := fieldFive_exists_sq htu0
  have hzc : ‖((z : ↥KSqrtFive) : ℚ̄₂)‖ = ‖c‖ := by
    have hsq : ‖((z : ↥KSqrtFive) : ℚ̄₂)‖ ^ 2 = ‖c‖ ^ 2 := by
      rw [← hbridge, hN, hcnorm]
    nlinarith [norm_nonneg ((z : ↥KSqrtFive) : ℚ̄₂), norm_nonneg c]
  rw [hzc, norm_two_alg]
  exact fieldFive_norm_le_two hc (hzc ▸ hlt)

/-- **THE `ℚ₂(√5)` ROW'S BRANCH DATUM, CLAUSE-FREE.**  Wave 78's
`fieldUni_genAsmBranch_sqrtFive_of_unramified` with its hypothesis discharged: the third of the
five frozen quadratic rows now carries nothing beyond the field's own bundle and the standing
instance binders, as `ℚ₂(√−2)` and `ℚ₂(√2)` already did. -/
theorem fieldFive_genAsmBranch_sqrtFive [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2] {Rec : LocalReciprocity} [T2Space (GalK KSqrtFive)]
    (B : MarkedRecip Rec KSqrtFive) :
    ∃ G : GenAsmBranch KSqrtFive B, G.pres = .M0 2 0 :=
  fieldUni_genAsmBranch_sqrtFive_of_unramified B fieldFive_twoIsUniformizer

end Main

/-! ## §5 Axiom pins

One line per declaration, in declaration order, following `GeneralAssembly.lean`'s convention.
The honest split: **everything through `fieldFive_twoIsUniformizer` is at the standard three**,
so the arithmetic discharged in this file costs no axiom.  The row theorem inherits exactly
wave 78's set for the `M`-row producer (the standard three plus `peripheralCyclotomicAction`
from `marked_matching_certificate_KTwoM_of_level_zero`, plus the even route's endpoint set);
discharging the clause adds nothing. -/

section AxiomPins

#print axioms fieldFive_norm_five
#print axioms fieldFive_norm_two_zpow
#print axioms fieldFive_norm_le_two
#print axioms fieldFive_sq_sub_one_le_eight
#print axioms fieldFive_exists_sq_sub_five
#print axioms fieldFive_exists_sq
#print axioms fieldFive_norm_quadElt
#print axioms fieldFive_twoIsUniformizer
#print axioms fieldFive_genAsmBranch_sqrtFive

end AxiomPins

end GQ2.Dyadic.FieldSqrtFive
