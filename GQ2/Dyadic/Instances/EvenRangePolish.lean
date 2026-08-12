/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenRangeModelFields

/-!
# W68-POLISH: the norm form of the `M` branch, and the quartic's ramification

## What this file is for

Wave 67 (`EvenRangeModelFields.lean`) computed the cyclotomic range at three named even-degree
fields.  Two of its three endpoints carry more than they need, and this file removes what it can.

## §1 to §3: the `M` branch without the base bundle

`hrangeFinal_sqrtTwo` carries two reciprocity bundles: `B` at `ℚ₂(√2)`, which every endpoint in
the tree carries, and `B0` at `ℚ₂` itself, which is an extra.  `B0` is there because wave 67
produced the value `−1` by making `χ` *surjective* at the base and then descending the resulting
Galois element to `ℚ₂(√2)`, and surjectivity at the base is what the odd-degree argument gives.

But a bundle already knows how to produce values at its own field.  Its norm-functoriality clause
(`MarkedRecip.norm_compat`, `incl ∘ rec_K = rec ∘ N_{K/ℚ₂}`) composed with the base bundle's
cyclotomic normalization on units (`LocalReciprocity.chiCyc_recip_unit`, `χ(rec u) = u⁻¹`) says

`χ_K(rec_K x) = N_{K/ℚ₂}(x)⁻¹`   whenever `N_{K/ℚ₂}(x)` is a `2`-adic **unit**,

so a single element of `K` whose norm is `−1` puts `−1` in the range.  At `ℚ₂(√2)` that element is
`1 + √2`, of norm `1 − 2 = −1`.  This is the same clause the tree already uses at odd degree
(`chiCycKAb_surjective_of_odd_finrank` feeds `norm_compat` a scalar unit, whose norm is a power);
the only new input is an honest norm computation at a quadratic field, which §1 supplies in the
general form `N(t + u√a) = t² − a u²`.

The route is not reciprocity-free: it is `B`-only.  No form of the `M` branch in the tree produces
a cyclotomic value without a reciprocity bundle somewhere, because producing a value is exactly
what reciprocity is for, and the honest gain here is that the bundle needed is the one the
endpoint already carries.  §3 restates the two `ℚ₂(√2)` headlines with the `B0` binder removed.

## §4 to §6: the quartic's ramification fact

`not_hasEqualNormValueGroups_KQuarticN` does not exist, and the quadratic row's proof
(`Fields.not_hasEqualNormValueGroups_quadField`) does not reach a quartic: its engine is
`Fields.exists_norm_sq_eq`, "every `z ∈ ℚ₂(√a)` has `‖z‖² ∈ ‖ℚ₂ˣ‖`", which is the statement that
the ramification index divides `2`.  At a quartic that statement is false.

What survives is the shape of the argument, with `2` replaced by the quartic's own index.  §4
proves the replacement engine at `KQuarticN` from the committed model data, §5 exhibits a witness
in `KQuarticN(i)` whose fourth power of the norm is an odd power of `‖2‖`, and §6 assembles.

## Numbering

1. the norm of `t + u√a` in `ℚ₂(√a)`;
2. `−1` as a cyclotomic value at `ℚ₂(√2)`, from the bundle at `ℚ₂(√2)`;
3. the two `ℚ₂(√2)` headlines with the base bundle removed;
4. the value group of the quartic model field;
5. the ramified-`i` witness at the quartic;
6. what the quartic still costs;
7. axiom pins.
-/

namespace GQ2.Dyadic.EvenRangePolish

open Polynomial IntermediateField
open GQ2 GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.Fields GQ2.Dyadic.EvenRangeModel

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The norm of `t + u√a`

`Algebra.norm` at a quadratic field is a two line computation once the minimal polynomial is
known, and the tree already carries the power basis of `ℚ_[2]⟮√a⟯`.  The element `t + u√a` with
`u ≠ 0` satisfies the monic `X² − 2tX + (t² − a u²)`, which has no `ℚ₂` root exactly because `a`
is not a square; so that polynomial *is* the minimal polynomial, `ℚ_[2]⟮t + u√a⟯` is all of
`ℚ₂(√a)`, and `Algebra.norm_eq_norm_adjoin` reads the norm off the constant coefficient. -/

section QuadNorm

variable {a : ℚ_[2]}

/-- The element `t + u√a` of `ℚ₂(√a)`. -/
noncomputable def evenPolish_quadElt (a t u : ℚ_[2]) : ↥(quadField a) :=
  ⟨algebraMap ℚ_[2] ℚ̄₂ t + algebraMap ℚ_[2] ℚ̄₂ u * sqrtIn a,
    add_mem ((quadField a).algebraMap_mem t)
      (mul_mem ((quadField a).algebraMap_mem u) (sqrtIn_mem_quadField a))⟩

@[simp] theorem evenPolish_quadElt_val (a t u : ℚ_[2]) :
    ((evenPolish_quadElt a t u : ↥(quadField a)) : ℚ̄₂)
      = algebraMap ℚ_[2] ℚ̄₂ t + algebraMap ℚ_[2] ℚ̄₂ u * sqrtIn a := rfl

/-- The monic quadratic `X² − 2tX + (t² − a u²)` satisfied by `t + u√a`. -/
noncomputable def evenPolish_quadMin (a t u : ℚ_[2]) : ℚ_[2][X] :=
  X ^ 2 - C (2 * t) * X + C (t ^ 2 - a * u ^ 2)

theorem evenPolish_quadMin_monic (a t u : ℚ_[2]) : (evenPolish_quadMin a t u).Monic := by
  unfold evenPolish_quadMin
  monicity!

theorem evenPolish_quadMin_natDegree (a t u : ℚ_[2]) :
    (evenPolish_quadMin a t u).natDegree = 2 := by
  unfold evenPolish_quadMin
  compute_degree!

theorem evenPolish_quadMin_coeff_zero (a t u : ℚ_[2]) :
    (evenPolish_quadMin a t u).coeff 0 = t ^ 2 - a * u ^ 2 := by
  simp only [evenPolish_quadMin, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_zero,
    coeff_C_zero, mul_zero]
  norm_num

theorem evenPolish_aeval_quadMin (a t u : ℚ_[2]) :
    aeval (algebraMap ℚ_[2] ℚ̄₂ t + algebraMap ℚ_[2] ℚ̄₂ u * sqrtIn a)
      (evenPolish_quadMin a t u) = 0 := by
  simp only [evenPolish_quadMin, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    map_ofNat]
  have hs := sqrtIn_sq a
  linear_combination (algebraMap ℚ_[2] ℚ̄₂ u) ^ 2 * hs

/-- **No `ℚ₂` root**, exactly because `a` is not a square: a root `r` gives `(r − t)² = a u²`. -/
theorem evenPolish_quadMin_irreducible (ha : ¬ IsSquare a) {t u : ℚ_[2]} (hu : u ≠ 0) :
    Irreducible (evenPolish_quadMin a t u) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by simp [evenPolish_quadMin_natDegree]) fun r hr => ha ⟨(r - t) / u, ?_⟩
  have hr' : r ^ 2 - 2 * t * r + (t ^ 2 - a * u ^ 2) = 0 := by
    simpa [evenPolish_quadMin, IsRoot, sub_eq_add_neg] using hr
  field_simp
  linear_combination -hr'

theorem evenPolish_minpoly_quadElt (ha : ¬ IsSquare a) {t u : ℚ_[2]} (hu : u ≠ 0) :
    minpoly ℚ_[2] (evenPolish_quadElt a t u) = evenPolish_quadMin a t u := by
  have hmin : minpoly ℚ_[2]
      (algebraMap ℚ_[2] ℚ̄₂ t + algebraMap ℚ_[2] ℚ̄₂ u * sqrtIn a)
      = evenPolish_quadMin a t u :=
    (minpoly.eq_of_irreducible_of_monic (evenPolish_quadMin_irreducible ha hu)
      (evenPolish_aeval_quadMin a t u) (evenPolish_quadMin_monic a t u)).symm
  rw [← hmin]
  exact (minpoly.algebraMap_eq (algebraMap (↥(quadField a)) ℚ̄₂).injective
    (evenPolish_quadElt a t u)).symm

theorem evenPolish_isIntegral_quadElt (a t u : ℚ_[2]) :
    IsIntegral ℚ_[2] (evenPolish_quadElt a t u) :=
  IsIntegral.of_finite ℚ_[2] _

/-- `ℚ₂(t + u√a)` is all of `ℚ₂(√a)`: both have degree `2` over `ℚ₂`. -/
theorem evenPolish_finrank_adjoin_quadElt (ha : ¬ IsSquare a) {t u : ℚ_[2]} (hu : u ≠ 0) :
    Module.finrank ↥(ℚ_[2]⟮evenPolish_quadElt a t u⟯) ↥(quadField a) = 1 := by
  have hbot : Module.finrank ℚ_[2] ↥(ℚ_[2]⟮evenPolish_quadElt a t u⟯) = 2 := by
    rw [IntermediateField.adjoin.finrank (evenPolish_isIntegral_quadElt a t u),
      evenPolish_minpoly_quadElt ha hu, evenPolish_quadMin_natDegree]
  have htower := Module.finrank_mul_finrank ℚ_[2]
    ↥(ℚ_[2]⟮evenPolish_quadElt a t u⟯) ↥(quadField a)
  rw [hbot, finrank_quadField ha] at htower
  omega

/-- **THE NORM AT A QUADRATIC FIELD.**  `N_{ℚ₂(√a)/ℚ₂}(t + u√a) = t² − a u²`, for `a` a non-square
and `u ≠ 0`.  At `a = 2`, `t = u = 1` this is `1 − 2 = −1`, the value §2 needs. -/
theorem evenPolish_norm_quadElt (ha : ¬ IsSquare a) {t u : ℚ_[2]} (hu : u ≠ 0) :
    Algebra.norm ℚ_[2] (evenPolish_quadElt a t u) = t ^ 2 - a * u ^ 2 := by
  rw [Algebra.norm_eq_norm_adjoin ℚ_[2] (evenPolish_quadElt a t u),
    evenPolish_finrank_adjoin_quadElt ha hu, pow_one]
  have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (IntermediateField.adjoin.powerBasis (evenPolish_isIntegral_quadElt a t u))
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
    IntermediateField.minpoly_gen, evenPolish_minpoly_quadElt ha hu,
    evenPolish_quadMin_natDegree, evenPolish_quadMin_coeff_zero] at hpb
  rw [hpb]
  ring

/-- `t + u√a` is nonzero when `a` is not a square and `u ≠ 0`: vanishing would exhibit `a` as
the square of `t/u`. -/
theorem evenPolish_quadElt_ne_zero (ha : ¬ IsSquare a) {t u : ℚ_[2]} (hu : u ≠ 0) :
    evenPolish_quadElt a t u ≠ 0 := by
  intro h
  have hcoe : algebraMap ℚ_[2] ℚ̄₂ t + algebraMap ℚ_[2] ℚ̄₂ u * sqrtIn a = 0 := by
    have := congrArg (Subtype.val (p := fun x => x ∈ quadField a)) h
    simpa [evenPolish_quadElt] using this
  have hsq : algebraMap ℚ_[2] ℚ̄₂ (u ^ 2 * a) = algebraMap ℚ_[2] ℚ̄₂ (t ^ 2) := by
    simp only [map_mul, map_pow]
    linear_combination (-(algebraMap ℚ_[2] ℚ̄₂ u ^ 2)) * sqrtIn_sq a
      + (algebraMap ℚ_[2] ℚ̄₂ u * sqrtIn a - algebraMap ℚ_[2] ℚ̄₂ t) * hcoe
  have hbase : u ^ 2 * a = t ^ 2 :=
    (algebraMap ℚ_[2] ℚ̄₂).injective hsq
  exact ha ⟨t / u, by field_simp; linear_combination hbase⟩

end QuadNorm

/-! ## §2 `−1` as a cyclotomic value at `ℚ₂(√2)`, from the bundle at `ℚ₂(√2)`

The bundle's norm-functoriality clause `norm_compat` sends `rec_K x` into `G_{ℚ₂}^{ab}` as
`rec (N_{K/ℚ₂} x)`, and the base bundle's clause (c) reads the cyclotomic character there as
inversion on units.  So a `K`-element of norm `−1` carries the cyclotomic value `(−1)⁻¹ = −1`,
and §1 exhibits one: `1 + √2`. -/

section SqrtTwoValue

open GQ2.Dyadic.LSquare

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **`1 + √2`**, as a unit of `ℚ₂(√2)`. -/
noncomputable def evenPolish_unitOnePlusSqrtTwo : (↥KSqrtTwo)ˣ :=
  Units.mk0 (evenPolish_quadElt 2 1 1) (evenPolish_quadElt_ne_zero not_isSquare_two one_ne_zero)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **`N_{ℚ₂(√2)/ℚ₂}(1 + √2) = −1`**, the arithmetic input of this file, in the shape the
bundle's norm clause consumes. -/
theorem evenPolish_normUnitsK_onePlusSqrtTwo :
    normUnitsK KSqrtTwo evenPolish_unitOnePlusSqrtTwo = unitEmbed (-1 : ℤ_[2]ˣ) := by
  apply Units.ext
  rw [normUnitsK_val, unitEmbed_val]
  show Algebra.norm ℚ_[2] (evenPolish_quadElt 2 1 1) = algebraMap ℤ_[2] ℚ_[2] (-1 : ℤ_[2])
  rw [evenPolish_norm_quadElt not_isSquare_two one_ne_zero]
  push_cast
  ring

/-- **`−1` IS A CYCLOTOMIC VALUE AT `ℚ₂(√2)`, FROM THE BUNDLE AT `ℚ₂(√2)`.**  This is
`EvenRangeModel.evenRangeF_neg_one_mem_sqrtTwo` with the base bundle `B0` removed: instead of
making `χ` surjective at `ℚ₂` and descending a Galois element, feed `1 + √2` to the bundle's own
norm clause.  `χ_K(rec_K(1 + √2)) = N(1 + √2)⁻¹ = (−1)⁻¹ = −1`. -/
theorem evenPolish_neg_one_mem_sqrtTwo (B : MarkedRecip R KSqrtTwo) :
    (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom := by
  rw [range_chiCycKTwo_eq_chiCycKAb]
  refine ⟨B.recip evenPolish_unitOnePlusSqrtTwo, ?_⟩
  rw [← chiCycAb_inclAbK, B.norm_compat, evenPolish_normUnitsK_onePlusSqrtTwo,
    R.chiCyc_recip_unit]
  simp

end SqrtTwoValue

/-! ## §3 The two `ℚ₂(√2)` headlines, with the base bundle removed

Same statements as `EvenRangeModel.hrangeFinal_sqrtTwo` and
`EvenRangeModel.hrangeFinal_orientedEquivM_sqrtTwo`, minus the `B0` binder.  The originals stand;
these are the primed forms. -/

section SqrtTwoEndpoints

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **`hrange` AT `ℚ₂(√2)`, OVER THE FIELD'S OWN BUNDLE ALONE.** -/
theorem hrangeFinal_sqrtTwo' (B : MarkedRecip R KSqrtTwo) :
    MonoidHom.range (chiCycKTwo (K := KSqrtTwo)).toMonoidHom = imChiM 3 :=
  evenRangeF_eq_imChiM_three_of_quadratic B finrank_KSqrtTwo
    (evenPolish_neg_one_mem_sqrtTwo B) evenRangeF_five_notMem_sqrtTwo

/-- **THE SECOND EVEN FIELD CLOSED, OVER ONE BUNDLE.**  `G_K(2)` for `K = ℚ₂(√2)` is
oriented-isomorphic to the `M` core at depth `3` and handle count `0`, over the reciprocity bundle
at `ℚ₂(√2)` and the standing instance binders alone.  The wave-67 form of this statement carried a
second bundle at `ℚ₂`. -/
theorem hrangeFinal_orientedEquivM_sqrtTwo' [T2Space (GalK KSqrtTwo)]
    (B : MarkedRecip R KSqrtTwo) :
    Nonempty (OrientedContinuousMulEquiv (chiM 3 0) (chiCycKTwo (K := KSqrtTwo))) :=
  GQ2.Dyadic.EvenParity.parityFinal_orientedEquivM_sqrtTwo (hrangeFinal_sqrtTwo' B)

end SqrtTwoEndpoints

end GQ2.Dyadic.EvenRangePolish

/-! ## §7 Axiom pins

The primed endpoints printed beside the wave-67 originals they replace, and beside the committed
statements they consume.  Nothing here may exceed the committed even endpoint set. -/

section AxiomPins

open GQ2.Dyadic.EvenRangePolish

-- §1 the quadratic norm
#print axioms evenPolish_quadMin_irreducible
#print axioms evenPolish_minpoly_quadElt
#print axioms evenPolish_finrank_adjoin_quadElt
#print axioms evenPolish_norm_quadElt
#print axioms evenPolish_quadElt_ne_zero

-- §2 the produced value
#print axioms evenPolish_normUnitsK_onePlusSqrtTwo
#print axioms evenPolish_neg_one_mem_sqrtTwo

-- §3 the primed endpoints
#print axioms hrangeFinal_sqrtTwo'
#print axioms hrangeFinal_orientedEquivM_sqrtTwo'

-- the wave-67 originals they replace, for the side-by-side
#print axioms GQ2.Dyadic.EvenRangeModel.hrangeFinal_sqrtTwo
#print axioms GQ2.Dyadic.EvenRangeModel.hrangeFinal_orientedEquivM_sqrtTwo
#print axioms GQ2.Dyadic.EvenRangeModel.hrangeFinal_orientedEquivN_sqrtNegTwo

end AxiomPins
