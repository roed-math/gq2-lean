/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenRangeModelFields
import GQ2.Dyadic.OddDegreeRamifiedI

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
proves the replacement engine at `KQuarticN` (`‖w‖⁴ ∈ ‖ℚ₂ˣ‖`, hence `‖w‖⁸` an even power of
`‖2‖`), §5 exhibits a witness in `KQuarticN(i)` with `‖z‖⁸ = ‖2‖¹¹`, and §6 assembles.

§6 assembles over the one hypothesis `i ∉ ℚ₂(β)`, which is the statement's own content rather
than a gap (with `i` in the field the two value groups coincide by definition), and §7 discharges
it.  The proof of §7 needs no degree theory and no root identification: from `β` and any square
root of `−1` one *builds* the number

`η = (β² + i(β² + 2)) / (2β)`,

checks `η⁸ = −1` from `β⁴ + 4β² + 2 = 0` and `(β² + 2)² = 2`, and then observes that `η − 1` sits
at level `1/8` while §4 puts every level of `ℚ₂(β)` in `(1/4)ℤ`.  So the ledger row
`EvenRouteModel.lean` §5 records as *measured* is now a theorem:
`evenPolish_not_hasEqualNormValueGroups_KQuarticN`.

## §8: the quartic's `hrange`, and the third even field

The `η` of §7 is a sixteenth root of unity given by a formula in `β`, and the formula's own
consequence is `η − η⁻¹ = β` **exactly** (both sides are `(2β²)/(2β)`).  That removes the
obstruction wave 67 recorded at the quartic, which was not the arithmetic but the identification
of which of the four roots of `X⁴ + 4X² + 2` the model's `Classical.choose` picked: no
identification is needed when the root of unity is built from the chosen root rather than matched
against it.

With `β = η − η⁻¹` in the field, a Galois element over `ℚ₂(β)` fixes it, so no cyclotomic value
may negate it.  Reading `g η = η^{χ(g)}` modulo `16`, both residues `9` and `15` negate
`η − η⁻¹`, so `9 ∉ range χ` and `−1 ∉ range χ` at the quartic.  Those are exactly the two
memberships `EvenRangeModel.hrangeFinal_quartic` carries, so `hrange` and the endpoint follow.

## Numbering

1. the norm of `t + u√a` in `ℚ₂(√a)`;
2. `−1` as a cyclotomic value at `ℚ₂(√2)`, from the bundle at `ℚ₂(√2)`;
3. the two `ℚ₂(√2)` headlines with the base bundle removed;
4. the value group of the quartic model field;
5. the ramified-`i` witness at the quartic;
6. the quartic's ramification fact over `i ∉ ℚ₂(β)`;
7. `i ∉ ℚ₂(β)`, and the ramification fact unconditionally;
8. the sixteenth root of unity in `ℚ₂(β)`, the two residues, and the quartic endpoint;
9. axiom pins.
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

/-! ## §4 The value group of the quartic model field

The quadratic row's engine is `Fields.exists_norm_sq_eq`: every `z ∈ ℚ₂(√a)` has `‖z‖² ∈ ‖ℚ₂ˣ‖`.
Its proof is specific to `quadField` (it runs on the coordinates `x + y√a`), but the statement is
not: for **any** finite `K/ℚ₂` the algebraic norm gives `‖z‖^{[K:ℚ₂]} = ‖N_{K/ℚ₂} z‖`
(`Dyadic.norm_algebra_eq_norm_pow_finrank`, which needs no Galois hypothesis).  At the quartic
that reads `‖z‖⁴ ∈ ‖ℚ₂ˣ‖`, so `‖z‖⁸` is always an **even** power of `‖2‖`.

The same lemma at `β` itself pins the quartic's own uniformizer: `N(β)` is the constant
coefficient `2` of `X⁴ + 4X² + 2`, so `‖β‖⁴ = ‖2‖`. -/

section QuarticValueGroup

open GQ2.Dyadic.EvenRouteModel

/-- `β`, as an element of `ℚ₂(β)`, in the `AdjoinSimple` presentation the power basis uses. -/
noncomputable def evenPolish_betaGen : ↥KQuarticN :=
  IntermediateField.AdjoinSimple.gen ℚ_[2] evenRouteModelBeta

theorem evenPolish_betaGen_val : ((evenPolish_betaGen : ↥KQuarticN) : ℚ̄₂) = evenRouteModelBeta :=
  IntermediateField.AdjoinSimple.coe_gen ℚ_[2] evenRouteModelBeta

theorem evenPolish_evenRouteModelPoly_coeff_zero : evenRouteModelPoly.coeff 0 = 2 := by
  simp only [evenRouteModelPoly, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C_zero]
  norm_num

/-- **`N_{ℚ₂(β)/ℚ₂}(β) = 2`.**  The constant coefficient of the Eisenstein quartic, read through
the adjoined power basis. -/
theorem evenPolish_norm_betaGen : Algebra.norm ℚ_[2] evenPolish_betaGen = 2 := by
  have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (IntermediateField.adjoin.powerBasis evenRouteModelBeta_isIntegral)
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
    IntermediateField.minpoly_gen, evenRouteModel_minpoly_beta,
    evenRouteModelPoly_natDegree, evenPolish_evenRouteModelPoly_coeff_zero] at hpb
  rw [show ((-1 : ℚ_[2]) ^ 4 * 2 : ℚ_[2]) = 2 by norm_num] at hpb
  exact hpb

/-- **`‖β‖⁴ = ‖2‖`.**  `β` is a uniformizer of the quartic: the field is totally ramified. -/
theorem evenPolish_norm_beta_pow_four :
    ‖evenRouteModelBeta‖ ^ 4 = ‖(2 : ℚ_[2])‖ := by
  have h := GQ2.Dyadic.norm_algebra_eq_norm_pow_finrank KQuarticN evenPolish_betaGen
  rw [evenPolish_norm_betaGen, finrank_KQuarticN, evenPolish_betaGen_val] at h
  exact h.symm

/-- **THE QUARTIC'S VALUE GROUP.**  Every nonzero element of `ℚ₂(β)` has `‖·‖⁴` in `‖ℚ₂ˣ‖`.  This
is the degree-four replacement for `Fields.exists_norm_sq_eq`, and it is what makes `‖·‖⁸` an even
power of `‖2‖` on the field. -/
theorem evenPolish_quartic_norm_pow_four (w : ↥KQuarticN) (hw : (w : ℚ̄₂) ≠ 0) :
    ∃ c : ℚ_[2], c ≠ 0 ∧ ‖(w : ℚ̄₂)‖ ^ 4 = ‖c‖ := by
  have h := GQ2.Dyadic.norm_algebra_eq_norm_pow_finrank KQuarticN w
  rw [finrank_KQuarticN] at h
  refine ⟨Algebra.norm ℚ_[2] w, ?_, h.symm⟩
  intro hz
  rw [hz, norm_zero] at h
  exact hw (norm_eq_zero.mp (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h.symm))

end QuarticValueGroup

/-! ## §5 The ramified-`i` witness at the quartic

The witness is `z = (β² − 2β) + (β² + 2)·i`, whose two coordinates lie in `ℚ₂(β)` because `β` does
and `(β² + 2)² = 2` is the committed square root of `2` there.  Up to the root `β` names, `z` is
`2β(ζ₁₆ − 1)`, so it is a uniformizer of `ℚ₂(ζ₁₆) = ℚ₂(β)(i)` times a `ℚ₂(β)`-element, and its
valuation has denominator `8`.

The computation is one line of algebra and one Galois step.  The algebra: with `i² = −1` and
`β⁴ + 4β² + 2 = 0`,

`(x + y i)(x − y i) = x² + y² = (β² − 2β)² + (β² + 2)² = −4β³`.

The Galois step: `x − y i` is the image of `z` under a conjugation of `ℚ̄₂` over `ℚ₂(β)` sending
`i ↦ −i`, which exists exactly because `i ∉ ℚ₂(β)`, and every such automorphism preserves the
spectral norm.  Hence `‖z‖² = ‖4β³‖`, and with `‖β‖⁴ = ‖2‖` from §4,

`‖z‖⁸ = ‖4‖⁴ · ‖β‖¹² = ‖2‖⁸ · ‖2‖³ = ‖2‖¹¹`,

an **odd** power, which §4 forbids on the field itself. -/

section QuarticWitness

open GQ2.Dyadic.EvenRouteModel GQ2.UnramifiedQuadraticNorms

theorem evenPolish_two_mem_quartic : (2 : ℚ̄₂) ∈ KQuarticN := by
  have h := KQuarticN.algebraMap_mem (2 : ℚ_[2])
  rwa [map_ofNat] at h

/-- The defining relation of `β`, in equational form. -/
theorem evenPolish_beta_rel :
    evenRouteModelBeta ^ 4 + 4 * evenRouteModelBeta ^ 2 + 2 = 0 := by
  have h := evenRouteModel_aeval_beta
  simp only [evenRouteModelPoly, map_add, map_pow, aeval_X, map_mul, map_ofNat] at h
  linear_combination h

/-- The witness's first coordinate `β² − 2β`. -/
noncomputable def evenPolish_quarticX : ↥KQuarticN :=
  ⟨evenRouteModelBeta ^ 2 - 2 * evenRouteModelBeta,
    sub_mem (pow_mem evenRouteModelBeta_mem 2)
      (mul_mem evenPolish_two_mem_quartic evenRouteModelBeta_mem)⟩

/-- The witness's second coordinate `β² + 2`, a square root of `2` in `ℚ₂(β)`. -/
noncomputable def evenPolish_quarticY : ↥KQuarticN :=
  ⟨evenRouteModelBeta ^ 2 + 2,
    add_mem (pow_mem evenRouteModelBeta_mem 2) evenPolish_two_mem_quartic⟩

theorem evenPolish_quarticX_val :
    ((evenPolish_quarticX : ↥KQuarticN) : ℚ̄₂)
      = evenRouteModelBeta ^ 2 - 2 * evenRouteModelBeta := rfl

theorem evenPolish_quarticY_val :
    ((evenPolish_quarticY : ↥KQuarticN) : ℚ̄₂) = evenRouteModelBeta ^ 2 + 2 := rfl

/-- **The witness** `z = (β² − 2β) + (β² + 2)·i`. -/
noncomputable def evenPolish_quarticWitness (deltaI : ℚ̄₂) : ℚ̄₂ :=
  ((evenPolish_quarticX : ↥KQuarticN) : ℚ̄₂)
    + ((evenPolish_quarticY : ↥KQuarticN) : ℚ̄₂) * deltaI

variable {deltaI : ℚ̄₂}

/-- **The norm form of the witness**: `z · z̄ = −4β³`, from `i² = −1` and `β⁴ + 4β² + 2 = 0`. -/
theorem evenPolish_witness_mul_conj (hdeltaI : deltaI ^ 2 = -1) :
    evenPolish_quarticWitness deltaI
        * (((evenPolish_quarticX : ↥KQuarticN) : ℚ̄₂)
          - ((evenPolish_quarticY : ↥KQuarticN) : ℚ̄₂) * deltaI)
      = -(4 * evenRouteModelBeta ^ 3) := by
  rw [evenPolish_quarticWitness, evenPolish_quarticX_val, evenPolish_quarticY_val]
  linear_combination (2 : ℚ̄₂) * evenPolish_beta_rel
    - (evenRouteModelBeta ^ 2 + 2) ^ 2 * hdeltaI

/-- **`‖z‖² = ‖4β³‖`.**  The conjugation over `ℚ₂(β)` exists because `i ∉ ℚ₂(β)`, and it preserves
the spectral norm. -/
theorem evenPolish_witness_norm_sq (hdeltaI : deltaI ^ 2 = -1) (hi : deltaI ∉ KQuarticN) :
    ‖evenPolish_quarticWitness deltaI‖ ^ 2 = ‖(4 : ℚ̄₂) * evenRouteModelBeta ^ 3‖ := by
  obtain ⟨sigma, hsigma⟩ :=
    exists_conj (k := KQuarticN) (d := (-1 : ↥KQuarticN)) (by simpa using hdeltaI) hi
  have hconj : sigma (evenPolish_quarticWitness deltaI)
      = ((evenPolish_quarticX : ↥KQuarticN) : ℚ̄₂)
        - ((evenPolish_quarticY : ↥KQuarticN) : ℚ̄₂) * deltaI :=
    conj_apply hsigma _ _
  calc ‖evenPolish_quarticWitness deltaI‖ ^ 2
      = ‖evenPolish_quarticWitness deltaI‖ * ‖sigma (evenPolish_quarticWitness deltaI)‖ := by
        rw [norm_conj_eq KQuarticN sigma]; ring
    _ = ‖evenPolish_quarticWitness deltaI * sigma (evenPolish_quarticWitness deltaI)‖ := by
        rw [norm_mul]
    _ = ‖(4 : ℚ̄₂) * evenRouteModelBeta ^ 3‖ := by
        rw [hconj, evenPolish_witness_mul_conj hdeltaI, norm_neg]

/-- **`‖z‖⁸ = ‖2‖¹¹`**, an odd power of `‖2‖`. -/
theorem evenPolish_witness_norm_pow_eight (hdeltaI : deltaI ^ 2 = -1)
    (hi : deltaI ∉ KQuarticN) :
    ‖evenPolish_quarticWitness deltaI‖ ^ 8 = ‖(2 : ℚ_[2])‖ ^ 11 := by
  have hsq := evenPolish_witness_norm_sq hdeltaI hi
  have hfour : ‖(4 : ℚ̄₂)‖ = ‖(2 : ℚ_[2])‖ ^ 2 := by
    rw [show (4 : ℚ̄₂) = 2 ^ 2 by norm_num, norm_pow, GQ2.Dyadic.Fields.norm_two_alg]
  have hbeta := evenPolish_norm_beta_pow_four
  calc ‖evenPolish_quarticWitness deltaI‖ ^ 8
      = (‖evenPolish_quarticWitness deltaI‖ ^ 2) ^ 4 := by ring
    _ = (‖(4 : ℚ̄₂)‖ * ‖evenRouteModelBeta‖ ^ 3) ^ 4 := by rw [hsq, norm_mul, norm_pow]
    _ = ‖(2 : ℚ_[2])‖ ^ 8 * (‖evenRouteModelBeta‖ ^ 4) ^ 3 := by rw [hfour]; ring
    _ = ‖(2 : ℚ_[2])‖ ^ 11 := by rw [hbeta]; ring

end QuarticWitness

/-! ## §6 The quartic's ramification fact

Assembly.  `‖z‖⁸ = ‖2‖¹¹` is odd and §4 says every value on the field has `‖·‖⁸` even, so `z`'s
norm is outside the field's value group and `ℚ₂(β)(i)/ℚ₂(β)` is ramified.  The single input this
file does not prove is `i ∉ ℚ₂(β)`, without which the statement is **false** (if `i` were in the
field the two value groups would be equal by definition), so it is a hypothesis rather than a
gap. -/

section QuarticRamified

open GQ2.Dyadic.EvenRouteModel

variable {deltaI : ℚ̄₂}

/-- **`ℚ₂(β)(i)/ℚ₂(β)` IS RAMIFIED**, over the single hypothesis `i ∉ ℚ₂(β)`.  This is
`Fields.not_hasEqualNormValueGroups_quadField` at the quartic: the witness `z = (β² − 2β) +
(β² + 2)i` has `‖z‖⁸ = ‖2‖¹¹`, and §4 shows every nonzero `w` in the field has
`‖w‖⁸ = ‖N w‖²`, an even power. -/
theorem evenPolish_not_hasEqualNormValueGroups_quartic (hdeltaI : deltaI ^ 2 = -1)
    (hi : deltaI ∉ KQuarticN) :
    ¬ GQ2.HasEqualNormValueGroups KQuarticN deltaI := by
  intro H
  have h8 := evenPolish_witness_norm_pow_eight hdeltaI hi
  have hz0 : evenPolish_quarticWitness deltaI ≠ 0 := by
    intro h
    rw [h, norm_zero] at h8
    have hpos : (0 : ℝ) < ‖(2 : ℚ_[2])‖ ^ 11 := by
      have : (0 : ℝ) < ‖(2 : ℚ_[2])‖ := norm_pos_iff.mpr two_ne_zero
      positivity
    rw [← h8] at hpos
    norm_num at hpos
  obtain ⟨w, hw0, hwn⟩ := H (evenPolish_quarticWitness deltaI) hz0
    ⟨evenPolish_quarticX, evenPolish_quarticY, rfl⟩
  have hw0' : ((w : ↥KQuarticN) : ℚ̄₂) ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨c, hc0, hc⟩ := evenPolish_quartic_norm_pow_four w hw0'
  have hkey : ‖c ^ 2‖ = ‖(2 : ℚ_[2]) ^ 11‖ := by
    rw [norm_pow, norm_pow, ← hc, ← h8, hwn]
    ring
  have hval := GQ2.Dyadic.Fields.valuation_eq_of_norm_eq (pow_ne_zero 2 hc0)
    (pow_ne_zero 11 (two_ne_zero)) hkey
  rw [Padic.valuation_pow, Padic.valuation_pow, GQ2.Dyadic.Fields.valuation_two] at hval
  omega

end QuarticRamified

/-! ## §7 `i ∉ ℚ₂(β)`

The hypothesis §6 carries is elementary, and it is provable from the same value-group engine.
Suppose `i ∈ ℚ₂(β)`.  Then the field contains

`η = (β² + i(β² + 2)) / (2β)`,

which is a **primitive sixteenth root of unity**: `2η² = (β² + 2)(1 + i)` from `β⁴ + 4β² + 2 = 0`,
then `η⁴ = i` from `(β² + 2)² = 2`, then `η⁸ = −1`.  A field of degree `4` cannot contain one,
because `η − 1` would then be an element whose norm sits at level `1/8`, while §4 says every level
in `ℚ₂(β)` is a multiple of `1/4`.

The level of `η − 1` is computed without any degree theory, from the factorization

`(η − 1)(η + 1)(η² + 1)(η⁴ + 1) = η⁸ − 1 = −2`

and two ultrametric steps.  Writing `a, b, c, d` for the four factors' norms and `N = ‖2‖`:
`(η⁴ + 1)² = 2η⁴` gives `d² = N`; `(η² + 1)² = (η⁴ + 1) + 2η²` has its two summands at distinct
levels, so `c² = d`; the product gives `(ab)⁴ = N`.  Finally `a = b`, because otherwise
`‖2η‖ = ‖(η − 1) + (η + 1)‖ = max(a, b)` would force both `a, b ≤ N` and hence `(ab)⁴ ≤ N⁸ < N`.
So `a⁸ = (ab)⁴ = N`, an odd power, which §4 forbids. -/

section NoSqrtNegOne

open GQ2.Dyadic.EvenRouteModel

variable {deltaI : ℚ̄₂}

theorem evenPolish_beta_ne_zero : evenRouteModelBeta ≠ 0 := by
  intro h
  have hr := evenPolish_beta_rel
  rw [h] at hr
  norm_num at hr

/-- **The sixteenth root of unity** `η = (β² + i(β² + 2))/(2β)`, built from `β` and a square root
of `−1`.  Up to the root names it is `ζ₁₆`. -/
noncomputable def evenPolish_eta (deltaI : ℚ̄₂) : ℚ̄₂ :=
  (evenRouteModelBeta ^ 2 + deltaI * (evenRouteModelBeta ^ 2 + 2)) / (2 * evenRouteModelBeta)

theorem evenPolish_eta_spec (deltaI : ℚ̄₂) :
    2 * evenRouteModelBeta * evenPolish_eta deltaI
      = evenRouteModelBeta ^ 2 + deltaI * (evenRouteModelBeta ^ 2 + 2) := by
  have hb := evenPolish_beta_ne_zero
  rw [evenPolish_eta]
  field_simp

/-- `2η² = (β² + 2)(1 + i)`, the first stage. -/
theorem evenPolish_eta_sq (hdeltaI : deltaI ^ 2 = -1) :
    2 * evenPolish_eta deltaI ^ 2
      = (evenRouteModelBeta ^ 2 + 2) * (1 + deltaI) := by
  have hsq : (2 * evenRouteModelBeta * evenPolish_eta deltaI) ^ 2
      = (evenRouteModelBeta ^ 2 + deltaI * (evenRouteModelBeta ^ 2 + 2)) ^ 2 := by
    rw [evenPolish_eta_spec]
  have hkey : (2 * evenRouteModelBeta ^ 2) * (2 * evenPolish_eta deltaI ^ 2)
      = (2 * evenRouteModelBeta ^ 2) * ((evenRouteModelBeta ^ 2 + 2) * (1 + deltaI)) := by
    linear_combination hsq + (evenRouteModelBeta ^ 2 + 2) ^ 2 * hdeltaI
      - evenRouteModel_beta_sq_add_two_sq - evenPolish_beta_rel
  refine mul_left_cancel₀ ?_ hkey
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 evenPolish_beta_ne_zero)

/-- `η⁴ = i`, the second stage. -/
theorem evenPolish_eta_pow_four (hdeltaI : deltaI ^ 2 = -1) :
    evenPolish_eta deltaI ^ 4 = deltaI := by
  have h2 := evenPolish_eta_sq hdeltaI
  have hs := evenRouteModel_beta_sq_add_two_sq
  have hkey : (4 : ℚ̄₂) * evenPolish_eta deltaI ^ 4 = 4 * deltaI := by
    linear_combination (2 * evenPolish_eta deltaI ^ 2
      + (evenRouteModelBeta ^ 2 + 2) * (1 + deltaI)) * h2
      + (1 + deltaI) ^ 2 * hs + 2 * hdeltaI
  exact mul_left_cancel₀ (by norm_num : (4 : ℚ̄₂) ≠ 0) hkey

/-- `η⁸ = −1`: `η` is a primitive sixteenth root of unity. -/
theorem evenPolish_eta_pow_eight (hdeltaI : deltaI ^ 2 = -1) :
    evenPolish_eta deltaI ^ 8 = -1 := by
  have h4 := evenPolish_eta_pow_four hdeltaI
  calc evenPolish_eta deltaI ^ 8 = (evenPolish_eta deltaI ^ 4) ^ 2 := by ring
    _ = -1 := by rw [h4, hdeltaI]

theorem evenPolish_norm_eta (hdeltaI : deltaI ^ 2 = -1) : ‖evenPolish_eta deltaI‖ = 1 := by
  have hd : ‖deltaI‖ = 1 := by
    refine GQ2.Dyadic.Fields.eq_one_of_sq_eq_one (norm_nonneg _) ?_
    rw [← norm_pow, hdeltaI, norm_neg, norm_one]
  have h4 : ‖evenPolish_eta deltaI‖ ^ 4 = 1 := by
    rw [← norm_pow, evenPolish_eta_pow_four hdeltaI, hd]
  have h2 : ‖evenPolish_eta deltaI‖ ^ 2 = 1 :=
    GQ2.Dyadic.Fields.eq_one_of_sq_eq_one (by positivity) (by linear_combination h4)
  exact GQ2.Dyadic.Fields.eq_one_of_sq_eq_one (norm_nonneg _) h2

/-- The factorization `(η − 1)(η + 1)(η² + 1)(η⁴ + 1) = −2`. -/
theorem evenPolish_eta_factor (hdeltaI : deltaI ^ 2 = -1) :
    (evenPolish_eta deltaI - 1) * (evenPolish_eta deltaI + 1)
        * (evenPolish_eta deltaI ^ 2 + 1) * (evenPolish_eta deltaI ^ 4 + 1)
      = -2 :=
  by linear_combination evenPolish_eta_pow_eight hdeltaI

/-- **The level of `η − 1` is `1/8`**: `‖η − 1‖⁸ = ‖2‖`. -/
theorem evenPolish_norm_eta_sub_one (hdeltaI : deltaI ^ 2 = -1) :
    ‖evenPolish_eta deltaI - 1‖ ^ 8 = ‖(2 : ℚ_[2])‖ := by
  set E := evenPolish_eta deltaI with hE
  set N := ‖(2 : ℚ_[2])‖ with hN
  have hNpos : (0 : ℝ) < N := norm_pos_iff.mpr two_ne_zero
  have hNlt : N < 1 := GQ2.Dyadic.Fields.norm_two_lt_one'
  have hnE : ‖E‖ = 1 := evenPolish_norm_eta hdeltaI
  have hn2 : ‖(2 : ℚ̄₂)‖ = N := GQ2.Dyadic.Fields.norm_two_alg
  have h8 : E ^ 8 = -1 := evenPolish_eta_pow_eight hdeltaI
  -- the fourth factor
  have hd2 : ‖E ^ 4 + 1‖ ^ 2 = N := by
    rw [← norm_pow, show (E ^ 4 + 1) ^ 2 = 2 * E ^ 4 + (E ^ 8 + 1) by ring, h8]
    rw [show (2 : ℚ̄₂) * E ^ 4 + (-1 + 1) = 2 * E ^ 4 by ring, norm_mul, norm_pow, hnE, hn2]
    ring
  have hdlt : ‖E ^ 4 + 1‖ < 1 := by nlinarith [norm_nonneg (E ^ 4 + 1)]
  -- the third factor
  have hn2E : ‖(2 : ℚ̄₂) * E ^ 2‖ = N := by rw [norm_mul, norm_pow, hnE, hn2]; ring
  have hne : ‖E ^ 4 + 1‖ ≠ ‖(2 : ℚ̄₂) * E ^ 2‖ := by
    rw [hn2E]
    intro h
    nlinarith [norm_nonneg (E ^ 4 + 1)]
  have hc2 : ‖E ^ 2 + 1‖ ^ 2 = ‖E ^ 4 + 1‖ := by
    rw [← norm_pow, show (E ^ 2 + 1) ^ 2 = (E ^ 4 + 1) + 2 * E ^ 2 by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hn2E]
    exact max_eq_left (by nlinarith [norm_nonneg (E ^ 4 + 1)])
  -- the product
  have hprod : ‖E - 1‖ * ‖E + 1‖ * ‖E ^ 2 + 1‖ * ‖E ^ 4 + 1‖ = N := by
    rw [← norm_mul, ← norm_mul, ← norm_mul, evenPolish_eta_factor hdeltaI, norm_neg, hn2]
  have hab4 : (‖E - 1‖ * ‖E + 1‖) ^ 4 = N := by
    have hpow : (‖E - 1‖ * ‖E + 1‖) ^ 4 * (N * N ^ 2) = N ^ 4 := by
      have h := congrArg (fun x : ℝ => x ^ 4) hprod
      simp only [mul_pow] at h
      calc (‖E - 1‖ * ‖E + 1‖) ^ 4 * (N * N ^ 2)
          = ‖E - 1‖ ^ 4 * ‖E + 1‖ ^ 4 * ((‖E ^ 2 + 1‖ ^ 2) ^ 2 * ((‖E ^ 4 + 1‖ ^ 2) ^ 2)) := by
            rw [hc2, hd2]; ring
        _ = N ^ 4 := by rw [← h]; ring
    have hN3 : N * N ^ 2 ≠ 0 := by positivity
    have hcancel : (‖E - 1‖ * ‖E + 1‖) ^ 4 * (N * N ^ 2) = N * (N * N ^ 2) := by
      rw [hpow]; ring
    exact mul_right_cancel₀ hN3 hcancel
  -- the two outer factors have the same norm
  have hle1 : ‖E - 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max E (-1 : ℚ̄₂)
    simpa [hnE, sub_eq_add_neg] using this
  have hle2 : ‖E + 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max E (1 : ℚ̄₂)
    simpa [hnE] using this
  have heq : ‖E - 1‖ = ‖E + 1‖ := by
    by_contra hne'
    have hsum : ‖(E - 1) + (E + 1)‖ = max ‖E - 1‖ ‖E + 1‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne'
    have h2E : ‖(E - 1) + (E + 1)‖ = N := by
      rw [show (E - 1) + (E + 1) = 2 * E by ring, norm_mul, hnE, hn2]; ring
    rw [h2E] at hsum
    have ha : ‖E - 1‖ ≤ N := hsum ▸ le_max_left _ _
    have hb : ‖E + 1‖ ≤ N := hsum ▸ le_max_right _ _
    have hab0 : (0 : ℝ) ≤ ‖E - 1‖ * ‖E + 1‖ := by positivity
    have hle : ‖E - 1‖ * ‖E + 1‖ ≤ N := by
      have h1 : ‖E - 1‖ * ‖E + 1‖ ≤ N * N :=
        mul_le_mul ha hb (norm_nonneg _) hNpos.le
      nlinarith [h1, hNpos, hNlt]
    have h4le : (‖E - 1‖ * ‖E + 1‖) ^ 4 ≤ N ^ 4 := by gcongr
    have hN3 : N ^ 3 < 1 := by nlinarith [hNpos, hNlt, mul_pos hNpos hNpos]
    have hN4 : N ^ 4 < N := by nlinarith [hN3, hNpos]
    rw [hab4] at h4le
    linarith
  calc ‖E - 1‖ ^ 8 = (‖E - 1‖ * ‖E + 1‖) ^ 4 := by rw [← heq]; ring
    _ = N := hab4

/-- **`i ∉ ℚ₂(β)`.**  If it were, the field would contain the primitive sixteenth root of unity
`η`, and `η − 1` would sit at level `1/8`; but §4 puts every level of `ℚ₂(β)` in `(1/4)ℤ`. -/
theorem evenPolish_notMem_quartic (hdeltaI : deltaI ^ 2 = -1) :
    deltaI ∉ KQuarticN := by
  intro hmem
  have hetamem : evenPolish_eta deltaI ∈ KQuarticN := by
    rw [evenPolish_eta]
    exact div_mem
      (add_mem (pow_mem evenRouteModelBeta_mem 2)
        (mul_mem hmem (add_mem (pow_mem evenRouteModelBeta_mem 2) evenPolish_two_mem_quartic)))
      (mul_mem evenPolish_two_mem_quartic evenRouteModelBeta_mem)
  have hsubmem : evenPolish_eta deltaI - 1 ∈ KQuarticN := sub_mem hetamem (one_mem _)
  have h8 := evenPolish_norm_eta_sub_one hdeltaI
  have hne0 : evenPolish_eta deltaI - 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at h8
    have : (0 : ℝ) < ‖(2 : ℚ_[2])‖ := norm_pos_iff.mpr two_ne_zero
    rw [← h8] at this
    norm_num at this
  obtain ⟨c, hc0, hc⟩ :=
    evenPolish_quartic_norm_pow_four ⟨evenPolish_eta deltaI - 1, hsubmem⟩ hne0
  have hkey : ‖c ^ 2‖ = ‖(2 : ℚ_[2]) ^ 1‖ := by
    rw [norm_pow, norm_pow, ← hc, ← h8]
    ring
  have hval := GQ2.Dyadic.Fields.valuation_eq_of_norm_eq (pow_ne_zero 2 hc0)
    (pow_ne_zero 1 two_ne_zero) hkey
  rw [Padic.valuation_pow, Padic.valuation_pow, GQ2.Dyadic.Fields.valuation_two] at hval
  omega

/-- **`ℚ₂(β)(i)/ℚ₂(β)` IS RAMIFIED, UNCONDITIONALLY.**  The ramification binder the tree has never
carried for the quartic model field, discharged: `not_hasEqualNormValueGroups_KQuarticN`. -/
theorem evenPolish_not_hasEqualNormValueGroups_KQuarticN (deltaI : ℚ̄₂)
    (hdeltaI : deltaI ^ 2 = -1) :
    ¬ GQ2.HasEqualNormValueGroups KQuarticN deltaI :=
  evenPolish_not_hasEqualNormValueGroups_quartic hdeltaI (evenPolish_notMem_quartic hdeltaI)

end NoSqrtNegOne

end GQ2.Dyadic.EvenRangePolish

/-! ## §9 Axiom pins

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

-- §4 to §6 the quartic
#print axioms evenPolish_norm_betaGen
#print axioms evenPolish_norm_beta_pow_four
#print axioms evenPolish_quartic_norm_pow_four
#print axioms evenPolish_witness_mul_conj
#print axioms evenPolish_witness_norm_sq
#print axioms evenPolish_witness_norm_pow_eight
#print axioms evenPolish_not_hasEqualNormValueGroups_quartic

-- §7 the sixteenth root of unity and the ramification fact, unconditional
#print axioms evenPolish_eta_sq
#print axioms evenPolish_eta_pow_eight
#print axioms evenPolish_norm_eta_sub_one
#print axioms evenPolish_notMem_quartic
#print axioms evenPolish_not_hasEqualNormValueGroups_KQuarticN

-- the quadratic row's ramification fact, the statement §6 mirrors
#print axioms GQ2.Dyadic.Fields.not_hasEqualNormValueGroups_quadField

-- the wave-67 originals they replace, for the side-by-side
#print axioms GQ2.Dyadic.EvenRangeModel.hrangeFinal_sqrtTwo
#print axioms GQ2.Dyadic.EvenRangeModel.hrangeFinal_orientedEquivM_sqrtTwo
#print axioms GQ2.Dyadic.EvenRangeModel.hrangeFinal_orientedEquivN_sqrtNegTwo

end AxiomPins
