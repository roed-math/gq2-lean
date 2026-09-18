/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAnchoredInertiaField
import GQ2.Dyadic.Instances.RamifiedCertificateRelativeOddCyclotomic

/-!
# Norm values in actual inertia-fixed extensions

Finite odd cyclotomic extensions are unramified over every finite dyadic base. Combined with
the exact inertia fixed-field description, this proves that every actual inertia-fixed element
has a norm partner in the base. The resulting anchored equal-value and relative-unramified
packets require only actual-to-full-tame inertia compatibility, not relative norm reciprocity
or the relative unit-index theorem. Over an odd-degree base the existing parity argument then
supplies the involution norm-value packet used by the determinant.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Actual relative inertia-fixed elements have values already represented in the base.
This is proved through finite odd cyclotomic containment, without relative class field theory. -/
theorem exists_same_norm_mem_base_of_inertia_fixed
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (FK : DyadicUnitFiltration K) {x : ℚ̄₂} (hx0 : x ≠ 0)
    (hx : x ∈ IntermediateField.fixedField
      (absoluteInertiaSubgroup ⊓ K.fixingSubgroup)) :
    ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ K ∧ ‖x‖ = ‖y‖ := by
  obtain ⟨m, ζ, hm, hζ, hxζ⟩ := exists_odd_primitive_root_of_inertia_fixed K hx
  exact exists_same_norm_mem_base_of_mem_odd_cyclotomic K FK m hm ζ hζ hx0 hxζ

/-- An actual-inertia-fixed finite extension has relative ramification index one. -/
theorem relE_eq_one_of_absoluteInertia_le_fixingSubgroup
    (K L : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (FK : DyadicUnitFiltration K) (FL : DyadicUnitFiltration L) (hKL : K ≤ L)
    (hI : absoluteInertiaSubgroup ⊓ K.fixingSubgroup ≤ L.fixingSubgroup) :
    GaloisCosetNorm.relE FK FL hKL = 1 := by
  have hdvd : GaloisCosetNorm.relE FK FL hKL ∣ (1 : ℤ) :=
    GaloisCosetNorm.relE_dvd FK FL hKL (n := 1) (by
      intro x hx0 hxL
      have hx : x ∈ IntermediateField.fixedField
          (absoluteInertiaSubgroup ⊓ K.fixingSubgroup) := by
        apply IntermediateField.fixedField_le hI
        rwa [InfiniteGalois.fixedField_fixingSubgroup]
      obtain ⟨y, hy0, hyK, hnorm⟩ := exists_same_norm_mem_base_of_inertia_fixed K FK hx0 hx
      exact ⟨y, hy0, hyK, by simpa only [pow_one] using hnorm⟩)
  have hpos := GaloisCosetNorm.relE_pos FK FL hKL
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · exact h
  · omega

/-- Actual inertia mapping into full tame inertia suffices for every compatible anchored
tame-inertia field to have the same spectral value group as the base. -/
theorem anchoredTameInertiaEqualNormValuesAt_of_actualInertia
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (hinertia : ∀ g : ↑(GalKsub K),
      subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup →
        tame g ∈ inertiaPartQ P.qK) :
    AnchoredTameInertiaEqualNormValuesAt P K tame := by
  intro D _ _ _ _ V _ _ c rho hfac _ x hx0 hx
  exact exists_same_norm_mem_base_of_inertia_fixed K FK hx0
    (anchoredTameInertiaField_le_actualInertiaFixedField P K tame hinertia c rho hfac hx)

/-- The corresponding compatible prescribed-field ramification statement, with no relative
norm-reciprocity premise. -/
theorem anchoredTameInertiaRelativeUnramifiedDataAt_of_actualInertia
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (hinertia : ∀ g : ↑(GalKsub K),
      subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup →
        tame g ∈ inertiaPartQ P.qK) :
    AnchoredTameInertiaRelativeUnramifiedDataAt P K FK tame :=
  (anchoredTameInertiaRelativeUnramifiedDataAt_iff_equalNormValues P K FK tame).mpr
    (anchoredTameInertiaEqualNormValuesAt_of_actualInertia P K FK tame hinertia)

/-- Over an odd-degree base this gives the involution norm-value packet used by the ramified
determinant. The input is actual/full tame inertia compatibility, not finite-layer CFT. -/
theorem anchoredInvolutionEqualNormValueGroupsAt_of_actualInertia
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (htame : Function.Surjective tame) (hodd : Odd (Module.finrank ℚ_[2] K))
    (hinertia : ∀ g : ↑(GalKsub K),
      subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup →
        tame g ∈ inertiaPartQ P.qK) :
    AnchoredInvolutionEqualNormValueGroupsAt P (GalKsub K) tame :=
  anchoredInvolutionEqualNormValueGroupsAt_of_prescribedTameUnramified P K FK tame htame hodd
    (anchoredTameInertiaRelativeUnramifiedDataAt_of_actualInertia P K FK tame hinertia)

#print axioms exists_same_norm_mem_base_of_inertia_fixed
#print axioms relE_eq_one_of_absoluteInertia_le_fixingSubgroup
#print axioms anchoredTameInertiaEqualNormValuesAt_of_actualInertia
#print axioms anchoredTameInertiaRelativeUnramifiedDataAt_of_actualInertia
#print axioms anchoredInvolutionEqualNormValueGroupsAt_of_actualInertia
end
end GQ2.Dyadic

