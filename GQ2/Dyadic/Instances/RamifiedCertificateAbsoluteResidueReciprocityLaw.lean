/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateUniformizerFrobeniusRows
import GQ2.Dyadic.MultiplicativeDecomposition

/-!
# The absolute-residue local reciprocity law

W194 identifies the field-side uniformizer input as an action by the expected power of square
Frobenius.  The unit and uniformizer clauses are the two rows of one canonical statement: if
`x` has valuation `n`, then every lift of `rec_K(x)` acts on the absolute residue field by the
`f*n`-th power of square Frobenius.

`absoluteResidueLocalReciprocityLaw_iff_rows` proves that this law is exactly the conjunction of
the landed unit-inertia condition and the W194 uniformizer row.  When it is combined with the
abstract geometric row in `QurQ`, the signed relative Frobenius comparison follows without a
separate full-inertia hypothesis.  Full tame inertia is then carried into actual inertia as a
consequence of that comparison.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K}
  {FF : DyadicUnitFiltration K}

/-- The natural local-reciprocity law on the absolute residue field. -/
def AbsoluteResidueLocalReciprocityLaw (B : MarkedRecip R K)
    (FF : DyadicUnitFiltration K) : Prop :=
  ∀ (x : (↥K)ˣ) (g : GalK K),
    toAbK K g = B.recip x →
      absoluteResidueAlgAction (subtypeAnc (GalKsub K) g) =
        absoluteResidueFrobenius ^
          ((FF.f : ℤ) * dyadicValuation FF x)

omit [FiniteDimensional ℚ_[2] K] in
theorem dyadicValuation_eq_zero_of_norm_eq_one (x : (↥K)ˣ)
    (hx : ‖((x : ↥K) : ℚ̄₂)‖ = 1) :
    dyadicValuation FF x = 0 := by
  apply dyadicValuation_eq_of_norm_eq_zpow FF x 0
  simpa using hx

omit [FiniteDimensional ℚ_[2] K] in
theorem dyadicValuation_uniformizerK :
    dyadicValuation FF (uniformizerK K FF) = 1 := by
  apply dyadicValuation_eq_of_norm_eq_zpow FF _ 1
  simp [uniformizerK_coe]

/-- The full field reciprocity law is exactly its unit and uniformizer rows. -/
theorem absoluteResidueLocalReciprocityLaw_iff_rows :
    AbsoluteResidueLocalReciprocityLaw B FF ↔
      AbsoluteResidueUnitInertia B ∧
        AbsoluteResidueUniformizerFrobeniusRow B FF := by
  constructor
  · intro H
    constructor
    · intro u g hu hg
      change subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup
      rw [← absoluteResidueAlgAction_ker]
      have h := H u g hg
      rw [dyadicValuation_eq_zero_of_norm_eq_one u hu, mul_zero, zpow_zero] at h
      exact h
    · intro g hg
      have h := H (uniformizerK K FF) g hg
      rw [dyadicValuation_uniformizerK, mul_one, zpow_natCast] at h
      exact h
  · rintro ⟨Hunit, Hpi⟩ x g hg
    apply absoluteResidueGalEquivZhat.injective
    change absoluteResidueCoordinateK (K := K) g = _
    rw [← absoluteResidueCoordinateKAb_toAbK, hg]
    obtain ⟨u, n, hx, hu⟩ := exists_unit_zpow_decomp K FF x
    have hval : dyadicValuation FF x = n := by
      apply dyadicValuation_eq_of_norm_eq_zpow FF x n
      rw [hx]
      simp only [Units.val_mul]
      push_cast
      rw [uniformizerK_val_zpow_coe, norm_mul, norm_zpow, hu, one_mul]
    rw [hval, hx, map_mul, map_zpow, map_mul, map_zpow]
    have Hu := (absoluteResidueUnitInertia_iff_reciprocity.mp Hunit) u hu
    have Hpi' :=
      absoluteResidueUniformizerNormalization_iff_frobeniusRow.mpr Hpi
    rw [Hu, Hpi', one_mul, map_zpow, absoluteResidueGalEquivZhat_frobenius]
    rw [← Zhat.ofInt_one_zpow, ← zpow_mul]

/-- The natural field reciprocity law and the abstract geometric row imply the full signed
relative Frobenius comparison.  No separate full-inertia premise remains. -/
theorem orientedAbsoluteResidueFrobeniusCompatibility_of_localReciprocityLaw
    (T : OrientedTameQuotientK B FF)
    (Hunit : TameUnitInertiaRefinement B FF T)
    (Habs : AbsoluteResidueLocalReciprocityLaw B FF)
    (Htame : AbstractTameUniformizerQurRow T) :
    OrientedAbsoluteResidueFrobeniusCompatibility T := by
  rw [orientedAbsoluteResidueFrobeniusCompatibility_iff_unit_uniformizer T Hunit]
  exact ⟨(absoluteResidueLocalReciprocityLaw_iff_rows.mp Habs).1,
    relativeFrobeniusUniformizerRow_of_normalizations T
      (absoluteResidueUniformizerNormalization_iff_frobeniusRow.mpr
        (absoluteResidueLocalReciprocityLaw_iff_rows.mp Habs).2)
      ((abstractTameUniformizerNormalization_iff_qurRow T).mpr Htame)⟩

#print axioms AbsoluteResidueLocalReciprocityLaw
#print axioms dyadicValuation_eq_zero_of_norm_eq_one
#print axioms dyadicValuation_uniformizerK
#print axioms absoluteResidueLocalReciprocityLaw_iff_rows
#print axioms orientedAbsoluteResidueFrobeniusCompatibility_of_localReciprocityLaw

end
end GQ2.Dyadic
