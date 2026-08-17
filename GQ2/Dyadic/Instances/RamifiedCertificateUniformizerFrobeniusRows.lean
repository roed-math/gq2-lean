/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateTameUniformizerQurRow

/-!
# The natural Frobenius rows at a reciprocity uniformizer

W193 replaces the opaque full abstract `Zhat` normalization by its natural geometric-Frobenius
row in `QurQ`.  This module does the same on the field side.  Every Galois lift of the chosen
reciprocity uniformizer must act on the absolute residue field by the `f`-th power of arithmetic
square Frobenius.

The normalized equivalence `absoluteResidueGalEquivZhat` proves that this action statement is
exactly `AbsoluteResidueUniformizerNormalization`.  Together with W193's quotient row, it feeds
the existing unit/uniformizer split and produces the signed relative Frobenius compatibility.
Thus both remaining uniformizer inputs now have direct quotient/action formulations, independent
of arbitrary coordinate choices.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K}
  {FF : DyadicUnitFiltration K}

/-- Every lift of the reciprocity uniformizer acts by the expected arithmetic Frobenius. -/
def AbsoluteResidueUniformizerFrobeniusRow (B : MarkedRecip R K)
    (FF : DyadicUnitFiltration K) : Prop :=
  ∀ g : GalK K,
    toAbK K g = B.recip (uniformizerK K FF) →
      absoluteResidueAlgAction (subtypeAnc (GalKsub K) g) =
        absoluteResidueFrobenius ^ FF.f

/-- The natural residue-action row is exactly the full absolute `Zhat` normalization. -/
theorem absoluteResidueUniformizerNormalization_iff_frobeniusRow :
    AbsoluteResidueUniformizerNormalization B FF ↔
      AbsoluteResidueUniformizerFrobeniusRow B FF := by
  constructor
  · intro hnorm g hg
    apply absoluteResidueGalEquivZhat.injective
    rw [map_pow, absoluteResidueGalEquivZhat_frobenius]
    change absoluteResidueCoordinateK (K := K) g = _
    rw [← absoluteResidueCoordinateKAb_toAbK, hg, hnorm]
    simpa [zpow_natCast] using (Zhat.ofInt_one_zpow (FF.f : ℤ)).symm
  · intro hrow
    rw [AbsoluteResidueUniformizerNormalization]
    obtain ⟨g, hg⟩ := surjective_toAbK K
      (B.recip (uniformizerK K FF))
    rw [← hg, absoluteResidueCoordinateKAb_toAbK]
    change absoluteResidueGalEquivZhat
      (absoluteResidueAlgAction (subtypeAnc (GalKsub K) g)) = _
    rw [hrow g hg, map_pow, absoluteResidueGalEquivZhat_frobenius]
    simpa [zpow_natCast] using Zhat.ofInt_one_zpow (FF.f : ℤ)

/-- The two natural Frobenius rows imply the signed relative Frobenius comparison. -/
theorem orientedAbsoluteResidueFrobeniusCompatibility_of_uniformizerRows
    (T : OrientedTameQuotientK B FF)
    (Hunit : TameUnitInertiaRefinement B FF T)
    (Hfull : OrientedFullTameInertiaLiesInAbsoluteInertiaAt T)
    (habs : AbsoluteResidueUniformizerFrobeniusRow B FF)
    (htame : AbstractTameUniformizerQurRow T) :
    OrientedAbsoluteResidueFrobeniusCompatibility T :=
  orientedAbsoluteResidueFrobeniusCompatibility_of_normalizations
    T Hunit Hfull
      (absoluteResidueUniformizerNormalization_iff_frobeniusRow.mpr habs)
      ((abstractTameUniformizerNormalization_iff_qurRow T).mpr htame)

#print axioms AbsoluteResidueUniformizerFrobeniusRow
#print axioms absoluteResidueUniformizerNormalization_iff_frobeniusRow
#print axioms orientedAbsoluteResidueFrobeniusCompatibility_of_uniformizerRows

end
end GQ2.Dyadic
