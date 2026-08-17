/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateRelativeFrobeniusUnitSplit

/-!
# The remaining relative Frobenius uniformizer normalization

Once abstract reciprocity units land in full tame inertia and full tame inertia lies in canonical
absolute inertia, the unit half of the W189 comparison is automatic.  This module proves that the
entire signed relative Frobenius equation is then equivalent to its one uniformizer row.

The row follows from the two expected normalizations: the actual residue coordinate sends the
chosen local uniformizer to arithmetic `2^f`-Frobenius, represented by `Zhat.ofInt f`, while the
abstract tame coordinate sends it to geometric Frobenius, represented by `Zhat.ofInt (-1)`.
Their signs and the residue-degree exponent combine exactly.

AX4 already determines the maximal pro-`2` projection of the abstract normalization.  It does not
determine its prime-to-`2` coordinates, and the current local-reciprocity packet does not state the
actual full `Zhat` normalization.  These are the exact surviving uniformizer inputs.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K}
  {FF : DyadicUnitFiltration K}

/-- The actual residue coordinate sends a local uniformizer to arithmetic `2^f`-Frobenius. -/
def AbsoluteResidueUniformizerNormalization (B : MarkedRecip R K)
    (FF : DyadicUnitFiltration K) : Prop :=
  absoluteResidueCoordinateKAb (K := K)
      (B.recip (uniformizerK K FF)) = Zhat.ofInt (FF.f : ℤ)

/-- The full abstract tame coordinate sends a reciprocity uniformizer to geometric Frobenius. -/
def AbstractTameUniformizerNormalization
    (T : OrientedTameQuotientK B FF) : Prop :=
  orientedTameQurCoordinateKAb T
      (B.recip (uniformizerK K FF)) = Zhat.ofInt (-1)

theorem relativeFrobeniusUniformizerRow_of_normalizations
    (T : OrientedTameQuotientK B FF)
    (habs : AbsoluteResidueUniformizerNormalization B FF)
    (htame : AbstractTameUniformizerNormalization T) :
    RelativeFrobeniusUniformizerRow T := by
  rw [RelativeFrobeniusUniformizerRow, habs, htame]
  calc
    Zhat.ofInt (FF.f : ℤ) = (Zhat.ofInt 1) ^ (FF.f : ℤ) :=
      (Zhat.ofInt_one_zpow (FF.f : ℤ)).symm
    _ = ((Zhat.ofInt 1) ^ (-1 : ℤ)) ^ (-(FF.f : ℤ)) := by
      rw [← zpow_mul]
      congr 1
      ring
    _ = (Zhat.ofInt (-1)) ^ (-(FF.f : ℤ)) := by
      rw [Zhat.ofInt_one_zpow]

/-- AX4 already determines the pro-`2` shadow of the abstract uniformizer normalization. -/
theorem maxProPMk_orientedTameQurCoordinateKAb_recip_uniformizer
    (T : OrientedTameQuotientK B FF) :
    maxProPMk 2 Zhat
        (orientedTameQurCoordinateKAb T
          (B.recip (uniformizerK K FF))) = ztwoOne⁻¹ := by
  obtain ⟨g, hg⟩ := surjective_toAbK K
    (B.recip (uniformizerK K FF))
  rw [← hg, orientedTameQurCoordinateKAb_toAbK,
    maxProPMk_qurQEquivZhat_qMkQ]
  exact T.nuT_recip_uniformizer g hg

theorem absoluteResidueUnitInertia_of_tame_full_inertia
    (T : OrientedTameQuotientK B FF)
    (Hunit : TameUnitInertiaRefinement B FF T)
    (Hfull : OrientedFullTameInertiaLiesInAbsoluteInertiaAt T) :
    AbsoluteResidueUnitInertia B := by
  intro u g hu hg
  change subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup
  exact Hfull g (Hunit u g hu hg)

theorem orientedAbsoluteResidueFrobeniusCompatibility_iff_uniformizer
    (T : OrientedTameQuotientK B FF)
    (Hunit : TameUnitInertiaRefinement B FF T)
    (Hfull : OrientedFullTameInertiaLiesInAbsoluteInertiaAt T) :
    OrientedAbsoluteResidueFrobeniusCompatibility T ↔
      RelativeFrobeniusUniformizerRow T := by
  rw [orientedAbsoluteResidueFrobeniusCompatibility_iff_unit_uniformizer
    T Hunit]
  exact and_iff_right (absoluteResidueUnitInertia_of_tame_full_inertia
    T Hunit Hfull)

theorem orientedAbsoluteResidueFrobeniusCompatibility_of_normalizations
    (T : OrientedTameQuotientK B FF)
    (Hunit : TameUnitInertiaRefinement B FF T)
    (Hfull : OrientedFullTameInertiaLiesInAbsoluteInertiaAt T)
    (habs : AbsoluteResidueUniformizerNormalization B FF)
    (htame : AbstractTameUniformizerNormalization T) :
    OrientedAbsoluteResidueFrobeniusCompatibility T :=
  (orientedAbsoluteResidueFrobeniusCompatibility_iff_uniformizer
    T Hunit Hfull).mpr
      (relativeFrobeniusUniformizerRow_of_normalizations T habs htame)

#print axioms AbsoluteResidueUniformizerNormalization
#print axioms AbstractTameUniformizerNormalization
#print axioms relativeFrobeniusUniformizerRow_of_normalizations
#print axioms maxProPMk_orientedTameQurCoordinateKAb_recip_uniformizer
#print axioms absoluteResidueUnitInertia_of_tame_full_inertia
#print axioms orientedAbsoluteResidueFrobeniusCompatibility_iff_uniformizer
#print axioms orientedAbsoluteResidueFrobeniusCompatibility_of_normalizations

end
end GQ2.Dyadic
