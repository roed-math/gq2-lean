/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceSourceComplete
import GQ2.Dyadic.Instances.RamifiedCertificateCanonicalFieldData

/-!
# The general ramified-i selected flexible presentation

The all-family source closure and the canonical shared field packet now assemble
without an additional analytic, pivot-placement, or reciprocity-comparison premise.
The theorem covers every degree in the campaign's original ramified-i scope.

The actual source word is part of the existential branch witness.  In the M families
it may be the uniform tame splice, not the old frozen canonical word.  The final
equivalence concerns exactly this carried word, whose complete corrected certificate
and marked pro-2 core realization are retained.

This is a closure relative to the established field-theoretic axiom baseline, not a
claim that the entire local-field presentation theorem uses only Lean's standard axioms.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceFinal

noncomputable section
open GQ2 GQ2.Dyadic
open Instances.FieldFamilyGeneralAssemblyExact
open Instances.FieldFamilySpliceSourceComplete

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The complete shared field packet is constructed from the existing field bundles.
No signed full Frobenius law or extra relative reciprocity hypothesis is supplied. -/
def genAsmCompatibleFieldInputs_of_norm_reciprocity
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    {n : ℕ} (hdeg : Module.finrank ℚ_[2] K = n) :
    GenAsmCompatibleFieldInputs B FF n where
  T := T
  params := D.params
  params_n := D.degree_eq.trans hdeg
  params_qK := D.qK_eq_qOf
  ramifiedData := compatibleRamifiedDataAt_of_norm_reciprocity T D.params D.qK_eq_qOf

/-- All degrees and all five selected families have a complete changed-source
presentation of the actual absolute Galois group in the ramified-i setting. -/
theorem hasSelectedFlexibleAssemblyRN_fieldSelectionFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    (RI : RamifiedIData K) :
    HasSelectedFlexibleAssemblyRN B FF (selectFieldBranchFamilyFromRange B FF D RI) := by
  let S := selectFieldBranchFamilyFromRange B FF D RI
  exact hasSelectedFlexibleAssemblyRN_fieldSelectionFromRange_of_fieldInputs B FF D RI
    (genAsmCompatibleFieldInputs_of_norm_reciprocity B FF T D S.degree_eq_field.symm)

#print axioms genAsmCompatibleFieldInputs_of_norm_reciprocity
#print axioms hasSelectedFlexibleAssemblyRN_fieldSelectionFromRange

end
end GQ2.Dyadic.Instances.FieldFamilySpliceFinal
