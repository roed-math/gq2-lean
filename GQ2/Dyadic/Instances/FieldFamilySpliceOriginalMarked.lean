/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWordFinal
import GQ2.Foundations.TauCetiInstance

/-!
# Exact selected word with its original core-character witness retained

This additive packaging keeps the source branch G *before* realization
calibration, its exact selected-word profile, its actual certificate, and the
same `AlignedMarkedFieldEquiv G ...` in one existential witness. Consequently
the cyclotomic equation is visibly against G's original realization, while the
pro-two equations use the induced realization carried by `M.branch`.

No new marking proof is made here. The existing source producer and marked
reconstruction are composed without forgetting the original branch. This
does not assert pointwise preservation of an arbitrary externally prescribed
core realization or equality to an arbitrarily prescribed selected handle.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked
noncomputable section

open GQ2 GQ2.Dyadic
open Instances.FieldFamilyFlexibleAssembly Instances.FieldFamilyGeneralAssemblyExact
open Instances.FieldFamilySpliceFinal Instances.FieldFamilySpliceMarkedFinal
open Instances.FieldFamilySpliceSelectedWord

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section FieldInputs

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- One pre-calibration selected source, its whole certificate, and one equivalence
with the ORIGINAL cyclotomic marking. The induced realization is available through
`AlignedMarkedFieldEquiv.branch`; it keeps this same word, core, nu and certificate. -/
def HasSelectedOriginalMarkedWordPresentationRN
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  ∃ G : GenAsmFlexibleBranch K B,
    G.degree = S.semantic.degree ∧ SelectedWordProfile FF S G ∧
    ∃ cert : GenAsmFlexibleRowResidualRN FF G,
      Nonempty (AlignedMarkedFieldEquiv G cert.cand T)

/-- Supplied-bundle endpoint retaining exact constructor provenance and original
core-character compatibility simultaneously. It introduces no new analytic premise. -/
theorem hasSelectedOriginalMarkedWordPresentationRN_of_matchesRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    (RI : RamifiedIData K)
    {W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange) :
    HasSelectedOriginalMarkedWordPresentationRN B FF T S := by
  obtain ⟨G, hdegree, hp, ⟨cert⟩⟩ := hasSelectedWordCertificate_of_matchesRange B FF D S hmatch
  exact ⟨G, hdegree, hp, cert, nonempty_alignedMarkedFieldEquiv G cert.cand
    (genAsmCompatibleFieldInputs_of_norm_reciprocity B FF T D G.hdeg) D RI⟩

/-- The actual field range selector discharges every selected-profile premise. -/
theorem hasSelectedOriginalMarkedWordPresentationRN_fieldSelectionFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    (RI : RamifiedIData K) :
    HasSelectedOriginalMarkedWordPresentationRN B FF T
      (selectFieldBranchFamilyFromRange B FF D RI) :=
  hasSelectedOriginalMarkedWordPresentationRN_of_matchesRange B FF T D RI _
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI)

end FieldInputs

section Canonical

private instance compact_abs : CompactSpace AbsGalQ2 := by
  change CompactSpace (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)
  infer_instance

private instance td_abs : TotallyDisconnectedSpace AbsGalQ2 := by
  change TotallyDisconnectedSpace (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)
  infer_instance

private instance t2_abs : T2Space AbsGalQ2 := by
  change T2Space (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)
  infer_instance

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

private instance compact_galK : CompactSpace (GalK K) :=
  isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_of_isOpen _ (isOpen_fixingSubgroup K)).isCompact

private instance t2_galK : T2Space (GalK K) :=
  inferInstanceAs (T2Space ↥(K.fixingSubgroup))

private instance td_galK : TotallyDisconnectedSpace (GalK K) :=
  inferInstanceAs (TotallyDisconnectedSpace ↥(K.fixingSubgroup))

/-- Canonical filtration and finite parameters, retaining supplied reciprocity/tame bundles. -/
theorem hasSelectedOriginalMarkedWordPresentationRN_canonicalParameters
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (T : OrientedTameQuotientK B (dyadicUnitFiltration K)) (RI : RamifiedIData K) :
    HasSelectedOriginalMarkedWordPresentationRN B (dyadicUnitFiltration K) T
      (selectFieldBranchFamilyFromRange B (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) RI) :=
  hasSelectedOriginalMarkedWordPresentationRN_fieldSelectionFromRange B
    (dyadicUnitFiltration K) T (canonicalFiniteDyadicParameters K) RI

/-- Bare finite-field endpoint: exact selected source provenance and the original
core-character witness are retained together, in the standing ramified-i scope. -/
theorem hasSelectedOriginalMarkedWordPresentationRN_ramifiedI
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (RI : RamifiedIData K) :
    HasSelectedOriginalMarkedWordPresentationRN (markedRecipAt K) (dyadicUnitFiltration K)
      (orientedTameQuotientAt K (dyadicUnitFiltration K))
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) RI) :=
  hasSelectedOriginalMarkedWordPresentationRN_canonicalParameters (markedRecipAt K)
    (orientedTameQuotientAt K (dyadicUnitFiltration K)) RI

/-- Odd degree supplies RI through the existing uniform obstruction. -/
theorem hasSelectedOriginalMarkedWordPresentationRN_oddDegree
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    HasSelectedOriginalMarkedWordPresentationRN (markedRecipAt K) (dyadicUnitFiltration K)
      (orientedTameQuotientAt K (dyadicUnitFiltration K))
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) (ramifiedIData_of_odd_finrank K hodd)) :=
  hasSelectedOriginalMarkedWordPresentationRN_ramifiedI K (ramifiedIData_of_odd_finrank K hodd)

end Canonical

#print axioms HasSelectedOriginalMarkedWordPresentationRN
#print axioms hasSelectedOriginalMarkedWordPresentationRN_of_matchesRange
#print axioms hasSelectedOriginalMarkedWordPresentationRN_fieldSelectionFromRange
#print axioms hasSelectedOriginalMarkedWordPresentationRN_canonicalParameters
#print axioms hasSelectedOriginalMarkedWordPresentationRN_ramifiedI
#print axioms hasSelectedOriginalMarkedWordPresentationRN_oddDegree

end
end GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked
