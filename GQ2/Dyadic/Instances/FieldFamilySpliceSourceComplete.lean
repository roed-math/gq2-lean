/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMSelectedSpliceComplete
import GQ2.Dyadic.Instances.MFieldMobilePivotBoundary
import GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact

/-!
# All selected families have a complete flexible source

The new pair/mobile splice certificates eliminate the canonical M-placement
obstruction at the honest changed-word interface.  The old L and N certificates
are retained.  Every range-matching selection has a complete field-tied source
at exactly the selected degree, with no remaining source analytic or pivot
placement premise.  This does not assert the old frozen M word is correct.

This assembly intentionally uses the established field orientation and canonical
certificate producers, so its axiom footprint includes their inherited arithmetic
inputs.  The separate compatibility-aware field packet is not silently assumed.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceSourceComplete

noncomputable section

open GQ2 GQ2.Dyadic
open Instances.EvenMSelectedSpliceComplete Instances.FieldFamilyCampaignBoundary
open Instances.FieldFamilyFlexibleAssembly Instances.FieldFamilyGeneralAssemblyExact
open Instances.MFieldStrictHandleNormalForm Instances.M0FamilyField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Complete flexible source coverage in every degree and every selected family. -/
theorem hasSelectedFlexibleRowResidualRN_of_matchesRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF)
    {W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange) : HasSelectedFlexibleRowResidualRN B FF S := by
  cases hb : S.branch with
  | L =>
      exact hasSelectedFlexibleRowResidualRN_of_canonical B FF S
        (hasSelectedRowResidualRN_l B FF D S hb)
  | N0 alpha =>
      exact hasSelectedFlexibleRowResidualRN_of_canonical B FF S
        (hasSelectedRowResidualRN_n0 B FF S hmatch hb)
  | Npc alpha r eta =>
      exact hasSelectedFlexibleRowResidualRN_of_canonical B FF S
        (hasSelectedRowResidualRN_npc B FF S hmatch hb)
  | M0 alpha =>
      have H := evenCanonicalOrStrictHandleBoundary_of_familySelection B FF S hmatch
      rw [EvenCanonicalOrStrictHandleBoundary, hb] at H
      exact hasSelectedFlexibleRowResidualRN_m0_of_boundary B FF S hb H
        (hasSelectedRowResidualRN_m0_of_cPivot B FF S hb)
  | Mpc alpha r epsilon eta =>
      obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_mpc B FF S hmatch hb
      exact hasSelectedFlexibleRowResidualRN_mpc_oriented B FF S hb e

/-- The actual range-based field selector has a complete flexible source, unconditionally
relative to the established field bundles. -/
theorem hasSelectedFlexibleRowResidualRN_fieldSelectionFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    HasSelectedFlexibleRowResidualRN B FF (selectFieldBranchFamilyFromRange B FF D RI) :=
  hasSelectedFlexibleRowResidualRN_of_matchesRange B FF D
    (selectFieldBranchFamilyFromRange B FF D RI)
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI)

/-- A selected-degree source, its actual certificate, and its actual field equivalence.
The source word is carried by the existential witness, not identified with a frozen word. -/
def HasSelectedFlexibleAssemblyRN (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  ∃ G : GenAsmFlexibleBranch K B, G.degree = S.semantic.degree ∧
    Nonempty (GenAsmFlexibleRowResidualRN FF G) ∧
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K))

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- Only the separate shared field packet remains after general source closure. -/
theorem hasSelectedFlexibleAssemblyRN_of_residual
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (F : GenAsmCompatibleFieldInputs B FF S.semantic.degree)
    (H : HasSelectedFlexibleRowResidualRN B FF S) : HasSelectedFlexibleAssemblyRN B FF S := by
  obtain ⟨G, hdegree, ⟨cert⟩⟩ := H
  let FG : GenAsmCompatibleFieldInputs B FF G.degree := hdegree.symm ▸ F
  exact ⟨G, hdegree, ⟨cert⟩, genAsmFlexible_candidate_equiv_galKRN_compatible G FG cert⟩

/-- The complete all-degree selected flexible assembly, with the field packet explicit. -/
theorem hasSelectedFlexibleAssemblyRN_fieldSelectionFromRange_of_fieldInputs
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (F : GenAsmCompatibleFieldInputs B FF
      (selectFieldBranchFamilyFromRange B FF D RI).semantic.degree) :
    HasSelectedFlexibleAssemblyRN B FF (selectFieldBranchFamilyFromRange B FF D RI) :=
  hasSelectedFlexibleAssemblyRN_of_residual B FF _ F
    (hasSelectedFlexibleRowResidualRN_fieldSelectionFromRange B FF D RI)

#print axioms hasSelectedFlexibleRowResidualRN_of_matchesRange
#print axioms hasSelectedFlexibleRowResidualRN_fieldSelectionFromRange
#print axioms HasSelectedFlexibleAssemblyRN
#print axioms hasSelectedFlexibleAssemblyRN_of_residual
#print axioms hasSelectedFlexibleAssemblyRN_fieldSelectionFromRange_of_fieldInputs

end
end GQ2.Dyadic.Instances.FieldFamilySpliceSourceComplete
