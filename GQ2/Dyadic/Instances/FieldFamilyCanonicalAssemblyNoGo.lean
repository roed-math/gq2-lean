/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact
import GQ2.Dyadic.Instances.M0FieldPivotParityNoGo

/-!
# The unchanged canonical general assembly is not universally viable

W322 reduced the general selected-family assembly to the absence of a canonical M-pivot
placement defect.  This module proves that the defect really occurs: on a selected depth-two
compact-M row over a field of odd residue degree, parity and the Hilbert/norm criterion force
the distinguished `C` pivot to vanish, while the intrinsic mobile pivot still exists.

Consequently neither a corrected residual nor the final assembly can exist for the unchanged
canonical presentation in that arithmetic pattern, even after all compatible ramified field
data have been supplied.  This is a uniform obstruction for every handle count, not a
nilpotency-class calculation.  A universal general theorem must therefore change the M normal
form so that it can use the intrinsic mobile pivot, rather than continue trying to prove the
false canonical-C condition.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyCanonicalAssemblyNoGo

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact
open GQ2.Dyadic.Instances.FieldFamilyPlacementDefectExact
open GQ2.Dyadic.Instances.M0FieldPivotParityNoGo
open GQ2.Dyadic.Instances.MFieldMobilePivotBoundary

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Odd residue degree makes the canonical pivot-placement defect unavoidable on a selected
depth-two compact-M row. -/
theorem canonicalPivotPlacementDefect_of_m0_two_odd_residue
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (hf : Odd FF.f)
    (hbranch :
      (selectFieldBranchFamilyFromRange B FF D RI).branch = .M0 2) :
    CanonicalPivotPlacementDefectBoundary B
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  let S := selectFieldBranchFamilyFromRange B FF D RI
  have Hmobile := canonicalMobilePivotBoundary_fieldSelectionFromRange B FF D RI
  have hmobile : MFieldMobilePivotAtLevel B 2 0
      (handleCount D.params (.M0 2)) := by
    rw [CanonicalMobilePivotBoundary, hbranch] at Hmobile
    exact Hmobile
  have hnotPivot : ¬ MFieldCPivotAtLevel B 2 0
      (handleCount D.params (.M0 2)) := by
    intro hpivot
    exact not_m0FieldPivotUnit_two_of_familySelection_odd_residue
      B FF hf S hbranch
      ((mFieldCPivotAtLevel_zero_iff_m0FieldPivotUnit B).mp hpivot)
  rw [CanonicalPivotPlacementDefectBoundary, hbranch]
  exact ⟨hmobile, hnotPivot⟩

/-- The current canonical selected row has no corrected-RN residual in the obstructed
arithmetic pattern. -/
theorem not_hasSelectedRowResidualRN_m0_two_odd_residue
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (hf : Odd FF.f)
    (hbranch :
      (selectFieldBranchFamilyFromRange B FF D RI).branch = .M0 2) :
    ¬ HasSelectedRowResidualRN B FF
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  rw [hasSelectedRowResidualRN_fieldSelectionFromRange_iff_not_placementDefect]
  exact not_not_intro
    (canonicalPivotPlacementDefect_of_m0_two_odd_residue B FF D RI hf hbranch)

/-- Even after the compatible field packet has been supplied, the unchanged canonical
selected assembly is impossible in the obstructed arithmetic pattern. -/
theorem not_hasSelectedAssemblyRN_m0_two_odd_residue
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (F : GenAsmCompatibleFieldInputs B FF
      (selectedPresentation (selectFieldBranchFamilyFromRange B FF D RI)).degree)
    (hf : Odd FF.f)
    (hbranch :
      (selectFieldBranchFamilyFromRange B FF D RI).branch = .M0 2) :
    ¬ HasSelectedAssemblyRN B FF
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  rw [hasSelectedAssemblyRN_fieldSelectionFromRange_iff_not_placementDefect
    B FF D RI F]
  exact not_not_intro
    (canonicalPivotPlacementDefect_of_m0_two_odd_residue B FF D RI hf hbranch)

#print axioms canonicalPivotPlacementDefect_of_m0_two_odd_residue
#print axioms not_hasSelectedRowResidualRN_m0_two_odd_residue
#print axioms not_hasSelectedAssemblyRN_m0_two_odd_residue

end

end GQ2.Dyadic.Instances.FieldFamilyCanonicalAssemblyNoGo
