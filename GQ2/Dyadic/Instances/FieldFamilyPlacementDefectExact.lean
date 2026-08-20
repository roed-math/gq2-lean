/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilyCampaignExactBoundary
import GQ2.Dyadic.Instances.MFieldMobilePivotBoundary

/-!
# The selected-family obstruction is exactly M-pivot placement

Every range-matching selected M row already has an exact mobile pivot.  Combining that fact
with the exact corrected-RN boundary shows that the remaining obstruction is neither pivot
existence nor a list of degree cases: it is precisely failure to place that intrinsic pivot on
the distinguished `C` coordinate of the canonical compact-M presentation.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyPlacementDefectExact

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.FieldFamilyCampaignExactBoundary
open GQ2.Dyadic.Instances.MFieldMobilePivotBoundary

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The exact obstruction left after the intrinsic mobile pivot has been constructed. -/
def CanonicalPivotPlacementDefectBoundary (B : MarkedRecip R K)
    {P : FieldParameters} {FF : DyadicUnitFiltration K}
    {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  match S.branch with
  | .M0 alpha =>
      MFieldPivotPlacementDefect B alpha 0 (handleCount P (.M0 alpha))
  | .Mpc alpha r false eta =>
      MFieldPivotPlacementDefect B alpha r
        (handleCount P (.Mpc alpha r false eta))
  | _ => False

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
theorem evenCanonicalMarkingBoundary_iff_not_placementDefect
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (Hmobile : CanonicalMobilePivotBoundary B S) :
    EvenCanonicalMarkingBoundary B S ↔
      ¬ CanonicalPivotPlacementDefectBoundary B S := by
  generalize hbranch : S.branch = branch
  cases branch with
  | L => simp [EvenCanonicalMarkingBoundary,
      CanonicalPivotPlacementDefectBoundary, hbranch]
  | N0 alpha => simp [EvenCanonicalMarkingBoundary,
      CanonicalPivotPlacementDefectBoundary, hbranch]
  | Npc alpha r eta => simp [EvenCanonicalMarkingBoundary,
      CanonicalPivotPlacementDefectBoundary, hbranch]
  | M0 alpha =>
      rw [CanonicalMobilePivotBoundary, hbranch] at Hmobile
      rw [EvenCanonicalMarkingBoundary, CanonicalPivotPlacementDefectBoundary,
        hbranch]
      exact mFieldCPivotAtLevel_iff_not_placementDefect B Hmobile
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [CanonicalMobilePivotBoundary, hbranch] at Hmobile
          rw [EvenCanonicalMarkingBoundary,
            CanonicalPivotPlacementDefectBoundary, hbranch]
          exact mFieldCPivotAtLevel_iff_not_placementDefect B Hmobile
      | true => simp [EvenCanonicalMarkingBoundary,
          CanonicalPivotPlacementDefectBoundary, hbranch]

/-- On the canonical range selection, a corrected residual exists exactly when the mobile
pivot has no canonical placement defect. -/
theorem hasSelectedRowResidualRN_fieldSelectionFromRange_iff_not_placementDefect
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    HasSelectedRowResidualRN B FF
        (selectFieldBranchFamilyFromRange B FF D RI) ↔
      ¬ CanonicalPivotPlacementDefectBoundary B
        (selectFieldBranchFamilyFromRange B FF D RI) := by
  rw [hasSelectedRowResidualRN_fieldSelectionFromRange_iff_boundary]
  exact evenCanonicalMarkingBoundary_iff_not_placementDefect B FF _
    (canonicalMobilePivotBoundary_fieldSelectionFromRange B FF D RI)

#print axioms CanonicalPivotPlacementDefectBoundary
#print axioms evenCanonicalMarkingBoundary_iff_not_placementDefect
#print axioms hasSelectedRowResidualRN_fieldSelectionFromRange_iff_not_placementDefect

end

end GQ2.Dyadic.Instances.FieldFamilyPlacementDefectExact
