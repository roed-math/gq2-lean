/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MStrictHandleResidualNoGo

/-!
# The exact corrected-RN boundary for the selected field family

For the range-matching field selector, the existence of a corrected RN row residual
is equivalent to `EvenCanonicalMarkingBoundary`.  Thus the complete selected-family
problem has one exact boundary predicate: it is trivial on the already closed rows,
and records precisely the distinguished-C pivot on the remaining compact-M rows.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyCampaignExactBoundary

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.MStrictHandleResidualNoGo

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [T2Space (GalK K)] in
theorem evenCanonicalMarkingBoundary_of_hasSelectedRowResidualRN
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    (H : HasSelectedRowResidualRN B FF S) :
    EvenCanonicalMarkingBoundary B S := by
  generalize hbranch : S.branch = branch
  cases branch with
  | L => rw [EvenCanonicalMarkingBoundary, hbranch]; trivial
  | N0 alpha => rw [EvenCanonicalMarkingBoundary, hbranch]; trivial
  | Npc alpha r eta => rw [EvenCanonicalMarkingBoundary, hbranch]; trivial
  | M0 alpha =>
      rw [EvenCanonicalMarkingBoundary, hbranch]
      exact mFieldCPivotAtLevel_m0_of_hasSelectedRowResidualRN
        B FF S hmatch hbranch H
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [EvenCanonicalMarkingBoundary, hbranch]
          exact mFieldCPivotAtLevel_mpc_of_hasSelectedRowResidualRN
            B FF S hmatch hbranch H
      | true => rw [EvenCanonicalMarkingBoundary, hbranch]; trivial

theorem hasSelectedRowResidualRN_fieldSelectionFromRange_iff_boundary
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    HasSelectedRowResidualRN B FF
        (selectFieldBranchFamilyFromRange B FF D RI) ↔
      EvenCanonicalMarkingBoundary B
        (selectFieldBranchFamilyFromRange B FF D RI) := by
  constructor
  · exact evenCanonicalMarkingBoundary_of_hasSelectedRowResidualRN
      B FF (selectFieldBranchFamilyFromRange B FF D RI)
        (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI)
  · exact hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_boundary
      B FF D RI

#print axioms evenCanonicalMarkingBoundary_of_hasSelectedRowResidualRN
#print axioms hasSelectedRowResidualRN_fieldSelectionFromRange_iff_boundary

end

end GQ2.Dyadic.Instances.FieldFamilyCampaignExactBoundary
