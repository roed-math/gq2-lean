/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMFlexibleModelNoGo
import GQ2.Dyadic.Instances.FieldFamilyCanonicalAssemblyNoGo
import GQ2.Dyadic.Instances.FieldFamilySelectionRangeFinal
import GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm

/-!
# The obstructed selected even-M branch requires a new source family

W343 showed that replacing a compact-M source by an equivalent model cannot evade the
distinguished-`C` pivot.  This module applies that structural no-go directly to the canonical
field selector.

If the selector chooses `.M0 2` at odd residue degree, then no `FlexibleModelSourceRN`
equivalent to the standard compact-M candidate can exist.  Moreover, the selector lies in the
strict handle-pivot alternative and therefore has positive handle count.  Thus the remaining
general repair is neither a rank-four exception nor another presentation of the standard
candidate: it must be a genuinely new, uniformly handle-supported source/reconstruction family.
-/

namespace GQ2.Dyadic.Instances.EvenMFlexibleSelectorNoGo

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.EvenMFlexibleModelNoGo
open GQ2.Dyadic.Instances.M0FieldPivotParityNoGo
open GQ2.Dyadic.Instances.MFieldMobilePivotBoundary
open GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary
open GQ2.Dyadic.Instances.FieldFamilyFlexibleModelAssembly
open GQ2.Dyadic.Instances.FieldFlexibleEvenMFinal
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Words.MCompact

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- The obstructed selected compact-M branch admits no corrected model source equivalent to
the standard candidate group. -/
theorem not_flexibleModelSourceRN_m0_two_odd_residue
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (hf : Odd FF.f)
    (hbranch :
      (selectFieldBranchFamilyFromRange B FF D RI).branch = .M0 2) :
    let h := handleCount D.params (.M0 2)
    ¬ Nonempty (FlexibleModelSourceRN (2 + 2 * h) (qOf K FF) (mCompactW 2 h)
      (maxProPQuotient 2 (GalK K)) isProP_maxProPQuotient
      (fieldCoreNuZtwo B) (standardNumerics (2 + 2 * h))) := by
  dsimp only
  rintro ⟨F⟩
  let S := selectFieldBranchFamilyFromRange B FF D RI
  obtain ⟨e0⟩ := orientedEquivM_of_familySelection_of_matchesRange_m0 B FF S
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI) hbranch
  have hpivot : MFieldCPivotAtLevel B 2 0 (handleCount D.params (.M0 2)) :=
    mCompact_flexibleModelSource_forces_cPivot B FF (by omega) e0 F
  exact not_m0FieldPivotUnit_two_of_familySelection_odd_residue B FF hf S hbranch
    ((mFieldCPivotAtLevel_zero_iff_m0FieldPivotUnit B).mp hpivot)

/-- The obstructed selected branch lies in the strict handle normal form. -/
theorem strictHandlePivot_m0_two_odd_residue
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (hf : Odd FF.f)
    (hbranch :
      (selectFieldBranchFamilyFromRange B FF D RI).branch = .M0 2) :
    MFieldStrictNormalizedHandlePivotAtLevel B 2 0
      (handleCount D.params (.M0 2)) := by
  let S := selectFieldBranchFamilyFromRange B FF D RI
  have H := evenCanonicalOrStrictHandleBoundary_of_familySelection B FF S
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI)
  rw [EvenCanonicalOrStrictHandleBoundary, hbranch] at H
  exact H.resolve_left fun hpivot =>
    not_m0FieldPivotUnit_two_of_familySelection_odd_residue B FF hf S hbranch
      ((mFieldCPivotAtLevel_zero_iff_m0FieldPivotUnit B).mp hpivot)

/-- In particular, the obstructed selected branch is genuinely handle-supported. -/
theorem handleCount_pos_m0_two_odd_residue
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (hf : Odd FF.f)
    (hbranch :
      (selectFieldBranchFamilyFromRange B FF D RI).branch = .M0 2) :
    0 < handleCount D.params (.M0 2) := by
  obtain ⟨e, j, hU, hV, qC, hC⟩ :=
    strictHandlePivot_m0_two_odd_residue B FF D RI hf hbranch
  exact Fin.pos_iff_nonempty.mpr ⟨j⟩

#print axioms not_flexibleModelSourceRN_m0_two_odd_residue
#print axioms strictHandlePivot_m0_two_odd_residue
#print axioms handleCount_pos_m0_two_odd_residue

end

end GQ2.Dyadic.Instances.EvenMFlexibleSelectorNoGo
