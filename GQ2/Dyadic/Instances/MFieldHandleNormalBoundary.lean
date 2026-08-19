/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldHandlePivotNormalForm

/-!
# The common normalized-handle boundary for the M family

This module packages the all-degree consequence of the mobile-pivot dichotomies and the handle
normal form.  Every range-matching selection already has its corrected RN residual except for
one uniform alternate case: the exact pivot is the U row of a chosen handle, its paired V row
is zero, and the C row is unchanged.

`NormalizedMHandleResidualSupply` is the exact remaining supply interface.  Its two clauses
distinguish only the compact and positive-level words; they use the same handle normal form.
Once that supply is constructed, the final theorem closes every branch selected from the
field's actual cyclotomic range, without any nilpotency-class enumeration.
-/

namespace GQ2.Dyadic.Instances.MFieldHandleNormalBoundary

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.MFieldMobileHandleDichotomy
open GQ2.Dyadic.Instances.MFieldPositiveHandleDichotomy
open GQ2.Dyadic.Instances.MFieldHandlePivotNormalForm

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The exact common boundary after normalizing the mobile M pivot. -/
def EvenCanonicalOrNormalizedHandleBoundary (B : MarkedRecip R K)
    {P : FieldParameters} {FF : DyadicUnitFiltration K}
    {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  match S.branch with
  | .M0 alpha =>
      MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) ∨
        MFieldNormalizedHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha))
  | .Mpc alpha r false eta =>
      MFieldCPivotAtLevel B alpha r (handleCount P (.Mpc alpha r false eta)) ∨
        MFieldNormalizedHandlePivotAtLevel B alpha r
          (handleCount P (.Mpc alpha r false eta))
  | _ => True

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
/-- Every range-matching family selection satisfies the canonical-or-normalized-handle
boundary, uniformly in the degree and level. -/
theorem evenCanonicalOrNormalizedHandleBoundary_of_familySelection
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange) :
    EvenCanonicalOrNormalizedHandleBoundary B S := by
  generalize hbranch : S.branch = branch
  cases branch with
  | L => simp [EvenCanonicalOrNormalizedHandleBoundary, hbranch]
  | N0 alpha => simp [EvenCanonicalOrNormalizedHandleBoundary, hbranch]
  | Npc alpha r eta => simp [EvenCanonicalOrNormalizedHandleBoundary, hbranch]
  | M0 alpha =>
      rw [EvenCanonicalOrNormalizedHandleBoundary, hbranch]
      rcases m0_cPivot_or_handlePivot_of_familySelection B FF S hmatch hbranch with
        hC | hH
      · exact Or.inl hC
      · apply Or.inr
        have hr : B.r = 0 := by
          have hs := S.level_eq
          rw [hbranch] at hs
          exact hs.symm
        exact mFieldNormalizedHandlePivotAtLevel_of_handlePivot B hr hH
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [EvenCanonicalOrNormalizedHandleBoundary, hbranch]
          rcases mpcFalse_cPivot_or_handlePivot_of_familySelection
            B FF S hmatch hbranch with hC | hH
          · exact Or.inl hC
          · apply Or.inr
            have hr : B.r = r := by
              have hs := S.level_eq
              rw [hbranch] at hs
              exact hs.symm
            exact mFieldNormalizedHandlePivotAtLevel_of_handlePivot B hr hH
      | true => simp [EvenCanonicalOrNormalizedHandleBoundary, hbranch]

/-- The sole remaining even-family supply: a normalized handle pivot must yield the selected
corrected row.  The definition has two clauses only because the selected word is compact M at
level zero and procyclic M at positive level; the handle normal form itself is common. -/
def NormalizedMHandleResidualSupply (B : MarkedRecip R K)
    (FF : DyadicUnitFiltration K) : Prop :=
  (∀ {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
      (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
      (_hmatch : W.MatchesCyclotomicRange) {alpha : ℕ}
      (_hbranch : S.branch = .M0 alpha),
      MFieldNormalizedHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) →
        HasSelectedRowResidualRN B FF S) ∧
  ∀ {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
      (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
      (_hmatch : W.MatchesCyclotomicRange) {alpha r : ℕ} {eta : ℤ_[2]ˣ}
      (_hbranch : S.branch = .Mpc alpha r false eta),
      MFieldNormalizedHandlePivotAtLevel B alpha r
          (handleCount P (.Mpc alpha r false eta)) →
        HasSelectedRowResidualRN B FF S

/-- Once the single normalized-handle supply is known, every selected family row has its
corrected RN residual. -/
theorem hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_normalizedHandleSupply
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (H : NormalizedMHandleResidualSupply B FF) :
    HasSelectedRowResidualRN B FF
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  let S := selectFieldBranchFamilyFromRange B FF D RI
  have hmatch := fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI
  have hboundary := evenCanonicalOrNormalizedHandleBoundary_of_familySelection
    B FF S hmatch
  generalize hbranch : S.branch = branch
  cases branch with
  | L => exact hasSelectedRowResidualRN_l B FF D S hbranch
  | N0 alpha => exact hasSelectedRowResidualRN_n0 B FF S hmatch hbranch
  | Npc alpha r eta => exact hasSelectedRowResidualRN_npc B FF S hmatch hbranch
  | M0 alpha =>
      rw [EvenCanonicalOrNormalizedHandleBoundary, hbranch] at hboundary
      rcases hboundary with hC | hH
      · exact hasSelectedRowResidualRN_m0_of_cPivot B FF S hbranch hC
      · exact H.1 S hmatch hbranch hH
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [EvenCanonicalOrNormalizedHandleBoundary, hbranch] at hboundary
          rcases hboundary with hC | hH
          · exact hasSelectedRowResidualRN_mpc_of_cPivot B FF S hbranch hC
          · exact H.2 S hmatch hbranch hH
      | true =>
          exact hasSelectedRowResidualRN_mpc_of_cPivot B FF S hbranch
            (mFieldCPivotAtLevel_mpc_true B FF S hmatch hbranch)

#print axioms EvenCanonicalOrNormalizedHandleBoundary
#print axioms evenCanonicalOrNormalizedHandleBoundary_of_familySelection
#print axioms NormalizedMHandleResidualSupply
#print axioms hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_normalizedHandleSupply

end

end GQ2.Dyadic.Instances.MFieldHandleNormalBoundary
