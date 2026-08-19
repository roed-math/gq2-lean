/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldHandleNormalBoundary

/-!
# The strict general M handle normal form

The normalized handle alternative from W311 can be sharpened whenever the canonical C pivot
is absent.  The level condition makes C divisible by `2^r`; failure of exactness makes its
quotient even, hence C is divisible by `2^(r+1)`.

Thus the single remaining even-family case has the strict form: a chosen U row is exactly
`2^r`, its paired V row is zero, and C lies one full level deeper.  The final dispatcher in
this module shows that supplying the corrected residual only for this strict form closes every
selected family row.  No degree or nilpotency class is fixed.
-/

namespace GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.MFieldHandlePivotNormalForm
open GQ2.Dyadic.Instances.MFieldHandleNormalBoundary
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily
open GQ2.Dyadic.Instances.M0FamilyField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- If C is level-r divisible but is not an exact level-r pivot, it is divisible one level
deeper. -/
theorem exists_deeper_C_of_not_exactPivot
    {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu)
    (hC : ¬ ∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmC alpha h)) = (gamma : ℤ_[2]) * 2 ^ r) :
    ∃ qC : ℤ_[2], toAdd (nu (dmC alpha h)) = 2 ^ (r + 1) * qC := by
  obtain ⟨qC, hqC⟩ := hlev (dmC alpha h) (chiM_dmC alpha h)
  have hnunit : ¬ IsUnit qC := by
    intro hunit
    apply hC
    refine ⟨hunit.unit, ?_⟩
    rw [hqC, hunit.unit_spec]
    ring
  have hpar : mParityZ qC = 0 := by
    by_contra h
    apply hnunit
    apply mIsUnit_of_parity_one
    revert h
    generalize mParityZ qC = z
    revert z
    decide
  obtain ⟨y, hy⟩ := (mParityZ_eq_zero_iff qC).mp hpar
  refine ⟨y, ?_⟩
  rw [hqC, hy, pow_succ]
  ring

/-- The strict alternate M normal form: U is the exact pivot, V vanishes, and C lies one
level deeper. -/
def StrictNormalizedMHandlePivotAtLevel {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2])) : Prop :=
  ∃ j : Fin h,
    toAdd (nu (dmGen alpha h (handleIdxU j))) = 2 ^ r ∧
      nu (dmGen alpha h (handleIdxV j)) = 1 ∧
      ∃ qC : ℤ_[2], toAdd (nu (dmC alpha h)) = 2 ^ (r + 1) * qC

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Field-side strict handle normal form. -/
def MFieldStrictNormalizedHandlePivotAtLevel (B : MarkedRecip R K)
    (alpha r h : ℕ) : Prop :=
  ∃ e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)),
    StrictNormalizedMHandlePivotAtLevel (r := r) (m0Transport B e)

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
/-- A normalized handle pivot becomes strict whenever the canonical C alternative is absent. -/
theorem mFieldStrictNormalizedHandlePivotAtLevel_of_not_cPivot
    (B : MarkedRecip R K) {alpha r h : ℕ} (hr : B.r = r)
    (hnotC : ¬ MFieldCPivotAtLevel B alpha r h)
    (H : MFieldNormalizedHandlePivotAtLevel B alpha r h) :
    MFieldStrictNormalizedHandlePivotAtLevel B alpha r h := by
  obtain ⟨e, j, hU, hV⟩ := H
  let nu := m0Transport B e
  have hlev := chiKerLevel_of_level B hr e
  change MpcChiKerLevelH alpha r h nu at hlev
  have hnotCe : ¬ ∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmC alpha h)) = (gamma : ℤ_[2]) * 2 ^ r := by
    intro h
    exact hnotC ⟨e, h⟩
  obtain ⟨qC, hC⟩ := exists_deeper_C_of_not_exactPivot nu hlev hnotCe
  refine ⟨e, j, ?_, ?_, qC, hC⟩
  · exact hU
  · exact hV

/-- The exact selected-family boundary: canonical C, or the strict normalized handle form. -/
def EvenCanonicalOrStrictHandleBoundary (B : MarkedRecip R K)
    {P : FieldParameters} {FF : DyadicUnitFiltration K}
    {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  match S.branch with
  | .M0 alpha =>
      MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) ∨
        MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha))
  | .Mpc alpha r false eta =>
      MFieldCPivotAtLevel B alpha r (handleCount P (.Mpc alpha r false eta)) ∨
        MFieldStrictNormalizedHandlePivotAtLevel B alpha r
          (handleCount P (.Mpc alpha r false eta))
  | _ => True

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2] in
/-- Every selected family row satisfies the strict canonical-or-handle boundary. -/
theorem evenCanonicalOrStrictHandleBoundary_of_familySelection
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange) :
    EvenCanonicalOrStrictHandleBoundary B S := by
  have H := evenCanonicalOrNormalizedHandleBoundary_of_familySelection B FF S hmatch
  generalize hbranch : S.branch = branch
  cases branch with
  | L => simp [EvenCanonicalOrStrictHandleBoundary, hbranch]
  | N0 alpha => simp [EvenCanonicalOrStrictHandleBoundary, hbranch]
  | Npc alpha r eta => simp [EvenCanonicalOrStrictHandleBoundary, hbranch]
  | M0 alpha =>
      rw [EvenCanonicalOrNormalizedHandleBoundary, hbranch] at H
      rw [EvenCanonicalOrStrictHandleBoundary, hbranch]
      by_cases hC : MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha))
      · exact Or.inl hC
      · apply Or.inr
        have hr : B.r = 0 := by
          have hs := S.level_eq
          rw [hbranch] at hs
          exact hs.symm
        exact mFieldStrictNormalizedHandlePivotAtLevel_of_not_cPivot B hr hC
          (H.resolve_left hC)
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [EvenCanonicalOrNormalizedHandleBoundary, hbranch] at H
          rw [EvenCanonicalOrStrictHandleBoundary, hbranch]
          by_cases hC : MFieldCPivotAtLevel B alpha r
              (handleCount P (.Mpc alpha r false eta))
          · exact Or.inl hC
          · apply Or.inr
            have hr : B.r = r := by
              have hs := S.level_eq
              rw [hbranch] at hs
              exact hs.symm
            exact mFieldStrictNormalizedHandlePivotAtLevel_of_not_cPivot B hr hC
              (H.resolve_left hC)
      | true => simp [EvenCanonicalOrStrictHandleBoundary, hbranch]

/-- The sharpened remaining supply asks only for the strict handle form, where C is known to
lie one level deeper. -/
def StrictNormalizedMHandleResidualSupply (B : MarkedRecip R K)
    (FF : DyadicUnitFiltration K) : Prop :=
  (∀ {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
      (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
      (_hmatch : W.MatchesCyclotomicRange) {alpha : ℕ}
      (_hbranch : S.branch = .M0 alpha),
      MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) →
        HasSelectedRowResidualRN B FF S) ∧
  ∀ {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
      (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
      (_hmatch : W.MatchesCyclotomicRange) {alpha r : ℕ} {eta : ℤ_[2]ˣ}
      (_hbranch : S.branch = .Mpc alpha r false eta),
      MFieldStrictNormalizedHandlePivotAtLevel B alpha r
          (handleCount P (.Mpc alpha r false eta)) →
        HasSelectedRowResidualRN B FF S

/-- The strict handle supply closes the all-degree selected family. -/
theorem hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_strictHandleSupply
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (H : StrictNormalizedMHandleResidualSupply B FF) :
    HasSelectedRowResidualRN B FF
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  let S := selectFieldBranchFamilyFromRange B FF D RI
  have hmatch := fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI
  have hboundary := evenCanonicalOrStrictHandleBoundary_of_familySelection
    B FF S hmatch
  generalize hbranch : S.branch = branch
  cases branch with
  | L => exact hasSelectedRowResidualRN_l B FF D S hbranch
  | N0 alpha => exact hasSelectedRowResidualRN_n0 B FF S hmatch hbranch
  | Npc alpha r eta => exact hasSelectedRowResidualRN_npc B FF S hmatch hbranch
  | M0 alpha =>
      rw [EvenCanonicalOrStrictHandleBoundary, hbranch] at hboundary
      rcases hboundary with hC | hH
      · exact hasSelectedRowResidualRN_m0_of_cPivot B FF S hbranch hC
      · exact H.1 S hmatch hbranch hH
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [EvenCanonicalOrStrictHandleBoundary, hbranch] at hboundary
          rcases hboundary with hC | hH
          · exact hasSelectedRowResidualRN_mpc_of_cPivot B FF S hbranch hC
          · exact H.2 S hmatch hbranch hH
      | true =>
          exact hasSelectedRowResidualRN_mpc_of_cPivot B FF S hbranch
            (mFieldCPivotAtLevel_mpc_true B FF S hmatch hbranch)

#print axioms exists_deeper_C_of_not_exactPivot
#print axioms StrictNormalizedMHandlePivotAtLevel
#print axioms MFieldStrictNormalizedHandlePivotAtLevel
#print axioms mFieldStrictNormalizedHandlePivotAtLevel_of_not_cPivot
#print axioms EvenCanonicalOrStrictHandleBoundary
#print axioms evenCanonicalOrStrictHandleBoundary_of_familySelection
#print axioms StrictNormalizedMHandleResidualSupply
#print axioms hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_strictHandleSupply

end

end GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm
