/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldCanonicalOrientationBoundary
import GQ2.Dyadic.Instances.MFieldMobilePivotBoundary
import GQ2.Dyadic.MarkedCore.MFrameExists

/-!
# The general M mobile-pivot dichotomy

This module locates the intrinsic M-family kernel pivot uniformly in the handle count.  If a
`Ztwo` marking takes a unit value somewhere on `ker chiM`, then either its distinguished `C`
row is a unit or one of its standard handle rows is a unit.  The proof uses the full general-h
abelian frame: chi-triviality makes the B coefficient even and kills the D coefficient, while
the relator makes the A row even.

Thus every family-selected M0 row has an honest dichotomy: the current canonical normal form
applies, or the mobile pivot is handle-supported.  This identifies a uniform alternate-normal-
form target and does not split by nilpotency class.
-/

namespace GQ2.Dyadic.Instances.MFieldMobileHandleDichotomy

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.SectionThree
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism
open GQ2.Dyadic.Instances.M0FamilyField
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open scoped GQ2.SectionThree.TopAbInstances

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

private theorem parity_sum {I : Type*} [Fintype I] (f : I → ℤ_[2]) :
    mParityZ (∑ i, f i) = ∑ i, mParityZ (f i) := by
  classical
  have hs : ∀ s : Finset I, mParityZ (∑ i ∈ s, f i) = ∑ i ∈ s, mParityZ (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [mParityZ_add, ih]
  exact hs Finset.univ

private theorem toAdd_prod {I : Type*} [Fintype I] (f : I → Multiplicative ℤ_[2]) :
    toAdd (∏ i, f i) = ∑ i, toAdd (f i) := by
  classical
  have hs : ∀ s : Finset I, toAdd (∏ i ∈ s, f i) = ∑ i ∈ s, toAdd (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [toAdd_mul, ih]
  exact hs Finset.univ

private theorem parity_eq_zero_of_not_isUnit {a : ℤ_[2]} (ha : ¬ IsUnit a) :
    mParityZ a = 0 := by
  by_contra h
  apply ha
  apply mIsUnit_of_parity_one
  revert h
  generalize mParityZ a = z
  revert z
  decide

/-- A unit value on the cyclotomic kernel of a general M core occurs either on the
distinguished C coordinate or on one of the handle coordinates. -/
theorem isUnit_C_or_handle_of_chiKer
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (nu' : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hker : MChiKerUnimodular alpha h nu') :
    IsUnit (toAdd (nu' (dmC alpha h))) ∨
      (∃ j : Fin h, IsUnit (toAdd (nu' (dmGen alpha h (handleIdxU j))))) ∨
      ∃ j : Fin h, IsUnit (toAdd (nu' (dmGen alpha h (handleIdxV j)))) := by
  classical
  by_cases hC : IsUnit (toAdd (nu' (dmC alpha h)))
  · exact Or.inl hC
  by_cases hU : ∃ j : Fin h, IsUnit (toAdd (nu' (dmGen alpha h (handleIdxU j))))
  · exact Or.inr (Or.inl hU)
  by_cases hV : ∃ j : Fin h, IsUnit (toAdd (nu' (dmGen alpha h (handleIdxV j))))
  · exact Or.inr (Or.inr hV)
  exfalso
  push Not at hU hV
  obtain ⟨x, hxchi, hxunit⟩ := hker
  obtain ⟨c, hc⟩ := mDMab_coord alpha h (abMk x)
  have hframe :
      mFrameApiChiModel alpha h
          (mPhiHom (by omega : 1 ≤ alpha) h (abMk x)) = 1 := by
    rw [← chiM_eq_mPhiHom (by omega : 1 ≤ alpha), hxchi]
  rw [hc, mPhiHom_word, mFrameApiChiModel_ofAdd] at hframe
  have hrow : mParityZ (c 1) = 0 ∧ c 3 = 0 := by
    apply mChi_row_extract halpha
    simpa [zpowZtwo_zero] using hframe
  have hnuWord :
      toAdd (nu' x) = ∑ i, c i * toAdd (nu' (dmGen alpha h i)) := by
    rw [← abLiftG_abMk nu' x, hc, mAbWord, map_prod, toAdd_prod]
    apply Finset.sum_congr rfl
    intro i hi
    rw [toAdd_map_zpowZtwo, abLiftG_abMk]
  have hA : toAdd (nu' (dmGen alpha h 0)) =
      -(2 ^ (alpha - 1) * toAdd (nu' (dmGen alpha h 2))) := by
    simpa only [nuFrame_apply] using
      (mChar_frameZero (α := alpha) (h := h) (by omega : 1 ≤ alpha) nu')
  have hterm : ∀ i : Fin (coreRank h),
      mParityZ (c i * toAdd (nu' (dmGen alpha h i))) = 0 := by
    intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · calc
        mParityZ (c 0 * toAdd (nu' (dmGen alpha h 0))) =
            mParityZ (-((c 0 * toAdd (nu' (dmGen alpha h 2))) *
              2 ^ (alpha - 1))) := by rw [hA]; congr 1; ring
        _ = mParityZ ((c 0 * toAdd (nu' (dmGen alpha h 2))) *
              2 ^ (alpha - 1)) := mParityZ_neg _
        _ = 0 := mParityZ_mul_two_pow halpha _
    · rw [mParityZ_mul, hrow.1, zero_mul]
    · rw [mParityZ_mul]
      change mParityZ (c 2) * mParityZ (toAdd (nu' (dmC alpha h))) = 0
      rw [parity_eq_zero_of_not_isUnit hC, mul_zero]
    · rw [hrow.2, zero_mul, mParityZ_zero]
    · rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [mHandleIdx_coordU, mParityZ_mul,
          parity_eq_zero_of_not_isUnit (hU j), mul_zero]
      · rw [mHandleIdx_coordV, mParityZ_mul,
          parity_eq_zero_of_not_isUnit (hV j), mul_zero]
  have hpar := mParityZ_of_isUnit hxunit
  rw [hnuWord, parity_sum] at hpar
  have hzero : (∑ i, mParityZ (c i * toAdd (nu' (dmGen alpha h i)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hterm i
  rw [hzero] at hpar
  exact zero_ne_one hpar

/-- A field-side exact-level value on one of the standard M handle coordinates. -/
def MFieldHandlePivotAtLevel {R : LocalReciprocity}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (B : MarkedRecip R K) (alpha r h : ℕ) : Prop :=
  ∃ e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)),
    (∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
      toAdd (nuUrKTwo B (e.1 (dmGen alpha h (handleIdxU j)))) =
        (gamma : ℤ_[2]) * 2 ^ r) ∨
    ∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
      toAdd (nuUrKTwo B (e.1 (dmGen alpha h (handleIdxV j)))) =
        (gamma : ℤ_[2]) * 2 ^ r

/-- At level zero the intrinsic M kernel pivot is supported either on the canonical C
coordinate or on a handle coordinate. -/
theorem mFieldCPivot_or_handlePivotAtLevel_zero
    {R : LocalReciprocity}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (B : MarkedRecip R K) {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (hker : MChiKerUnimodular alpha h (m0Transport B e)) :
    MFieldCPivotAtLevel B alpha 0 h ∨
      MFieldHandlePivotAtLevel B alpha 0 h := by
  rcases isUnit_C_or_handle_of_chiKer halpha (m0Transport B e) hker with hC | hU | hV
  · refine Or.inl ⟨e, hC.unit, ?_⟩
    rw [pow_zero, mul_one, hC.unit_spec]
    rfl
  · obtain ⟨j, hj⟩ := hU
    refine Or.inr ⟨e, Or.inl ⟨j, hj.unit, ?_⟩⟩
    rw [pow_zero, mul_one, hj.unit_spec]
    rfl
  · obtain ⟨j, hj⟩ := hV
    refine Or.inr ⟨e, Or.inr ⟨j, hj.unit, ?_⟩⟩
    rw [pow_zero, mul_one, hj.unit_spec]
    rfl

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- Every family-selected M0 row has either the canonical C pivot or an exact unit on a
handle.  This is uniform in alpha and the handle count. -/
theorem m0_cPivot_or_handlePivot_of_familySelection
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha) :
    MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) ∨
      MFieldHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) := by
  have halpha : 2 ≤ alpha := by
    have hv : (BranchData.M0 alpha).Valid := hbranch ▸ S.valid
    exact BranchData.valid_M0_iff.mp hv
  obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_m0
    B FF S hmatch hbranch
  have hr : B.r = 0 := by
    have hs := S.level_eq
    rw [hbranch] at hs
    exact hs.symm
  exact mFieldCPivot_or_handlePivotAtLevel_zero B halpha e
    (mChiKerUnimodular_of_level_zero_general B hr e)

#print axioms isUnit_C_or_handle_of_chiKer
#print axioms MFieldHandlePivotAtLevel
#print axioms mFieldCPivot_or_handlePivotAtLevel_zero
#print axioms m0_cPivot_or_handlePivot_of_familySelection

end

end GQ2.Dyadic.Instances.MFieldMobileHandleDichotomy
