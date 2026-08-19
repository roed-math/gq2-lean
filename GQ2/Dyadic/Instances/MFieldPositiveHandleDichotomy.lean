/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldMobileHandleDichotomy
import GQ2.Dyadic.Instances.MpcFieldPivotFiltered

/-!
# The positive-level M mobile-pivot dichotomy

This module extends W309 from units to exact positive `Ztwo` levels.  If the B row is already
divisible by `2^r`, the full level condition and one exact kernel value force the divided
level-r unit onto either the distinguished C row or a standard handle row.

The epsilon-false Mpc selector supplies precisely the deep-B hypothesis.  Consequently every
selected epsilon-false Mpc row, for arbitrary alpha, level, and handle count, has either the
current canonical C pivot or an exact handle pivot.  Together with W309, both unresolved M
families now have the same uniform alternate-normal-form boundary: handle-supported pivot data.
-/

namespace GQ2.Dyadic.Instances.MFieldPositiveHandleDichotomy

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.SectionThree
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcFieldPivotFiltered
open GQ2.Dyadic.Instances.MFieldMobileHandleDichotomy
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

/-- At positive level, if the B row is already level-r divisible, an exact kernel value
occurs either on C or on a handle. -/
theorem exactLevel_C_or_handle_of_deepB
    {alpha r h : ℕ} (halpha : 2 ≤ alpha)
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu)
    (qB : ℤ_[2]) (hB : toAdd (nu (dmB alpha h)) = 2 ^ r * qB)
    (x : DM alpha h) (hxchi : chiM alpha h x = 1)
    (hxnu : toAdd (nu x) = 2 ^ r) :
    (∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmC alpha h)) = (gamma : ℤ_[2]) * 2 ^ r) ∨
      (∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
        toAdd (nu (dmGen alpha h (handleIdxU j))) =
          (gamma : ℤ_[2]) * 2 ^ r) ∨
      ∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
        toAdd (nu (dmGen alpha h (handleIdxV j))) =
          (gamma : ℤ_[2]) * 2 ^ r := by
  classical
  by_cases hC : ∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmC alpha h)) = (gamma : ℤ_[2]) * 2 ^ r
  · exact Or.inl hC
  by_cases hU : ∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmGen alpha h (handleIdxU j))) =
        (gamma : ℤ_[2]) * 2 ^ r
  · exact Or.inr (Or.inl hU)
  by_cases hV : ∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmGen alpha h (handleIdxV j))) =
        (gamma : ℤ_[2]) * 2 ^ r
  · exact Or.inr (Or.inr hV)
  exfalso
  push Not at hU hV
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
      toAdd (nu x) = ∑ i, c i * toAdd (nu (dmGen alpha h i)) := by
    rw [← abLiftG_abMk nu x, hc, mAbWord, map_prod, toAdd_prod]
    apply Finset.sum_congr rfl
    intro i hi
    rw [toAdd_map_zpowZtwo, abLiftG_abMk]
  have hA : toAdd (nu (dmGen alpha h 0)) =
      -(2 ^ (alpha - 1) * toAdd (nu (dmGen alpha h 2))) := by
    simpa only [nuFrame_apply] using
      (mChar_frameZero (α := alpha) (h := h) (by omega : 1 ≤ alpha) nu)
  have hsafe : ∀ i : Fin (coreRank h), ∃ y : ℤ_[2],
      c i * toAdd (nu (dmGen alpha h i)) = 2 ^ r * y ∧ mParityZ y = 0 := by
    intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · obtain ⟨qC, hqC⟩ := hlev (dmC alpha h) (chiM_dmC alpha h)
      refine ⟨-(c 0 * 2 ^ (alpha - 1) * qC), ?_, ?_⟩
      · rw [hA]
        change c 0 * (-(2 ^ (alpha - 1) * toAdd (nu (dmC alpha h)))) = _
        rw [hqC]
        ring
      · rw [mParityZ_neg]
        rw [show c 0 * 2 ^ (alpha - 1) * qC =
          (c 0 * qC) * 2 ^ (alpha - 1) by ring]
        exact mParityZ_mul_two_pow halpha _
    · refine ⟨c 1 * qB, ?_, ?_⟩
      · change c 1 * toAdd (nu (dmB alpha h)) = _
        rw [hB]
        ring
      · rw [mParityZ_mul, hrow.1, zero_mul]
    · obtain ⟨qC, hqC⟩ := hlev (dmC alpha h) (chiM_dmC alpha h)
      have hnqC : ¬ IsUnit qC := by
        intro hu
        apply hC
        refine ⟨hu.unit, ?_⟩
        rw [hqC, hu.unit_spec]
        ring
      refine ⟨c 2 * qC, ?_, ?_⟩
      · change c 2 * toAdd (nu (dmC alpha h)) = _
        rw [hqC]
        ring
      · rw [mParityZ_mul, parity_eq_zero_of_not_isUnit hnqC, mul_zero]
    · refine ⟨0, ?_, mParityZ_zero⟩
      rw [hrow.2, zero_mul, mul_zero]
    · rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [mHandleIdx_coordU]
        obtain ⟨qU, hqU⟩ := hlev _ (chiM_handleU alpha h j)
        have hnqU : ¬ IsUnit qU := by
          intro hu
          apply hU j hu.unit
          rw [hqU, hu.unit_spec]
          ring
        refine ⟨c (handleIdxU j) * qU, ?_, ?_⟩
        · rw [hqU]
          ring
        · rw [mParityZ_mul, parity_eq_zero_of_not_isUnit hnqU, mul_zero]
      · rw [mHandleIdx_coordV]
        obtain ⟨qV, hqV⟩ := hlev _ (chiM_handleV alpha h j)
        have hnqV : ¬ IsUnit qV := by
          intro hu
          apply hV j hu.unit
          rw [hqV, hu.unit_spec]
          ring
        refine ⟨c (handleIdxV j) * qV, ?_, ?_⟩
        · rw [hqV]
          ring
        · rw [mParityZ_mul, parity_eq_zero_of_not_isUnit hnqV, mul_zero]
  let q : Fin (coreRank h) → ℤ_[2] := fun i => Classical.choose (hsafe i)
  have hqspec : ∀ i, c i * toAdd (nu (dmGen alpha h i)) = 2 ^ r * q i :=
    fun i => (Classical.choose_spec (hsafe i)).1
  have hqpar : ∀ i, mParityZ (q i) = 0 :=
    fun i => (Classical.choose_spec (hsafe i)).2
  have hfactor : toAdd (nu x) = 2 ^ r * ∑ i, q i := by
    rw [hnuWord, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hqspec i
  have hsum : (∑ i, q i) = 1 := by
    rw [hxnu] at hfactor
    apply mul_left_cancel₀ (pow_ne_zero r (by norm_num : (2 : ℤ_[2]) ≠ 0))
    simpa using hfactor.symm
  have hpar := congrArg mParityZ hsum
  rw [parity_sum] at hpar
  have hzero : (∑ i, mParityZ (q i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hqpar i
  rw [hzero, mParityZ_one] at hpar
  exact zero_ne_one hpar

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- Every epsilon-false family-selected Mpc row has either the canonical exact C pivot or an
exact level-r handle pivot.  This is uniform in alpha, r, and the handle count. -/
theorem mpcFalse_cPivot_or_handlePivot_of_familySelection
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r false eta) :
    MFieldCPivotAtLevel B alpha r (handleCount P (.Mpc alpha r false eta)) ∨
      MFieldHandlePivotAtLevel B alpha r
        (handleCount P (.Mpc alpha r false eta)) := by
  let h := handleCount P (.Mpc alpha r false eta)
  have halpha : 2 ≤ alpha := by
    have hv : (BranchData.Mpc alpha r false eta).Valid := hbranch ▸ S.valid
    exact hv.1
  obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_mpc
    B FF S hmatch hbranch
  have hr : B.r = r := by
    have hs := S.level_eq
    rw [hbranch] at hs
    exact hs.symm
  let nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
    transport (nuUrKTwo B).toMonoidHom e.1
      ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
  obtain ⟨hlev, _hD, qB, hB⟩ := level_and_residues_of_familySelection
    B FF S hbranch e
  change MpcChiKerLevelH alpha r h nu at hlev
  change toAdd (nu (dmB alpha h)) = (p false r : ℤ_[2]) + 2 ^ r * qB at hB
  have hBdeep : toAdd (nu (dmB alpha h)) = 2 ^ r * qB := by
    simpa [p] using hB
  obtain ⟨x, hxchi, hxnu⟩ := exists_mpcExactKernelValue B hr e
  change toAdd (nu x) = 2 ^ r at hxnu
  have hcases := exactLevel_C_or_handle_of_deepB halpha nu hlev qB hBdeep
    x hxchi hxnu
  rcases hcases with hC | hU | hV
  · exact Or.inl ⟨e, hC⟩
  · exact Or.inr ⟨e, Or.inl hU⟩
  · exact Or.inr ⟨e, Or.inr hV⟩

#print axioms exactLevel_C_or_handle_of_deepB
#print axioms mpcFalse_cPivot_or_handlePivot_of_familySelection

end

end GQ2.Dyadic.Instances.MFieldPositiveHandleDichotomy
