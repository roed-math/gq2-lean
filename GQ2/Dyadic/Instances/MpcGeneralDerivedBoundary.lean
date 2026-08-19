/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralRowKernel

/-!
# The uniform derived-C boundary

The all-degree climb already puts every coordinate in an exact `chiM` fibre.  This module
rewrites the sole remaining constraint, uniformly in the degree, handle count, and stage:
the `C` correction must lie in the image of the deep topological derived subgroup.

Thus the general campaign is not a sequence of nilpotency-class calculations.  It is one
parameterized lifting problem inside an already nonempty affine fibre.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralDerivedBoundary

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralDerivationBridge
open GQ2.Dyadic.Instances.MpcGeneralChiCorrection
open GQ2.Dyadic.Instances.MpcGeneralConstraintShadow
open GQ2.Dyadic.Instances.MpcGeneralRowKernel
open GQ2.Roe.Labute

/-- The finite image of the deep topological derived subgroup in the distinguished slot. -/
def mpcGeneralDerivedCImage (alpha h j n : ℕ) :
    Subgroup (levelQuot (DM alpha h) n) :=
  (twoCentralSeries (DM alpha h : Type) j ⊓
    (mAbMkHom alpha h).toMonoidHom.ker).map (levelMk (DM alpha h) n)

/-- At correction depth at least two, the original universal-row condition is exactly the
deep derived image. -/
theorem mpcGeneralCorrectionImage_two_eq_derivedCImage
    {alpha h j n : ℕ} (halpha : 1 ≤ alpha) (hj : 2 ≤ j) :
    mpcGeneralCorrectionImage alpha h j n (2 : Fin (coreRank h)) =
      mpcGeneralDerivedCImage alpha h j n := by
  rw [mpcGeneralCorrectionImage, mpcGeneralDerivedCImage,
    mpcGeneralCorrectionSource_two_eq_abMkKernel halpha hj]

/-- Away from `C`, the constrained image is just the exact-`chiM` image. -/
theorem mpcGeneralCorrectionImage_eq_chiImage_of_ne
    {alpha h j n : ℕ} {i : Fin (coreRank h)} (hi : i ≠ 2) :
    mpcGeneralCorrectionImage alpha h j n i =
      mpcGeneralChiCorrectionImage alpha h j n := by
  rw [mpcGeneralCorrectionImage, mpcGeneralCorrectionSource, if_neg hi,
    mpcGeneralChiCorrectionImage]

/-- Membership in the original constrained correction group is exactly exact-`chiM`
membership away from `C`, together with one deep-derived condition at `C`. -/
theorem mem_mpcGeneralLevelToRaw_range_iff_exactChi_and_derivedC
    {alpha h k : ℕ} (halpha : 2 ≤ alpha) (hk : 3 ≤ k)
    (V : EvenRawDepthCorrection (DM alpha h) h k) :
    V ∈ (mpcGeneralLevelToRawHom alpha h k).range ↔
      (∀ i, i ≠ 2 → V.correction i ∈
        mpcGeneralChiCorrectionImage alpha h (k - 1) (k + 1)) ∧
      V.correction 2 ∈ mpcGeneralDerivedCImage alpha h (k - 1) (k + 1) := by
  rw [mem_mpcGeneralLevelToRaw_range_iff]
  constructor
  · intro H
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [← mpcGeneralCorrectionImage_eq_chiImage_of_ne hi]
      exact H i
    · rw [← mpcGeneralCorrectionImage_two_eq_derivedCImage (by omega) (by omega)]
      exact H 2
  · rintro ⟨Hchi, HC⟩ i
    by_cases hi : i = 2
    · subst hi
      rw [mpcGeneralCorrectionImage_two_eq_derivedCImage (by omega) (by omega)]
      exact HC
    · rw [mpcGeneralCorrectionImage_eq_chiImage_of_ne hi]
      exact Hchi i hi

/-- Exact uniform endpoint: constrained coverage is equivalent to finding, in the raw affine
fibre, exact-`chiM` corrections away from `C` and a deep-derived correction at `C`. -/
theorem mpcGeneral_target_mem_constrainedRange_iff_fiber_derivedC
    {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    mpcGeneralLevelTarget hm ∈ (mpcGeneralLevelShiftHom m k hk).range ↔
      ∃ V ∈ mpcGeneralRawFiber m hm hk,
        (∀ i, i ≠ 2 → V.correction i ∈
          mpcGeneralChiCorrectionImage alpha h (k - 1) (k + 1)) ∧
        V.correction 2 ∈ mpcGeneralDerivedCImage alpha h (k - 1) (k + 1) := by
  rw [mpcGeneral_target_mem_constrainedRange_iff_fiber_meets]
  constructor
  · rintro ⟨V, hV, hVr⟩
    exact ⟨V, hV,
      (mem_mpcGeneralLevelToRaw_range_iff_exactChi_and_derivedC halpha hk V).mp hVr⟩
  · rintro ⟨V, hV, hVc⟩
    exact ⟨V, hV,
      (mem_mpcGeneralLevelToRaw_range_iff_exactChi_and_derivedC halpha hk V).mpr hVc⟩

/-- The precise all-degree residual after exact-character reachability has been discharged. -/
def MpcGeneralDerivedCLiftSupply (alpha h : ℕ) : Prop :=
  ∀ k (hk : 3 ≤ k) m (hm : m ∈ mpcGeneralStage alpha h k),
    ∃ V ∈ mpcGeneralRawFiber m hm hk,
      (∀ i, i ≠ 2 → V.correction i ∈
        mpcGeneralChiCorrectionImage alpha h (k - 1) (k + 1)) ∧
      V.correction 2 ∈ mpcGeneralDerivedCImage alpha h (k - 1) (k + 1)

/-- The general derived-`C` lift supply is exactly the original finite-range supply. -/
theorem mpcGeneralDerivedCLiftSupply_iff_finiteRangeSupply
    {alpha h : ℕ} (halpha : 2 ≤ alpha) :
    MpcGeneralDerivedCLiftSupply alpha h ↔ MpcGeneralFiniteRangeSupply alpha h := by
  constructor
  · intro H k hk m hm
    exact (mpcGeneral_target_mem_constrainedRange_iff_fiber_derivedC
      halpha m hm hk).mpr (H k hk m hm)
  · intro H k hk m hm
    exact (mpcGeneral_target_mem_constrainedRange_iff_fiber_derivedC
      halpha m hm hk).mp (H k hk m hm)

/-- Solving the single derived-`C` lifting problem uniformly proves the general pivot shift. -/
theorem mpcPivShiftH_of_generalDerivedCLift {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (H : MpcGeneralDerivedCLiftSupply alpha h) : MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalFiniteRange halpha
    ((mpcGeneralDerivedCLiftSupply_iff_finiteRangeSupply halpha).mp H)

end

end GQ2.Dyadic.Instances.MpcGeneralDerivedBoundary

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralDerivedBoundary

#print axioms mpcGeneralDerivedCImage
#print axioms mpcGeneralCorrectionImage_two_eq_derivedCImage
#print axioms mpcGeneralCorrectionImage_eq_chiImage_of_ne
#print axioms mem_mpcGeneralLevelToRaw_range_iff_exactChi_and_derivedC
#print axioms mpcGeneral_target_mem_constrainedRange_iff_fiber_derivedC
#print axioms MpcGeneralDerivedCLiftSupply
#print axioms mpcGeneralDerivedCLiftSupply_iff_finiteRangeSupply
#print axioms mpcPivShiftH_of_generalDerivedCLift

end AxiomPins
