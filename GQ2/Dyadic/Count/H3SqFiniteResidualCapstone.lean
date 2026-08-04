/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedCubicObstruction
import GQ2.Dyadic.Count.H3SqAdjointReconstructionDefect
import GQ2.Dyadic.Count.H3SqCofinalTransitionDetector

/-!
# End-to-end capstones from the finite square-presentation residuals

This file combines the three independent boundaries left by the completed Magnus and finite
bar--Fox campaigns:

* all-degree completed Magnus--PBW kernel exactness;
* cofinal local solvability with simultaneous range-good transition refinements;
* vanishing of the finite-support reconstruction defect for the chosen single-relator lift.

No eventual relation-generation premise occurs: it is already unconditional for `DSq h`.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

/-- The exact current end-to-end theorem.  Range-good compactness constructs the universal
degree-three comparisons; the displayed defect-zero condition turns each of them into the
single-relator reconstruction required by the completed bar--Fox assembly. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_finiteResiduals
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (hlocal : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeGoodCofinalAt h V)
    (hcommon : SqUniversalBarInputTransitionCommonRefinementRange h)
    (hcancel : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqUniversalBarInputCocycleCancellationTransitionKernel h V)
    (hdefect : ∀ (V : OpenNormalSubgroup (DSq h : Type))
      (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V),
      S.sqPresentationFiniteSupportTransportDefect = 0) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) := by
  let S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V := fun V =>
    Classical.choice
      (nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_rangeGoodCofinal
        h V (hlocal V) hcommon (hcancel V))
  let C : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputUniversalDegreeThreeComparisonAt h V := fun V =>
    (S V).degreeThreeComparison
  apply finiteElementaryH2RightExactSupply_DSq_of_kernelIdentity_universalComparisonKernel
    h H C
  intro V
  exact ((S V).reconstructionKernel_iff_defect_eq_zero
    (S V).universalSyzygy.relationLiftOfSqPresentation).2 (hdefect V (S V))

/-- Detector form of the capstone.  An effective marking of each paired finite transition
detector supplies the simultaneous common refinements used above. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_effectiveTransitionDetectors
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (hlocal : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeGoodCofinalAt h V)
    (heffective : SqUniversalBarInputTransitionPairDetectorEffectiveMarking h)
    (hcancel : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqUniversalBarInputCocycleCancellationTransitionKernel h V)
    (hdefect : ∀ (V : OpenNormalSubgroup (DSq h : Type))
      (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V),
      S.sqPresentationFiniteSupportTransportDefect = 0) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_finiteResiduals h H hlocal
    (sqUniversalBarInputTransitionCommonRefinementRange_of_effectivePairDetectorMarking
      h heffective)
    hcancel hdefect

/-- Fully decomposed regression: degrees zero, one, and two are already unconditional, so
last-letter row exactness from degree two onward plus the two finite degree-three detector
conditions prove the complete finite-coefficient `H²` tail for the improved square core. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_lastLetterAndFiniteDetectors
    (h : ℕ)
    (Hstep : ∀ n (Hn : SqCompletedMonomialPBWKernelIdentity h n), 2 ≤ n →
      SqCompletedLastLetterKernelExact h n Hn)
    (hlocal : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeGoodCofinalAt h V)
    (heffective : SqUniversalBarInputTransitionPairDetectorEffectiveMarking h)
    (hcancel : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqUniversalBarInputCocycleCancellationTransitionKernel h V)
    (hdefect : ∀ (V : OpenNormalSubgroup (DSq h : Type))
      (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V),
      S.sqPresentationFiniteSupportTransportDefect = 0) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_effectiveTransitionDetectors h
    (sqCompletedMonomialPBWKernelIdentityAll_of_lastLetterKernelExact h Hstep)
    hlocal heffective hcancel hdefect

end

end GQ2.ContCoh
