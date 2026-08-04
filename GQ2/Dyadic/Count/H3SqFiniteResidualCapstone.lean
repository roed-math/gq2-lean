/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedCubicObstruction
import GQ2.Dyadic.Count.H3SqReconstructionFiniteDetector
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

/-- The minimal assembled endpoint: a compatible cocycle-cancelling universal output with
zero square-presentation transport defect at every finite input quotient, together with the
all-degree Magnus identity, proves the complete finite-coefficient `H²` tail. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_compatibleDefectZero
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (hdefect : ∀ V : OpenNormalSubgroup (DSq h : Type),
      (S V).sqPresentationFiniteSupportTransportDefect = 0) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) := by
  let C : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputUniversalDegreeThreeComparisonAt h V := fun V =>
    (S V).degreeThreeComparison
  apply finiteElementaryH2RightExactSupply_DSq_of_kernelIdentity_universalComparisonKernel
    h H C
  intro V
  exact ((S V).reconstructionKernel_iff_defect_eq_zero
    (S V).universalSyzygy.relationLiftOfSqPresentation).2 (hdefect V)

/-- Standard-basis detector form of the minimal assembled endpoint. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_compatibleReconstructionGenerators
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (hgenerators : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionGeneratorSystemAt
        (S V).degreeThreeComparison
        (S V).universalSyzygy.relationLiftOfSqPresentation) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_compatibleDefectZero h H S
    (fun V => ((S V).sqPresentationFiniteSupportTransportDefect_eq_zero_iff_generators).2
      (hgenerators V))

/-- A fully decomposed current end-to-end theorem.  Range-good compactness constructs the
universal degree-three comparisons; the displayed defect-zero condition turns each of them into
the single-relator reconstruction required by the completed bar--Fox assembly. -/
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
  exact finiteElementaryH2RightExactSupply_DSq_of_compatibleDefectZero h H S
    (fun V => hdefect V (S V))

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

/-- Fully finite detector form: the transition condition is an effective marking of the paired
finite obstruction, and reconstruction is the explicit standard-basis linear system. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_transitionAndReconstructionDetectors
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (hlocal : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeGoodCofinalAt h V)
    (heffective : SqUniversalBarInputTransitionPairDetectorEffectiveMarking h)
    (hcancel : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqUniversalBarInputCocycleCancellationTransitionKernel h V)
    (hgenerators : ∀ (V : OpenNormalSubgroup (DSq h : Type))
      (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V),
      SqFiniteInputRelationReconstructionGeneratorSystemAt
        S.degreeThreeComparison
        S.universalSyzygy.relationLiftOfSqPresentation) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_effectiveTransitionDetectors h H
    hlocal heffective hcancel fun V S =>
      (S.sqPresentationFiniteSupportTransportDefect_eq_zero_iff_generators).2
        (hgenerators V S)

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
