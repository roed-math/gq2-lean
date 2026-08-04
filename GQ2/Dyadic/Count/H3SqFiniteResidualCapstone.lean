/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedCubicObstruction
import GQ2.Dyadic.Count.H3SqReconstructionFiniteDetector
import GQ2.Dyadic.Count.H3SqCofinalTransitionDetector

/-!
# Conditional capstones from the finite square-presentation residuals

This file combines the independent boundaries left by the completed Magnus and finite bar--Fox
campaigns.  Its first two theorems are the live abstract endpoint: they start from an already
compatible family of universal comparisons and ask for either the reconstruction defect or its
explicit generator table to vanish.

The later theorems retain an earlier attempted construction of that family from literal
range-good universal-relation transitions.  `H3SqCofinalTransitionNoGo` proves that those
transition premises are false for the present free universal-relation alphabet.  They remain
here as regression lemmas documenting exactly what a corrected transition object must replace;
they are not viable hypotheses for the final proof.

The three independent live boundaries are:

* all-degree completed Magnus--PBW kernel exactness;
* construction of a compatible universal family using corrected relation-cell transport;
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

/-- Live joint-lift form of the finite endpoint.  The compatible one-relator lift is chosen
together with its reconstruction table instead of first fixing the canonical Fox-preserving
lift.  This retains the freedom in the universal Fox kernel exposed by the scalar-coordinate
detector. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_compatibleLiftReconstructionGenerators
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (L : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalBarRelationLiftAt (S V).universalSyzygy)
    (hgenerators : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionGeneratorSystemAt
        (S V).degreeThreeComparison (L V)) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) := by
  apply finiteElementaryH2RightExactSupply_DSq_of_kernelIdentity_reconstructionTransport h H
  refine {
    comparison := fun V => (S V).degreeThreeComparison
    reconstructionTransport := fun V => ⟨L V, ?_⟩ }
  exact (sqFiniteInputRelationReconstructionTransportAt_iff_kernel
      (S V).degreeThreeComparison (L V)).1
    ((sqFiniteInputRelationReconstructionGeneratorSystemAt_iff
      (S V).degreeThreeComparison (L V)).1 (hgenerators V))

/-- Standard-basis detector form using the named canonical square-presentation lift.  This is
a specialization of the joint-lift endpoint above. -/
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
  finiteElementaryH2RightExactSupply_DSq_of_compatibleLiftReconstructionGenerators
    h H S (fun V => (S V).universalSyzygy.relationLiftOfSqPresentation) hgenerators

/-- Historical conditional endpoint.  Range-good compactness would construct the universal
degree-three comparisons, but `not_sqUniversalBarInputTransitionCommonRefinementRange` proves
that its literal transition premise is false.  The theorem is retained to specify the interface
that a corrected relation-cell transition construction should recover. -/
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

/-- Historical detector form of the capstone.  Its effective-marking premise is refuted by
`not_sqUniversalBarInputTransitionPairDetectorEffectiveMarking`; a corrected detector must
first quotient the universal relation coordinates or carry explicit relation-cell corrections. -/
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

/-- Historical fully finite detector form.  The reconstruction table is a live finite target,
whereas the literal paired-transition marking is now known to be impossible. -/
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

/-- Historical decomposed regression.  Degrees zero, one, and two are unconditional and the
last-letter premise is live, but the literal effective transition detector must be replaced by
corrected relation-cell transport. -/
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
