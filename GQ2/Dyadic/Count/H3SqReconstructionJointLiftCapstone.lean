/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqReconstructionJointLift
import GQ2.Dyadic.Count.H3SqFiniteResidualCapstone

/-!
# Capstone consumer for the joint reconstruction-lift system

A solution of the finite joint affine system at every input quotient chooses both the compatible
one-relator lift and its reconstruction table.  This file feeds those choices into the live
joint-lift capstone.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

/-- Global family regression for the finite joint-lift systems. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_jointReconstructionLiftSystems
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (hjoint : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionJointLiftSystemAt
        (S V).degreeThreeComparison
        (S V).universalSyzygy.relationLiftOfSqPresentation) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) := by
  let L : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalBarRelationLiftAt (S V).universalSyzygy := fun V =>
    sqFiniteInputRelationReconstructionCompatibleLiftOfJointSystem
      (S V).degreeThreeComparison
      (S V).universalSyzygy.relationLiftOfSqPresentation
      (hjoint V)
  apply finiteElementaryH2RightExactSupply_DSq_of_compatibleLiftReconstructionGenerators
    h H S L
  intro V
  exact sqFiniteInputRelationReconstructionCompatibleLiftOfJointSystem_generators
    (S V).degreeThreeComparison
    (S V).universalSyzygy.relationLiftOfSqPresentation
    (hjoint V)

#print axioms finiteElementaryH2RightExactSupply_DSq_of_jointReconstructionLiftSystems

end

end GQ2.ContCoh
