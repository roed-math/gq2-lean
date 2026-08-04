/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CorrectedCocycleFiber
import GQ2.Dyadic.Instances.GammaLSylowPreimageInflationKernel

/-!
# From the improved square core to `GammaL` Tate duality

This file joins the finite square-core campaign to the existing Sylow-preimage devissage.  It
keeps the two independent ambient inputs visible: degree-two vanishing on the maximal-pro-`2`
kernel of each chosen Sylow preimage, and identification of that maximal pro-`2` quotient with
the improved square core.

The preferred square-core input below is a compatible family of finite universal comparisons
whose explicit reconstruction generator systems are solvable.  It deliberately does not use
the literal common-refinement transition premise, which is refuted by
`H3SqCofinalTransitionNoGo`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

variable {h q : ℕ}

/-- The two residual Sylow-preimage inputs that are independent of the square-core `H²` tail.
For every simultaneous finite coefficient action, one may choose a Sylow subgroup for which
the maximal-pro-`2` kernel has vanishing finite elementary `H²` and the canonical map to the
improved square core has the expected kernel. -/
noncomputable abbrev GammaLSylowPreimageKernelH2AndCoreEqualitySupply
    (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B],
      ∃ P : Sylow 2
          (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)),
        GammaLSylowPreimageKernelH2VanishesSupply P ∧
          GammaLSylowPreimageProTwoKernelEquality P

/-- Kernel `H²`-vanishing supplies the already-unconditional degree-one transgression field;
kernel equality transports the square-core `H²` tail.  Together they fill the exact
Sylow-preimage package used by the Tate-duality devissage. -/
theorem gammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply_of_coreAndKernelResiduals
    (hq2 : 2 ≤ q) (hqe : Even q)
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q)
    (hcore : FiniteElementaryH2RightExactSupply (DSq h : Type)) :
    GammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨P, hH2, hker⟩ := R A B
  let U := sylowTwoPreimage
    (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P
  have hinf : FiniteElementaryMaxProTwoKernelOneTwoSupply (G := U) :=
    finiteElementaryMaxProTwoKernelOneTwoSupply_of_h2Vanishes_transgression hH2
      (finiteElementaryMaxProTwoKernelTransgression (G := U))
  exact ⟨P, sylowPreimageMaxProTwoKernelOneTwoCDTwoPackage_of_improvedCore
    hq2 hqe P hinf hker hcore⟩

/-- Honest end-to-end constructor from a proved square-core `H²` tail and the two residual
Sylow-kernel statements. -/
noncomputable def tateDualityG_of_sqCoreAndSylowKernelResiduals
    (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q)
    (hcore : FiniteElementaryH2RightExactSupply (DSq h : Type)) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sylowPreimageMaxProTwoKernelOneTwoCDTwo hqe
    (gammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply_of_coreAndKernelResiduals
      hq2 hqe R hcore)

/-- Current preferred finite certificate route to `GammaL` Tate duality.  The compatible
one-relator lift is chosen jointly with its reconstruction table, retaining the freedom in the
universal Fox kernel. -/
noncomputable def tateDualityG_of_sqCompatibleLiftReconstructionGenerators
    (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (L : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalBarRelationLiftAt (S V).universalSyzygy)
    (hgenerators : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionGeneratorSystemAt
        (S V).degreeThreeComparison (L V))
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sqCoreAndSylowKernelResiduals hq2 hqe R
    (finiteElementaryH2RightExactSupply_DSq_of_compatibleLiftReconstructionGenerators
      h H S L hgenerators)

/-- Finite affine-system form of the honest Tate-duality endpoint.  At each input quotient the
joint system chooses a globally reachable correction of the one-relator lift together with its
reconstruction table. -/
noncomputable def tateDualityG_of_sqJointReconstructionLiftSystems
    (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (hjoint : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionJointLiftSystemAt
        (S V).degreeThreeComparison
        (S V).universalSyzygy.relationLiftOfSqPresentation)
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sqCoreAndSylowKernelResiduals hq2 hqe R
    (finiteElementaryH2RightExactSupply_DSq_of_jointReconstructionLiftSystems
      h H S hjoint)

/-- Corrected-transition form of the honest arithmetic endpoint.  The transition family is
first strictified through its explicit affine Fox-kernel obstruction; the one-relator lift is
then chosen jointly with its reconstruction table. -/
noncomputable def tateDualityG_of_sqCorrectedJointLiftSystems
    (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (C : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCorrectedCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (T : ∀ V : OpenNormalSubgroup (DSq h : Type),
      (C V).RawStrictification)
    (hjoint : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionJointLiftSystemAt
        (T V).raw.degreeThreeComparison
        (T V).raw.universalSyzygy.relationLiftOfSqPresentation)
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sqCoreAndSylowKernelResiduals hq2 hqe R
    (finiteElementaryH2RightExactSupply_DSq_of_correctedJointLiftSystems
      h H C T hjoint)

/-- Fully scalar finite-certificate form of the corrected-transition arithmetic endpoint. -/
noncomputable def tateDualityG_of_sqCorrectedScalarBilinearCertificates
    (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (C : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCorrectedCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (T : ∀ V : OpenNormalSubgroup (DSq h : Type),
      (C V).RawStrictification)
    (hscalar : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionScalarBilinearCertificateAt
        (T V).raw.degreeThreeComparison
        (T V).raw.universalSyzygy.relationLiftOfSqPresentation)
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sqCoreAndSylowKernelResiduals hq2 hqe R
    (finiteElementaryH2RightExactSupply_DSq_of_correctedScalarBilinearCertificates
      h H C T hscalar)

/-- Specialization of the preceding route to the named canonical square-presentation lift. -/
noncomputable def tateDualityG_of_sqCompatibleReconstructionGenerators
    (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (hgenerators : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionGeneratorSystemAt
        (S V).degreeThreeComparison
        (S V).universalSyzygy.relationLiftOfSqPresentation)
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sqCoreAndSylowKernelResiduals hq2 hqe R
    (finiteElementaryH2RightExactSupply_DSq_of_compatibleReconstructionGenerators
      h H S hgenerators)

/-- Regression form exposing the higher completed-Magnus induction one degree at a time. -/
noncomputable def tateDualityG_of_sqCompatibleLastLetterAndReconstructionGenerators
    (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (Hstep : ∀ n (Hn : SqCompletedMonomialPBWKernelIdentity h n), 2 ≤ n →
      SqCompletedLastLetterKernelExact h n Hn)
    (S : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (hgenerators : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionGeneratorSystemAt
        (S V).degreeThreeComparison
        (S V).universalSyzygy.relationLiftOfSqPresentation)
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sqCompatibleReconstructionGenerators hq2 hqe
    (sqCompletedMonomialPBWKernelIdentityAll_of_lastLetterKernelExact h Hstep)
    S hgenerators R

end

end GQ2.Dyadic.LSquare
