/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CorrectedCocycleFiber
import GQ2.Dyadic.Instances.GammaLSylowPreimageVariableCore

/-!
# Uniform square-core certificates for variable-rank Sylow preimages

An action-image Sylow preimage can have any odd finite index, so its expected square-core
handle count is not bounded by the ambient handle count.  The honest arithmetic capstone must
therefore consume the finite square-core theorem uniformly in `h'`.

This file provides that final adapter for the two live finite-certificate interfaces:

* joint reconstruction lifts on literal compatible universal syzygies;
* scalar bilinear certificates after corrected-transition strictification.

Both constructors use `GammaLSylowPreimageKernelH2AndVariableCoreSupply`; neither assumes the
generally false fixed-core kernel equality.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

variable {h q : ℕ}

/-- Variable-rank Tate endpoint from joint reconstruction-lift systems at every square-core
handle count. -/
noncomputable def tateDualityG_of_sqVariableCoreJointReconstructionLiftSystems
    (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (H : ∀ h' : ℕ, SqCompletedMonomialPBWKernelIdentityAll h')
    (S : ∀ (h' : ℕ) (V : OpenNormalSubgroup (DSq h' : Type)),
      SqCompatibleUniversalCocycleCancellingSyzygyAt h' V)
    (hjoint : ∀ (h' : ℕ) (V : OpenNormalSubgroup (DSq h' : Type)),
      SqFiniteInputRelationReconstructionJointLiftSystemAt
        (S h' V).degreeThreeComparison
        (S h' V).universalSyzygy.relationLiftOfSqPresentation)
    (R : GammaLSylowPreimageKernelH2AndVariableCoreSupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_variableCoreAndSylowKernelResiduals hqe R fun h' ↦
    finiteElementaryH2RightExactSupply_DSq_of_jointReconstructionLiftSystems
      h' (H h') (S h') (hjoint h')

/-- Preferred variable-rank arithmetic endpoint.  Corrected transition families are
strictified at every handle count, and the remaining reconstruction obstruction is supplied
by the finite scalar bilinear certificate. -/
noncomputable def tateDualityG_of_sqVariableCoreCorrectedScalarBilinearCertificates
    (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (H : ∀ h' : ℕ, SqCompletedMonomialPBWKernelIdentityAll h')
    (C : ∀ (h' : ℕ) (V : OpenNormalSubgroup (DSq h' : Type)),
      SqCorrectedCompatibleUniversalCocycleCancellingSyzygyAt h' V)
    (T : ∀ (h' : ℕ) (V : OpenNormalSubgroup (DSq h' : Type)),
      (C h' V).RawStrictification)
    (hscalar : ∀ (h' : ℕ) (V : OpenNormalSubgroup (DSq h' : Type)),
      SqFiniteInputRelationReconstructionScalarBilinearCertificateAt
        (T h' V).raw.degreeThreeComparison
        (T h' V).raw.universalSyzygy.relationLiftOfSqPresentation)
    (R : GammaLSylowPreimageKernelH2AndVariableCoreSupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_variableCoreAndSylowKernelResiduals hqe R fun h' ↦
    finiteElementaryH2RightExactSupply_DSq_of_correctedScalarBilinearCertificates
      h' (H h') (C h') (T h') (hscalar h')

#print axioms tateDualityG_of_sqVariableCoreJointReconstructionLiftSystems
#print axioms tateDualityG_of_sqVariableCoreCorrectedScalarBilinearCertificates

end


end GQ2.Dyadic.LSquare
