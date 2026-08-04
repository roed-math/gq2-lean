/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2MaxProTwoTransport
import GQ2.Dyadic.Instances.GammaLReconstruction
import GQ2.Dyadic.Instances.GammaLSylowPreimageDevissage

/-!
# The maximal pro-2 endpoint for the `GammaL` Sylow preimages

This file specializes the exact maximal-pro-2 transport package to the simultaneous finite
coefficient-action images used in the `GammaL` devissage.  It also records a concrete structural
consequence of the improved L presentation: if `q` is even and at least two, then the maximal
pro-2 quotient of every action-image Sylow preimage maps *onto* the canonical square core.

The resulting map is not asserted to be an isomorphism.  The two premises in
`GammaLSylowPreimageMaxProTwoCDTwoSupply` remain exactly:

* finite-elementary degree-two inflation from `U(2)` to `U` is onto;
* `U(2)` has the finite-elementary CD-2/right-exactness tail.

Thus the endpoint can be filled by a future pro-2 presentation/asphericity theorem without
silently identifying scalar Demushkin data with cohomological dimension two.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ}

/-! ## The exact maximal-pro-2 supply and its Tate-duality adapter -/

/-- For every simultaneous coefficient-action image, choose a Sylow `2`-subgroup and supply
the two honest maximal-pro-2 inputs: H² inflation surjectivity and finite-elementary CD-2 on
the maximal pro-2 quotient of its preimage. -/
noncomputable abbrev GammaLSylowPreimageMaxProTwoCDTwoSupply (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B],
      ∃ P : Sylow 2
          (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)),
        SylowPreimageMaxProTwoCDTwoPackage
          (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P

/-- The maximal-pro-2 comparison/CD-2 package supplies the scalar-kernel tail isolated by the
Sylow and coefficient devissages. -/
theorem gammaLSylowPreimageScalarKernelH2TailSupply_of_maxProTwoCDTwo
    (S : GammaLSylowPreimageMaxProTwoCDTwoSupply h q) :
    GammaLSylowPreimageScalarKernelH2TailSupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨P, D⟩ := S A B
  exact ⟨P, D.toScalarKernelH2Tail _ _⟩

/-- The same package directly supplies the transfer-free Sylow-local H² endpoint. -/
theorem gammaLSylowTwoLocalH2RightExactSupply_of_maxProTwoCDTwo
    (S : GammaLSylowPreimageMaxProTwoCDTwoSupply h q) :
    GammaLSylowTwoLocalH2RightExactSupply h q :=
  gammaLSylowTwoLocalH2RightExactSupply_of_scalarKernelTails
    (gammaLSylowPreimageScalarKernelH2TailSupply_of_maxProTwoCDTwo S)

/-- End-to-end constructor: the exact maximal-pro-2 comparison/CD-2 supply proves the full
`TateDualityG` package for the improved L presentation. -/
noncomputable def tateDualityG_of_sylowPreimageMaxProTwoCDTwo
    (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (S : GammaLSylowPreimageMaxProTwoCDTwoSupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sylowPreimageScalarKernelTails hq
    (gammaLSylowPreimageScalarKernelH2TailSupply_of_maxProTwoCDTwo S)

/-! ## The concrete map to the improved-L square core -/

variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction (gamma h q : Type) A]
  [ContinuousSMul (gamma h q : Type) A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction (gamma h q : Type) B]
  [ContinuousSMul (gamma h q : Type) B]

/-- The maximal pro-2 quotient of an action-image Sylow preimage maps canonically to the
square core in the improved L presentation. -/
noncomputable def gammaLSylowPreimageMaxProTwoToLCore
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2
      (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    ContinuousMonoidHom
      (maxProPQuotient 2 (sylowTwoPreimage
        (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P))
      (SqCore.DSq h) :=
  sylowPreimageMaxProTwoLift
    (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P
    (SqCore.isProP_DSq h) (lCanonicalPro2 h q hq2 hqe)

/-- The canonical map from `U(2)` to the improved-L square core is onto.  This is the precise
pro-2 structural consequence of combining odd Sylow index with the proved square-core
quotient; no injectivity or CD-2 conclusion is bundled into it. -/
theorem gammaLSylowPreimageMaxProTwoToLCore_surjective
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2
      (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    Function.Surjective
      (gammaLSylowPreimageMaxProTwoToLCore hq2 hqe P) :=
  sylowPreimageMaxProTwoLift_surjective
    (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B))
    pairFiniteActionImageHom_surjective P (SqCore.isProP_DSq h)
    (lCanonicalPro2 h q hq2 hqe)
    (Count.CorePresentation.coreHom_surjective
      (Instances.LSquareCore.lCorePresentation h)
      (q_ne_zero_of_two_le hq2) hqe)

end

end GQ2.Dyadic.LSquare
