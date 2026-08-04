/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2KernelHochschildSerre
import GQ2.Dyadic.Instances.GammaLSylowPreimageSchreier

/-!
# The explicit maximal-pro-2 inflation target for GammaL

This file replaces the opaque H²-inflation field in the `GammaL` Sylow-preimage package by the
equivalent cochain task: correct every finite elementary two-cocycle by a continuous
one-coboundary until it factors continuously through the maximal pro-2 quotient.

It does not weaken or discharge the second, independent finite-elementary CD2 premise.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ}

/-- For every simultaneous coefficient action, choose a Sylow subgroup and supply explicit
cocycle descent together with the still-independent finite-elementary CD2 tail on `U(2)`. -/
noncomputable abbrev GammaLSylowPreimageMaxProTwoCocycleDescentCDTwoSupply
    (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B],
      ∃ P : Sylow 2
          (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)),
        SylowPreimageMaxProTwoCocycleDescentCDTwoPackage
          (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P

/-- Explicit cocycle descent fills exactly the inflation component of the earlier maximal-pro-2
package. -/
theorem gammaLSylowPreimageMaxProTwoCDTwoSupply_of_cocycleDescent
    (S : GammaLSylowPreimageMaxProTwoCocycleDescentCDTwoSupply h q) :
    GammaLSylowPreimageMaxProTwoCDTwoSupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨P, D⟩ := S A B
  exact ⟨P, D.toCDTwoPackage _ _⟩

/-- The explicit descent/CD2 supply reaches the scalar-kernel H² tail isolated by the two
devissages. -/
theorem gammaLSylowPreimageScalarKernelH2TailSupply_of_cocycleDescent
    (S : GammaLSylowPreimageMaxProTwoCocycleDescentCDTwoSupply h q) :
    GammaLSylowPreimageScalarKernelH2TailSupply h q :=
  gammaLSylowPreimageScalarKernelH2TailSupply_of_maxProTwoCDTwo
    (gammaLSylowPreimageMaxProTwoCDTwoSupply_of_cocycleDescent S)

/-- End-to-end constructor phrased with the operational H² cocycle-descent target. -/
noncomputable def tateDualityG_of_sylowPreimageMaxProTwoCocycleDescentCDTwo
    (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (S : GammaLSylowPreimageMaxProTwoCocycleDescentCDTwoSupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sylowPreimageMaxProTwoCDTwo hq
    (gammaLSylowPreimageMaxProTwoCDTwoSupply_of_cocycleDescent S)

/-! ## The non-tautological kernel `H¹`--`H²` route -/

/-- For every simultaneous coefficient action, choose a Sylow subgroup and supply literal
`H²`-vanishing on its pro-2 kernel, the degree-one transgression normalization, and the
independent CD2 tail on `U(2)`. -/
noncomputable abbrev GammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply
    (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B],
      ∃ P : Sylow 2
          (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)),
        SylowPreimageMaxProTwoKernelOneTwoCDTwoPackage
          (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P

/-- Kernel `H¹`--`H²` data fills the H²-inflation field without assuming a class already
descends. -/
theorem gammaLSylowPreimageMaxProTwoCDTwoSupply_of_kernelOneTwo
    (S : GammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply h q) :
    GammaLSylowPreimageMaxProTwoCDTwoSupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨P, D⟩ := S A B
  exact ⟨P, D.toCDTwoPackage _ _⟩

/-- The kernel `H¹`--`H²` route reaches the scalar-kernel tail. -/
theorem gammaLSylowPreimageScalarKernelH2TailSupply_of_kernelOneTwo
    (S : GammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply h q) :
    GammaLSylowPreimageScalarKernelH2TailSupply h q :=
  gammaLSylowPreimageScalarKernelH2TailSupply_of_maxProTwoCDTwo
    (gammaLSylowPreimageMaxProTwoCDTwoSupply_of_kernelOneTwo S)

/-- End-to-end Tate constructor from literal pro-2-kernel degree `1`--`2` data. -/
noncomputable def tateDualityG_of_sylowPreimageMaxProTwoKernelOneTwoCDTwo
    (hq : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (S : GammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sylowPreimageMaxProTwoCDTwo hq
    (gammaLSylowPreimageMaxProTwoCDTwoSupply_of_kernelOneTwo S)

section ImprovedCoreBoundary

variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction (gamma h q : Type) A]
  [ContinuousSMul (gamma h q : Type) A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction (gamma h q : Type) B]
  [ContinuousSMul (gamma h q : Type) B]

/-- Exact interaction with the improved-L presentation.  The presentation side fills the CD2
field only after the separate Schreier kernel equality and a genuine core-CD2 theorem.  The
new degree `1`--`2` kernel supply fills the independent inflation field. -/
theorem sylowPreimageMaxProTwoKernelOneTwoCDTwoPackage_of_improvedCore
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hinf : FiniteElementaryMaxProTwoKernelOneTwoSupply
      (G := sylowTwoPreimage
        (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P))
    (hker : GammaLSylowPreimageProTwoKernelEquality P)
    (hcore : FiniteElementaryH2RightExactSupply (SqCore.DSq h)) :
    SylowPreimageMaxProTwoKernelOneTwoCDTwoPackage
      (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P where
  inflationKernel := hinf
  cdTwo := gammaLSylowPreimageMaxProTwoCDTwo_of_kernelEquality
    hq2 hqe P hker hcore

end ImprovedCoreBoundary

end

end GQ2.Dyadic.LSquare
