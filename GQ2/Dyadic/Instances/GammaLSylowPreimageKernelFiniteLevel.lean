/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2KernelFiniteLevel
import GQ2.Dyadic.Instances.GammaLSylowPreimageInflationKernel

/-!
# The remaining GammaL kernel H² statement at finite level

This file replaces the literal continuous `H²`-vanishing boundary on
`K₂(G) = proPKernel 2 G` by its exact finite-quotient form.  For every finite elementary
quotient-compatible coefficient module, every two-cocycle on one finite quotient of `K₂(G)`
must become a coboundary after pullback to some finer finite quotient.

The word *finer* is essential.  The statement does not assert that the first finite quotient
has zero `H²`; equivalently, it asks every represented finite extension to split eventually in
the directed system of finite quotients.
-/

namespace GQ2.ContCoh

noncomputable section

section UniformKernelBoundary

variable {G : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The finite-quotient form of the sole residual maximal-pro-`2` kernel input. -/
def FiniteElementaryMaxProTwoKernelFiniteRefinementSupply : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [Finite M]
    [DistribMulAction G M] [ContinuousSMul G M]
    [DistribMulAction (maxProPQuotient 2 G) M]
    [ContinuousSMul (maxProPQuotient 2 G) M],
    (∀ m : M, m + m = 0) →
    ∀ _hcompat : ∀ (g : G) (m : M), maxProPMk 2 G g • m = g • m,
      letI : IsClosed (proPKernel 2 G : Set G) := proPKernel_isClosed 2 G
      letI : CompactSpace (proPKernel 2 G) := isCompact_iff_compactSpace.mp
        (proPKernel_isClosed 2 G).isCompact
      FiniteRefinementTrivialHTwoVanishes (G := proPKernel 2 G) (M := M)

/-- Exact reduction of uniform kernel `H²`-vanishing to eventual finite-quotient
coboundaries.  Quotient compatibility makes the action on `K₂(G)` trivial, so the general
finite-refinement equivalence applies coefficient by coefficient. -/
theorem finiteElementaryMaxProTwoKernelH2VanishesSupply_iff_finiteRefinement :
    FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := G) ↔
      FiniteElementaryMaxProTwoKernelFiniteRefinementSupply (G := G) := by
  constructor
  · intro D M _ _ _ _ _ _ _ _ _ hM2 hcompat
    letI : IsClosed (proPKernel 2 G : Set G) := proPKernel_isClosed 2 G
    letI : CompactSpace (proPKernel 2 G) := isCompact_iff_compactSpace.mp
      (proPKernel_isClosed 2 G).isCompact
    have htriv : ∀ (k : proPKernel 2 G) (m : M), k • m = m := by
      intro k m
      exact maxProTwoKernel_smul_eq hcompat k m
    exact (finiteRefinementTrivialHTwoVanishes_iff_continuousH2Vanishes htriv).2
      (D M hM2 hcompat)
  · intro D M _ _ _ _ _ _ _ _ _ hM2 hcompat
    letI : IsClosed (proPKernel 2 G : Set G) := proPKernel_isClosed 2 G
    letI : CompactSpace (proPKernel 2 G) := isCompact_iff_compactSpace.mp
      (proPKernel_isClosed 2 G).isCompact
    have htriv : ∀ (k : proPKernel 2 G) (m : M), k • m = m := by
      intro k m
      exact maxProTwoKernel_smul_eq hcompat k m
    exact (finiteRefinementTrivialHTwoVanishes_iff_continuousH2Vanishes htriv).1
      (D M hM2 hcompat)

/-- Eventual finite-quotient splitting is therefore sufficient for maximal-pro-`2` degree-two
inflation. -/
theorem finiteElementaryH2InflationSurjective_of_kernelFiniteRefinement
    (D : FiniteElementaryMaxProTwoKernelFiniteRefinementSupply (G := G)) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 G) :=
  finiteElementaryH2InflationSurjective_of_kernelH2Vanishes
    (finiteElementaryMaxProTwoKernelH2VanishesSupply_iff_finiteRefinement.mpr D)

end UniformKernelBoundary

end

end GQ2.ContCoh

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ}
variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction (gamma h q : Type) A]
  [ContinuousSMul (gamma h q : Type) A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction (gamma h q : Type) B]
  [ContinuousSMul (gamma h q : Type) B]

local notation "rhoAB" =>
  pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)

local notation "U" P => sylowTwoPreimage rhoAB P

/-- The exact finite-quotient target for the special kernel attached to a `GammaL`
Sylow preimage. -/
noncomputable abbrev GammaLSylowPreimageKernelFiniteRefinementSupply
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  FiniteElementaryMaxProTwoKernelFiniteRefinementSupply (G := U P)

/-- The remaining `GammaL` kernel theorem is exactly eventual finite-quotient splitting. -/
theorem gammaLSylowPreimageKernelH2Vanishes_iff_finiteRefinement
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageKernelH2VanishesSupply P ↔
      GammaLSylowPreimageKernelFiniteRefinementSupply P :=
  finiteElementaryMaxProTwoKernelH2VanishesSupply_iff_finiteRefinement

/-- Finite-quotient splitting on the special kernel supplies the desired inflation theorem. -/
theorem gammaLSylowPreimageH2InflationSurjective_of_kernelFiniteRefinement
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (D : GammaLSylowPreimageKernelFiniteRefinementSupply P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (U P)) :=
  finiteElementaryH2InflationSurjective_of_kernelFiniteRefinement D

end


/-! ## The `n = 1` / Q₂ regression

At `(h,q)=(0,2)`, the existing realization identifies `gamma 0 2` with `G_Q₂` and proves its
Tate-duality package.  Those theorems do not currently prove acyclicity of the kernel of the
maximal pro-`2` quotient.  The regression below records the exact additional finite-level
statement needed in this base case; it is not silently discharged by Tate duality.
-/

noncomputable section

open GQ2 GQ2.ContCoh

section ZeroTwo

variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction (gamma 0 2 : Type) A]
  [ContinuousSMul (gamma 0 2 : Type) A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction (gamma 0 2 : Type) B]
  [ContinuousSMul (gamma 0 2 : Type) B]

local notation "rhoZeroTwo" =>
  pairFiniteActionImageHom (h := 0) (q := 2) (A := A) (B := B)

local notation "UZeroTwo" P => sylowTwoPreimage rhoZeroTwo P

/-- Explicit base-case pin: even for `G_Q₂`, the special kernel claim is precisely the
eventual finite-refinement statement. -/
theorem gammaLZeroTwoSylowPreimageKernelH2Vanishes_iff_finiteRefinement
    (P : Sylow 2 (PairFiniteActionImage (h := 0) (q := 2) (A := A) (B := B))) :
    GammaLSylowPreimageKernelH2VanishesSupply P ↔
      GammaLSylowPreimageKernelFiniteRefinementSupply P :=
  gammaLSylowPreimageKernelH2Vanishes_iff_finiteRefinement P

/-- The honest `n=1` conclusion: the indicated finite-refinement premise implies the desired
maximal-pro-`2` inflation theorem for the Q₂ Sylow preimage. -/
theorem gammaLZeroTwoSylowPreimageH2InflationSurjective_of_kernelFiniteRefinement
    (P : Sylow 2 (PairFiniteActionImage (h := 0) (q := 2) (A := A) (B := B)))
    (D : GammaLSylowPreimageKernelFiniteRefinementSupply P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (UZeroTwo P)) :=
  gammaLSylowPreimageH2InflationSurjective_of_kernelFiniteRefinement P D

end ZeroTwo

end

end GQ2.Dyadic.LSquare
