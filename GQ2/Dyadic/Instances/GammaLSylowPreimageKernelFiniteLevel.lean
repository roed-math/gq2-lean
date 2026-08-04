/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2KernelFiniteLevel
import GQ2.Dyadic.Instances.GammaLSylowPreimageInflationKernel
import GQ2.Dyadic.MaxProTwoCohomology

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

/-- The single scalar statement to which the uniform finite-elementary kernel premise reduces.
The explicit trivial action keeps this proposition independent of any ambient choice of an
action on `ZMod 2`. -/
def MaxProTwoKernelScalarH2Vanishes : Prop :=
  letI := trivialAddAction (M := ZMod 2) (proPKernel 2 G)
  letI : ContinuousSMul (proPKernel 2 G) (ZMod 2) :=
    continuousSMul_trivialAddAction (M := ZMod 2) (proPKernel 2 G)
  ContinuousH2Vanishes (proPKernel 2 G) (ZMod 2)

/-- A single scalar kernel-acyclicity theorem supplies the uniform kernel `H²` premise for
every finite elementary quotient-compatible coefficient module. -/
theorem finiteElementaryMaxProTwoKernelH2VanishesSupply_of_scalar
    (hscalar : MaxProTwoKernelScalarH2Vanishes (G := G)) :
    FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := G) := by
  intro M _ _ _ _ _ _ _ _ _ hM₂ hcompat
  letI : IsClosed (proPKernel 2 G : Set G) := proPKernel_isClosed 2 G
  letI : CompactSpace (proPKernel 2 G) := isCompact_iff_compactSpace.mp
    (proPKernel_isClosed 2 G).isCompact
  have htrivM : ∀ (k : proPKernel 2 G) (m : M), k • m = m := by
    intro k m
    exact maxProTwoKernel_smul_eq hcompat k m
  letI : DistribMulAction (proPKernel 2 G) (ZMod 2) :=
    trivialAddAction (M := ZMod 2) (proPKernel 2 G)
  letI : ContinuousSMul (proPKernel 2 G) (ZMod 2) :=
    continuousSMul_trivialAddAction (M := ZMod 2) (proPKernel 2 G)
  exact continuousH2Vanishes_of_zmodTwo hM₂ htrivM (fun _ _ ↦ rfl) hscalar

/-- Thus the previously uniform residual premise is exactly one scalar kernel statement. -/
theorem finiteElementaryMaxProTwoKernelH2VanishesSupply_iff_scalar :
    FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := G) ↔
      MaxProTwoKernelScalarH2Vanishes (G := G) := by
  constructor
  · intro D
    letI : DistribMulAction G (ZMod 2) := trivialAddAction (M := ZMod 2) G
    letI : ContinuousSMul G (ZMod 2) := continuousSMul_trivialAddAction (M := ZMod 2) G
    letI : DistribMulAction (maxProPQuotient 2 G) (ZMod 2) :=
      trivialAddAction (M := ZMod 2) (maxProPQuotient 2 G)
    letI : ContinuousSMul (maxProPQuotient 2 G) (ZMod 2) :=
      continuousSMul_trivialAddAction (M := ZMod 2) (maxProPQuotient 2 G)
    exact D (ZMod 2) (by decide) (fun _ _ ↦ rfl)
  · exact finiteElementaryMaxProTwoKernelH2VanishesSupply_of_scalar

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

/-- The finite-refinement version of the residual premise is likewise equivalent to the one
scalar kernel statement. -/
theorem finiteElementaryMaxProTwoKernelFiniteRefinementSupply_iff_scalar :
    FiniteElementaryMaxProTwoKernelFiniteRefinementSupply (G := G) ↔
      MaxProTwoKernelScalarH2Vanishes (G := G) :=
  finiteElementaryMaxProTwoKernelH2VanishesSupply_iff_finiteRefinement.symm.trans
    finiteElementaryMaxProTwoKernelH2VanishesSupply_iff_scalar

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

namespace GQ2.Dyadic

noncomputable section

open GQ2.ContCoh

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2)]
  [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)]

/-- The strongest presently formalized scalar consequence on an arithmetic local Galois
group: every mod-two two-cocycle on `G_K` admits explicit descent, after a continuous
one-cochain correction, to `G_K(2)`.

This follows from the existing scalar `H²` inflation equivalence.  It is deliberately not
repackaged as `H²(proPKernel 2 (GalK K), F₂)=0`: that conclusion needs an additional
Hochschild--Serre edge/degree-three input and does not follow from inflation surjectivity alone. -/
theorem galKScalarMaxProTwoH2CocycleDescent :
    MaxProTwoH2CocycleDescent (G := GalK K) (M := ZMod 2) := by
  let hcompat : ∀ (g : GalK K) (m : ZMod 2),
      maxProPMk 2 (GalK K) g • m = g • m :=
    fun g m ↦ (Count.smul_zmod2 (maxProPMk 2 (GalK K) g) m).trans
      (htriv_galK K g m).symm
  apply (maxProTwoH2CocycleDescent_iff_surjective_inf2 hcompat).2
  intro y
  obtain ⟨x, hx⟩ := (h2MaxProTwoEquivGalK (K := K)).surjective y
  refine ⟨x, ?_⟩
  rw [← h2MaxProTwoEquivGalK_apply]
  exact hx

/-- The precise kernel consequence of the existing arithmetic inflation equivalence: every
*ambient* scalar cocycle on `G_K` restricts to a continuous coboundary on the maximal-pro-`2`
kernel.  In particular this specializes to `K = ℚ₂`, the field occurring in the
`(h,q)=(0,2)` realization.

The quantifier remains over cocycles on `G_K`; it does not assert that every cocycle defined
intrinsically on the kernel extends to `G_K`.  That missing extension step is exactly why this
theorem is noncircular but does not close `MaxProTwoKernelScalarH2Vanishes`. -/
theorem galKScalarAmbientCocycleRestrictsToKernelCoboundary (z : Z2 (GalK K) (ZMod 2)) :
    ∃ phi : proPKernel 2 (GalK K) → ZMod 2, Continuous phi ∧
      ∀ k l : proPKernel 2 (GalK K),
        dOne (proPKernel 2 (GalK K)) (ZMod 2) phi (k, l) = z.1 (k.1, l.1) := by
  let hcompat : ∀ (g : GalK K) (m : ZMod 2),
      maxProPMk 2 (GalK K) g • m = g • m :=
    fun g m ↦ (Count.smul_zmod2 (maxProPMk 2 (GalK K) g) m).trans
      (htriv_galK K g m).symm
  exact h2CocycleInflationDescent_kernel_coboundary hcompat z
    (galKScalarMaxProTwoH2CocycleDescent z)

end

end GQ2.Dyadic

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

/-- The scalar maximal-pro-`2` kernel statement for the chosen `GammaL` Sylow preimage. -/
noncomputable abbrev GammaLSylowPreimageScalarKernelH2Vanishes
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  MaxProTwoKernelScalarH2Vanishes (G := U P)

/-- The remaining `GammaL` kernel theorem is exactly eventual finite-quotient splitting. -/
theorem gammaLSylowPreimageKernelH2Vanishes_iff_finiteRefinement
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageKernelH2VanishesSupply P ↔
      GammaLSylowPreimageKernelFiniteRefinementSupply P :=
  finiteElementaryMaxProTwoKernelH2VanishesSupply_iff_finiteRefinement

/-- The full finite-elementary kernel premise is exactly scalar kernel `H²`-vanishing. -/
theorem gammaLSylowPreimageKernelH2Vanishes_iff_scalar
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageKernelH2VanishesSupply P ↔
      GammaLSylowPreimageScalarKernelH2Vanishes P :=
  finiteElementaryMaxProTwoKernelH2VanishesSupply_iff_scalar

/-- Equivalently, all finite elementary refinement problems reduce to the scalar one. -/
theorem gammaLSylowPreimageKernelFiniteRefinement_iff_scalar
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageKernelFiniteRefinementSupply P ↔
      GammaLSylowPreimageScalarKernelH2Vanishes P :=
  finiteElementaryMaxProTwoKernelFiniteRefinementSupply_iff_scalar

/-- Finite-quotient splitting on the special kernel supplies the desired inflation theorem. -/
theorem gammaLSylowPreimageH2InflationSurjective_of_kernelFiniteRefinement
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (D : GammaLSylowPreimageKernelFiniteRefinementSupply P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (U P)) :=
  finiteElementaryH2InflationSurjective_of_kernelFiniteRefinement D

/-- Hence the single scalar kernel theorem supplies degree-two inflation for every finite
elementary quotient-compatible coefficient module. -/
theorem gammaLSylowPreimageH2InflationSurjective_of_scalarKernelH2Vanishes
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (D : GammaLSylowPreimageScalarKernelH2Vanishes P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (U P)) :=
  finiteElementaryH2InflationSurjective_of_kernelH2Vanishes
    (gammaLSylowPreimageKernelH2Vanishes_iff_scalar P |>.mpr D)

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

/-- At the Q₂ row the formerly uniform kernel premise is exactly one scalar
`H²(proPKernel 2 U, F₂)=0` statement. -/
theorem gammaLZeroTwoSylowPreimageKernelH2Vanishes_iff_scalar
    (P : Sylow 2 (PairFiniteActionImage (h := 0) (q := 2) (A := A) (B := B))) :
    GammaLSylowPreimageKernelH2VanishesSupply P ↔
      GammaLSylowPreimageScalarKernelH2Vanishes P :=
  gammaLSylowPreimageKernelH2Vanishes_iff_scalar P

/-- The honest `n=1` conclusion: the indicated finite-refinement premise implies the desired
maximal-pro-`2` inflation theorem for the Q₂ Sylow preimage. -/
theorem gammaLZeroTwoSylowPreimageH2InflationSurjective_of_kernelFiniteRefinement
    (P : Sylow 2 (PairFiniteActionImage (h := 0) (q := 2) (A := A) (B := B)))
    (D : GammaLSylowPreimageKernelFiniteRefinementSupply P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (UZeroTwo P)) :=
  gammaLSylowPreimageH2InflationSurjective_of_kernelFiniteRefinement P D

/-- The corresponding scalar-only Q₂ regression. -/
theorem gammaLZeroTwoSylowPreimageH2InflationSurjective_of_scalarKernelH2Vanishes
    (P : Sylow 2 (PairFiniteActionImage (h := 0) (q := 2) (A := A) (B := B)))
    (D : GammaLSylowPreimageScalarKernelH2Vanishes P) :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (UZeroTwo P)) :=
  gammaLSylowPreimageH2InflationSurjective_of_scalarKernelH2Vanishes P D

end ZeroTwo

end

end GQ2.Dyadic.LSquare
