/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqTateDualityCapstone
import GQ2.Dyadic.Instances.GammaLSylowPreimageBurnside
import GQ2.Dyadic.Instances.GammaLSylowPreimageKernelFiniteLevel

/-!
# Finite arithmetic form of the two residual GammaL inputs

The square-core route to `TateDualityG (gamma h q : Type) 2` leaves two inputs at every
simultaneous coefficient-action image:

* `H²`-vanishing for the kernel of the maximal pro-`2` quotient of a Sylow preimage;
* equality between that intrinsic kernel and the pullback of the ambient pro-`2` kernel.

This file puts both inputs into their strongest currently available concrete forms.  The first
is equivalent both to eventual finite-quotient splitting and to scalar cup-generation.  The
second is equivalent to finite normal-core `2`-residual separation.  Thus the combined supply is
equivalent to one finite cohomological condition and one finite group-theoretic condition, for
the *same* chosen Sylow subgroup.

There is also a sufficient constructor using the more explicit normal-closure Burnside checks.
Those checks are not claimed necessary: normal-core residual separation is the exact boundary,
whereas the Burnside package is a usable way of proving it.

At `(h,q)=(0,2)`, the existing field realization proves Tate duality for `gamma 0 2`, but it does
not prove either member of this stronger Sylow-preimage supply.  The final regression below
specializes the exact finite reduction to that row.  In particular, the Q2 theorem does not
silently supply norm-residue generation on the generally infinite maximal pro-`2` fixed field,
nor does it identify maximal pro-`2` quotients of arbitrary odd-index Sylow preimages with the
fixed four-generator square core.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {h q : ℕ}

/-! ## Scalar cup-generation is exact on a maximal-pro-two kernel -/

/-- Vanishing scalar `H²` trivially implies cup-generation (use an empty sum).  Combined with
the already-proved intrinsic scalar `H¹`-vanishing of a maximal-pro-`2` kernel, this makes
cup-generation equivalent to scalar `H²`-vanishing in this special setting. -/
theorem maxProTwoKernelScalarH2CupGenerated_of_vanishes
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hzero : MaxProTwoKernelScalarH2Vanishes (G := G)) :
    MaxProTwoKernelScalarH2CupGenerated (G := G) := by
  letI : DistribMulAction (proPKernel 2 G) (ZMod 2) :=
    trivialAddAction (M := ZMod 2) (proPKernel 2 G)
  letI : ContinuousSMul (proPKernel 2 G) (ZMod 2) :=
    continuousSMul_trivialAddAction (M := ZMod 2) (proPKernel 2 G)
  intro z
  refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
  simpa using hzero z

/-- Exact scalar formulation of maximal-pro-`2` kernel acyclicity. -/
theorem maxProTwoKernelScalarH2Vanishes_iff_cupGenerated
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    MaxProTwoKernelScalarH2Vanishes (G := G) ↔
      MaxProTwoKernelScalarH2CupGenerated (G := G) := by
  constructor
  · exact maxProTwoKernelScalarH2CupGenerated_of_vanishes
  · exact maxProTwoKernelScalarH2Vanishes_of_cupGenerated

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

/-- For a fixed action-image Sylow preimage, the uniform kernel `H²` premise is exactly scalar
cup-generation on its maximal-pro-`2` kernel. -/
theorem gammaLSylowPreimageKernelH2Vanishes_iff_cupGenerated
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageKernelH2VanishesSupply P ↔
      GammaLSylowPreimageScalarKernelH2CupGenerated P :=
  (gammaLSylowPreimageKernelH2Vanishes_iff_scalar P).trans
    maxProTwoKernelScalarH2Vanishes_iff_cupGenerated

/-! ## Pointwise combined reductions -/

/-- Exact finite formulation of both residual inputs at one chosen Sylow subgroup. -/
theorem gammaLSylowPreimage_kernelH2AndCoreEquality_iff_finiteResiduals
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    (GammaLSylowPreimageKernelH2VanishesSupply P ∧
        GammaLSylowPreimageProTwoKernelEquality P) ↔
      (GammaLSylowPreimageKernelFiniteRefinementSupply P ∧
        GammaLSylowPreimageNormalCoreTwoResidualSeparation P) := by
  rw [gammaLSylowPreimageKernelH2Vanishes_iff_finiteRefinement P,
    gammaLSylowPreimageProTwoKernelEquality_iff_normalCoreTwoResidualSeparation hq2 hqe P]

/-- Equivalent norm-residue/normal-core formulation of both residual inputs. -/
theorem gammaLSylowPreimage_kernelH2AndCoreEquality_iff_cupAndNormalCore
    (hq2 : 2 ≤ q) (hqe : Even q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    (GammaLSylowPreimageKernelH2VanishesSupply P ∧
        GammaLSylowPreimageProTwoKernelEquality P) ↔
      (GammaLSylowPreimageScalarKernelH2CupGenerated P ∧
        GammaLSylowPreimageNormalCoreTwoResidualSeparation P) := by
  rw [gammaLSylowPreimageKernelH2Vanishes_iff_cupGenerated P,
    gammaLSylowPreimageProTwoKernelEquality_iff_normalCoreTwoResidualSeparation hq2 hqe P]

/-- A scalar norm-residue input plus the explicit normal-closure Burnside checks proves both
residual inputs at the chosen Sylow subgroup. -/
theorem gammaLSylowPreimage_kernelH2AndCoreEquality_of_cupAndBurnside
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hcup : GammaLSylowPreimageScalarKernelH2CupGenerated P)
    (hburn : GammaLSylowPreimageNormalClosureBurnsideSupply P) :
    GammaLSylowPreimageKernelH2VanishesSupply P ∧
      GammaLSylowPreimageProTwoKernelEquality P :=
  ⟨gammaLSylowPreimageKernelH2VanishesSupply_of_cupGenerated P hcup,
    gammaLSylowPreimageProTwoKernelEquality_of_normalClosureBurnside P hburn⟩

/-! ## Uniform supplies -/

/-- The exact finite residual supply: eventual finite splitting for kernel `H²`, and normal-core
`2`-residual separation, with one common choice of action-image Sylow subgroup. -/
noncomputable abbrev GammaLSylowPreimageFiniteArithmeticResidualSupply
    (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B],
      ∃ P : Sylow 2
          (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)),
        GammaLSylowPreimageKernelFiniteRefinementSupply P ∧
          GammaLSylowPreimageNormalCoreTwoResidualSeparation P

/-- The equivalent norm-residue formulation of the exact residual supply. -/
noncomputable abbrev GammaLSylowPreimageCupNormalCoreResidualSupply
    (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B],
      ∃ P : Sylow 2
          (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)),
        GammaLSylowPreimageScalarKernelH2CupGenerated P ∧
          GammaLSylowPreimageNormalCoreTwoResidualSeparation P

/-- A more concrete sufficient supply, replacing the exact normal-core condition by the three
normal-closure/Burnside checks at every intrinsic finite `2`-quotient. -/
noncomputable abbrev GammaLSylowPreimageCupBurnsideResidualSupply
    (h q : ℕ) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [DiscreteTopology B] [Finite B]
    [DistribMulAction (gamma h q : Type) B] [ContinuousSMul (gamma h q : Type) B],
      ∃ P : Sylow 2
          (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)),
        GammaLSylowPreimageScalarKernelH2CupGenerated P ∧
          GammaLSylowPreimageNormalClosureBurnsideSupply P

/-- The original combined residual supply is exactly the finite-refinement/normal-core supply. -/
theorem gammaLSylowPreimageKernelH2AndCoreEqualitySupply_iff_finiteArithmeticResiduals
    (hq2 : 2 ≤ q) (hqe : Even q) :
    GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q ↔
      GammaLSylowPreimageFiniteArithmeticResidualSupply h q := by
  constructor
  · intro R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨P, hP⟩ := R A B
    exact ⟨P,
      (gammaLSylowPreimage_kernelH2AndCoreEquality_iff_finiteResiduals
        hq2 hqe P).mp hP⟩
  · intro R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨P, hP⟩ := R A B
    exact ⟨P,
      (gammaLSylowPreimage_kernelH2AndCoreEquality_iff_finiteResiduals
        hq2 hqe P).mpr hP⟩

/-- Equivalently, the cohomological half is scalar cup-generation and the group-theoretic half
is normal-core `2`-residual separation. -/
theorem gammaLSylowPreimageKernelH2AndCoreEqualitySupply_iff_cupNormalCore
    (hq2 : 2 ≤ q) (hqe : Even q) :
    GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q ↔
      GammaLSylowPreimageCupNormalCoreResidualSupply h q := by
  constructor
  · intro R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨P, hP⟩ := R A B
    exact ⟨P,
      (gammaLSylowPreimage_kernelH2AndCoreEquality_iff_cupAndNormalCore
        hq2 hqe P).mp hP⟩
  · intro R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨P, hP⟩ := R A B
    exact ⟨P,
      (gammaLSylowPreimage_kernelH2AndCoreEquality_iff_cupAndNormalCore
        hq2 hqe P).mpr hP⟩

/-- The explicit cup/Burnside certificate supply constructs the two residual inputs. -/
theorem gammaLSylowPreimageKernelH2AndCoreEqualitySupply_of_cupBurnside
    (R : GammaLSylowPreimageCupBurnsideResidualSupply h q) :
    GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨P, hcup, hburn⟩ := R A B
  exact ⟨P,
    gammaLSylowPreimage_kernelH2AndCoreEquality_of_cupAndBurnside P hcup hburn⟩

/-- End-to-end square-core constructor using only the scalar norm-residue and finite Burnside
forms of the two ambient residual inputs. -/
noncomputable def tateDualityG_of_sqCoreAndSylowCupBurnsideResiduals
    (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (R : GammaLSylowPreimageCupBurnsideResidualSupply h q)
    (hcore : FiniteElementaryH2RightExactSupply (SqCore.DSq h : Type)) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sqCoreAndSylowKernelResiduals hq2 hqe
    (gammaLSylowPreimageKernelH2AndCoreEqualitySupply_of_cupBurnside R) hcore

/-! ## The Q2 row -/

/-- At `(h,q)=(0,2)`, the residual supply remains exactly the same pair of finite problems.
This is the base-case regression: the separately formalized Q2 Tate-duality theorem does not
alter or discharge this stronger intermediate proposition. -/
theorem gammaLZeroTwoKernelH2AndCoreEqualitySupply_iff_finiteArithmeticResiduals :
    GammaLSylowPreimageKernelH2AndCoreEqualitySupply 0 2 ↔
      GammaLSylowPreimageFiniteArithmeticResidualSupply 0 2 :=
  gammaLSylowPreimageKernelH2AndCoreEqualitySupply_iff_finiteArithmeticResiduals
    (by decide) (by decide)

/-- Norm-residue/normal-core spelling of the same Q2-row boundary. -/
theorem gammaLZeroTwoKernelH2AndCoreEqualitySupply_iff_cupNormalCore :
    GammaLSylowPreimageKernelH2AndCoreEqualitySupply 0 2 ↔
      GammaLSylowPreimageCupNormalCoreResidualSupply 0 2 :=
  gammaLSylowPreimageKernelH2AndCoreEqualitySupply_iff_cupNormalCore
    (by decide) (by decide)

end

end GQ2.Dyadic.LSquare
