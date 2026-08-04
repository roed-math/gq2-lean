/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageInflationKernel

/-!
# Variable-rank cores for GammaL Sylow preimages

The maximal pro-`2` quotient of an odd-index open subgroup of a local Demushkin group is not
expected to have the same generator rank as the ambient maximal pro-`2` quotient.  If the
ambient square core has rank `3 + 2h` and the subgroup has odd index `d`, the expected
Reidemeister--Schreier rank is

`2 + d * ((3 + 2h) - 2) = 2 + d * (1 + 2h)`.

This is again of square-core form `3 + 2h'`, with

`h' = (d * (1 + 2h) - 1) / 2`.

The old condition `GammaLSylowPreimageProTwoKernelEquality` instead forces the canonical
surjection onto the *fixed* core `DSq h` to be an isomorphism.  It is retained elsewhere as a
sharp criterion for that unusually strong assertion, but it is not the presentation input used
here.

This file proves all available index and numerical facts unconditionally.  The genuinely
arithmetic/group-theoretic missing theorem is isolated as
`GammaLSylowPreimageVariableCorePresentation`: an equivalence between the preimage's maximal
pro-`2` quotient and `DSq h'` at the computed handle count.  No such equivalence is asserted
without being supplied.  Once it is supplied, the existing square-core CD-2 theorem transports
honestly and feeds the Tate-duality devissage.
-/

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

/-! ## Index and handle-count arithmetic -/

/-- The expected handle count for an arbitrary finite-index open subgroup of `GammaL`.  The
oddness premise needed to make the displayed quotient exact is kept on the theorems that use
this definition. -/
def gammaLOpenSubgroupHandleCount (U' : Subgroup (gamma h q : Type)) : ℕ :=
  (U'.index * (1 + 2 * h) - 1) / 2

/-- The actual finite index of the Sylow preimage. -/
def gammaLSylowPreimageIndex
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : ℕ :=
  (U P).index

/-- The handle count predicted by the Demushkin open-subgroup rank formula. -/
def gammaLSylowPreimageHandleCount
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : ℕ :=
  gammaLOpenSubgroupHandleCount (U P)

/-- The preimage index agrees with the finite Sylow index. -/
theorem gammaLSylowPreimageIndex_eq_sylowIndex
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    gammaLSylowPreimageIndex P = P.index :=
  sylowTwoPreimage_index rhoAB pairFiniteActionImageHom_surjective P

/-- In particular, the index used in the variable-rank formula is odd. -/
theorem odd_gammaLSylowPreimageIndex
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    Odd (gammaLSylowPreimageIndex P) :=
  odd_sylowTwoPreimage_index rhoAB pairFiniteActionImageHom_surjective P

/-- At index one the variable-core handle count specializes back to the ambient handle count. -/
theorem gammaLSylowPreimageHandleCount_eq_of_index_one
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hindex : gammaLSylowPreimageIndex P = 1) :
    gammaLSylowPreimageHandleCount P = h := by
  change (U P).index = 1 at hindex
  rw [gammaLSylowPreimageHandleCount, gammaLOpenSubgroupHandleCount, hindex]
  omega

/-- The computed handle count has exactly the expected open-subgroup rank. -/
theorem gammaLSylowPreimageHandleCount_rank
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    3 + 2 * gammaLSylowPreimageHandleCount P =
      2 + gammaLSylowPreimageIndex P * (1 + 2 * h) := by
  obtain ⟨k, hk⟩ := odd_gammaLSylowPreimageIndex P
  change (U P).index = 2 * k + 1 at hk
  have hprod : (2 * k + 1) * (1 + 2 * h) =
      2 * (2 * k * h + k + h) + 1 := by ring
  rw [gammaLSylowPreimageHandleCount, gammaLOpenSubgroupHandleCount,
    gammaLSylowPreimageIndex, hk, hprod]
  rw [Nat.add_sub_cancel,
    Nat.mul_div_right _ (by norm_num : 0 < 2)]
  ring

/-- Reidemeister--Schreier form of the same calculation, using `sqRank` on both sides. -/
theorem sqRank_gammaLSylowPreimageHandleCount
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    SqCore.sqRank (gammaLSylowPreimageHandleCount P) =
      2 + gammaLSylowPreimageIndex P * (SqCore.sqRank h - 2) := by
  have hrank : SqCore.sqRank h - 2 = 1 + 2 * h := by
    simp only [SqCore.sqRank]
    omega
  rw [hrank]
  exact gammaLSylowPreimageHandleCount_rank P

/-! ## The honest variable-core presentation boundary -/

/-- The corrected presentation statement for one action-image Sylow preimage.

It asks for an actual topological group equivalence with the square core at the handle count
dictated by the odd subgroup index.  This is the exact missing local-field/Demushkin
open-subgroup theorem; it is deliberately a premise, not a definitionally manufactured map. -/
def GammaLSylowPreimageVariableCorePresentation
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) : Prop :=
  Nonempty (ContinuousMulEquiv
    (maxProPQuotient 2 (U P))
    (SqCore.DSq (gammaLSylowPreimageHandleCount P)))

/-- The natural group-theoretic theorem which would supply the pointwise presentation above:
every odd-index open subgroup of `GammaL` has the variable-rank square presentation predicted by
the Demushkin Schreier formula.

For an arithmetic realization of `GammaL`, this is the exact place to use Galois
correspondence, the degree formula for the corresponding finite extension, and the local-field
Demushkin presentation theorem.  None of those steps is currently exposed by the repository as
one theorem. -/
def GammaLOddIndexOpenSubgroupVariableCorePresentationSupply (h q : ℕ) : Prop :=
  ∀ (U' : Subgroup (gamma h q : Type)) [CompactSpace U'],
    IsOpen (U' : Set (gamma h q : Type)) → Odd U'.index →
      Nonempty (ContinuousMulEquiv
        (maxProPQuotient 2 U')
        (SqCore.DSq (gammaLOpenSubgroupHandleCount U')))

/-- The open-subgroup presentation theorem specializes immediately to every coefficient-action
Sylow preimage. -/
theorem gammaLSylowPreimageVariableCorePresentation_of_oddIndexOpenSubgroups
    (S : GammaLOddIndexOpenSubgroupVariableCorePresentationSupply h q)
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B))) :
    GammaLSylowPreimageVariableCorePresentation P :=
  S (U P) (isOpen_sylowTwoPreimage rhoAB P)
    (odd_sylowTwoPreimage_index rhoAB pairFiniteActionImageHom_surjective P)

/-- A supplied variable-core presentation transports the square-core finite-elementary CD-2
tail to the maximal pro-`2` quotient of the actual Sylow preimage. -/
theorem gammaLSylowPreimageMaxProTwoCDTwo_of_variableCorePresentation
    (P : Sylow 2 (PairFiniteActionImage (h := h) (q := q) (A := A) (B := B)))
    (hpresentation : GammaLSylowPreimageVariableCorePresentation P)
    (hcore : ∀ h' : ℕ,
      FiniteElementaryH2RightExactSupply (SqCore.DSq h' : Type)) :
    FiniteElementaryH2RightExactSupply (maxProPQuotient 2 (U P)) := by
  obtain ⟨e⟩ := hpresentation
  exact finiteTwoH2RightExactSupply_congr e
    (hcore (gammaLSylowPreimageHandleCount P))

/-! ## Uniform supply and Tate-duality adapter -/

/-- The two honest residual inputs at every coefficient-action image:

* `H²`-vanishing on the maximal-pro-`2` kernel of a chosen Sylow preimage;
* the variable-rank presentation of that preimage's maximal pro-`2` quotient.

Unlike the fixed-core supply, this statement allows the core rank to grow with the odd index. -/
noncomputable abbrev GammaLSylowPreimageKernelH2AndVariableCoreSupply
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
          GammaLSylowPreimageVariableCorePresentation P

/-- Variable square-core presentations and uniform square-core CD-2 fill the exact maximal
pro-`2` package used by the Sylow-preimage devissage. -/
theorem gammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply_of_variableCore
    (R : GammaLSylowPreimageKernelH2AndVariableCoreSupply h q)
    (hcore : ∀ h' : ℕ,
      FiniteElementaryH2RightExactSupply (SqCore.DSq h' : Type)) :
    GammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply h q := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨P, hH2, hpresentation⟩ := R A B
  let U' := sylowTwoPreimage
    (pairFiniteActionImageHom (h := h) (q := q) (A := A) (B := B)) P
  have hinf : FiniteElementaryMaxProTwoKernelOneTwoSupply (G := U') :=
    finiteElementaryMaxProTwoKernelOneTwoSupply_of_h2Vanishes_transgression hH2
      (finiteElementaryMaxProTwoKernelTransgression (G := U'))
  exact ⟨P, {
    inflationKernel := hinf
    cdTwo := gammaLSylowPreimageMaxProTwoCDTwo_of_variableCorePresentation
      P hpresentation hcore }⟩

/-- Corrected end-to-end endpoint: Tate duality follows from square-core CD-2 uniformly in the
handle count and the two honest Sylow-preimage residual statements.  No fixed-core kernel
equality and no spurious `2 ≤ q` premise occurs. -/
noncomputable def tateDualityG_of_variableCoreAndSylowKernelResiduals
    (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (R : GammaLSylowPreimageKernelH2AndVariableCoreSupply h q)
    (hcore : ∀ h' : ℕ,
      FiniteElementaryH2RightExactSupply (SqCore.DSq h' : Type)) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sylowPreimageMaxProTwoKernelOneTwoCDTwo hqe
    (gammaLSylowPreimageMaxProTwoKernelOneTwoCDTwoSupply_of_variableCore R hcore)

#print axioms gammaLSylowPreimageHandleCount_rank
#print axioms sqRank_gammaLSylowPreimageHandleCount
#print axioms gammaLSylowPreimageMaxProTwoCDTwo_of_variableCorePresentation
#print axioms tateDualityG_of_variableCoreAndSylowKernelResiduals

end

end GQ2.Dyadic.LSquare
