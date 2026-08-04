/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageSchreier
import GQ2.Dyadic.LocalGauss.Q0
import GQ2.Dyadic.MaxProTwoCohomology
import GQ2.Dyadic.SqCore.Rank3

/-!
# The fixed-core obstruction at the Q2 row

The maximal pro-`2` quotient of an odd-index subgroup of `GammaL` need not be the fixed
square core.  This file proves the formal rank obstruction behind the unramified cubic
counterexample.

For a Sylow-`2` preimage `U`, the proposed kernel equality constructs

`U(2) ≃ DSq 0`.

Consequently it forces equality of the cardinalities of scalar `H¹`.  But `DSq 0` is the frozen
rank-three Roe core and has `#H¹ = 8`, while the maximal pro-`2` Galois group of a degree-three
dyadic field has `#H¹ = 2^(3+2) = 32`.  Therefore any identification of `U(2)` with that Galois
group disproves the fixed-core kernel equality.

The only input not constructed here is the geometric identification of the particular
coefficient-action Sylow preimage with the Galois group of the degree-three fixed field.  The
repository contains the order-three irreducible action on `F₂²` (`NpcJet.PinC`/`PinV`) and the
full tame quotient of `GammaL`; however, the available unconditional equivalence
`gamma 0 2 ≃ G_Q2` does not expose compatibility with the full (odd as well as pro-`2`)
unramified quotient.  The theorem `not_gammaLZeroTwo_fixedCore_of_degreeThreeModel` below makes
that exact remaining premise explicit and proves all group/cohomology/rank consequences.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction (gamma 0 2 : Type) A]
  [ContinuousSMul (gamma 0 2 : Type) A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
  [DistribMulAction (gamma 0 2 : Type) B]
  [ContinuousSMul (gamma 0 2 : Type) B]

local notation "rhoAB" =>
  pairFiniteActionImageHom (h := 0) (q := 2) (A := A) (B := B)

local notation "U" P => sylowTwoPreimage rhoAB P

/-! ## Pure H1 obstruction -/

/-- Kernel equality forces the scalar `H¹` cardinality of the Sylow preimage's maximal
pro-`2` quotient to equal that of the fixed square core. -/
theorem gammaLZeroTwo_H1_card_eq_fixedCore_of_kernelEquality
    (P : Sylow 2 (PairFiniteActionImage (h := 0) (q := 2) (A := A) (B := B)))
    (hker : GammaLSylowPreimageProTwoKernelEquality P) :
    letI : DistribMulAction (maxProPQuotient 2 (U P)) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul (maxProPQuotient 2 (U P)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    letI : DistribMulAction (SqCore.DSq 0 : Type) (ZMod 2) := scalarActionZmodTwo _
    letI : ContinuousSMul (SqCore.DSq 0 : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    Nat.card (H1 (maxProPQuotient 2 (U P)) (ZMod 2)) =
      Nat.card (H1 (SqCore.DSq 0 : Type) (ZMod 2)) := by
  letI : DistribMulAction (maxProPQuotient 2 (U P)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (maxProPQuotient 2 (U P)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction (SqCore.DSq 0 : Type) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (SqCore.DSq 0 : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let e := gammaLSylowPreimageMaxProTwoCoreEquiv (by decide) (by decide) P hker
  let eH1 := H1congrGroup e (AddEquiv.refl (ZMod 2)) continuous_id continuous_id (by
    intro g m
    change m = m
    rfl)
  exact Nat.card_congr eH1.toEquiv

/-- Any unequal scalar-`H¹` cardinalities disprove the fixed-core kernel equality. -/
theorem not_gammaLZeroTwo_kernelEquality_of_H1_card_ne
    (P : Sylow 2 (PairFiniteActionImage (h := 0) (q := 2) (A := A) (B := B)))
    (hcard :
      letI : DistribMulAction (maxProPQuotient 2 (U P)) (ZMod 2) :=
        scalarActionZmodTwo _
      letI : ContinuousSMul (maxProPQuotient 2 (U P)) (ZMod 2) :=
        scalarActionZmodTwo_continuousSMul _
      letI : DistribMulAction (SqCore.DSq 0 : Type) (ZMod 2) := scalarActionZmodTwo _
      letI : ContinuousSMul (SqCore.DSq 0 : Type) (ZMod 2) :=
        scalarActionZmodTwo_continuousSMul _
      Nat.card (H1 (maxProPQuotient 2 (U P)) (ZMod 2)) ≠
        Nat.card (H1 (SqCore.DSq 0 : Type) (ZMod 2))) :
    ¬ GammaLSylowPreimageProTwoKernelEquality P := by
  intro hker
  exact hcard (gammaLZeroTwo_H1_card_eq_fixedCore_of_kernelEquality P hker)

/-! ## Degree-three local-field model -/

/-- The fixed square core at `h=0` has eight scalar `H¹` classes. -/
theorem card_H1_dsqZero :
    letI : DistribMulAction (SqCore.DSq 0 : Type) (ZMod 2) := scalarActionZmodTwo _
    letI : ContinuousSMul (SqCore.DSq 0 : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    Nat.card (H1 (SqCore.DSq 0 : Type) (ZMod 2)) = 8 := by
  letI : DistribMulAction (SqCore.DSq 0 : Type) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (SqCore.DSq 0 : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let eH1 := H1congrGroup SqCore.dsqEquivDR (AddEquiv.refl (ZMod 2))
    continuous_id continuous_id (by
      intro g m
      change m = m
      rfl)
  rw [Nat.card_congr eH1.toEquiv]
  exact GQ2.card_H1_DR

/-- A degree-three dyadic field has 32 scalar `H¹` classes on its maximal pro-`2` Galois
group.  This is the repository's local Euler-characteristic theorem specialized to degree
three. -/
theorem card_H1_maxProTwoGalK_degreeThree
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hdeg : Module.finrank ℚ_[2] K = 3) :
    letI : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 32 := by
  letI : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  rw [card_H1_zmodTwo_maxProTwoGalK, hdeg]
  norm_num

/-- **The formal unramified-cubic counterexample.**  Suppose the chosen coefficient-action
Sylow preimage has maximal pro-`2` quotient equal to that of a degree-three dyadic field (for
the intended example, the unramified cubic extension of `Q2`).  Then its scalar `H¹` has 32
elements, whereas `DSq 0` has eight, so the fixed-core kernel equality is false.

Thus the remaining assembly problem is exactly to construct `eU` for the explicit tame
order-three action; no further Reidemeister--Schreier or cohomological argument is missing. -/
theorem not_gammaLZeroTwo_fixedCore_of_degreeThreeModel
    (P : Sylow 2 (PairFiniteActionImage (h := 0) (q := 2) (A := A) (B := B)))
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hdeg : Module.finrank ℚ_[2] K = 3)
    (eU : ContinuousMulEquiv
      (maxProPQuotient 2 (U P)) (maxProPQuotient 2 (GalK K))) :
    ¬ GammaLSylowPreimageProTwoKernelEquality P := by
  letI : DistribMulAction (maxProPQuotient 2 (U P)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (maxProPQuotient 2 (U P)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : DistribMulAction (SqCore.DSq 0 : Type) (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul (SqCore.DSq 0 : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  apply not_gammaLZeroTwo_kernelEquality_of_H1_card_ne P
  let eH1 := H1congrGroup eU (AddEquiv.refl (ZMod 2)) continuous_id continuous_id (by
    intro g m
    change m = m
    rfl)
  have hUcard : Nat.card (H1 (maxProPQuotient 2 (U P)) (ZMod 2)) = 32 := by
    rw [Nat.card_congr eH1.toEquiv]
    exact card_H1_maxProTwoGalK_degreeThree hdeg
  rw [hUcard, card_H1_dsqZero]
  decide

end

end GQ2.Dyadic.LSquare
