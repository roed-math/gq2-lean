/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteFrattiniFrame
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteLevelThreeTransgression

/-!
# The unconditional arbitrary odd-degree level-three stage

Both finite supplies of the level-three seed are now theorems:
`oddDegreeSqCyclotomicFrattiniFrameSupply_holds` constructs a cup-adapted Frattini frame for
every odd-degree field, and `oddDegreeSqLevelThreeRelationRealization` kills the improved word
modulo `λ₃` on every such frame.  Composing them through the seed reduction gives the
level-three stage base of the direct forward rigidity capstone with no remaining hypothesis.
The only open input of
`nonempty_orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing` is therefore
the all-stage residual supply for `k ≥ 3`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The arbitrary odd-degree level-three stage, over the caller's marked bundle and nothing
else.  `B` replaces what used to be an application of the axiom `markedRecipAt` (B5-K) inside
the frame supply; every endpoint downstream already carries a bundle, so no endpoint statement
changes and B5-K leaves the odd-degree forward route entirely. -/
theorem oddDegree_sqCyclotomicStageTuple_levelThree
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    Nonempty (SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) 3) :=
  oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization
    oddDegreeSqCyclotomicFrattiniFrameSupply_holds
    oddDegreeSqLevelThreeRelationRealization K B hodd

#print axioms oddDegree_sqCyclotomicStageTuple_levelThree

end

end GQ2.Dyadic.LSquare
