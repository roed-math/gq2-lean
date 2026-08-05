/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteVariableStageTwo
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteLevelThreeBase

/-!
# The forward presentation capstone over the kernel-adapted supply

The level-three base of the forward capstone is a theorem
(`oddDegree_sqCyclotomicStageTuple_levelThree`), and the variable-stage lane reduces the
all-stage residual premise to the kernel-adapted raw supply
(`oddDegreeGalKSq_allStagePrimitiveResidualVanishing`).  Composing the two through
`nonempty_orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing` gives the
forward presentation theorem for every odd-degree ramified field over the single remaining
arithmetic hypothesis `SqKernelAdaptedDefectSupply K ((finrank - 1) / 2)`:

* every core character row of that hypothesis is discharged internally (the `σ`/`x₀` moves,
  the automatic `x₁` digit, and the central fresh-digit flips are theorems);
* at `h = 0` the hypothesis is exactly raw Labute reachability, which holds at the bottom
  field; the full-circle regression below reproduces the oriented `Q₂` classification through
  the *new* route, certifying that the reduction chain is consistent and correctly oriented.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **The forward presentation theorem over the kernel-adapted supply.**  For an odd-degree
field, the kernel-adapted raw supply at its handle count is the only remaining input: the
level-three stage base is unconditional, and the sharp correction chain turns the supply into
the primitive-residual premise of the direct rigidity capstone. -/
theorem nonempty_orientedEquiv_oddDegree_of_kernelAdaptedSupply
    {K : IntermediateField ℚ_[2] ℚ̄₂}
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hsupply : SqKernelAdaptedDefectSupply K ((Module.finrank ℚ_[2] K - 1) / 2)) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) := by
  obtain ⟨base⟩ := oddDegree_sqCyclotomicStageTuple_levelThree K hodd
  exact nonempty_orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing hodd base
    (oddDegreeGalKSq_allStagePrimitiveResidualVanishing hodd Hsupply)

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Full-circle regression through the new route: at the bottom field the kernel-adapted
supply is a theorem, and the capstone over it reproduces the oriented rank-one
classification. -/
theorem nonempty_orientedEquiv_bot_of_kernelAdaptedSupply :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2]
        (⊥ : IntermediateField ℚ_[2] ℚ̄₂) - 1) / 2))
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂)))) := by
  have hodd : Odd (Module.finrank ℚ_[2]
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) := by
    rw [IntermediateField.finrank_bot]
    exact odd_one
  have hhandles : ((Module.finrank ℚ_[2]
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂) - 1) / 2) = 0 := by
    simp [IntermediateField.finrank_bot]
  refine nonempty_orientedEquiv_oddDegree_of_kernelAdaptedSupply hodd ?_
  rw [hhandles]
  exact sqKernelAdaptedDefectSupply_bot

#print axioms nonempty_orientedEquiv_oddDegree_of_kernelAdaptedSupply
#print axioms nonempty_orientedEquiv_bot_of_kernelAdaptedSupply

end

end GQ2.Dyadic.LSquare
