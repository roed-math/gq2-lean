/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldPivotArtinValue

/-!
# Exact compact-M uniformizer Artin boundary

The W172 compact-M consumer used two explicit field inputs: placement of the transported
distinguished `D` class on the filtration-uniformizer Kummer class, and one Artin value.  This
module proves that, after the placement, the Artin value is not merely sufficient: it is exactly
equivalent to the intrinsic compact-M pivot.

Thus no weaker pivot theorem can be extracted from the current cup-form interface without either
changing the `D` placement or proving `M0UniformizerArtinCompatibility` itself.
-/

namespace GQ2.Dyadic.Instances.M0FieldPivotArtinExact

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.Instances.M0FieldPivotInvariant
open GQ2.Dyadic.Instances.M0FieldPivotArtinValue
open GQ2.Dyadic.LSquare.NuKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- Once transported `D` is the uniformizer Kummer class, the intrinsic compact-M pivot is
equivalent to the single uniformizer Artin value. -/
theorem m0FieldPivotUnit_iff_uniformizerArtinValue
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (hD : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldDCharacter e.1)) =
      kummerClassK K (piUnitK FF)) :
    M0FieldPivotUnit B alpha h ↔ M0UniformizerArtinCompatibility B FF := by
  rw [m0FieldPivotUnit_iff_cup B halpha e,
    m0UniformizerArtinCompatibility_iff_cup_one]
  unfold m0PivotCupValue
  rw [hD, (FieldData.isCupFormFp2_cupFormK K).symm]

#print axioms m0FieldPivotUnit_iff_uniformizerArtinValue

end
end GQ2.Dyadic.Instances.M0FieldPivotArtinExact
