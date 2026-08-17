/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldPivotArtin

/-!
# The single Artin value needed by the compact-M pivot

The compact-M pivot does not require the full pointwise Tate--Kummer--Artin theorem.  It uses
only the equation obtained by evaluating the mod-two unramified character on reciprocity of one
filtration uniformizer.  This module isolates that exact value, proves that it is equivalent to
the one cup value needed by the pivot, and exports the corresponding selected corrected-RN
consumer.

Thus the M0 arithmetic frontier is strictly smaller than a full local-CFT compatibility packet:
uniformizer placement of transported `D` plus `M0UniformizerArtinCompatibility` suffices.
-/

namespace GQ2.Dyadic.Instances.M0FieldPivotArtinValue

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.Instances.M0FieldPivotInvariant
open GQ2.Dyadic.Instances.M0FieldPivotArtin
open GQ2.Dyadic.Instances.M0FieldPivotUniformizer
open GQ2.Dyadic.LSquare.NuKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The single Artin--Kummer equation used by the compact-M uniformizer pivot. -/
def M0UniformizerArtinCompatibility
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) : Prop :=
  let x := h1MaxProTwoEquivGalK (K := K)
    (evenModelCharacterClass (m0FieldNuCharacter B))
  h1GalKMaxProTwoAbCharacter (K := K) x
      (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip (piUnitK FF))) =
    Multiplicative.ofAdd (FieldData.cupFormK K x (kummerClassK K (piUnitK FF)))

/-- The full mod-two Artin--Kummer compatibility implies its uniformizer specialization. -/
theorem m0UniformizerArtinCompatibility_of_modTwo
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (H : ModTwoTateKummerArtinCompatibility B) :
    M0UniformizerArtinCompatibility B FF :=
  H _ _

/-- The uniformizer Artin equation is exactly nonvanishing of the required unramified cup. -/
theorem m0UniformizerArtinCompatibility_iff_cup_one
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) :
    M0UniformizerArtinCompatibility B FF ↔
      FieldData.cupFormK K
        (h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldNuCharacter B)))
        (kummerClassK K (piUnitK FF)) = 1 := by
  change
    h1GalKMaxProTwoAbCharacter (K := K)
        (h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldNuCharacter B)))
        (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip (piUnitK FF))) =
      Multiplicative.ofAdd (FieldData.cupFormK K
        (h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldNuCharacter B)))
        (kummerClassK K (piUnitK FF))) ↔ _
  rw [m0FieldNuCharacter_recip_piUnitK]
  constructor
  · intro h
    exact (congrArg Multiplicative.toAdd h).symm
  · intro h
    rw [h]

/-- Uniformizer placement of transported `D` and the single Artin value force the M0 pivot. -/
theorem m0FieldPivotUnit_of_uniformizerD_of_artinValue
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (hD : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldDCharacter e.1)) =
      kummerClassK K (piUnitK FF))
    (H : M0UniformizerArtinCompatibility B FF) :
    M0FieldPivotUnit B alpha h := by
  rw [m0FieldPivotUnit_iff_cup B halpha e, m0PivotCupValue, hD,
    (FieldData.isCupFormFp2_cupFormK K).symm]
  exact (m0UniformizerArtinCompatibility_iff_cup_one B FF).mp H

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The selected corrected-RN residual from uniformizer placement of `D` and one Artin value. -/
theorem m0RowResidualRN_of_familySelection_of_uniformizerD_artinValue
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.M0 alpha))) (chiCycKTwo (K := K)))
    (hD : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldDCharacter e.1)) =
      kummerClassK K (piUnitK FF))
    (H : M0UniformizerArtinCompatibility B FF) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have halpha := S.valid
  rw [hbranch] at halpha
  exact m0RowResidualRN_of_familySelection_of_fieldPivot B FF S hbranch
    (m0FieldPivotUnit_of_uniformizerD_of_artinValue B FF halpha e hD H)

#print axioms M0UniformizerArtinCompatibility
#print axioms m0UniformizerArtinCompatibility_of_modTwo
#print axioms m0UniformizerArtinCompatibility_iff_cup_one
#print axioms m0FieldPivotUnit_of_uniformizerD_of_artinValue
#print axioms m0RowResidualRN_of_familySelection_of_uniformizerD_artinValue

end
end GQ2.Dyadic.Instances.M0FieldPivotArtinValue
