/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldPivotUniformizer
import GQ2.Dyadic.FiniteTwoLocalReciprocityTateKummer

/-!
# The compact-M pivot from Artin--Kummer compatibility

The compact-M pivot is the cup of the transported distinguished `D` class with the mod-two
unramified character.  If the `D` class is the Kummer class of a filtration uniformizer, the
pointwise Artin--Kummer formula evaluates that cup directly: marked reciprocity sends the
uniformizer to unramified value `-1`, hence to the nonzero class modulo two.

This removes the separate premise identifying the unramified character with the Kummer class
of an unramified quadratic extension.  The remaining field-side inputs are exactly placement
of transported `D` on the uniformizer class and the pointwise Artin--Kummer compatibility.
-/

namespace GQ2.Dyadic.Instances.M0FieldPivotArtin

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.Instances.M0FieldPivotInvariant
open GQ2.Dyadic.Instances.M0FieldPivotUniformizer
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism
open GQ2.Dyadic.LSquare.NuKummer
open scoped GQ2.SectionThree.TopAbInstances

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] in
/-- Evaluation of an even-model character class on the original field Galois group. -/
theorem h1GalKCharacter_h1Max_evenModelCharacterClass
    (c : ContinuousMonoidHom
      (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)))
    (g : GalK K) :
    h1GalKCharacter (K := K)
        (h1MaxProTwoEquivGalK (K := K) (evenModelCharacterClass c)) g =
      c (maxProPMk 2 (GalK K) g) := by
  rw [h1MaxProTwoEquivGalK_apply]
  unfold evenModelCharacterClass
  rw [inf1_H1mk]
  rfl

/-- The abelianized version of even-model character evaluation. -/
theorem h1GalKMaxProTwoAbCharacter_evenModelCharacterClass
    (c : ContinuousMonoidHom
      (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)))
    (y : topAbelianization (GalK K)) :
    h1GalKMaxProTwoAbCharacter (K := K)
        (h1MaxProTwoEquivGalK (K := K) (evenModelCharacterClass c))
        (topAbToTopAbMaxProP (p := 2) (GalK K) y) =
      SectionThree.abLiftG
        (c.comp (maxProPMk 2 (GalK K))) y := by
  obtain ⟨g, rfl⟩ := SectionThree.abMk_surjective y
  rw [h1GalKMaxProTwoAbCharacter_topAbToTopAbMaxProP,
    h1GalKCharacter_h1Max_evenModelCharacterClass, SectionThree.abLiftG_abMk]
  rfl

/-- The mod-two unramified class evaluates nontrivially on a filtration uniformizer. -/
theorem m0FieldNuCharacter_recip_piUnitK
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) :
    h1GalKMaxProTwoAbCharacter (K := K)
        (h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldNuCharacter B)))
        (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip (piUnitK FF))) =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  rw [h1GalKMaxProTwoAbCharacter_evenModelCharacterClass]
  obtain ⟨g, hg⟩ := SectionThree.abMk_surjective (B.recip (piUnitK FF))
  have hg' : toAbK K g = B.recip (piUnitK FF) := hg
  rw [← hg, SectionThree.abLiftG_abMk]
  change dmModTwo (nuUrKTwo B (maxProPMk 2 (GalK K) g)) = _
  rw [nuUrKTwo_maxProPMk, hg']
  have hnu := nuUrK_recip_eq B FF (piUnitK FF) 1 (by
    rw [piUnitK_coe, zpow_one])
  rw [hnu]
  apply Multiplicative.toAdd.injective
  rw [toAdd_dmModTwo]
  simp [mParityZ]

/-- Uniformizer placement of transported `D`, together with the Artin--Kummer formula, forces
the intrinsic compact-M field pivot. -/
theorem m0FieldPivotUnit_of_uniformizerD_of_artin
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (hD : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldDCharacter e.1)) =
      kummerClassK K (piUnitK FF))
    (H : ModTwoTateKummerArtinCompatibility B) :
    M0FieldPivotUnit B alpha h := by
  rw [m0FieldPivotUnit_iff_cup B halpha e, m0PivotCupValue, hD,
    (FieldData.isCupFormFp2_cupFormK K).symm]
  let x := h1MaxProTwoEquivGalK (K := K)
    (evenModelCharacterClass (m0FieldNuCharacter B))
  have hArt := H x (piUnitK FF)
  have hval := m0FieldNuCharacter_recip_piUnitK B FF
  rw [hval] at hArt
  exact (congrArg Multiplicative.toAdd hArt).symm

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The family-selected compact-M corrected residual from uniformizer placement of `D` and the
Artin--Kummer compatibility theorem. -/
theorem m0RowResidualRN_of_familySelection_of_uniformizerD_artin
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.M0 alpha))) (chiCycKTwo (K := K)))
    (hD : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldDCharacter e.1)) =
      kummerClassK K (piUnitK FF))
    (H : ModTwoTateKummerArtinCompatibility B) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have halpha := S.valid
  rw [hbranch] at halpha
  exact m0RowResidualRN_of_familySelection_of_fieldPivot B FF S hbranch
    (m0FieldPivotUnit_of_uniformizerD_of_artin B FF halpha e hD H)

#print axioms h1GalKCharacter_h1Max_evenModelCharacterClass
#print axioms h1GalKMaxProTwoAbCharacter_evenModelCharacterClass
#print axioms m0FieldNuCharacter_recip_piUnitK
#print axioms m0FieldPivotUnit_of_uniformizerD_of_artin
#print axioms m0RowResidualRN_of_familySelection_of_uniformizerD_artin

end
end GQ2.Dyadic.Instances.M0FieldPivotArtin
