/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldUniformizerDInvariant
import GQ2.Dyadic.Instances.GammaLUnramifiedHilbertValue

/-!
# The compact-M unramified-character norm boundary

The single uniformizer Artin value remaining after intrinsic distinguished-D placement is exactly
one quadratic non-norm statement for any Kummer representative of the mod-two unramified class.
At marked level zero, an unramified quadratic Kummer realization proves that non-norm statement
and therefore the selected corrected-RN residual.

This is an honest reduction rather than a universal existence result.  The current marked
reciprocity bundle has no finite-layer norm-reciprocity clause over an arbitrary even-degree
field, so it does not itself construct the required unramified Kummer realization.
-/

namespace GQ2.Dyadic.Instances.M0FieldNuUnramifiedBridge

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.EvenModel GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.Instances.M0FieldPivotUniformizer
open GQ2.Dyadic.Instances.M0FieldPivotArtinValue
open GQ2.Dyadic.Instances.M0FieldUniformizerDInvariant
open GQ2.Dyadic.LSquare.MarkedFrame
open GQ2.Dyadic.LSquare.NuKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- Once a Kummer representative of the mod-two unramified class is fixed, the single
uniformizer Artin equation is exactly failure of the corresponding quadratic norm form. -/
theorem m0UniformizerArtinCompatibility_iff_not_normForm_of_kummer
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) (b : (↥K)ˣ)
    (hb : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldNuCharacter B)) = kummerClassK K b) :
    M0UniformizerArtinCompatibility B FF ↔
      ¬ ∃ x y : ↥K,
        ((piUnitK FF : (↥K)ˣ) : ↥K) = x ^ 2 - (b : ↥K) * y ^ 2 := by
  rw [m0UniformizerArtinCompatibility_iff_cup_one, hb]
  exact cupFormK_kummer_eq_one_iff K b (piUnitK FF)

/-- The exact uniformizer Artin boundary always admits a concrete Kummer/norm-form spelling. -/
theorem exists_kummerRepresentative_m0UniformizerArtinBoundary
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) :
    ∃ b : (↥K)ˣ,
      h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldNuCharacter B)) = kummerClassK K b ∧
        (M0UniformizerArtinCompatibility B FF ↔
          ¬ ∃ x y : ↥K,
            ((piUnitK FF : (↥K)ˣ) : ↥K) = x ^ 2 - (b : ↥K) * y ^ 2) := by
  obtain ⟨b, hb⟩ := kummerClassK_surjective K
    (h1MaxProTwoEquivGalK (K := K)
      (evenModelCharacterClass (m0FieldNuCharacter B)))
  exact ⟨b, hb.symm,
    m0UniformizerArtinCompatibility_iff_not_normForm_of_kummer B FF b hb.symm⟩

/-- At level zero, an unramified quadratic Kummer realization of the mod-two unramified
character proves the exact uniformizer Artin value. -/
theorem m0UniformizerArtinCompatibility_of_nuUrUnramifiedKummerClass
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) (hr : B.r = 0)
    (H : NuUrUnramifiedKummerClass B) :
    M0UniformizerArtinCompatibility B FF := by
  obtain ⟨u, δu, hδ2, hunram, hclass⟩ := H
  have hclass' : h1MaxProTwoEquivGalK (K := K)
      (evenModelCharacterClass (m0FieldNuCharacter B)) = kummerClassK K u := by
    rw [evenModelCharacterClass_m0FieldNuCharacter]
    exact hclass
  rw [m0UniformizerArtinCompatibility_iff_not_normForm_of_kummer B FF u hclass']
  apply not_normForm_piUnitK_of_unramified FF hδ2
  · have hne : kummerClassK K u ≠ 0 := by
      rw [← hclass]
      intro h0
      exact nuUrModTwoClassKTwo_ne_zero B hr
        ((h1MaxProTwoEquivGalK (K := K)).injective
          (h0.trans (map_zero _).symm))
    exact sqrt_notMem_of_kummerClass_ne_zero hδ2 hne
  · exact hunram

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The family-selected M0 residual from intrinsic D placement and an unramified quadratic
Kummer realization of the marked unramified character. -/
theorem m0RowResidualRN_of_familySelection_of_unramifiedKummer
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (Hplace : M0UniformizerDPlacement FF alpha (handleCount FP (.M0 alpha)))
    (Hnu : NuUrUnramifiedKummerClass B) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have hr := S.level_eq
  rw [hbranch] at hr
  exact m0RowResidualRN_of_familySelection_of_intrinsic_uniformizer_data
    B FF S hbranch Hplace
      (m0UniformizerArtinCompatibility_of_nuUrUnramifiedKummerClass
        B FF hr.symm Hnu)

#print axioms m0UniformizerArtinCompatibility_iff_not_normForm_of_kummer
#print axioms exists_kummerRepresentative_m0UniformizerArtinBoundary
#print axioms m0UniformizerArtinCompatibility_of_nuUrUnramifiedKummerClass
#print axioms m0RowResidualRN_of_familySelection_of_unramifiedKummer

end
end GQ2.Dyadic.Instances.M0FieldNuUnramifiedBridge
