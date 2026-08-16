/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldPivotHilbert
import GQ2.Dyadic.Instances.GammaLNuKummerIdentification

/-!
# Uniformizer criterion for the compact-M field pivot
-/

namespace GQ2.Dyadic.Instances.M0FieldPivotUniformizer

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenModel
open GQ2.Dyadic.LSquare.MarkedFrame
open GQ2.Dyadic.LSquare.NuKummer
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.Instances.M0FieldPivotInvariant
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [T2Space (GalK K)] in
/-- The compact-M copy of the mod-two unramified character is the Frattini-frame copy. -/
theorem m0FieldNuCharacter_eq_nuUrModTwoKTwo (B : MarkedRecip Rec K) :
    m0FieldNuCharacter B = nuUrModTwoKTwo B := by
  ext g
  change Multiplicative.toAdd (dmModTwo (nuUrKTwo B g)) =
    Multiplicative.toAdd (redTwoChar (nuUrKTwo B g))
  calc
    _ = mParityZ (Multiplicative.toAdd (nuUrKTwo B g)) := by
      simpa using toAdd_dmModTwo (Multiplicative.toAdd (nuUrKTwo B g))
    _ = redTwo (Multiplicative.toAdd (nuUrKTwo B g)) := by
      unfold mParityZ redTwo
      simp
    _ = _ := rfl

omit [T2Space (GalK K)] in
/-- Consequently the two cohomology-class presentations of the unramified character agree. -/
theorem evenModelCharacterClass_m0FieldNuCharacter (B : MarkedRecip Rec K) :
    evenModelCharacterClass (m0FieldNuCharacter B) = nuUrModTwoClassKTwo B := by
  rw [m0FieldNuCharacter_eq_nuUrModTwoKTwo B]
  rfl

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- A filtration uniformizer is not a norm from a genuine unramified quadratic extension. -/
theorem not_normForm_piUnitK_of_unramified (FF : DyadicUnitFiltration K)
    {a : (↥K)ˣ} {δa : ℚ̄₂}
    (hδ2 : δa ^ 2 = ((a : ↥K) : ℚ̄₂)) (hδk : δa ∉ K)
    (hunram : HasEqualNormValueGroups K δa) :
    ¬ ∃ x y : ↥K,
      ((piUnitK FF : (↥K)ˣ) : ↥K) = x ^ 2 - (a : ↥K) * y ^ 2 := by
  rintro ⟨x, y, hxy⟩
  obtain ⟨σ, hσ⟩ := UnramifiedQuadraticNorms.exists_conj hδ2 hδk
  have hπ : ((x ^ 2 - (a : ↥K) * y ^ 2 : ↥K) : ℚ̄₂) = FF.π := by
    rw [← hxy]
    exact piUnitK_coe FF
  have hprod :
      ((x : ℚ̄₂) + (y : ℚ̄₂) * δa) *
          σ ((x : ℚ̄₂) + (y : ℚ̄₂) * δa) = FF.π := by
    rw [UnramifiedQuadraticNorms.conj_apply hσ,
      UnramifiedQuadraticNorms.norm_coord hδ2, hπ]
  have hz0 : (x : ℚ̄₂) + (y : ℚ̄₂) * δa ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact FF.hπ_ne hprod.symm
  have hconj :
      ‖σ ((x : ℚ̄₂) + (y : ℚ̄₂) * δa)‖ =
        ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖ :=
    UnramifiedQuadraticNorms.norm_conj_eq K σ _
  have hzz :
      ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖ *
          ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖ = ‖FF.π‖ := by
    calc
      ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖ *
          ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖ =
          ‖((x : ℚ̄₂) + (y : ℚ̄₂) * δa) *
            σ ((x : ℚ̄₂) + (y : ℚ̄₂) * δa)‖ := by
              rw [norm_mul, hconj]
      _ = ‖FF.π‖ := by rw [hprod]
  obtain ⟨w, hw0, hw⟩ := hunram _ hz0 ⟨x, y, rfl⟩
  have hwne : ((w : ↥K) : ℚ̄₂) ≠ 0 := fun h => hw0 (by exact_mod_cast h)
  obtain ⟨m, hm⟩ := UnramifiedNorm.norm_eq_zpow FF (SetLike.coe_mem w) hwne
  have hπ0 : ‖FF.π‖ ≠ 0 := (norm_piUnitK_pos FF).ne'
  have hpow : ‖FF.π‖ ^ (2 * m) = ‖FF.π‖ ^ (1 : ℤ) := by
    rw [two_mul, zpow_add₀ hπ0, ← hm, ← hw, hzz, zpow_one]
  have hone : (1 : ℤ) = 2 * m :=
    (zpow_right_injective₀ (norm_piUnitK_pos FF) (ne_of_lt FF.hπ_lt) hpow).symm
  omega

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- The Kummer class of a genuine unramified quadratic extension pairs nontrivially with the
filtration uniformizer. -/
theorem cupFormK_kummer_unramified_piUnitK_eq_one
    (FF : DyadicUnitFiltration K) {a : (↥K)ˣ} {δa : ℚ̄₂}
    (hδ2 : δa ^ 2 = ((a : ↥K) : ℚ̄₂)) (hδk : δa ∉ K)
    (hunram : HasEqualNormValueGroups K δa) :
    FieldData.cupFormK K (kummerClassK K a) (kummerClassK K (piUnitK FF)) = 1 :=
  (cupFormK_kummer_eq_one_iff K a (piUnitK FF)).mpr
    (not_normForm_piUnitK_of_unramified FF hδ2 hδk hunram)

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- The same uniformizer value in the order used by the compact-M pivot. -/
theorem cupFormK_piUnitK_kummer_unramified_eq_one
    (FF : DyadicUnitFiltration K) {a : (↥K)ˣ} {δa : ℚ̄₂}
    (hδ2 : δa ^ 2 = ((a : ↥K) : ℚ̄₂)) (hδk : δa ∉ K)
    (hunram : HasEqualNormValueGroups K δa) :
    FieldData.cupFormK K (kummerClassK K (piUnitK FF)) (kummerClassK K a) = 1 := by
  rw [(FieldData.isCupFormFp2_cupFormK K).symm]
  exact cupFormK_kummer_unramified_piUnitK_eq_one FF hδ2 hδk hunram

/-- The two concrete Kummer identifications which imply the intrinsic compact-M pivot. -/
def M0UniformizerKummerData (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ}
    (e : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) : Prop :=
  ∃ (u : (↥K)ˣ) (δu : ℚ̄₂),
    δu ^ 2 = ((u : ↥K) : ℚ̄₂) ∧ δu ∉ K ∧
      HasEqualNormValueGroups K δu ∧
      h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldDCharacter e)) =
        kummerClassK K (piUnitK FF) ∧
      h1MaxProTwoEquivGalK (K := K)
          (evenModelCharacterClass (m0FieldNuCharacter B)) =
        kummerClassK K u

/-- Uniformizer placement of the distinguished D class and unramified Kummer placement of the
field marking close the intrinsic compact-M pivot. -/
theorem m0FieldPivotUnit_of_uniformizerKummerData
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (H : M0UniformizerKummerData B FF e.1) :
    M0FieldPivotUnit B alpha h := by
  obtain ⟨u, δu, hδ2, hδk, hunram, hD, hnu⟩ := H
  rw [m0FieldPivotUnit_iff_cup B halpha e, m0PivotCupValue, hD, hnu]
  exact cupFormK_piUnitK_kummer_unramified_eq_one FF hδ2 hδk hunram

/-- A level-zero unramified Kummer identification reduces the M0 pivot to placement of the
transported distinguished D class on the filtration-uniformizer square class. -/
theorem m0FieldPivotUnit_of_uniformizerD_of_unramifiedNu
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha) (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (hD : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldDCharacter e.1)) =
      kummerClassK K (piUnitK FF))
    (hnu : NuUrUnramifiedKummerClass B) :
    M0FieldPivotUnit B alpha h := by
  obtain ⟨u, δu, hδ2, hunram, hclass⟩ := hnu
  have hku : kummerClassK K u ≠ 0 := by
    rw [← hclass]
    intro hzero
    exact nuUrModTwoClassKTwo_ne_zero B hr
      ((h1MaxProTwoEquivGalK (K := K)).injective
        (hzero.trans (map_zero _).symm))
  have hδk := sqrt_notMem_of_kummerClass_ne_zero hδ2 hku
  apply m0FieldPivotUnit_of_uniformizerKummerData B FF halpha e
  refine ⟨u, δu, hδ2, hδk, hunram, hD, ?_⟩
  rw [evenModelCharacterClass_m0FieldNuCharacter B]
  exact hclass

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The selected compact-M residual from the exact two-class Kummer placement packet. -/
theorem m0RowResidualRN_of_familySelection_of_uniformizerKummerData
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.M0 alpha))) (chiCycKTwo (K := K)))
    (H : M0UniformizerKummerData B FF e.1) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have halpha := S.valid
  rw [hbranch] at halpha
  exact m0RowResidualRN_of_familySelection_of_fieldPivot B FF S hbranch
    (m0FieldPivotUnit_of_uniformizerKummerData B FF halpha e H)

/-- Family-selected M0 residual from the two natural arithmetic identifications: the
distinguished D class is the uniformizer class and the field marking is the unramified Kummer
class. -/
theorem m0RowResidualRN_of_familySelection_of_uniformizerD
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.M0 alpha))) (chiCycKTwo (K := K)))
    (hD : h1MaxProTwoEquivGalK (K := K)
        (evenModelCharacterClass (m0FieldDCharacter e.1)) =
      kummerClassK K (piUnitK FF))
    (hnu : NuUrUnramifiedKummerClass B) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  have halpha := S.valid
  rw [hbranch] at halpha
  have hr := S.level_eq
  rw [hbranch] at hr
  exact m0RowResidualRN_of_familySelection_of_fieldPivot B FF S hbranch
    (m0FieldPivotUnit_of_uniformizerD_of_unramifiedNu B FF halpha hr.symm e hD hnu)

#print axioms not_normForm_piUnitK_of_unramified
#print axioms m0FieldNuCharacter_eq_nuUrModTwoKTwo
#print axioms evenModelCharacterClass_m0FieldNuCharacter
#print axioms cupFormK_kummer_unramified_piUnitK_eq_one
#print axioms cupFormK_piUnitK_kummer_unramified_eq_one
#print axioms M0UniformizerKummerData
#print axioms m0FieldPivotUnit_of_uniformizerKummerData
#print axioms m0FieldPivotUnit_of_uniformizerD_of_unramifiedNu
#print axioms m0RowResidualRN_of_familySelection_of_uniformizerKummerData
#print axioms m0RowResidualRN_of_familySelection_of_uniformizerD

end
end GQ2.Dyadic.Instances.M0FieldPivotUniformizer
