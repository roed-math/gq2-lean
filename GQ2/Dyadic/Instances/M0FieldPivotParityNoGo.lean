/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldUniformizerDeepClass
import GQ2.Dyadic.Instances.M0FieldNuOddResidueSpectral

/-!
# A parity obstruction to the depth-two compact-M pivot

When the absolute ramification index is even, `2` is a square times a norm-one unit.  Every
norm-one unit is a norm from a spectrally unramified quadratic extension, so the Hilbert cup of
the corresponding unramified Kummer class with `[2]` vanishes.

The depth-two compact-M distinguished `D` class is `[2]` by
`M0FieldUniformizerDeepClass`.  Hence an unramified realization of the marked unramified class
rules out the intrinsic compact-M pivot whenever the ramification index is even.  On a
family-selected depth-two M0 branch the degree is even; if the residue degree is odd, the
fundamental identity forces even ramification.  The selected pivot is therefore impossible.

Unlike the deep-class identification, the cup comparison here deliberately inherits the
repository's Hilbert/norm criterion and Tate-duality foundations.
-/

namespace GQ2.Dyadic.Instances.M0FieldPivotParityNoGo

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.EvenModel GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.Instances.M0FieldPivotInvariant
open GQ2.Dyadic.Instances.M0FieldPivotUniformizer
open GQ2.Dyadic.Instances.M0FieldUniformizerDeepClass
open GQ2.Dyadic.LSquare.MarkedFrame
open GQ2.Dyadic.LSquare.NuKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-- If `e(K/Q₂)` is even, `2` is represented by the norm form of every spectrally
unramified quadratic extension. -/
theorem exists_normForm_two_of_unramified_even_ramification
    (FF : DyadicUnitFiltration K) (heven : Even FF.e)
    {a : (↥K)ˣ} {δa : ℚ̄₂}
    (hδ2 : δa ^ 2 = ((a : ↥K) : ℚ̄₂))
    (hunram : HasEqualNormValueGroups K δa) :
    ∃ x y : ↥K, (twoUnit K : ↥K) = x ^ 2 - (a : ↥K) * y ^ 2 := by
  obtain ⟨j, hj⟩ := heven
  have htwo : dyadicValuation FF (twoUnit K) = (FF.e : ℤ) := by
    apply dyadicValuation_eq_of_norm_eq_zpow FF
    change ‖(2 : ℚ̄₂)‖ = ‖FF.π‖ ^ (FF.e : ℤ)
    rw [FF.he, zpow_natCast]
  let u : (↥K)ˣ := (normalizedUnit FF (twoUnit K)).1
  have huNorm : ‖((u : ↥K) : ℚ̄₂)‖ = 1 := by
    exact (mem_normUnits K (normalizedUnit FF (twoUnit K)).1).mp
      (normalizedUnit FF (twoUnit K)).2
  obtain ⟨x, y, hxy⟩ :=
    unramifiedQuadratic_units_are_norms K a δa hδ2 hunram u huNorm
  let s : (↥K)ˣ := uniformizerK K FF ^ (j : ℤ)
  have hs : s ^ 2 = uniformizerK K FF ^ (FF.e : ℤ) := by
    change (uniformizerK K FF ^ (j : ℤ)) ^ 2 =
      uniformizerK K FF ^ (FF.e : ℤ)
    rw [pow_two, ← zpow_add]
    congr 2
    exact_mod_cast hj.symm
  have hdecomp : u * s ^ 2 = twoUnit K := by
    rw [hs, ← htwo]
    exact normalizedUnit_mul_uniformizer FF (twoUnit K)
  refine ⟨(s : ↥K) * x, (s : ↥K) * y, ?_⟩
  have hdecomp' : (u : ↥K) * (s : ↥K) ^ 2 = (twoUnit K : ↥K) :=
    congrArg Units.val hdecomp
  rw [← hdecomp', hxy]
  ring

variable {Rec : LocalReciprocity} [CompactSpace (GalK K)]
  [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- Even ramification and an unramified Kummer realization force the depth-two M0 pivot to
vanish. -/
theorem not_m0FieldPivotUnit_two_of_even_ramification_of_unramifiedKummer
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) (heven : Even FF.e)
    (Hnu : NuUrUnramifiedKummerClass B) {h : ℕ} :
    ¬ M0FieldPivotUnit B 2 h := by
  intro Hpivot
  obtain ⟨e, he⟩ := Hpivot
  obtain ⟨u, δu, hδ2, hunram, hclass⟩ := Hnu
  have hD : h1MaxProTwoEquivGalK (K := K)
      (evenModelCharacterClass (m0FieldDCharacter e.1)) =
        kummerClassK K (twoUnit K) := by
    rw [evenModelCharacterClass_m0FieldDCharacter_eq_evenDeepClass (by omega) e,
      GQ2.Dyadic.EvenDeepIsotropy.evenDeepClass_two_eq_omegaClass,
      h1MaxProTwoEquivGalK_cyclotomicModEightOmegaClassKTwo,
      cyclotomicModEightOmegaClassK_eq_kummerTwo]
  have hnu : h1MaxProTwoEquivGalK (K := K)
      (evenModelCharacterClass (m0FieldNuCharacter B)) = kummerClassK K u := by
    rw [evenModelCharacterClass_m0FieldNuCharacter B]
    exact hclass
  have hnorm := exists_normForm_two_of_unramified_even_ramification
    FF heven hδ2 hunram
  have hcupUtwo :
      FieldData.cupFormK K (kummerClassK K u) (kummerClassK K (twoUnit K)) = 0 := by
    rcases ZMod.eq_zero_or_eq_one
        (FieldData.cupFormK K (kummerClassK K u) (kummerClassK K (twoUnit K))) with h0 | h1
    · exact h0
    · exact False.elim ((cupFormK_kummer_eq_one_iff K u (twoUnit K)).mp h1 hnorm)
  have hcup :
      FieldData.cupFormK K (kummerClassK K (twoUnit K)) (kummerClassK K u) = 0 := by
    rw [(FieldData.isCupFormFp2_cupFormK K).symm]
    exact hcupUtwo
  have hpivotCup := (m0FieldPivotUnit_iff_cup B (by omega) e).mp ⟨e, he⟩
  rw [m0PivotCupValue, hD, hnu, hcup] at hpivotCup
  exact zero_ne_one hpivotCup

/-- Odd residue degree supplies the unramified Kummer realization, so even ramification rules
out the depth-two M0 pivot without a separate arithmetic premise. -/
theorem not_m0FieldPivotUnit_two_of_even_ramification_odd_residue
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (heven : Even FF.e) (hf : Odd FF.f) {h : ℕ} :
    ¬ M0FieldPivotUnit B 2 h := by
  apply not_m0FieldPivotUnit_two_of_even_ramification_of_unramifiedKummer B FF heven
  exact nuUrUnramifiedKummerClass_of_odd_residueDegree B FF hf
    (hasEqualNormValueGroups_of_sq_eq_neg_three_of_odd_residueDegree
      FF hf (sq_sqrtCl_negThreeUnit K))

/-- A selected depth-two compact-M branch with odd residue degree cannot carry the intrinsic
field pivot required by the corrected-RN realization. -/
theorem not_m0FieldPivotUnit_two_of_familySelection_odd_residue
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) (hf : Odd FF.f)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    (hbranch : S.branch = .M0 2) :
    ¬ M0FieldPivotUnit B 2 (handleCount FP (.M0 2)) := by
  have hdegree : Even (Module.finrank ℚ_[2] K) := by
    have hdeg := S.degree_eq_field
    rw [hbranch] at hdeg
    change 2 + 2 * handleCount FP (.M0 2) = Module.finrank ℚ_[2] K at hdeg
    rw [← hdeg]
    exact ⟨1 + handleCount FP (.M0 2), by omega⟩
  have heven : Even FF.e := by
    rw [SpectralLocalField.field_finrank_eq_e_mul_f (K := K) (FF := FF)] at hdegree
    exact (Nat.even_mul.mp hdegree).resolve_right (Nat.not_even_iff_odd.mpr hf)
  exact not_m0FieldPivotUnit_two_of_even_ramification_odd_residue B FF heven hf

#print axioms exists_normForm_two_of_unramified_even_ramification
#print axioms not_m0FieldPivotUnit_two_of_even_ramification_of_unramifiedKummer
#print axioms not_m0FieldPivotUnit_two_of_even_ramification_odd_residue
#print axioms not_m0FieldPivotUnit_two_of_familySelection_odd_residue

end
end GQ2.Dyadic.Instances.M0FieldPivotParityNoGo
