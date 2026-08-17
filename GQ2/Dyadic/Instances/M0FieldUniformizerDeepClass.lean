/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.M0FieldUniformizerDInvariant
import GQ2.Dyadic.Instances.StageAbstractionEvenFrameDeep
import GQ2.Dyadic.MultiplicativeDecomposition

/-!
# The compact-M uniformizer-D condition is the deep cyclotomic class

The distinguished compact-M `D` character transported to the field is exactly the depth
`alpha` cyclotomic digit.  Thus intrinsic uniformizer-D placement is equality between the deep
cyclotomic class and the uniformizer Kummer class.

At depth two, the deep class is the mod-eight omega class, hence the Kummer class of `2`.
Uniformizer-D placement is therefore equivalent to `2 / pi` being a square.  Comparing discrete
valuations shows that this forces the absolute ramification index to be odd.  Consequently a
selected depth-two compact-M branch in odd residue degree cannot satisfy uniformizer-D placement:
its presentation degree is even, so the fundamental identity forces even ramification index.

This is a no-go result, not a positive placement producer.  In particular, it supersedes treating
the depth-two placement premise in the odd-residue compact-M consumer as an open construction.
-/

namespace GQ2.Dyadic.Instances.M0FieldUniformizerDeepClass

noncomputable section

open GQ2 GQ2.Dyadic ContCoh
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel
open GQ2.Dyadic.EvenFrameDeep
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.M0C0PivotAutomorphism
open GQ2.Dyadic.Instances.M0FieldPivotCup
open GQ2.Dyadic.Instances.M0FieldUniformizerDInvariant
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.NuKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- An oriented compact-M identification determines the exact cyclotomic character image. -/
theorem range_chiCycKTwo_eq_imChiM_of_oriented {alpha h : ℕ}
    (e : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K))) :
    MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha := by
  ext u
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := e.1.surjective y
    rw [e.2 x]
    rw [← range_chiM alpha h]
    exact ⟨x, rfl⟩
  · intro hu
    rw [← range_chiM alpha h] at hu
    obtain ⟨x, rfl⟩ := hu
    exact ⟨e.1 x, e.2 x⟩

private theorem evenDualVector_two_apply {h : ℕ}
    (i : Fin (coreRank h)) :
    evenDualVector (2 : Fin (coreRank h)) i =
      if (i : ℕ) = 3 then 1 else 0 := by
  classical
  rw [evenDualVector_two_eq]
  by_cases hi : i = (3 : Fin (coreRank h))
  · subst i
    rw [Pi.single_eq_same, if_pos (coreVal_three h)]
  · have hiv : (i : ℕ) ≠ 3 := by
      intro hiv
      apply hi
      apply Fin.ext
      exact hiv.trans (coreVal_three h).symm
    rw [Pi.single_eq_of_ne hi, if_neg hiv]

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- The transported distinguished `D` character is the depth-`alpha` cyclotomic digit. -/
theorem m0FieldDCharacter_eq_evenDeepDigitChar {alpha h : ℕ}
    (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K))) :
    m0FieldDCharacter e.1 =
      evenDeepDigitChar alpha (by omega) (chiCycKTwo (K := K))
        (evenDeep_bound_of_range (by omega)
          (range_chiCycKTwo_eq_imChiM_of_oriented e)) := by
  let ee : ContinuousMonoidHom (DM alpha h : Type)
      (maxProPQuotient 2 (GalK K)) :=
    ⟨e.1.toMonoidHom, e.1.continuous_toFun⟩
  let deep := evenDeepDigitChar alpha (by omega) (chiCycKTwo (K := K))
    (evenDeep_bound_of_range (by omega)
      (range_chiCycKTwo_eq_imChiM_of_oriented e))
  have hcomp : (m0FieldDCharacter e.1).comp ee = deep.comp ee := by
    apply dm_hom_ext
    intro i
    change dmDeltaDRed alpha h (e.1.symm (e.1 (dmGen alpha h i))) =
      Multiplicative.ofAdd
        (evenDeepDigit alpha (chiCycKTwo (K := K) (e.1 (dmGen alpha h i))))
    rw [e.1.symm_apply_apply]
    have horient : chiCycKTwo (K := K) (e.1 (dmGen alpha h i)) =
        chiM alpha h (dmGen alpha h i) := e.2 (dmGen alpha h i)
    rw [horient, chiM_dmGen, evenDeep_mTable halpha]
    change dmDeltaDRed alpha h (dmGen alpha h i) =
      Multiplicative.ofAdd (if (i : ℕ) = 3 then 1 else 0)
    rw [← dmCoordinateCharacter_evenDual_two (alpha := alpha) (h := h) (by omega),
      dmCoordinateCharacter_gen, evenDualVector_two_apply]
  apply DFunLike.ext _ _
  intro y
  let x := e.1.symm y
  have hx := DFunLike.congr_fun hcomp x
  calc
    m0FieldDCharacter e.1 y =
        m0FieldDCharacter e.1 (e.1 x) := by rw [e.1.apply_symm_apply]
    _ = deep (e.1 x) := hx
    _ = deep y := by rw [e.1.apply_symm_apply]

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- At cohomology level, transported `D` is exactly the deep cyclotomic class. -/
theorem evenModelCharacterClass_m0FieldDCharacter_eq_evenDeepClass
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K))) :
    evenModelCharacterClass (m0FieldDCharacter e.1) =
      evenDeepClass alpha (by omega)
        (range_chiCycKTwo_eq_imChiM_of_oriented e) := by
  rw [m0FieldDCharacter_eq_evenDeepDigitChar halpha e]
  rfl

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- Intrinsic uniformizer-D placement is equality of the deep and uniformizer Kummer classes. -/
theorem m0UniformizerDPlacement_iff_evenDeepClass
    (FF : DyadicUnitFiltration K) {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e : OrientedContinuousMulEquiv
      (chiM alpha h) (chiCycKTwo (K := K))) :
    M0UniformizerDPlacement FF alpha h ↔
      h1MaxProTwoEquivGalK (K := K)
          (evenDeepClass alpha (by omega)
            (range_chiCycKTwo_eq_imChiM_of_oriented e)) =
        kummerClassK K (piUnitK FF) := by
  rw [m0UniformizerDPlacement_iff FF halpha e,
    evenModelCharacterClass_m0FieldDCharacter_eq_evenDeepClass halpha e]

omit [T2Space (GalK K)] in
/-- At depth two, uniformizer-D placement is equality of the Kummer classes of `2` and `pi`. -/
theorem m0UniformizerDPlacement_two_iff_kummerTwo
    (FF : DyadicUnitFiltration K) {h : ℕ}
    (e : OrientedContinuousMulEquiv
      (chiM 2 h) (chiCycKTwo (K := K))) :
    M0UniformizerDPlacement FF 2 h ↔
      kummerClassK K (twoUnit K) = kummerClassK K (piUnitK FF) := by
  rw [m0UniformizerDPlacement_iff_evenDeepClass FF (by omega) e,
    GQ2.Dyadic.EvenDeepIsotropy.evenDeepClass_two_eq_omegaClass,
    h1MaxProTwoEquivGalK_cyclotomicModEightOmegaClassKTwo,
    cyclotomicModEightOmegaClassK_eq_kummerTwo]
  rfl

/-- The explicit square-class condition behind depth-two uniformizer placement. -/
def M0UniformizerTwoSquareClass (FF : DyadicUnitFiltration K) : Prop :=
  ∃ w : ↥K,
    w ^ 2 = ((twoUnit K * (piUnitK FF)⁻¹ : (↥K)ˣ) : ↥K)

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
    [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- Equality of the two Kummer classes is the literal square-class equation `2 / pi = w²`. -/
theorem kummerTwo_eq_kummerPi_iff_squareClass
    (FF : DyadicUnitFiltration K) :
    kummerClassK K (twoUnit K) = kummerClassK K (piUnitK FF) ↔
      M0UniformizerTwoSquareClass FF := by
  constructor
  · intro heq
    have hzero : kummerClassK K (twoUnit K * (piUnitK FF)⁻¹) = 0 := by
      rw [kummerClassK_mul, kummerClassK_inv, heq]
      exact h1_add_self _
    exact exists_sq_of_kummerClassK_eq_zero K _ hzero
  · rintro ⟨w, hw⟩
    have hzero := kummerClassK_eq_zero_of_sq K
      (twoUnit K * (piUnitK FF)⁻¹) w hw
    rw [kummerClassK_mul, kummerClassK_inv] at hzero
    exact (eq_neg_of_add_eq_zero_left hzero).trans
      (neg_eq_of_add_eq_zero_left (h1_add_self _))

omit [T2Space (GalK K)] in
/-- The depth-two placement condition in its explicit square-class form. -/
theorem m0UniformizerDPlacement_two_iff_squareClass
    (FF : DyadicUnitFiltration K) {h : ℕ}
    (e : OrientedContinuousMulEquiv
      (chiM 2 h) (chiCycKTwo (K := K))) :
    M0UniformizerDPlacement FF 2 h ↔
      M0UniformizerTwoSquareClass FF :=
  (m0UniformizerDPlacement_two_iff_kummerTwo FF e).trans
    (kummerTwo_eq_kummerPi_iff_squareClass FF)

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
    [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- If `2 / pi` is a square, discreteness of the value group forces `e(K/Q₂)` to be odd. -/
theorem odd_ramificationIndex_of_uniformizerTwoSquareClass
    (FF : DyadicUnitFiltration K)
    (H : M0UniformizerTwoSquareClass FF) : Odd FF.e := by
  obtain ⟨w, hw⟩ := H
  have hw0 : w ≠ 0 := by
    intro hwzero
    rw [hwzero, zero_pow (by omega)] at hw
    have hunit : ((twoUnit K * (piUnitK FF)⁻¹ : (↥K)ˣ) : ↥K) ≠ 0 :=
      Units.ne_zero _
    exact hunit hw.symm
  let wu : (↥K)ˣ := Units.mk0 w hw0
  have hwu : wu ^ 2 = twoUnit K * (piUnitK FF)⁻¹ := by
    apply Units.ext
    exact hw
  have hpi : dyadicValuation FF (piUnitK FF) = 1 := by
    apply dyadicValuation_eq_of_norm_eq_zpow FF
    rw [piUnitK_coe, zpow_one]
  have hpiInv : dyadicValuation FF (piUnitK FF)⁻¹ = -1 := by
    have hinv := dyadicValuation_mul FF (piUnitK FF) (piUnitK FF)⁻¹
    simp only [mul_inv_cancel, dyadicValuation_one, hpi] at hinv
    omega
  have htwo : dyadicValuation FF (twoUnit K) = (FF.e : ℤ) := by
    apply dyadicValuation_eq_of_norm_eq_zpow FF
    change ‖(2 : ℚ̄₂)‖ = ‖FF.π‖ ^ (FF.e : ℤ)
    rw [FF.he, zpow_natCast]
  have hval := congrArg (dyadicValuation FF) hwu
  rw [pow_two, dyadicValuation_mul,
    dyadicValuation_mul, hpiInv, htwo] at hval
  have heq : (FF.e : ℤ) = 2 * dyadicValuation FF wu + 1 := by omega
  have hm0 : 0 ≤ dyadicValuation FF wu := by
    have hepos : 0 < (FF.e : ℤ) := by exact_mod_cast FF.he_pos
    omega
  refine ⟨(dyadicValuation FF wu).toNat, ?_⟩
  have heq' : (FF.e : ℤ) =
      2 * ((dyadicValuation FF wu).toNat : ℤ) + 1 := by
    simpa [Int.toNat_of_nonneg hm0] using heq
  exact_mod_cast heq'

omit [T2Space (GalK K)] in
/-- With a displayed orientation, even ramification rules out depth-two placement. -/
theorem not_m0UniformizerDPlacement_two_of_even_ramificationIndex_at_oriented
    (FF : DyadicUnitFiltration K) (heven : Even FF.e) {h : ℕ}
    (e : OrientedContinuousMulEquiv
      (chiM 2 h) (chiCycKTwo (K := K))) :
    ¬ M0UniformizerDPlacement FF 2 h := by
  intro H
  have hodd := odd_ramificationIndex_of_uniformizerTwoSquareClass FF
    ((m0UniformizerDPlacement_two_iff_squareClass FF e).mp H)
  exact (Nat.not_even_iff_odd.mpr hodd) heven

omit [T2Space (GalK K)] in
/-- Intrinsically, even ramification rules out depth-two uniformizer-D placement. -/
theorem not_m0UniformizerDPlacement_two_of_even_ramificationIndex
    (FF : DyadicUnitFiltration K) (heven : Even FF.e) {h : ℕ} :
    ¬ M0UniformizerDPlacement FF 2 h := by
  intro H
  obtain ⟨e, he⟩ := H
  exact not_m0UniformizerDPlacement_two_of_even_ramificationIndex_at_oriented
    FF heven e ⟨e, he⟩

omit [T2Space (GalK K)] in
/-- In even field degree and odd residue degree, depth-two placement is impossible. -/
theorem not_m0UniformizerDPlacement_two_of_even_degree_odd_residue
    (FF : DyadicUnitFiltration K)
    (hdegree : Even (Module.finrank ℚ_[2] K)) (hf : Odd FF.f) {h : ℕ} :
    ¬ M0UniformizerDPlacement FF 2 h := by
  have heven : Even FF.e := by
    rw [SpectralLocalField.field_finrank_eq_e_mul_f (K := K) (FF := FF)] at hdegree
    exact (Nat.even_mul.mp hdegree).resolve_right (Nat.not_even_iff_odd.mpr hf)
  exact not_m0UniformizerDPlacement_two_of_even_ramificationIndex FF heven

variable {Rec : LocalReciprocity}

omit [T2Space (GalK K)] in
/-- A selected depth-two compact-M branch has even degree, so odd residue degree makes its
uniformizer-D placement premise impossible. -/
theorem not_m0UniformizerDPlacement_two_of_familySelection_odd_residue
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) (hf : Odd FF.f)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    (hbranch : S.branch = .M0 2) :
    ¬ M0UniformizerDPlacement FF 2 (handleCount FP (.M0 2)) := by
  have hdegree : Even (Module.finrank ℚ_[2] K) := by
    have hdeg := S.degree_eq_field
    rw [hbranch] at hdeg
    change 2 + 2 * handleCount FP (.M0 2) = Module.finrank ℚ_[2] K at hdeg
    rw [← hdeg]
    exact ⟨1 + handleCount FP (.M0 2), by omega⟩
  exact not_m0UniformizerDPlacement_two_of_even_degree_odd_residue FF hdegree hf

#print axioms range_chiCycKTwo_eq_imChiM_of_oriented
#print axioms m0FieldDCharacter_eq_evenDeepDigitChar
#print axioms evenModelCharacterClass_m0FieldDCharacter_eq_evenDeepClass
#print axioms m0UniformizerDPlacement_iff_evenDeepClass
#print axioms m0UniformizerDPlacement_two_iff_kummerTwo
#print axioms M0UniformizerTwoSquareClass
#print axioms kummerTwo_eq_kummerPi_iff_squareClass
#print axioms m0UniformizerDPlacement_two_iff_squareClass
#print axioms odd_ramificationIndex_of_uniformizerTwoSquareClass
#print axioms not_m0UniformizerDPlacement_two_of_even_ramificationIndex_at_oriented
#print axioms not_m0UniformizerDPlacement_two_of_even_ramificationIndex
#print axioms not_m0UniformizerDPlacement_two_of_even_degree_odd_residue
#print axioms not_m0UniformizerDPlacement_two_of_familySelection_odd_residue

end
end GQ2.Dyadic.Instances.M0FieldUniformizerDeepClass
