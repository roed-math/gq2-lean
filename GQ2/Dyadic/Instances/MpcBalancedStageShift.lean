/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedClimb
import GQ2.Dyadic.Instances.StageAbstractionEvenRawSpan

/-!
# The exact stage shift behind the balanced one-handle climb

W203 isolates a five-variable correction whose only nonlinear field says that the new
balanced defect lies one rung deeper.  This module replaces that field by the exact finite
quotient equation seen by the generic stage machinery.

The correction of the four-letter core marking is not coordinatewise by the raw five
factors: the corrected `D` letter is `z * d`.  Its actual right correction is therefore
`d⁻¹ * e_z * d * e_d`.  The other three core corrections are `e_a`, `e_b`, and `e_c`, while
both handle corrections are trivial.  With this correction marking, the stage shift kills
the old relator exactly if and only if the modified balanced defect lies in the next
two-central subgroup.

Consequently the W203 climb supply is equivalent to a finite-quotient stage-shift supply.
No reachability assertion is made here: the shift equation is the precise target for the
graded multi-slot span calculation that remains.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedStageShift

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedLevelThree
open GQ2.Dyadic.Instances.MpcBalancedClimb
open GQ2.Roe.Labute

/-- The six-letter marking correction induced by five raw balanced factors. -/
def oneHandleBalancedCorrectionMark (p e : OneHandleBalancedPoint) :
    Fin (coreRank 1) → DM 2 1 :=
  fullMark (balancedA e) (balancedB e) (balancedC e)
    ((balancedD p)⁻¹ * balancedZ e * balancedD p * balancedD e)
    (fun _ ↦ 1) (fun _ ↦ 1)

/-- Coordinatewise modification by the induced marking correction is exactly modification
of the underlying five balanced variables. -/
theorem balancedCorrectedMark_modify_eq_mul (p e : OneHandleBalancedPoint)
    (i : Fin (coreRank 1)) :
    balancedCorrectedMark (oneHandleBalancedModify p e) i =
      balancedCorrectedMark p i * oneHandleBalancedCorrectionMark p e i := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp only [balancedCorrectedMark, standardHandleMark_zero, balancedA_modify,
      oneHandleBalancedCorrectionMark, fullMark_zero]
  · simp only [balancedCorrectedMark, standardHandleMark_one, balancedB_modify,
      oneHandleBalancedCorrectionMark, fullMark_one]
  · simp only [balancedCorrectedMark, standardHandleMark_two, balancedC_modify,
      oneHandleBalancedCorrectionMark, fullMark_two]
  · simp only [balancedCorrectedMark, standardHandleMark_three, balancedZ_modify,
      balancedD_modify, oneHandleBalancedCorrectionMark, fullMark_three]
    group
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [balancedCorrectedMark, mHandleIdx_coordU,
        standardHandleMark_handleU, oneHandleBalancedCorrectionMark,
        fullMark_handleU, mul_one]
    · simp only [balancedCorrectedMark, mHandleIdx_coordV,
        standardHandleMark_handleV, oneHandleBalancedCorrectionMark,
        fullMark_handleV, mul_one]

/-- The exact quotient-level relator shift induced by five balanced factors. -/
def oneHandleBalancedRelatorShift (p e : OneHandleBalancedPoint) (k : ℕ) :
    levelQuot (DM 2 1) (k + 1) :=
  stageShift (mStageWord 2 1 (by omega))
    (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i))
    (fun i ↦ levelMk (DM 2 1) (k + 1)
      (oneHandleBalancedCorrectionMark p e i))

/-- The abstract stage shift is literally the old relator inverse times the modified
relator. -/
theorem oneHandleBalancedRelatorShift_eq (p e : OneHandleBalancedPoint) (k : ℕ) :
    oneHandleBalancedRelatorShift p e k =
      (levelMk (DM 2 1) (k + 1)
        (mRelWord 2 (balancedCorrectedMark p)))⁻¹ *
      levelMk (DM 2 1) (k + 1)
        (mRelWord 2 (balancedCorrectedMark (oneHandleBalancedModify p e))) := by
  have hmark :
      (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i) *
        levelMk (DM 2 1) (k + 1) (oneHandleBalancedCorrectionMark p e i)) =
      (fun i ↦ levelMk (DM 2 1) (k + 1)
        (balancedCorrectedMark (oneHandleBalancedModify p e) i)) := by
    funext i
    rw [← map_mul, ← balancedCorrectedMark_modify_eq_mul]
  rw [oneHandleBalancedRelatorShift, stageShift]
  change
    (mRelWord 2 (fun i ↦ levelMk (DM 2 1) (k + 1)
      (balancedCorrectedMark p i)))⁻¹ *
      mRelWord 2 (fun i ↦
        levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i) *
          levelMk (DM 2 1) (k + 1) (oneHandleBalancedCorrectionMark p e i)) = _
  rw [hmark, ← map_mRelWord, ← map_mRelWord]

/-- The finite-quotient replacement for W203's nonlinear `nextDefect` field. -/
structure OneHandleBalancedShiftCorrection (p : OneHandleBalancedPoint) (k : ℕ) where
  factors : OneHandleBalancedPoint
  depthA : balancedA factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthB : balancedB factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthC : balancedC factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthD : balancedD factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthZ : balancedZ factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  forgetA : dmForgetHandles 2 1 (balancedA factors) = 1
  forgetB : dmForgetHandles 2 1 (balancedB factors) = 1
  forgetC : dmForgetHandles 2 1 (balancedC factors) = 1
  forgetD : dmForgetHandles 2 1 (balancedD factors) = 1
  forgetZ : dmForgetHandles 2 1 (balancedZ factors) = 1
  row : ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
    toAdd (f (balancedC factors)) = 0
  /-- The correction shift cancels the current relator in `DM/λ_(k+1)`. -/
  kills : oneHandleBalancedRelatorShift p factors k =
    (levelMk (DM 2 1) (k + 1)
      (mRelWord 2 (balancedCorrectedMark p)))⁻¹

/-- All six induced marking corrections have the required raw depth.  The nontrivial
`D` correction uses normality to conjugate the raw `z` factor. -/
theorem correctionMark_mem_twoCentralSeries
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedShiftCorrection p k) (i : Fin (coreRank 1)) :
    oneHandleBalancedCorrectionMark p E.factors i ∈
      twoCentralSeries (DM 2 1) (k - 1) := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simpa only [oneHandleBalancedCorrectionMark, fullMark_zero] using E.depthA
  · simpa only [oneHandleBalancedCorrectionMark, fullMark_one] using E.depthB
  · simpa only [oneHandleBalancedCorrectionMark, fullMark_two] using E.depthC
  · simp only [oneHandleBalancedCorrectionMark, fullMark_three]
    apply Subgroup.mul_mem _
    · simpa only [inv_inv] using
        (twoCentralSeries_normal (DM 2 1) (k - 1)).conj_mem
          (balancedZ E.factors) E.depthZ (balancedD p)⁻¹
    · exact E.depthD
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [oneHandleBalancedCorrectionMark, mHandleIdx_coordU,
        fullMark_handleU]
      exact Subgroup.one_mem _
    · simp only [oneHandleBalancedCorrectionMark, mHandleIdx_coordV,
        fullMark_handleV]
      exact Subgroup.one_mem _

/-- The induced quotient corrections lie in the generic stage modification space. -/
theorem correctionMark_mem_lambdaImage
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedShiftCorrection p k) (i : Fin (coreRank 1)) :
    levelMk (DM 2 1) (k + 1) (oneHandleBalancedCorrectionMark p E.factors i) ∈
      lambdaImage (DM 2 1) (k - 1) (k + 1) :=
  ⟨oneHandleBalancedCorrectionMark p E.factors i,
    correctionMark_mem_twoCentralSeries E i, rfl⟩

/-- The exact balanced shift is the existing even crossed-derivation word.  This is the
handoff from the five-slot correction problem to the graded raw-span machinery. -/
theorem oneHandleBalancedRelatorShift_eq_evenRawDbarWord
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedShiftCorrection p k) (hk : 3 ≤ k) :
    oneHandleBalancedRelatorShift p E.factors k =
      evenRawDbarWord
        (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i))
        (fun i ↦ levelMk (DM 2 1) (k + 1)
          (oneHandleBalancedCorrectionMark p E.factors i)) := by
  exact evenRawStageShift_m (G := DM 2 1) (by omega) (by omega) 1 k hk _ _
    (correctionMark_mem_lambdaImage E)

/-- The shift equation implies the W203 next-defect condition. -/
def OneHandleBalancedShiftCorrection.toCorrection
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedShiftCorrection p k) :
    OneHandleBalancedCorrection p k where
  factors := E.factors
  depthA := E.depthA
  depthB := E.depthB
  depthC := E.depthC
  depthD := E.depthD
  depthZ := E.depthZ
  forgetA := E.forgetA
  forgetB := E.forgetB
  forgetC := E.forgetC
  forgetD := E.forgetD
  forgetZ := E.forgetZ
  row := E.row
  nextDefect := by
    let p' := oneHandleBalancedModify p E.factors
    have hshift := E.kills
    rw [oneHandleBalancedRelatorShift_eq] at hshift
    have hrelLevel : levelMk (DM 2 1) (k + 1)
        (mRelWord 2 (balancedCorrectedMark p')) = 1 := by
      apply mul_left_cancel
        (a := (levelMk (DM 2 1) (k + 1)
          (mRelWord 2 (balancedCorrectedMark p)))⁻¹)
      simpa only [mul_one] using hshift
    have hrel : mRelWord 2 (balancedCorrectedMark p') ∈
        twoCentralSeries (DM 2 1) (k + 1) :=
      (lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mpr hrelLevel
    rw [oneHandleDDefect_eq_conj_relWord]
    simpa only [inv_inv] using
      (twoCentralSeries_normal (DM 2 1) (k + 1)).conj_mem
        (mRelWord 2 (balancedCorrectedMark p')) hrel
        (mWord 2 (balancedA p') (balancedB p') (balancedC p') (balancedD p'))⁻¹

/-- Conversely, W203's next-defect field gives the exact killing shift. -/
def oneHandleBalancedCorrection_toShiftCorrection
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedCorrection p k) :
    OneHandleBalancedShiftCorrection p k where
  factors := E.factors
  depthA := E.depthA
  depthB := E.depthB
  depthC := E.depthC
  depthD := E.depthD
  depthZ := E.depthZ
  forgetA := E.forgetA
  forgetB := E.forgetB
  forgetC := E.forgetC
  forgetD := E.forgetD
  forgetZ := E.forgetZ
  row := E.row
  kills := by
    let p' := oneHandleBalancedModify p E.factors
    have hdef := E.nextDefect
    rw [oneHandleDDefect_eq_conj_relWord] at hdef
    have hrel : mRelWord 2 (balancedCorrectedMark p') ∈
        twoCentralSeries (DM 2 1) (k + 1) := by
      have hc := (twoCentralSeries_normal (DM 2 1) (k + 1)).conj_mem
        ((mWord 2 (balancedA p') (balancedB p') (balancedC p') (balancedD p'))⁻¹ *
          mRelWord 2 (balancedCorrectedMark p') *
          mWord 2 (balancedA p') (balancedB p') (balancedC p') (balancedD p'))
        hdef (mWord 2 (balancedA p') (balancedB p') (balancedC p') (balancedD p'))
      convert hc using 1
      group
    have hrelLevel : levelMk (DM 2 1) (k + 1)
        (mRelWord 2 (balancedCorrectedMark p')) = 1 :=
      (lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mp hrel
    rw [oneHandleBalancedRelatorShift_eq, hrelLevel, mul_one]

/-- The nonlinear W203 correction and the exact finite-quotient shift correction are
equivalent. -/
theorem nonempty_shiftCorrection_iff_correction
    (p : OneHandleBalancedPoint) (k : ℕ) :
    Nonempty (OneHandleBalancedShiftCorrection p k) ↔
      Nonempty (OneHandleBalancedCorrection p k) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.toCorrection⟩
  · rintro ⟨E⟩
    exact ⟨oneHandleBalancedCorrection_toShiftCorrection E⟩

/-- Uniform availability of exact finite-quotient killing shifts. -/
def OneHandleBalancedShiftSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ p ∈ oneHandleBalancedSet Psi0 k,
    Nonempty (OneHandleBalancedShiftCorrection p k)

/-- The exact shift supply is precisely the W203 climb supply. -/
theorem balancedShiftSupply_iff_climbSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedShiftSupply Psi0 ↔ OneHandleBalancedClimbSupply Psi0 := by
  constructor <;> intro H k hk p hp
  · exact (nonempty_shiftCorrection_iff_correction p k).mp (H k hk p hp)
  · exact (nonempty_shiftCorrection_iff_correction p k).mpr (H k hk p hp)

/-- The cup-adapted seed plus exact stage-shift reachability yields the one-handle pivot. -/
theorem mpcPivShiftH_two_one_of_balancedShift
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hshift : OneHandleBalancedShiftSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedClimb Psi0 hchi0 hrow
    ((balancedShiftSupply_iff_climbSupply Psi0).mp Hshift)

#print axioms oneHandleBalancedCorrectionMark
#print axioms balancedCorrectedMark_modify_eq_mul
#print axioms oneHandleBalancedRelatorShift
#print axioms oneHandleBalancedRelatorShift_eq
#print axioms OneHandleBalancedShiftCorrection
#print axioms correctionMark_mem_twoCentralSeries
#print axioms correctionMark_mem_lambdaImage
#print axioms oneHandleBalancedRelatorShift_eq_evenRawDbarWord
#print axioms OneHandleBalancedShiftCorrection.toCorrection
#print axioms oneHandleBalancedCorrection_toShiftCorrection
#print axioms nonempty_shiftCorrection_iff_correction
#print axioms OneHandleBalancedShiftSupply
#print axioms balancedShiftSupply_iff_climbSupply
#print axioms mpcPivShiftH_two_one_of_balancedShift

end
end GQ2.Dyadic.Instances.MpcBalancedStageShift
