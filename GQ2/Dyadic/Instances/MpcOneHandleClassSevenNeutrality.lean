/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCoordinates
import GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel

/-!
# The two class-seven relative obstructions at the standard marking

The standard six-letter marking is a literal balanced point.  Its four constrained shift
rows agree exactly with the standard relative rows isolated after the W6 base reduction.
This imports the existing generic coordinate machinery without identifying the W268 target
with a balanced target: the latter would incorrectly require an exact compact automorphism.

Relaxing only the character-neutrality condition on the `C` source gives a larger ordinary
relative span.  The W6 class-seven target is correctable exactly when it lies in this relaxed
span and its resulting finite neutrality obstruction vanishes.  Neither vanishing is asserted
here; the theorem separates the two remaining finite calculations without hiding either one.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCoordinates

private abbrev H := DM 2 1

def oneHandleStandardBalancedPoint : OneHandleBalancedPoint :=
  (dmA 2 1, dmB 2 1, dmC 2 1, dmD 2 1, 1)

theorem balancedCorrectedMark_standard :
    balancedCorrectedMark oneHandleStandardBalancedPoint = dmGen 2 1 := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · rfl
  · rfl
  · rfl
  · simp only [balancedCorrectedMark, standardHandleMark_three,
      oneHandleStandardBalancedPoint, balancedZ, balancedD, one_mul, dmD]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleStandardBalancedPoint, balancedCorrectedMark,
        mHandleIdx_coordU, mHandleIdx_coordV]

theorem standardRelativeShiftA_eq_balanced :
    oneHandleStandardRelativeShiftA =
      oneHandleBalancedCoreRelativeShiftA
        oneHandleStandardBalancedPoint 6 (by omega) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  rw [oneHandleStandardRelativeShiftA_apply,
    oneHandleBalancedCoreRelativeShiftA_apply,
    balancedCorrectedMark_standard]
  rfl

theorem standardRelativeShiftB_eq_balanced :
    oneHandleStandardRelativeShiftB =
      oneHandleBalancedCoreRelativeShiftB
        oneHandleStandardBalancedPoint 6 (by omega) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  rw [oneHandleStandardRelativeShiftB_apply,
    oneHandleBalancedCoreRelativeShiftB_apply,
    balancedCorrectedMark_standard]
  rfl

theorem standardRelativeShiftC_eq_balanced :
    oneHandleStandardRelativeShiftC =
      oneHandleBalancedCoreRelativeShiftC
        oneHandleStandardBalancedPoint 6 (by omega) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  rw [oneHandleStandardRelativeShiftC_apply,
    oneHandleBalancedCoreRelativeShiftC_apply,
    balancedCorrectedMark_standard]
  rfl

theorem standardRelativeShiftD_eq_balanced :
    oneHandleStandardRelativeShiftD =
      oneHandleBalancedCoreRelativeShiftD
        oneHandleStandardBalancedPoint 6 (by omega) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  rw [oneHandleStandardRelativeShiftD_apply,
    oneHandleBalancedCoreRelativeShiftD_apply,
    balancedCorrectedMark_standard]
  rfl

theorem standardRelativeCoordinateSpan_eq_balanced :
    oneHandleStandardRelativeCoordinateSpan =
      oneHandleBalancedCoreCoordinateSpan
        oneHandleStandardBalancedPoint 6 (by omega) := by
  simp only [oneHandleStandardRelativeCoordinateSpan,
    oneHandleBalancedCoreCoordinateSpan,
    standardRelativeShiftA_eq_balanced,
    standardRelativeShiftB_eq_balanced,
    standardRelativeShiftC_eq_balanced,
    standardRelativeShiftD_eq_balanced]

def oneHandleStandardRelativeRelaxedCoordinateSpan :
    Subgroup (oneHandleRelativeZLayer 6) :=
  oneHandleBalancedCoreRelativeCoordinateSpan
    oneHandleStandardBalancedPoint 6 (by omega)

theorem standardRelativeCoordinateSpan_le_relaxed :
    oneHandleStandardRelativeCoordinateSpan ≤
      oneHandleStandardRelativeRelaxedCoordinateSpan := by
  rw [standardRelativeCoordinateSpan_eq_balanced]
  exact oneHandleBalancedCoreCoordinateSpan_le_relativeCoordinateSpan
    oneHandleStandardBalancedPoint 6 (by omega)

abbrev OneHandleC7StandardRelativeCokernel :=
  (oneHandleRelativeZLayer 6) ⧸ oneHandleStandardRelativeRelaxedCoordinateSpan

noncomputable instance : Finite OneHandleC7StandardRelativeCokernel := by
  dsimp [OneHandleC7StandardRelativeCokernel]
  infer_instance

def oneHandleC7StandardRelativeObstruction (E : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeCokernel :=
  QuotientGroup.mk' oneHandleStandardRelativeRelaxedCoordinateSpan
    (oneHandleC7RelativeTarget E)

theorem standardRelativeObstruction_eq_one_iff (E : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeObstruction E = 1 ↔
      oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan := by
  exact QuotientGroup.eq_one_iff _

def oneHandleC7StandardNeutralitySubgroup :
    Subgroup oneHandleStandardRelativeRelaxedCoordinateSpan :=
  Subgroup.comap oneHandleStandardRelativeRelaxedCoordinateSpan.subtype
    oneHandleStandardRelativeCoordinateSpan

abbrev OneHandleC7StandardNeutralityCokernel :=
  oneHandleStandardRelativeRelaxedCoordinateSpan ⧸
    oneHandleC7StandardNeutralitySubgroup

noncomputable instance : Finite OneHandleC7StandardNeutralityCokernel := by
  dsimp [OneHandleC7StandardNeutralityCokernel]
  infer_instance

def oneHandleC7StandardNeutralityObstruction
    (E : OneHandleC7RelativeLift)
    (hrel : oneHandleC7RelativeTarget E ∈
      oneHandleStandardRelativeRelaxedCoordinateSpan) :
    OneHandleC7StandardNeutralityCokernel :=
  QuotientGroup.mk' oneHandleC7StandardNeutralitySubgroup
    ⟨oneHandleC7RelativeTarget E, hrel⟩

theorem standardNeutralityObstruction_eq_one_iff
    (E : OneHandleC7RelativeLift)
    (hrel : oneHandleC7RelativeTarget E ∈
      oneHandleStandardRelativeRelaxedCoordinateSpan) :
    oneHandleC7StandardNeutralityObstruction E hrel = 1 ↔
      oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeCoordinateSpan := by
  exact QuotientGroup.eq_one_iff _

theorem relativeCorrectable_iff_relaxed_and_neutrality
    (E : OneHandleC7RelativeLift) :
    OneHandleC7RelativeCorrectable E ↔
      ∃ hrel : oneHandleC7RelativeTarget E ∈
          oneHandleStandardRelativeRelaxedCoordinateSpan,
        oneHandleC7StandardNeutralityObstruction E hrel = 1 := by
  rw [relativeCorrectable_iff_standard_target_mem_coordinateSpan]
  constructor
  · intro h
    let hrel := standardRelativeCoordinateSpan_le_relaxed h
    exact ⟨hrel,
      (standardNeutralityObstruction_eq_one_iff E hrel).mpr h⟩
  · rintro ⟨hrel, hzero⟩
    exact (standardNeutralityObstruction_eq_one_iff E hrel).mp hzero

#print axioms balancedCorrectedMark_standard
#print axioms standardRelativeShiftA_eq_balanced
#print axioms standardRelativeShiftB_eq_balanced
#print axioms standardRelativeShiftC_eq_balanced
#print axioms standardRelativeShiftD_eq_balanced
#print axioms standardRelativeCoordinateSpan_eq_balanced
#print axioms oneHandleStandardRelativeRelaxedCoordinateSpan
#print axioms standardRelativeCoordinateSpan_le_relaxed
#print axioms OneHandleC7StandardRelativeCokernel
#print axioms oneHandleC7StandardRelativeObstruction
#print axioms standardRelativeObstruction_eq_one_iff
#print axioms OneHandleC7StandardNeutralityCokernel
#print axioms oneHandleC7StandardNeutralityObstruction
#print axioms standardNeutralityObstruction_eq_one_iff
#print axioms relativeCorrectable_iff_relaxed_and_neutrality

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
