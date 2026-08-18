/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetCharacterDot

/-!
# The nine balanced target directions

W234 reduces target detection to a nonzero mod-four dot product. Multiplication of both
coefficients by a unit preserves every zero and nonzero dot-product condition. The fifteen
nonzero coefficient pairs therefore reduce to nine directions:

* six primitive directions, with at least one odd coefficient;
* three parity directions `(2,0)`, `(0,2)`, and `(2,2)`.

This file proves the exact classification and rewrites pointwise successor failure as one of
these nine finite cases. It does not assert that any direction actually detects a target.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetDirectionCases

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacterDot

def oneHandlePrimitiveDirectionCoeffs : Fin 6 → ZMod 4 × ZMod 4 :=
  ![(1, 0), (0, 1), (1, 1), (1, 2), (1, 3), (2, 1)]

def oneHandleParityDirectionCoeffs : Fin 3 → ZMod 4 × ZMod 4 :=
  ![(2, 0), (0, 2), (2, 2)]

theorem nonzero_coefficients_classification
    (a b : ZMod 4) (h : a ≠ 0 ∨ b ≠ 0) :
    (∃ i : Fin 6, ∃ u : ZMod 4, IsUnit u ∧
      oneHandlePrimitiveDirectionCoeffs i = (u * a, u * b)) ∨
    (∃ i : Fin 3, oneHandleParityDirectionCoeffs i = (a, b)) := by
  revert a b
  decide

theorem oneHandleZModFourDot_unit_mul
    (u a b : ZMod 4)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleZModFourDot (u * a) (u * b) z =
      u * oneHandleZModFourDot a b z := by
  simp [oneHandleZModFourDot, mul_add, mul_assoc]

theorem oneHandleZModFourDot_unit_mul_eq_zero_iff
    (u a b : ZMod 4) (hu : IsUnit u)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleZModFourDot (u * a) (u * b) z = 0 ↔
      oneHandleZModFourDot a b z = 0 := by
  rw [oneHandleZModFourDot_unit_mul]
  obtain ⟨u', rfl⟩ := hu
  simp

theorem oneHandleZModFourDot_unit_mul_ne_zero_iff
    (u a b : ZMod 4) (hu : IsUnit u)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleZModFourDot (u * a) (u * b) z ≠ 0 ↔
      oneHandleZModFourDot a b z ≠ 0 :=
  not_congr (oneHandleZModFourDot_unit_mul_eq_zero_iff u a b hu z)

def OneHandleBalancedCoreTargetDirectionDetected
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (c : ZMod 4 × ZMod 4) : Prop :=
  oneHandleZModFourDot c.1 c.2 z ≠ 0 ∧
    ∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
      oneHandleZModFourDot c.1 c.2
        (oneHandleBalancedCoreNeutralityCoordinateRow p k hk x) = 0

def OneHandleBalancedCoreTargetDirectionCaseDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∃ z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
        oneHandleBalancedCoreNeutralityObstruction p hk hp hrel ∧
      ((∃ i : Fin 6, OneHandleBalancedCoreTargetDirectionDetected
          p k hk z (oneHandlePrimitiveDirectionCoeffs i)) ∨
        (∃ i : Fin 3, OneHandleBalancedCoreTargetDirectionDetected
          p k hk z (oneHandleParityDirectionCoeffs i)))

theorem targetDirectionDetected_unit_mul_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (u a b : ZMod 4) (hu : IsUnit u) :
    OneHandleBalancedCoreTargetDirectionDetected p k hk z (u * a, u * b) ↔
      OneHandleBalancedCoreTargetDirectionDetected p k hk z (a, b) := by
  simp only [OneHandleBalancedCoreTargetDirectionDetected,
    oneHandleZModFourDot_unit_mul_ne_zero_iff u a b hu,
    oneHandleZModFourDot_unit_mul_eq_zero_iff u a b hu]

theorem targetDotDetected_iff_directionCaseDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetDotDetected p hk hp hrel ↔
      OneHandleBalancedCoreTargetDirectionCaseDetected p hk hp hrel := by
  constructor
  · rintro ⟨z, hz, a, b, htarget, hrows⟩
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_cases ha : a = 0
      · right
        intro hb
        apply htarget
        simp [oneHandleZModFourDot, ha, hb]
      · exact Or.inl ha
    refine ⟨z, hz, ?_⟩
    rcases nonzero_coefficients_classification a b hab with hprim | hpar
    · left
      obtain ⟨i, u, hu, hi⟩ := hprim
      refine ⟨i, ?_⟩
      rw [hi, targetDirectionDetected_unit_mul_iff p k hk z u a b hu]
      exact ⟨htarget, hrows⟩
    · right
      obtain ⟨i, hi⟩ := hpar
      refine ⟨i, ?_⟩
      rw [hi]
      exact ⟨htarget, hrows⟩
  · rintro ⟨z, hz, hprim | hpar⟩
    · obtain ⟨i, hi⟩ := hprim
      exact ⟨z, hz, (oneHandlePrimitiveDirectionCoeffs i).1,
        (oneHandlePrimitiveDirectionCoeffs i).2, hi⟩
    · obtain ⟨i, hi⟩ := hpar
      exact ⟨z, hz, (oneHandleParityDirectionCoeffs i).1,
        (oneHandleParityDirectionCoeffs i).2, hi⟩

theorem targetDirectionCaseDetected_iff_not_coordinateSpan
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetDirectionCaseDetected p hk hp hrel ↔
      oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk := by
  rw [← targetDotDetected_iff_directionCaseDetected,
    targetDotDetected_iff_not_coordinateSpan]

theorem oneHandleBalancedSet_succ_empty_iff_pointwise_directionCaseObstruction
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (k : ℕ) (hk : 3 ≤ k) :
    ¬(oneHandleBalancedSet Psi0 (k + 1)).Nonempty ↔
      ∀ p : OneHandleBalancedPoint,
        ∀ hp : p ∈ oneHandleBalancedSet Psi0 k,
          oneHandleBalancedCoreRelativeTarget p hp ∉
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk ∨
            ∃ hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk,
                OneHandleBalancedCoreTargetDirectionCaseDetected p hk hp hrel := by
  simpa only [targetDotDetected_iff_directionCaseDetected] using
    oneHandleBalancedSet_succ_empty_iff_pointwise_dotObstruction Psi0 k hk

#print axioms oneHandlePrimitiveDirectionCoeffs
#print axioms oneHandleParityDirectionCoeffs
#print axioms nonzero_coefficients_classification
#print axioms oneHandleZModFourDot_unit_mul
#print axioms oneHandleZModFourDot_unit_mul_eq_zero_iff
#print axioms oneHandleZModFourDot_unit_mul_ne_zero_iff
#print axioms OneHandleBalancedCoreTargetDirectionDetected
#print axioms OneHandleBalancedCoreTargetDirectionCaseDetected
#print axioms targetDirectionDetected_unit_mul_iff
#print axioms targetDotDetected_iff_directionCaseDetected
#print axioms targetDirectionCaseDetected_iff_not_coordinateSpan
#print axioms oneHandleBalancedSet_succ_empty_iff_pointwise_directionCaseObstruction

end
end GQ2.Dyadic.Instances.MpcBalancedTargetDirectionCases
