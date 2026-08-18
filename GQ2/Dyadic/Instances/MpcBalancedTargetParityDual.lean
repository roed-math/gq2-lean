/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetParityObstruction

/-!
# Dual detection of the canonical target parity obstruction

W238 makes target parity a canonical class in a quotient of the two-dimensional parity
plane. This file evaluates that class against the three nonzero characters of the plane.

If a parity character kills the interaction row, its value on a target lift is independent
of the lift. The canonical parity obstruction is nontrivial exactly when one of these three
characters kills every interaction row but is nontrivial on the target. Equivalently, parity
coverage is the conjunction of three explicit scalar compatibility conditions.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetParityDual

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityParity
open GQ2.Dyadic.Instances.MpcBalancedNeutralityDual
open GQ2.Dyadic.Instances.MpcBalancedTargetParityDirections
open GQ2.Dyadic.Instances.MpcBalancedTargetParityCoverage
open GQ2.Dyadic.Instances.MpcBalancedTargetParityObstruction

def OneHandleBalancedCoreTargetParityCharacterDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∃ i : Fin 3,
    oneHandleParityDirectionCharacter i
        (coordinateParity
          (oneHandleBalancedCoreTargetParityLift p hk hp hrel)) =
      ofAdd 1 ∧
    ∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
      oneHandleParityDirectionCharacter i
          (oneHandleBalancedCoreNeutralityParityRow p k hk x) = 1

def OneHandleBalancedCoreTargetParityCharacterCompatible
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∀ i : Fin 3,
    (∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
      oneHandleParityDirectionCharacter i
          (oneHandleBalancedCoreNeutralityParityRow p k hk x) = 1) →
    oneHandleParityDirectionCharacter i
        (coordinateParity
          (oneHandleBalancedCoreTargetParityLift p hk hp hrel)) = 1

theorem targetParityCharacter_eq_of_factor_eq
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (i : Fin 3)
    (hkill : ∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
      oneHandleParityDirectionCharacter i
          (oneHandleBalancedCoreNeutralityParityRow p k hk x) = 1)
    (z w : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (hfactor : oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
      oneHandleBalancedCoreNeutralityCoordinateFactor p k hk w) :
    oneHandleParityDirectionCharacter i (coordinateParity z) =
      oneHandleParityDirectionCharacter i (coordinateParity w) := by
  have hdiffker : z * w⁻¹ ∈
      (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hfactor, mul_inv_cancel]
  have hdiffH : z * w⁻¹ ∈
      (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range := by
    rw [oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker]
    exact hdiffker
  rcases hdiffH with ⟨x, hx⟩
  have hchar := hkill x
  change oneHandleParityDirectionCharacter i
    (coordinateParity
      (oneHandleBalancedCoreNeutralityCoordinateRow p k hk x)) = 1 at hchar
  rw [hx, map_mul, map_inv, map_mul, map_inv] at hchar
  exact mul_inv_eq_one.mp hchar

theorem targetParityObstruction_ne_one_iff_lift_not_mem
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreTargetParityObstruction p hk hp hrel ≠ 1 ↔
      coordinateParity
          (oneHandleBalancedCoreTargetParityLift p hk hp hrel) ∉
        (oneHandleBalancedCoreNeutralityParityRow p k hk).range := by
  rw [oneHandleBalancedCoreTargetParityObstruction]
  exact not_congr (QuotientGroup.eq_one_iff _)

theorem targetParityObstruction_ne_one_iff_characterDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreTargetParityObstruction p hk hp hrel ≠ 1 ↔
      OneHandleBalancedCoreTargetParityCharacterDetected p hk hp hrel := by
  rw [targetParityObstruction_ne_one_iff_lift_not_mem,
    parityTarget_not_mem_iff_directionCharacter]
  simp only [OneHandleBalancedCoreTargetParityCharacterDetected]
  constructor
  · rintro ⟨i, hi, hkill⟩
    refine ⟨i, hi, ?_⟩
    intro x
    exact hkill _ ⟨x, rfl⟩
  · rintro ⟨i, hi, hkill⟩
    refine ⟨i, hi, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hkill x

theorem targetParityCovered_iff_characterCompatible
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetParityCovered p hk hp hrel ↔
      OneHandleBalancedCoreTargetParityCharacterCompatible p hk hp hrel := by
  rw [targetParityCovered_iff_obstruction_eq_one]
  constructor
  · intro hobs i hkill
    have hmem : coordinateParity
          (oneHandleBalancedCoreTargetParityLift p hk hp hrel) ∈
        (oneHandleBalancedCoreNeutralityParityRow p k hk).range := by
      exact (QuotientGroup.eq_one_iff _).mp hobs
    rcases hmem with ⟨x, hx⟩
    rw [← hx]
    exact hkill x
  · intro hcompat
    by_contra hobs
    have hdetected :=
      (targetParityObstruction_ne_one_iff_characterDetected
        p hk hp hrel).mp hobs
    rcases hdetected with ⟨i, hi, hkill⟩
    have hone := hcompat i hkill
    rw [hi] at hone
    exact (by decide : ofAdd (1 : ZMod 2) ≠
      (1 : Multiplicative (ZMod 2))) hone

theorem target_not_coordinateSpan_iff_primitive_or_characterDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk ↔
      OneHandleBalancedCoreTargetPrimitiveCaseDetected p hk hp hrel ∨
        OneHandleBalancedCoreTargetParityCharacterDetected p hk hp hrel := by
  rw [target_not_coordinateSpan_iff_primitive_or_parityObstruction,
    targetParityObstruction_ne_one_iff_characterDetected]

#print axioms OneHandleBalancedCoreTargetParityCharacterDetected
#print axioms OneHandleBalancedCoreTargetParityCharacterCompatible
#print axioms targetParityCharacter_eq_of_factor_eq
#print axioms targetParityObstruction_ne_one_iff_lift_not_mem
#print axioms targetParityObstruction_ne_one_iff_characterDetected
#print axioms targetParityCovered_iff_characterCompatible
#print axioms target_not_coordinateSpan_iff_primitive_or_characterDetected

end
end GQ2.Dyadic.Instances.MpcBalancedTargetParityDual
