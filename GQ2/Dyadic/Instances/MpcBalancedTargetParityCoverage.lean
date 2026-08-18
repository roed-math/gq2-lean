/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetParityDirections

/-!
# Parity coverage of a balanced target

W236 separates parity-visible target failure from primitive order-four failure. This file
packages the distinction without choosing a coordinate lift.

A target is parity covered when one mod-four lift of its obstruction has parity in the
interaction range. This property is independent of the chosen lift. The parity-detected case
is exactly failure of parity coverage. Once parity coverage holds, failure of the full
coordinate span is equivalent to a primitive order-four detector.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetParityCoverage

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
open GQ2.Dyadic.Instances.MpcBalancedTargetDirectionCases
open GQ2.Dyadic.Instances.MpcBalancedTargetParityDirections

def OneHandleBalancedCoreTargetParityCovered
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∃ z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
        oneHandleBalancedCoreNeutralityObstruction p hk hp hrel ∧
      coordinateParity z ∈
        (oneHandleBalancedCoreNeutralityParityRow p k hk).range

private theorem parity_mem_of_factor_eq
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z w : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (hfactor : oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
      oneHandleBalancedCoreNeutralityCoordinateFactor p k hk w)
    (hw : coordinateParity w ∈
      (oneHandleBalancedCoreNeutralityParityRow p k hk).range) :
    coordinateParity z ∈
      (oneHandleBalancedCoreNeutralityParityRow p k hk).range := by
  have hdiffker : z * w⁻¹ ∈
      (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hfactor, mul_inv_cancel]
  have hdiffH : z * w⁻¹ ∈
      (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range := by
    rw [oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker]
    exact hdiffker
  have hdiffHp : coordinateParity (z * w⁻¹) ∈
      (oneHandleBalancedCoreNeutralityParityRow p k hk).range := by
    rw [oneHandleBalancedCoreNeutralityParityRow_range_eq_map]
    exact ⟨z * w⁻¹, hdiffH, rfl⟩
  have heq : coordinateParity z =
      coordinateParity (z * w⁻¹) * coordinateParity w := by
    rw [map_mul, map_inv]
    group
  rw [heq]
  exact (oneHandleBalancedCoreNeutralityParityRow p k hk).range.mul_mem
    hdiffHp hw

theorem targetParityCovered_preimage_iff
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z w : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (hfactor : oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
      oneHandleBalancedCoreNeutralityCoordinateFactor p k hk w) :
    coordinateParity z ∈
        (oneHandleBalancedCoreNeutralityParityRow p k hk).range ↔
      coordinateParity w ∈
        (oneHandleBalancedCoreNeutralityParityRow p k hk).range := by
  constructor
  · exact parity_mem_of_factor_eq p k hk w z hfactor.symm
  · exact parity_mem_of_factor_eq p k hk z w hfactor

theorem targetParityCaseDetected_iff_not_parityCovered
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetParityCaseDetected p hk hp hrel ↔
      ¬ OneHandleBalancedCoreTargetParityCovered p hk hp hrel := by
  constructor
  · intro Hpar Hcovered
    rcases (targetParityCaseDetected_iff_parityTarget_not_mem
      p hk hp hrel).mp Hpar with ⟨z, hz, hzpar⟩
    rcases Hcovered with ⟨w, hw, hwpar⟩
    apply hzpar
    exact (targetParityCovered_preimage_iff p k hk z w
      (hz.trans hw.symm)).mpr hwpar
  · intro Hnot
    obtain ⟨z, hz⟩ :=
      oneHandleBalancedCoreNeutralityCoordinateFactor_surjective p k hk
        (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel)
    apply (targetParityCaseDetected_iff_parityTarget_not_mem
      p hk hp hrel).mpr
    refine ⟨z, hz, ?_⟩
    intro hzpar
    exact Hnot ⟨z, hz, hzpar⟩

theorem target_not_coordinateSpan_iff_primitive_or_not_parityCovered
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk ↔
      OneHandleBalancedCoreTargetPrimitiveCaseDetected p hk hp hrel ∨
        ¬ OneHandleBalancedCoreTargetParityCovered p hk hp hrel := by
  rw [target_not_coordinateSpan_iff_primitive_or_parity,
    targetParityCaseDetected_iff_not_parityCovered]

theorem target_not_coordinateSpan_iff_primitive_of_parityCovered
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (Hcovered : OneHandleBalancedCoreTargetParityCovered p hk hp hrel) :
    oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk ↔
      OneHandleBalancedCoreTargetPrimitiveCaseDetected p hk hp hrel := by
  rw [target_not_coordinateSpan_iff_primitive_or_not_parityCovered]
  constructor
  · rintro (hprim | hnot)
    · exact hprim
    · exact False.elim (hnot Hcovered)
  · exact Or.inl

#print axioms OneHandleBalancedCoreTargetParityCovered
#print axioms targetParityCovered_preimage_iff
#print axioms targetParityCaseDetected_iff_not_parityCovered
#print axioms target_not_coordinateSpan_iff_primitive_or_not_parityCovered
#print axioms target_not_coordinateSpan_iff_primitive_of_parityCovered

end
end GQ2.Dyadic.Instances.MpcBalancedTargetParityCoverage
