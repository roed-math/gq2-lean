/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetParityCoverage

/-!
# The canonical parity obstruction of a balanced target

W237 packages parity coverage without choosing a mod-four lift. This file makes the
lift-independence structural: the parity of any lift defines the same class modulo the
parity interaction range.

The resulting finite quotient class vanishes exactly when the target is parity covered.
Thus the parity-visible branch is nontriviality of one canonical obstruction, and full
selected-coordinate failure is exactly primitive order-four detection or nontriviality of
this parity obstruction.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetParityObstruction

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

abbrev OneHandleBalancedCoreTargetParityCokernel
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :=
  OneHandleParityPlane ⧸
    (oneHandleBalancedCoreNeutralityParityRow p k hk).range

noncomputable instance oneHandleBalancedCoreTargetParityCokernel_finite
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Finite (OneHandleBalancedCoreTargetParityCokernel p k hk) := by
  dsimp [OneHandleBalancedCoreTargetParityCokernel]
  infer_instance

noncomputable def oneHandleBalancedCoreTargetParityLift
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  Classical.choose
    (oneHandleBalancedCoreNeutralityCoordinateFactor_surjective p k hk
      (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel))

theorem oneHandleBalancedCoreTargetParityLift_factor
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk
        (oneHandleBalancedCoreTargetParityLift p hk hp hrel) =
      oneHandleBalancedCoreNeutralityObstruction p hk hp hrel :=
  Classical.choose_spec
    (oneHandleBalancedCoreNeutralityCoordinateFactor_surjective p k hk
      (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel))

noncomputable def oneHandleBalancedCoreTargetParityObstruction
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetParityCokernel p k hk :=
  QuotientGroup.mk'
    (oneHandleBalancedCoreNeutralityParityRow p k hk).range
    (coordinateParity
      (oneHandleBalancedCoreTargetParityLift p hk hp hrel))

private theorem parity_difference_mem_of_factor_eq
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z w : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (hfactor : oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
      oneHandleBalancedCoreNeutralityCoordinateFactor p k hk w) :
    coordinateParity (z * w⁻¹) ∈
      (oneHandleBalancedCoreNeutralityParityRow p k hk).range := by
  have hdiffker : z * w⁻¹ ∈
      (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hfactor, mul_inv_cancel]
  have hdiffH : z * w⁻¹ ∈
      (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range := by
    rw [oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker]
    exact hdiffker
  rw [oneHandleBalancedCoreNeutralityParityRow_range_eq_map]
  exact ⟨z * w⁻¹, hdiffH, rfl⟩

theorem oneHandleBalancedCoreTargetParityObstruction_eq_mk_of_factor
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (hz : oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
      oneHandleBalancedCoreNeutralityObstruction p hk hp hrel) :
    oneHandleBalancedCoreTargetParityObstruction p hk hp hrel =
      QuotientGroup.mk'
        (oneHandleBalancedCoreNeutralityParityRow p k hk).range
        (coordinateParity z) := by
  rw [oneHandleBalancedCoreTargetParityObstruction,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hmem := parity_difference_mem_of_factor_eq p k hk z
    (oneHandleBalancedCoreTargetParityLift p hk hp hrel)
    (hz.trans (oneHandleBalancedCoreTargetParityLift_factor
      p hk hp hrel).symm)
  simpa [map_mul, map_inv, mul_comm] using hmem

theorem targetParityCovered_iff_obstruction_eq_one
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetParityCovered p hk hp hrel ↔
      oneHandleBalancedCoreTargetParityObstruction p hk hp hrel = 1 := by
  constructor
  · rintro ⟨z, hz, hzpar⟩
    rw [oneHandleBalancedCoreTargetParityObstruction_eq_mk_of_factor
      p hk hp hrel z hz]
    exact (QuotientGroup.eq_one_iff _).mpr hzpar
  · intro hobs
    refine ⟨oneHandleBalancedCoreTargetParityLift p hk hp hrel,
      oneHandleBalancedCoreTargetParityLift_factor p hk hp hrel, ?_⟩
    exact (QuotientGroup.eq_one_iff _).mp hobs

theorem targetParityCaseDetected_iff_obstruction_ne_one
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetParityCaseDetected p hk hp hrel ↔
      oneHandleBalancedCoreTargetParityObstruction p hk hp hrel ≠ 1 := by
  rw [targetParityCaseDetected_iff_not_parityCovered,
    targetParityCovered_iff_obstruction_eq_one]

theorem target_not_coordinateSpan_iff_primitive_or_parityObstruction
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk ↔
      OneHandleBalancedCoreTargetPrimitiveCaseDetected p hk hp hrel ∨
        oneHandleBalancedCoreTargetParityObstruction p hk hp hrel ≠ 1 := by
  rw [target_not_coordinateSpan_iff_primitive_or_not_parityCovered,
    targetParityCovered_iff_obstruction_eq_one]

#print axioms OneHandleBalancedCoreTargetParityCokernel
#print axioms oneHandleBalancedCoreTargetParityLift
#print axioms oneHandleBalancedCoreTargetParityLift_factor
#print axioms oneHandleBalancedCoreTargetParityObstruction
#print axioms oneHandleBalancedCoreTargetParityObstruction_eq_mk_of_factor
#print axioms targetParityCovered_iff_obstruction_eq_one
#print axioms targetParityCaseDetected_iff_obstruction_ne_one
#print axioms target_not_coordinateSpan_iff_primitive_or_parityObstruction

end
end GQ2.Dyadic.Instances.MpcBalancedTargetParityObstruction
