/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedStageShift

/-!
# Removing the redundant fifth variable from the balanced stage shift

The five raw W204 factors induce only four nontrivial marking corrections.  The `z` and `d`
factors occur together in the corrected `D` row as `d⁻¹ * e_z * d * e_d`.  This module
packages the exact four-core-slot problem and proves it equivalent to W204.

The four correction rows all lie in `lambda_(k-1)` and in the handle-forgetting kernel.  The
`C` row is additionally killed by every continuous `Z_2`-valued character.  Both handle
rows are trivial.  Conversely, every four-row correction is represented by balanced factors
with `e_z = 1`, so no reachability is lost.

The remaining boundary is therefore a constrained four-slot image problem for
`evenRawDbarWord`, rather than a five-variable nonlinear problem.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedCoreShift

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedClimb
open GQ2.Dyadic.Instances.MpcBalancedStageShift
open GQ2.Roe.Labute

/-- Four independent core correction rows. -/
abbrev OneHandleBalancedCorePoint :=
  (DM 2 1) × (DM 2 1) × (DM 2 1) × (DM 2 1)

def coreCorrA (e : OneHandleBalancedCorePoint) : DM 2 1 := e.1
def coreCorrB (e : OneHandleBalancedCorePoint) : DM 2 1 := e.2.1
def coreCorrC (e : OneHandleBalancedCorePoint) : DM 2 1 := e.2.2.1
def coreCorrD (e : OneHandleBalancedCorePoint) : DM 2 1 := e.2.2.2

/-- The four core rows followed by two trivial handle rows. -/
def oneHandleBalancedCoreCorrectionMark (e : OneHandleBalancedCorePoint) :
    Fin (coreRank 1) → DM 2 1 :=
  fullMark (coreCorrA e) (coreCorrB e) (coreCorrC e) (coreCorrD e)
    (fun _ ↦ 1) (fun _ ↦ 1)

/-- Regard four core factors as five balanced factors by taking the redundant `z` factor to
be trivial. -/
def coreCorrectionToBalanced (e : OneHandleBalancedCorePoint) :
    OneHandleBalancedPoint :=
  (coreCorrA e, coreCorrB e, coreCorrC e, coreCorrD e, 1)

/-- Combine the raw balanced `z` and `d` factors into their actual correction of the `D`
row. -/
def balancedCorrectionToCore (p e : OneHandleBalancedPoint) :
    OneHandleBalancedCorePoint :=
  (balancedA e, balancedB e, balancedC e,
    (balancedD p)⁻¹ * balancedZ e * balancedD p * balancedD e)

/-- Taking `e_z = 1` recovers the given four-row correction marking exactly. -/
theorem correctionMark_coreCorrectionToBalanced
    (p : OneHandleBalancedPoint) (e : OneHandleBalancedCorePoint) :
    oneHandleBalancedCorrectionMark p (coreCorrectionToBalanced e) =
      oneHandleBalancedCoreCorrectionMark e := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [oneHandleBalancedCorrectionMark, coreCorrectionToBalanced,
      oneHandleBalancedCoreCorrectionMark, coreCorrA, balancedA]
  · simp [oneHandleBalancedCorrectionMark, coreCorrectionToBalanced,
      oneHandleBalancedCoreCorrectionMark, coreCorrB, balancedB]
  · simp [oneHandleBalancedCorrectionMark, coreCorrectionToBalanced,
      oneHandleBalancedCoreCorrectionMark, coreCorrC, balancedC]
  · simp only [oneHandleBalancedCorrectionMark, coreCorrectionToBalanced,
      oneHandleBalancedCoreCorrectionMark, coreCorrD, balancedA, balancedB,
      balancedC, balancedD, balancedZ, fullMark_three]
    group
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [oneHandleBalancedCorrectionMark, coreCorrectionToBalanced,
        oneHandleBalancedCoreCorrectionMark, mHandleIdx_coordU]
    · simp [oneHandleBalancedCorrectionMark, coreCorrectionToBalanced,
        oneHandleBalancedCoreCorrectionMark, mHandleIdx_coordV]

/-- Combining `e_z` and `e_d` does not change the induced correction marking. -/
theorem coreCorrectionMark_balancedCorrectionToCore
    (p e : OneHandleBalancedPoint) :
    oneHandleBalancedCoreCorrectionMark (balancedCorrectionToCore p e) =
      oneHandleBalancedCorrectionMark p e := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [oneHandleBalancedCoreCorrectionMark, balancedCorrectionToCore,
      oneHandleBalancedCorrectionMark, coreCorrA, balancedA]
  · simp [oneHandleBalancedCoreCorrectionMark, balancedCorrectionToCore,
      oneHandleBalancedCorrectionMark, coreCorrB, balancedB]
  · simp [oneHandleBalancedCoreCorrectionMark, balancedCorrectionToCore,
      oneHandleBalancedCorrectionMark, coreCorrC, balancedC]
  · simp [oneHandleBalancedCoreCorrectionMark, balancedCorrectionToCore,
      oneHandleBalancedCorrectionMark, coreCorrD, balancedD, balancedZ]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [oneHandleBalancedCoreCorrectionMark, balancedCorrectionToCore,
        oneHandleBalancedCorrectionMark, mHandleIdx_coordU]
    · simp [oneHandleBalancedCoreCorrectionMark, balancedCorrectionToCore,
        oneHandleBalancedCorrectionMark, mHandleIdx_coordV]

/-- The exact generic stage shift of four constrained core corrections. -/
def oneHandleBalancedCoreRelatorShift
    (p : OneHandleBalancedPoint) (e : OneHandleBalancedCorePoint) (k : ℕ) :
    levelQuot (DM 2 1) (k + 1) :=
  stageShift (mStageWord 2 1 (by omega))
    (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i))
    (fun i ↦ levelMk (DM 2 1) (k + 1)
      (oneHandleBalancedCoreCorrectionMark e i))

/-- The four-slot shift is the five-factor shift with trivial `z` factor. -/
theorem coreRelatorShift_eq_balancedRelatorShift
    (p : OneHandleBalancedPoint) (e : OneHandleBalancedCorePoint) (k : ℕ) :
    oneHandleBalancedCoreRelatorShift p e k =
      oneHandleBalancedRelatorShift p (coreCorrectionToBalanced e) k := by
  rw [oneHandleBalancedCoreRelatorShift, oneHandleBalancedRelatorShift]
  congr 2
  funext i
  rw [correctionMark_coreCorrectionToBalanced]

/-- Combining a five-factor correction into four core rows preserves its stage shift. -/
theorem coreRelatorShift_balancedCorrectionToCore
    (p e : OneHandleBalancedPoint) (k : ℕ) :
    oneHandleBalancedCoreRelatorShift p (balancedCorrectionToCore p e) k =
      oneHandleBalancedRelatorShift p e k := by
  rw [oneHandleBalancedCoreRelatorShift, oneHandleBalancedRelatorShift]
  congr 2

/-- The finite-quotient four-core-slot correction problem. -/
structure OneHandleBalancedCoreShiftCorrection
    (p : OneHandleBalancedPoint) (k : ℕ) where
  factors : OneHandleBalancedCorePoint
  depthA : coreCorrA factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthB : coreCorrB factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthC : coreCorrC factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  depthD : coreCorrD factors ∈ twoCentralSeries (DM 2 1) (k - 1)
  forgetA : dmForgetHandles 2 1 (coreCorrA factors) = 1
  forgetB : dmForgetHandles 2 1 (coreCorrB factors) = 1
  forgetC : dmForgetHandles 2 1 (coreCorrC factors) = 1
  forgetD : dmForgetHandles 2 1 (coreCorrD factors) = 1
  row : ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
    toAdd (f (coreCorrC factors)) = 0
  kills : oneHandleBalancedCoreRelatorShift p factors k =
    (levelMk (DM 2 1) (k + 1)
      (mRelWord 2 (balancedCorrectedMark p)))⁻¹

/-- A four-slot correction gives a W204 correction by taking `e_z = 1`. -/
def OneHandleBalancedCoreShiftCorrection.toShiftCorrection
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedCoreShiftCorrection p k) :
    OneHandleBalancedShiftCorrection p k where
  factors := coreCorrectionToBalanced E.factors
  depthA := E.depthA
  depthB := E.depthB
  depthC := E.depthC
  depthD := E.depthD
  depthZ := Subgroup.one_mem _
  forgetA := E.forgetA
  forgetB := E.forgetB
  forgetC := E.forgetC
  forgetD := E.forgetD
  forgetZ := map_one _
  row := E.row
  kills := by
    rw [← coreRelatorShift_eq_balancedRelatorShift]
    exact E.kills

/-- A W204 correction gives a four-slot correction by combining its `z` and `d` factors. -/
def balancedShiftCorrection_toCoreShiftCorrection
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedShiftCorrection p k) :
    OneHandleBalancedCoreShiftCorrection p k where
  factors := balancedCorrectionToCore p E.factors
  depthA := E.depthA
  depthB := E.depthB
  depthC := E.depthC
  depthD := by
    apply Subgroup.mul_mem _
    · simpa only [inv_inv] using
        (twoCentralSeries_normal (DM 2 1) (k - 1)).conj_mem
          (balancedZ E.factors) E.depthZ (balancedD p)⁻¹
    · exact E.depthD
  forgetA := E.forgetA
  forgetB := E.forgetB
  forgetC := E.forgetC
  forgetD := by
    simp only [balancedCorrectionToCore, coreCorrD, map_mul, map_inv,
      E.forgetZ, E.forgetD, mul_one]
    group
  row := E.row
  kills := by
    rw [coreRelatorShift_balancedCorrectionToCore]
    exact E.kills

/-- The four-slot formulation loses no corrections. -/
theorem nonempty_coreShiftCorrection_iff_shiftCorrection
    (p : OneHandleBalancedPoint) (k : ℕ) :
    Nonempty (OneHandleBalancedCoreShiftCorrection p k) ↔
      Nonempty (OneHandleBalancedShiftCorrection p k) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.toShiftCorrection⟩
  · rintro ⟨E⟩
    exact ⟨balancedShiftCorrection_toCoreShiftCorrection E⟩

/-- Uniform constrained four-core-slot reachability. -/
def OneHandleBalancedCoreShiftSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ p ∈ oneHandleBalancedSet Psi0 k,
    Nonempty (OneHandleBalancedCoreShiftCorrection p k)

/-- The four-core-slot supply is exactly the W204 finite-quotient supply. -/
theorem coreShiftSupply_iff_shiftSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreShiftSupply Psi0 ↔
      OneHandleBalancedShiftSupply Psi0 := by
  constructor <;> intro H k hk p hp
  · exact (nonempty_coreShiftCorrection_iff_shiftCorrection p k).mp (H k hk p hp)
  · exact (nonempty_coreShiftCorrection_iff_shiftCorrection p k).mpr (H k hk p hp)

/-- Four constrained core rows are enough for the one-handle pivot. -/
theorem mpcPivShiftH_two_one_of_balancedCoreShift
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hcore : OneHandleBalancedCoreShiftSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedShift Psi0 hchi0 hrow
    ((coreShiftSupply_iff_shiftSupply Psi0).mp Hcore)

#print axioms OneHandleBalancedCorePoint
#print axioms oneHandleBalancedCoreCorrectionMark
#print axioms coreCorrectionToBalanced
#print axioms balancedCorrectionToCore
#print axioms correctionMark_coreCorrectionToBalanced
#print axioms coreCorrectionMark_balancedCorrectionToCore
#print axioms oneHandleBalancedCoreRelatorShift
#print axioms coreRelatorShift_eq_balancedRelatorShift
#print axioms coreRelatorShift_balancedCorrectionToCore
#print axioms OneHandleBalancedCoreShiftCorrection
#print axioms OneHandleBalancedCoreShiftCorrection.toShiftCorrection
#print axioms balancedShiftCorrection_toCoreShiftCorrection
#print axioms nonempty_coreShiftCorrection_iff_shiftCorrection
#print axioms OneHandleBalancedCoreShiftSupply
#print axioms coreShiftSupply_iff_shiftSupply
#print axioms mpcPivShiftH_two_one_of_balancedCoreShift

end
end GQ2.Dyadic.Instances.MpcBalancedCoreShift
