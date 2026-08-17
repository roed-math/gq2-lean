/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan

/-!
# The finite cokernel of the balanced coordinate span

W210 identifies the exact constrained shift image as a four-coordinate span inside the
relative central layer.  This file compares that span with the established unrestricted raw
shift span and packages the remaining target-specific question as one class in a finite
cokernel.

The ambient comparison is one-way: every constrained coordinate shift is an unrestricted
raw shift.  The converse would have to recover separate handle-kernel representatives in
the `A`, `B`, and `D` slots and a character-neutral representative in the `C` slot.  Neither
the raw span nor the augmented raw span records those conditions.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedCoordinateCokernel

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedFiniteSpan
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Roe.Labute

/-! ## Comparison with the unrestricted raw span -/

/-- The W210 coordinate span, included in the ambient finite level quotient. -/
def oneHandleBalancedCoreCoordinateAmbientSpan
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Subgroup (levelQuot (DM 2 1) (k + 1)) :=
  Subgroup.map (oneHandleRelativeZLayer k).subtype
    (oneHandleBalancedCoreCoordinateSpan p k hk)

/-- Every constrained coordinate shift is an unrestricted raw shift. -/
theorem oneHandleBalancedCoreCoordinateAmbientSpan_le_rawShiftSpan
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreCoordinateAmbientSpan p k hk ≤
      evenRawShiftSpan
        (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i)) hk := by
  rintro y ⟨z, hz, rfl⟩
  rw [← oneHandleBalancedCoreRelativeShift_range_eq_coordinateSpan] at hz
  obtain ⟨E, rfl⟩ := hz
  change ((evenRawDepthShiftHom
    (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i)) hk)
      (oneHandleBalancedCoreLevelToRaw E)).1 ∈ _
  exact evenRawDepthShift_mem_shiftSpan _ hk _

/-- W210 target coverage implies unrestricted raw target coverage.  No converse is claimed. -/
theorem rawTarget_mem_shiftSpan_of_coordinateSpan
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hspan : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreCoordinateSpan p k hk) :
    (oneHandleBalancedCoreRelativeTarget p hp).1 ∈
      evenRawShiftSpan
        (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i)) hk :=
  oneHandleBalancedCoreCoordinateAmbientSpan_le_rawShiftSpan p k hk ⟨_, hspan, rfl⟩

/-! ## The finite coordinate cokernel -/

/-- The relative central layer is commutative: it lies in the central layer of the finite
quotient. -/
noncomputable instance oneHandleRelativeZLayer_isMulCommutative (k : ℕ) :
    IsMulCommutative (oneHandleRelativeZLayer k) where
  is_comm := ⟨fun (x y : oneHandleRelativeZLayer k) ↦
    Subtype.ext (zLayer_commute x.2.1 y.1).eq⟩

/-- The relative central layer is finite. -/
noncomputable instance oneHandleRelativeZLayer_finite (k : ℕ) :
    Finite (oneHandleRelativeZLayer k) := by
  letI : Finite (levelQuot (DM 2 1) (k + 1)) :=
    finite_levelQuot (DM 2 1) (dmFinsetTopGen 2 1) (isProP_DM 2 1) (k + 1)
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- The exact finite cokernel of the four constrained coordinate ranges. -/
abbrev OneHandleBalancedCoreCoordinateCokernel
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :=
  (oneHandleRelativeZLayer k) ⧸
    (oneHandleBalancedCoreCoordinateSpan p k hk)

noncomputable instance oneHandleBalancedCoreCoordinateCokernel_finite
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Finite (OneHandleBalancedCoreCoordinateCokernel p k hk) := by
  dsimp [OneHandleBalancedCoreCoordinateCokernel]
  infer_instance

/-- The current balanced relator target, reduced modulo the four coordinate ranges. -/
def oneHandleBalancedCoreCoordinateObstruction
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    OneHandleBalancedCoreCoordinateCokernel p k hk :=
  QuotientGroup.mk' (oneHandleBalancedCoreCoordinateSpan p k hk)
    (oneHandleBalancedCoreRelativeTarget p hp)

/-- The obstruction vanishes exactly when the W210 target lies in the coordinate span. -/
theorem oneHandleBalancedCoreCoordinateObstruction_eq_one_iff
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    oneHandleBalancedCoreCoordinateObstruction p hk hp = 1 ↔
      oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreCoordinateSpan p k hk := by
  exact QuotientGroup.eq_one_iff _

/-- Uniform vanishing of the finite obstruction classes. -/
def OneHandleBalancedCoreCoordinateObstructionVanishing
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint)
    (hp : p ∈ oneHandleBalancedSet Psi0 k),
      oneHandleBalancedCoreCoordinateObstruction p hk hp = 1

/-- Cokernel obstruction vanishing is exactly the W210 coordinate-span supply. -/
theorem coordinateObstructionVanishing_iff_coordinateSpanSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreCoordinateObstructionVanishing Psi0 ↔
      OneHandleBalancedCoreCoordinateSpanSupply Psi0 := by
  constructor <;> intro H k hk p hp
  · exact (oneHandleBalancedCoreCoordinateObstruction_eq_one_iff p hk hp).mp
      (H k hk p hp)
  · exact (oneHandleBalancedCoreCoordinateObstruction_eq_one_iff p hk hp).mpr
      (H k hk p hp)

/-- Vanishing of the finite coordinate obstruction is enough for the one-handle pivot. -/
theorem mpcPivShiftH_two_one_of_balancedCoordinateObstruction
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hobs : OneHandleBalancedCoreCoordinateObstructionVanishing Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedCoordinateSpan Psi0 hchi0 hrow
    ((coordinateObstructionVanishing_iff_coordinateSpanSupply Psi0).mp Hobs)

#print axioms oneHandleBalancedCoreCoordinateAmbientSpan
#print axioms oneHandleBalancedCoreCoordinateAmbientSpan_le_rawShiftSpan
#print axioms rawTarget_mem_shiftSpan_of_coordinateSpan
#print axioms oneHandleRelativeZLayer_isMulCommutative
#print axioms oneHandleRelativeZLayer_finite
#print axioms OneHandleBalancedCoreCoordinateCokernel
#print axioms oneHandleBalancedCoreCoordinateCokernel_finite
#print axioms oneHandleBalancedCoreCoordinateObstruction
#print axioms oneHandleBalancedCoreCoordinateObstruction_eq_one_iff
#print axioms OneHandleBalancedCoreCoordinateObstructionVanishing
#print axioms coordinateObstructionVanishing_iff_coordinateSpanSupply
#print axioms mpcPivShiftH_two_one_of_balancedCoordinateObstruction

end
end GQ2.Dyadic.Instances.MpcBalancedCoordinateCokernel
