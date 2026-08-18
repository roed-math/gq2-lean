/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetPrimitiveCABD

/-!
# The nine-CABD successor criterion

W241 characterizes coverage of one relatively covered target by three parity and six primitive
scalar CABD implications. This file inserts that finite criterion into the balanced one-handle
successor machine.

The next stage is nonempty exactly when the current stage contains a point whose target has
ordinary relative coverage and satisfies those nine implications. Requiring such a point at
every nonempty stage is therefore equivalent to the existing coordinate-selectable supply. In
particular, it gives every finite stage and the one-handle pivot shift.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetCABDSelectable

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedSelectableCharacters
open GQ2.Dyadic.Instances.MpcBalancedTargetParityCABD
open GQ2.Dyadic.Instances.MpcBalancedTargetPrimitiveCABD

/-- A stagewise selector whose chosen target has ordinary relative coverage and satisfies all
nine scalar CABD compatibility implications. -/
def OneHandleBalancedCoreTargetCABDSelectableSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k),
    (oneHandleBalancedSet Psi0 k).Nonempty →
      ∃ p : OneHandleBalancedPoint,
        ∃ hp : p ∈ oneHandleBalancedSet Psi0 k,
          ∃ hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk,
            OneHandleBalancedCoreTargetParityCABDCompatible p hk hp hrel ∧
              OneHandleBalancedCoreTargetPrimitiveCABDCompatible p hk hp hrel

/-- Advancing one stage is exactly the existence of a relatively covered point satisfying the
three parity and six primitive CABD implications. -/
theorem oneHandleBalancedSet_succ_nonempty_iff_exists_targetCABD
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedSet Psi0 (k + 1)).Nonempty ↔
      ∃ p : OneHandleBalancedPoint,
        ∃ hp : p ∈ oneHandleBalancedSet Psi0 k,
          ∃ hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk,
            OneHandleBalancedCoreTargetParityCABDCompatible p hk hp hrel ∧
              OneHandleBalancedCoreTargetPrimitiveCABDCompatible p hk hp hrel := by
  constructor
  · intro H
    obtain ⟨p, hp, hspan⟩ :=
      (oneHandleBalancedSet_succ_nonempty_iff_exists_coordinateSpan
        Psi0 k hk).mp H
    have hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk :=
      oneHandleBalancedCoreCoordinateSpan_le_relativeCoordinateSpan
        p k hk hspan
    exact ⟨p, hp, hrel,
      (target_mem_coordinateSpan_iff_parity_and_primitive_CABD
        p hk hp hrel).mp hspan⟩
  · rintro ⟨p, hp, hrel, hCABD⟩
    exact (oneHandleBalancedSet_succ_nonempty_iff_exists_coordinateSpan
      Psi0 k hk).mpr ⟨p, hp,
        (target_mem_coordinateSpan_iff_parity_and_primitive_CABD
          p hk hp hrel).mpr hCABD⟩

/-- The nine-CABD selector is exactly the old coordinate-selectable successor supply. -/
theorem targetCABDSelectableSupply_iff_coordinateSelectableSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreTargetCABDSelectableSupply Psi0 ↔
      OneHandleBalancedCoreCoordinateSelectableSupply Psi0 := by
  constructor
  · intro H k hk hnonempty
    obtain ⟨p, hp, hrel, hCABD⟩ := H k hk hnonempty
    exact ⟨p, hp,
      (target_mem_coordinateSpan_iff_parity_and_primitive_CABD
        p hk hp hrel).mpr hCABD⟩
  · intro H k hk hnonempty
    obtain ⟨p, hp, hspan⟩ := H k hk hnonempty
    have hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk :=
      oneHandleBalancedCoreCoordinateSpan_le_relativeCoordinateSpan
        p k hk hspan
    exact ⟨p, hp, hrel,
      (target_mem_coordinateSpan_iff_parity_and_primitive_CABD
        p hk hp hrel).mp hspan⟩

/-- A nine-CABD selector produces every finite balanced stage. -/
theorem oneHandleBalancedSet_nonempty_all_of_targetCABDSelectable
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hselect : OneHandleBalancedCoreTargetCABDSelectableSupply Psi0)
    (k : ℕ) :
    (oneHandleBalancedSet Psi0 k).Nonempty :=
  oneHandleBalancedSet_nonempty_all_of_coordinateSelectable Psi0 hrow
    ((targetCABDSelectableSupply_iff_coordinateSelectableSupply Psi0).mp
      Hselect) k

/-- The finite nine-CABD selection problem is sufficient for the one-handle pivot shift. -/
theorem mpcPivShiftH_two_one_of_targetCABDSelectable
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hselect : OneHandleBalancedCoreTargetCABDSelectableSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balanced_forall_class Psi0 hchi0
    (oneHandleBalancedSet_nonempty_all_of_targetCABDSelectable
      Psi0 hrow Hselect)

#print axioms OneHandleBalancedCoreTargetCABDSelectableSupply
#print axioms oneHandleBalancedSet_succ_nonempty_iff_exists_targetCABD
#print axioms targetCABDSelectableSupply_iff_coordinateSelectableSupply
#print axioms oneHandleBalancedSet_nonempty_all_of_targetCABDSelectable
#print axioms mpcPivShiftH_two_one_of_targetCABDSelectable

end
end GQ2.Dyadic.Instances.MpcBalancedTargetCABDSelectable
