/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedSelectableCharacters
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Target-sensitive characters for the balanced one-handle obstruction

W229 kills the entire finite neutrality cokernel by requiring three scalar rows to span its
parity plane. W230 only needs one target at one selected point. This file applies finite
Pontryagin duality to that target.

An element of a finite abelian quotient is trivial exactly when every complex additive
character evaluates to one. Consequently, at a relatively covered balanced point, the target
lies in the constrained coordinate span exactly when every character of its finite neutrality
cokernel kills the single obstruction class. Selecting such a point is exactly equivalent to
successor nonemptiness.

This is a quantifier reduction, not a vanishing theorem. The remaining front is target-sensitive:
select one relatively covered point per rung and show that no character detects its obstruction.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetCharacters

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedFiniteSpan
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedSelectableCharacters

open scoped IsMulCommutative

theorem mem_subgroup_iff_forall_quotient_addChar
    {G : Type*} [CommGroup G] [Finite G]
    (H : Subgroup G) (z : G) :
    z ∈ H ↔
      ∀ chi : AddChar (Additive (G ⧸ H)) ℂ,
        chi (Additive.ofMul (QuotientGroup.mk z)) = 1 := by
  rw [← QuotientGroup.eq_one_iff]
  change Additive.ofMul (QuotientGroup.mk z) = 0 ↔ _
  exact (AddChar.forall_apply_eq_zero
    (α := Additive (G ⧸ H))
    (a := Additive.ofMul (QuotientGroup.mk z))).symm

def OneHandleBalancedCoreTargetCharacterVanishing
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∀ chi : AddChar
      (Additive (OneHandleBalancedCoreNeutralityCokernel p k hk)) ℂ,
    chi (Additive.ofMul
      (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel)) = 1

theorem targetCharacterVanishing_iff_coordinateSpan
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetCharacterVanishing p hk hp hrel ↔
      oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreCoordinateSpan p k hk := by
  rw [← oneHandleBalancedCoreNeutralityObstruction_eq_one_iff p hk hp hrel]
  change (∀ chi : AddChar
      (Additive (OneHandleBalancedCoreNeutralityCokernel p k hk)) ℂ,
      chi (Additive.ofMul
        (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel)) = 1) ↔ _
  change (∀ chi : AddChar
      (Additive (OneHandleBalancedCoreNeutralityCokernel p k hk)) ℂ,
      chi (Additive.ofMul
        (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel)) = 1) ↔
    Additive.ofMul
      (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel) = 0
  exact AddChar.forall_apply_eq_zero
    (α := Additive (OneHandleBalancedCoreNeutralityCokernel p k hk))
    (a := Additive.ofMul
      (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel))

def OneHandleBalancedCoreTargetCharacterSelectableSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k),
    (oneHandleBalancedSet Psi0 k).Nonempty →
      ∃ p : OneHandleBalancedPoint,
        ∃ hp : p ∈ oneHandleBalancedSet Psi0 k,
          ∃ hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
            oneHandleBalancedCoreRelativeCoordinateSpan p k hk,
              OneHandleBalancedCoreTargetCharacterVanishing p hk hp hrel

theorem targetCharacterSelectableSupply_iff_coordinateSelectable
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreTargetCharacterSelectableSupply Psi0 ↔
      OneHandleBalancedCoreCoordinateSelectableSupply Psi0 := by
  constructor
  · intro H k hk hnonempty
    obtain ⟨p, hp, hrel, hchars⟩ := H k hk hnonempty
    exact ⟨p, hp,
      (targetCharacterVanishing_iff_coordinateSpan p hk hp hrel).mp hchars⟩
  · intro H k hk hnonempty
    obtain ⟨p, hp, hspan⟩ := H k hk hnonempty
    have hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk :=
      oneHandleBalancedCoreCoordinateSpan_le_relativeCoordinateSpan
        p k hk hspan
    exact ⟨p, hp, hrel,
      (targetCharacterVanishing_iff_coordinateSpan p hk hp hrel).mpr hspan⟩

theorem targetCharacterSelectableSupply_iff_successor
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreTargetCharacterSelectableSupply Psi0 ↔
      ∀ (k : ℕ), 3 ≤ k →
        (oneHandleBalancedSet Psi0 k).Nonempty →
          (oneHandleBalancedSet Psi0 (k + 1)).Nonempty := by
  rw [targetCharacterSelectableSupply_iff_coordinateSelectable,
    coordinateSelectableSupply_iff_successor]

theorem mpcPivShiftH_two_one_of_targetCharacters
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hselect : OneHandleBalancedCoreTargetCharacterSelectableSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balanced_forall_class Psi0 hchi0
    (oneHandleBalancedSet_nonempty_all_of_coordinateSelectable Psi0 hrow
      ((targetCharacterSelectableSupply_iff_coordinateSelectable Psi0).mp Hselect))

#print axioms mem_subgroup_iff_forall_quotient_addChar
#print axioms OneHandleBalancedCoreTargetCharacterVanishing
#print axioms targetCharacterVanishing_iff_coordinateSpan
#print axioms OneHandleBalancedCoreTargetCharacterSelectableSupply
#print axioms targetCharacterSelectableSupply_iff_coordinateSelectable
#print axioms targetCharacterSelectableSupply_iff_successor
#print axioms mpcPivShiftH_two_one_of_targetCharacters

end
end GQ2.Dyadic.Instances.MpcBalancedTargetCharacters
