/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityDual

/-!
# Selecting a character-complete point at each balanced stage

The uniform supplies preceding this file ask every balanced point to solve the constrained
coordinate problem.  Compactness needs less.  At each rung it is enough to select one point
whose relative target lies in the full coordinate span.

The local condition is exact: for `k ≥ 3`, nonemptiness at stage `k + 1` is equivalent to the
existence of such a selected point at stage `k`.  At that point, ordinary-relative coverage
together with the three nonzero parity-character rows from W229 implies full coordinate
coverage.  Iterating these selected successors gives all finite stages and hence
`MpcPivShiftH 2 1` through the existing compactness theorem.

No selectable character supply is asserted here.  The remaining front is therefore narrower
than a uniform row theorem: at every nonempty stage, find one point for which the relative
target is covered and the first, second, and diagonal parity characters all occur.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedSelectableCharacters

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcCupAdaptedSeed
open GQ2.Dyadic.Instances.MpcBalancedClimb
open GQ2.Dyadic.Instances.MpcBalancedStageShift
open GQ2.Dyadic.Instances.MpcBalancedCoreShift
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedFiniteSpan
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySourceQuotient
open GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
open GQ2.Dyadic.Instances.MpcBalancedNeutralityEquation
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleCoordinates
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateGenerators
open GQ2.Dyadic.Instances.MpcBalancedNeutralityParity
open GQ2.Dyadic.Instances.MpcBalancedNeutralityDual
open GQ2.Roe.Labute

theorem oneHandleBalancedCoreCoordinateSpan_of_relative_and_characters
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (hchars :
      (oneHandleBalancedCoreNeutralityUCharacterRow p k hk).range = ⊤ ∧
        (oneHandleBalancedCoreNeutralityVCharacterRow p k hk).range = ⊤ ∧
          (oneHandleBalancedCoreNeutralityDiagonalCharacterRow p k hk).range = ⊤) :
    oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreCoordinateSpan p k hk := by
  apply (oneHandleBalancedCoreNeutralityObstruction_eq_one_iff
    p hk hp hrel).mp
  obtain ⟨x, hx⟩ :=
    exists_relativeC_class_eq_neutralityObstruction p hk hp hrel
  apply (neutralityObstruction_eq_one_iff_coordinateInteraction
    p hk hp hrel x hx).mpr
  have hparity :
      (oneHandleBalancedCoreNeutralityParityRow p k hk).range = ⊤ :=
    (oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_characters
      p k hk).mpr hchars
  have hcoordinate :
      (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range = ⊤ :=
    (oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff p k hk).mp
      hparity
  rw [hcoordinate]
  exact Subgroup.mem_top _

theorem oneHandleBalancedSet_succ_nonempty_of_coordinateSpan
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hspan : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreCoordinateSpan p k hk) :
    (oneHandleBalancedSet Psi0 (k + 1)).Nonempty := by
  have hrelative : oneHandleBalancedCoreRelativeTarget p hp ∈
      (oneHandleBalancedCoreRelativeShiftHom p k hk).range := by
    rw [oneHandleBalancedCoreRelativeShift_range_eq_coordinateSpan]
    exact hspan
  have hlevel : oneHandleBalancedCoreLevelTarget p hp ∈
      (oneHandleBalancedCoreLevelShiftHom p k hk).range :=
    (target_mem_relativeRange_iff_target_mem_range p hk hp).mp hrelative
  have hcorrection : Nonempty (OneHandleBalancedCoreShiftCorrection p k) :=
    (nonempty_coreShiftCorrection_iff_exists_levelCorrection p k).mpr
      ((exists_levelCorrection_iff_target_mem_range p hk hp).mpr hlevel)
  obtain ⟨E⟩ := hcorrection
  let C : OneHandleBalancedCorrection p k := E.toShiftCorrection.toCorrection
  exact ⟨oneHandleBalancedModify p C.factors,
    oneHandleBalancedSet_succ_of_correction Psi0 hp C⟩

theorem oneHandleBalancedSet_succ_nonempty_iff_exists_coordinateSpan
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedSet Psi0 (k + 1)).Nonempty ↔
      ∃ p : OneHandleBalancedPoint,
        ∃ hp : p ∈ oneHandleBalancedSet Psi0 k,
          oneHandleBalancedCoreRelativeTarget p hp ∈
            oneHandleBalancedCoreCoordinateSpan p k hk := by
  constructor
  · rintro ⟨p, hpSucc⟩
    have hp : p ∈ oneHandleBalancedSet Psi0 k :=
      oneHandleBalancedSet_antitone (by omega) hpSucc
    refine ⟨p, hp, ?_⟩
    have hrel := balancedCorrectedRelator_mem_twoCentralSeries hpSucc
    have hlevel : levelMk (DM 2 1) (k + 1)
        (mRelWord 2 (balancedCorrectedMark p)) = 1 :=
      (lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mp hrel
    have htarget : oneHandleBalancedCoreRelativeTarget p hp = 1 := by
      apply Subtype.ext
      change (levelMk (DM 2 1) (k + 1)
        (mRelWord 2 (balancedCorrectedMark p)))⁻¹ = 1
      rw [hlevel, inv_one]
    rw [htarget]
    exact Subgroup.one_mem _
  · rintro ⟨p, hp, hspan⟩
    exact oneHandleBalancedSet_succ_nonempty_of_coordinateSpan p hk hp hspan

def OneHandleBalancedCoreCoordinateSelectableSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k),
    (oneHandleBalancedSet Psi0 k).Nonempty →
      ∃ p : OneHandleBalancedPoint,
        ∃ hp : p ∈ oneHandleBalancedSet Psi0 k,
          oneHandleBalancedCoreRelativeTarget p hp ∈
            oneHandleBalancedCoreCoordinateSpan p k hk

theorem coordinateSelectableSupply_iff_successor
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreCoordinateSelectableSupply Psi0 ↔
      ∀ (k : ℕ), 3 ≤ k →
        (oneHandleBalancedSet Psi0 k).Nonempty →
          (oneHandleBalancedSet Psi0 (k + 1)).Nonempty := by
  constructor <;> intro H k hk hnonempty
  · exact (oneHandleBalancedSet_succ_nonempty_iff_exists_coordinateSpan
      Psi0 k hk).mpr (H k hk hnonempty)
  · exact (oneHandleBalancedSet_succ_nonempty_iff_exists_coordinateSpan
      Psi0 k hk).mp (H k hk hnonempty)

def OneHandleBalancedCoreRelativeCharacterSelectableSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k),
    (oneHandleBalancedSet Psi0 k).Nonempty →
      ∃ p : OneHandleBalancedPoint,
        ∃ hp : p ∈ oneHandleBalancedSet Psi0 k,
          oneHandleBalancedCoreRelativeTarget p hp ∈
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk ∧
            (oneHandleBalancedCoreNeutralityUCharacterRow p k hk).range = ⊤ ∧
            (oneHandleBalancedCoreNeutralityVCharacterRow p k hk).range = ⊤ ∧
            (oneHandleBalancedCoreNeutralityDiagonalCharacterRow p k hk).range = ⊤

theorem coordinateSelectableSupply_of_relativeCharacters
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (H : OneHandleBalancedCoreRelativeCharacterSelectableSupply Psi0) :
    OneHandleBalancedCoreCoordinateSelectableSupply Psi0 := by
  intro k hk hnonempty
  obtain ⟨p, hp, hrel, hU, hV, hD⟩ := H k hk hnonempty
  exact ⟨p, hp,
    oneHandleBalancedCoreCoordinateSpan_of_relative_and_characters
      p hk hp hrel ⟨hU, hV, hD⟩⟩

theorem oneHandleBalancedSet_nonempty_all_of_coordinateSelectable
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hselect : OneHandleBalancedCoreCoordinateSelectableSupply Psi0)
    (k : ℕ) :
    (oneHandleBalancedSet Psi0 k).Nonempty := by
  have Hsucc := (coordinateSelectableSupply_iff_successor Psi0).mp Hselect
  by_cases hk : k ≤ 3
  · exact ⟨Classical.choose (oneHandleBalancedSet_three_nonempty Psi0 hrow),
      oneHandleBalancedSet_antitone hk
        (Classical.choose_spec (oneHandleBalancedSet_three_nonempty Psi0 hrow))⟩
  · obtain ⟨d, rfl⟩ : ∃ d, k = 3 + d := ⟨k - 3, by omega⟩
    clear hk
    induction d with
    | zero => simpa using oneHandleBalancedSet_three_nonempty Psi0 hrow
    | succ d ih =>
      simpa only [Nat.add_assoc] using Hsucc (3 + d) (by omega) ih

theorem oneHandleBalancedSet_nonempty_all_of_selectableCharacters
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hselect : OneHandleBalancedCoreRelativeCharacterSelectableSupply Psi0)
    (k : ℕ) :
    (oneHandleBalancedSet Psi0 k).Nonempty :=
  oneHandleBalancedSet_nonempty_all_of_coordinateSelectable Psi0 hrow
    (coordinateSelectableSupply_of_relativeCharacters Hselect) k

theorem mpcPivShiftH_two_one_of_selectableCharacters
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hselect : OneHandleBalancedCoreRelativeCharacterSelectableSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balanced_forall_class Psi0 hchi0
    (oneHandleBalancedSet_nonempty_all_of_selectableCharacters
      Psi0 hrow Hselect)

#print axioms oneHandleBalancedCoreCoordinateSpan_of_relative_and_characters
#print axioms oneHandleBalancedSet_succ_nonempty_of_coordinateSpan
#print axioms oneHandleBalancedSet_succ_nonempty_iff_exists_coordinateSpan
#print axioms OneHandleBalancedCoreCoordinateSelectableSupply
#print axioms coordinateSelectableSupply_iff_successor
#print axioms OneHandleBalancedCoreRelativeCharacterSelectableSupply
#print axioms coordinateSelectableSupply_of_relativeCharacters
#print axioms oneHandleBalancedSet_nonempty_all_of_coordinateSelectable
#print axioms oneHandleBalancedSet_nonempty_all_of_selectableCharacters
#print axioms mpcPivShiftH_two_one_of_selectableCharacters

end
end GQ2.Dyadic.Instances.MpcBalancedSelectableCharacters
