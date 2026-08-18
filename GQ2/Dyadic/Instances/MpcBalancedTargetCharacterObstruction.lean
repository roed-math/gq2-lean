/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetCharacters

/-!
# Character detection of the balanced one-handle obstruction

W231 characterizes membership of one selected target in the constrained coordinate span by
vanishing against every character of its finite neutrality cokernel. This file records the
exact complementary statement.

At a relatively covered point, failure of constrained coverage is equivalent to the existence
of a complex additive character which detects the obstruction. Consequently, the next balanced
stage is empty exactly when every point in the current stage either fails ordinary relative
coverage or has a detecting character.

No detecting character is constructed uniformly here. The result exposes the pointwise finite
obstruction which any negative argument must produce and which any positive selection argument
must avoid.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetCharacterObstruction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedSelectableCharacters
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacters

open scoped IsMulCommutative

def OneHandleBalancedCoreTargetCharacterDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∃ chi : AddChar
      (Additive (OneHandleBalancedCoreNeutralityCokernel p k hk)) ℂ,
    chi (Additive.ofMul
      (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel)) ≠ 1

theorem targetCharacterDetected_iff_not_coordinateSpan
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetCharacterDetected p hk hp hrel ↔
      oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk := by
  constructor
  · rintro ⟨chi, hchi⟩ hspan
    exact hchi
      ((targetCharacterVanishing_iff_coordinateSpan p hk hp hrel).mpr
        hspan chi)
  · intro hspan
    have hnot : ¬OneHandleBalancedCoreTargetCharacterVanishing p hk hp hrel :=
      fun hvanish ↦ hspan
        ((targetCharacterVanishing_iff_coordinateSpan p hk hp hrel).mp hvanish)
    unfold OneHandleBalancedCoreTargetCharacterVanishing at hnot
    push Not at hnot
    exact hnot

theorem oneHandleBalancedSet_succ_empty_iff_pointwise_characterObstruction
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (k : ℕ) (hk : 3 ≤ k) :
    ¬(oneHandleBalancedSet Psi0 (k + 1)).Nonempty ↔
      ∀ p : OneHandleBalancedPoint,
        ∀ hp : p ∈ oneHandleBalancedSet Psi0 k,
          oneHandleBalancedCoreRelativeTarget p hp ∉
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk ∨
            ∃ hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk,
                OneHandleBalancedCoreTargetCharacterDetected p hk hp hrel := by
  rw [oneHandleBalancedSet_succ_nonempty_iff_exists_coordinateSpan Psi0 k hk]
  constructor
  · intro H p hp
    have Hpoint : oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk := by
      intro hspan
      exact H ⟨p, hp, hspan⟩
    by_cases hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk
    · right
      refine ⟨hrel, (targetCharacterDetected_iff_not_coordinateSpan
        p hk hp hrel).mpr ?_⟩
      exact Hpoint
    · exact Or.inl hrel
  · intro H hex
    obtain ⟨p, hp, hspan⟩ := hex
    rcases H p hp with hrel | ⟨hrel, hdet⟩
    · exact hrel
        (oneHandleBalancedCoreCoordinateSpan_le_relativeCoordinateSpan p k hk hspan)
    · exact ((targetCharacterDetected_iff_not_coordinateSpan
        p hk hp hrel).mp hdet) hspan

#print axioms OneHandleBalancedCoreTargetCharacterDetected
#print axioms targetCharacterDetected_iff_not_coordinateSpan
#print axioms oneHandleBalancedSet_succ_empty_iff_pointwise_characterObstruction

end
end GQ2.Dyadic.Instances.MpcBalancedTargetCharacterObstruction
