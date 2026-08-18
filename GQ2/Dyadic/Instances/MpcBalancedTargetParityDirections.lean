/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetDirectionCases
import GQ2.Dyadic.Instances.MpcBalancedNeutralityDual

/-!
# Parity-visible and primitive target directions

W235 splits the fifteen nonzero mod-four coefficient pairs into six primitive directions and
three parity directions. This file identifies the parity directions with the three explicit
characters of the mod-two coordinate plane.

A parity direction detects a chosen target exactly when the target's parity lies outside the
parity interaction range. Consequently every selected-coordinate failure splits exactly into
a parity-visible case or a genuinely primitive order-four case.

This is an exact target-sensitive dichotomy. It does not eliminate either branch.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetParityDirections

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
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacterDot
open GQ2.Dyadic.Instances.MpcBalancedTargetDirectionCases

def oneHandleParityDirectionCharacter :
    Fin 3 → OneHandleParityPlane →* Multiplicative (ZMod 2) :=
  ![parityUCharacter, parityVCharacter, parityDiagonalCharacter]

theorem parityDirectionDot_eq_zero_iff
    (i : Fin 3)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleZModFourDot
        (oneHandleParityDirectionCoeffs i).1
        (oneHandleParityDirectionCoeffs i).2 z = 0 ↔
      oneHandleParityDirectionCharacter i (coordinateParity z) = 1 := by
  fin_cases i <;> revert z <;> decide

theorem parityDirectionDot_ne_zero_iff
    (i : Fin 3)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleZModFourDot
        (oneHandleParityDirectionCoeffs i).1
        (oneHandleParityDirectionCoeffs i).2 z ≠ 0 ↔
      oneHandleParityDirectionCharacter i (coordinateParity z) =
        ofAdd 1 := by
  fin_cases i <;> revert z <;> decide

private theorem parityDirectionCharacter_value_cases
    (i : Fin 3) (z : OneHandleParityPlane) :
    oneHandleParityDirectionCharacter i z = 1 ∨
      oneHandleParityDirectionCharacter i z = ofAdd 1 := by
  fin_cases i <;> revert z <;> decide

private theorem exists_parityDirectionCharacter_nontrivial
    (z : OneHandleParityPlane) (hz : z ≠ 1) :
    ∃ i : Fin 3, oneHandleParityDirectionCharacter i z = ofAdd 1 := by
  revert z
  decide

private theorem parityDirectionCharacter_kernel_pair
    (i : Fin 3) (z x : OneHandleParityPlane)
    (hz1 : z ≠ 1)
    (hz : oneHandleParityDirectionCharacter i z = 1)
    (hx : oneHandleParityDirectionCharacter i x = 1) :
    x = 1 ∨ x = z := by
  fin_cases i <;> revert z x <;> decide

private theorem paritySubgroup_eq_bot_of_map_bot_of_target
    (H : Subgroup OneHandleParityPlane) (z : OneHandleParityPlane)
    (hzH : z ∉ H) (i : Fin 3)
    (hmap : Subgroup.map (oneHandleParityDirectionCharacter i) H = ⊥)
    (hz : oneHandleParityDirectionCharacter i z = 1) : H = ⊥ := by
  have hz1 : z ≠ 1 := by
    intro hz'
    exact hzH (hz' ▸ H.one_mem)
  ext x
  constructor
  · intro hxH
    have hxmap : oneHandleParityDirectionCharacter i x ∈
        Subgroup.map (oneHandleParityDirectionCharacter i) H :=
      ⟨x, hxH, rfl⟩
    rw [hmap] at hxmap
    rcases parityDirectionCharacter_kernel_pair i z x hz1 hz
        (Subgroup.mem_bot.mp hxmap) with rfl | rfl
    · exact Subgroup.mem_bot.mpr rfl
    · exact False.elim (hzH hxH)
  · intro hx
    exact Subgroup.mem_bot.mp hx ▸ H.one_mem

theorem parityTarget_not_mem_iff_directionCharacter
    (H : Subgroup OneHandleParityPlane) (z : OneHandleParityPlane) :
    z ∉ H ↔
      ∃ i : Fin 3,
        oneHandleParityDirectionCharacter i z = ofAdd 1 ∧
          ∀ x ∈ H, oneHandleParityDirectionCharacter i x = 1 := by
  constructor
  · intro hzH
    have hne : H ≠ ⊤ := by
      intro htop
      apply hzH
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨i, hmap⟩ : ∃ i : Fin 3,
        Subgroup.map (oneHandleParityDirectionCharacter i) H = ⊥ := by
      rcases (paritySubgroup_ne_top_iff_characterMaps_eq_bot H).mp hne with
        hU | hV | hD
      · exact ⟨0, hU⟩
      · exact ⟨1, hV⟩
      · exact ⟨2, hD⟩
    rcases parityDirectionCharacter_value_cases i z with hz | hz
    · have hbot := paritySubgroup_eq_bot_of_map_bot_of_target
        H z hzH i hmap hz
      obtain ⟨j, hj⟩ := exists_parityDirectionCharacter_nontrivial z (by
        intro hz1
        exact hzH (hz1 ▸ H.one_mem))
      refine ⟨j, hj, ?_⟩
      intro x hx
      rw [hbot] at hx
      exact Subgroup.mem_bot.mp hx ▸ map_one _
    · refine ⟨i, hz, ?_⟩
      intro x hx
      have hxmap : oneHandleParityDirectionCharacter i x ∈
          Subgroup.map (oneHandleParityDirectionCharacter i) H :=
        ⟨x, hx, rfl⟩
      rw [hmap] at hxmap
      exact Subgroup.mem_bot.mp hxmap
  · rintro ⟨i, hz, hkill⟩ hzH
    have h := hkill z hzH
    rw [hz] at h
    exact (by decide : ofAdd (1 : ZMod 2) ≠
      (1 : Multiplicative (ZMod 2))) h

theorem parityDirectionDetected_iff_targetParity_not_mem
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    (∃ i : Fin 3, OneHandleBalancedCoreTargetDirectionDetected
      p k hk z (oneHandleParityDirectionCoeffs i)) ↔
      coordinateParity z ∉
        (oneHandleBalancedCoreNeutralityParityRow p k hk).range := by
  rw [parityTarget_not_mem_iff_directionCharacter]
  constructor
  · rintro ⟨i, htarget, hrows⟩
    refine ⟨i, (parityDirectionDot_ne_zero_iff i z).mp htarget, ?_⟩
    rintro y ⟨x, rfl⟩
    exact (parityDirectionDot_eq_zero_iff i _).mp (hrows x)
  · rintro ⟨i, htarget, hrows⟩
    refine ⟨i, (parityDirectionDot_ne_zero_iff i z).mpr htarget, ?_⟩
    intro x
    apply (parityDirectionDot_eq_zero_iff i _).mpr
    exact hrows _ ⟨x, rfl⟩

def OneHandleBalancedCoreTargetPrimitiveCaseDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∃ z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
        oneHandleBalancedCoreNeutralityObstruction p hk hp hrel ∧
      ∃ i : Fin 6, OneHandleBalancedCoreTargetDirectionDetected
        p k hk z (oneHandlePrimitiveDirectionCoeffs i)

def OneHandleBalancedCoreTargetParityCaseDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∃ z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
        oneHandleBalancedCoreNeutralityObstruction p hk hp hrel ∧
      ∃ i : Fin 3, OneHandleBalancedCoreTargetDirectionDetected
        p k hk z (oneHandleParityDirectionCoeffs i)

theorem targetDirectionCaseDetected_iff_primitive_or_parity
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetDirectionCaseDetected p hk hp hrel ↔
      OneHandleBalancedCoreTargetPrimitiveCaseDetected p hk hp hrel ∨
        OneHandleBalancedCoreTargetParityCaseDetected p hk hp hrel := by
  constructor
  · rintro ⟨z, hz, hprim | hpar⟩
    · exact Or.inl ⟨z, hz, hprim⟩
    · exact Or.inr ⟨z, hz, hpar⟩
  · rintro (⟨z, hz, hprim⟩ | ⟨z, hz, hpar⟩)
    · exact ⟨z, hz, Or.inl hprim⟩
    · exact ⟨z, hz, Or.inr hpar⟩

theorem targetParityCaseDetected_iff_parityTarget_not_mem
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetParityCaseDetected p hk hp hrel ↔
      ∃ z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
        oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
            oneHandleBalancedCoreNeutralityObstruction p hk hp hrel ∧
          coordinateParity z ∉
            (oneHandleBalancedCoreNeutralityParityRow p k hk).range := by
  simp only [OneHandleBalancedCoreTargetParityCaseDetected,
    parityDirectionDetected_iff_targetParity_not_mem]

theorem target_not_coordinateSpan_iff_primitive_or_parity
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk ↔
      OneHandleBalancedCoreTargetPrimitiveCaseDetected p hk hp hrel ∨
        OneHandleBalancedCoreTargetParityCaseDetected p hk hp hrel := by
  rw [← targetDirectionCaseDetected_iff_primitive_or_parity,
    targetDirectionCaseDetected_iff_not_coordinateSpan]

#print axioms oneHandleParityDirectionCharacter
#print axioms parityDirectionDot_eq_zero_iff
#print axioms parityDirectionDot_ne_zero_iff
#print axioms parityTarget_not_mem_iff_directionCharacter
#print axioms parityDirectionDetected_iff_targetParity_not_mem
#print axioms OneHandleBalancedCoreTargetPrimitiveCaseDetected
#print axioms OneHandleBalancedCoreTargetParityCaseDetected
#print axioms targetDirectionCaseDetected_iff_primitive_or_parity
#print axioms targetParityCaseDetected_iff_parityTarget_not_mem
#print axioms target_not_coordinateSpan_iff_primitive_or_parity

end
end GQ2.Dyadic.Instances.MpcBalancedTargetParityDirections
