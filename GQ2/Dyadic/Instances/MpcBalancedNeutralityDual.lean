/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityParity

/-!
# The three scalar neutrality characters

The one-handle neutrality target was reduced in the preceding module to the parity plane
`(ZMod 2)^2`.  This module dualizes that finite target.  Its three nonzero characters are
the first coordinate, the second coordinate, and their sum.  A subgroup fills the parity
plane exactly when all three character images are nontrivial.

For the balanced interaction row this has two complementary concrete consequences:

* success is equivalent to three scalar CABD relations, one detected by each character;
* failure is equivalent to one of the three characters annihilating every admissible CABD
  relation.

Thus the remaining neutrality problem is no longer an opaque subgroup statement.  It is
an explicit three-character graded separation problem.  This module proves the exact
reduction; it does not assert that the three scalar relations exist.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityDual

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
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

abbrev OneHandleParityPlane :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

def parityUCharacter : OneHandleParityPlane →* Multiplicative (ZMod 2) where
  toFun z := z.1
  map_one' := rfl
  map_mul' _ _ := rfl

def parityVCharacter : OneHandleParityPlane →* Multiplicative (ZMod 2) where
  toFun z := z.2
  map_one' := rfl
  map_mul' _ _ := rfl

def parityDiagonalCharacter : OneHandleParityPlane →* Multiplicative (ZMod 2) where
  toFun z := z.1 * z.2
  map_one' := by simp
  map_mul' x y := by
    change x.1 * y.1 * (x.2 * y.2) = x.1 * x.2 * (y.1 * y.2)
    ac_rfl

theorem parityUCharacter_surjective : Function.Surjective parityUCharacter := by
  intro z
  exact ⟨(z, 1), rfl⟩

theorem parityVCharacter_surjective : Function.Surjective parityVCharacter := by
  intro z
  exact ⟨(1, z), rfl⟩

theorem parityDiagonalCharacter_surjective :
    Function.Surjective parityDiagonalCharacter := by
  intro z
  exact ⟨(z, 1), by simp [parityDiagonalCharacter]⟩

theorem parityUCharacter_eq_nontrivial_iff
    (z : OneHandleParityPlane) :
    parityUCharacter z = ofAdd 1 ↔
      z = coordinateParityU ∨ z = coordinateParityU * coordinateParityV := by
  revert z
  decide

theorem parityVCharacter_eq_nontrivial_iff
    (z : OneHandleParityPlane) :
    parityVCharacter z = ofAdd 1 ↔
      z = coordinateParityV ∨ z = coordinateParityU * coordinateParityV := by
  revert z
  decide

theorem parityDiagonalCharacter_eq_nontrivial_iff
    (z : OneHandleParityPlane) :
    parityDiagonalCharacter z = ofAdd 1 ↔
      z = coordinateParityU ∨ z = coordinateParityV := by
  revert z
  decide

theorem paritySubgroup_eq_top_iff_characterMaps
    (H : Subgroup OneHandleParityPlane) :
    H = ⊤ ↔
      Subgroup.map parityUCharacter H = ⊤ ∧
        Subgroup.map parityVCharacter H = ⊤ ∧
          Subgroup.map parityDiagonalCharacter H = ⊤ := by
  constructor
  · intro hH
    subst H
    exact ⟨Subgroup.map_top_of_surjective _ parityUCharacter_surjective,
      Subgroup.map_top_of_surjective _ parityVCharacter_surjective,
      Subgroup.map_top_of_surjective _ parityDiagonalCharacter_surjective⟩
  · rintro ⟨hUmap, hVmap, hDmap⟩
    have hUtarget : ofAdd (1 : ZMod 2) ∈ Subgroup.map parityUCharacter H := by
      rw [hUmap]
      exact Subgroup.mem_top _
    have hVtarget : ofAdd (1 : ZMod 2) ∈ Subgroup.map parityVCharacter H := by
      rw [hVmap]
      exact Subgroup.mem_top _
    have hDtarget : ofAdd (1 : ZMod 2) ∈
        Subgroup.map parityDiagonalCharacter H := by
      rw [hDmap]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hUtarget hVtarget hDtarget
    obtain ⟨x, hx, hxchar⟩ := hUtarget
    obtain ⟨y, hy, hychar⟩ := hVtarget
    obtain ⟨z, hz, hzchar⟩ := hDtarget
    have hxclass := (parityUCharacter_eq_nontrivial_iff x).mp hxchar
    have hyclass := (parityVCharacter_eq_nontrivial_iff y).mp hychar
    have hzclass := (parityDiagonalCharacter_eq_nontrivial_iff z).mp hzchar
    apply (parityCoordinateSubgroup_eq_top_iff_generators H).mpr
    rcases hzclass with rfl | rfl
    · refine ⟨hz, ?_⟩
      rcases hyclass with rfl | rfl
      · exact hy
      · have hmul : coordinateParityU *
            (coordinateParityU * coordinateParityV) = coordinateParityV := by
          decide
        rw [← hmul]
        exact H.mul_mem hz hy
    · refine ⟨?_, hz⟩
      rcases hxclass with rfl | rfl
      · exact hx
      · have hmul : (coordinateParityU * coordinateParityV) *
            coordinateParityV = coordinateParityU := by
          decide
        rw [← hmul]
        exact H.mul_mem hx hz

theorem zmodTwoMultiplicative_eq_one_or_nontrivial
    (z : Multiplicative (ZMod 2)) :
    z = 1 ∨ z = ofAdd (1 : ZMod 2) := by
  rw [← ofAdd_toAdd z]
  generalize toAdd z = a
  revert a
  decide

theorem zmodTwoSubgroup_eq_top_iff_nontrivial
    (H : Subgroup (Multiplicative (ZMod 2))) :
    H = ⊤ ↔ ofAdd (1 : ZMod 2) ∈ H := by
  constructor
  · intro hH
    rw [hH]
    exact Subgroup.mem_top _
  · intro hnontrivial
    apply top_unique
    intro z _
    have hz := zmodTwoMultiplicative_eq_one_or_nontrivial z
    rcases hz with rfl | rfl
    · exact H.one_mem
    · exact hnontrivial

theorem zmodTwoSubgroup_ne_top_iff_eq_bot
    (H : Subgroup (Multiplicative (ZMod 2))) :
    H ≠ ⊤ ↔ H = ⊥ := by
  constructor
  · intro hne
    ext z
    constructor
    · intro hz
      have hclass := zmodTwoMultiplicative_eq_one_or_nontrivial z
      rcases hclass with rfl | rfl
      · exact Subgroup.mem_bot.mpr rfl
      · exact False.elim (hne
          ((zmodTwoSubgroup_eq_top_iff_nontrivial H).mpr hz))
    · intro hz
      exact Subgroup.mem_bot.mp hz ▸ H.one_mem
  · rintro rfl htop
    have hnontrivial : ofAdd (1 : ZMod 2) ∈
        (⊥ : Subgroup (Multiplicative (ZMod 2))) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hone := Subgroup.mem_bot.mp hnontrivial
    exact (by decide : ofAdd (1 : ZMod 2) ≠
      (1 : Multiplicative (ZMod 2))) hone

theorem paritySubgroup_ne_top_iff_characterMaps_eq_bot
    (H : Subgroup OneHandleParityPlane) :
    H ≠ ⊤ ↔
      Subgroup.map parityUCharacter H = ⊥ ∨
        Subgroup.map parityVCharacter H = ⊥ ∨
          Subgroup.map parityDiagonalCharacter H = ⊥ := by
  constructor
  · intro hne
    have hnot : ¬ (Subgroup.map parityUCharacter H = ⊤ ∧
        Subgroup.map parityVCharacter H = ⊤ ∧
          Subgroup.map parityDiagonalCharacter H = ⊤) :=
      fun hall ↦ hne ((paritySubgroup_eq_top_iff_characterMaps H).mpr hall)
    simp only [not_and_or] at hnot
    rcases hnot with hU | hV | hD
    · exact Or.inl ((zmodTwoSubgroup_ne_top_iff_eq_bot _).mp hU)
    · exact Or.inr (Or.inl
        ((zmodTwoSubgroup_ne_top_iff_eq_bot _).mp hV))
    · exact Or.inr (Or.inr
        ((zmodTwoSubgroup_ne_top_iff_eq_bot _).mp hD))
  · intro hbot htop
    have hall := (paritySubgroup_eq_top_iff_characterMaps H).mp htop
    rcases hbot with hU | hV | hD
    · exact ((zmodTwoSubgroup_ne_top_iff_eq_bot _).mpr hU) hall.1
    · exact ((zmodTwoSubgroup_ne_top_iff_eq_bot _).mpr hV) hall.2.1
    · exact ((zmodTwoSubgroup_ne_top_iff_eq_bot _).mpr hD) hall.2.2

noncomputable def oneHandleBalancedCoreNeutralityCharacterRow
    (chi : OneHandleParityPlane →* Multiplicative (ZMod 2))
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreNeutralityInteractionSource p k hk →*
      Multiplicative (ZMod 2) :=
  chi.comp (oneHandleBalancedCoreNeutralityParityRow p k hk)

noncomputable def oneHandleBalancedCoreNeutralityUCharacterRow
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreNeutralityInteractionSource p k hk →*
      Multiplicative (ZMod 2) :=
  oneHandleBalancedCoreNeutralityCharacterRow parityUCharacter p k hk

noncomputable def oneHandleBalancedCoreNeutralityVCharacterRow
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreNeutralityInteractionSource p k hk →*
      Multiplicative (ZMod 2) :=
  oneHandleBalancedCoreNeutralityCharacterRow parityVCharacter p k hk

noncomputable def oneHandleBalancedCoreNeutralityDiagonalCharacterRow
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreNeutralityInteractionSource p k hk →*
      Multiplicative (ZMod 2) :=
  oneHandleBalancedCoreNeutralityCharacterRow parityDiagonalCharacter p k hk

theorem oneHandleBalancedCoreNeutralityCharacterRow_range_eq_map
    (chi : OneHandleParityPlane →* Multiplicative (ZMod 2))
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityCharacterRow chi p k hk).range =
      Subgroup.map chi
        (oneHandleBalancedCoreNeutralityParityRow p k hk).range := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨oneHandleBalancedCoreNeutralityParityRow p k hk x,
      ⟨x, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

theorem mem_oneHandleBalancedCoreNeutralityCharacterRow_range_iff
    (chi : OneHandleParityPlane →* Multiplicative (ZMod 2))
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (z : Multiplicative (ZMod 2)) :
    z ∈ (oneHandleBalancedCoreNeutralityCharacterRow chi p k hk).range ↔
      ∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        chi (coordinateParity (oneHandleRelativeCCoordinates k hk y)) = z ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, b, d, heq⟩ :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
        p k hk y.1).mp y.2
    exact ⟨y.1, a, b, d, hy, heq⟩
  · rintro ⟨y, a, b, d, hy, heq⟩
    have hymem : y ∈ oneHandleBalancedCoreNeutralityInteractionSource p k hk :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff p k hk y).mpr
        ⟨a, b, d, heq⟩
    exact ⟨⟨y, hymem⟩, hy⟩

theorem monoidHom_range_eq_bot_iff
    {G A : Type*} [Group G] [Group A] (f : G →* A) :
    f.range = ⊥ ↔ ∀ x, f x = 1 := by
  constructor
  · intro hrange x
    have hx : f x ∈ f.range := ⟨x, rfl⟩
    rw [hrange] at hx
    exact Subgroup.mem_bot.mp hx
  · intro h
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_bot.mpr (h x)
    · intro hz
      have hz1 := Subgroup.mem_bot.mp hz
      subst z
      exact f.range.one_mem

theorem oneHandleBalancedCoreNeutralityCharacterRow_range_eq_bot_iff
    (chi : OneHandleParityPlane →* Multiplicative (ZMod 2))
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityCharacterRow chi p k hk).range = ⊥ ↔
      ∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d →
          chi (coordinateParity (oneHandleRelativeCCoordinates k hk y)) = 1 := by
  rw [monoidHom_range_eq_bot_iff]
  constructor
  · intro h y a b d heq
    have hymem : y ∈ oneHandleBalancedCoreNeutralityInteractionSource p k hk :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff p k hk y).mpr
        ⟨a, b, d, heq⟩
    exact h ⟨y, hymem⟩
  · intro h y
    obtain ⟨a, b, d, heq⟩ :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
        p k hk y.1).mp y.2
    exact h y.1 a b d heq

theorem oneHandleBalancedCoreNeutralityCharacterRow_range_eq_top_iff
    (chi : OneHandleParityPlane →* Multiplicative (ZMod 2))
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityCharacterRow chi p k hk).range = ⊤ ↔
      ∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        chi (coordinateParity (oneHandleRelativeCCoordinates k hk y)) = ofAdd 1 ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d := by
  rw [zmodTwoSubgroup_eq_top_iff_nontrivial,
    mem_oneHandleBalancedCoreNeutralityCharacterRow_range_iff]

theorem oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_characters
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityParityRow p k hk).range = ⊤ ↔
      (oneHandleBalancedCoreNeutralityUCharacterRow p k hk).range = ⊤ ∧
        (oneHandleBalancedCoreNeutralityVCharacterRow p k hk).range = ⊤ ∧
          (oneHandleBalancedCoreNeutralityDiagonalCharacterRow p k hk).range = ⊤ := by
  rw [oneHandleBalancedCoreNeutralityUCharacterRow,
    oneHandleBalancedCoreNeutralityVCharacterRow,
    oneHandleBalancedCoreNeutralityDiagonalCharacterRow,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_map,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_map,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_map,
    paritySubgroup_eq_top_iff_characterMaps]

theorem oneHandleBalancedCoreNeutralityParityRow_ne_top_iff_characterBots
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityParityRow p k hk).range ≠ ⊤ ↔
      (oneHandleBalancedCoreNeutralityUCharacterRow p k hk).range = ⊥ ∨
        (oneHandleBalancedCoreNeutralityVCharacterRow p k hk).range = ⊥ ∨
          (oneHandleBalancedCoreNeutralityDiagonalCharacterRow p k hk).range = ⊥ := by
  rw [oneHandleBalancedCoreNeutralityUCharacterRow,
    oneHandleBalancedCoreNeutralityVCharacterRow,
    oneHandleBalancedCoreNeutralityDiagonalCharacterRow,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_map,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_map,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_map,
    paritySubgroup_ne_top_iff_characterMaps_eq_bot]

theorem oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_scalarCABD
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityParityRow p k hk).range = ⊤ ↔
      (∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        parityUCharacter
              (coordinateParity (oneHandleRelativeCCoordinates k hk y)) =
            ofAdd 1 ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d) ∧
      (∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        parityVCharacter
              (coordinateParity (oneHandleRelativeCCoordinates k hk y)) =
            ofAdd 1 ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d) ∧
      (∃ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        parityDiagonalCharacter
              (coordinateParity (oneHandleRelativeCCoordinates k hk y)) =
            ofAdd 1 ∧
          oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d) := by
  rw [oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_characters,
    oneHandleBalancedCoreNeutralityUCharacterRow,
    oneHandleBalancedCoreNeutralityVCharacterRow,
    oneHandleBalancedCoreNeutralityDiagonalCharacterRow,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_top_iff,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_top_iff,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_top_iff]

theorem oneHandleBalancedCoreNeutralityParityRow_ne_top_iff_scalarAnnihilator
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityParityRow p k hk).range ≠ ⊤ ↔
      (∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d →
          parityUCharacter
              (coordinateParity (oneHandleRelativeCCoordinates k hk y)) = 1) ∨
      (∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d →
          parityVCharacter
              (coordinateParity (oneHandleRelativeCCoordinates k hk y)) = 1) ∨
      (∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
        oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
            oneHandleBalancedCoreRelativeShiftA p k hk a *
              oneHandleBalancedCoreRelativeShiftB p k hk b *
                oneHandleBalancedCoreRelativeShiftD p k hk d →
          parityDiagonalCharacter
              (coordinateParity (oneHandleRelativeCCoordinates k hk y)) = 1) := by
  rw [oneHandleBalancedCoreNeutralityParityRow_ne_top_iff_characterBots,
    oneHandleBalancedCoreNeutralityUCharacterRow,
    oneHandleBalancedCoreNeutralityVCharacterRow,
    oneHandleBalancedCoreNeutralityDiagonalCharacterRow,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_bot_iff,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_bot_iff,
    oneHandleBalancedCoreNeutralityCharacterRow_range_eq_bot_iff]

def OneHandleBalancedCoreNeutralityCharacterSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint)
    (_hp : p ∈ oneHandleBalancedSet Psi0 k),
      (oneHandleBalancedCoreNeutralityUCharacterRow p k hk).range = ⊤ ∧
        (oneHandleBalancedCoreNeutralityVCharacterRow p k hk).range = ⊤ ∧
          (oneHandleBalancedCoreNeutralityDiagonalCharacterRow p k hk).range = ⊤

theorem paritySupply_iff_characterSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreNeutralityParitySupply Psi0 ↔
      OneHandleBalancedCoreNeutralityCharacterSupply Psi0 := by
  constructor <;> intro H k hk p hp
  · exact (oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_characters
      p k hk).mp (H k hk p hp)
  · exact (oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_characters
      p k hk).mpr (H k hk p hp)

theorem mpcPivShiftH_two_one_of_balancedRelative_and_characters
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hrel : OneHandleBalancedCoreRelativeCoordinateSpanSupply Psi0)
    (Hchars : OneHandleBalancedCoreNeutralityCharacterSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedRelative_and_parity Psi0 hchi0 hrow Hrel
    ((paritySupply_iff_characterSupply Psi0).mpr Hchars)

#print axioms parityUCharacter
#print axioms parityVCharacter
#print axioms parityDiagonalCharacter
#print axioms parityUCharacter_surjective
#print axioms parityVCharacter_surjective
#print axioms parityDiagonalCharacter_surjective
#print axioms parityUCharacter_eq_nontrivial_iff
#print axioms parityVCharacter_eq_nontrivial_iff
#print axioms parityDiagonalCharacter_eq_nontrivial_iff
#print axioms paritySubgroup_eq_top_iff_characterMaps
#print axioms zmodTwoMultiplicative_eq_one_or_nontrivial
#print axioms zmodTwoSubgroup_eq_top_iff_nontrivial
#print axioms zmodTwoSubgroup_ne_top_iff_eq_bot
#print axioms paritySubgroup_ne_top_iff_characterMaps_eq_bot
#print axioms oneHandleBalancedCoreNeutralityCharacterRow
#print axioms oneHandleBalancedCoreNeutralityUCharacterRow
#print axioms oneHandleBalancedCoreNeutralityVCharacterRow
#print axioms oneHandleBalancedCoreNeutralityDiagonalCharacterRow
#print axioms oneHandleBalancedCoreNeutralityCharacterRow_range_eq_map
#print axioms mem_oneHandleBalancedCoreNeutralityCharacterRow_range_iff
#print axioms monoidHom_range_eq_bot_iff
#print axioms oneHandleBalancedCoreNeutralityCharacterRow_range_eq_bot_iff
#print axioms oneHandleBalancedCoreNeutralityCharacterRow_range_eq_top_iff
#print axioms oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_characters
#print axioms oneHandleBalancedCoreNeutralityParityRow_ne_top_iff_characterBots
#print axioms oneHandleBalancedCoreNeutralityParityRow_range_eq_top_iff_scalarCABD
#print axioms oneHandleBalancedCoreNeutralityParityRow_ne_top_iff_scalarAnnihilator
#print axioms OneHandleBalancedCoreNeutralityCharacterSupply
#print axioms paritySupply_iff_characterSupply
#print axioms mpcPivShiftH_two_one_of_balancedRelative_and_characters

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityDual
