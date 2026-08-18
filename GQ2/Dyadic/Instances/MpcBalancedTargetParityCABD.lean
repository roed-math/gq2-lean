/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetParityDual

/-!
# The target parity obstruction as three scalar CABD implications

W239 reduces parity coverage to three scalar character compatibilities. This file removes
the abstract interaction source from those compatibilities.

Choose one ordinary relative `C` class representing the selected neutrality obstruction.
For each of the three parity characters, parity coverage says exactly that annihilating every
homogeneous CABD relation forces the character to annihilate the two coordinates of this
target `C` representative. Character values are independent of all choices by W239.

This is the literal finite graded calculation still required on the parity side; no quotient
or unspecified character remains in its statement.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetParityCABD

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
open GQ2.Dyadic.Instances.MpcBalancedNeutralityEquation
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleCoordinates
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityParity
open GQ2.Dyadic.Instances.MpcBalancedNeutralityDual
open GQ2.Dyadic.Instances.MpcBalancedTargetParityDirections
open GQ2.Dyadic.Instances.MpcBalancedTargetParityCoverage
open GQ2.Dyadic.Instances.MpcBalancedTargetParityObstruction
open GQ2.Dyadic.Instances.MpcBalancedTargetParityDual

noncomputable def oneHandleBalancedCoreTargetCRepresentative
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleRelativeLambdaImage (k - 1) (k + 1) :=
  Classical.choose
    (exists_relativeC_class_eq_neutralityObstruction p hk hp hrel)

theorem oneHandleBalancedCoreTargetCRepresentative_class
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreNeutralityClassHom p k hk
        (oneHandleBalancedCoreTargetCRepresentative p hk hp hrel) =
      oneHandleBalancedCoreNeutralityObstruction p hk hp hrel :=
  Classical.choose_spec
    (exists_relativeC_class_eq_neutralityObstruction p hk hp hrel)

theorem oneHandleBalancedCoreTargetCRepresentative_factor
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk
        (oneHandleRelativeCCoordinates k hk
          (oneHandleBalancedCoreTargetCRepresentative p hk hp hrel)) =
      oneHandleBalancedCoreNeutralityObstruction p hk hp hrel := by
  rw [oneHandleBalancedCoreNeutralityCoordinateFactor_coordinates]
  exact oneHandleBalancedCoreTargetCRepresentative_class p hk hp hrel

theorem targetParityCharacter_eq_CRepresentative
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (i : Fin 3)
    (hkill : ∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
      oneHandleParityDirectionCharacter i
          (oneHandleBalancedCoreNeutralityParityRow p k hk x) = 1) :
    oneHandleParityDirectionCharacter i
        (coordinateParity
          (oneHandleBalancedCoreTargetParityLift p hk hp hrel)) =
      oneHandleParityDirectionCharacter i
        (coordinateParity
          (oneHandleRelativeCCoordinates k hk
            (oneHandleBalancedCoreTargetCRepresentative p hk hp hrel))) := by
  apply targetParityCharacter_eq_of_factor_eq p k hk i hkill
  exact (oneHandleBalancedCoreTargetParityLift_factor p hk hp hrel).trans
    (oneHandleBalancedCoreTargetCRepresentative_factor p hk hp hrel).symm

def OneHandleBalancedCoreTargetParityCABDCompatible
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∀ i : Fin 3,
    (∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
      oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
          oneHandleBalancedCoreRelativeShiftA p k hk a *
            oneHandleBalancedCoreRelativeShiftB p k hk b *
              oneHandleBalancedCoreRelativeShiftD p k hk d →
        oneHandleParityDirectionCharacter i
          (coordinateParity (oneHandleRelativeCCoordinates k hk y)) = 1) →
    oneHandleParityDirectionCharacter i
        (coordinateParity
          (oneHandleRelativeCCoordinates k hk
            (oneHandleBalancedCoreTargetCRepresentative p hk hp hrel))) = 1

private theorem character_kills_interaction_iff_CABD
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (i : Fin 3) :
    (∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
      oneHandleParityDirectionCharacter i
          (oneHandleBalancedCoreNeutralityParityRow p k hk x) = 1) ↔
    ∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
      oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
          oneHandleBalancedCoreRelativeShiftA p k hk a *
            oneHandleBalancedCoreRelativeShiftB p k hk b *
              oneHandleBalancedCoreRelativeShiftD p k hk d →
        oneHandleParityDirectionCharacter i
          (coordinateParity (oneHandleRelativeCCoordinates k hk y)) = 1 := by
  constructor
  · intro h y a b d heq
    have hy : y ∈ oneHandleBalancedCoreNeutralityInteractionSource p k hk :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
        p k hk y).mpr ⟨a, b, d, heq⟩
    exact h ⟨y, hy⟩
  · intro h x
    obtain ⟨a, b, d, heq⟩ :=
      (mem_oneHandleBalancedCoreNeutralityInteractionSource_iff
        p k hk x.1).mp x.2
    exact h x.1 a b d heq

theorem targetParityCharacterCompatible_iff_CABDCompatible
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetParityCharacterCompatible p hk hp hrel ↔
      OneHandleBalancedCoreTargetParityCABDCompatible p hk hp hrel := by
  constructor
  · intro H i hCABD
    have hkill := (character_kills_interaction_iff_CABD p k hk i).mpr hCABD
    have ht := H i hkill
    rw [targetParityCharacter_eq_CRepresentative p hk hp hrel i hkill] at ht
    exact ht
  · intro H i hkill
    rw [targetParityCharacter_eq_CRepresentative p hk hp hrel i hkill]
    exact H i ((character_kills_interaction_iff_CABD p k hk i).mp hkill)

theorem targetParityCovered_iff_CABDCompatible
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetParityCovered p hk hp hrel ↔
      OneHandleBalancedCoreTargetParityCABDCompatible p hk hp hrel := by
  rw [targetParityCovered_iff_characterCompatible,
    targetParityCharacterCompatible_iff_CABDCompatible]

#print axioms oneHandleBalancedCoreTargetCRepresentative
#print axioms oneHandleBalancedCoreTargetCRepresentative_class
#print axioms oneHandleBalancedCoreTargetCRepresentative_factor
#print axioms targetParityCharacter_eq_CRepresentative
#print axioms OneHandleBalancedCoreTargetParityCABDCompatible
#print axioms targetParityCharacterCompatible_iff_CABDCompatible
#print axioms targetParityCovered_iff_CABDCompatible

end
end GQ2.Dyadic.Instances.MpcBalancedTargetParityCABD
