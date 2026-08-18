/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetCABDSelectable

/-!
# Literal CABD certificates for failure of a balanced successor

W242 states the positive nine-CABD successor criterion. This file records its exact negative
form. At a relatively covered point, CABD detection means that one of the three parity or six
primitive scalar functionals annihilates every homogeneous CABD relation but not the selected
target coordinates.

The next stage is empty exactly when every point in the current stage either fails ordinary
relative coverage or has such a literal detecting functional. Thus both a positive proof and a
negative proof now have finite, target-specific certificates.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetCABDObstruction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleCoordinates
open GQ2.Dyadic.Instances.MpcBalancedNeutralityParity
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacterDot
open GQ2.Dyadic.Instances.MpcBalancedTargetDirectionCases
open GQ2.Dyadic.Instances.MpcBalancedTargetParityDirections
open GQ2.Dyadic.Instances.MpcBalancedTargetParityCABD
open GQ2.Dyadic.Instances.MpcBalancedTargetPrimitiveCABD
open GQ2.Dyadic.Instances.MpcBalancedTargetCABDSelectable

/-- A literal one-of-nine scalar detector for a relatively covered selected target. -/
def OneHandleBalancedCoreTargetCABDDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  (∃ i : Fin 3,
    (∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
      oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
          oneHandleBalancedCoreRelativeShiftA p k hk a *
            oneHandleBalancedCoreRelativeShiftB p k hk b *
              oneHandleBalancedCoreRelativeShiftD p k hk d →
        oneHandleParityDirectionCharacter i
          (coordinateParity (oneHandleRelativeCCoordinates k hk y)) = 1) ∧
    oneHandleParityDirectionCharacter i
        (coordinateParity
          (oneHandleRelativeCCoordinates k hk
            (oneHandleBalancedCoreTargetCRepresentative p hk hp hrel))) ≠ 1) ∨
  (∃ i : Fin 6,
    (∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
      oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
          oneHandleBalancedCoreRelativeShiftA p k hk a *
            oneHandleBalancedCoreRelativeShiftB p k hk b *
              oneHandleBalancedCoreRelativeShiftD p k hk d →
        oneHandleZModFourDot
          (oneHandlePrimitiveDirectionCoeffs i).1
          (oneHandlePrimitiveDirectionCoeffs i).2
          (oneHandleRelativeCCoordinates k hk y) = 0) ∧
    oneHandleZModFourDot
        (oneHandlePrimitiveDirectionCoeffs i).1
        (oneHandlePrimitiveDirectionCoeffs i).2
        (oneHandleRelativeCCoordinates k hk
          (oneHandleBalancedCoreTargetCRepresentative p hk hp hrel)) ≠ 0)

/-- Literal detection is exactly failure of at least one of the nine CABD implications. -/
theorem targetCABDDetected_iff_not_compatible
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetCABDDetected p hk hp hrel ↔
      ¬ (OneHandleBalancedCoreTargetParityCABDCompatible p hk hp hrel ∧
        OneHandleBalancedCoreTargetPrimitiveCABDCompatible p hk hp hrel) := by
  constructor
  · rintro (⟨i, hkill, htarget⟩ | ⟨i, hkill, htarget⟩) ⟨hpar, hprim⟩
    · exact htarget (hpar i hkill)
    · exact htarget (hprim i hkill)
  · intro Hnot
    by_cases hpar :
        OneHandleBalancedCoreTargetParityCABDCompatible p hk hp hrel
    · right
      have hprim :
          ¬ OneHandleBalancedCoreTargetPrimitiveCABDCompatible p hk hp hrel :=
        fun hprim ↦ Hnot ⟨hpar, hprim⟩
      simp only [OneHandleBalancedCoreTargetPrimitiveCABDCompatible] at hprim
      push Not at hprim
      exact hprim
    · left
      simp only [OneHandleBalancedCoreTargetParityCABDCompatible] at hpar
      push Not at hpar
      exact hpar

/-- The next stage is empty exactly when every current point either lacks ordinary relative
coverage or carries a literal one-of-nine CABD detector. -/
theorem oneHandleBalancedSet_succ_empty_iff_pointwise_CABDObstruction
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (k : ℕ) (hk : 3 ≤ k) :
    ¬ (oneHandleBalancedSet Psi0 (k + 1)).Nonempty ↔
      ∀ p : OneHandleBalancedPoint,
        ∀ hp : p ∈ oneHandleBalancedSet Psi0 k,
          oneHandleBalancedCoreRelativeTarget p hp ∉
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk ∨
            ∃ hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk,
                OneHandleBalancedCoreTargetCABDDetected p hk hp hrel := by
  constructor
  · intro H p hp
    by_cases hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreRelativeCoordinateSpan p k hk
    · right
      refine ⟨hrel, (targetCABDDetected_iff_not_compatible
        p hk hp hrel).mpr ?_⟩
      intro hCABD
      exact H ((oneHandleBalancedSet_succ_nonempty_iff_exists_targetCABD
        Psi0 k hk).mpr ⟨p, hp, hrel, hCABD⟩)
    · exact Or.inl hrel
  · intro H hsucc
    obtain ⟨p, hp, hrel, hCABD⟩ :=
      (oneHandleBalancedSet_succ_nonempty_iff_exists_targetCABD
        Psi0 k hk).mp hsucc
    rcases H p hp with hnrel | ⟨hrel', hdet⟩
    · exact hnrel hrel
    · have hcompat' :=
        (targetCABDDetected_iff_not_compatible p hk hp hrel').mp hdet
      have hrelEq : hrel' = hrel := Subsingleton.elim _ _
      cases hrelEq
      exact hcompat' hCABD

#print axioms OneHandleBalancedCoreTargetCABDDetected
#print axioms targetCABDDetected_iff_not_compatible
#print axioms oneHandleBalancedSet_succ_empty_iff_pointwise_CABDObstruction

end
end GQ2.Dyadic.Instances.MpcBalancedTargetCABDObstruction
