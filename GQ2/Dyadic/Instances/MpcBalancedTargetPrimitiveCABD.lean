/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetParityCABD

/-!
# The six primitive target CABD implications

W240 isolates three scalar parity implications. This file treats the six primitive
order-four directions in the same target-sensitive form.

For each primitive direction, if its `ZMod 4` dot product annihilates the C coordinate of
every homogeneous CABD relation, it must annihilate the selected target C coordinates. This
condition is exactly the negation of primitive target detection.

The final theorem combines both layers: the selected target belongs to the correction span
exactly when the three parity implications and the six primitive implications all hold.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetPrimitiveCABD

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
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacterCoordinates
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacterDot
open GQ2.Dyadic.Instances.MpcBalancedTargetDirectionCases
open GQ2.Dyadic.Instances.MpcBalancedTargetParityDirections
open GQ2.Dyadic.Instances.MpcBalancedTargetParityCoverage
open GQ2.Dyadic.Instances.MpcBalancedTargetParityCABD

private theorem targetDot_eq_of_factor_eq
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (a b : ZMod 4)
    (hkill : ∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
      oneHandleZModFourDot a b
          (oneHandleBalancedCoreNeutralityCoordinateRow p k hk x) = 0)
    (z w : Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (hfactor : oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
      oneHandleBalancedCoreNeutralityCoordinateFactor p k hk w) :
    oneHandleZModFourDot a b z = oneHandleZModFourDot a b w := by
  have hdiffker : z * w⁻¹ ∈
      (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hfactor, mul_inv_cancel]
  have hdiffH : z * w⁻¹ ∈
      (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range := by
    rw [oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker]
    exact hdiffker
  rcases hdiffH with ⟨x, hx⟩
  have hdot := hkill x
  rw [hx] at hdot
  rcases z with ⟨zu, zv⟩
  rcases w with ⟨wu, wv⟩
  change a * (zu * wu⁻¹).toAdd + b * (zv * wv⁻¹).toAdd = 0 at hdot
  rw [toAdd_mul, toAdd_inv, toAdd_mul, toAdd_inv] at hdot
  change a * zu.toAdd + b * zv.toAdd = a * wu.toAdd + b * wv.toAdd
  linear_combination hdot

def OneHandleBalancedCoreTargetPrimitiveCABDCompatible
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∀ i : Fin 6,
    (∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
      oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
          oneHandleBalancedCoreRelativeShiftA p k hk a *
            oneHandleBalancedCoreRelativeShiftB p k hk b *
              oneHandleBalancedCoreRelativeShiftD p k hk d →
        oneHandleZModFourDot
          (oneHandlePrimitiveDirectionCoeffs i).1
          (oneHandlePrimitiveDirectionCoeffs i).2
          (oneHandleRelativeCCoordinates k hk y) = 0) →
    oneHandleZModFourDot
      (oneHandlePrimitiveDirectionCoeffs i).1
      (oneHandlePrimitiveDirectionCoeffs i).2
      (oneHandleRelativeCCoordinates k hk
        (oneHandleBalancedCoreTargetCRepresentative p hk hp hrel)) = 0

private theorem primitive_kills_interaction_iff_CABD
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (i : Fin 6) :
    (∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
      oneHandleZModFourDot
        (oneHandlePrimitiveDirectionCoeffs i).1
        (oneHandlePrimitiveDirectionCoeffs i).2
        (oneHandleBalancedCoreNeutralityCoordinateRow p k hk x) = 0) ↔
    ∀ y a b d : oneHandleRelativeLambdaImage (k - 1) (k + 1),
      oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y =
          oneHandleBalancedCoreRelativeShiftA p k hk a *
            oneHandleBalancedCoreRelativeShiftB p k hk b *
              oneHandleBalancedCoreRelativeShiftD p k hk d →
        oneHandleZModFourDot
          (oneHandlePrimitiveDirectionCoeffs i).1
          (oneHandlePrimitiveDirectionCoeffs i).2
          (oneHandleRelativeCCoordinates k hk y) = 0 := by
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

theorem targetPrimitiveCaseDetected_iff_not_CABDCompatible
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetPrimitiveCaseDetected p hk hp hrel ↔
      ¬ OneHandleBalancedCoreTargetPrimitiveCABDCompatible p hk hp hrel := by
  constructor
  · rintro ⟨z, hz, i, htarget, hrows⟩ Hcompat
    have hkill : ∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
        oneHandleZModFourDot
          (oneHandlePrimitiveDirectionCoeffs i).1
          (oneHandlePrimitiveDirectionCoeffs i).2
          (oneHandleBalancedCoreNeutralityCoordinateRow p k hk x) = 0 := by
      intro x
      exact hrows x
    have htargetEq := targetDot_eq_of_factor_eq p k hk
      (oneHandlePrimitiveDirectionCoeffs i).1
      (oneHandlePrimitiveDirectionCoeffs i).2 hkill z
      (oneHandleRelativeCCoordinates k hk
        (oneHandleBalancedCoreTargetCRepresentative p hk hp hrel))
      (hz.trans
        (oneHandleBalancedCoreTargetCRepresentative_factor p hk hp hrel).symm)
    apply htarget
    rw [htargetEq]
    exact Hcompat i ((primitive_kills_interaction_iff_CABD p k hk i).mp hkill)
  · intro Hnot
    simp only [OneHandleBalancedCoreTargetPrimitiveCABDCompatible] at Hnot
    push Not at Hnot
    obtain ⟨i, hkillCABD, htarget⟩ := Hnot
    let z := oneHandleRelativeCCoordinates k hk
      (oneHandleBalancedCoreTargetCRepresentative p hk hp hrel)
    refine ⟨z, oneHandleBalancedCoreTargetCRepresentative_factor p hk hp hrel,
      i, htarget, ?_⟩
    intro x
    exact (primitive_kills_interaction_iff_CABD p k hk i).mpr hkillCABD x

theorem target_mem_coordinateSpan_iff_parity_and_primitive_CABD
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    oneHandleBalancedCoreRelativeTarget p hp ∈
        oneHandleBalancedCoreCoordinateSpan p k hk ↔
      OneHandleBalancedCoreTargetParityCABDCompatible p hk hp hrel ∧
        OneHandleBalancedCoreTargetPrimitiveCABDCompatible p hk hp hrel := by
  constructor
  · intro hspan
    constructor
    · by_contra hpar
      have hnotCovered :
          ¬ OneHandleBalancedCoreTargetParityCovered p hk hp hrel := by
        intro hcovered
        exact hpar ((targetParityCovered_iff_CABDCompatible
          p hk hp hrel).mp hcovered)
      have hnotSpan :=
        (target_not_coordinateSpan_iff_primitive_or_not_parityCovered
          p hk hp hrel).mpr (Or.inr hnotCovered)
      exact hnotSpan hspan
    · by_contra hprim
      have hdetected :=
        (targetPrimitiveCaseDetected_iff_not_CABDCompatible
          p hk hp hrel).mpr hprim
      have hnotSpan :=
        (target_not_coordinateSpan_iff_primitive_or_not_parityCovered
          p hk hp hrel).mpr (Or.inl hdetected)
      exact hnotSpan hspan
  · rintro ⟨hpar, hprim⟩
    by_contra hnotSpan
    rcases (target_not_coordinateSpan_iff_primitive_or_not_parityCovered
      p hk hp hrel).mp hnotSpan with hdetected | hnotCovered
    · exact (targetPrimitiveCaseDetected_iff_not_CABDCompatible
        p hk hp hrel).mp hdetected hprim
    · exact hnotCovered
        ((targetParityCovered_iff_CABDCompatible p hk hp hrel).mpr hpar)

#print axioms OneHandleBalancedCoreTargetPrimitiveCABDCompatible
#print axioms targetPrimitiveCaseDetected_iff_not_CABDCompatible
#print axioms target_mem_coordinateSpan_iff_parity_and_primitive_CABD

end
end GQ2.Dyadic.Instances.MpcBalancedTargetPrimitiveCABD
