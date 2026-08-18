/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingTargetRank

/-!
# Finite full solutions of the one-handle class-seven problem

W282 realizes every compact-kernel correction by a canonical legal lift.  A correction is a
full solution when its connecting value equals the reference ordinary obstruction and the
remaining neutral-C obstruction of that canonical lift vanishes.

This solution type is finite.  Its nonemptiness is equivalent to actual W6 correctability:
the forward implication applies the correction, while the reverse implication compares an
arbitrary correctable lift with the canonical realization of its finite difference.  Equality
of their finite direct tuples forces equality of their residual targets.  Thus both the
ordinary connecting condition and the neutral-C condition now live in one exact finite search.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCoordinates
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeFiniteLiftIndependence
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization

theorem compactKernelCorrectionLift_obstruction_eq_one_of_connects
    (E : OneHandleC7RelativeLift) (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E) :
    oneHandleC7StandardRelativeObstruction
        (compactKernelCorrectionLift E D) = 1 := by
  rw [relativeObstruction_eq_connecting_inv_mul E
    (compactKernelCorrectionLift E D)]
  have hdiff := realizedCompactKernelDifference_correctionLift E D
  have hconn : oneHandleCompactConnectingHom
      (realizedCompactKernelDifference E (compactKernelCorrectionLift E D)) =
        oneHandleCompactConnectingHom D := by
    congr 1
    exact Subtype.ext hdiff
  rw [hconn, hD]
  group

def compactKernelCorrectionLift_relaxed
    (E : OneHandleC7RelativeLift) (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E) :
    oneHandleC7RelativeTarget (compactKernelCorrectionLift E D) ∈
      oneHandleStandardRelativeRelaxedCoordinateSpan :=
  (standardRelativeObstruction_eq_one_iff _).mp
    (compactKernelCorrectionLift_obstruction_eq_one_of_connects E D hD)

structure OneHandleCompactKernelFullSolution
    (E : OneHandleC7RelativeLift) where
  correction : OneHandleCompactKernelCorrection
  connects : oneHandleCompactConnectingHom correction =
    oneHandleC7StandardRelativeObstruction E
  neutral : oneHandleC7StandardNeutralityObstruction
    (compactKernelCorrectionLift E correction)
    (compactKernelCorrectionLift_relaxed E correction connects) = 1

noncomputable instance (E : OneHandleC7RelativeLift) :
    Finite (OneHandleCompactKernelFullSolution E) := by
  let f : OneHandleCompactKernelFullSolution E →
      OneHandleCompactKernelCorrection := fun S ↦ S.correction
  apply Finite.of_injective f
  intro S T h
  cases S
  cases T
  cases h
  rfl

theorem relativeResidual_eq_of_toDirect_eq
    (E F : OneHandleC7RelativeLift)
    (h : relativeLiftToDirect E = relativeLiftToDirect F) :
    E.residual = F.residual := by
  have hshift := congrArg
    (oneHandleDirectLevelShift oneHandleW6Mark) h
  rw [relativeLift_levelShift E, relativeLift_levelShift F] at hshift
  exact mul_left_cancel hshift

theorem relativeTarget_eq_of_toDirect_eq
    (E F : OneHandleC7RelativeLift)
    (h : relativeLiftToDirect E = relativeLiftToDirect F) :
    oneHandleC7RelativeTarget E = oneHandleC7RelativeTarget F := by
  apply Subtype.ext
  change E.residual⁻¹ = F.residual⁻¹
  rw [relativeResidual_eq_of_toDirect_eq E F h]

theorem nonempty_compactKernelFullSolution_iff_oneHandleW6Correctable
    (E : OneHandleC7RelativeLift) :
    Nonempty (OneHandleCompactKernelFullSolution E) ↔
      OneHandleW6Correctable := by
  constructor
  · rintro ⟨S⟩
    apply oneHandleW6Correctable_of_relativeCorrectable
      (compactKernelCorrectionLift E S.correction)
    rw [relativeCorrectable_iff_relaxed_and_neutrality]
    exact ⟨compactKernelCorrectionLift_relaxed E S.correction S.connects,
      S.neutral⟩
  · intro hcorrect
    obtain ⟨F, hF⟩ :=
      oneHandleW6Correctable_iff_exists_relativeCorrectable.mp hcorrect
    let D : OneHandleCompactKernelCorrection :=
      realizedCompactKernelDifference E F
    have hFcoord : oneHandleC7RelativeTarget F ∈
        oneHandleStandardRelativeCoordinateSpan :=
      (relativeCorrectable_iff_standard_target_mem_coordinateSpan F).mp hF
    have hFrel : oneHandleC7RelativeTarget F ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan :=
      standardRelativeCoordinateSpan_le_relaxed hFcoord
    have hFobs : oneHandleC7StandardRelativeObstruction F = 1 :=
      (standardRelativeObstruction_eq_one_iff F).mpr hFrel
    have hcoc := relativeObstruction_eq_connecting_inv_mul E F
    have hconnect : oneHandleCompactConnectingHom D =
        oneHandleC7StandardRelativeObstruction E := by
      calc
        oneHandleCompactConnectingHom D =
            oneHandleCompactConnectingHom D * 1 := by group
        _ = oneHandleCompactConnectingHom D *
            oneHandleC7StandardRelativeObstruction F := by rw [hFobs]
        _ = oneHandleCompactConnectingHom D *
            ((oneHandleCompactConnectingHom D)⁻¹ *
              oneHandleC7StandardRelativeObstruction E) := by rw [← hcoc]
        _ = oneHandleC7StandardRelativeObstruction E := by group
    have hdirect : relativeLiftToDirect (compactKernelCorrectionLift E D) =
        relativeLiftToDirect F := by
      rw [compactKernelCorrectionLift_toDirect]
      change relativeLiftToDirect E *
        ((relativeLiftToDirect E)⁻¹ * relativeLiftToDirect F) = _
      group
    have htarget : oneHandleC7RelativeTarget
        (compactKernelCorrectionLift E D) = oneHandleC7RelativeTarget F :=
      relativeTarget_eq_of_toDirect_eq _ _ hdirect
    refine ⟨⟨D, hconnect, ?_⟩⟩
    apply (standardNeutralityObstruction_eq_one_iff _ _).mpr
    rw [htarget]
    exact hFcoord

noncomputable def compactKernelFullSolutions
    (E : OneHandleC7RelativeLift) :
    Finset (OneHandleCompactKernelFullSolution E) := by
  letI := Fintype.ofFinite (OneHandleCompactKernelFullSolution E)
  exact Finset.univ

theorem compactKernelFullSolutions_nonempty_iff
    (E : OneHandleC7RelativeLift) :
    (compactKernelFullSolutions E).Nonempty ↔ OneHandleW6Correctable := by
  classical
  constructor
  · rintro ⟨S, -⟩
    exact (nonempty_compactKernelFullSolution_iff_oneHandleW6Correctable E).mp
      ⟨S⟩
  · intro h
    obtain ⟨S⟩ :=
      (nonempty_compactKernelFullSolution_iff_oneHandleW6Correctable E).mpr h
    exact ⟨S, by simp [compactKernelFullSolutions]⟩

#print axioms compactKernelCorrectionLift_obstruction_eq_one_of_connects
#print axioms compactKernelCorrectionLift_relaxed
#print axioms OneHandleCompactKernelFullSolution
#print axioms relativeResidual_eq_of_toDirect_eq
#print axioms relativeTarget_eq_of_toDirect_eq
#print axioms nonempty_compactKernelFullSolution_iff_oneHandleW6Correctable
#print axioms compactKernelFullSolutions
#print axioms compactKernelFullSolutions_nonempty_iff

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution
