/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeEquation

/-!
# Independence of the class-seven target from relative lift choices

Two direct lift packets of the same compact class-seven packet differ coordinatewise by exact
relative depth-five classes.  The `C` ratio is character-neutral because both lifted `C` rows
are neutral.  These four ratios therefore form a legal relative correction.

The new residual is the old residual times the standard relative shift of that correction.
Thus the two inverse targets define the same class modulo the standard coordinate span.  In
particular ordinary relaxed coverage, the literal row equation, and the zero-or-one rank jump
depend only on the compact packet, not on its arbitrary direct relative lifts.

This does not compare different compact class-seven successor packets.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeLiftIndependence

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenBaseReduction
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCoordinates
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRank
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRankJump
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeEquation
open GQ2.Roe.Labute

private abbrev H := DM 2 1

private theorem factorRatio_depth (E F : OneHandleC7RelativeLift)
    (i : Fin (coreRank 1)) :
    (E.factors i)⁻¹ * F.factors i ∈ twoCentralSeries H 5 :=
  Subgroup.mul_mem _ (Subgroup.inv_mem _ (E.depth i)) (F.depth i)

private theorem factorRatio_forget (E F : OneHandleC7RelativeLift)
    (hcompact : E.compactFactors = F.compactFactors)
    (i : Fin (coreRank 1)) :
    dmForgetHandles 2 1 ((E.factors i)⁻¹ * F.factors i) = 1 := by
  rw [map_mul, map_inv, E.forget, F.forget, congrFun hcompact i,
    inv_mul_cancel]

private theorem factorRatio_row (E F : OneHandleC7RelativeLift)
    (f : ContinuousMonoidHom H (Multiplicative ℤ_[2])) :
    toAdd (f ((E.factors 2)⁻¹ * F.factors 2)) = 0 := by
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, E.row, F.row]
  simp

/-- The exact relative correction taking one lift packet to another lift of the same compact
packet. -/
def relativeLiftDifference (E F : OneHandleC7RelativeLift)
    (hcompact : E.compactFactors = F.compactFactors) :
    OneHandleBalancedCoreLevelCorrection 6 where
  corrA := ⟨levelMk H 7 ((E.factors 0)⁻¹ * F.factors 0),
    (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) _).mpr
      ⟨_, factorRatio_depth E F 0, factorRatio_forget E F hcompact 0, rfl⟩⟩
  corrB := ⟨levelMk H 7 ((E.factors 1)⁻¹ * F.factors 1),
    (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) _).mpr
      ⟨_, factorRatio_depth E F 1, factorRatio_forget E F hcompact 1, rfl⟩⟩
  corrC := ⟨levelMk H 7 ((E.factors 2)⁻¹ * F.factors 2),
    (mem_oneHandleNeutralRelativeLambdaImage_iff_exists_exact _).mpr
      ⟨_, factorRatio_depth E F 2, factorRatio_forget E F hcompact 2,
        factorRatio_row E F, rfl⟩⟩
  corrD := ⟨levelMk H 7 ((E.factors 3)⁻¹ * F.factors 3),
    (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) _).mpr
      ⟨_, factorRatio_depth E F 3, factorRatio_forget E F hcompact 3, rfl⟩⟩

theorem relativeLiftToDirect_mul_difference
    (E F : OneHandleC7RelativeLift)
    (hcompact : E.compactFactors = F.compactFactors) :
    relativeLiftToDirect E *
      relativeCoreToDirect (relativeLiftDifference E F hcompact) =
      relativeLiftToDirect F := by
  apply Prod.ext
  · apply Subtype.ext
    change levelMk H 7 (E.factors 0) *
      levelMk H 7 ((E.factors 0)⁻¹ * F.factors 0) =
        levelMk H 7 (F.factors 0)
    simp only [map_mul, map_inv]
    group
  · apply Prod.ext
    · apply Subtype.ext
      change levelMk H 7 (E.factors 1) *
        levelMk H 7 ((E.factors 1)⁻¹ * F.factors 1) =
          levelMk H 7 (F.factors 1)
      simp only [map_mul, map_inv]
      group
    · apply Prod.ext
      · apply Subtype.ext
        change levelMk H 7 (E.factors 2) *
          levelMk H 7 ((E.factors 2)⁻¹ * F.factors 2) =
            levelMk H 7 (F.factors 2)
        simp only [map_mul, map_inv]
        group
      · apply Subtype.ext
        change levelMk H 7 (E.factors 3) *
          levelMk H 7 ((E.factors 3)⁻¹ * F.factors 3) =
            levelMk H 7 (F.factors 3)
        simp only [map_mul, map_inv]
        group

private theorem oneHandleDirectLevelShift_mul
    (m : Fin (coreRank 1) → H)
    (A R : OneHandleDirectLevelCorrection 6) :
    oneHandleDirectLevelShift m (A * R) =
      oneHandleDirectLevelShift m A * oneHandleDirectLevelShift m R := by
  have h := congrArg Subtype.val
    (map_mul (oneHandleDirectLevelShiftHom m 6 (by omega)) A R)
  simpa only [oneHandleDirectLevelShiftHom_apply, Subgroup.coe_mul] using h

theorem relativeLift_levelShift_difference
    (E F : OneHandleC7RelativeLift)
    (hcompact : E.compactFactors = F.compactFactors) :
    oneHandleDirectLevelShift oneHandleW6Mark (relativeLiftToDirect F) =
      oneHandleDirectLevelShift oneHandleW6Mark (relativeLiftToDirect E) *
        oneHandleDirectLevelShift (dmGen 2 1)
          (relativeCoreToDirect (relativeLiftDifference E F hcompact)) := by
  rw [← relativeLiftToDirect_mul_difference E F hcompact,
    oneHandleDirectLevelShift_mul,
    oneHandleDirectLevelShift_W6_eq_standard]

theorem residual_eq_mul_standardShift
    (E F : OneHandleC7RelativeLift)
    (hcompact : E.compactFactors = F.compactFactors) :
    F.residual = E.residual *
      oneHandleDirectLevelShift (dmGen 2 1)
        (relativeCoreToDirect (relativeLiftDifference E F hcompact)) := by
  have h := relativeLift_levelShift_difference E F hcompact
  rw [relativeLift_levelShift E, relativeLift_levelShift F] at h
  let w : levelQuot H 7 := levelMk H 7 (mRelWord 2 oneHandleW6Mark)
  let s : levelQuot H 7 := oneHandleDirectLevelShift (dmGen 2 1)
    (relativeCoreToDirect (relativeLiftDifference E F hcompact))
  change w⁻¹ * F.residual = (w⁻¹ * E.residual) * s at h
  calc
    F.residual = w * (w⁻¹ * F.residual) := by group
    _ = w * ((w⁻¹ * E.residual) * s) := by rw [h]
    _ = E.residual * s := by group

theorem relativeTarget_eq_standardShift_inv_mul
    (E F : OneHandleC7RelativeLift)
    (hcompact : E.compactFactors = F.compactFactors) :
    oneHandleC7RelativeTarget F =
      (oneHandleStandardRelativeShiftHom
        (relativeLiftDifference E F hcompact))⁻¹ *
          oneHandleC7RelativeTarget E := by
  apply Subtype.ext
  change F.residual⁻¹ =
    ((oneHandleStandardRelativeShiftHom
      (relativeLiftDifference E F hcompact)).1)⁻¹ * E.residual⁻¹
  rw [oneHandleStandardRelativeShiftHom_apply,
    residual_eq_mul_standardShift E F hcompact]
  group

theorem relativeTarget_mem_relaxed_iff_of_compactFactors_eq
    (E F : OneHandleC7RelativeLift)
    (hcompact : E.compactFactors = F.compactFactors) :
    oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      oneHandleC7RelativeTarget F ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan := by
  let s := oneHandleStandardRelativeShiftHom
    (relativeLiftDifference E F hcompact)
  have hscoord : s ∈ oneHandleStandardRelativeCoordinateSpan := by
    rw [← oneHandleStandardRelativeShift_range_eq_coordinateSpan]
    exact ⟨relativeLiftDifference E F hcompact, rfl⟩
  have hs : s ∈ oneHandleStandardRelativeRelaxedCoordinateSpan :=
    standardRelativeCoordinateSpan_le_relaxed hscoord
  rw [relativeTarget_eq_standardShift_inv_mul E F hcompact]
  constructor
  · intro hE
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) hE
  · intro hF
    have hprod := Subgroup.mul_mem _ hs hF
    simpa [s, relativeTarget_eq_standardShift_inv_mul E F hcompact,
      mul_assoc] using hprod

theorem relativeRowEquation_iff_of_compactFactors_eq
    (E F : OneHandleC7RelativeLift)
    (hcompact : E.compactFactors = F.compactFactors) :
    OneHandleC7StandardRelativeRowEquation E ↔
      OneHandleC7StandardRelativeRowEquation F := by
  rw [← standardRelativeTarget_mem_relaxed_iff_rowEquation,
    ← standardRelativeTarget_mem_relaxed_iff_rowEquation]
  exact relativeTarget_mem_relaxed_iff_of_compactFactors_eq E F hcompact

theorem relativeRankJump_eq_of_compactFactors_eq
    (E F : OneHandleC7RelativeLift)
    (hcompact : E.compactFactors = F.compactFactors) :
    oneHandleC7StandardRelativeAugmentedTransposeRank E -
        oneHandleC7StandardRelativeCoordinateTransposeRank =
      oneHandleC7StandardRelativeAugmentedTransposeRank F -
        oneHandleC7StandardRelativeCoordinateTransposeRank := by
  rcases standardRelativeAugmentedRank_eq_or_eq_add_one E with hE | hE <;>
    rcases standardRelativeAugmentedRank_eq_or_eq_add_one F with hF | hF
  · omega
  · exfalso
    have hrowE : OneHandleC7StandardRelativeRowEquation E :=
      (standardRelativeRankJump_zero_iff_rowEquation E).mp (by omega)
    have hrowF :=
      (relativeRowEquation_iff_of_compactFactors_eq E F hcompact).mp hrowE
    exact (standardRelativeRankJump_one_iff_no_rowEquation F).mp (by omega) hrowF
  · exfalso
    have hrowF : OneHandleC7StandardRelativeRowEquation F :=
      (standardRelativeRankJump_zero_iff_rowEquation F).mp (by omega)
    have hrowE :=
      (relativeRowEquation_iff_of_compactFactors_eq E F hcompact).mpr hrowF
    exact (standardRelativeRankJump_one_iff_no_rowEquation E).mp (by omega) hrowE
  · omega

#print axioms relativeLiftDifference
#print axioms relativeLiftToDirect_mul_difference
#print axioms relativeLift_levelShift_difference
#print axioms residual_eq_mul_standardShift
#print axioms relativeTarget_eq_standardShift_inv_mul
#print axioms relativeTarget_mem_relaxed_iff_of_compactFactors_eq
#print axioms relativeRowEquation_iff_of_compactFactors_eq
#print axioms relativeRankJump_eq_of_compactFactors_eq

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeLiftIndependence
