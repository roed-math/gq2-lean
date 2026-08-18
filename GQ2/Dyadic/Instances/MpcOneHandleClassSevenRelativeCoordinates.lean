/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenBaseReduction
import GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan

/-!
# Four coordinate rows of the standard class-seven relative shift

After base reduction, the finite source splits into its `A`, `B`, `C`, and `D` relative
coordinates.  This module proves that the standard relative range is exactly the join of the
four coordinate ranges and records their literal values.  The `A` coordinate contributes the
diagonal square and its two adjacent brackets; the other coordinates contribute the brackets
against `A`, `D`, and `C` respectively.

Thus the remaining class-seven statement is target membership in one explicit finite relative
four-row span.  No surjectivity or target membership is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCoordinates

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedFiniteSpan
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenBaseReduction
open GQ2.Roe.Labute

private abbrev H := DM 2 1

noncomputable def oneHandleRelativeCoordA :
    oneHandleRelativeLambdaImage 5 7 →*
      OneHandleBalancedCoreLevelCorrection 6 where
  toFun x := ⟨x, 1, 1, 1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def oneHandleRelativeCoordB :
    oneHandleRelativeLambdaImage 5 7 →*
      OneHandleBalancedCoreLevelCorrection 6 where
  toFun x := ⟨1, x, 1, 1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def oneHandleRelativeCoordC :
    oneHandleNeutralRelativeLambdaImage 5 7 →*
      OneHandleBalancedCoreLevelCorrection 6 where
  toFun x := ⟨1, 1, x, 1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def oneHandleRelativeCoordD :
    oneHandleRelativeLambdaImage 5 7 →*
      OneHandleBalancedCoreLevelCorrection 6 where
  toFun x := ⟨1, 1, 1, x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem oneHandleRelativeCorrection_eq_coords
    (F : OneHandleBalancedCoreLevelCorrection 6) :
    F = oneHandleRelativeCoordA F.corrA *
        oneHandleRelativeCoordB F.corrB *
        oneHandleRelativeCoordC F.corrC *
        oneHandleRelativeCoordD F.corrD := by
  cases F
  apply OneHandleBalancedCoreLevelCorrection.ext <;>
    simp [oneHandleRelativeCoordA, oneHandleRelativeCoordB,
      oneHandleRelativeCoordC, oneHandleRelativeCoordD]

noncomputable def oneHandleStandardRelativeShiftA :
    oneHandleRelativeLambdaImage 5 7 →* oneHandleRelativeZLayer 6 :=
  oneHandleStandardRelativeShiftHom.comp oneHandleRelativeCoordA

noncomputable def oneHandleStandardRelativeShiftB :
    oneHandleRelativeLambdaImage 5 7 →* oneHandleRelativeZLayer 6 :=
  oneHandleStandardRelativeShiftHom.comp oneHandleRelativeCoordB

noncomputable def oneHandleStandardRelativeShiftC :
    oneHandleNeutralRelativeLambdaImage 5 7 →* oneHandleRelativeZLayer 6 :=
  oneHandleStandardRelativeShiftHom.comp oneHandleRelativeCoordC

noncomputable def oneHandleStandardRelativeShiftD :
    oneHandleRelativeLambdaImage 5 7 →* oneHandleRelativeZLayer 6 :=
  oneHandleStandardRelativeShiftHom.comp oneHandleRelativeCoordD

def oneHandleStandardRelativeCoordinateSpan :
    Subgroup (oneHandleRelativeZLayer 6) :=
  ((oneHandleStandardRelativeShiftA.range ⊔
    oneHandleStandardRelativeShiftB.range) ⊔
  (oneHandleStandardRelativeShiftC.range ⊔
    oneHandleStandardRelativeShiftD.range))

theorem oneHandleStandardRelativeShift_range_eq_coordinateSpan :
    oneHandleStandardRelativeShiftHom.range =
      oneHandleStandardRelativeCoordinateSpan := by
  apply le_antisymm
  · rintro y ⟨F, rfl⟩
    rw [oneHandleRelativeCorrection_eq_coords F]
    simp only [map_mul]
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · apply Subgroup.mul_mem
        · exact (show oneHandleStandardRelativeShiftA.range ≤
              oneHandleStandardRelativeCoordinateSpan from
            le_trans le_sup_left le_sup_left) ⟨F.corrA, rfl⟩
        · exact (show oneHandleStandardRelativeShiftB.range ≤
              oneHandleStandardRelativeCoordinateSpan from
            le_trans le_sup_right le_sup_left) ⟨F.corrB, rfl⟩
      · exact (show oneHandleStandardRelativeShiftC.range ≤
            oneHandleStandardRelativeCoordinateSpan from
          le_trans le_sup_left le_sup_right) ⟨F.corrC, rfl⟩
    · exact (show oneHandleStandardRelativeShiftD.range ≤
          oneHandleStandardRelativeCoordinateSpan from
        le_trans le_sup_right le_sup_right) ⟨F.corrD, rfl⟩
  · apply sup_le
    · apply sup_le
      · rintro y ⟨x, rfl⟩
        exact ⟨oneHandleRelativeCoordA x, rfl⟩
      · rintro y ⟨x, rfl⟩
        exact ⟨oneHandleRelativeCoordB x, rfl⟩
    · apply sup_le
      · rintro y ⟨x, rfl⟩
        exact ⟨oneHandleRelativeCoordC x, rfl⟩
      · rintro y ⟨x, rfl⟩
        exact ⟨oneHandleRelativeCoordD x, rfl⟩

private theorem relativeCoreToDirect_coordA
    (x : oneHandleRelativeLambdaImage 5 7) :
    relativeCoreToDirect (oneHandleRelativeCoordA x) =
      oneHandleDirectCoordA 6
        (relativeCoreToDirect (oneHandleRelativeCoordA x)).1 := rfl

private theorem relativeCoreToDirect_coordB
    (x : oneHandleRelativeLambdaImage 5 7) :
    relativeCoreToDirect (oneHandleRelativeCoordB x) =
      oneHandleDirectCoordB 6
        (relativeCoreToDirect (oneHandleRelativeCoordB x)).2.1 := rfl

private theorem relativeCoreToDirect_coordC
    (x : oneHandleNeutralRelativeLambdaImage 5 7) :
    relativeCoreToDirect (oneHandleRelativeCoordC x) =
      oneHandleDirectCoordC 6
        (relativeCoreToDirect (oneHandleRelativeCoordC x)).2.2.1 := rfl

private theorem relativeCoreToDirect_coordD
    (x : oneHandleRelativeLambdaImage 5 7) :
    relativeCoreToDirect (oneHandleRelativeCoordD x) =
      oneHandleDirectCoordD 6
        (relativeCoreToDirect (oneHandleRelativeCoordD x)).2.2.2 := rfl

@[simp] theorem oneHandleStandardRelativeShiftA_apply
    (x : oneHandleRelativeLambdaImage 5 7) :
    (oneHandleStandardRelativeShiftA x).1 =
      x.1 ^ 2 * commP x.1 (levelMk H 7 (dmA 2 1)) *
        commP x.1 (levelMk H 7 (dmB 2 1)) := by
  rw [show (oneHandleStandardRelativeShiftA x).1 =
      (oneHandleStandardRelativeShiftHom (oneHandleRelativeCoordA x)).1 from rfl,
    oneHandleStandardRelativeShiftHom_apply]
  change oneHandleDirectLevelShift (dmGen 2 1)
    (relativeCoreToDirect (oneHandleRelativeCoordA x)) = _
  rw [relativeCoreToDirect_coordA]
  rw [← oneHandleDirectLevelShiftHom_apply]
  simpa [oneHandleDirectShiftA, relativeCoreToDirect,
    oneHandleRelativeCoordA, dmA, dmB] using
      oneHandleDirectShiftA_apply (dmGen 2 1) 6 (by omega)
        (relativeCoreToDirect (oneHandleRelativeCoordA x)).1

@[simp] theorem oneHandleStandardRelativeShiftB_apply
    (x : oneHandleRelativeLambdaImage 5 7) :
    (oneHandleStandardRelativeShiftB x).1 =
      commP x.1 (levelMk H 7 (dmA 2 1)) := by
  rw [show (oneHandleStandardRelativeShiftB x).1 =
      (oneHandleStandardRelativeShiftHom (oneHandleRelativeCoordB x)).1 from rfl,
    oneHandleStandardRelativeShiftHom_apply]
  change oneHandleDirectLevelShift (dmGen 2 1)
    (relativeCoreToDirect (oneHandleRelativeCoordB x)) = _
  rw [relativeCoreToDirect_coordB]
  rw [← oneHandleDirectLevelShiftHom_apply]
  simpa [oneHandleDirectShiftB, relativeCoreToDirect,
    oneHandleRelativeCoordB, dmA] using
      oneHandleDirectShiftB_apply (dmGen 2 1) 6 (by omega)
        (relativeCoreToDirect (oneHandleRelativeCoordB x)).2.1

@[simp] theorem oneHandleStandardRelativeShiftC_apply
    (x : oneHandleNeutralRelativeLambdaImage 5 7) :
    (oneHandleStandardRelativeShiftC x).1 =
      commP x.1 (levelMk H 7 (dmD 2 1)) := by
  rw [show (oneHandleStandardRelativeShiftC x).1 =
      (oneHandleStandardRelativeShiftHom (oneHandleRelativeCoordC x)).1 from rfl,
    oneHandleStandardRelativeShiftHom_apply]
  change oneHandleDirectLevelShift (dmGen 2 1)
    (relativeCoreToDirect (oneHandleRelativeCoordC x)) = _
  rw [relativeCoreToDirect_coordC]
  rw [← oneHandleDirectLevelShiftHom_apply]
  simpa [oneHandleDirectShiftC, relativeCoreToDirect,
    oneHandleRelativeCoordC, dmD] using
      oneHandleDirectShiftC_apply (dmGen 2 1) 6 (by omega)
        (relativeCoreToDirect (oneHandleRelativeCoordC x)).2.2.1

@[simp] theorem oneHandleStandardRelativeShiftD_apply
    (x : oneHandleRelativeLambdaImage 5 7) :
    (oneHandleStandardRelativeShiftD x).1 =
      commP x.1 (levelMk H 7 (dmC 2 1)) := by
  rw [show (oneHandleStandardRelativeShiftD x).1 =
      (oneHandleStandardRelativeShiftHom (oneHandleRelativeCoordD x)).1 from rfl,
    oneHandleStandardRelativeShiftHom_apply]
  change oneHandleDirectLevelShift (dmGen 2 1)
    (relativeCoreToDirect (oneHandleRelativeCoordD x)) = _
  rw [relativeCoreToDirect_coordD]
  rw [← oneHandleDirectLevelShiftHom_apply]
  simpa [oneHandleDirectShiftD, relativeCoreToDirect,
    oneHandleRelativeCoordD, dmC] using
      oneHandleDirectShiftD_apply (dmGen 2 1) 6 (by omega)
        (relativeCoreToDirect (oneHandleRelativeCoordD x)).2.2.2

theorem relativeCorrectable_iff_standard_target_mem_coordinateSpan
    (E : OneHandleC7RelativeLift) :
    OneHandleC7RelativeCorrectable E ↔
      oneHandleC7RelativeTarget E ∈ oneHandleStandardRelativeCoordinateSpan := by
  rw [← oneHandleStandardRelativeShift_range_eq_coordinateSpan]
  exact relativeCorrectable_iff_standard_target_mem_range E

#print axioms oneHandleRelativeCorrection_eq_coords
#print axioms oneHandleStandardRelativeShiftA
#print axioms oneHandleStandardRelativeShiftB
#print axioms oneHandleStandardRelativeShiftC
#print axioms oneHandleStandardRelativeShiftD
#print axioms oneHandleStandardRelativeCoordinateSpan
#print axioms oneHandleStandardRelativeShift_range_eq_coordinateSpan
#print axioms oneHandleStandardRelativeShiftA_apply
#print axioms oneHandleStandardRelativeShiftB_apply
#print axioms oneHandleStandardRelativeShiftC_apply
#print axioms oneHandleStandardRelativeShiftD_apply
#print axioms relativeCorrectable_iff_standard_target_mem_coordinateSpan

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCoordinates
