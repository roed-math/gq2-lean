/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeLiftIndependence
import GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan

/-!
# Finite lift independence of the class-seven relative obstruction

The exact lift-independence theorem requires the four compact factors to agree.  For the
ordinary relaxed obstruction this can be weakened to equality only in the compact quotient
modulo `lambda_7`.  The four factor ratios then define ordinary relative depth-five classes;
the `C` ratio need not be character-neutral, so it is routed through the relaxed `C` row.

Their standard coordinate shifts account exactly for the change in the direct residual.
Consequently relaxed target membership, the quotient obstruction, and the literal row
equation depend only on the compact factor classes modulo `lambda_7`.  No corresponding claim
is made for the neutral-`C` refinement, which can retain finer representative information.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeFiniteLiftIndependence

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenBaseReduction
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCoordinates
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeF2
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRank
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeRankJump
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeEquation
open GQ2.Roe.Labute

private abbrev H := DM 2 1

def SameCompactLevelSeven (E F : OneHandleC7RelativeLift) : Prop :=
  ∀ i, levelMk (DM 2 0 : Type) 7 (E.compactFactors i) =
    levelMk (DM 2 0 : Type) 7 (F.compactFactors i)

private theorem factorRatio_mem_relative
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F)
    (i : Fin (coreRank 1)) :
    levelMk H 7 ((E.factors i)⁻¹ * F.factors i) ∈
      oneHandleRelativeLambdaImage 5 7 := by
  refine ⟨⟨(E.factors i)⁻¹ * F.factors i,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (E.depth i)) (F.depth i), rfl⟩, ?_⟩
  change oneHandleForgetLevelMap 7
    (levelMk H 7 ((E.factors i)⁻¹ * F.factors i)) = 1
  rw [oneHandleForgetLevelMap_levelMk,
    map_mul, map_inv, E.forget, F.forget, map_mul, map_inv,
    hlevel i, inv_mul_cancel]

def relativeFiniteDifferenceA
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    oneHandleRelativeLambdaImage 5 7 :=
  ⟨levelMk H 7 ((E.factors 0)⁻¹ * F.factors 0),
    factorRatio_mem_relative E F hlevel 0⟩

def relativeFiniteDifferenceB
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    oneHandleRelativeLambdaImage 5 7 :=
  ⟨levelMk H 7 ((E.factors 1)⁻¹ * F.factors 1),
    factorRatio_mem_relative E F hlevel 1⟩

def relativeFiniteDifferenceC
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    oneHandleRelativeLambdaImage 5 7 :=
  ⟨levelMk H 7 ((E.factors 2)⁻¹ * F.factors 2),
    factorRatio_mem_relative E F hlevel 2⟩

def relativeFiniteDifferenceD
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    oneHandleRelativeLambdaImage 5 7 :=
  ⟨levelMk H 7 ((E.factors 3)⁻¹ * F.factors 3),
    factorRatio_mem_relative E F hlevel 3⟩

def directFiniteLiftDifference (E F : OneHandleC7RelativeLift) :
    OneHandleDirectLevelCorrection 6 :=
  (relativeLiftToDirect E)⁻¹ * relativeLiftToDirect F

private theorem directFiniteLiftDifference_fst
    (E F : OneHandleC7RelativeLift) :
    (directFiniteLiftDifference E F).1.1 =
      levelMk H 7 ((E.factors 0)⁻¹ * F.factors 0) := by
  simp [directFiniteLiftDifference, relativeLiftToDirect, map_mul, map_inv]

private theorem directFiniteLiftDifference_snd_fst
    (E F : OneHandleC7RelativeLift) :
    (directFiniteLiftDifference E F).2.1.1 =
      levelMk H 7 ((E.factors 1)⁻¹ * F.factors 1) := by
  simp [directFiniteLiftDifference, relativeLiftToDirect, map_mul, map_inv]

private theorem directFiniteLiftDifference_snd_snd_fst
    (E F : OneHandleC7RelativeLift) :
    (directFiniteLiftDifference E F).2.2.1.1 =
      levelMk H 7 ((E.factors 2)⁻¹ * F.factors 2) := by
  simp [directFiniteLiftDifference, relativeLiftToDirect, map_mul, map_inv]

private theorem directFiniteLiftDifference_snd_snd_snd
    (E F : OneHandleC7RelativeLift) :
    (directFiniteLiftDifference E F).2.2.2.1 =
      levelMk H 7 ((E.factors 3)⁻¹ * F.factors 3) := by
  simp [directFiniteLiftDifference, relativeLiftToDirect, map_mul, map_inv]

private theorem directLevelShift_mul
    (m : Fin (coreRank 1) → H) (A R : OneHandleDirectLevelCorrection 6) :
    oneHandleDirectLevelShift m (A * R) =
      oneHandleDirectLevelShift m A * oneHandleDirectLevelShift m R := by
  have h := congrArg Subtype.val
    (map_mul (oneHandleDirectLevelShiftHom m 6 (by omega)) A R)
  simpa only [oneHandleDirectLevelShiftHom_apply, Subgroup.coe_mul] using h

private theorem directLevelShift_inv
    (m : Fin (coreRank 1) → H) (A : OneHandleDirectLevelCorrection 6) :
    oneHandleDirectLevelShift m A⁻¹ =
      (oneHandleDirectLevelShift m A)⁻¹ := by
  have h := congrArg Subtype.val
    (map_inv (oneHandleDirectLevelShiftHom m 6 (by omega)) A)
  simpa only [oneHandleDirectLevelShiftHom_apply, Subgroup.coe_inv] using h

theorem directFiniteLiftDifference_shift
    (E F : OneHandleC7RelativeLift) :
    oneHandleDirectLevelShift oneHandleW6Mark (directFiniteLiftDifference E F) =
      E.residual⁻¹ * F.residual := by
  rw [directFiniteLiftDifference, directLevelShift_mul,
    directLevelShift_inv, relativeLift_levelShift E,
    relativeLift_levelShift F]
  group

private theorem directLevelShift_W6_eq_standard
    (D : OneHandleDirectLevelCorrection 6) :
    oneHandleDirectLevelShift oneHandleW6Mark D =
      oneHandleDirectLevelShift (dmGen 2 1) D := by
  rw [oneHandleDirectLevelShift, oneHandleDirectLevelShift]
  have hc := (oneHandleDirectLevelToRaw D).depth
  rw [evenRawStageShift_m (G := H) (by omega) (by omega) 1 6 (by omega)
      (fun i ↦ levelMk H 7 (oneHandleW6Mark i))
      (oneHandleDirectLevelCorrectionMark D) hc,
    evenRawStageShift_m (G := H) (by omega) (by omega) 1 6 (by omega)
      (fun i ↦ levelMk H 7 (dmGen 2 1 i))
      (oneHandleDirectLevelCorrectionMark D) hc]
  exact (evenRawDbarWord_congr_base
    oneHandleW6Mark_level_congr_standard hc).symm

private theorem standardShift_eq_coordinateProduct
    (D : OneHandleDirectLevelCorrection 6) :
    oneHandleDirectLevelShift (dmGen 2 1) D =
      (oneHandleDirectShiftA (dmGen 2 1) 6 (by omega) D.1).1 *
        (oneHandleDirectShiftB (dmGen 2 1) 6 (by omega) D.2.1).1 *
          (oneHandleDirectShiftC (dmGen 2 1) 6 (by omega) D.2.2.1).1 *
            (oneHandleDirectShiftD (dmGen 2 1) 6 (by omega) D.2.2.2).1 := by
  calc
    oneHandleDirectLevelShift (dmGen 2 1) D =
        oneHandleDirectLevelShift (dmGen 2 1)
          (oneHandleDirectCoordA 6 D.1 *
            oneHandleDirectCoordB 6 D.2.1 *
              oneHandleDirectCoordC 6 D.2.2.1 *
                oneHandleDirectCoordD 6 D.2.2.2) :=
      congrArg (oneHandleDirectLevelShift (dmGen 2 1))
        (oneHandleDirectLevelCorrection_eq_coords D)
    _ = _ := by
      rw [directLevelShift_mul, directLevelShift_mul, directLevelShift_mul]
      rw [show oneHandleDirectLevelShift (dmGen 2 1)
              (oneHandleDirectCoordA 6 D.1) =
            (oneHandleDirectShiftA (dmGen 2 1) 6 (by omega) D.1).1 by
            simpa [oneHandleDirectShiftA] using
              (oneHandleDirectLevelShiftHom_apply (dmGen 2 1) 6
                (by omega) (oneHandleDirectCoordA 6 D.1)).symm,
        show oneHandleDirectLevelShift (dmGen 2 1)
              (oneHandleDirectCoordB 6 D.2.1) =
            (oneHandleDirectShiftB (dmGen 2 1) 6 (by omega) D.2.1).1 by
            simpa [oneHandleDirectShiftB] using
              (oneHandleDirectLevelShiftHom_apply (dmGen 2 1) 6
                (by omega) (oneHandleDirectCoordB 6 D.2.1)).symm,
        show oneHandleDirectLevelShift (dmGen 2 1)
              (oneHandleDirectCoordC 6 D.2.2.1) =
            (oneHandleDirectShiftC (dmGen 2 1) 6 (by omega) D.2.2.1).1 by
            simpa [oneHandleDirectShiftC] using
              (oneHandleDirectLevelShiftHom_apply (dmGen 2 1) 6
                (by omega) (oneHandleDirectCoordC 6 D.2.2.1)).symm,
        show oneHandleDirectLevelShift (dmGen 2 1)
              (oneHandleDirectCoordD 6 D.2.2.2) =
            (oneHandleDirectShiftD (dmGen 2 1) 6 (by omega) D.2.2.2).1 by
            simpa [oneHandleDirectShiftD] using
              (oneHandleDirectLevelShiftHom_apply (dmGen 2 1) 6
                (by omega) (oneHandleDirectCoordD 6 D.2.2.2)).symm]

def relativeFiniteLiftShift
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    oneHandleRelativeZLayer 6 :=
  oneHandleStandardRelativeShiftA (relativeFiniteDifferenceA E F hlevel) *
    oneHandleStandardRelativeShiftB (relativeFiniteDifferenceB E F hlevel) *
      oneHandleStandardRelativeShiftCRelaxed
        (relativeFiniteDifferenceC E F hlevel) *
        oneHandleStandardRelativeShiftD (relativeFiniteDifferenceD E F hlevel)

theorem directFiniteLiftDifference_shift_eq_relativeRows
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    oneHandleDirectLevelShift oneHandleW6Mark (directFiniteLiftDifference E F) =
      (oneHandleStandardRelativeShiftA
        (relativeFiniteDifferenceA E F hlevel)).1 *
        (oneHandleStandardRelativeShiftB
          (relativeFiniteDifferenceB E F hlevel)).1 *
          (oneHandleStandardRelativeShiftCRelaxed
            (relativeFiniteDifferenceC E F hlevel)).1 *
            (oneHandleStandardRelativeShiftD
              (relativeFiniteDifferenceD E F hlevel)).1 := by
  let D := directFiniteLiftDifference E F
  have hA :
      (oneHandleDirectShiftA (dmGen 2 1) 6 (by omega) D.1).1 =
        (oneHandleStandardRelativeShiftA
          (relativeFiniteDifferenceA E F hlevel)).1 := by
    rw [oneHandleDirectShiftA_apply,
      oneHandleStandardRelativeShiftA_apply,
      directFiniteLiftDifference_fst]
    rfl
  have hB :
      (oneHandleDirectShiftB (dmGen 2 1) 6 (by omega) D.2.1).1 =
        (oneHandleStandardRelativeShiftB
          (relativeFiniteDifferenceB E F hlevel)).1 := by
    rw [oneHandleDirectShiftB_apply,
      oneHandleStandardRelativeShiftB_apply,
      directFiniteLiftDifference_snd_fst]
    rfl
  have hC :
      (oneHandleDirectShiftC (dmGen 2 1) 6 (by omega) D.2.2.1).1 =
        (oneHandleStandardRelativeShiftCRelaxed
          (relativeFiniteDifferenceC E F hlevel)).1 := by
    rw [oneHandleDirectShiftC_apply,
      oneHandleStandardRelativeShiftCRelaxed_apply,
      directFiniteLiftDifference_snd_snd_fst]
    rfl
  have hD :
      (oneHandleDirectShiftD (dmGen 2 1) 6 (by omega) D.2.2.2).1 =
        (oneHandleStandardRelativeShiftD
          (relativeFiniteDifferenceD E F hlevel)).1 := by
    rw [oneHandleDirectShiftD_apply,
      oneHandleStandardRelativeShiftD_apply,
      directFiniteLiftDifference_snd_snd_snd]
    rfl
  rw [directLevelShift_W6_eq_standard,
    standardShift_eq_coordinateProduct, hA, hB, hC, hD]

theorem directFiniteLiftDifference_shift_mem_relaxed
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    relativeFiniteLiftShift E F hlevel ∈
      oneHandleStandardRelativeRelaxedCoordinateSpan := by
  rw [oneHandleStandardRelativeRelaxedCoordinateSpan_eq_rows]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact (show oneHandleStandardRelativeShiftA.range ≤ _ from
          le_trans le_sup_left le_sup_left)
          ⟨relativeFiniteDifferenceA E F hlevel, rfl⟩
      · exact (show oneHandleStandardRelativeShiftB.range ≤ _ from
          le_trans le_sup_right le_sup_left)
          ⟨relativeFiniteDifferenceB E F hlevel, rfl⟩
    · exact (show oneHandleStandardRelativeShiftCRelaxed.range ≤ _ from
        le_trans le_sup_left le_sup_right)
        ⟨relativeFiniteDifferenceC E F hlevel, rfl⟩
  · exact (show oneHandleStandardRelativeShiftD.range ≤ _ from
      le_trans le_sup_right le_sup_right)
      ⟨relativeFiniteDifferenceD E F hlevel, rfl⟩

theorem relativeTarget_eq_finiteShift_inv_mul
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    oneHandleC7RelativeTarget F =
      (relativeFiniteLiftShift E F hlevel)⁻¹ *
        oneHandleC7RelativeTarget E := by
  apply Subtype.ext
  change F.residual⁻¹ = (relativeFiniteLiftShift E F hlevel).1⁻¹ * E.residual⁻¹
  rw [show (relativeFiniteLiftShift E F hlevel).1 =
      oneHandleDirectLevelShift oneHandleW6Mark (directFiniteLiftDifference E F) by
        symm
        exact directFiniteLiftDifference_shift_eq_relativeRows E F hlevel,
    directFiniteLiftDifference_shift]
  group

theorem relativeTarget_mem_relaxed_iff_of_sameCompactLevelSeven
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    oneHandleC7RelativeTarget E ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan ↔
      oneHandleC7RelativeTarget F ∈
        oneHandleStandardRelativeRelaxedCoordinateSpan := by
  let s := relativeFiniteLiftShift E F hlevel
  have hs : s ∈ oneHandleStandardRelativeRelaxedCoordinateSpan :=
    directFiniteLiftDifference_shift_mem_relaxed E F hlevel
  rw [relativeTarget_eq_finiteShift_inv_mul E F hlevel]
  constructor
  · intro hE
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) hE
  · intro hF
    have hprod := Subgroup.mul_mem _ hs hF
    simpa [s, relativeTarget_eq_finiteShift_inv_mul E F hlevel,
      mul_assoc] using hprod

theorem relativeObstruction_eq_of_sameCompactLevelSeven
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    oneHandleC7StandardRelativeObstruction E =
      oneHandleC7StandardRelativeObstruction F := by
  change QuotientGroup.mk' oneHandleStandardRelativeRelaxedCoordinateSpan
      (oneHandleC7RelativeTarget E) =
    QuotientGroup.mk' oneHandleStandardRelativeRelaxedCoordinateSpan
      (oneHandleC7RelativeTarget F)
  rw [relativeTarget_eq_finiteShift_inv_mul E F hlevel,
    map_mul, map_inv]
  have hs : QuotientGroup.mk' oneHandleStandardRelativeRelaxedCoordinateSpan
      (relativeFiniteLiftShift E F hlevel) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr
      (directFiniteLiftDifference_shift_mem_relaxed E F hlevel)
  rw [hs, inv_one, one_mul]

theorem relativeRowEquation_iff_of_sameCompactLevelSeven
    (E F : OneHandleC7RelativeLift) (hlevel : SameCompactLevelSeven E F) :
    OneHandleC7StandardRelativeRowEquation E ↔
      OneHandleC7StandardRelativeRowEquation F := by
  rw [← standardRelativeTarget_mem_relaxed_iff_rowEquation,
    ← standardRelativeTarget_mem_relaxed_iff_rowEquation]
  exact relativeTarget_mem_relaxed_iff_of_sameCompactLevelSeven E F hlevel

#print axioms SameCompactLevelSeven
#print axioms relativeFiniteDifferenceA
#print axioms relativeFiniteDifferenceB
#print axioms relativeFiniteDifferenceC
#print axioms relativeFiniteDifferenceD
#print axioms directFiniteLiftDifference_shift_eq_relativeRows
#print axioms directFiniteLiftDifference_shift_mem_relaxed
#print axioms relativeTarget_mem_relaxed_iff_of_sameCompactLevelSeven
#print axioms relativeObstruction_eq_of_sameCompactLevelSeven
#print axioms relativeRowEquation_iff_of_sameCompactLevelSeven

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeFiniteLiftIndependence
