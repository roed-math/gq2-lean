/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactObstructionCoset

/-!
# Realizing every compact connecting value

Every finite direct correction has exact depth-five representatives satisfying the direct
character and neutral-row conditions.  Starting from a legal relative lift, multiply its
finite correction tuple by a compact-kernel correction and choose such representatives.
The vanishing compact cost is exactly what makes the new compact relator vanish at level seven.

This constructs another legal relative lift whose finite difference is the prescribed kernel
correction.  Therefore the realization predicate from W281 always holds, and the finite packet
obstruction set is exactly the coset of the compact connecting image through any reference
obstruction.  No vanishing claim for that image is made.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSixCompactLift
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactSupply
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeFiniteLiftIndependence
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenFinitePacket
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingCriterion
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactObstructionCoset
open GQ2.Roe.Labute

private abbrev H := DM 2 1

structure OneHandleDirectLevelRepresentatives
    (T : OneHandleDirectLevelCorrection 6) where
  factors : Fin (coreRank 1) → H
  depth : ∀ i, factors i ∈ twoCentralSeries H 5
  handleU : ∀ j : Fin 1, factors (handleIdxU j) = 1
  handleV : ∀ j : Fin 1, factors (handleIdxV j) = 1
  chi : ∀ i, chiM 2 1 (factors i) = 1
  row : ∀ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
    toAdd (f (factors 2)) = 0
  level : (fun i ↦ levelMk H 7 (factors i)) =
    oneHandleDirectLevelCorrectionMark T

theorem nonempty_oneHandleDirectLevelRepresentatives
    (T : OneHandleDirectLevelCorrection 6) :
    Nonempty (OneHandleDirectLevelRepresentatives T) := by
  obtain ⟨a, ha, hachi, haQ⟩ :=
    (mem_oneHandleDirectLambdaImage_iff_exists_exact T.1.1).mp T.1.2
  obtain ⟨b, hb, hbchi, hbQ⟩ :=
    (mem_oneHandleDirectLambdaImage_iff_exists_exact T.2.1.1).mp T.2.1.2
  obtain ⟨c, hc, hcchi, hcrow, hcQ⟩ :=
    (mem_oneHandleDirectNeutralLambdaImage_iff_exists_exact T.2.2.1.1).mp
      T.2.2.1.2
  obtain ⟨d, hd, hdchi, hdQ⟩ :=
    (mem_oneHandleDirectLambdaImage_iff_exists_exact T.2.2.2.1).mp
      T.2.2.2.2
  let e : Fin (coreRank 1) → H :=
    fullMark a b c d (fun _ ↦ 1) (fun _ ↦ 1)
  refine ⟨⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
        simp [e, mHandleIdx_coordU, mHandleIdx_coordV]
  · intro j
    simp [e]
  · intro j
    simp [e]
  · intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · exact hachi
    · exact hbchi
    · exact hcchi
    · exact hdchi
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
        simp [e, mHandleIdx_coordU, mHandleIdx_coordV]
  · simpa [e] using hcrow
  · funext i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · exact haQ
    · exact hbQ
    · exact hcQ
    · exact hdQ
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
        simp [e, oneHandleDirectLevelCorrectionMark,
          mHandleIdx_coordU, mHandleIdx_coordV]

noncomputable def oneHandleDirectLevelRepresentatives
    (T : OneHandleDirectLevelCorrection 6) :
    OneHandleDirectLevelRepresentatives T :=
  Classical.choice (nonempty_oneHandleDirectLevelRepresentatives T)

private theorem directLevelShift_mul
    (A B : OneHandleDirectLevelCorrection 6) :
    oneHandleDirectLevelShift oneHandleW6Mark (A * B) =
      oneHandleDirectLevelShift oneHandleW6Mark A *
        oneHandleDirectLevelShift oneHandleW6Mark B := by
  have h := congrArg Subtype.val
    (map_mul (oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)) A B)
  simpa only [oneHandleDirectLevelShiftHom_apply, Subgroup.coe_mul] using h

theorem oneHandleCompactCostHom_apply
    (D : OneHandleDirectLevelCorrection 6) :
    oneHandleCompactCostHom D =
      dmForgetHandlesLevelSeven
        (oneHandleDirectLevelShift oneHandleW6Mark D) := by
  rw [oneHandleCompactCostHom, MonoidHom.comp_apply,
    MonoidHom.comp_apply]
  apply congrArg dmForgetHandlesLevelSeven
  change (oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega) D).1 =
    oneHandleDirectLevelShift oneHandleW6Mark D
  exact oneHandleDirectLevelShiftHom_apply oneHandleW6Mark 6 (by omega) D

private theorem compactRelator_mem_of_kernel
    (E : OneHandleC7RelativeLift) (D : OneHandleCompactKernelCorrection)
    (R : OneHandleDirectLevelRepresentatives (relativeLiftToDirect E * D.1)) :
    mRelWord 2 (fun i ↦ compactC6Mark i *
      dmForgetHandles 2 1 (R.factors i)) ∈
        twoCentralSeries (DM 2 0 : Type) 7 := by
  let T : OneHandleDirectLevelCorrection 6 := relativeLiftToDirect E * D.1
  have hshiftRep : oneHandleDirectRelatorShift oneHandleW6Mark R.factors 6 =
      oneHandleDirectLevelShift oneHandleW6Mark T := by
    rw [oneHandleDirectRelatorShift, oneHandleDirectLevelShift]
    exact congrArg (stageShift (mStageWord 2 1 (by omega))
      (fun i ↦ levelMk H 7 (oneHandleW6Mark i))) R.level
  have hshiftMul : oneHandleDirectLevelShift oneHandleW6Mark T =
      oneHandleDirectLevelShift oneHandleW6Mark (relativeLiftToDirect E) *
        oneHandleDirectLevelShift oneHandleW6Mark D.1 := by
    exact directLevelShift_mul _ _
  have hD : oneHandleCompactCostHom D.1 = 1 :=
    MonoidHom.mem_ker.mp D.2
  have hD' : dmForgetHandlesLevelSeven
      (oneHandleDirectLevelShift oneHandleW6Mark D.1) = 1 := by
    rw [← oneHandleCompactCostHom_apply]
    exact hD
  have hE : dmForgetHandlesLevelSeven E.residual = 1 :=
    MonoidHom.mem_ker.mp E.residual_mem_ker
  have hnew : dmForgetHandlesLevelSeven
      (levelMk H 7 (mRelWord 2
        (oneHandleDirectModify oneHandleW6Mark R.factors))) = 1 := by
    have hrel := oneHandleDirectRelatorShift_eq
      oneHandleW6Mark R.factors 6
    have hlevel : levelMk H 7 (mRelWord 2
        (oneHandleDirectModify oneHandleW6Mark R.factors)) =
      levelMk H 7 (mRelWord 2 oneHandleW6Mark) *
        oneHandleDirectLevelShift oneHandleW6Mark T := by
      calc
        _ = levelMk H 7 (mRelWord 2 oneHandleW6Mark) *
            oneHandleDirectRelatorShift oneHandleW6Mark R.factors 6 := by
          rw [hrel]
          group
        _ = _ := by rw [hshiftRep]
    rw [hlevel, map_mul, hshiftMul, map_mul,
      relativeLift_levelShift E, map_mul, map_inv, hD']
    rw [hE]
    group
  apply (lim_mem_twoCentralSeries_iff_levelMk 7 _).mpr
  have hfun : (fun i ↦ compactC6Mark i *
      dmForgetHandles 2 1 (R.factors i)) =
      fun i ↦ dmForgetHandles 2 1
        (oneHandleDirectModify oneHandleW6Mark R.factors i) := by
    funext i
    rw [oneHandleDirectModify, map_mul,
      dmForgetHandles_oneHandleW6Mark]
  rw [hfun, ← map_mRelWord]
  exact hnew

noncomputable def compactKernelCorrectionLift
    (E : OneHandleC7RelativeLift) (D : OneHandleCompactKernelCorrection) :
    OneHandleC7RelativeLift := by
  let T : OneHandleDirectLevelCorrection 6 := relativeLiftToDirect E * D.1
  let R := oneHandleDirectLevelRepresentatives T
  exact {
    factors := R.factors
    compactFactors := fun i ↦ dmForgetHandles 2 1 (R.factors i)
    depth := R.depth
    handleU := R.handleU
    handleV := R.handleV
    chi := R.chi
    row := R.row
    forget := fun _ ↦ rfl
    compactRelator := compactRelator_mem_of_kernel E D R }

theorem compactKernelCorrectionLift_toDirect
    (E : OneHandleC7RelativeLift) (D : OneHandleCompactKernelCorrection) :
    relativeLiftToDirect (compactKernelCorrectionLift E D) =
      relativeLiftToDirect E * D.1 := by
  let T : OneHandleDirectLevelCorrection 6 := relativeLiftToDirect E * D.1
  let R := oneHandleDirectLevelRepresentatives T
  have hall : oneHandleDirectLevelCorrectionMark
      (relativeLiftToDirect (compactKernelCorrectionLift E D)) =
        oneHandleDirectLevelCorrectionMark T := by
    rw [relativeLiftToDirect_mark]
    simpa [compactKernelCorrectionLift, T, R] using R.level
  apply Prod.ext
  · apply Subtype.ext
    simpa [oneHandleDirectLevelCorrectionMark, T] using congrFun hall 0
  · apply Prod.ext
    · apply Subtype.ext
      simpa [oneHandleDirectLevelCorrectionMark, T] using congrFun hall 1
    · apply Prod.ext
      · apply Subtype.ext
        simpa [oneHandleDirectLevelCorrectionMark, T] using congrFun hall 2
      · apply Subtype.ext
        simpa [oneHandleDirectLevelCorrectionMark, T] using congrFun hall 3

theorem realizedCompactKernelDifference_correctionLift
    (E : OneHandleC7RelativeLift) (D : OneHandleCompactKernelCorrection) :
    (realizedCompactKernelDifference E (compactKernelCorrectionLift E D)).1 =
      D.1 := by
  change (relativeLiftToDirect E)⁻¹ *
      relativeLiftToDirect (compactKernelCorrectionLift E D) = D.1
  rw [compactKernelCorrectionLift_toDirect]
  group

theorem compactConnectingRealizedAt (E : OneHandleC7RelativeLift) :
    OneHandleCompactConnectingRealizedAt E := by
  intro D
  refine ⟨compactKernelCorrectionLift E D, ?_⟩
  congr 1
  apply Subtype.ext
  exact realizedCompactKernelDifference_correctionLift E D

theorem compactPacketObstructionValues_eq_connectingCoset
    (E : OneHandleC7RelativeLift) :
    (↑compactPacketObstructionValues :
        Set OneHandleC7StandardRelativeCokernel) =
      compactConnectingObstructionCoset E :=
  (compactPacketObstructionValues_eq_connectingCoset_iff E).mpr
    (compactConnectingRealizedAt E)

theorem ordinaryRelativeSolvable_iff_obstruction_mem_connectingValues
    (E : OneHandleC7RelativeLift) :
    OneHandleW6OrdinaryRelativeSolvable ↔
      oneHandleC7StandardRelativeObstruction E ∈ compactConnectingValues := by
  rw [← one_mem_compactPacketObstructionValues_iff]
  constructor
  · intro hone
    have hcos : 1 ∈ compactConnectingObstructionCoset E := by
      rw [← compactPacketObstructionValues_eq_connectingCoset E]
      exact hone
    obtain ⟨D, hD⟩ := hcos
    rw [mem_compactConnectingValues_iff]
    refine ⟨D, ?_⟩
    calc
      oneHandleCompactConnectingHom D =
          oneHandleCompactConnectingHom D * 1 := by group
      _ = oneHandleCompactConnectingHom D *
          ((oneHandleCompactConnectingHom D)⁻¹ *
            oneHandleC7StandardRelativeObstruction E) := by rw [← hD]
      _ = oneHandleC7StandardRelativeObstruction E := by group
  · intro hmem
    rw [mem_compactConnectingValues_iff] at hmem
    obtain ⟨D, hD⟩ := hmem
    have hcos : 1 ∈ compactConnectingObstructionCoset E := by
      refine ⟨D, ?_⟩
      rw [hD]
      group
    have hset : (1 : OneHandleC7StandardRelativeCokernel) ∈
        (↑compactPacketObstructionValues :
          Set OneHandleC7StandardRelativeCokernel) := by
      rw [compactPacketObstructionValues_eq_connectingCoset E]
      exact hcos
    exact hset

#print axioms OneHandleDirectLevelRepresentatives
#print axioms nonempty_oneHandleDirectLevelRepresentatives
#print axioms oneHandleDirectLevelRepresentatives
#print axioms compactKernelCorrectionLift
#print axioms compactKernelCorrectionLift_toDirect
#print axioms realizedCompactKernelDifference_correctionLift
#print axioms compactConnectingRealizedAt
#print axioms compactPacketObstructionValues_eq_connectingCoset
#print axioms ordinaryRelativeSolvable_iff_obstruction_mem_connectingValues

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization
