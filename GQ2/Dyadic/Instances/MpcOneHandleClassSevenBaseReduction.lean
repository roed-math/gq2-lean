/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection

/-!
# Base independence of the one-handle class-seven relative shift

The explicit W6 marking differs coordinatewise from the standard six-letter marking by a
class in `lambda_2`.  A depth-five correction only brackets this base class in degree seven,
where it vanishes.  Consequently the relative class-seven shift homomorphism is exactly the
standard-base shift homomorphism, not merely isomorphic to it or equal after taking ranks.

This removes all accumulated W4/W5/W6 base expressions from the remaining finite range
problem.  The class-seven target is correctable precisely when it belongs to the range of the
four-coordinate relative shift computed at the standard `D_M(2,1)` generators.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenBaseReduction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleClassFourSeed
open GQ2.Dyadic.Instances.MpcOneHandleClassFiveSeed
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleClassSixCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Roe.Labute
open scoped commutatorElement

private abbrev H := DM 2 1

private theorem commP_congr_base {v g g' : levelQuot H 7}
    (hv : v ∈ lambdaImage H 5 7) (hg : g⁻¹ * g' ∈ lambdaImage H 2 7) :
    commP v g = commP v g' := by
  have hg' : g' = g * (g⁻¹ * g') := by group
  have h1 : commP v (g⁻¹ * g') = 1 := by
    have h := commP_mem_lambdaImage_add hv hg
    rw [show 5 + 2 = 7 by omega, lambdaImage_self] at h
    simpa using h
  have h2 : commP v g ∈ zLayer H 6 := by
    have hgt : g ∈ lambdaImage H 1 7 := by
      rw [lambdaImage_one_eq_top]
      trivial
    have h := commP_mem_lambdaImage_add hv hgt
    simpa using h
  have key : commP v (g * (g⁻¹ * g')) =
      commP v (g⁻¹ * g') * ((g⁻¹ * g')⁻¹ * commP v g * (g⁻¹ * g')) := by
    simp only [commP]
    group
  have hcen := Subgroup.mem_center_iff.mp (zLayer_le_center H 6 h2) (g⁻¹ * g')
  rw [hg', key, h1, one_mul, mul_assoc, ← hcen, ← mul_assoc,
    inv_mul_cancel, one_mul]

theorem evenRawDbarWord_congr_base
    {base base' c : Fin (coreRank 1) → levelQuot H 7}
    (hb : ∀ i, (base i)⁻¹ * base' i ∈ lambdaImage H 2 7)
    (hc : ∀ i, c i ∈ lambdaImage H 5 7) :
    evenRawDbarWord base c = evenRawDbarWord base' c := by
  have key : ∀ j i : Fin (coreRank 1),
      commP (c j) (base i) = commP (c j) (base' i) :=
    fun j i ↦ commP_congr_base (hc j) (hb i)
  simp only [evenRawDbarWord, evenRawCoreDbarWord,
    evenRawHandleDbarWord, key]

private theorem w4_congr_standard (i : Fin (coreRank 1)) :
    (dmGen 2 1 i)⁻¹ * oneHandleW4Mark i ∈ twoCentralSeries H 2 := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp only [oneHandleW4Mark, standardHandleMark_zero, oneHandleW4]
    change (dmA 2 1)⁻¹ *
      (dmA 2 1 * (dmB 2 1 ^ 4)⁻¹ *
        commP (dmD 2 1) (dmB 2 1)) ∈ twoCentralSeries H 2
    have hB4 : dmB 2 1 ^ 4 ∈ twoCentralSeries H 2 := by
      apply twoCentralSeries_antitone (G := H) (show 2 ≤ 3 by omega)
      simpa [oneHandleW5Ut] using oneHandleW5Ut_mem_three
    have hW : commP (dmD 2 1) (dmB 2 1) ∈ twoCentralSeries H 2 := by
      have heq : commP (dmD 2 1) (dmB 2 1) =
          ⁅(dmD 2 1)⁻¹, (dmB 2 1)⁻¹⁆ := by
        simp only [commP, commutatorElement_def, inv_inv]
      rw [heq]
      exact commutator_mem_twoCentralSeries_succ (G := H) (k := 1)
        (Subgroup.mem_top _) _
    have : (dmA 2 1)⁻¹ *
        (dmA 2 1 * (dmB 2 1 ^ 4)⁻¹ * commP (dmD 2 1) (dmB 2 1)) =
          (dmB 2 1 ^ 4)⁻¹ * commP (dmD 2 1) (dmB 2 1) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hB4) hW
  · simp only [oneHandleW4Mark, standardHandleMark_one, oneHandleW4]
    change (dmB 2 1)⁻¹ *
      (dmB 2 1 * commP (dmD 2 1) (dmB 2 1)) ∈
        twoCentralSeries H 2
    have hW : commP (dmD 2 1) (dmB 2 1) ∈ twoCentralSeries H 2 := by
      have heq : commP (dmD 2 1) (dmB 2 1) =
          ⁅(dmD 2 1)⁻¹, (dmB 2 1)⁻¹⁆ := by
        simp only [commP, commutatorElement_def, inv_inv]
      rw [heq]
      exact commutator_mem_twoCentralSeries_succ (G := H) (k := 1)
        (Subgroup.mem_top _) _
    have : (dmB 2 1)⁻¹ *
        (dmB 2 1 * commP (dmD 2 1) (dmB 2 1)) =
          commP (dmD 2 1) (dmB 2 1) := by group
    rwa [this]
  · simp only [oneHandleW4Mark, standardHandleMark_two]
    change (dmC 2 1)⁻¹ * (dmB 2 1 ^ 2 * dmC 2 1) ∈
      twoCentralSeries H 2
    have hB2 : dmB 2 1 ^ 2 ∈ twoCentralSeries H 2 :=
      sq_mem_twoCentralSeries_succ _ (Subgroup.mem_top _)
    have hC := (twoCentralSeries_normal H 2).conj_mem
      (dmB 2 1 ^ 2) hB2 (dmC 2 1)⁻¹
    simp only [inv_inv] at hC
    simpa only [mul_assoc] using hC
  · change (dmD 2 1)⁻¹ * dmD 2 1 ∈ twoCentralSeries H 2
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleW4Mark, mHandleIdx_coordU, mHandleIdx_coordV]

theorem oneHandleW6Mark_congr_standard (i : Fin (coreRank 1)) :
    (dmGen 2 1 i)⁻¹ * oneHandleW6Mark i ∈ twoCentralSeries H 2 := by
  rw [oneHandleW6Mark, oneHandleDirectModify,
    MpcOneHandleClassSixTarget.oneHandleW5Mark, oneHandleDirectModify]
  have h4 := w4_congr_standard i
  have h5 : oneHandleW5Factors i ∈ twoCentralSeries H 2 :=
    twoCentralSeries_antitone (G := H) (show 2 ≤ 3 by omega)
      (oneHandleW5Factors_depth i)
  have h6 : oneHandleC6CorrectedFactors i ∈ twoCentralSeries H 2 :=
    twoCentralSeries_antitone (G := H) (show 2 ≤ 4 by omega)
      (oneHandleC6CorrectedFactors_depth i)
  have hprod : (dmGen 2 1 i)⁻¹ *
      (oneHandleW4Mark i * oneHandleW5Factors i) ∈
        twoCentralSeries H 2 := by
    have heq : (dmGen 2 1 i)⁻¹ *
        (oneHandleW4Mark i * oneHandleW5Factors i) =
        ((dmGen 2 1 i)⁻¹ * oneHandleW4Mark i) *
          oneHandleW5Factors i := by group
    rw [heq]
    exact Subgroup.mul_mem _ h4 h5
  have heq : (dmGen 2 1 i)⁻¹ *
      (oneHandleW4Mark i * oneHandleW5Factors i *
        oneHandleC6CorrectedFactors i) =
      ((dmGen 2 1 i)⁻¹ *
        (oneHandleW4Mark i * oneHandleW5Factors i)) *
          oneHandleC6CorrectedFactors i := by group
  rw [heq]
  exact Subgroup.mul_mem _ hprod h6

theorem oneHandleW6Mark_level_congr_standard (i : Fin (coreRank 1)) :
    (levelMk H 7 (dmGen 2 1 i))⁻¹ * levelMk H 7 (oneHandleW6Mark i) ∈
      lambdaImage H 2 7 := by
  refine ⟨(dmGen 2 1 i)⁻¹ * oneHandleW6Mark i,
    oneHandleW6Mark_congr_standard i, ?_⟩
  simp only [map_mul, map_inv]

private theorem relativeCorrection_depth
    (F : OneHandleBalancedCoreLevelCorrection 6) :
    ∀ i, oneHandleBalancedCoreLevelCorrectionMark F i ∈ lambdaImage H 5 7 := by
  intro i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · exact F.corrA.2.1
  · exact F.corrB.2.1
  · exact ((oneHandleNeutralRelativeLambdaImage_le_relative 5 7 (by omega))
      F.corrC.2).1
  · exact F.corrD.2.1
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleBalancedCoreLevelCorrectionMark,
        mHandleIdx_coordU, mHandleIdx_coordV]

theorem oneHandleDirectLevelShift_W6_eq_standard
    (F : OneHandleBalancedCoreLevelCorrection 6) :
    oneHandleDirectLevelShift oneHandleW6Mark (relativeCoreToDirect F) =
      oneHandleDirectLevelShift (dmGen 2 1) (relativeCoreToDirect F) := by
  rw [oneHandleDirectLevelShift, oneHandleDirectLevelShift,
    relativeCoreToDirect_mark]
  have hc := relativeCorrection_depth F
  rw [evenRawStageShift_m (G := H) (by omega) (by omega) 1 6 (by omega)
      (fun i ↦ levelMk H 7 (oneHandleW6Mark i))
      (oneHandleBalancedCoreLevelCorrectionMark F) hc,
    evenRawStageShift_m (G := H) (by omega) (by omega) 1 6 (by omega)
      (fun i ↦ levelMk H 7 (dmGen 2 1 i))
      (oneHandleBalancedCoreLevelCorrectionMark F) hc]
  exact (evenRawDbarWord_congr_base
    oneHandleW6Mark_level_congr_standard hc).symm

theorem oneHandleForgetLevelMap_standard_relativeShift
    (F : OneHandleBalancedCoreLevelCorrection 6) :
    oneHandleForgetLevelMap 7
      (oneHandleDirectLevelShift (dmGen 2 1) (relativeCoreToDirect F)) = 1 := by
  rw [← oneHandleDirectLevelShift_W6_eq_standard]
  exact oneHandleForgetLevelMap_W6_relativeShift F

/-- The same finite relative correction map, now based at the standard six-letter marking. -/
noncomputable def oneHandleStandardRelativeShiftHom :
    OneHandleBalancedCoreLevelCorrection 6 →* oneHandleRelativeZLayer 6 where
  toFun F :=
    ⟨(oneHandleDirectLevelShiftHom (dmGen 2 1) 6 (by omega)
      (relativeCoreToDirect F)).1,
      ⟨(oneHandleDirectLevelShiftHom (dmGen 2 1) 6 (by omega)
        (relativeCoreToDirect F)).2,
        MonoidHom.mem_ker.mpr (by
          rw [oneHandleDirectLevelShiftHom_apply]
          exact oneHandleForgetLevelMap_standard_relativeShift F)⟩⟩
  map_one' := by
    apply Subtype.ext
    change ((oneHandleDirectLevelShiftHom (dmGen 2 1) 6 (by omega)).comp
      relativeCoreToDirectHom 1).1 = 1
    exact congrArg Subtype.val (map_one
      ((oneHandleDirectLevelShiftHom (dmGen 2 1) 6 (by omega)).comp
        relativeCoreToDirectHom))
  map_mul' F G := by
    apply Subtype.ext
    change ((oneHandleDirectLevelShiftHom (dmGen 2 1) 6 (by omega)).comp
      relativeCoreToDirectHom (F * G)).1 =
        ((oneHandleDirectLevelShiftHom (dmGen 2 1) 6 (by omega)).comp
          relativeCoreToDirectHom F).1 *
        ((oneHandleDirectLevelShiftHom (dmGen 2 1) 6 (by omega)).comp
          relativeCoreToDirectHom G).1
    exact congrArg Subtype.val (map_mul
      ((oneHandleDirectLevelShiftHom (dmGen 2 1) 6 (by omega)).comp
        relativeCoreToDirectHom) F G)

@[simp] theorem oneHandleStandardRelativeShiftHom_apply
    (F : OneHandleBalancedCoreLevelCorrection 6) :
    (oneHandleStandardRelativeShiftHom F).1 =
      oneHandleDirectLevelShift (dmGen 2 1) (relativeCoreToDirect F) := by
  exact oneHandleDirectLevelShiftHom_apply (dmGen 2 1) 6 (by omega)
    (relativeCoreToDirect F)

theorem oneHandleW6RelativeShiftHom_eq_standard :
    oneHandleW6RelativeShiftHom = oneHandleStandardRelativeShiftHom := by
  apply MonoidHom.ext
  intro F
  apply Subtype.ext
  rw [oneHandleW6RelativeShiftHom_apply,
    oneHandleStandardRelativeShiftHom_apply]
  exact oneHandleDirectLevelShift_W6_eq_standard F

theorem oneHandleW6RelativeShiftHom_range_eq_standard :
    oneHandleW6RelativeShiftHom.range = oneHandleStandardRelativeShiftHom.range := by
  rw [oneHandleW6RelativeShiftHom_eq_standard]

theorem relativeCorrectable_iff_standard_target_mem_range
    (E : OneHandleC7RelativeLift) :
    OneHandleC7RelativeCorrectable E ↔
      oneHandleC7RelativeTarget E ∈ oneHandleStandardRelativeShiftHom.range := by
  rw [← oneHandleW6RelativeShiftHom_range_eq_standard]
  exact relativeCorrectable_iff_target_mem_range E

#print axioms evenRawDbarWord_congr_base
#print axioms oneHandleW6Mark_congr_standard
#print axioms oneHandleW6Mark_level_congr_standard
#print axioms oneHandleDirectLevelShift_W6_eq_standard
#print axioms oneHandleStandardRelativeShiftHom
#print axioms oneHandleW6RelativeShiftHom_eq_standard
#print axioms oneHandleW6RelativeShiftHom_range_eq_standard
#print axioms relativeCorrectable_iff_standard_target_mem_range

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenBaseReduction
