/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan

/-!
# The four literal rows of the direct one-handle span

The finite source of W247 is a direct product of four constrained coordinate groups.  This
file splits its shift range into the four literal coordinate ranges and identifies their
values: the `A` row is a square plus two brackets, while the `B`, `C`, and `D` rows are the
three cross brackets.

The remaining successor boundary is therefore target membership in one explicit subgroup
join.  This is an exact reformulation, not a surjectivity assertion.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Roe.Labute

private abbrev H := DM 2 1

/-! ## Coordinate inclusions and their span -/

noncomputable def oneHandleDirectCoordA (k : ℕ) :
    oneHandleDirectLambdaImage (k - 1) (k + 1) →*
      OneHandleDirectLevelCorrection k where
  toFun x := (x, 1, 1, 1)
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def oneHandleDirectCoordB (k : ℕ) :
    oneHandleDirectLambdaImage (k - 1) (k + 1) →*
      OneHandleDirectLevelCorrection k where
  toFun x := (1, x, 1, 1)
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def oneHandleDirectCoordC (k : ℕ) :
    oneHandleDirectNeutralLambdaImage (k - 1) (k + 1) →*
      OneHandleDirectLevelCorrection k where
  toFun x := (1, 1, x, 1)
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def oneHandleDirectCoordD (k : ℕ) :
    oneHandleDirectLambdaImage (k - 1) (k + 1) →*
      OneHandleDirectLevelCorrection k where
  toFun x := (1, 1, 1, x)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem oneHandleDirectLevelCorrection_eq_coords
    {k : ℕ} (E : OneHandleDirectLevelCorrection k) :
    E = oneHandleDirectCoordA k E.1 *
        oneHandleDirectCoordB k E.2.1 *
        oneHandleDirectCoordC k E.2.2.1 *
        oneHandleDirectCoordD k E.2.2.2 := by
  rcases E with ⟨a, b, c, d⟩
  have hA : ∀ y, oneHandleDirectCoordA k y = (y, 1, 1, 1) := fun _ ↦ rfl
  have hB : ∀ y, oneHandleDirectCoordB k y = (1, y, 1, 1) := fun _ ↦ rfl
  have hC : ∀ y, oneHandleDirectCoordC k y = (1, 1, y, 1) := fun _ ↦ rfl
  have hD : ∀ y, oneHandleDirectCoordD k y = (1, 1, 1, y) := fun _ ↦ rfl
  simp [hA, hB, hC, hD]

noncomputable def oneHandleDirectShiftA
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleDirectLambdaImage (k - 1) (k + 1) →* zLayer H k :=
  (oneHandleDirectLevelShiftHom m k hk).comp (oneHandleDirectCoordA k)

noncomputable def oneHandleDirectShiftB
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleDirectLambdaImage (k - 1) (k + 1) →* zLayer H k :=
  (oneHandleDirectLevelShiftHom m k hk).comp (oneHandleDirectCoordB k)

noncomputable def oneHandleDirectShiftC
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleDirectNeutralLambdaImage (k - 1) (k + 1) →* zLayer H k :=
  (oneHandleDirectLevelShiftHom m k hk).comp (oneHandleDirectCoordC k)

noncomputable def oneHandleDirectShiftD
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleDirectLambdaImage (k - 1) (k + 1) →* zLayer H k :=
  (oneHandleDirectLevelShiftHom m k hk).comp (oneHandleDirectCoordD k)

def oneHandleDirectCoordinateSpan
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    Subgroup (zLayer H k) :=
  ((oneHandleDirectShiftA m k hk).range ⊔
    (oneHandleDirectShiftB m k hk).range) ⊔
  ((oneHandleDirectShiftC m k hk).range ⊔
    (oneHandleDirectShiftD m k hk).range)

theorem oneHandleDirectLevelShift_range_eq_coordinateSpan
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleDirectLevelShiftHom m k hk).range =
      oneHandleDirectCoordinateSpan m k hk := by
  apply le_antisymm
  · rintro y ⟨E, rfl⟩
    rw [oneHandleDirectLevelCorrection_eq_coords E]
    simp only [map_mul]
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · apply Subgroup.mul_mem
        · exact (show (oneHandleDirectShiftA m k hk).range ≤
              oneHandleDirectCoordinateSpan m k hk from
            le_trans le_sup_left le_sup_left) ⟨E.1, rfl⟩
        · exact (show (oneHandleDirectShiftB m k hk).range ≤
              oneHandleDirectCoordinateSpan m k hk from
            le_trans le_sup_right le_sup_left) ⟨E.2.1, rfl⟩
      · exact (show (oneHandleDirectShiftC m k hk).range ≤
            oneHandleDirectCoordinateSpan m k hk from
          le_trans le_sup_left le_sup_right) ⟨E.2.2.1, rfl⟩
    · exact (show (oneHandleDirectShiftD m k hk).range ≤
          oneHandleDirectCoordinateSpan m k hk from
        le_trans le_sup_right le_sup_right) ⟨E.2.2.2, rfl⟩
  · apply sup_le
    · apply sup_le
      · rintro y ⟨x, rfl⟩
        exact ⟨oneHandleDirectCoordA k x, rfl⟩
      · rintro y ⟨x, rfl⟩
        exact ⟨oneHandleDirectCoordB k x, rfl⟩
    · apply sup_le
      · rintro y ⟨x, rfl⟩
        exact ⟨oneHandleDirectCoordC k x, rfl⟩
      · rintro y ⟨x, rfl⟩
        exact ⟨oneHandleDirectCoordD k x, rfl⟩

/-! ## Literal coordinate formulas -/

private theorem directCoreIdx_ne {i j : Fin (coreRank 1)}
    (hij : (i : ℕ) ≠ (j : ℕ)) : i ≠ j :=
  fun h ↦ hij (congrArg Fin.val h)

@[simp] private theorem directIdx01 : (0 : Fin (coreRank 1)) ≠ 1 :=
  directCoreIdx_ne (by rw [coreVal_zero, coreVal_one]; omega)
@[simp] private theorem directIdx10 : (1 : Fin (coreRank 1)) ≠ 0 := directIdx01.symm
@[simp] private theorem directIdx02 : (0 : Fin (coreRank 1)) ≠ 2 :=
  directCoreIdx_ne (by rw [coreVal_zero, coreVal_two]; omega)
@[simp] private theorem directIdx20 : (2 : Fin (coreRank 1)) ≠ 0 := directIdx02.symm
@[simp] private theorem directIdx03 : (0 : Fin (coreRank 1)) ≠ 3 :=
  directCoreIdx_ne (by rw [coreVal_zero, coreVal_three]; omega)
@[simp] private theorem directIdx30 : (3 : Fin (coreRank 1)) ≠ 0 := directIdx03.symm
@[simp] private theorem directIdx12 : (1 : Fin (coreRank 1)) ≠ 2 :=
  directCoreIdx_ne (by rw [coreVal_one, coreVal_two]; omega)
@[simp] private theorem directIdx21 : (2 : Fin (coreRank 1)) ≠ 1 := directIdx12.symm
@[simp] private theorem directIdx13 : (1 : Fin (coreRank 1)) ≠ 3 :=
  directCoreIdx_ne (by rw [coreVal_one, coreVal_three]; omega)
@[simp] private theorem directIdx31 : (3 : Fin (coreRank 1)) ≠ 1 := directIdx13.symm
@[simp] private theorem directIdx23 : (2 : Fin (coreRank 1)) ≠ 3 :=
  directCoreIdx_ne (by rw [coreVal_two, coreVal_three]; omega)
@[simp] private theorem directIdx32 : (3 : Fin (coreRank 1)) ≠ 2 := directIdx23.symm

private theorem directHandleU_ne_core (j : Fin 1) {i : Fin (coreRank 1)}
    (hi : (i : ℕ) < 4) : handleIdxU j ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [handleIdxU_val] at hv
  omega

private theorem directHandleV_ne_core (j : Fin 1) {i : Fin (coreRank 1)}
    (hi : (i : ℕ) < 4) : handleIdxV j ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [handleIdxV_val] at hv
  omega

theorem oneHandleDirectLevelToRaw_coordA
    {k : ℕ} (x : oneHandleDirectLambdaImage (k - 1) (k + 1)) :
    oneHandleDirectLevelToRaw (oneHandleDirectCoordA k x) =
      evenRawDepthCoordinateCorrection 0
        ⟨x.1, oneHandleDirectLambdaImage_le_lambdaImage _ _ x.2⟩ := by
  have hc : ∀ y, oneHandleDirectCoordA k y = (y, 1, 1, 1) := fun _ ↦ rfl
  apply EvenRawDepthCorrection.ext
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · rw [evenRawDepthCoordinateCorrection_apply, if_neg directIdx10]
    simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
        hc, mHandleIdx_coordU, mHandleIdx_coordV,
        directHandleU_ne_core j (by rw [coreVal_zero]; omega),
        directHandleV_ne_core j (by rw [coreVal_zero]; omega)]

theorem oneHandleDirectLevelToRaw_coordB
    {k : ℕ} (x : oneHandleDirectLambdaImage (k - 1) (k + 1)) :
    oneHandleDirectLevelToRaw (oneHandleDirectCoordB k x) =
      evenRawDepthCoordinateCorrection 1
        ⟨x.1, oneHandleDirectLambdaImage_le_lambdaImage _ _ x.2⟩ := by
  have hc : ∀ y, oneHandleDirectCoordB k y = (1, y, 1, 1) := fun _ ↦ rfl
  apply EvenRawDepthCorrection.ext
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · rw [evenRawDepthCoordinateCorrection_apply, if_neg directIdx01]
    simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
        hc, mHandleIdx_coordU, mHandleIdx_coordV,
        directHandleU_ne_core j (by rw [coreVal_one]; omega),
        directHandleV_ne_core j (by rw [coreVal_one]; omega)]

theorem oneHandleDirectLevelToRaw_coordC
    {k : ℕ} (x : oneHandleDirectNeutralLambdaImage (k - 1) (k + 1)) :
    oneHandleDirectLevelToRaw (oneHandleDirectCoordC k x) =
      evenRawDepthCoordinateCorrection 2
        ⟨x.1, oneHandleDirectNeutralLambdaImage_le_lambdaImage _ _ x.2⟩ := by
  have hc : ∀ y, oneHandleDirectCoordC k y = (1, 1, y, 1) := fun _ ↦ rfl
  apply EvenRawDepthCorrection.ext
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
        hc, mHandleIdx_coordU, mHandleIdx_coordV,
        directHandleU_ne_core j (by rw [coreVal_two]; omega),
        directHandleV_ne_core j (by rw [coreVal_two]; omega)]

theorem oneHandleDirectLevelToRaw_coordD
    {k : ℕ} (x : oneHandleDirectLambdaImage (k - 1) (k + 1)) :
    oneHandleDirectLevelToRaw (oneHandleDirectCoordD k x) =
      evenRawDepthCoordinateCorrection 3
        ⟨x.1, oneHandleDirectLambdaImage_le_lambdaImage _ _ x.2⟩ := by
  have hc : ∀ y, oneHandleDirectCoordD k y = (1, 1, 1, y) := fun _ ↦ rfl
  apply EvenRawDepthCorrection.ext
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
      hc]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleDirectLevelToRaw, oneHandleDirectLevelCorrectionMark,
        hc, mHandleIdx_coordU, mHandleIdx_coordV,
        directHandleU_ne_core j (by rw [coreVal_three]; omega),
        directHandleV_ne_core j (by rw [coreVal_three]; omega)]

theorem oneHandleDirectShiftA_apply
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleDirectLambdaImage (k - 1) (k + 1)) :
    (oneHandleDirectShiftA m k hk x).1 =
      x.1 ^ 2 * commP x.1 (levelMk H (k + 1) (m 0)) *
        commP x.1 (levelMk H (k + 1) (m 1)) := by
  change ((evenRawDepthShiftHom (fun i ↦ levelMk H (k + 1) (m i)) hk)
    (oneHandleDirectLevelToRaw (oneHandleDirectCoordA k x))).1 = _
  rw [oneHandleDirectLevelToRaw_coordA]
  exact evenRawDepthShiftHom_zero_apply _ hk
    ⟨x.1, oneHandleDirectLambdaImage_le_lambdaImage _ _ x.2⟩

theorem oneHandleDirectShiftB_apply
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleDirectLambdaImage (k - 1) (k + 1)) :
    (oneHandleDirectShiftB m k hk x).1 =
      commP x.1 (levelMk H (k + 1) (m 0)) := by
  change ((evenRawDepthShiftHom (fun i ↦ levelMk H (k + 1) (m i)) hk)
    (oneHandleDirectLevelToRaw (oneHandleDirectCoordB k x))).1 = _
  rw [oneHandleDirectLevelToRaw_coordB]
  exact evenRawDepthShiftHom_one_apply _ hk
    ⟨x.1, oneHandleDirectLambdaImage_le_lambdaImage _ _ x.2⟩

theorem oneHandleDirectShiftC_apply
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleDirectNeutralLambdaImage (k - 1) (k + 1)) :
    (oneHandleDirectShiftC m k hk x).1 =
      commP x.1 (levelMk H (k + 1) (m 3)) := by
  change ((evenRawDepthShiftHom (fun i ↦ levelMk H (k + 1) (m i)) hk)
    (oneHandleDirectLevelToRaw (oneHandleDirectCoordC k x))).1 = _
  rw [oneHandleDirectLevelToRaw_coordC]
  exact evenRawDepthShiftHom_two_apply _ hk
    ⟨x.1, oneHandleDirectNeutralLambdaImage_le_lambdaImage _ _ x.2⟩

theorem oneHandleDirectShiftD_apply
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleDirectLambdaImage (k - 1) (k + 1)) :
    (oneHandleDirectShiftD m k hk x).1 =
      commP x.1 (levelMk H (k + 1) (m 2)) := by
  change ((evenRawDepthShiftHom (fun i ↦ levelMk H (k + 1) (m i)) hk)
    (oneHandleDirectLevelToRaw (oneHandleDirectCoordD k x))).1 = _
  rw [oneHandleDirectLevelToRaw_coordD]
  exact evenRawDepthShiftHom_three_apply _ hk
    ⟨x.1, oneHandleDirectLambdaImage_le_lambdaImage _ _ x.2⟩

def OneHandleDirectCoordinateSpanSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      oneHandleDirectLevelTarget hm ∈
        oneHandleDirectCoordinateSpan m k (by omega)

theorem directCoordinateSpanSupply_iff_finiteRangeSupply :
    OneHandleDirectCoordinateSpanSupply ↔ OneHandleDirectFiniteRangeSupply := by
  constructor <;> intro Hspan k hk m hm
  · rw [oneHandleDirectLevelShift_range_eq_coordinateSpan]
    exact Hspan k hk m hm
  · rw [← oneHandleDirectLevelShift_range_eq_coordinateSpan]
    exact Hspan k hk m hm

theorem mpcPivShiftH_two_one_of_directCoordinateSpan
    (Hspan : OneHandleDirectCoordinateSpanSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_directFiniteRange
    (directCoordinateSpanSupply_iff_finiteRangeSupply.mp Hspan)

#print axioms oneHandleDirectCoordA
#print axioms oneHandleDirectCoordB
#print axioms oneHandleDirectCoordC
#print axioms oneHandleDirectCoordD
#print axioms oneHandleDirectLevelCorrection_eq_coords
#print axioms oneHandleDirectShiftA
#print axioms oneHandleDirectShiftB
#print axioms oneHandleDirectShiftC
#print axioms oneHandleDirectShiftD
#print axioms oneHandleDirectCoordinateSpan
#print axioms oneHandleDirectLevelShift_range_eq_coordinateSpan
#print axioms oneHandleDirectLevelToRaw_coordA
#print axioms oneHandleDirectLevelToRaw_coordB
#print axioms oneHandleDirectLevelToRaw_coordC
#print axioms oneHandleDirectLevelToRaw_coordD
#print axioms oneHandleDirectShiftA_apply
#print axioms oneHandleDirectShiftB_apply
#print axioms oneHandleDirectShiftC_apply
#print axioms oneHandleDirectShiftD_apply
#print axioms OneHandleDirectCoordinateSpanSupply
#print axioms directCoordinateSpanSupply_iff_finiteRangeSupply
#print axioms mpcPivShiftH_two_one_of_directCoordinateSpan

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan
