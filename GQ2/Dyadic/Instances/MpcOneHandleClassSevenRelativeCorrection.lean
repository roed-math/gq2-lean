/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
import GQ2.Dyadic.Instances.MpcBalancedRelativeSpan

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedFiniteSpan
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSixCompactLift
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactSupply
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Roe.Labute

private abbrev H := DM 2 1

private theorem chi_of_forget_eq_one {e : H}
    (he : dmForgetHandles 2 1 e = 1) : chiM 2 1 e = 1 := by
  rw [← chiM_dmForgetHandles 2 1, he, map_one]

private theorem relative_mem_direct {x : levelQuot H 7}
    (hx : x ∈ oneHandleRelativeLambdaImage 5 7) :
    x ∈ oneHandleDirectLambdaImage 5 7 := by
  obtain ⟨e, he, hef, hex⟩ :=
    (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) x).mp hx
  exact (mem_oneHandleDirectLambdaImage_iff_exists_exact x).mpr
    ⟨e, he, chi_of_forget_eq_one hef, hex⟩

private theorem neutralRelative_mem_direct {x : levelQuot H 7}
    (hx : x ∈ oneHandleNeutralRelativeLambdaImage 5 7) :
    x ∈ oneHandleDirectNeutralLambdaImage 5 7 := by
  obtain ⟨e, he, hef, hrow, hex⟩ :=
    (mem_oneHandleNeutralRelativeLambdaImage_iff_exists_exact x).mp hx
  exact (mem_oneHandleDirectNeutralLambdaImage_iff_exists_exact x).mpr
    ⟨e, he, chi_of_forget_eq_one hef, hrow, hex⟩

/-- Regard an exact relative four-core correction as an ordinary legal direct correction. -/
def relativeCoreToDirect
    (F : OneHandleBalancedCoreLevelCorrection 6) :
    OneHandleDirectLevelCorrection 6 :=
  (⟨F.corrA.1, relative_mem_direct F.corrA.2⟩,
    ⟨F.corrB.1, relative_mem_direct F.corrB.2⟩,
    ⟨F.corrC.1, neutralRelative_mem_direct F.corrC.2⟩,
    ⟨F.corrD.1, relative_mem_direct F.corrD.2⟩)

theorem relativeCoreToDirect_mark
    (F : OneHandleBalancedCoreLevelCorrection 6) :
    oneHandleDirectLevelCorrectionMark (relativeCoreToDirect F) =
      oneHandleBalancedCoreLevelCorrectionMark F := by
  rfl

noncomputable def relativeCoreToDirectHom :
    OneHandleBalancedCoreLevelCorrection 6 →*
      OneHandleDirectLevelCorrection 6 where
  toFun := relativeCoreToDirect
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- The finite direct correction represented by a lifted compact class-seven packet. -/
def relativeLiftToDirect
    (E : OneHandleC7RelativeLift) : OneHandleDirectLevelCorrection 6 :=
  (⟨levelMk H 7 (E.factors 0),
      (mem_oneHandleDirectLambdaImage_iff_exists_exact _).mpr
        ⟨E.factors 0, E.depth 0, E.chi 0, rfl⟩⟩,
    ⟨levelMk H 7 (E.factors 1),
      (mem_oneHandleDirectLambdaImage_iff_exists_exact _).mpr
        ⟨E.factors 1, E.depth 1, E.chi 1, rfl⟩⟩,
    ⟨levelMk H 7 (E.factors 2),
      (mem_oneHandleDirectNeutralLambdaImage_iff_exists_exact _).mpr
        ⟨E.factors 2, E.depth 2, E.chi 2, E.row, rfl⟩⟩,
    ⟨levelMk H 7 (E.factors 3),
      (mem_oneHandleDirectLambdaImage_iff_exists_exact _).mpr
        ⟨E.factors 3, E.depth 3, E.chi 3, rfl⟩⟩)

theorem relativeLiftToDirect_mark (E : OneHandleC7RelativeLift) :
    oneHandleDirectLevelCorrectionMark (relativeLiftToDirect E) =
      fun i ↦ levelMk H 7 (E.factors i) := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [oneHandleDirectLevelCorrectionMark,
        mHandleIdx_coordU, E.handleU]
    · simp [oneHandleDirectLevelCorrectionMark,
        mHandleIdx_coordV, E.handleV]

theorem relativeLift_levelShift (E : OneHandleC7RelativeLift) :
    oneHandleDirectLevelShift oneHandleW6Mark (relativeLiftToDirect E) =
      (levelMk H 7 (mRelWord 2 oneHandleW6Mark))⁻¹ * E.residual := by
  rw [oneHandleDirectLevelShift, relativeLiftToDirect_mark]
  change oneHandleDirectRelatorShift oneHandleW6Mark E.factors 6 = _
  rw [oneHandleDirectRelatorShift_eq]
  rfl

/-- The exact finite relative correction equation for a chosen compact lift. -/
def OneHandleC7RelativeCorrectable (E : OneHandleC7RelativeLift) : Prop :=
  ∃ F : OneHandleBalancedCoreLevelCorrection 6,
    oneHandleDirectLevelShift oneHandleW6Mark (relativeCoreToDirect F) =
      E.residual⁻¹

theorem oneHandleForgetLevelMap_W6_relativeShift
    (F : OneHandleBalancedCoreLevelCorrection 6) :
    oneHandleForgetLevelMap 7
      (oneHandleDirectLevelShift oneHandleW6Mark
        (relativeCoreToDirect F)) = 1 := by
  rw [oneHandleDirectLevelShift, relativeCoreToDirect_mark, stageShift]
  change oneHandleForgetLevelMap 7
    ((mRelWord 2 (fun i ↦ levelMk H 7 (oneHandleW6Mark i)))⁻¹ *
      mRelWord 2 (fun i ↦ levelMk H 7 (oneHandleW6Mark i) *
        oneHandleBalancedCoreLevelCorrectionMark F i)) = 1
  rw [map_mul, map_inv, map_mRelWord, map_mRelWord]
  have hsame :
      (fun i ↦ oneHandleForgetLevelMap 7
        (levelMk H 7 (oneHandleW6Mark i) *
          oneHandleBalancedCoreLevelCorrectionMark F i)) =
        fun i ↦ oneHandleForgetLevelMap 7
          (levelMk H 7 (oneHandleW6Mark i)) := by
    funext i
    rw [map_mul]
    have hi := congrFun
      (oneHandleForgetLevelMap_coreLevelCorrectionMark F) i
    rw [hi, mul_one]
  rw [hsame]
  exact inv_mul_cancel _

/-- The class-seven relative shift homomorphism at the explicit W6 marking. -/
noncomputable def oneHandleW6RelativeShiftHom :
    OneHandleBalancedCoreLevelCorrection 6 →*
      oneHandleRelativeZLayer 6 where
  toFun F :=
    ⟨(oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)
      (relativeCoreToDirect F)).1,
      ⟨(oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)
        (relativeCoreToDirect F)).2,
        MonoidHom.mem_ker.mpr (by
          rw [oneHandleDirectLevelShiftHom_apply]
          exact oneHandleForgetLevelMap_W6_relativeShift F)⟩⟩
  map_one' := by
    apply Subtype.ext
    change ((oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)).comp
      relativeCoreToDirectHom 1).1 = 1
    exact congrArg Subtype.val (map_one
      ((oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)).comp
        relativeCoreToDirectHom))
  map_mul' F G := by
    apply Subtype.ext
    change ((oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)).comp
      relativeCoreToDirectHom (F * G)).1 =
        ((oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)).comp
          relativeCoreToDirectHom F).1 *
        ((oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)).comp
          relativeCoreToDirectHom G).1
    exact congrArg Subtype.val (map_mul
      ((oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)).comp
        relativeCoreToDirectHom) F G)

@[simp] theorem oneHandleW6RelativeShiftHom_apply
    (F : OneHandleBalancedCoreLevelCorrection 6) :
    (oneHandleW6RelativeShiftHom F).1 =
      oneHandleDirectLevelShift oneHandleW6Mark (relativeCoreToDirect F) := by
  exact oneHandleDirectLevelShiftHom_apply oneHandleW6Mark 6 (by omega)
    (relativeCoreToDirect F)

/-- The inverse residual as an element of the existing relative central layer. -/
def oneHandleC7RelativeTarget (E : OneHandleC7RelativeLift) :
    oneHandleRelativeZLayer 6 :=
  ⟨E.residual⁻¹, ⟨Subgroup.inv_mem _ E.residual_mem_zLayer,
    MonoidHom.mem_ker.mpr (by
      rw [map_inv]
      have hzero : oneHandleForgetLevelMap 7 E.residual = 1 := by
        rw [OneHandleC7RelativeLift.residual]
        change relativeLevelMap (dmForgetHandles 2 1) 7
          (levelMk H 7 (mRelWord 2 E.modified)) = 1
        rw [relativeLevelMap_levelMk]
        exact (lim_mem_twoCentralSeries_iff_levelMk 7 _).mp
          E.forget_relator_mem
      change ((oneHandleForgetLevelMap 7) E.residual)⁻¹ = 1
      rw [hzero, inv_one])⟩⟩

@[simp] theorem oneHandleC7RelativeTarget_val (E : OneHandleC7RelativeLift) :
    (oneHandleC7RelativeTarget E).1 = E.residual⁻¹ := rfl

theorem relativeCorrectable_iff_target_mem_range
    (E : OneHandleC7RelativeLift) :
    OneHandleC7RelativeCorrectable E ↔
      oneHandleC7RelativeTarget E ∈ oneHandleW6RelativeShiftHom.range := by
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨F, Subtype.ext ?_⟩
    rw [oneHandleW6RelativeShiftHom_apply,
      oneHandleC7RelativeTarget_val]
    exact hF
  · rintro ⟨F, hF⟩
    exact ⟨F, by
      have h := congrArg Subtype.val hF
      rw [oneHandleW6RelativeShiftHom_apply,
        oneHandleC7RelativeTarget_val] at h
      exact h⟩

theorem relativeCorrectable_of_residual_eq_one
    (E : OneHandleC7RelativeLift) (hE : E.residual = 1) :
    OneHandleC7RelativeCorrectable E := by
  refine ⟨1, ?_⟩
  have hone : relativeCoreToDirect
      (1 : OneHandleBalancedCoreLevelCorrection 6) =
      (1 : OneHandleDirectLevelCorrection 6) := by
    rfl
  rw [hone, show oneHandleDirectLevelShift oneHandleW6Mark
      (1 : OneHandleDirectLevelCorrection 6) = 1 by
        rw [← oneHandleDirectLevelShiftHom_apply oneHandleW6Mark 6 (by omega),
          map_one]
        rfl,
    hE, inv_one]

theorem oneHandleW6Correctable_of_relativeCorrectable
    (E : OneHandleC7RelativeLift) (hE : OneHandleC7RelativeCorrectable E) :
    OneHandleW6Correctable := by
  obtain ⟨F, hF⟩ := hE
  let A := relativeLiftToDirect E
  let R := relativeCoreToDirect F
  have hmul : oneHandleDirectLevelShift oneHandleW6Mark (A * R) =
      oneHandleDirectLevelShift oneHandleW6Mark A *
        oneHandleDirectLevelShift oneHandleW6Mark R := by
    rw [← oneHandleDirectLevelShiftHom_apply oneHandleW6Mark 6 (by omega),
      ← oneHandleDirectLevelShiftHom_apply oneHandleW6Mark 6 (by omega),
      ← oneHandleDirectLevelShiftHom_apply oneHandleW6Mark 6 (by omega)]
    exact congrArg Subtype.val
      (map_mul (oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)) A R)
  have hkill : oneHandleDirectLevelShift oneHandleW6Mark (A * R) =
      (levelMk H 7 (mRelWord 2 oneHandleW6Mark))⁻¹ := by
    rw [hmul, show oneHandleDirectLevelShift oneHandleW6Mark A =
      (levelMk H 7 (mRelWord 2 oneHandleW6Mark))⁻¹ * E.residual by
        exact relativeLift_levelShift E, show
      oneHandleDirectLevelShift oneHandleW6Mark R = E.residual⁻¹ by
        exact hF]
    group
  exact (nonempty_directCorrection_iff_exists_levelCorrection
    oneHandleW6Mark 6).mpr ⟨A * R, hkill⟩

theorem oneHandleDirectSet_seven_nonempty_of_relativeCorrectable
    (E : OneHandleC7RelativeLift) (hE : OneHandleC7RelativeCorrectable E) :
    (oneHandleDirectSet 7).Nonempty :=
  oneHandleDirectSet_seven_nonempty_of_W6Correctable
    (oneHandleW6Correctable_of_relativeCorrectable E hE)

theorem oneHandleW6Correctable_iff_exists_relativeCorrectable :
    OneHandleW6Correctable ↔
      ∃ E : OneHandleC7RelativeLift, OneHandleC7RelativeCorrectable E := by
  constructor
  · intro h
    obtain ⟨E, hE⟩ :=
      exists_relativeLift_residual_eq_one_of_oneHandleW6Correctable h
    exact ⟨E, relativeCorrectable_of_residual_eq_one E hE⟩
  · rintro ⟨E, hE⟩
    exact oneHandleW6Correctable_of_relativeCorrectable E hE

#print axioms relativeCoreToDirect
#print axioms relativeLiftToDirect
#print axioms relativeLift_levelShift
#print axioms OneHandleC7RelativeCorrectable
#print axioms oneHandleW6RelativeShiftHom
#print axioms relativeCorrectable_iff_target_mem_range
#print axioms oneHandleW6Correctable_of_relativeCorrectable
#print axioms oneHandleDirectSet_seven_nonempty_of_relativeCorrectable
#print axioms oneHandleW6Correctable_iff_exists_relativeCorrectable

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection

