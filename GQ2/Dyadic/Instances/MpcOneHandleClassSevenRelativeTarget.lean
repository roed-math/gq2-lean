/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenPivotLift

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad
open GQ2.Dyadic.Instances.MpcMk
open GQ2.Dyadic.Instances.MpcSx
open GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleClassSixCompactLift
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactSupply
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenPivotLift
open GQ2.Roe.Labute

private abbrev H := DM 2 1

/-- A direct one-handle factor packet whose compact image is a genuine class-seven
successor. -/
structure OneHandleC7RelativeLift where
  factors : Fin (coreRank 1) → H
  compactFactors : Fin (coreRank 1) → (DM 2 0 : Type)
  depth : ∀ i, factors i ∈ twoCentralSeries H 5
  handleU : ∀ j : Fin 1, factors (handleIdxU j) = 1
  handleV : ∀ j : Fin 1, factors (handleIdxV j) = 1
  chi : ∀ i, chiM 2 1 (factors i) = 1
  row : ∀ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
    toAdd (f (factors 2)) = 0
  forget : ∀ i, dmForgetHandles 2 1 (factors i) = compactFactors i
  compactRelator :
    mRelWord 2 (fun i ↦ compactC6Mark i * compactFactors i) ∈
      twoCentralSeries (DM 2 0 : Type) 7

theorem exists_oneHandleC7RelativeLift : Nonempty OneHandleC7RelativeLift := by
  obtain ⟨us, ut, um, un, hm, hkill⟩ := compactC7_fullSupply
  obtain ⟨ys, hys, hchis, hfs⟩ := exists_oneHandleDepthChiLift hm.1
  obtain ⟨yt, hyt, hchit, hft⟩ := exists_oneHandleDepthChiLift hm.2.1
  obtain ⟨ym, hym, hchim, hrowm, hfm⟩ := exists_oneHandlePivotLift hm.2.2.1
  obtain ⟨yn, hyn, hchin, hfn⟩ := exists_oneHandleDepthChiLift hm.2.2.2
  let e : Fin (coreRank 1) → H :=
    fullMark ys yt ym yn (fun _ ↦ 1) (fun _ ↦ 1)
  let e0 : Fin (coreRank 1) → (DM 2 0 : Type) :=
    fullMark us ut um un (fun _ ↦ 1) (fun _ ↦ 1)
  have hnext :
      (compactC6Tuple.1 * us, compactC6Tuple.2.1 * ut,
        compactC6Tuple.2.2.1 * um, compactC6Tuple.2.2.2 * un) ∈
        mpcWordSet 7 := by
    apply mpcBld_step compactC6Tuple_mem us ut um un
    · exact mpcSx_kill_le_corr (by omega) hm.1
    · exact hm.1.2
    · exact mpcSx_kill_le_corr (by omega) hm.2.1
    · exact hm.2.1.2
    · exact mpcMk_pivotKill_le_corrC (by omega) hm.2.2.1
    · exact hm.2.2.1.2
    · exact mpcSx_kill_le_corr (by omega) hm.2.2.2
    · exact hm.2.2.2.2
    · simpa [mpcLadDefect] using hkill
  refine ⟨⟨e, e0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · simpa [e] using hys
    · simpa [e] using hyt
    · simpa [e] using hym
    · simpa [e] using hyn
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
        simp [e, mHandleIdx_coordU, mHandleIdx_coordV]
  · intro j
    simp [e]
  · intro j
    simp [e]
  · intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · simpa [e] using hchis
    · simpa [e] using hchit
    · simpa [e] using hchim
    · simpa [e] using hchin
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
        simp [e, mHandleIdx_coordU, mHandleIdx_coordV]
  · intro f
    simpa [e] using hrowm f
  · intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · simpa [e, e0] using hfs
    · simpa [e, e0] using hft
    · simpa [e, e0] using hfm
    · simpa [e, e0] using hfn
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
        simp [e, e0, mHandleIdx_coordU, mHandleIdx_coordV]
  · have hmark : (fun i ↦ compactC6Mark i * e0 i) =
        fullMark
          (mpcWordLetA (compactC6Tuple.1 * us))
          (mpcWordLetB (compactC6Tuple.2.1 * ut))
          (mpcWordLetC (compactC6Tuple.2.2.1 * um))
          (mpcWordLetD (compactC6Tuple.2.2.2 * un))
          (fun _ ↦ 1) (fun _ ↦ 1) := by
      funext i
      rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · simp [e0, compactC6Mark, compactW5Mark, compactC6Factors,
          compactC6Tuple, mpcWordLetA]
        group
      · simp [e0, compactC6Mark, compactW5Mark, compactC6Factors,
          compactC6Tuple, mpcWordLetB]
        group
      · simp [e0, compactC6Mark, compactW5Mark, compactC6Factors,
          compactC6Tuple, mpcWordLetC]
        group
      · simp [e0, compactC6Mark, compactW5Mark, compactC6Factors,
          compactC6Tuple, mpcWordLetD]
        group
      · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
          simp [e0, compactC6Mark, compactW5Mark, compactC6Factors,
            mHandleIdx_coordU, mHandleIdx_coordV]
    rw [hmark]
    simpa [mRelWord, handleWord_one] using hnext.2.2.2.2

def OneHandleC7RelativeLift.modified (E : OneHandleC7RelativeLift) :
    Fin (coreRank 1) → H :=
  oneHandleDirectModify oneHandleW6Mark E.factors

theorem OneHandleC7RelativeLift.forget_modified
    (E : OneHandleC7RelativeLift) (i : Fin (coreRank 1)) :
    dmForgetHandles 2 1 (E.modified i) =
      compactC6Mark i * E.compactFactors i := by
  rw [OneHandleC7RelativeLift.modified, oneHandleDirectModify, map_mul,
    dmForgetHandles_oneHandleW6Mark, E.forget]

theorem OneHandleC7RelativeLift.forget_relator_mem
    (E : OneHandleC7RelativeLift) :
    dmForgetHandles 2 1 (mRelWord 2 E.modified) ∈
      twoCentralSeries (DM 2 0 : Type) 7 := by
  rw [map_mRelWord]
  have hfun : (fun i ↦ dmForgetHandles 2 1 (E.modified i)) =
      fun i ↦ compactC6Mark i * E.compactFactors i := by
    funext i
    exact E.forget_modified i
  rw [hfun]
  exact E.compactRelator

noncomputable def dmForgetHandlesLevelSeven :
    levelQuot H 7 →* levelQuot (DM 2 0 : Type) 7 :=
  QuotientGroup.map (twoCentralSeries H 7)
    (twoCentralSeries (DM 2 0 : Type) 7)
    (dmForgetHandles 2 1).toMonoidHom (by
      intro x hx
      exact map_twoCentralSeries_le (dmForgetHandles 2 1).toMonoidHom
        (dmForgetHandles 2 1).continuous_toFun 7 ⟨x, hx, rfl⟩)

@[simp] theorem dmForgetHandlesLevelSeven_levelMk (x : H) :
    dmForgetHandlesLevelSeven (levelMk H 7 x) =
      levelMk (DM 2 0 : Type) 7 (dmForgetHandles 2 1 x) := by
  rfl

def OneHandleC7RelativeLift.residual (E : OneHandleC7RelativeLift) :
    levelQuot H 7 := levelMk H 7 (mRelWord 2 E.modified)

theorem OneHandleC7RelativeLift.residual_mem_ker
    (E : OneHandleC7RelativeLift) :
    E.residual ∈ dmForgetHandlesLevelSeven.ker := by
  rw [MonoidHom.mem_ker, OneHandleC7RelativeLift.residual,
    dmForgetHandlesLevelSeven_levelMk]
  exact (lim_mem_twoCentralSeries_iff_levelMk 7 _).mp E.forget_relator_mem

theorem OneHandleC7RelativeLift.residual_mem_zLayer
    (E : OneHandleC7RelativeLift) : E.residual ∈ zLayer H 6 := by
  have hdepth : ∀ i, levelMk H 7 (E.factors i) ∈ lambdaImage H 5 7 :=
    fun i ↦ ⟨E.factors i, E.depth i, rfl⟩
  have hshift :
      oneHandleDirectRelatorShift oneHandleW6Mark E.factors 6 ∈
        zLayer H 6 := by
    rw [oneHandleDirectRelatorShift,
      evenRawStageShift_m (G := H) (by omega) (by omega) 1 6 (by omega)
        (fun i ↦ levelMk H 7 (oneHandleW6Mark i))
        (fun i ↦ levelMk H 7 (E.factors i)) hdepth]
    exact evenRawDbarWord_mem_zLayer 1 6 (by omega) _ _ hdepth
  have horig : levelMk H 7 (mRelWord 2 oneHandleW6Mark) ∈ zLayer H 6 :=
    ⟨mRelWord 2 oneHandleW6Mark, oneHandleW6Mark_mem.2.2.2.2, rfl⟩
  rw [oneHandleDirectRelatorShift_eq] at hshift
  change (levelMk H 7 (mRelWord 2 oneHandleW6Mark))⁻¹ *
      E.residual ∈ zLayer H 6 at hshift
  have hprod := Subgroup.mul_mem _ horig hshift
  have heq : levelMk H 7 (mRelWord 2 oneHandleW6Mark) *
      ((levelMk H 7 (mRelWord 2 oneHandleW6Mark))⁻¹ * E.residual) =
        E.residual := by group
  rwa [heq] at hprod

def oneHandleC7RelativeLayer : Subgroup (levelQuot H 7) :=
  zLayer H 6 ⊓ dmForgetHandlesLevelSeven.ker

theorem OneHandleC7RelativeLift.residual_mem_relativeLayer
    (E : OneHandleC7RelativeLift) : E.residual ∈ oneHandleC7RelativeLayer :=
  ⟨E.residual_mem_zLayer, E.residual_mem_ker⟩

theorem oneHandleW6Correctable_of_relativeResidual_eq_one
    (E : OneHandleC7RelativeLift) (hE : E.residual = 1) :
    OneHandleW6Correctable := by
  refine ⟨{
    factors := E.factors
    depth := E.depth
    handleU := E.handleU
    handleV := E.handleV
    chi := E.chi
    row := E.row
    kills := ?_ }⟩
  rw [oneHandleDirectRelatorShift_eq]
  change (levelMk H 7 (mRelWord 2 oneHandleW6Mark))⁻¹ * E.residual = _
  rw [hE, mul_one]

theorem exists_relativeLift_residual_eq_one_of_oneHandleW6Correctable
    (h : OneHandleW6Correctable) :
    ∃ E : OneHandleC7RelativeLift, E.residual = 1 := by
  let D := h.some
  let E : OneHandleC7RelativeLift := {
    factors := D.factors
    compactFactors := fun i ↦ dmForgetHandles 2 1 (D.factors i)
    depth := D.depth
    handleU := D.handleU
    handleV := D.handleV
    chi := D.chi
    row := D.row
    forget := fun _ ↦ rfl
    compactRelator := by
      have hdeep := D.kills_relator
      have himage := map_twoCentralSeries_le
        (dmForgetHandles 2 1).toMonoidHom
        (dmForgetHandles 2 1).continuous_toFun 7 ⟨_, hdeep, rfl⟩
      rw [map_mRelWord] at himage
      have hfun : (fun i ↦ (dmForgetHandles 2 1).toMonoidHom
          (oneHandleDirectModify oneHandleW6Mark D.factors i)) =
          fun i ↦ compactC6Mark i *
            dmForgetHandles 2 1 (D.factors i) := by
        funext i
        rw [oneHandleDirectModify, map_mul]
        change dmForgetHandles 2 1 (oneHandleW6Mark i) *
            dmForgetHandles 2 1 (D.factors i) = _
        rw [dmForgetHandles_oneHandleW6Mark]
      rwa [hfun] at himage }
  refine ⟨E, ?_⟩
  apply (lim_mem_twoCentralSeries_iff_levelMk 7 _).mp
  exact D.kills_relator

theorem oneHandleW6Correctable_iff_relativeResidual :
    OneHandleW6Correctable ↔
      ∃ E : OneHandleC7RelativeLift, E.residual = 1 := by
  constructor
  · exact exists_relativeLift_residual_eq_one_of_oneHandleW6Correctable
  · rintro ⟨E, hE⟩
    exact oneHandleW6Correctable_of_relativeResidual_eq_one E hE

#print axioms exists_oneHandleC7RelativeLift
#print axioms OneHandleC7RelativeLift.residual_mem_relativeLayer
#print axioms oneHandleW6Correctable_of_relativeResidual_eq_one
#print axioms oneHandleW6Correctable_iff_relativeResidual

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
