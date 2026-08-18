/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSixCompactLift

/-!
# The one-handle class-six correction

This module closes the relative residual isolated by
`MpcOneHandleClassSixCompactLift`.  The weighted certificate is first evaluated in the
one-handle depth-six quotient.  Its residual is cancelled by three explicit relator words:
two copies of `relationXWord` and one copy of `relationYWord`.

The cancellation is not inferred from an external computation.  The universal 65-row
trace in `MpcC6WeightedTraceFinal` proves the certificate times the displayed relation
product is one in every deep model, without using a relator rule.  This module proves that
the explicit correction factors have exactly that relation product as their stage shift.
They retain depth four, cyclotomic neutrality, the distinguished row, and both handle
letters.  The resulting `OneHandleDirectCorrection` advances the explicit one-handle
marking from class five to class six.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSixCorrection

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad
open GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcSx
open GQ2.Dyadic.Instances.MpcMk
open GQ2.Dyadic.Instances.MpcMkC6
open GQ2.Dyadic.Instances.MpcC6WeightedChecker
open GQ2.Dyadic.Instances.MpcC6WeightedChecker.CWord
open GQ2.Dyadic.Instances.MpcC6WeightedCertificate
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleClassFourSeed
open GQ2.Dyadic.Instances.MpcOneHandleClassFiveSeed
open GQ2.Dyadic.Instances.MpcOneHandleClassSixCompactLift
open GQ2.Roe.Labute

private abbrev H := DM 2 1
private abbrev A : H := dmA 2 1
private abbrev B : H := dmB 2 1
private abbrev C : H := dmC 2 1
private abbrev D : H := dmD 2 1

def oneHandleVal : Gen4 → H
  | .A => A
  | .B => B
  | .C => C
  | .D => D

noncomputable def oneHandleDeepModel : DeepModel (levelQuot H 6) where
  val := fun g ↦ levelMk H 6 (oneHandleVal g)
  deep := by
    intro w hw
    rw [eval_map (levelMk H 6) oneHandleVal w]
    apply (lim_mem_twoCentralSeries_iff_levelMk (G := H) 6 _).mp
    exact twoCentralSeries_antitone (G := H) hw
      (eval_mem_twoCentralSeries oneHandleVal w)

theorem eval_closedDefect_oneHandle :
    eval oneHandleDeepModel.val Bridge.closedDefect =
      MpcOneHandleClassSixTarget.oneHandleW6ClosedDefect := by
  simp only [Bridge.closedDefect, Bridge.sxE1, Bridge.sxE2, Bridge.sxE3,
    Bridge.sxE4, eval, oneHandleDeepModel, oneHandleVal,
    MpcOneHandleClassSixTarget.oneHandleW6ClosedDefect,
    MpcOneHandleClassSixTarget.oneHandleSxA,
    MpcOneHandleClassSixTarget.oneHandleSxB,
    MpcOneHandleClassSixTarget.oneHandleSxC,
    MpcOneHandleClassSixTarget.oneHandleSxD,
    MpcOneHandleClassSixTarget.oneHandleSxW,
    MpcOneHandleClassSixTarget.oneHandleSxZ,
    MpcOneHandleClassSixTarget.oneHandleSxN,
    mpcSxE1, mpcSxE2, mpcSxE3, mpcSxE4]
  congr 1

theorem eval_certificate_closed_part :
    eval oneHandleDeepModel.val Bridge.closedDefect =
      levelMk H 6 (mRelWord 2 MpcOneHandleClassSixTarget.oneHandleW5Mark) := by
  rw [eval_closedDefect_oneHandle,
    ← MpcOneHandleClassSixTarget.oneHandleW5Mark_defect_six]

private abbrev qA : levelQuot H 6 := levelMk H 6 A
private abbrev qB : levelQuot H 6 := levelMk H 6 B
private abbrev qC : levelQuot H 6 := levelMk H 6 C
private abbrev qD : levelQuot H 6 := levelMk H 6 D

private abbrev qUs : levelQuot H 6 := levelMk H 6 oneHandleC6Us
private abbrev qUt : levelQuot H 6 := levelMk H 6 oneHandleC6Ut
private abbrev qUm : levelQuot H 6 := levelMk H 6 oneHandleC6Um
private abbrev qUn : levelQuot H 6 := levelMk H 6 oneHandleC6Un

private theorem eval_mkUs_oneHandle :
    eval oneHandleDeepModel.val Bridge.mkUs = qUs := by
  rw [show oneHandleDeepModel.val = fun g ↦ levelMk H 6 (oneHandleVal g) from rfl,
    eval_map]
  apply congrArg (levelMk H 6)
  simp only [Bridge.mkUs, eval, oneHandleVal, oneHandleC6Us]

private theorem eval_mkUt_oneHandle :
    eval oneHandleDeepModel.val Bridge.mkUt = qUt := by
  rw [show oneHandleDeepModel.val = fun g ↦ levelMk H 6 (oneHandleVal g) from rfl,
    eval_map]
  apply congrArg (levelMk H 6)
  simp only [Bridge.mkUt, eval, oneHandleVal, oneHandleC6Ut]
  norm_num [← pow_mul]

private theorem eval_mkUm_oneHandle :
    eval oneHandleDeepModel.val Bridge.mkUm = qUm := by
  rw [show oneHandleDeepModel.val = fun g ↦ levelMk H 6 (oneHandleVal g) from rfl,
    eval_map]
  rfl

private theorem eval_mkUn_oneHandle :
    eval oneHandleDeepModel.val Bridge.mkUn = qUn := by
  rw [show oneHandleDeepModel.val = fun g ↦ levelMk H 6 (oneHandleVal g) from rfl,
    eval_map]
  apply congrArg (levelMk H 6)
  simp only [Bridge.mkUn, eval, oneHandleVal, oneHandleC6Un]
  norm_num [← pow_mul]

def oneHandleSparseIncrement : levelQuot H 6 :=
  qUs ^ 2 * commP qUs qA *
    commP qUs (qB * (commP qD qB * qB ^ 4)) *
    commP qUm (qD * (qB ^ 4 * commP (qB ^ 2) qD)) *
    commP qA qUt * commP qC qUn

theorem eval_sparseIncrement_oneHandle :
    eval oneHandleDeepModel.val Bridge.sparseIncrement =
      oneHandleSparseIncrement := by
  rw [Bridge.eval_sparseIncrement_shape, eval_mkUs_oneHandle,
    eval_mkUt_oneHandle, eval_mkUm_oneHandle, eval_mkUn_oneHandle]
  rfl

private def baseQ : Fin (coreRank 1) → levelQuot H 6 :=
  fun i ↦ levelMk H 6 (MpcOneHandleClassSixTarget.oneHandleW5Mark i)

private def compactFactorsQ : Fin (coreRank 1) → levelQuot H 6 :=
  fun i ↦ levelMk H 6 (oneHandleC6Factors i)

private theorem baseQ_zero :
    baseQ 0 = qA * (qB ^ 4)⁻¹ * commP qD qB := by
  simp [baseQ, MpcOneHandleClassSixTarget.oneHandleW5Mark,
    oneHandleDirectModify, oneHandleW4Mark, oneHandleW5Factors,
    oneHandleW4, map_mul, map_inv, map_pow, Marking.map_commP]

private theorem baseQ_one :
    baseQ 1 = qB * (commP qD qB * qB ^ 4) := by
  simp [baseQ, MpcOneHandleClassSixTarget.oneHandleW5Mark,
    oneHandleDirectModify, oneHandleW4Mark, oneHandleW5Factors,
    oneHandleW5Ut, oneHandleW4, map_mul, map_pow, Marking.map_commP]
  group

private theorem baseQ_two : baseQ 2 = qB ^ 2 * qC := by
  simp [baseQ, MpcOneHandleClassSixTarget.oneHandleW5Mark,
    oneHandleDirectModify, oneHandleW4Mark, oneHandleW5Factors,
    map_mul, map_pow]

private theorem baseQ_three :
    baseQ 3 = qD * (qB ^ 4 * commP (qB ^ 2) qD) := by
  simp [baseQ, MpcOneHandleClassSixTarget.oneHandleW5Mark,
    oneHandleDirectModify, oneHandleW4Mark, oneHandleW5Factors,
    oneHandleW5Un, map_mul, map_pow, Marking.map_commP]

private theorem compactFactorsQ_zero : compactFactorsQ 0 = qUs := by
  simp [compactFactorsQ, oneHandleC6Factors]

private theorem compactFactorsQ_one : compactFactorsQ 1 = qUt := by
  simp [compactFactorsQ, oneHandleC6Factors]

private theorem compactFactorsQ_two : compactFactorsQ 2 = qUm := by
  simp [compactFactorsQ, oneHandleC6Factors]

private theorem compactFactorsQ_three : compactFactorsQ 3 = qUn := by
  simp [compactFactorsQ, oneHandleC6Factors]

private theorem compactFactorsQ_handleU (j : Fin 1) :
    compactFactorsQ (handleIdxU j) = 1 := by
  simp [compactFactorsQ, oneHandleC6Factors]

private theorem compactFactorsQ_handleV (j : Fin 1) :
    compactFactorsQ (handleIdxV j) = 1 := by
  simp [compactFactorsQ, oneHandleC6Factors]

private theorem commP_drop_right_of_four
    {m x y : levelQuot H 6} (hm : m ∈ lambdaImage H 4 6)
    (hy : y ∈ lambdaImage H 2 6) : commP m (x * y) = commP m x := by
  rw [cfour_commP_mul_right, mpcSx_vanish_four hm hy,
    mpcSx_commP_zLayer_left (mpcSx_commP_step hm x) y, one_mul, mul_one]

private theorem commP_drop_left_right_of_four
    {m x y : levelQuot H 6} (hm : m ∈ lambdaImage H 4 6)
    (hy : y ∈ lambdaImage H 2 6) : commP m (y * x) = commP m x := by
  rw [cfour_commP_mul_right, mpcSx_vanish_four hm hy,
    cfour_one_comm, mul_one, mul_one]

private theorem commP_swap_of_four
    {m x : levelQuot H 6} (hm : m ∈ lambdaImage H 4 6) :
    commP x m = commP m x := by
  rw [mpcSx_swap, zLayer_inv_self (mpcSx_commP_step hm x)]

private theorem regroup_six {Q : Type*} [Group Q]
    (z0 z1 z2 z3 z4 z5 : Q)
    (hz2 : ∀ x, z2 * x = x * z2) (hz4 : ∀ x, z4 * x = x * z4) :
    z0 * z1 * (z2 * z3) * (z4 * z5) =
      z0 * z1 * z3 * z5 * z2 * z4 := by
  calc
    _ = z0 * z1 * (z3 * z2) * (z4 * z5) := by rw [hz2 z3]
    _ = z0 * z1 * z3 * (z2 * (z4 * z5)) := by group
    _ = z0 * z1 * z3 * ((z4 * z5) * z2) := by rw [hz2 (z4 * z5)]
    _ = z0 * z1 * z3 * (z4 * z5) * z2 := by group
    _ = z0 * z1 * z3 * (z5 * z4) * z2 := by rw [hz4 z5]
    _ = z0 * z1 * z3 * z5 * (z4 * z2) := by group
    _ = z0 * z1 * z3 * z5 * (z2 * z4) := by rw [hz4 z2]
    _ = z0 * z1 * z3 * z5 * z2 * z4 := by group

theorem evenRawDbarWord_compactFactorsQ :
    evenRawDbarWord baseQ compactFactorsQ = oneHandleSparseIncrement := by
  have hUs : qUs ∈ lambdaImage H 4 6 := ⟨oneHandleC6Us,
    oneHandleC6Us_mem, rfl⟩
  have hUt : qUt ∈ lambdaImage H 4 6 := ⟨oneHandleC6Ut,
    oneHandleC6Ut_mem, rfl⟩
  have hUm : qUm ∈ lambdaImage H 4 6 := ⟨oneHandleC6Um,
    oneHandleC6Um_mem, rfl⟩
  have hUn : qUn ∈ lambdaImage H 4 6 := ⟨oneHandleC6Un,
    oneHandleC6Un_mem, rfl⟩
  have hB4 : qB ^ 4 ∈ lambdaImage H 2 6 :=
    mpcSx_lam_le (by omega) (mpcSx_pow_four_mem qB)
  have hW : commP qD qB ∈ lambdaImage H 2 6 :=
    mpcSx_commP_mem_two qD qB
  have hB2 : qB ^ 2 ∈ lambdaImage H 2 6 := mpcSx_pow_two_mem qB
  have hUsA : commP qUs qA ∈ zLayer H 5 := mpcSx_commP_step hUs qA
  have hUtA : commP qUt qA ∈ zLayer H 5 := mpcSx_commP_step hUt qA
  have hUnC : commP qUn qC ∈ zLayer H 5 := mpcSx_commP_step hUn qC
  have hAUt : commP qA qUt ∈ zLayer H 5 := mpcSx_commP_step' qA hUt
  have hCUn : commP qC qUn ∈ zLayer H 5 := mpcSx_commP_step' qC hUn
  rw [evenRawDbarWord, evenRawCoreDbarWord, evenRawHandleDbarWord,
    show List.finRange 1 = [0] by decide, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil,
    compactFactorsQ_zero, compactFactorsQ_one, compactFactorsQ_two,
    compactFactorsQ_three, compactFactorsQ_handleU, compactFactorsQ_handleV,
    baseQ_zero, baseQ_one, baseQ_two, baseQ_three]
  simp only [cfour_one_comm, mul_one]
  rw [show commP qUs (qA * (qB ^ 4)⁻¹ * commP qD qB) = commP qUs qA by
    rw [commP_drop_right_of_four hUs hW,
      commP_drop_right_of_four hUs (Subgroup.inv_mem _ hB4)],
    show commP qUt (qA * (qB ^ 4)⁻¹ * commP qD qB) = commP qUt qA by
      rw [commP_drop_right_of_four hUt hW,
        commP_drop_right_of_four hUt (Subgroup.inv_mem _ hB4)],
    show commP qUn (qB ^ 2 * qC) = commP qUn qC by
      rw [commP_drop_left_right_of_four hUn hB2],
    (commP_swap_of_four hUt).symm, (commP_swap_of_four hUn).symm]
  exact regroup_six _ _ _ _ _ _ (fun x ↦ (zLayer_commute hAUt x).eq)
    (fun x ↦ (zLayer_commute hCUn x).eq)

theorem compactRelatorShift_eq_sparseIncrement :
    oneHandleDirectRelatorShift
        MpcOneHandleClassSixTarget.oneHandleW5Mark oneHandleC6Factors 5 =
      oneHandleSparseIncrement := by
  have hdepth : ∀ i,
      levelMk H 6 (oneHandleC6Factors i) ∈ lambdaImage H 4 6 :=
    fun i ↦ ⟨oneHandleC6Factors i, oneHandleC6Factors_depth i, rfl⟩
  rw [oneHandleDirectRelatorShift,
    evenRawStageShift_m (G := H) (by omega) (by omega) 1 5 (by omega)
      (fun i ↦ levelMk H 6
        (MpcOneHandleClassSixTarget.oneHandleW5Mark i))
      (fun i ↦ levelMk H 6 (oneHandleC6Factors i)) hdepth]
  exact evenRawDbarWord_compactFactorsQ

theorem eval_certificateWord_eq_oneHandleC6Residual :
    eval oneHandleDeepModel.val Bridge.certificateWord = oneHandleC6Residual := by
  calc
    _ = eval oneHandleDeepModel.val Bridge.closedDefect *
        eval oneHandleDeepModel.val Bridge.sparseIncrement := rfl
    _ = levelMk H 6 (mRelWord 2 MpcOneHandleClassSixTarget.oneHandleW5Mark) *
        oneHandleSparseIncrement := by
      rw [eval_certificate_closed_part, eval_sparseIncrement_oneHandle]
    _ = levelMk H 6 (mRelWord 2 MpcOneHandleClassSixTarget.oneHandleW5Mark) *
        oneHandleDirectRelatorShift
          MpcOneHandleClassSixTarget.oneHandleW5Mark oneHandleC6Factors 5 := by
      rw [compactRelatorShift_eq_sparseIncrement]
    _ = oneHandleC6Residual := by
      rw [oneHandleDirectRelatorShift_eq]
      simp only [oneHandleC6Residual]
      group

def relationXWord : CWord :=
  .mul (.sq (.comm mRel (.gen .B)))
    (.comm (.comm mRel (.gen .D)) (.gen .B))

def relationYWord : CWord :=
  .mul (.sq (.comm mRel (.gen .B)))
    (.comm (.comm mRel (.gen .B)) (.gen .B))

def oneHandleRelationX : H := eval oneHandleVal relationXWord
def oneHandleRelationY : H := eval oneHandleVal relationYWord

def oneHandleRelationFactors : Fin (coreRank 1) → H :=
  fullMark oneHandleRelationX oneHandleRelationX oneHandleRelationY 1
    (fun _ ↦ 1) (fun _ ↦ 1)

private abbrev qR : levelQuot H 6 := eval oneHandleDeepModel.val mRel
private abbrev qK : levelQuot H 6 := commP qR qB
private abbrev qL : levelQuot H 6 := commP qR qD
private abbrev qLB : levelQuot H 6 := commP qL qB
private abbrev qKB : levelQuot H 6 := commP qK qB
private abbrev qKD : levelQuot H 6 := commP qK qD
private abbrev qX : levelQuot H 6 := qK ^ 2 * qLB
private abbrev qY : levelQuot H 6 := qK ^ 2 * qKB

private theorem levelMk_relationX : levelMk H 6 oneHandleRelationX = qX := by
  change levelMk H 6 (eval oneHandleVal relationXWord) =
    eval (fun g ↦ levelMk H 6 (oneHandleVal g)) relationXWord
  exact (eval_map (levelMk H 6) oneHandleVal relationXWord).symm

private theorem levelMk_relationY : levelMk H 6 oneHandleRelationY = qY := by
  change levelMk H 6 (eval oneHandleVal relationYWord) =
    eval (fun g ↦ levelMk H 6 (oneHandleVal g)) relationYWord
  exact (eval_map (levelMk H 6) oneHandleVal relationYWord).symm

theorem relationXWord_depth : relationXWord.depth = 4 := by decide
theorem relationYWord_depth : relationYWord.depth = 4 := by decide

theorem oneHandleRelationX_mem :
    oneHandleRelationX ∈ twoCentralSeries H 4 := by
  simpa only [oneHandleRelationX, ← relationXWord_depth] using
    eval_mem_twoCentralSeries oneHandleVal relationXWord

theorem oneHandleRelationY_mem :
    oneHandleRelationY ∈ twoCentralSeries H 4 := by
  simpa only [oneHandleRelationY, ← relationYWord_depth] using
    eval_mem_twoCentralSeries oneHandleVal relationYWord

theorem oneHandleRelationFactors_depth (i : Fin (coreRank 1)) :
    oneHandleRelationFactors i ∈ twoCentralSeries H 4 := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simpa [oneHandleRelationFactors] using oneHandleRelationX_mem
  · simpa [oneHandleRelationFactors] using oneHandleRelationX_mem
  · simpa [oneHandleRelationFactors] using oneHandleRelationY_mem
  · simp [oneHandleRelationFactors]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleRelationFactors, mHandleIdx_coordU, mHandleIdx_coordV]

private def relationFactorsQ : Fin (coreRank 1) → levelQuot H 6 :=
  fun i ↦ levelMk H 6 (oneHandleRelationFactors i)

private theorem relationFactorsQ_zero : relationFactorsQ 0 = qX := by
  simp [relationFactorsQ, oneHandleRelationFactors, levelMk_relationX]

private theorem relationFactorsQ_one : relationFactorsQ 1 = qX := by
  simp [relationFactorsQ, oneHandleRelationFactors, levelMk_relationX]

private theorem relationFactorsQ_two : relationFactorsQ 2 = qY := by
  simp [relationFactorsQ, oneHandleRelationFactors, levelMk_relationY]

private theorem relationFactorsQ_three : relationFactorsQ 3 = 1 := by
  simp [relationFactorsQ, oneHandleRelationFactors]

private theorem relationFactorsQ_handleU (j : Fin 1) :
    relationFactorsQ (handleIdxU j) = 1 := by
  simp [relationFactorsQ, oneHandleRelationFactors]

private theorem relationFactorsQ_handleV (j : Fin 1) :
    relationFactorsQ (handleIdxV j) = 1 := by
  simp [relationFactorsQ, oneHandleRelationFactors]

def oneHandleRelationShift : levelQuot H 6 :=
  qX ^ 2 * commP qX qB * commP qY qD

private theorem qR_mem : qR ∈ lambdaImage H 2 6 := by
  refine ⟨eval oneHandleVal mRel, ?_, ?_⟩
  · change eval oneHandleVal mRel ∈ twoCentralSeries H 2
    simpa only [show mRel.depth = 2 by decide] using
      (eval_mem_twoCentralSeries oneHandleVal mRel)
  · exact (eval_map (levelMk H 6) oneHandleVal mRel).symm

private theorem qK_mem : qK ∈ lambdaImage H 3 6 :=
  mpcSx_commP_step qR_mem qB

private theorem qL_mem : qL ∈ lambdaImage H 3 6 :=
  mpcSx_commP_step qR_mem qD

private theorem qK_sq_mem : qK ^ 2 ∈ lambdaImage H 4 6 :=
  mpcSx_sq_step qK_mem

private theorem qLB_mem : qLB ∈ lambdaImage H 4 6 :=
  mpcSx_commP_step qL_mem qB

private theorem qKB_mem : qKB ∈ lambdaImage H 4 6 :=
  mpcSx_commP_step qK_mem qB

private theorem qKD_mem : qKD ∈ lambdaImage H 4 6 :=
  mpcSx_commP_step qK_mem qD

private theorem qX_mem : qX ∈ lambdaImage H 4 6 :=
  Subgroup.mul_mem _ qK_sq_mem qLB_mem

private theorem qY_mem : qY ∈ lambdaImage H 4 6 :=
  Subgroup.mul_mem _ qK_sq_mem qKB_mem

private theorem cancel_double_top {z0 a b c : levelQuot H 6}
    (ha : a ∈ zLayer H 5) : z0 * a * (a * b) * c = z0 * b * c := by
  have haa : a * a = 1 := by
    rw [← pow_two]
    exact zLayer_sq _ ha
  rw [show z0 * a * (a * b) * c = z0 * (a * a) * b * c by group,
    haa, mul_one]

theorem evenRawDbarWord_relationFactorsQ :
    evenRawDbarWord baseQ relationFactorsQ = oneHandleRelationShift := by
  have htailB : commP qD qB * qB ^ 4 ∈ lambdaImage H 2 6 :=
    Subgroup.mul_mem _ (mpcSx_commP_mem_two qD qB)
      (mpcSx_lam_le (by omega) (mpcSx_pow_four_mem qB))
  have htailD : qB ^ 4 * commP (qB ^ 2) qD ∈ lambdaImage H 2 6 :=
    Subgroup.mul_mem _ (mpcSx_lam_le (by omega) (mpcSx_pow_four_mem qB))
      (mpcSx_commP_mem_two (qB ^ 2) qD)
  have hhead : commP qX (baseQ 0) ∈ zLayer H 5 :=
    mpcSx_commP_step qX_mem (baseQ 0)
  rw [evenRawDbarWord, evenRawCoreDbarWord, evenRawHandleDbarWord,
    show List.finRange 1 = [0] by decide, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, relationFactorsQ_zero,
    relationFactorsQ_one, relationFactorsQ_two, relationFactorsQ_three,
    relationFactorsQ_handleU, relationFactorsQ_handleV,
    cfour_one_comm, one_mul, mul_one, baseQ_one, baseQ_three,
    commP_drop_right_of_four qX_mem htailB,
    commP_drop_right_of_four qY_mem htailD]
  have hhandle :
      commP (1 : levelQuot H 6) (baseQ (handleIdxU (0 : Fin 1))) *
          commP 1 (baseQ (handleIdxV (0 : Fin 1))) = 1 := by
    simp [commP]
  rw [hhandle, mul_one]
  rw [oneHandleRelationShift]
  apply cancel_double_top
  exact hhead

private theorem qX_sq : qX ^ 2 = qK ^ 4 * qLB ^ 2 := by
  change (qK ^ 2 * qLB) ^ 2 = qK ^ 4 * qLB ^ 2
  rw [cfour_sq_mul, mpcSx_vanish_four qLB_mem
      (mpcSx_lam_le (by omega) qK_sq_mem),
    cfour_one_comm, mul_one, mul_one]
  norm_num [← pow_mul]

private theorem commP_qX_B :
    commP qX qB = qKB ^ 2 * commP qLB qB := by
  change commP (qK ^ 2 * qLB) qB = _
  have hK2 : qK ∈ lambdaImage H 2 6 := mpcSx_lam_le (by omega) qK_mem
  rw [mpcSx_commP_add_left_four qK_sq_mem qLB qB, pow_two,
    mpcSx_commP_add_left_three qK_mem hK2 qB, ← pow_two]

private theorem commP_qY_D :
    commP qY qD = qKD ^ 2 * commP qKB qD := by
  change commP (qK ^ 2 * qKB) qD = _
  have hK2 : qK ∈ lambdaImage H 2 6 := mpcSx_lam_le (by omega) qK_mem
  rw [mpcSx_commP_add_left_four qK_sq_mem qKB qD, pow_two,
    mpcSx_commP_add_left_three qK_mem hK2 qD, ← pow_two]

private theorem regroup_relation_factors :
    qK ^ 4 * qLB ^ 2 * (qKB ^ 2 * commP qLB qB) *
        (qKD ^ 2 * commP qKB qD) =
      qK ^ 4 * qKB ^ 2 * qLB ^ 2 * qKD ^ 2 *
        commP qLB qB * commP qKB qD := by
  have hLB2 : qLB ^ 2 ∈ zLayer H 5 := mpcSx_sq_step qLB_mem
  have hLBB : commP qLB qB ∈ zLayer H 5 := mpcSx_commP_step qLB_mem qB
  calc
    _ = qK ^ 4 * (qLB ^ 2 * qKB ^ 2) * commP qLB qB *
        (qKD ^ 2 * commP qKB qD) := by group
    _ = qK ^ 4 * (qKB ^ 2 * qLB ^ 2) * commP qLB qB *
        (qKD ^ 2 * commP qKB qD) := by
      rw [(zLayer_commute hLB2 (qKB ^ 2)).eq]
    _ = qK ^ 4 * qKB ^ 2 * qLB ^ 2 * commP qLB qB *
        (qKD ^ 2 * commP qKB qD) := by
      group
    _ = qK ^ 4 * qKB ^ 2 * qLB ^ 2 *
        (commP qLB qB * qKD ^ 2) * commP qKB qD := by group
    _ = qK ^ 4 * qKB ^ 2 * qLB ^ 2 *
        (qKD ^ 2 * commP qLB qB) * commP qKB qD := by
      rw [(zLayer_commute hLBB (qKD ^ 2)).eq]
    _ = qK ^ 4 * qKB ^ 2 * qLB ^ 2 * qKD ^ 2 *
        commP qLB qB * commP qKB qD := by
      group

theorem oneHandleRelationShift_eq_eval_relationProduct :
    oneHandleRelationShift =
      eval oneHandleDeepModel.val
        MpcC6WeightedRelationSupport.relationProduct := by
  rw [oneHandleRelationShift, qX_sq, commP_qX_B, commP_qY_D,
    regroup_relation_factors,
    MpcC6WeightedRelationSupport.eval_relationProduct_shape]
  rfl

theorem relationRelatorShift_eq_eval_relationProduct :
    oneHandleDirectRelatorShift
        MpcOneHandleClassSixTarget.oneHandleW5Mark oneHandleRelationFactors 5 =
      eval oneHandleDeepModel.val
        MpcC6WeightedRelationSupport.relationProduct := by
  have hdepth : ∀ i,
      levelMk H 6 (oneHandleRelationFactors i) ∈ lambdaImage H 4 6 :=
    fun i ↦ ⟨oneHandleRelationFactors i,
      oneHandleRelationFactors_depth i, rfl⟩
  rw [oneHandleDirectRelatorShift,
    evenRawStageShift_m (G := H) (by omega) (by omega) 1 5 (by omega)
      (fun i ↦ levelMk H 6
        (MpcOneHandleClassSixTarget.oneHandleW5Mark i))
      (fun i ↦ levelMk H 6 (oneHandleRelationFactors i)) hdepth]
  change evenRawDbarWord baseQ relationFactorsQ = _
  rw [evenRawDbarWord_relationFactorsQ,
    oneHandleRelationShift_eq_eval_relationProduct]

def oneHandleC6CorrectedFactors : Fin (coreRank 1) → H :=
  fun i ↦ oneHandleC6Factors i * oneHandleRelationFactors i

theorem oneHandleC6CorrectedFactors_depth (i : Fin (coreRank 1)) :
    oneHandleC6CorrectedFactors i ∈ twoCentralSeries H 4 :=
  Subgroup.mul_mem _ (oneHandleC6Factors_depth i)
    (oneHandleRelationFactors_depth i)

private theorem relationX_chi : chiM 2 1 oneHandleRelationX = 1 := by
  have hK := map_commP_eq_one (chiM 2 1).toMonoidHom
    (eval oneHandleVal mRel) (oneHandleVal .B)
  have hLB := map_commP_eq_one (chiM 2 1).toMonoidHom
    (commP (eval oneHandleVal mRel) (oneHandleVal .D))
    (oneHandleVal .B)
  simp only [oneHandleRelationX, relationXWord, eval, map_mul, map_pow]
  change (chiM 2 1).toMonoidHom
      (commP (eval oneHandleVal mRel) (oneHandleVal .B)) ^ 2 *
      (chiM 2 1).toMonoidHom
        (commP (commP (eval oneHandleVal mRel) (oneHandleVal .D))
          (oneHandleVal .B)) = 1
  rw [hK, hLB, one_pow, one_mul]

private theorem relationY_chi : chiM 2 1 oneHandleRelationY = 1 := by
  have hK := map_commP_eq_one (chiM 2 1).toMonoidHom
    (eval oneHandleVal mRel) (oneHandleVal .B)
  have hKB := map_commP_eq_one (chiM 2 1).toMonoidHom
    (commP (eval oneHandleVal mRel) (oneHandleVal .B))
    (oneHandleVal .B)
  simp only [oneHandleRelationY, relationYWord, eval, map_mul, map_pow]
  change (chiM 2 1).toMonoidHom
      (commP (eval oneHandleVal mRel) (oneHandleVal .B)) ^ 2 *
      (chiM 2 1).toMonoidHom
        (commP (commP (eval oneHandleVal mRel) (oneHandleVal .B))
          (oneHandleVal .B)) = 1
  rw [hK, hKB, one_pow, one_mul]

theorem oneHandleRelationFactors_chi (i : Fin (coreRank 1)) :
    chiM 2 1 (oneHandleRelationFactors i) = 1 := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simpa [oneHandleRelationFactors] using relationX_chi
  · simpa [oneHandleRelationFactors] using relationX_chi
  · simpa [oneHandleRelationFactors] using relationY_chi
  · simp [oneHandleRelationFactors]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleRelationFactors, mHandleIdx_coordU, mHandleIdx_coordV]

theorem oneHandleC6CorrectedFactors_chi (i : Fin (coreRank 1)) :
    chiM 2 1 (oneHandleC6CorrectedFactors i) = 1 := by
  rw [oneHandleC6CorrectedFactors, map_mul, oneHandleC6Factors_chi,
    oneHandleRelationFactors_chi, one_mul]

private theorem relationY_map_one
    (f : ContinuousMonoidHom H (Multiplicative ℤ_[2])) :
    f oneHandleRelationY = 1 := by
  have hK := map_commP_eq_one f.toMonoidHom
    (eval oneHandleVal mRel) (oneHandleVal .B)
  have hKB := map_commP_eq_one f.toMonoidHom
    (commP (eval oneHandleVal mRel) (oneHandleVal .B))
    (oneHandleVal .B)
  simp only [oneHandleRelationY, relationYWord, eval, map_mul, map_pow]
  change f.toMonoidHom
      (commP (eval oneHandleVal mRel) (oneHandleVal .B)) ^ 2 *
      f.toMonoidHom
        (commP (commP (eval oneHandleVal mRel) (oneHandleVal .B))
          (oneHandleVal .B)) = 1
  rw [hK, hKB, one_pow, one_mul]

theorem oneHandleC6CorrectedFactors_row
    (f : ContinuousMonoidHom H (Multiplicative ℤ_[2])) :
    toAdd (f (oneHandleC6CorrectedFactors 2)) = 0 := by
  change toAdd (f (oneHandleC6Factors 2 * oneHandleRelationY)) = 0
  rw [map_mul, relationY_map_one f, mul_one]
  exact oneHandleC6Factors_row f

private def correctedFactorsQ : Fin (coreRank 1) → levelQuot H 6 :=
  fun i ↦ levelMk H 6 (oneHandleC6CorrectedFactors i)

private theorem correctedFactorsQ_eq (i : Fin (coreRank 1)) :
    correctedFactorsQ i = compactFactorsQ i * relationFactorsQ i := by
  rw [correctedFactorsQ, oneHandleC6CorrectedFactors, map_mul]
  rfl

theorem correctedRelatorShift_eq_product :
    oneHandleDirectRelatorShift
        MpcOneHandleClassSixTarget.oneHandleW5Mark
        oneHandleC6CorrectedFactors 5 =
      oneHandleSparseIncrement *
        eval oneHandleDeepModel.val
          MpcC6WeightedRelationSupport.relationProduct := by
  have hcDepth : ∀ i, compactFactorsQ i ∈ lambdaImage H 4 6 :=
    fun i ↦ ⟨oneHandleC6Factors i, oneHandleC6Factors_depth i, rfl⟩
  have hrDepth : ∀ i, relationFactorsQ i ∈ lambdaImage H 4 6 :=
    fun i ↦ ⟨oneHandleRelationFactors i,
      oneHandleRelationFactors_depth i, rfl⟩
  have hDepth : ∀ i, correctedFactorsQ i ∈ lambdaImage H 4 6 :=
    fun i ↦ ⟨oneHandleC6CorrectedFactors i,
      oneHandleC6CorrectedFactors_depth i, rfl⟩
  rw [oneHandleDirectRelatorShift,
    evenRawStageShift_m (G := H) (by omega) (by omega) 1 5 (by omega)
      (fun i ↦ levelMk H 6
        (MpcOneHandleClassSixTarget.oneHandleW5Mark i))
      (fun i ↦ levelMk H 6 (oneHandleC6CorrectedFactors i)) hDepth]
  change evenRawDbarWord baseQ correctedFactorsQ = _
  have hpoint : correctedFactorsQ =
      fun i ↦ compactFactorsQ i * relationFactorsQ i := by
    funext i
    exact correctedFactorsQ_eq i
  rw [hpoint, evenRawDbarWord_mul 1 5 (by omega) baseQ hcDepth hrDepth,
    evenRawDbarWord_compactFactorsQ, evenRawDbarWord_relationFactorsQ,
    oneHandleRelationShift_eq_eval_relationProduct]

theorem oneHandleResidual_mul_relationProduct_eq_one :
    oneHandleC6Residual *
        eval oneHandleDeepModel.val
          MpcC6WeightedRelationSupport.relationProduct = 1 := by
  rw [← eval_certificateWord_eq_oneHandleC6Residual]
  exact MpcC6WeightedTraceFinal.eval_certificateWord_mul_relationProduct_eq_one_noRel
    oneHandleDeepModel

theorem correctedRelatorShift_kills :
    oneHandleDirectRelatorShift
        MpcOneHandleClassSixTarget.oneHandleW5Mark
        oneHandleC6CorrectedFactors 5 =
      (levelMk H 6
        (mRelWord 2 MpcOneHandleClassSixTarget.oneHandleW5Mark))⁻¹ := by
  have hres : levelMk H 6
        (mRelWord 2 MpcOneHandleClassSixTarget.oneHandleW5Mark) *
      oneHandleSparseIncrement = oneHandleC6Residual := by
    rw [← compactRelatorShift_eq_sparseIncrement]
    rw [oneHandleDirectRelatorShift_eq]
    simp only [oneHandleC6Residual]
    group
  apply eq_inv_of_mul_eq_one_right
  rw [correctedRelatorShift_eq_product, ← mul_assoc, hres,
    oneHandleResidual_mul_relationProduct_eq_one]

def oneHandleW5ClassSixCorrection :
    OneHandleDirectCorrection
      MpcOneHandleClassSixTarget.oneHandleW5Mark 5 where
  factors := oneHandleC6CorrectedFactors
  depth := oneHandleC6CorrectedFactors_depth
  handleU j := by
    simp [oneHandleC6CorrectedFactors, oneHandleC6Factors,
      oneHandleRelationFactors]
  handleV j := by
    simp [oneHandleC6CorrectedFactors, oneHandleC6Factors,
      oneHandleRelationFactors]
  chi := oneHandleC6CorrectedFactors_chi
  row := oneHandleC6CorrectedFactors_row
  kills := correctedRelatorShift_kills

theorem oneHandleW5Correctable :
    MpcOneHandleClassSixTarget.OneHandleW5Correctable :=
  ⟨oneHandleW5ClassSixCorrection⟩

theorem oneHandleDirectSet_six_nonempty : (oneHandleDirectSet 6).Nonempty :=
  MpcOneHandleClassSixTarget.oneHandleDirectSet_six_nonempty_of_W5Correctable
    oneHandleW5Correctable

#print axioms oneHandleC6CorrectedFactors_depth
#print axioms oneHandleC6CorrectedFactors_chi
#print axioms oneHandleC6CorrectedFactors_row
#print axioms oneHandleResidual_mul_relationProduct_eq_one
#print axioms correctedRelatorShift_kills
#print axioms oneHandleW5ClassSixCorrection
#print axioms oneHandleW5Correctable
#print axioms oneHandleDirectSet_six_nonempty

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSixCorrection
