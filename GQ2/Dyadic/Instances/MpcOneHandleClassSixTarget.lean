/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassFiveSeed
import GQ2.Dyadic.Instances.MpcSix

/-!
# The exact class-six target at one handle

This module evaluates the full six-letter relator of W264's explicit class-five marking in
`D_M(2,1) / lambda_6`.  The value is the same universal class-six expression `E1 E2 E3 E4 C1
C2` that governs the compact calculation, now evaluated on the one-handle generators.  The
unchanged handle commutator introduces no extra term: the W5 relator is already central at
depth five, so conjugating the closed expression through the handle block fixes it.

The inverse of this value is therefore the literal target of the four-coordinate correction
map.  Correctability of the named W5 marking is restated as finite range membership, equal
coordinate and augmented ranks, and the four scalar target-row coefficients.  No such
correction is asserted here; the result identifies the exact 5-to-6 finite target.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSixTarget

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcSx
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank
open GQ2.Dyadic.Instances.MpcOneHandleDirectRowCoefficients
open GQ2.Dyadic.Instances.MpcOneHandleClassFourSeed
open GQ2.Dyadic.Instances.MpcOneHandleClassFiveSeed
open GQ2.Roe.Labute

private abbrev H := DM 2 1

def oneHandleW5Mark : Fin (coreRank 1) → H :=
  oneHandleDirectModify oneHandleW4Mark oneHandleW5Factors

theorem oneHandleW5Mark_mem : oneHandleW5Mark ∈ oneHandleDirectSet 5 :=
  oneHandleW5Mark_mem_direct_five

def oneHandleSxA : levelQuot H 6 := levelMk H 6 (dmA 2 1)
def oneHandleSxB : levelQuot H 6 := levelMk H 6 (dmB 2 1)
def oneHandleSxC : levelQuot H 6 := levelMk H 6 (dmC 2 1)
def oneHandleSxD : levelQuot H 6 := levelMk H 6 (dmD 2 1)
def oneHandleSxZ : levelQuot H 6 := (oneHandleSxB ^ 4)⁻¹
def oneHandleSxW : levelQuot H 6 := commP oneHandleSxD oneHandleSxB
def oneHandleSxN : levelQuot H 6 :=
  oneHandleSxB ^ 4 * commP (oneHandleSxB ^ 2) oneHandleSxD

def oneHandleW6ClosedDefect : levelQuot H 6 :=
  mpcSxE1 oneHandleSxA oneHandleSxW oneHandleSxZ *
    mpcSxE2 oneHandleSxA oneHandleSxB oneHandleSxW
      (oneHandleSxW * oneHandleSxB ^ 4) oneHandleSxZ *
    mpcSxE3 oneHandleSxB oneHandleSxC *
    mpcSxE4 oneHandleSxB oneHandleSxC oneHandleSxD oneHandleSxN *
    (commP (mpcSxE1 oneHandleSxA oneHandleSxW oneHandleSxZ)
        (commP oneHandleSxA oneHandleSxB * oneHandleSxC ^ 4 *
          commP oneHandleSxC oneHandleSxD) *
      commP (mpcSxE2 oneHandleSxA oneHandleSxB oneHandleSxW
          (oneHandleSxW * oneHandleSxB ^ 4) oneHandleSxZ)
        (oneHandleSxC ^ 4 * commP oneHandleSxC oneHandleSxD))

theorem oneHandleW5Mark_defect_six :
    levelMk H 6 (mRelWord 2 oneHandleW5Mark) =
      oneHandleW6ClosedDefect := by
  let p := oneHandleSxA
  let q := oneHandleSxB
  let r := oneHandleSxC
  let w := oneHandleSxD
  let u := levelMk H 6 (dmGen 2 1 (handleIdxU (0 : Fin 1)))
  let v := levelMk H 6 (dmGen 2 1 (handleIdxV (0 : Fin 1)))
  let z := oneHandleSxZ
  let sigma := oneHandleSxW
  let tau := oneHandleSxW * oneHandleSxB ^ 4
  let nu := oneHandleSxN
  let closed := oneHandleW6ClosedDefect
  have hsigma : sigma ∈ lambdaImage H 2 6 :=
    mpcSx_commP_mem_two w q
  have hz : z ∈ lambdaImage H 3 6 :=
    Subgroup.inv_mem _ (mpcSx_pow_four_mem q)
  have htau : tau ∈ lambdaImage H 2 6 :=
    Subgroup.mul_mem _ hsigma
      (mpcSx_lam_le (by omega) (mpcSx_pow_four_mem q))
  have hnu : nu ∈ lambdaImage H 2 6 :=
    Subgroup.mul_mem _
      (mpcSx_lam_le (by omega) (mpcSx_pow_four_mem q))
      (mpcSx_commP_mem_two (q ^ 2) w)
  have hbase : mWord 2 p q r w * commP u v = 1 := by
    have h := congrArg (levelMk H 6) (dm_relation 2 1)
    rw [map_one, map_mRelWord, mRelWord, handleWord_one] at h
    exact h
  have hbase' : mWord 2 p q r w = (commP u v)⁻¹ :=
    eq_inv_of_mul_eq_one_left hbase
  have hexpand : levelMk H 6 (mRelWord 2 oneHandleW5Mark) =
      mWord 2 p q r w * closed * commP u v := by
    simp [oneHandleW5Mark, oneHandleDirectModify, oneHandleW4Mark,
      oneHandleW5Factors, oneHandleW5Ut, oneHandleW5Un, oneHandleW4,
      mRelWord, handleWord_one]
    rw [map_mWord]
    change mWord 2 (p * z * sigma) (q * tau) (q ^ 2 * r) (w * nu) *
        commP u v = mWord 2 p q r w * closed * commP u v
    rw [mpcSx_mWord_six hsigma htau hnu hz]
    rfl
  have hcentral : levelMk H 6 (mRelWord 2 oneHandleW5Mark) ∈ zLayer H 5 :=
    ⟨mRelWord 2 oneHandleW5Mark, oneHandleW5Mark_mem.2.2.2.2, rfl⟩
  have hclosed : closed = levelMk H 6 (mRelWord 2 oneHandleW5Mark) := by
    calc
      closed = commP u v *
          (mWord 2 p q r w * closed * commP u v) * (commP u v)⁻¹ := by
        rw [hbase']
        group
      _ = commP u v * levelMk H 6 (mRelWord 2 oneHandleW5Mark) *
          (commP u v)⁻¹ := by rw [← hexpand]
      _ = levelMk H 6 (mRelWord 2 oneHandleW5Mark) := by
        rw [← (zLayer_commute hcentral (commP u v)).eq]
        group
  exact hclosed.symm

def OneHandleW5Correctable : Prop :=
  Nonempty (OneHandleDirectCorrection oneHandleW5Mark 5)

theorem oneHandleW5Correctable_iff_target_mem_range :
    OneHandleW5Correctable ↔
      oneHandleDirectLevelTarget oneHandleW5Mark_mem ∈
        (oneHandleDirectLevelShiftHom oneHandleW5Mark 5 (by omega)).range :=
  nonempty_directCorrection_iff_target_mem_range oneHandleW5Mark
    (by omega) oneHandleW5Mark_mem

theorem oneHandleW5_target_value :
    (oneHandleDirectLevelTarget oneHandleW5Mark_mem).1 =
      oneHandleW6ClosedDefect⁻¹ := by
  exact congrArg Inv.inv oneHandleW5Mark_defect_six

theorem oneHandleW6ClosedDefect_mem : oneHandleW6ClosedDefect ∈ zLayer H 5 := by
  rw [← oneHandleW5Mark_defect_six]
  exact ⟨mRelWord 2 oneHandleW5Mark, oneHandleW5Mark_mem.2.2.2.2, rfl⟩

theorem oneHandleW5Correctable_iff_finrank_eq :
    OneHandleW5Correctable ↔
      oneHandleDirectAugmentedTransposeRank (by omega) oneHandleW5Mark_mem =
        oneHandleDirectCoordinateTransposeRank oneHandleW5Mark 5 (by omega) :=
  nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
    (by omega) oneHandleW5Mark_mem

theorem oneHandleW5Correctable_iff_targetRowCoefficients :
    OneHandleW5Correctable ↔
      OneHandleDirectTargetRowCoefficients (by omega) oneHandleW5Mark_mem :=
  (targetRowCoefficients_iff_nonempty_directCorrection
    (by omega) oneHandleW5Mark_mem).symm

theorem oneHandleDirectSet_six_nonempty_of_W5Correctable
    (h : OneHandleW5Correctable) : (oneHandleDirectSet 6).Nonempty :=
  ⟨oneHandleDirectModify oneHandleW5Mark h.some.factors,
    h.some.toSuccessor (by omega) oneHandleW5Mark_mem⟩

#print axioms oneHandleW5Mark_defect_six
#print axioms oneHandleW5_target_value
#print axioms oneHandleW6ClosedDefect_mem
#print axioms oneHandleW5Correctable_iff_target_mem_range
#print axioms oneHandleW5Correctable_iff_finrank_eq
#print axioms oneHandleW5Correctable_iff_targetRowCoefficients
#print axioms oneHandleDirectSet_six_nonempty_of_W5Correctable

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSixTarget
