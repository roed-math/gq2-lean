/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSixCorrection

/-!
# The exact class-seven target at one handle

W267 supplies explicit depth-four correction factors for W264's class-five marking.  This
module names the resulting class-six marking and records its exact next defect in
`D_M(2,1) / lambda_7`.  The correction packet proves that the marking belongs to the sixth
direct stage, so its relator lies in `lambda_6` and its class-seven image lies in the top
central layer.

Correctability of this named marking is restated through the generic direct finite machinery:
as membership of the target in the four-coordinate image, equality of the coordinate and
augmented ranks, and existence of four scalar row coefficients.  No class-seven collection or
correction is asserted here.  These equivalent finite statements are the exact next target.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank
open GQ2.Dyadic.Instances.MpcOneHandleDirectRowCoefficients
open GQ2.Dyadic.Instances.MpcOneHandleClassSixTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSixCorrection
open GQ2.Roe.Labute

private abbrev H := DM 2 1

/-- The explicit one-handle class-six marking produced by the W267 correction. -/
def oneHandleW6Mark : Fin (coreRank 1) → H :=
  oneHandleDirectModify oneHandleW5Mark oneHandleC6CorrectedFactors

theorem oneHandleW6Mark_mem : oneHandleW6Mark ∈ oneHandleDirectSet 6 :=
  oneHandleW5ClassSixCorrection.toSuccessor (by omega) oneHandleW5Mark_mem

/-- The literal class-seven defect of the explicit class-six marking. -/
def oneHandleW7Defect : levelQuot H 7 :=
  levelMk H 7 (mRelWord 2 oneHandleW6Mark)

theorem oneHandleW6Mark_defect_seven :
    levelMk H 7 (mRelWord 2 oneHandleW6Mark) = oneHandleW7Defect := rfl

theorem oneHandleW7Defect_mem : oneHandleW7Defect ∈ zLayer H 6 := by
  exact ⟨mRelWord 2 oneHandleW6Mark, oneHandleW6Mark_mem.2.2.2.2, rfl⟩

/-- The exact W6-to-W7 direct-correction interface. -/
def OneHandleW6Correctable : Prop :=
  Nonempty (OneHandleDirectCorrection oneHandleW6Mark 6)

theorem oneHandleW6Correctable_iff_target_mem_range :
    OneHandleW6Correctable ↔
      oneHandleDirectLevelTarget oneHandleW6Mark_mem ∈
        (oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)).range :=
  nonempty_directCorrection_iff_target_mem_range oneHandleW6Mark
    (by omega) oneHandleW6Mark_mem

theorem oneHandleW6_target_value :
    (oneHandleDirectLevelTarget oneHandleW6Mark_mem).1 = oneHandleW7Defect⁻¹ := by
  exact congrArg Inv.inv oneHandleW6Mark_defect_seven

theorem oneHandleW6Correctable_iff_finrank_eq :
    OneHandleW6Correctable ↔
      oneHandleDirectAugmentedTransposeRank (by omega) oneHandleW6Mark_mem =
        oneHandleDirectCoordinateTransposeRank oneHandleW6Mark 6 (by omega) :=
  nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
    (by omega) oneHandleW6Mark_mem

theorem oneHandleW6Correctable_iff_targetRowCoefficients :
    OneHandleW6Correctable ↔
      OneHandleDirectTargetRowCoefficients (by omega) oneHandleW6Mark_mem :=
  (targetRowCoefficients_iff_nonempty_directCorrection
    (by omega) oneHandleW6Mark_mem).symm

theorem oneHandleDirectSet_seven_nonempty_of_W6Correctable
    (h : OneHandleW6Correctable) : (oneHandleDirectSet 7).Nonempty :=
  ⟨oneHandleDirectModify oneHandleW6Mark h.some.factors,
    h.some.toSuccessor (by omega) oneHandleW6Mark_mem⟩

#print axioms oneHandleW6Mark_mem
#print axioms oneHandleW6Mark_defect_seven
#print axioms oneHandleW7Defect_mem
#print axioms oneHandleW6Correctable_iff_target_mem_range
#print axioms oneHandleW6_target_value
#print axioms oneHandleW6Correctable_iff_finrank_eq
#print axioms oneHandleW6Correctable_iff_targetRowCoefficients
#print axioms oneHandleDirectSet_seven_nonempty_of_W6Correctable

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
