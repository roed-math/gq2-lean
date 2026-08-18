/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateF2

/-!
# The transpose of the four direct one-handle rows

W253 gives four elementary-dual row equations.  This file assembles their pullbacks into one
finite transpose homomorphism.  Its kernel is exactly the space of functionals satisfying all
four equations.

The successor condition is now the standard finite-linear statement that the target is
annihilated by the kernel of the transpose.  No such vanishing theorem is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateF2
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

private abbrev DirectSource (k : ℕ) :=
  Additive (oneHandleDirectLambdaImage (k - 1) (k + 1))

private abbrev DirectNeutralSource (k : ℕ) :=
  Additive (oneHandleDirectNeutralLambdaImage (k - 1) (k + 1))

private abbrev DirectTransposeTarget (k : ℕ) :=
  (DirectSource k →+ ZMod 2) ×
    (DirectSource k →+ ZMod 2) ×
      (DirectNeutralSource k →+ ZMod 2) × (DirectSource k →+ ZMod 2)

noncomputable def oneHandleDirectCoordinateTranspose
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    ElemDual (Additive (zLayer H k)) →+ DirectTransposeTarget k where
  toFun ell :=
    ((ell : Additive (zLayer H k) →+ ZMod 2).comp
        (oneHandleDirectShiftA m k hk).toAdditive,
      (ell : Additive (zLayer H k) →+ ZMod 2).comp
        (oneHandleDirectShiftB m k hk).toAdditive,
      (ell : Additive (zLayer H k) →+ ZMod 2).comp
        (oneHandleDirectShiftC m k hk).toAdditive,
      (ell : Additive (zLayer H k) →+ ZMod 2).comp
        (oneHandleDirectShiftD m k hk).toAdditive)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem oneHandleDirectCoordinateTranspose_apply_A
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (ell : ElemDual (Additive (zLayer H k)))
    (x : oneHandleDirectLambdaImage (k - 1) (k + 1)) :
    (oneHandleDirectCoordinateTranspose m k hk ell).1 (Additive.ofMul x) =
      ell (Additive.ofMul (oneHandleDirectShiftA m k hk x)) := rfl

@[simp] theorem oneHandleDirectCoordinateTranspose_apply_B
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (ell : ElemDual (Additive (zLayer H k)))
    (x : oneHandleDirectLambdaImage (k - 1) (k + 1)) :
    (oneHandleDirectCoordinateTranspose m k hk ell).2.1 (Additive.ofMul x) =
      ell (Additive.ofMul (oneHandleDirectShiftB m k hk x)) := rfl

@[simp] theorem oneHandleDirectCoordinateTranspose_apply_C
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (ell : ElemDual (Additive (zLayer H k)))
    (x : oneHandleDirectNeutralLambdaImage (k - 1) (k + 1)) :
    (oneHandleDirectCoordinateTranspose m k hk ell).2.2.1 (Additive.ofMul x) =
      ell (Additive.ofMul (oneHandleDirectShiftC m k hk x)) := rfl

@[simp] theorem oneHandleDirectCoordinateTranspose_apply_D
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (ell : ElemDual (Additive (zLayer H k)))
    (x : oneHandleDirectLambdaImage (k - 1) (k + 1)) :
    (oneHandleDirectCoordinateTranspose m k hk ell).2.2.2 (Additive.ofMul x) =
      ell (Additive.ofMul (oneHandleDirectShiftD m k hk x)) := rfl

theorem coordinateTranspose_eq_zero_iff_rowsAnnihilate
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (ell : ElemDual (Additive (zLayer H k))) :
    oneHandleDirectCoordinateTranspose m k hk ell = 0 ↔
      OneHandleDirectCoordinateRowsAnnihilate m k hk ell := by
  constructor
  · intro h
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
    · have hx := congrArg (fun q : DirectTransposeTarget k => q.1 (Additive.ofMul x)) h
      simpa using hx
    · have hx := congrArg (fun q : DirectTransposeTarget k => q.2.1 (Additive.ofMul x)) h
      simpa using hx
    · have hx := congrArg (fun q : DirectTransposeTarget k => q.2.2.1 (Additive.ofMul x)) h
      simpa using hx
    · have hx := congrArg (fun q : DirectTransposeTarget k => q.2.2.2 (Additive.ofMul x)) h
      simpa using hx
  · rintro ⟨hA, hB, hC, hD⟩
    apply Prod.ext
    · ext x
      exact hA x
    · apply Prod.ext
      · ext x
        exact hB x
      · apply Prod.ext
        · ext x
          exact hC x
        · ext x
          exact hD x

def OneHandleDirectTargetTransposeVanishing
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∀ ell : ElemDual (Additive (zLayer H k)),
    oneHandleDirectCoordinateTranspose m k hk ell = 0 →
      ell (Additive.ofMul (oneHandleDirectLevelTarget hm)) = 0

theorem directTargetTransposeVanishing_iff_nonempty_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeVanishing hk hm ↔
      Nonempty (OneHandleDirectCorrection m k) := by
  rw [← directTargetCoordinateF2Vanishing_iff_nonempty_correction hk hm]
  constructor <;> intro Hvan ell hell
  · exact Hvan ell ((coordinateTranspose_eq_zero_iff_rowsAnnihilate m k hk ell).mpr hell)
  · exact Hvan ell ((coordinateTranspose_eq_zero_iff_rowsAnnihilate m k hk ell).mp hell)

def OneHandleDirectTargetTransposeDetected
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∃ ell : ElemDual (Additive (zLayer H k)),
    oneHandleDirectCoordinateTranspose m k hk ell = 0 ∧
      ell (Additive.ofMul (oneHandleDirectLevelTarget hm)) ≠ 0

theorem directTargetTransposeDetected_iff_no_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeDetected hk hm ↔
      ¬ Nonempty (OneHandleDirectCorrection m k) := by
  rw [← directTargetTransposeVanishing_iff_nonempty_correction hk hm]
  unfold OneHandleDirectTargetTransposeDetected OneHandleDirectTargetTransposeVanishing
  push Not
  rfl

def OneHandleDirectTargetTransposeVanishingSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      OneHandleDirectTargetTransposeVanishing (by omega) hm

theorem directTargetTransposeSupply_iff_correctionSupply :
    OneHandleDirectTargetTransposeVanishingSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (directTargetTransposeVanishing_iff_nonempty_correction
      (by omega) hm).mp (H k hk m hm)
  · exact (directTargetTransposeVanishing_iff_nonempty_correction
      (by omega) hm).mpr (H k hk m hm)

theorem mpcPivShiftH_two_one_of_directTargetTranspose
    (HT : OneHandleDirectTargetTransposeVanishingSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (directTargetTransposeSupply_iff_correctionSupply.mp HT)

#print axioms oneHandleDirectCoordinateTranspose
#print axioms coordinateTranspose_eq_zero_iff_rowsAnnihilate
#print axioms OneHandleDirectTargetTransposeVanishing
#print axioms directTargetTransposeVanishing_iff_nonempty_correction
#print axioms OneHandleDirectTargetTransposeDetected
#print axioms directTargetTransposeDetected_iff_no_correction
#print axioms OneHandleDirectTargetTransposeVanishingSupply
#print axioms directTargetTransposeSupply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_directTargetTranspose

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
