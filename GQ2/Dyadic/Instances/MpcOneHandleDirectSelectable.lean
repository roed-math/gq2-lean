/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectRowCoefficients

/-!
# Selectable direct one-handle correction

The uniform direct-correction interfaces ask for a correction of every point at every stage.
The inverse-limit argument only needs one correctable point whenever the current stage is
nonempty.  This file records that strictly weaker selectable supply.

Selectable correction, selectable zero finrank jump, and selectable four-row coefficients are
equivalent, and each suffices for `MpcPivShiftH 2 1`.  No selectable witness is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectSelectable

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank
open GQ2.Dyadic.Instances.MpcOneHandleDirectRowSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectRowCoefficients

private abbrev H := DM 2 1

def OneHandleDirectSelectableCorrectionSupply : Prop :=
  ∀ (k : ℕ) (_hk : 4 ≤ k), (oneHandleDirectSet k).Nonempty →
    ∃ m : Fin (coreRank 1) → H, m ∈ oneHandleDirectSet k ∧
      Nonempty (OneHandleDirectCorrection m k)

theorem directSuccessorSupply_of_selectableCorrectionSupply
    (Hcorr : OneHandleDirectSelectableCorrectionSupply) :
    OneHandleDirectSuccessorSupply := by
  intro k hk hstage
  obtain ⟨m, hm, E⟩ := Hcorr k hk hstage
  exact ⟨oneHandleDirectModify m E.some.factors,
    E.some.toSuccessor hk hm⟩

theorem mpcPivShiftH_two_one_of_selectableCorrection
    (Hcorr : OneHandleDirectSelectableCorrectionSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_successor
    (directSuccessorSupply_of_selectableCorrectionSupply Hcorr)

def OneHandleDirectSelectableFinrankSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), (oneHandleDirectSet k).Nonempty →
    ∃ m : Fin (coreRank 1) → H, ∃ hm : m ∈ oneHandleDirectSet k,
      oneHandleDirectAugmentedTransposeRank (by omega) hm =
        oneHandleDirectCoordinateTransposeRank m k (by omega)

theorem selectableFinrankSupply_iff_selectableCorrectionSupply :
    OneHandleDirectSelectableFinrankSupply ↔
      OneHandleDirectSelectableCorrectionSupply := by
  constructor <;> intro H k hk hstage
  · obtain ⟨m, hm, hrank⟩ := H k hk hstage
    exact ⟨m, hm,
      (nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
        (by omega) hm).mpr hrank⟩
  · obtain ⟨m, hm, hcorr⟩ := H k hk hstage
    exact ⟨m, hm,
      (nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
        (by omega) hm).mp hcorr⟩

def OneHandleDirectSelectableRowCoefficientSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), (oneHandleDirectSet k).Nonempty →
    ∃ m : Fin (coreRank 1) → H, ∃ hm : m ∈ oneHandleDirectSet k,
      OneHandleDirectTargetRowCoefficients (by omega) hm

theorem selectableRowCoefficientSupply_iff_selectableCorrectionSupply :
    OneHandleDirectSelectableRowCoefficientSupply ↔
      OneHandleDirectSelectableCorrectionSupply := by
  constructor <;> intro H k hk hstage
  · obtain ⟨m, hm, hcoeff⟩ := H k hk hstage
    exact ⟨m, hm,
      (targetRowCoefficients_iff_nonempty_directCorrection
        (by omega) hm).mp hcoeff⟩
  · obtain ⟨m, hm, hcorr⟩ := H k hk hstage
    exact ⟨m, hm,
      (targetRowCoefficients_iff_nonempty_directCorrection
        (by omega) hm).mpr hcorr⟩

theorem selectableRowCoefficientSupply_iff_selectableFinrankSupply :
    OneHandleDirectSelectableRowCoefficientSupply ↔
      OneHandleDirectSelectableFinrankSupply := by
  rw [selectableRowCoefficientSupply_iff_selectableCorrectionSupply,
    selectableFinrankSupply_iff_selectableCorrectionSupply]

theorem mpcPivShiftH_two_one_of_selectableFinranks
    (Hrank : OneHandleDirectSelectableFinrankSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_selectableCorrection
    (selectableFinrankSupply_iff_selectableCorrectionSupply.mp Hrank)

theorem mpcPivShiftH_two_one_of_selectableRowCoefficients
    (Hcoeff : OneHandleDirectSelectableRowCoefficientSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_selectableCorrection
    (selectableRowCoefficientSupply_iff_selectableCorrectionSupply.mp Hcoeff)

#print axioms OneHandleDirectSelectableCorrectionSupply
#print axioms directSuccessorSupply_of_selectableCorrectionSupply
#print axioms mpcPivShiftH_two_one_of_selectableCorrection
#print axioms OneHandleDirectSelectableFinrankSupply
#print axioms selectableFinrankSupply_iff_selectableCorrectionSupply
#print axioms OneHandleDirectSelectableRowCoefficientSupply
#print axioms selectableRowCoefficientSupply_iff_selectableCorrectionSupply
#print axioms selectableRowCoefficientSupply_iff_selectableFinrankSupply
#print axioms mpcPivShiftH_two_one_of_selectableFinranks
#print axioms mpcPivShiftH_two_one_of_selectableRowCoefficients

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectSelectable
