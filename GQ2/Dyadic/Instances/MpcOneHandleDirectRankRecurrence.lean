/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectSelectable

/-!
# The exact direct one-handle rank recurrence

A point already lying at depth `k + 1` has the trivial correction at depth `k`.  Conversely,
the direct successor theorem turns any correction at depth `k` into a point at depth `k + 1`.
Thus the next finite stage is nonempty exactly when some current point is correctable.

Combining this observation with the finite transpose criteria gives the exact recurrence in
three equivalent forms: existence of a correction, equality of the coordinate and augmented
finranks, or four scalar bidual row coefficients.  Consequently, the selectable supplies are
equivalent to the original direct successor supply; they are not merely sufficient weakenings.
No correction, rank equality, or row coefficient is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectRankRecurrence

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank
open GQ2.Dyadic.Instances.MpcOneHandleDirectRowCoefficients
open GQ2.Dyadic.Instances.MpcOneHandleDirectSelectable
open GQ2.Roe.Labute

private abbrev H := DM 2 1

theorem nonempty_directCorrection_of_mem_succ
    {m : Fin (coreRank 1) → H} {k : ℕ}
    (hm : m ∈ oneHandleDirectSet (k + 1)) :
    Nonempty (OneHandleDirectCorrection m k) := by
  have hlevel : levelMk H (k + 1) (mRelWord 2 m) = 1 :=
    (lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mp hm.2.2.2.2
  refine ⟨{
    factors := fun _ ↦ 1
    depth := by simp
    handleU := by simp
    handleV := by simp
    chi := by simp
    row := by simp
    kills := ?_ }⟩
  rw [oneHandleDirectRelatorShift_eq]
  change
    (levelMk H (k + 1) (mRelWord 2 m))⁻¹ *
        levelMk H (k + 1) (mRelWord 2 (fun i ↦ m i * 1)) =
      (levelMk H (k + 1) (mRelWord 2 m))⁻¹
  simp [hlevel]

theorem oneHandleDirectSet_succ_nonempty_iff_exists_correction
    (k : ℕ) (hk : 4 ≤ k) :
    (oneHandleDirectSet (k + 1)).Nonempty ↔
      ∃ m : Fin (coreRank 1) → H, m ∈ oneHandleDirectSet k ∧
        Nonempty (OneHandleDirectCorrection m k) := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, oneHandleDirectSet_antitone (by omega) hm,
      nonempty_directCorrection_of_mem_succ hm⟩
  · rintro ⟨m, hm, E⟩
    exact ⟨oneHandleDirectModify m E.some.factors,
      E.some.toSuccessor hk hm⟩

theorem oneHandleDirectSet_succ_nonempty_iff_exists_finrank_eq
    (k : ℕ) (hk : 4 ≤ k) :
    (oneHandleDirectSet (k + 1)).Nonempty ↔
      ∃ m : Fin (coreRank 1) → H, ∃ hm : m ∈ oneHandleDirectSet k,
        oneHandleDirectAugmentedTransposeRank (by omega) hm =
          oneHandleDirectCoordinateTransposeRank m k (by omega) := by
  rw [oneHandleDirectSet_succ_nonempty_iff_exists_correction k hk]
  constructor
  · rintro ⟨m, hm, hcorr⟩
    exact ⟨m, hm,
      (nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
        (by omega) hm).mp hcorr⟩
  · rintro ⟨m, hm, hrank⟩
    exact ⟨m, hm,
      (nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
        (by omega) hm).mpr hrank⟩

theorem oneHandleDirectSet_succ_nonempty_iff_exists_rowCoefficients
    (k : ℕ) (hk : 4 ≤ k) :
    (oneHandleDirectSet (k + 1)).Nonempty ↔
      ∃ m : Fin (coreRank 1) → H, ∃ hm : m ∈ oneHandleDirectSet k,
        OneHandleDirectTargetRowCoefficients (by omega) hm := by
  rw [oneHandleDirectSet_succ_nonempty_iff_exists_correction k hk]
  constructor
  · rintro ⟨m, hm, hcorr⟩
    exact ⟨m, hm,
      (targetRowCoefficients_iff_nonempty_directCorrection
        (by omega) hm).mpr hcorr⟩
  · rintro ⟨m, hm, hcoeff⟩
    exact ⟨m, hm,
      (targetRowCoefficients_iff_nonempty_directCorrection
        (by omega) hm).mp hcoeff⟩

theorem selectableCorrectionSupply_iff_successorSupply :
    OneHandleDirectSelectableCorrectionSupply ↔
      OneHandleDirectSuccessorSupply := by
  constructor
  · exact directSuccessorSupply_of_selectableCorrectionSupply
  · intro Hsucc k hk hstage
    obtain ⟨m, hm, hcorr⟩ :=
      (oneHandleDirectSet_succ_nonempty_iff_exists_correction k hk).mp
        (Hsucc k hk hstage)
    exact ⟨m, hm, hcorr⟩

theorem selectableFinrankSupply_iff_successorSupply :
    OneHandleDirectSelectableFinrankSupply ↔
      OneHandleDirectSuccessorSupply := by
  rw [selectableFinrankSupply_iff_selectableCorrectionSupply,
    selectableCorrectionSupply_iff_successorSupply]

theorem selectableRowCoefficientSupply_iff_successorSupply :
    OneHandleDirectSelectableRowCoefficientSupply ↔
      OneHandleDirectSuccessorSupply := by
  rw [selectableRowCoefficientSupply_iff_selectableCorrectionSupply,
    selectableCorrectionSupply_iff_successorSupply]

#print axioms nonempty_directCorrection_of_mem_succ
#print axioms oneHandleDirectSet_succ_nonempty_iff_exists_correction
#print axioms oneHandleDirectSet_succ_nonempty_iff_exists_finrank_eq
#print axioms oneHandleDirectSet_succ_nonempty_iff_exists_rowCoefficients
#print axioms selectableCorrectionSupply_iff_successorSupply
#print axioms selectableFinrankSupply_iff_successorSupply
#print axioms selectableRowCoefficientSupply_iff_successorSupply

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectRankRecurrence
