/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose

/-!
# A finite kernel-cardinality test for the direct one-handle obstruction

The augmented transpose kernel lies inside the four-coordinate transpose kernel.  Since both
are finite, they agree exactly when their cardinalities agree.  Thus direct correction is a
literal finite nullity equality, while a dual detector exists exactly when the two kernel
cardinalities differ.

This file packages that rank-test boundary.  It does not assert the required equality.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectRankTest

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

theorem augmentedTranspose_ker_eq_iff_card_eq
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    (oneHandleDirectAugmentedTranspose hk hm).ker =
        (oneHandleDirectCoordinateTranspose m k hk).ker ↔
      Nat.card (oneHandleDirectAugmentedTranspose hk hm).ker =
        Nat.card (oneHandleDirectCoordinateTranspose m k hk).ker := by
  constructor
  · intro h
    rw [h]
  · intro hcard
    exact AddSubgroup.eq_of_le_of_card_ge
      (augmentedTranspose_ker_le_coordinateTranspose_ker hk hm)
      (le_of_eq hcard.symm)

theorem nonempty_directCorrection_iff_augmentedTranspose_kernelCard_eq
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Nonempty (OneHandleDirectCorrection m k) ↔
      Nat.card (oneHandleDirectAugmentedTranspose hk hm).ker =
        Nat.card (oneHandleDirectCoordinateTranspose m k hk).ker := by
  rw [nonempty_directCorrection_iff_augmentedTranspose_ker_eq hk hm,
    augmentedTranspose_ker_eq_iff_card_eq hk hm]

theorem directTargetTransposeDetected_iff_kernelCard_ne
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeDetected hk hm ↔
      Nat.card (oneHandleDirectAugmentedTranspose hk hm).ker ≠
        Nat.card (oneHandleDirectCoordinateTranspose m k hk).ker := by
  rw [directTargetTransposeDetected_iff_no_correction hk hm]
  exact not_congr
    (nonempty_directCorrection_iff_augmentedTranspose_kernelCard_eq hk hm)

def OneHandleDirectAugmentedTransposeRankSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      Nat.card (oneHandleDirectAugmentedTranspose (by omega) hm).ker =
        Nat.card (oneHandleDirectCoordinateTranspose m k (by omega)).ker

theorem augmentedTransposeRankSupply_iff_correctionSupply :
    OneHandleDirectAugmentedTransposeRankSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (nonempty_directCorrection_iff_augmentedTranspose_kernelCard_eq
      (by omega) hm).mpr (H k hk m hm)
  · exact (nonempty_directCorrection_iff_augmentedTranspose_kernelCard_eq
      (by omega) hm).mp (H k hk m hm)

theorem mpcPivShiftH_two_one_of_augmentedTransposeRanks
    (HR : OneHandleDirectAugmentedTransposeRankSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (augmentedTransposeRankSupply_iff_correctionSupply.mp HR)

#print axioms augmentedTranspose_ker_eq_iff_card_eq
#print axioms nonempty_directCorrection_iff_augmentedTranspose_kernelCard_eq
#print axioms directTargetTransposeDetected_iff_kernelCard_ne
#print axioms OneHandleDirectAugmentedTransposeRankSupply
#print axioms augmentedTransposeRankSupply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_augmentedTransposeRanks

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectRankTest
