/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectRankTest

/-!
# The image-rank form of the direct one-handle obstruction

W256 expresses correction as equality of the augmented and coordinate transpose nullities.
Rank-nullity over their common finite source shows that this is equivalent to equality of the
two image cardinalities.  Thus the target row is correctable exactly when adjoining it does not
increase the finite transpose rank.

This file packages that image-rank boundary.  It does not assert the required equality.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectImageRank

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectRankTest
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

private theorem rangeCard_mul_kernelCard
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Finite A]
    (f : A →+ B) :
    Nat.card f.range * Nat.card f.ker = Nat.card A := by
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker).symm

private theorem rangeCard_eq_iff_kernelCard_eq
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Finite A] (f : A →+ B) (g : A →+ C) :
    Nat.card f.range = Nat.card g.range ↔
      Nat.card f.ker = Nat.card g.ker := by
  letI : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  letI : Finite g.range :=
    Finite.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hf := rangeCard_mul_kernelCard f
  have hg := rangeCard_mul_kernelCard g
  constructor
  · intro hrange
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := f.range))
    calc
      Nat.card f.range * Nat.card f.ker = Nat.card A := hf
      _ = Nat.card g.range * Nat.card g.ker := hg.symm
      _ = Nat.card f.range * Nat.card g.ker := by rw [hrange]
  · intro hker
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.ker))
    calc
      Nat.card f.range * Nat.card f.ker = Nat.card A := hf
      _ = Nat.card g.range * Nat.card g.ker := hg.symm
      _ = Nat.card g.range * Nat.card f.ker := by rw [hker]

theorem augmentedTranspose_rangeCard_eq_iff_kernelCard_eq
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Nat.card (oneHandleDirectAugmentedTranspose hk hm).range =
        Nat.card (oneHandleDirectCoordinateTranspose m k hk).range ↔
      Nat.card (oneHandleDirectAugmentedTranspose hk hm).ker =
        Nat.card (oneHandleDirectCoordinateTranspose m k hk).ker :=
  rangeCard_eq_iff_kernelCard_eq _ _

theorem nonempty_directCorrection_iff_augmentedTranspose_rangeCard_eq
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Nonempty (OneHandleDirectCorrection m k) ↔
      Nat.card (oneHandleDirectAugmentedTranspose hk hm).range =
        Nat.card (oneHandleDirectCoordinateTranspose m k hk).range := by
  rw [nonempty_directCorrection_iff_augmentedTranspose_kernelCard_eq hk hm,
    ← augmentedTranspose_rangeCard_eq_iff_kernelCard_eq hk hm]

theorem directTargetTransposeDetected_iff_rangeCard_ne
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeDetected hk hm ↔
      Nat.card (oneHandleDirectAugmentedTranspose hk hm).range ≠
        Nat.card (oneHandleDirectCoordinateTranspose m k hk).range := by
  rw [directTargetTransposeDetected_iff_no_correction hk hm]
  exact not_congr
    (nonempty_directCorrection_iff_augmentedTranspose_rangeCard_eq hk hm)

def OneHandleDirectAugmentedTransposeImageRankSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      Nat.card (oneHandleDirectAugmentedTranspose (by omega) hm).range =
        Nat.card (oneHandleDirectCoordinateTranspose m k (by omega)).range

theorem augmentedTransposeImageRankSupply_iff_correctionSupply :
    OneHandleDirectAugmentedTransposeImageRankSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (nonempty_directCorrection_iff_augmentedTranspose_rangeCard_eq
      (by omega) hm).mpr (H k hk m hm)
  · exact (nonempty_directCorrection_iff_augmentedTranspose_rangeCard_eq
      (by omega) hm).mp (H k hk m hm)

theorem mpcPivShiftH_two_one_of_augmentedTransposeImageRanks
    (HR : OneHandleDirectAugmentedTransposeImageRankSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (augmentedTransposeImageRankSupply_iff_correctionSupply.mp HR)

#print axioms augmentedTranspose_rangeCard_eq_iff_kernelCard_eq
#print axioms nonempty_directCorrection_iff_augmentedTranspose_rangeCard_eq
#print axioms directTargetTransposeDetected_iff_rangeCard_ne
#print axioms OneHandleDirectAugmentedTransposeImageRankSupply
#print axioms augmentedTransposeImageRankSupply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_augmentedTransposeImageRanks

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectImageRank
