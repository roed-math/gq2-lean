/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank

/-!
# The direct one-handle rank jump

The augmented transpose is the coordinate transpose together with one scalar target row.
Projection onto the coordinate rows is surjective on images, while the full augmented image
embeds into the coordinate image times `ZMod 2`.  Consequently its finrank is either the
coordinate finrank or exactly one larger.

Thus a direct correction is precisely the zero-jump case, and the dual obstruction is
precisely the one-dimensional-jump case.  This file proves the dichotomy but does not decide
which alternative occurs.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectRankJump

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

private noncomputable def rangeProjection
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    (oneHandleDirectAugmentedTranspose hk hm).range →
      (oneHandleDirectCoordinateTranspose m k hk).range := fun y =>
  ⟨y.1.1, by
    rcases y.2 with ⟨ell, h⟩
    exact ⟨ell, congrArg Prod.fst h⟩⟩

private theorem rangeProjection_surjective
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Function.Surjective (rangeProjection hk hm) := by
  rintro ⟨y, ell, rfl⟩
  refine ⟨⟨oneHandleDirectAugmentedTranspose hk hm ell, ⟨ell, rfl⟩⟩, ?_⟩
  rfl

private noncomputable def rangeEmbedding
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    (oneHandleDirectAugmentedTranspose hk hm).range →
      (oneHandleDirectCoordinateTranspose m k hk).range × ZMod 2 := fun y =>
  (rangeProjection hk hm y, y.1.2)

private theorem rangeEmbedding_injective
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Function.Injective (rangeEmbedding hk hm) := by
  intro x y hxy
  change (rangeProjection hk hm x, x.1.2) =
    (rangeProjection hk hm y, y.1.2) at hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z => z.1.1) hxy
  · exact congrArg (fun z => z.2) hxy

theorem coordinateTransposeRank_le_augmentedTransposeRank
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    oneHandleDirectCoordinateTransposeRank m k hk ≤
      oneHandleDirectAugmentedTransposeRank hk hm := by
  letI : Finite (oneHandleDirectAugmentedTranspose hk hm).range :=
    Finite.of_surjective _
      (oneHandleDirectAugmentedTranspose hk hm).rangeRestrict_surjective
  have hcard :
      Nat.card (oneHandleDirectCoordinateTranspose m k hk).range ≤
        Nat.card (oneHandleDirectAugmentedTranspose hk hm).range :=
    Nat.card_le_card_of_surjective _ (rangeProjection_surjective hk hm)
  rw [coordinateTranspose_rangeCard_eq_pow_rank,
    augmentedTranspose_rangeCard_eq_pow_rank] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem augmentedTransposeRank_le_coordinateTransposeRank_add_one
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    oneHandleDirectAugmentedTransposeRank hk hm ≤
      oneHandleDirectCoordinateTransposeRank m k hk + 1 := by
  letI : Finite (oneHandleDirectCoordinateTranspose m k hk).range :=
    Finite.of_surjective _
      (oneHandleDirectCoordinateTranspose m k hk).rangeRestrict_surjective
  have hcard :
      Nat.card (oneHandleDirectAugmentedTranspose hk hm).range ≤
        Nat.card ((oneHandleDirectCoordinateTranspose m k hk).range × ZMod 2) :=
    Nat.card_le_card_of_injective _ (rangeEmbedding_injective hk hm)
  rw [Nat.card_prod, Nat.card_zmod,
    coordinateTranspose_rangeCard_eq_pow_rank,
    augmentedTranspose_rangeCard_eq_pow_rank, ← pow_succ] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

theorem augmentedTransposeRank_eq_or_eq_add_one
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    oneHandleDirectAugmentedTransposeRank hk hm =
        oneHandleDirectCoordinateTransposeRank m k hk ∨
      oneHandleDirectAugmentedTransposeRank hk hm =
        oneHandleDirectCoordinateTransposeRank m k hk + 1 := by
  have hlo := coordinateTransposeRank_le_augmentedTransposeRank hk hm
  have hhi := augmentedTransposeRank_le_coordinateTransposeRank_add_one hk hm
  omega

theorem directTargetTransposeDetected_iff_finrank_eq_add_one
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeDetected hk hm ↔
      oneHandleDirectAugmentedTransposeRank hk hm =
        oneHandleDirectCoordinateTransposeRank m k hk + 1 := by
  rw [directTargetTransposeDetected_iff_finrank_ne hk hm]
  rcases augmentedTransposeRank_eq_or_eq_add_one hk hm with h | h
  · simp [h]
  · simp [h]

theorem nonempty_directCorrection_iff_no_finrank_jump
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Nonempty (OneHandleDirectCorrection m k) ↔
      oneHandleDirectAugmentedTransposeRank hk hm -
        oneHandleDirectCoordinateTransposeRank m k hk = 0 := by
  rw [nonempty_directCorrection_iff_augmentedTranspose_finrank_eq hk hm]
  have hle := coordinateTransposeRank_le_augmentedTransposeRank hk hm
  omega

theorem directTargetTransposeDetected_iff_finrank_jump_one
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeDetected hk hm ↔
      oneHandleDirectAugmentedTransposeRank hk hm -
        oneHandleDirectCoordinateTransposeRank m k hk = 1 := by
  rw [directTargetTransposeDetected_iff_finrank_eq_add_one hk hm]
  have hle := coordinateTransposeRank_le_augmentedTransposeRank hk hm
  omega

#print axioms coordinateTransposeRank_le_augmentedTransposeRank
#print axioms augmentedTransposeRank_le_coordinateTransposeRank_add_one
#print axioms augmentedTransposeRank_eq_or_eq_add_one
#print axioms directTargetTransposeDetected_iff_finrank_eq_add_one
#print axioms nonempty_directCorrection_iff_no_finrank_jump
#print axioms directTargetTransposeDetected_iff_finrank_jump_one

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectRankJump
