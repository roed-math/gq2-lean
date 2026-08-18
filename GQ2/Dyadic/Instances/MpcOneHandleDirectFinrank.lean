/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectImageRank

/-!
# Finrank of the direct one-handle transpose

The repository deliberately keeps `ZMod` module structures local.  This file installs them
only inside the relevant definitions and records the dimensions of the coordinate transpose
image and its target-augmented image.  Their cardinalities are powers of two with precisely
those exponents.

A direct correction exists exactly when the two finranks agree; inequality is exactly the
dual obstruction.  No finrank equality is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCokernel
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectImageRank
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

private theorem zmodTwo_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_smul (R := ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

private theorem directTransposeTarget_add_self {k : ℕ}
    (v : DirectTransposeTarget k) : v + v = 0 := by
  apply Prod.ext
  · ext x
    exact zmodTwo_add_self _
  · apply Prod.ext
    · ext x
      exact zmodTwo_add_self _
    · apply Prod.ext
      · ext x
        exact zmodTwo_add_self _
      · ext x
        exact zmodTwo_add_self _

private theorem augmentedTransposeTarget_add_self {k : ℕ}
    (v : DirectTransposeTarget k × ZMod 2) : v + v = 0 := by
  apply Prod.ext
  · exact directTransposeTarget_add_self v.1
  · exact zmodTwo_add_self _

noncomputable def oneHandleDirectCoordinateTransposeRank
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) : ℕ := by
  letI : Module (ZMod 2) (DirectTransposeTarget k) :=
    AddCommGroup.zmodModule (fun v ↦ by rw [two_nsmul]; exact directTransposeTarget_add_self v)
  exact Module.finrank (ZMod 2)
    (AddSubgroup.toZModSubmodule 2 (oneHandleDirectCoordinateTranspose m k hk).range)

noncomputable def oneHandleDirectAugmentedTransposeRank
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : ℕ := by
  letI : Module (ZMod 2) (DirectTransposeTarget k × ZMod 2) :=
    AddCommGroup.zmodModule (fun v ↦ by rw [two_nsmul]; exact augmentedTransposeTarget_add_self v)
  exact Module.finrank (ZMod 2)
    (AddSubgroup.toZModSubmodule 2 (oneHandleDirectAugmentedTranspose hk hm).range)

theorem coordinateTranspose_rangeCard_eq_pow_rank
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    Nat.card (oneHandleDirectCoordinateTranspose m k hk).range =
      2 ^ oneHandleDirectCoordinateTransposeRank m k hk := by
  letI : Module (ZMod 2) (DirectTransposeTarget k) :=
    AddCommGroup.zmodModule (fun v ↦ by rw [two_nsmul]; exact directTransposeTarget_add_self v)
  letI : Finite (oneHandleDirectCoordinateTranspose m k hk).range :=
    Finite.of_surjective _ (oneHandleDirectCoordinateTranspose m k hk).rangeRestrict_surjective
  letI : Finite
      (AddSubgroup.toZModSubmodule 2 (oneHandleDirectCoordinateTranspose m k hk).range) :=
    inferInstanceAs (Finite (oneHandleDirectCoordinateTranspose m k hk).range)
  letI : Fintype
      (AddSubgroup.toZModSubmodule 2 (oneHandleDirectCoordinateTranspose m k hk).range) :=
    Fintype.ofFinite _
  letI : FiniteDimensional (ZMod 2)
      (AddSubgroup.toZModSubmodule 2 (oneHandleDirectCoordinateTranspose m k hk).range) :=
    Module.Finite.of_finite
  change Nat.card
      (AddSubgroup.toZModSubmodule 2 (oneHandleDirectCoordinateTranspose m k hk).range) = _
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rfl

theorem augmentedTranspose_rangeCard_eq_pow_rank
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Nat.card (oneHandleDirectAugmentedTranspose hk hm).range =
      2 ^ oneHandleDirectAugmentedTransposeRank hk hm := by
  letI : Module (ZMod 2) (DirectTransposeTarget k × ZMod 2) :=
    AddCommGroup.zmodModule (fun v ↦ by rw [two_nsmul]; exact augmentedTransposeTarget_add_self v)
  letI : Finite (oneHandleDirectAugmentedTranspose hk hm).range :=
    Finite.of_surjective _ (oneHandleDirectAugmentedTranspose hk hm).rangeRestrict_surjective
  letI : Finite
      (AddSubgroup.toZModSubmodule 2 (oneHandleDirectAugmentedTranspose hk hm).range) :=
    inferInstanceAs (Finite (oneHandleDirectAugmentedTranspose hk hm).range)
  letI : Fintype
      (AddSubgroup.toZModSubmodule 2 (oneHandleDirectAugmentedTranspose hk hm).range) :=
    Fintype.ofFinite _
  letI : FiniteDimensional (ZMod 2)
      (AddSubgroup.toZModSubmodule 2 (oneHandleDirectAugmentedTranspose hk hm).range) :=
    Module.Finite.of_finite
  change Nat.card
      (AddSubgroup.toZModSubmodule 2 (oneHandleDirectAugmentedTranspose hk hm).range) = _
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rfl

theorem nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Nonempty (OneHandleDirectCorrection m k) ↔
      oneHandleDirectAugmentedTransposeRank hk hm =
        oneHandleDirectCoordinateTransposeRank m k hk := by
  rw [nonempty_directCorrection_iff_augmentedTranspose_rangeCard_eq hk hm,
    augmentedTranspose_rangeCard_eq_pow_rank hk hm,
    coordinateTranspose_rangeCard_eq_pow_rank]
  exact (Nat.pow_right_injective (a := 2) (by omega)).eq_iff

theorem directTargetTransposeDetected_iff_finrank_ne
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeDetected hk hm ↔
      oneHandleDirectAugmentedTransposeRank hk hm ≠
        oneHandleDirectCoordinateTransposeRank m k hk := by
  rw [directTargetTransposeDetected_iff_no_correction hk hm]
  exact not_congr
    (nonempty_directCorrection_iff_augmentedTranspose_finrank_eq hk hm)

def OneHandleDirectAugmentedTransposeFinrankSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      oneHandleDirectAugmentedTransposeRank (by omega) hm =
        oneHandleDirectCoordinateTransposeRank m k (by omega)

theorem augmentedTransposeFinrankSupply_iff_correctionSupply :
    OneHandleDirectAugmentedTransposeFinrankSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
      (by omega) hm).mpr (H k hk m hm)
  · exact (nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
      (by omega) hm).mp (H k hk m hm)

theorem mpcPivShiftH_two_one_of_augmentedTransposeFinranks
    (HR : OneHandleDirectAugmentedTransposeFinrankSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (augmentedTransposeFinrankSupply_iff_correctionSupply.mp HR)

#print axioms oneHandleDirectCoordinateTransposeRank
#print axioms oneHandleDirectAugmentedTransposeRank
#print axioms coordinateTranspose_rangeCard_eq_pow_rank
#print axioms augmentedTranspose_rangeCard_eq_pow_rank
#print axioms nonempty_directCorrection_iff_augmentedTranspose_finrank_eq
#print axioms directTargetTransposeDetected_iff_finrank_ne
#print axioms OneHandleDirectAugmentedTransposeFinrankSupply
#print axioms augmentedTransposeFinrankSupply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_augmentedTransposeFinranks

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank
