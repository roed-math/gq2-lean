/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose

/-!
# The target-augmented direct transpose

W254 isolates the four-row transpose.  This file appends target evaluation as a fifth
coordinate.  A correction exists exactly when the augmented transpose has the same kernel as
the four-row transpose.  Failure is exactly strict kernel containment.

This is the finite rank-test form of the remaining one-handle problem.  No kernel equality is
asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
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

noncomputable def oneHandleDirectTargetEvaluation
    {m : Fin (coreRank 1) → H} {k : ℕ} (hm : m ∈ oneHandleDirectSet k) :
    ElemDual (Additive (zLayer H k)) →+ ZMod 2 where
  toFun ell := ell (Additive.ofMul (oneHandleDirectLevelTarget hm))
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def oneHandleDirectAugmentedTranspose
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    ElemDual (Additive (zLayer H k)) →+ DirectTransposeTarget k × ZMod 2 where
  toFun ell :=
    (oneHandleDirectCoordinateTranspose m k hk ell,
      oneHandleDirectTargetEvaluation hm ell)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem augmentedTranspose_ker_le_coordinateTranspose_ker
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    (oneHandleDirectAugmentedTranspose hk hm).ker ≤
      (oneHandleDirectCoordinateTranspose m k hk).ker := by
  intro ell hell
  have hzero := AddMonoidHom.mem_ker.mp hell
  exact AddMonoidHom.mem_ker.mpr (congrArg Prod.fst hzero)

theorem directTargetTransposeVanishing_iff_ker_eq
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeVanishing hk hm ↔
      (oneHandleDirectAugmentedTranspose hk hm).ker =
        (oneHandleDirectCoordinateTranspose m k hk).ker := by
  constructor
  · intro Hvan
    apply le_antisymm
    · exact augmentedTranspose_ker_le_coordinateTranspose_ker hk hm
    · intro ell hell
      have hT := AddMonoidHom.mem_ker.mp hell
      apply AddMonoidHom.mem_ker.mpr
      apply Prod.ext
      · exact hT
      · exact Hvan ell hT
  · intro hker ell hT
    have hell : ell ∈ (oneHandleDirectCoordinateTranspose m k hk).ker :=
      AddMonoidHom.mem_ker.mpr hT
    rw [← hker] at hell
    have haug := AddMonoidHom.mem_ker.mp hell
    exact congrArg Prod.snd haug

theorem directTargetTransposeDetected_iff_ker_lt
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeDetected hk hm ↔
      (oneHandleDirectAugmentedTranspose hk hm).ker <
        (oneHandleDirectCoordinateTranspose m k hk).ker := by
  constructor
  · rintro ⟨ell, hT, ht⟩
    refine lt_of_le_of_ne
      (augmentedTranspose_ker_le_coordinateTranspose_ker hk hm) ?_
    intro heq
    have hell : ell ∈ (oneHandleDirectCoordinateTranspose m k hk).ker :=
      AddMonoidHom.mem_ker.mpr hT
    rw [← heq] at hell
    exact ht (congrArg Prod.snd (AddMonoidHom.mem_ker.mp hell))
  · intro hlt
    have hne : (oneHandleDirectAugmentedTranspose hk hm).ker ≠
        (oneHandleDirectCoordinateTranspose m k hk).ker := ne_of_lt hlt
    have hnot : ¬ OneHandleDirectTargetTransposeVanishing hk hm := by
      intro Hvan
      exact hne ((directTargetTransposeVanishing_iff_ker_eq hk hm).mp Hvan)
    apply (directTargetTransposeDetected_iff_no_correction hk hm).mpr
    rw [← directTargetTransposeVanishing_iff_nonempty_correction hk hm]
    exact hnot

theorem nonempty_directCorrection_iff_augmentedTranspose_ker_eq
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Nonempty (OneHandleDirectCorrection m k) ↔
      (oneHandleDirectAugmentedTranspose hk hm).ker =
        (oneHandleDirectCoordinateTranspose m k hk).ker := by
  rw [← directTargetTransposeVanishing_iff_nonempty_correction hk hm,
    directTargetTransposeVanishing_iff_ker_eq]

def OneHandleDirectAugmentedTransposeKernelSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      (oneHandleDirectAugmentedTranspose (by omega) hm).ker =
        (oneHandleDirectCoordinateTranspose m k (by omega)).ker

theorem augmentedTransposeKernelSupply_iff_correctionSupply :
    OneHandleDirectAugmentedTransposeKernelSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (nonempty_directCorrection_iff_augmentedTranspose_ker_eq
      (by omega) hm).mpr (H k hk m hm)
  · exact (nonempty_directCorrection_iff_augmentedTranspose_ker_eq
      (by omega) hm).mp (H k hk m hm)

theorem mpcPivShiftH_two_one_of_augmentedTransposeKernels
    (HK : OneHandleDirectAugmentedTransposeKernelSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (augmentedTransposeKernelSupply_iff_correctionSupply.mp HK)

#print axioms oneHandleDirectTargetEvaluation
#print axioms oneHandleDirectAugmentedTranspose
#print axioms augmentedTranspose_ker_le_coordinateTranspose_ker
#print axioms directTargetTransposeVanishing_iff_ker_eq
#print axioms directTargetTransposeDetected_iff_ker_lt
#print axioms nonempty_directCorrection_iff_augmentedTranspose_ker_eq
#print axioms OneHandleDirectAugmentedTransposeKernelSupply
#print axioms augmentedTransposeKernelSupply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_augmentedTransposeKernels

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
