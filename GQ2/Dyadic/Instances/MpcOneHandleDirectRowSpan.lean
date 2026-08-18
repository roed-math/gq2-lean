/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectRankJump

/-!
# The target row in the direct one-handle transpose

The zero-rank-jump condition has the usual row-span interpretation.  The target-evaluation
row belongs to the span of the four coordinate-row families exactly when it factors through
the coordinate transpose.  Since the coordinate image is an `F₂`-subspace, a factor on the
image extends to the full coordinate target.

This file proves that target-row factorization, direct correction, and zero finrank jump are
equivalent.  Failure is exactly non-membership in the row span.  No row-span membership is
asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectRowSpan

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectAugmentedTranspose
open GQ2.Dyadic.Instances.MpcOneHandleDirectFinrank
open GQ2.Dyadic.Instances.MpcOneHandleDirectRankJump
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

def OneHandleDirectTargetRowSpan
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∃ E : DirectTransposeTarget k →+ ZMod 2,
    E.comp (oneHandleDirectCoordinateTranspose m k hk) =
      oneHandleDirectTargetEvaluation hm

private theorem targetEvaluation_ker_le_of_vanishing
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k)
    (Hvan : OneHandleDirectTargetTransposeVanishing hk hm) :
    (oneHandleDirectCoordinateTranspose m k hk).ker ≤
      (oneHandleDirectTargetEvaluation hm).ker := by
  intro ell hell
  apply AddMonoidHom.mem_ker.mpr
  exact Hvan ell (AddMonoidHom.mem_ker.mp hell)

private theorem exists_targetRangeFactor_of_vanishing
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k)
    (Hvan : OneHandleDirectTargetTransposeVanishing hk hm) :
    ∃ E : (oneHandleDirectCoordinateTranspose m k hk).range →+ ZMod 2,
      E.comp (oneHandleDirectCoordinateTranspose m k hk).rangeRestrict =
        oneHandleDirectTargetEvaluation hm := by
  let T := oneHandleDirectCoordinateTranspose m k hk
  let t := oneHandleDirectTargetEvaluation hm
  have hker : T.rangeRestrict.ker ≤ t.ker := by
    rw [AddMonoidHom.ker_rangeRestrict]
    exact targetEvaluation_ker_le_of_vanishing hk hm Hvan
  let E : T.range →+ ZMod 2 :=
    T.rangeRestrict.liftOfSurjective T.rangeRestrict_surjective ⟨t, hker⟩
  refine ⟨E, ?_⟩
  ext ell
  exact AddMonoidHom.liftOfRightInverse_comp_apply T.rangeRestrict
    (Function.surjInv T.rangeRestrict_surjective)
    (Function.rightInverse_surjInv T.rangeRestrict_surjective)
    ⟨t, hker⟩ ell

theorem targetRowSpan_of_transposeVanishing
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k)
    (Hvan : OneHandleDirectTargetTransposeVanishing hk hm) :
    OneHandleDirectTargetRowSpan hk hm := by
  obtain ⟨ER, hER⟩ := exists_targetRangeFactor_of_vanishing hk hm Hvan
  letI : Module (ZMod 2) (DirectTransposeTarget k) :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact directTransposeTarget_add_self v)
  let T := oneHandleDirectCoordinateTranspose m k hk
  let p : Submodule (ZMod 2) (DirectTransposeTarget k) :=
    AddSubgroup.toZModSubmodule 2 T.range
  let ERlin : p →ₗ[ZMod 2] ZMod 2 := ER.toZModLinearMap 2
  obtain ⟨E, hE⟩ := LinearMap.exists_extend ERlin
  refine ⟨E.toAddMonoidHom, ?_⟩
  ext ell
  let Tell : (oneHandleDirectCoordinateTranspose m k hk).range :=
    ⟨oneHandleDirectCoordinateTranspose m k hk ell, ⟨ell, rfl⟩⟩
  have hEell := LinearMap.congr_fun hE Tell
  have hERell := congrArg (fun f => f ell) hER
  exact hEell.trans hERell

theorem targetTransposeVanishing_of_rowSpan
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k)
    (Hspan : OneHandleDirectTargetRowSpan hk hm) :
    OneHandleDirectTargetTransposeVanishing hk hm := by
  obtain ⟨E, hE⟩ := Hspan
  intro ell hell
  have h := congrArg (fun f => f ell) hE
  rw [AddMonoidHom.comp_apply, hell, map_zero] at h
  exact h.symm

theorem targetRowSpan_iff_nonempty_directCorrection
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetRowSpan hk hm ↔
      Nonempty (OneHandleDirectCorrection m k) := by
  rw [← directTargetTransposeVanishing_iff_nonempty_correction hk hm]
  exact ⟨targetTransposeVanishing_of_rowSpan hk hm,
    targetRowSpan_of_transposeVanishing hk hm⟩

theorem targetRowSpan_iff_no_finrank_jump
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetRowSpan hk hm ↔
      oneHandleDirectAugmentedTransposeRank hk hm =
        oneHandleDirectCoordinateTransposeRank m k hk := by
  rw [targetRowSpan_iff_nonempty_directCorrection hk hm,
    nonempty_directCorrection_iff_augmentedTranspose_finrank_eq hk hm]

theorem directTargetTransposeDetected_iff_not_rowSpan
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetTransposeDetected hk hm ↔
      ¬ OneHandleDirectTargetRowSpan hk hm := by
  rw [directTargetTransposeDetected_iff_no_correction hk hm,
    targetRowSpan_iff_nonempty_directCorrection hk hm]

def OneHandleDirectTargetRowSpanSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      OneHandleDirectTargetRowSpan (by omega) hm

theorem targetRowSpanSupply_iff_correctionSupply :
    OneHandleDirectTargetRowSpanSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (targetRowSpan_iff_nonempty_directCorrection (by omega) hm).mp
      (H k hk m hm)
  · exact (targetRowSpan_iff_nonempty_directCorrection (by omega) hm).mpr
      (H k hk m hm)

theorem mpcPivShiftH_two_one_of_targetRowSpan
    (Hspan : OneHandleDirectTargetRowSpanSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (targetRowSpanSupply_iff_correctionSupply.mp Hspan)

#print axioms OneHandleDirectTargetRowSpan
#print axioms targetRowSpan_of_transposeVanishing
#print axioms targetTransposeVanishing_of_rowSpan
#print axioms targetRowSpan_iff_nonempty_directCorrection
#print axioms targetRowSpan_iff_no_finrank_jump
#print axioms directTargetTransposeDetected_iff_not_rowSpan
#print axioms OneHandleDirectTargetRowSpanSupply
#print axioms targetRowSpanSupply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_targetRowSpan

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectRowSpan
