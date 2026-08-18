/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectCokernel
import GQ2.Devissage.ElemDualPack

/-!
# Elementary dual detection of the direct one-handle obstruction

The W249 cokernel is elementary abelian.  Its obstruction therefore vanishes exactly when
every `ZMod 2`-valued additive functional kills it.  Failure of a direct correction is
equivalently witnessed by one such functional.

This replaces W250's complex-character reformulation by finite linear algebra over `𝔽₂`.
It is still a boundary theorem: no uniform vanishing statement is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectF2Dual

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCokernel
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

theorem oneHandleDirectCoordinateCokernel_sq
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (x : OneHandleDirectCoordinateCokernel m k hk) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | _ z =>
    have hz : z ^ 2 = 1 := Subtype.ext (zLayer_sq H z.2)
    change (QuotientGroup.mk' (oneHandleDirectCoordinateSpan m k hk) z) ^ 2 = 1
    rw [← map_pow, hz, map_one]

theorem oneHandleDirectCoordinateCokernel_add_self
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (x : Additive (OneHandleDirectCoordinateCokernel m k hk)) : x + x = 0 := by
  apply Additive.toMul.injective
  simpa [pow_two] using oneHandleDirectCoordinateCokernel_sq hk x.toMul

def OneHandleDirectTargetF2Vanishing
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∀ ell : ElemDual (Additive (OneHandleDirectCoordinateCokernel m k hk)),
    ell (Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm)) = 0

theorem directTargetF2Vanishing_iff_obstruction_eq_one
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetF2Vanishing hk hm ↔
      oneHandleDirectCoordinateObstruction hk hm = 1 := by
  constructor
  · intro h
    by_contra hne
    have ha : Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm) ≠ 0 := by
      simpa using hne
    obtain ⟨ell, hell⟩ := elemDual_separates
      (oneHandleDirectCoordinateCokernel_add_self hk) ha
    exact hell (h ell)
  · intro h ell
    rw [h]
    exact map_zero ell

theorem directTargetF2Vanishing_iff_nonempty_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetF2Vanishing hk hm ↔
      Nonempty (OneHandleDirectCorrection m k) := by
  rw [directTargetF2Vanishing_iff_obstruction_eq_one,
    oneHandleDirectCoordinateObstruction_eq_one_iff,
    ← oneHandleDirectLevelShift_range_eq_coordinateSpan,
    ← nonempty_directCorrection_iff_target_mem_range]

def OneHandleDirectTargetF2Detected
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∃ ell : ElemDual (Additive (OneHandleDirectCoordinateCokernel m k hk)),
    ell (Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm)) ≠ 0

theorem directTargetF2Detected_iff_no_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetF2Detected hk hm ↔
      ¬ Nonempty (OneHandleDirectCorrection m k) := by
  rw [← directTargetF2Vanishing_iff_nonempty_correction hk hm]
  unfold OneHandleDirectTargetF2Detected OneHandleDirectTargetF2Vanishing
  push Not
  rfl

def OneHandleDirectTargetF2VanishingSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      OneHandleDirectTargetF2Vanishing (by omega) hm

theorem directTargetF2Supply_iff_correctionSupply :
    OneHandleDirectTargetF2VanishingSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (directTargetF2Vanishing_iff_nonempty_correction
      (by omega) hm).mp (H k hk m hm)
  · exact (directTargetF2Vanishing_iff_nonempty_correction
      (by omega) hm).mpr (H k hk m hm)

theorem mpcPivShiftH_two_one_of_directTargetF2
    (HF2 : OneHandleDirectTargetF2VanishingSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (directTargetF2Supply_iff_correctionSupply.mp HF2)

#print axioms oneHandleDirectCoordinateCokernel_sq
#print axioms oneHandleDirectCoordinateCokernel_add_self
#print axioms OneHandleDirectTargetF2Vanishing
#print axioms directTargetF2Vanishing_iff_obstruction_eq_one
#print axioms directTargetF2Vanishing_iff_nonempty_correction
#print axioms OneHandleDirectTargetF2Detected
#print axioms directTargetF2Detected_iff_no_correction
#print axioms OneHandleDirectTargetF2VanishingSupply
#print axioms directTargetF2Supply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_directTargetF2

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectF2Dual
