/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectAmbientF2

/-!
# The four elementary-dual coordinate equations

W252 asks for ambient `ZMod 2`-functionals annihilating the direct coordinate span.  This file
proves that condition is exactly the conjunction of four row equations, one for each of the
`A`, `B`, `C`, and `D` shift families from W248.

Consequently the direct successor exists exactly when every functional satisfying those four
equations kills the target.  No such target-vanishing theorem is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateF2

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectAmbientF2
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

private def oneHandleDirectF2Kernel {k : ℕ}
    (ell : ElemDual (Additive (zLayer H k))) : Subgroup (zLayer H k) :=
  ell.ker.toSubgroup'

private theorem mem_oneHandleDirectF2Kernel_iff {k : ℕ}
    (ell : ElemDual (Additive (zLayer H k))) (z : zLayer H k) :
    z ∈ oneHandleDirectF2Kernel ell ↔ ell (Additive.ofMul z) = 0 := by
  rfl

def OneHandleDirectCoordinateRowsAnnihilate
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (ell : ElemDual (Additive (zLayer H k))) : Prop :=
  (∀ x : oneHandleDirectLambdaImage (k - 1) (k + 1),
      ell (Additive.ofMul (oneHandleDirectShiftA m k hk x)) = 0) ∧
  (∀ x : oneHandleDirectLambdaImage (k - 1) (k + 1),
      ell (Additive.ofMul (oneHandleDirectShiftB m k hk x)) = 0) ∧
  (∀ x : oneHandleDirectNeutralLambdaImage (k - 1) (k + 1),
      ell (Additive.ofMul (oneHandleDirectShiftC m k hk x)) = 0) ∧
  (∀ x : oneHandleDirectLambdaImage (k - 1) (k + 1),
      ell (Additive.ofMul (oneHandleDirectShiftD m k hk x)) = 0)

theorem coordinateRowsAnnihilate_iff_spanAnnihilates
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (ell : ElemDual (Additive (zLayer H k))) :
    OneHandleDirectCoordinateRowsAnnihilate m k hk ell ↔
      OneHandleDirectSpanAnnihilates (m := m) hk ell := by
  constructor
  · rintro ⟨hA, hB, hC, hD⟩ z hz
    have hspan : oneHandleDirectCoordinateSpan m k hk ≤
        oneHandleDirectF2Kernel ell := by
      apply sup_le
      · apply sup_le
        · rintro y ⟨x, rfl⟩
          exact (mem_oneHandleDirectF2Kernel_iff ell _).mpr (hA x)
        · rintro y ⟨x, rfl⟩
          exact (mem_oneHandleDirectF2Kernel_iff ell _).mpr (hB x)
      · apply sup_le
        · rintro y ⟨x, rfl⟩
          exact (mem_oneHandleDirectF2Kernel_iff ell _).mpr (hC x)
        · rintro y ⟨x, rfl⟩
          exact (mem_oneHandleDirectF2Kernel_iff ell _).mpr (hD x)
    exact (mem_oneHandleDirectF2Kernel_iff ell z).mp (hspan hz)
  · intro hann
    refine ⟨fun x ↦ hann _ ?_, fun x ↦ hann _ ?_,
      fun x ↦ hann _ ?_, fun x ↦ hann _ ?_⟩
    · exact (show (oneHandleDirectShiftA m k hk).range ≤
          oneHandleDirectCoordinateSpan m k hk from
        le_trans le_sup_left le_sup_left) ⟨x, rfl⟩
    · exact (show (oneHandleDirectShiftB m k hk).range ≤
          oneHandleDirectCoordinateSpan m k hk from
        le_trans le_sup_right le_sup_left) ⟨x, rfl⟩
    · exact (show (oneHandleDirectShiftC m k hk).range ≤
          oneHandleDirectCoordinateSpan m k hk from
        le_trans le_sup_left le_sup_right) ⟨x, rfl⟩
    · exact (show (oneHandleDirectShiftD m k hk).range ≤
          oneHandleDirectCoordinateSpan m k hk from
        le_trans le_sup_right le_sup_right) ⟨x, rfl⟩

def OneHandleDirectTargetCoordinateF2Vanishing
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∀ ell : ElemDual (Additive (zLayer H k)),
    OneHandleDirectCoordinateRowsAnnihilate m k hk ell →
      ell (Additive.ofMul (oneHandleDirectLevelTarget hm)) = 0

theorem directTargetCoordinateF2Vanishing_iff_nonempty_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetCoordinateF2Vanishing hk hm ↔
      Nonempty (OneHandleDirectCorrection m k) := by
  rw [← directTargetAmbientF2Vanishing_iff_nonempty_correction hk hm]
  constructor <;> intro Hvan ell hell
  · exact Hvan ell ((coordinateRowsAnnihilate_iff_spanAnnihilates m k hk ell).mpr hell)
  · exact Hvan ell ((coordinateRowsAnnihilate_iff_spanAnnihilates m k hk ell).mp hell)

def OneHandleDirectTargetCoordinateF2Detected
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∃ ell : ElemDual (Additive (zLayer H k)),
    OneHandleDirectCoordinateRowsAnnihilate m k hk ell ∧
      ell (Additive.ofMul (oneHandleDirectLevelTarget hm)) ≠ 0

theorem directTargetCoordinateF2Detected_iff_no_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetCoordinateF2Detected hk hm ↔
      ¬ Nonempty (OneHandleDirectCorrection m k) := by
  rw [← directTargetCoordinateF2Vanishing_iff_nonempty_correction hk hm]
  unfold OneHandleDirectTargetCoordinateF2Detected
  unfold OneHandleDirectTargetCoordinateF2Vanishing
  push Not
  rfl

def OneHandleDirectTargetCoordinateF2VanishingSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      OneHandleDirectTargetCoordinateF2Vanishing (by omega) hm

theorem directTargetCoordinateF2Supply_iff_correctionSupply :
    OneHandleDirectTargetCoordinateF2VanishingSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (directTargetCoordinateF2Vanishing_iff_nonempty_correction
      (by omega) hm).mp (H k hk m hm)
  · exact (directTargetCoordinateF2Vanishing_iff_nonempty_correction
      (by omega) hm).mpr (H k hk m hm)

theorem mpcPivShiftH_two_one_of_directTargetCoordinateF2
    (HF2 : OneHandleDirectTargetCoordinateF2VanishingSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (directTargetCoordinateF2Supply_iff_correctionSupply.mp HF2)

#print axioms OneHandleDirectCoordinateRowsAnnihilate
#print axioms coordinateRowsAnnihilate_iff_spanAnnihilates
#print axioms OneHandleDirectTargetCoordinateF2Vanishing
#print axioms directTargetCoordinateF2Vanishing_iff_nonempty_correction
#print axioms OneHandleDirectTargetCoordinateF2Detected
#print axioms directTargetCoordinateF2Detected_iff_no_correction
#print axioms OneHandleDirectTargetCoordinateF2VanishingSupply
#print axioms directTargetCoordinateF2Supply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_directTargetCoordinateF2

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateF2
