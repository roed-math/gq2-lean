/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectF2Dual

/-!
# Ambient elementary-dual detection of the direct one-handle obstruction

W251 tests the obstruction in the finite coordinate cokernel.  This file pulls the test back
to the ambient central layer.  A direct correction exists exactly when every `ZMod 2`-valued
functional annihilating the four-coordinate span also kills the target.

The complementary detector is now an ordinary functional on the central layer, subject only
to four span-annihilation conditions.  No target vanishing is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectAmbientF2

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCokernel
open GQ2.Dyadic.Instances.MpcOneHandleDirectF2Dual
open GQ2.FoxH GQ2.Roe.Labute
open scoped IsMulCommutative

private abbrev H := DM 2 1

def OneHandleDirectSpanAnnihilates
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (ell : ElemDual (Additive (zLayer H k))) : Prop :=
  ∀ z : zLayer H k, z ∈ oneHandleDirectCoordinateSpan m k hk →
    ell (Additive.ofMul z) = 0

def OneHandleDirectTargetAmbientF2Vanishing
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∀ ell : ElemDual (Additive (zLayer H k)),
    OneHandleDirectSpanAnnihilates (m := m) hk ell →
      ell (Additive.ofMul (oneHandleDirectLevelTarget hm)) = 0

private def oneHandleDirectCoordinateQuotientAdd
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k) :
    Additive (zLayer H k) →+
      Additive (OneHandleDirectCoordinateCokernel m k hk) :=
  (QuotientGroup.mk' (oneHandleDirectCoordinateSpan m k hk)).toAdditive

theorem directTargetAmbientF2Vanishing_iff_target_mem_span
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetAmbientF2Vanishing hk hm ↔
      oneHandleDirectLevelTarget hm ∈
        oneHandleDirectCoordinateSpan m k hk := by
  constructor
  · intro Hvan
    by_contra hmem
    have hobs : oneHandleDirectCoordinateObstruction hk hm ≠ 1 := by
      intro hzero
      exact hmem ((oneHandleDirectCoordinateObstruction_eq_one_iff hk hm).mp hzero)
    have hadd : Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm) ≠ 0 := by
      simpa using hobs
    obtain ⟨qell, hqell⟩ := elemDual_separates
      (oneHandleDirectCoordinateCokernel_add_self hk) hadd
    let ell : ElemDual (Additive (zLayer H k)) :=
      ((qell : Additive (OneHandleDirectCoordinateCokernel m k hk) →+ ZMod 2).comp
        (oneHandleDirectCoordinateQuotientAdd hk) :
          ElemDual (Additive (zLayer H k)))
    have hann : OneHandleDirectSpanAnnihilates (m := m) hk ell := by
      intro z hz
      change qell (Additive.ofMul
        (QuotientGroup.mk' (oneHandleDirectCoordinateSpan m k hk) z)) = 0
      have hq : QuotientGroup.mk' (oneHandleDirectCoordinateSpan m k hk) z = 1 :=
        (QuotientGroup.eq_one_iff z).mpr hz
      rw [hq]
      exact map_zero qell
    exact hqell (Hvan ell hann)
  · intro hmem ell hann
    exact hann _ hmem

theorem directTargetAmbientF2Vanishing_iff_nonempty_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetAmbientF2Vanishing hk hm ↔
      Nonempty (OneHandleDirectCorrection m k) := by
  rw [directTargetAmbientF2Vanishing_iff_target_mem_span,
    ← oneHandleDirectLevelShift_range_eq_coordinateSpan,
    ← nonempty_directCorrection_iff_target_mem_range]

def OneHandleDirectTargetAmbientF2Detected
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∃ ell : ElemDual (Additive (zLayer H k)),
    OneHandleDirectSpanAnnihilates (m := m) hk ell ∧
      ell (Additive.ofMul (oneHandleDirectLevelTarget hm)) ≠ 0

theorem directTargetAmbientF2Detected_iff_no_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetAmbientF2Detected hk hm ↔
      ¬ Nonempty (OneHandleDirectCorrection m k) := by
  rw [← directTargetAmbientF2Vanishing_iff_nonempty_correction hk hm]
  unfold OneHandleDirectTargetAmbientF2Detected
  unfold OneHandleDirectTargetAmbientF2Vanishing
  push Not
  rfl

def OneHandleDirectTargetAmbientF2VanishingSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      OneHandleDirectTargetAmbientF2Vanishing (by omega) hm

theorem directTargetAmbientF2Supply_iff_correctionSupply :
    OneHandleDirectTargetAmbientF2VanishingSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (directTargetAmbientF2Vanishing_iff_nonempty_correction
      (by omega) hm).mp (H k hk m hm)
  · exact (directTargetAmbientF2Vanishing_iff_nonempty_correction
      (by omega) hm).mpr (H k hk m hm)

theorem mpcPivShiftH_two_one_of_directTargetAmbientF2
    (HF2 : OneHandleDirectTargetAmbientF2VanishingSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (directTargetAmbientF2Supply_iff_correctionSupply.mp HF2)

#print axioms OneHandleDirectSpanAnnihilates
#print axioms OneHandleDirectTargetAmbientF2Vanishing
#print axioms directTargetAmbientF2Vanishing_iff_target_mem_span
#print axioms directTargetAmbientF2Vanishing_iff_nonempty_correction
#print axioms OneHandleDirectTargetAmbientF2Detected
#print axioms directTargetAmbientF2Detected_iff_no_correction
#print axioms OneHandleDirectTargetAmbientF2VanishingSupply
#print axioms directTargetAmbientF2Supply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_directTargetAmbientF2

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectAmbientF2
