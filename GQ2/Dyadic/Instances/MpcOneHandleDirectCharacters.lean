/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectCokernel
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Character detection of the direct one-handle obstruction

The W249 obstruction is an element of a finite abelian cokernel.  Finite Pontryagin duality
therefore says that it vanishes exactly when every additive complex character evaluates to
one.  Dually, failure of a direct successor is equivalent to one character detecting the
obstruction.

This is a scalar reformulation, not a vanishing theorem.  It identifies the precise finite
functional which any remaining positive or negative calculation must control.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectCharacters

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCokernel

open scoped IsMulCommutative

private abbrev H := DM 2 1

def OneHandleDirectTargetCharacterVanishing
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∀ chi : AddChar (Additive (OneHandleDirectCoordinateCokernel m k hk)) ℂ,
    chi (Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm)) = 1

theorem directTargetCharacterVanishing_iff_obstruction_eq_one
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetCharacterVanishing hk hm ↔
      oneHandleDirectCoordinateObstruction hk hm = 1 := by
  change (∀ chi : AddChar
      (Additive (OneHandleDirectCoordinateCokernel m k hk)) ℂ,
      chi (Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm)) = 1) ↔ _
  change (∀ chi : AddChar
      (Additive (OneHandleDirectCoordinateCokernel m k hk)) ℂ,
      chi (Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm)) = 1) ↔
    Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm) = 0
  exact AddChar.forall_apply_eq_zero
    (a := Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm))

theorem directTargetCharacterVanishing_iff_nonempty_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetCharacterVanishing hk hm ↔
      Nonempty (OneHandleDirectCorrection m k) := by
  rw [directTargetCharacterVanishing_iff_obstruction_eq_one,
    oneHandleDirectCoordinateObstruction_eq_one_iff,
    ← oneHandleDirectLevelShift_range_eq_coordinateSpan,
    ← nonempty_directCorrection_iff_target_mem_range]

def OneHandleDirectTargetCharacterDetected
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) : Prop :=
  ∃ chi : AddChar (Additive (OneHandleDirectCoordinateCokernel m k hk)) ℂ,
    chi (Additive.ofMul (oneHandleDirectCoordinateObstruction hk hm)) ≠ 1

theorem directTargetCharacterDetected_iff_no_correction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectTargetCharacterDetected hk hm ↔
      ¬ Nonempty (OneHandleDirectCorrection m k) := by
  rw [← directTargetCharacterVanishing_iff_nonempty_correction hk hm]
  unfold OneHandleDirectTargetCharacterDetected
  unfold OneHandleDirectTargetCharacterVanishing
  push Not
  rfl

def OneHandleDirectTargetCharacterVanishingSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      OneHandleDirectTargetCharacterVanishing (by omega) hm

theorem directTargetCharacterSupply_iff_correctionSupply :
    OneHandleDirectTargetCharacterVanishingSupply ↔
      OneHandleDirectCorrectionSupply := by
  constructor <;> intro H k hk m hm
  · exact (directTargetCharacterVanishing_iff_nonempty_correction
      (by omega) hm).mp (H k hk m hm)
  · exact (directTargetCharacterVanishing_iff_nonempty_correction
      (by omega) hm).mpr (H k hk m hm)

theorem mpcPivShiftH_two_one_of_directTargetCharacters
    (Hchars : OneHandleDirectTargetCharacterVanishingSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (directTargetCharacterSupply_iff_correctionSupply.mp Hchars)

#print axioms OneHandleDirectTargetCharacterVanishing
#print axioms directTargetCharacterVanishing_iff_obstruction_eq_one
#print axioms directTargetCharacterVanishing_iff_nonempty_correction
#print axioms OneHandleDirectTargetCharacterDetected
#print axioms directTargetCharacterDetected_iff_no_correction
#print axioms OneHandleDirectTargetCharacterVanishingSupply
#print axioms directTargetCharacterSupply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_directTargetCharacters

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectCharacters
