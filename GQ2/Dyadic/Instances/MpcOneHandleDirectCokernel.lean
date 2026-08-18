/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan

/-!
# The finite cokernel obstruction for the direct one-handle span

W248 identifies the direct correction range with four literal coordinate rows inside the
finite central layer.  This file quotients by that span and packages the remaining successor
question as one element of a finite cokernel.

The obstruction vanishes exactly when the direct successor exists.  No vanishing theorem is
asserted here; the point is to isolate the final target-specific graded calculation as a
single finite class.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectCokernel

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectCoordinateSpan
open GQ2.Roe.Labute

private abbrev H := DM 2 1

noncomputable instance oneHandleDirectZLayer_isMulCommutative (k : ℕ) :
    IsMulCommutative (zLayer H k) where
  is_comm := ⟨fun (x y : zLayer H k) ↦
    Subtype.ext (zLayer_commute x.2 y.1).eq⟩

noncomputable instance oneHandleDirectZLayer_finite (k : ℕ) :
    Finite (zLayer H k) := by
  letI : Finite (levelQuot H (k + 1)) :=
    finite_levelQuot H (dmFinsetTopGen 2 1) (isProP_DM 2 1) (k + 1)
  exact Finite.of_injective Subtype.val Subtype.val_injective

abbrev OneHandleDirectCoordinateCokernel
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :=
  (zLayer H k) ⧸ oneHandleDirectCoordinateSpan m k hk

noncomputable instance oneHandleDirectCoordinateCokernel_finite
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    Finite (OneHandleDirectCoordinateCokernel m k hk) := by
  dsimp [OneHandleDirectCoordinateCokernel]
  infer_instance

def oneHandleDirectCoordinateObstruction
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    OneHandleDirectCoordinateCokernel m k hk :=
  QuotientGroup.mk' (oneHandleDirectCoordinateSpan m k hk)
    (oneHandleDirectLevelTarget hm)

theorem oneHandleDirectCoordinateObstruction_eq_one_iff
    {m : Fin (coreRank 1) → H} {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    oneHandleDirectCoordinateObstruction hk hm = 1 ↔
      oneHandleDirectLevelTarget hm ∈
        oneHandleDirectCoordinateSpan m k hk := by
  exact QuotientGroup.eq_one_iff _

def OneHandleDirectCoordinateObstructionVanishing : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      oneHandleDirectCoordinateObstruction (by omega) hm = 1

theorem directCoordinateObstructionVanishing_iff_spanSupply :
    OneHandleDirectCoordinateObstructionVanishing ↔
      OneHandleDirectCoordinateSpanSupply := by
  constructor <;> intro Hobs k hk m hm
  · exact (oneHandleDirectCoordinateObstruction_eq_one_iff (by omega) hm).mp
      (Hobs k hk m hm)
  · exact (oneHandleDirectCoordinateObstruction_eq_one_iff (by omega) hm).mpr
      (Hobs k hk m hm)

theorem mpcPivShiftH_two_one_of_directCoordinateObstruction
    (Hobs : OneHandleDirectCoordinateObstructionVanishing) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_directCoordinateSpan
    (directCoordinateObstructionVanishing_iff_spanSupply.mp Hobs)

#print axioms oneHandleDirectZLayer_isMulCommutative
#print axioms oneHandleDirectZLayer_finite
#print axioms OneHandleDirectCoordinateCokernel
#print axioms oneHandleDirectCoordinateCokernel_finite
#print axioms oneHandleDirectCoordinateObstruction
#print axioms oneHandleDirectCoordinateObstruction_eq_one_iff
#print axioms OneHandleDirectCoordinateObstructionVanishing
#print axioms directCoordinateObstructionVanishing_iff_spanSupply
#print axioms mpcPivShiftH_two_one_of_directCoordinateObstruction

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectCokernel
