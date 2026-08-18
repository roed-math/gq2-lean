/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenFinitePacket
import GQ2.Dyadic.Instances.MpcMarkedUniform

/-!
# The compact class-seven packets form one raw-cost fiber

The four compact factors of a legal one-handle relative lift form an unrestricted marked-cost
source at depth five.  Expanding the moved compact relator proves that its raw cost is exactly
the fixed class-six defect.  Hence every attained compact packet lies in one affine fiber of
the compact raw-cost map, and the pointwise ratio of any two sources lies in its kernel.

This sharpens W276's finite search: variation of the ordinary one-handle obstruction is driven
only by this named compact raw-cost kernel.  It does not assert that the induced connecting map
on the kernel vanishes or that its image contains the reference obstruction.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactCostFiber

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad
open GQ2.Dyadic.Instances.MpcMk
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcOneHandleClassSixCompactLift
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactSupply
open GQ2.Roe.Labute

private theorem compactFactor_depth (E : OneHandleC7RelativeLift)
    (i : Fin (coreRank 1)) :
    E.compactFactors i ∈ twoCentralSeries (DM 2 0 : Type) 5 := by
  have hmap := map_twoCentralSeries_le
    (dmForgetHandles 2 1).toMonoidHom
    (dmForgetHandles 2 1).continuous_toFun 5
    ⟨E.factors i, E.depth i, rfl⟩
  simpa [E.forget i] using hmap

def compactRawSource (E : OneHandleC7RelativeLift) : MpcMkRawSource 5 :=
  (⟨E.compactFactors 0, compactFactor_depth E 0⟩,
    ⟨E.compactFactors 1, compactFactor_depth E 1⟩,
    ⟨E.compactFactors 2, compactFactor_depth E 2⟩,
    ⟨E.compactFactors 3, compactFactor_depth E 3⟩)

def compactCorrectedTuple (E : OneHandleC7RelativeLift) :
    (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type) :=
  (compactC6Tuple.1 * E.compactFactors 0,
    compactC6Tuple.2.1 * E.compactFactors 1,
    compactC6Tuple.2.2.1 * E.compactFactors 2,
    compactC6Tuple.2.2.2 * E.compactFactors 3)

private theorem compactCorrectedMark (E : OneHandleC7RelativeLift) :
    (fun i ↦ compactC6Mark i * E.compactFactors i) =
      fullMark
        (mpcWordLetA (compactCorrectedTuple E).1)
        (mpcWordLetB (compactCorrectedTuple E).2.1)
        (mpcWordLetC (compactCorrectedTuple E).2.2.1)
        (mpcWordLetD (compactCorrectedTuple E).2.2.2)
        (fun _ ↦ 1) (fun _ ↦ 1) := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simp [compactCorrectedTuple, compactC6Mark, compactW5Mark,
      compactC6Factors, compactC6Tuple, mpcWordLetA]
    group
  · simp [compactCorrectedTuple, compactC6Mark, compactW5Mark,
      compactC6Factors, compactC6Tuple, mpcWordLetB]
    group
  · simp [compactCorrectedTuple, compactC6Mark, compactW5Mark,
      compactC6Factors, compactC6Tuple, mpcWordLetC]
    group
  · simp [compactCorrectedTuple, compactC6Mark, compactW5Mark,
      compactC6Factors, compactC6Tuple, mpcWordLetD]
    group
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [compactCorrectedTuple, compactC6Mark, compactW5Mark,
        compactC6Factors, mHandleIdx_coordU, mHandleIdx_coordV]
    · calc
        E.compactFactors (handleIdxU j) =
            dmForgetHandles 2 1 (E.factors (handleIdxU j)) :=
          (E.forget (handleIdxU j)).symm
        _ = 1 := by rw [E.handleU j, map_one]
    · calc
        E.compactFactors (handleIdxV j) =
            dmForgetHandles 2 1 (E.factors (handleIdxV j)) :=
          (E.forget (handleIdxV j)).symm
        _ = 1 := by rw [E.handleV j, map_one]

theorem compactCorrectedTuple_relator_mem (E : OneHandleC7RelativeLift) :
    mpcLadDefect (compactCorrectedTuple E) ∈
      twoCentralSeries (DM 2 0 : Type) 7 := by
  have heq : mRelWord 2 (fun i ↦ compactC6Mark i * E.compactFactors i) =
      mpcLadDefect (compactCorrectedTuple E) := by
    rw [compactCorrectedMark E]
    simp [mRelWord, handleWord_one, mpcLadDefect]
  rw [← heq]
  exact E.compactRelator

private theorem compactRawCost_value (E : OneHandleC7RelativeLift) :
    levelMk (DM 2 0 : Type) 7
        (mpcBldIncr compactC6Tuple.2.1 compactC6Tuple.2.2.2
          (E.compactFactors 0) (E.compactFactors 1)
          (E.compactFactors 2) (E.compactFactors 3)) =
      levelMk (DM 2 0 : Type) 7 (mpcLadDefect compactC6Tuple) := by
  have hmove : levelMk (DM 2 0 : Type) 7
        (mpcLadDefect (compactCorrectedTuple E)) =
      levelMk (DM 2 0 : Type) 7
        (mpcLadDefect compactC6Tuple *
          mpcBldIncr compactC6Tuple.2.1 compactC6Tuple.2.2.2
            (E.compactFactors 0) (E.compactFactors 1)
            (E.compactFactors 2) (E.compactFactors 3)) := by
    simpa [compactCorrectedTuple] using mpcLad_defect_move
      (j := 5) compactC6Tuple_mem.1.1
      compactC6Tuple_mem.2.2.1.1.1
      (twoCentralSeries_antitone (G := (DM 2 0 : Type))
        (by omega : 2 ≤ 5) (compactFactor_depth E 0))
      (compactFactor_depth E 0) (compactFactor_depth E 1)
      (twoCentralSeries_antitone (G := (DM 2 0 : Type))
        (by omega : 2 ≤ 5) (compactFactor_depth E 2))
      (compactFactor_depth E 2) (compactFactor_depth E 3)
  have hzero : levelMk (DM 2 0 : Type) 7
      (mpcLadDefect (compactCorrectedTuple E)) = 1 :=
    (lim_mem_twoCentralSeries_iff_levelMk 7 _).mp
      (compactCorrectedTuple_relator_mem E)
  rw [hzero] at hmove
  have hz : levelMk (DM 2 0 : Type) 7
      (mpcBldIncr compactC6Tuple.2.1 compactC6Tuple.2.2.2
        (E.compactFactors 0) (E.compactFactors 1)
        (E.compactFactors 2) (E.compactFactors 3)) ∈
      zLayer (DM 2 0 : Type) 6 :=
    mpcLad_incr_mem_zLayer _ _ (compactFactor_depth E 0)
      (compactFactor_depth E 1) (compactFactor_depth E 2)
      (compactFactor_depth E 3)
  have hprod : levelMk (DM 2 0 : Type) 7 (mpcLadDefect compactC6Tuple) *
      levelMk (DM 2 0 : Type) 7
        (mpcBldIncr compactC6Tuple.2.1 compactC6Tuple.2.2.2
          (E.compactFactors 0) (E.compactFactors 1)
          (E.compactFactors 2) (E.compactFactors 3)) = 1 := by
    simpa [compactCorrectedTuple] using hmove.symm
  symm
  calc
    levelMk (DM 2 0 : Type) 7 (mpcLadDefect compactC6Tuple) =
        (levelMk (DM 2 0 : Type) 7
          (mpcBldIncr compactC6Tuple.2.1 compactC6Tuple.2.2.2
            (E.compactFactors 0) (E.compactFactors 1)
            (E.compactFactors 2) (E.compactFactors 3)))⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    _ = _ := zLayer_inv_self hz

theorem compactRawCost_eq_defect (E : OneHandleC7RelativeLift) :
    mpcMkRawCost 5 (by omega) compactC6Tuple.2.1 compactC6Tuple.2.2.2
        (compactRawSource E) =
      mpcMkDefectTop 5 compactC6Tuple compactC6Tuple_mem := by
  apply Subtype.ext
  rw [mpcMkRawCost_apply]
  exact compactRawCost_value E

def compactRawDifference (E F : OneHandleC7RelativeLift) : MpcMkRawSource 5 :=
  (compactRawSource E)⁻¹ * compactRawSource F

theorem compactRawDifference_mem_costKernel (E F : OneHandleC7RelativeLift) :
    compactRawDifference E F ∈
      (mpcMkRawCost 5 (by omega) compactC6Tuple.2.1
        compactC6Tuple.2.2.2).ker := by
  rw [MonoidHom.mem_ker, compactRawDifference, map_mul, map_inv,
    compactRawCost_eq_defect E, compactRawCost_eq_defect F, inv_mul_cancel]

theorem compactRawCost_fiber_eq :
    Set.range compactRawSource ⊆
      {u | mpcMkRawCost 5 (by omega) compactC6Tuple.2.1
        compactC6Tuple.2.2.2 u =
          mpcMkDefectTop 5 compactC6Tuple compactC6Tuple_mem} := by
  rintro _ ⟨E, rfl⟩
  exact compactRawCost_eq_defect E

#print axioms compactRawSource
#print axioms compactCorrectedTuple_relator_mem
#print axioms compactRawCost_eq_defect
#print axioms compactRawDifference_mem_costKernel
#print axioms compactRawCost_fiber_eq

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactCostFiber
