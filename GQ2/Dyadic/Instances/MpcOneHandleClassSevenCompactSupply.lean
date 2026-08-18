/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
import GQ2.Dyadic.Instances.MpcMarkedUniform

/-!
# Compact class-seven supply beneath the explicit one-handle marking

The explicit W267 one-handle marking forgets to the compact class-six marking constructed
from the same four sparse factors.  This module proves that the latter marking has full marked
class-seven supply.  The proof uses the checked class-six certificate to identify its exact
cost witness, then applies the uniform marked successor theorem at that named point.

Thus the compact part of the W6-to-W7 correction is unconditional.  What remains in the
one-handle lane is to lift a compact correction with the direct character and pivot-row
constraints and cancel the resulting handle-relative residual; no ambient class-seven
p-quotient computation is needed for this reduction.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactSupply

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcLad
open GQ2.Dyadic.Instances.MpcMk
open GQ2.Dyadic.Instances.MpcMkC6
open GQ2.Dyadic.Instances.MpcOrb
open GQ2.Dyadic.Instances.MpcSx
open GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcC6WeightedTraceFinal
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleClassSixCompactLift
open GQ2.Dyadic.Instances.MpcOneHandleClassSixCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Roe.Labute

private abbrev H := DM 2 1

/-- The explicit compact class-six correction, packaged in the exact marked cost domain. -/
def compactC6Cost : MpcMkCostDomain 4 :=
  (⟨mpcMkC6Us, mpcMkC6Us_mem⟩,
    ⟨mpcMkC6Ut, mpcMkC6Ut_mem⟩,
    ⟨mpcMkC6Um, mpcMkC6Um_mem⟩,
    ⟨mpcMkC6Un, mpcMkC6Un_mem⟩)

/-- The checked class-six certificate says that the displayed cost is the W5 defect. -/
theorem compactC6Cost_eq_defect :
    mpcMkCost 4 (by omega) mpcFvW5.2.1 mpcFvW5.2.2.2 compactC6Cost =
      mpcMkDefectTop 4 mpcFvW5 mpcFv_w5_mem := by
  apply Subtype.ext
  have hone : levelMk (DM 2 0 : Type) 6
      (mpcLadDefect mpcFvW5 *
        mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2
          mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un) = 1 :=
    mpcMkC6_certificateKill
  have hz : levelMk (DM 2 0 : Type) 6
      (mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2
        mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un) ∈
        zLayer (DM 2 0 : Type) 5 :=
    mpcLad_incr_mem_zLayer _ _ mpcMkC6Us_mem.2 mpcMkC6Ut_mem.2
      mpcMkC6Um_mem.2 mpcMkC6Un_mem.2
  change levelMk (DM 2 0 : Type) 6
      (mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2
        mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un) =
    levelMk (DM 2 0 : Type) 6 (mpcLadDefect mpcFvW5)
  have hone' : levelMk (DM 2 0 : Type) 6 (mpcLadDefect mpcFvW5) *
      levelMk (DM 2 0 : Type) 6
        (mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2
          mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un) = 1 := by
    simpa only [map_mul] using hone
  symm
  calc
    levelMk (DM 2 0 : Type) 6 (mpcLadDefect mpcFvW5) =
        (levelMk (DM 2 0 : Type) 6
          (mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2
            mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un))⁻¹ :=
      eq_inv_of_mul_eq_one_left hone'
    _ = levelMk (DM 2 0 : Type) 6
        (mpcBldIncr mpcFvW5.2.1 mpcFvW5.2.2.2
          mpcMkC6Us mpcMkC6Ut mpcMkC6Um mpcMkC6Un) := zLayer_inv_self hz

/-- The marked advance by the displayed cost is literally the named compact C6 tuple. -/
theorem compactC6Advance_eq :
    mpcMkAdvance 4 mpcFvW5 compactC6Cost = compactC6Tuple := rfl

/-- The explicit compact W5 head remains in the marked carrier. -/
theorem mpcFvW5_markedHead : MpcMkMarkedHead mpcFvW5 := by
  simpa [MpcMkMarkedHead, mpcFvW5, mpcLadW4] using mpcMk_markedHead_w4

/-- The exact compact image of the one-handle W6 marking has full class-seven supply. -/
theorem compactC7_fullSupply : MpcMkFullSupply 5 compactC6Tuple := by
  have hnext := mpcMk_secondary_mem_costRange (by omega) mpcFv_w5_mem
    mpcFvW5_markedHead compactC6Cost compactC6Cost_eq_defect
  have hbase := mpcMk_cost_succ_base_indep (by omega)
    mpcFvW5.2.1 mpcFvW5.2.2.2 compactC6Cost.2.1.2.2
      compactC6Cost.2.2.2.2.2
  have hbase' :
      mpcMkCost 5 (by omega) compactC6Tuple.2.1 compactC6Tuple.2.2.2 =
        mpcMkCost 5 (by omega) mpcFvW5.2.1 mpcFvW5.2.2.2 := by
    simpa [compactC6Tuple, compactC6Cost, mpcFvW5] using hbase
  have hnext' : mpcMkDefectTop 5 compactC6Tuple compactC6Tuple_mem ∈
      MonoidHom.range
        (mpcMkCost 5 (by omega) mpcFvW5.2.1 mpcFvW5.2.2.2) := by
    simpa only [compactC6Advance_eq] using hnext
  apply (mpcMk_fullSupply_iff_mem_costRange (by omega) compactC6Tuple_mem).mpr
  rw [hbase']
  exact hnext'

/-! ## The exact compact image of the W6 marking -/

private theorem dmForgetHandles_eval_mRel :
    dmForgetHandles 2 1
        (MpcC6WeightedChecker.CWord.eval oneHandleVal
          MpcC6WeightedChecker.CWord.mRel) = 1 := by
  rw [MpcC6WeightedChecker.CWord.eval_mRel, map_mWord]
  simpa [oneHandleVal, dmForgetHandles_dmA, dmForgetHandles_dmB,
    dmForgetHandles_dmC, dmForgetHandles_dmD] using mpcOrb_relation

theorem dmForgetHandles_oneHandleRelationX :
    dmForgetHandles 2 1 oneHandleRelationX = 1 := by
  simp only [oneHandleRelationX, relationXWord,
    MpcC6WeightedChecker.CWord.eval, commP, map_mul, map_pow, map_inv]
  simp only [dmForgetHandles_eval_mRel]
  simp

theorem dmForgetHandles_oneHandleRelationY :
    dmForgetHandles 2 1 oneHandleRelationY = 1 := by
  simp only [oneHandleRelationY, relationYWord,
    MpcC6WeightedChecker.CWord.eval, commP, map_mul, map_pow, map_inv]
  simp only [dmForgetHandles_eval_mRel]
  simp

theorem dmForgetHandles_oneHandleRelationFactors (i : Fin (coreRank 1)) :
    dmForgetHandles 2 1 (oneHandleRelationFactors i) = 1 := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simpa [oneHandleRelationFactors] using dmForgetHandles_oneHandleRelationX
  · simpa [oneHandleRelationFactors] using dmForgetHandles_oneHandleRelationX
  · simpa [oneHandleRelationFactors] using dmForgetHandles_oneHandleRelationY
  · simp [oneHandleRelationFactors]
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleRelationFactors, mHandleIdx_coordU, mHandleIdx_coordV]

theorem dmForgetHandles_oneHandleC6CorrectedFactors (i : Fin (coreRank 1)) :
    dmForgetHandles 2 1 (oneHandleC6CorrectedFactors i) = compactC6Factors i := by
  rw [oneHandleC6CorrectedFactors, map_mul,
    dmForgetHandles_oneHandleC6Factors,
    dmForgetHandles_oneHandleRelationFactors, mul_one]

theorem dmForgetHandles_oneHandleW6Mark (i : Fin (coreRank 1)) :
    dmForgetHandles 2 1 (oneHandleW6Mark i) = compactC6Mark i := by
  rw [oneHandleW6Mark, oneHandleDirectModify, map_mul,
    dmForgetHandles_oneHandleW5Mark,
    dmForgetHandles_oneHandleC6CorrectedFactors]
  rfl

theorem dmForgetHandles_oneHandleW6Relator :
    dmForgetHandles 2 1 (mRelWord 2 oneHandleW6Mark) =
      mRelWord 2 compactC6Mark := by
  rw [map_mRelWord]
  congr 1
  funext i
  exact dmForgetHandles_oneHandleW6Mark i

/-! ## Exact lifts for the three row-free slots -/

/-- Every compact marked factor has an exact depth-preserving one-handle lift.  Its character
is automatically trivial because the orientation factors through handle-forgetting. -/
theorem exists_oneHandleDepthChiLift {j : ℕ} {x : DM 2 0}
    (hx : x ∈ mpcSxKill j) :
    ∃ y : H, y ∈ twoCentralSeries H j ∧ chiM 2 1 y = 1 ∧
      dmForgetHandles 2 1 y = x := by
  have hmap :
      (twoCentralSeries H j).map (dmForgetHandles 2 1).toMonoidHom =
        twoCentralSeries (DM 2 0 : Type) j :=
    map_twoCentralSeries_eq (dmForgetHandles 2 1).toMonoidHom
      (dmForgetHandles 2 1).continuous_toFun
      (dmForgetHandles_surjective 2 1) j
  have hxmap : x ∈
      (twoCentralSeries H j).map (dmForgetHandles 2 1).toMonoidHom := by
    rw [hmap]
    exact hx.2
  obtain ⟨y, hy, hyx⟩ := hxmap
  change dmForgetHandles 2 1 y = x at hyx
  refine ⟨y, hy, ?_, hyx⟩
  rw [← chiM_dmForgetHandles 2 1, hyx]
  exact mpcSx_marked_chi hx.1

#print axioms compactC6Cost_eq_defect
#print axioms compactC6Advance_eq
#print axioms mpcFvW5_markedHead
#print axioms compactC7_fullSupply
#print axioms dmForgetHandles_oneHandleRelationFactors
#print axioms dmForgetHandles_oneHandleC6CorrectedFactors
#print axioms dmForgetHandles_oneHandleW6Mark
#print axioms dmForgetHandles_oneHandleW6Relator
#print axioms exists_oneHandleDepthChiLift

end

end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactSupply
