/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectLimit

/-!
# A direct correction criterion for the one-handle successor

A direct successor modifies only the four core letters by factors in `lambda_(k-1)`.  The
handle factors are one, every factor is chi-trivial, and the `C` factor is invisible to all
continuous Z2-valued characters.  Its last field is exactly the finite quotient stage-shift
equation which cancels the current relator.

Such a correction preserves the standard handles, orientation, universal row, and mod-two
independence.  The latter is automatic because `lambda_2` lies in every index-two open normal
subgroup.  A correction at every direct stage therefore gives the direct successor supply and
the one-handle pivot shift.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Roe.Labute

private abbrev H := DM 2 1

def oneHandleDirectModify
    (m e : Fin (coreRank 1) → H) : Fin (coreRank 1) → H :=
  fun i => m i * e i

def oneHandleDirectRelatorShift
    (m e : Fin (coreRank 1) → H) (k : ℕ) : levelQuot H (k + 1) :=
  stageShift (mStageWord 2 1 (by omega))
    (fun i => levelMk H (k + 1) (m i))
    (fun i => levelMk H (k + 1) (e i))

theorem oneHandleDirectRelatorShift_eq
    (m e : Fin (coreRank 1) → H) (k : ℕ) :
    oneHandleDirectRelatorShift m e k =
      (levelMk H (k + 1) (mRelWord 2 m))⁻¹ *
        levelMk H (k + 1) (mRelWord 2 (oneHandleDirectModify m e)) := by
  have hmark :
      (fun i => levelMk H (k + 1) (m i) * levelMk H (k + 1) (e i)) =
        fun i => levelMk H (k + 1) (oneHandleDirectModify m e i) := by
    funext i
    rw [oneHandleDirectModify, map_mul]
  rw [oneHandleDirectRelatorShift, stageShift]
  change
    (mRelWord 2 (fun i => levelMk H (k + 1) (m i)))⁻¹ *
      mRelWord 2 (fun i =>
        levelMk H (k + 1) (m i) * levelMk H (k + 1) (e i)) = _
  rw [hmark, ← map_mRelWord, ← map_mRelWord]

/-- A four-core-slot correction taking one direct stage to its successor. -/
structure OneHandleDirectCorrection
    (m : Fin (coreRank 1) → H) (k : ℕ) where
  factors : Fin (coreRank 1) → H
  depth : ∀ i, factors i ∈ twoCentralSeries H (k - 1)
  handleU : ∀ j : Fin 1, factors (handleIdxU j) = 1
  handleV : ∀ j : Fin 1, factors (handleIdxV j) = 1
  chi : ∀ i, chiM 2 1 (factors i) = 1
  row : ∀ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
    toAdd (f (factors 2)) = 0
  kills : oneHandleDirectRelatorShift m factors k =
    (levelMk H (k + 1) (mRelWord 2 m))⁻¹

theorem OneHandleDirectCorrection.kills_relator
    {m : Fin (coreRank 1) → H} {k : ℕ}
    (E : OneHandleDirectCorrection m k) :
    mRelWord 2 (oneHandleDirectModify m E.factors) ∈
      twoCentralSeries H (k + 1) := by
  have hshift := E.kills
  rw [oneHandleDirectRelatorShift_eq] at hshift
  apply (lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mpr
  apply mul_left_cancel
    (a := (levelMk H (k + 1) (mRelWord 2 m))⁻¹)
  simpa only [mul_one] using hshift

/-- The second two-central level lies in every index-two open normal subgroup. -/
theorem oneHandle_lambdaTwo_le_indexTwo
    (M : OpenNormalSubgroup H) (hM : M.toSubgroup.index = 2) :
    twoCentralSeries H 2 ≤ M.toSubgroup := by
  rw [twoCentralSeries_succ (G := H) (k := 1) le_rfl]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
    M.toOpenSubgroup.isClosed
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨v, -, rfl⟩
    exact sq_mem_of_index_two hM v
  · rw [Subgroup.commutator_le]
    intro g _ t _
    rw [commutatorElement_def]
    have hc := commP_mem_of_index_two (M := M.toSubgroup) hM g⁻¹ t⁻¹
    rwa [show commP g⁻¹ t⁻¹ = g * t * g⁻¹ * t⁻¹ by
      rw [commP]
      group] at hc

theorem oneHandleDirectModify_modTwoIndep
    {m : Fin (coreRank 1) → H} {k : ℕ}
    (hk : 4 ≤ k) (hm : OneHandleModTwoIndep m)
    (E : OneHandleDirectCorrection m k) :
    OneHandleModTwoIndep (oneHandleDirectModify m E.factors) := by
  intro M hM
  obtain ⟨i, hi⟩ := hm M hM
  refine ⟨i, ?_⟩
  have hdepth : E.factors i ∈ twoCentralSeries H 2 :=
    twoCentralSeries_antitone (G := H) (by omega) (E.depth i)
  have hei : E.factors i ∈ M.toSubgroup :=
    oneHandle_lambdaTwo_le_indexTwo M hM hdepth
  exact notMem_mul_notMem hM hi hei

theorem OneHandleDirectCorrection.toSuccessor
    {m : Fin (coreRank 1) → H} {k : ℕ}
    (hk : 4 ≤ k) (hm : m ∈ oneHandleDirectSet k)
    (E : OneHandleDirectCorrection m k) :
    oneHandleDirectModify m E.factors ∈ oneHandleDirectSet (k + 1) := by
  obtain ⟨hind, hhandles, hchi, hrow, -⟩ := hm
  refine ⟨oneHandleDirectModify_modTwoIndep hk hind E, ?_, ?_, ?_, E.kills_relator⟩
  · intro j
    constructor
    · rw [oneHandleDirectModify, E.handleU, mul_one]
      exact (hhandles j).1
    · rw [oneHandleDirectModify, E.handleV, mul_one]
      exact (hhandles j).2
  · intro i
    rw [oneHandleDirectModify, map_mul, E.chi, mul_one, hchi]
  · intro f
    rw [oneHandleDirectModify, map_mul, toAdd_mul, E.row f, add_zero,
      hrow f]

theorem oneHandleDirectCorrection_kills_level
    {m : Fin (coreRank 1) → H} {k : ℕ}
    (E : OneHandleDirectCorrection m k) :
    levelMk H (k + 1)
        (mRelWord 2 (oneHandleDirectModify m E.factors)) = 1 :=
  (lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mp E.kills_relator

def OneHandleDirectCorrectionSupply : Prop :=
  ∀ (k : ℕ) (_hk : 4 ≤ k) (m : Fin (coreRank 1) → H),
    m ∈ oneHandleDirectSet k → Nonempty (OneHandleDirectCorrection m k)

theorem directSuccessorSupply_of_correctionSupply
    (Hcorr : OneHandleDirectCorrectionSupply) :
    OneHandleDirectSuccessorSupply := by
  intro k hk hstage
  obtain ⟨m, hm⟩ := hstage
  obtain ⟨E⟩ := Hcorr k hk m hm
  exact ⟨oneHandleDirectModify m E.factors,
    E.toSuccessor hk hm⟩

theorem mpcPivShiftH_two_one_of_direct_correctionSupply
    (Hcorr : OneHandleDirectCorrectionSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_successor
    (directSuccessorSupply_of_correctionSupply Hcorr)

#print axioms OneHandleDirectCorrection
#print axioms oneHandleDirectRelatorShift_eq
#print axioms OneHandleDirectCorrection.kills_relator
#print axioms oneHandle_lambdaTwo_le_indexTwo
#print axioms oneHandleDirectModify_modTwoIndep
#print axioms OneHandleDirectCorrection.toSuccessor
#print axioms OneHandleDirectCorrectionSupply
#print axioms directSuccessorSupply_of_correctionSupply
#print axioms mpcPivShiftH_two_one_of_direct_correctionSupply

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
