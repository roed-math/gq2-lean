/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassFourSeed

/-!
# Direct finite stages for the one-handle Mpc shift

This module removes the compact-automorphism fibre from the remaining one-handle problem.  A
direct stage consists of a six-letter marking with the standard handle pair, mod-two
independence, the canonical chi rows, the universal `C + 2B` row, and full relator depth `k`.

The W4 marking gives a concrete nonempty fourth stage.  The stage sets are nested closed subsets
of a compact function space, so nonemptiness at every finite depth gives an exact marking and
`MpcPivShiftH 2 1`.  Equivalently, it now suffices to prove the single direct successor supply
from depth four onward.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectLimit

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralHandleShiftRecipe
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcOneHandleClassFourSeed
open GQ2.Roe.Labute

private abbrev H := DM 2 1

def oneHandleDirectSet (k : ℕ) : Set (Fin (coreRank 1) → H) :=
  {m | OneHandleModTwoIndep m ∧
    (∀ j : Fin 1,
      m (handleIdxU j) = dmGen 2 1 (handleIdxU j) ∧
      m (handleIdxV j) = dmGen 2 1 (handleIdxV j)) ∧
    (∀ i, chiM 2 1 (m i) = chiM 2 1 (dmGen 2 1 i)) ∧
    (∀ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
      toAdd (f (m 2)) = toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))) ∧
    mRelWord 2 m ∈ twoCentralSeries H k}

theorem oneHandleDirectSet_antitone {k k' : ℕ} (hkk : k' ≤ k) :
    oneHandleDirectSet k ⊆ oneHandleDirectSet k' :=
  fun _ ⟨hind, hhandles, hchi, hrow, hrel⟩ =>
    ⟨hind, hhandles, hchi, hrow,
      twoCentralSeries_antitone (G := H) hkk hrel⟩

private theorem continuous_eval (i : Fin (coreRank 1)) :
    Continuous fun m : Fin (coreRank 1) → H => m i := continuous_apply i

theorem oneHandleDirectSet_isClosed_indep :
    IsClosed {m : Fin (coreRank 1) → H | OneHandleModTwoIndep m} := by
  have hset : {m : Fin (coreRank 1) → H | OneHandleModTwoIndep m} =
      ⋂ (M : OpenNormalSubgroup H) (_ : M.toSubgroup.index = 2),
        ⋃ i : Fin (coreRank 1), {m | m i ∈ ((M.toSubgroup : Set H))ᶜ} := by
    ext m
    simp only [OneHandleModTwoIndep, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_iUnion, Set.mem_compl_iff, SetLike.mem_coe]
  rw [hset]
  refine isClosed_iInter fun M => isClosed_iInter fun _ =>
    isClosed_iUnion_of_finite fun i => ?_
  exact IsClosed.preimage (continuous_eval i) M.isOpen'.isClosed_compl

theorem oneHandleDirectSet_isClosed_chi : IsClosed
    {m : Fin (coreRank 1) → H |
      ∀ i, chiM 2 1 (m i) = chiM 2 1 (dmGen 2 1 i)} := by
  rw [show {m : Fin (coreRank 1) → H |
      ∀ i, chiM 2 1 (m i) = chiM 2 1 (dmGen 2 1 i)} =
      ⋂ i, {m | chiM 2 1 (m i) = chiM 2 1 (dmGen 2 1 i)} by
        ext m
        simp]
  exact isClosed_iInter fun i => isClosed_eq
    ((chiM 2 1).continuous_toFun.comp (continuous_eval i)) continuous_const

theorem oneHandleDirectSet_isClosed_handles : IsClosed
    {m : Fin (coreRank 1) → H | ∀ j : Fin 1,
      m (handleIdxU j) = dmGen 2 1 (handleIdxU j) ∧
      m (handleIdxV j) = dmGen 2 1 (handleIdxV j)} := by
  rw [show {m : Fin (coreRank 1) → H | ∀ j : Fin 1,
      m (handleIdxU j) = dmGen 2 1 (handleIdxU j) ∧
      m (handleIdxV j) = dmGen 2 1 (handleIdxV j)} =
      ⋂ j : Fin 1,
        ({m | m (handleIdxU j) = dmGen 2 1 (handleIdxU j)} ∩
          {m | m (handleIdxV j) = dmGen 2 1 (handleIdxV j)}) by
        ext m
        simp]
  exact isClosed_iInter fun j =>
    (isClosed_eq (continuous_eval (handleIdxU j)) continuous_const).inter
      (isClosed_eq (continuous_eval (handleIdxV j)) continuous_const)

theorem oneHandleDirectSet_isClosed_row : IsClosed
    {m : Fin (coreRank 1) → H |
      ∀ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
        toAdd (f (m 2)) = toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))} := by
  rw [show {m : Fin (coreRank 1) → H |
      ∀ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
        toAdd (f (m 2)) = toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))} =
      ⋂ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
        {m | toAdd (f (m 2)) =
        toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))} by
        ext m
        simp]
  exact isClosed_iInter fun f => isClosed_eq
    (continuous_toAdd.comp (f.continuous_toFun.comp (continuous_eval 2))) continuous_const

theorem continuous_directRelator :
    Continuous fun m : Fin (coreRank 1) → H => mRelWord 2 m := by
  simp only [mRelWord, mWord, handleWord, commP]
  fun_prop

theorem oneHandleDirectSet_isClosed (k : ℕ) : IsClosed (oneHandleDirectSet k) := by
  exact oneHandleDirectSet_isClosed_indep.inter
    (oneHandleDirectSet_isClosed_handles.inter
      (oneHandleDirectSet_isClosed_chi.inter
        (oneHandleDirectSet_isClosed_row.inter
          ((isClosed_twoCentralSeries (G := H) k).preimage continuous_directRelator))))

theorem oneHandleW4Mark_handles (j : Fin 1) :
    oneHandleW4Mark (handleIdxU j) = dmGen 2 1 (handleIdxU j) ∧
      oneHandleW4Mark (handleIdxV j) = dmGen 2 1 (handleIdxV j) := by
  simp [oneHandleW4Mark]

theorem oneHandleDirectSet_four_nonempty : (oneHandleDirectSet 4).Nonempty := by
  refine ⟨oneHandleW4Mark, oneHandleW4Mark_modTwoIndep,
    oneHandleW4Mark_handles, oneHandleW4Mark_chi,
    oneHandleW4Mark_C_row, oneHandleW4Mark_relator_mem_four⟩

theorem oneHandleDirect_iInter_nonempty
    (hsupply : ∀ k, (oneHandleDirectSet k).Nonempty) :
    (⋂ k, oneHandleDirectSet k).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro k k'
    exact ⟨max k k', oneHandleDirectSet_antitone (le_max_left k k'),
      oneHandleDirectSet_antitone (le_max_right k k')⟩
  · exact hsupply
  · exact fun k => (oneHandleDirectSet_isClosed k).isCompact
  · exact oneHandleDirectSet_isClosed

theorem mpcPivShiftH_two_one_of_direct_finite_stages
    (hsupply : ∀ k, (oneHandleDirectSet k).Nonempty) : MpcPivShiftH 2 1 := by
  obtain ⟨m, hm⟩ := oneHandleDirect_iInter_nonempty hsupply
  have hmem : ∀ k, m ∈ oneHandleDirectSet k := Set.mem_iInter.mp hm
  obtain ⟨hind, _, hchi, hrow, -⟩ := hmem 0
  apply mpcPivShiftH_of_marking m
  · have hall : mRelWord 2 m ∈ ⨅ k, twoCentralSeries H k :=
      Subgroup.mem_iInf.mpr fun k => (hmem k).2.2.2.2
    rw [oneHandle_iInf_twoCentralSeries, Subgroup.mem_bot] at hall
    exact hall
  · exact topGen_of_oneHandleModTwoIndep hind
  · exact hchi
  · exact hrow

def OneHandleDirectSuccessorSupply : Prop :=
  ∀ k, 4 ≤ k → (oneHandleDirectSet k).Nonempty →
    (oneHandleDirectSet (k + 1)).Nonempty

theorem oneHandleDirectSet_nonempty_all
    (hsucc : OneHandleDirectSuccessorSupply) (k : ℕ) :
    (oneHandleDirectSet k).Nonempty := by
  by_cases hk : k ≤ 4
  · exact oneHandleDirectSet_four_nonempty.mono (oneHandleDirectSet_antitone hk)
  · have h4k : 4 ≤ k := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h4k
    clear hk h4k
    induction d with
    | zero => simpa using oneHandleDirectSet_four_nonempty
    | succ d ih =>
      have hstage := hsucc (4 + d) (by omega) ih
      simpa [Nat.add_assoc] using hstage

theorem mpcPivShiftH_two_one_of_direct_successor
    (hsucc : OneHandleDirectSuccessorSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_finite_stages
    (oneHandleDirectSet_nonempty_all hsucc)

#print axioms oneHandleDirectSet_four_nonempty
#print axioms oneHandleDirectSet_isClosed
#print axioms oneHandleDirect_iInter_nonempty
#print axioms mpcPivShiftH_two_one_of_direct_finite_stages
#print axioms OneHandleDirectSuccessorSupply
#print axioms oneHandleDirectSet_nonempty_all
#print axioms mpcPivShiftH_two_one_of_direct_successor

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
