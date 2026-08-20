/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRPWordNielsenElementary
import GQ2.Dyadic.Words.M0

/-!
# A uniform head-handle source for the strict even-M branch

W343 and W344 rule out every source equivalent to the standard compact-M candidate on the
obstructed selected branch.  This module gives the first genuinely different structural
candidate.  For a chosen handle `j`, exchange the tame head `sigma` with `handleU j` inside the
compact-M wild word while leaving the ambient tame relation unchanged.

The new word still specializes to the ordinary tame quotient.  Its pro-2 value is the compact-M
relator with `handleU j` in the distinguished `C` slot and the old tame head in the corresponding
handle commutator.  The exchange crosses the tame/wild partition, so it is not an admissible
relabeling back to the standard candidate and is not covered by the equivalent-source no-go.

This is a structural source layer only.  It does not assert the exact-lifting, Stokes, scalar, or
determinant fields of a corrected certificate.  Those must be reconstructed for this genuinely
new source family rather than transported from the old one.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandleSource

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Words
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Instances.GammaRPWordNielsenElementary

/-- Exchange the tame head with the first letter of a chosen handle pair. -/
def headHandleSwap {h : ℕ} (j : Fin h) :
    Generator (2 + 2 * h) ≃ Generator (2 + 2 * h) :=
  Equiv.swap .sigma (handleU j)

@[simp] theorem headHandleSwap_sigma {h : ℕ} (j : Fin h) :
    headHandleSwap j .sigma = handleU j :=
  Equiv.swap_apply_left _ _

@[simp] theorem headHandleSwap_handleU_self {h : ℕ} (j : Fin h) :
    headHandleSwap j (handleU j) = .sigma :=
  Equiv.swap_apply_right _ _

@[simp] theorem headHandleSwap_tau {h : ℕ} (j : Fin h) :
    headHandleSwap j .tau = .tau := by
  apply Equiv.swap_apply_of_ne_of_ne <;> simp [handleU]

private theorem coreLetter_ne_handleU {h : ℕ} (i : Fin 3) (j : Fin h) :
    coreLetter h i ≠ handleU j := by
  intro H
  have E := congrArg (Generator.equivFin (2 + 2 * h)) H
  simp [coreLetter, handleU, Generator.equivFin] at E
  have := i.isLt
  omega

@[simp] theorem headHandleSwap_coreLetter {h : ℕ} (j : Fin h) (i : Fin 3) :
    headHandleSwap j (coreLetter h i) = coreLetter h i := by
  apply Equiv.swap_apply_of_ne_of_ne
  · simp [coreLetter]
  · exact coreLetter_ne_handleU i j

private theorem handleV_ne_handleU {h : ℕ} (k j : Fin h) :
    handleV k ≠ handleU j := by
  intro H
  have E := congrArg (Generator.equivFin (2 + 2 * h)) H
  simp [handleV, handleU, Generator.equivFin] at E
  omega

@[simp] theorem headHandleSwap_handleV {h : ℕ} (j k : Fin h) :
    headHandleSwap j (handleV k) = handleV k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · simp [handleV]
  · exact handleV_ne_handleU k j

private theorem handleU_injective {h : ℕ} : Function.Injective (@handleU h) := by
  intro j k H
  apply Fin.ext
  simpa [handleU] using congrArg (fun g => Generator.equivFin (2 + 2 * h) g) H

@[simp] theorem headHandleSwap_handleU {h : ℕ} (j k : Fin h) :
    headHandleSwap j (handleU k) = if k = j then .sigma else handleU k := by
  classical
  by_cases H : k = j
  · subst k
    simp
  · rw [if_neg H]
    apply Equiv.swap_apply_of_ne_of_ne
    · simp [handleU]
    · exact fun E => H (handleU_injective E)

/-- Precompose a marking by the head-handle exchange. -/
def headHandleMark {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) : Marking (2 + 2 * h) G :=
  ⟨fun g => t (headHandleSwap j g)⟩

@[simp] theorem headHandleMark_sigma {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) :
    (headHandleMark t j).σ = t (handleU j) := by
  rfl

@[simp] theorem headHandleMark_tau {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) :
    (headHandleMark t j).τ = t.τ := by
  rfl

@[simp] theorem headHandleMark_coreLetter {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) (i : Fin 3) :
    headHandleMark t j (coreLetter h i) = t (coreLetter h i) := by
  simp [headHandleMark]

@[simp] theorem headHandleMark_handleU {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j k : Fin h) :
    headHandleMark t j (handleU k) = if k = j then t.σ else t (handleU k) := by
  classical
  simp only [headHandleMark, Marking.coe_mk, headHandleSwap_handleU]
  split <;> rfl

@[simp] theorem headHandleMark_handleV {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j k : Fin h) :
    headHandleMark t j (handleV k) = t (handleV k) := by
  simp [headHandleMark]

/-- The uniform candidate obtained by moving the tame head into a chosen handle plane. -/
def headHandleCompactW (α : ℕ) {h : ℕ} (j : Fin h) :
    PWord (Generator (2 + 2 * h)) :=
  PWord.subst (fun g => .gen (headHandleSwap j g)) (mCompactW α h)

theorem eval_headHandleCompactW {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {α h : ℕ} (j : Fin h) (t : Marking (2 + 2 * h) G) :
    t.eval (headHandleCompactW α j) = (headHandleMark t j).eval (mCompactW α h) := by
  rw [Marking.eval_def, headHandleCompactW, PWord.eval_subst, Marking.eval_def]
  rfl

theorem pro2_subst_headHandleSwap {h : ℕ} (j : Fin h)
    (w : PWord (Generator (2 + 2 * h))) :
    pro2 (PWord.subst (fun g => .gen (headHandleSwap j g)) w) =
      PWord.subst (fun g => .gen (headHandleSwap j g)) (pro2 w) := by
  induction w with
  | one => rfl
  | gen g =>
      cases g with
      | sigma => rfl
      | tau => simp
      | wild i =>
          rw [PWord.subst_gen, pro2_gen_wild, PWord.subst_gen]
          by_cases H : Generator.wild i = handleU j
          · rw [H, headHandleSwap_handleU_self, pro2_gen_sigma]
          · have Hσ : Generator.wild i ≠ Generator.sigma := by simp
            rw [headHandleSwap, Equiv.swap_apply_of_ne_of_ne Hσ H]
            rfl
  | mul u v hu hv => simp only [PWord.subst_mul, pro2_mul, hu, hv]
  | inv u hu => simp only [PWord.subst_inv, pro2_inv, hu]
  | conj u v hu hv => simp only [PWord.subst_conj, pro2_conj, hu, hv]
  | comm u v hu hv => simp only [PWord.subst_comm, pro2_comm, hu, hv]
  | zpow u k hu => simp only [PWord.subst_zpow, pro2_zpow, hu]
  | z2pow u z hu => simp only [PWord.subst_z2pow, pro2_z2pow, hu]
  | profPow u γ hu =>
      by_cases H : γ = omega2
      · subst γ
        simp only [PWord.subst_profPow, pro2_profPow_omega2, hu]
      · simp only [PWord.subst_profPow, pro2_profPow_of_ne _ H, hu]

/-- The pro-2 relator has the selected handle in the compact-M `C` slot and the old tame head
in that handle's commutator. -/
theorem eval_pro2_headHandleCompactW {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {α h : ℕ} (hα : 1 ≤ α) (j : Fin h) (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (headHandleCompactW α j)) =
      MarkedCore.mWord α
          ((t (coreLetter h 0))⁻¹ * (t (handleU j)) ^ (-(mOf α : ℤ)))
          (t (coreLetter h 1)) (t (handleU j)) (t (coreLetter h 2)) *
        MarkedCore.handleWord
          (fun k => if k = j then t.σ else t (handleU k))
          (fun k => t (handleV k)) := by
  rw [headHandleCompactW, pro2_subst_headHandleSwap, Marking.eval_def,
    PWord.eval_subst]
  simp only [PWord.eval_gen]
  change (headHandleMark t j).eval (pro2 (mCompactW α h)) = _
  simpa using eval_pro2_mCompact hα (headHandleMark t j)

/-- Moving the head into a handle still gives a valid tame specialization. -/
theorem tameSpecializes_headHandleCompactW {α h q : ℕ} (j : Fin h)
    (hq0 : q ≠ 0) (hqe : Even q) :
    TameSpec.TameSpecializes (2 + 2 * h) q (headHandleCompactW α j) := by
  rw [TameSpec.tameSpecializes_iff, eval_headHandleCompactW]
  let s := headHandleMark (tameMarking (2 + 2 * h) q) j
  change s.eval (mCompactW α h) = 1
  have hsigma : s.σ = 1 := by
    change (headHandleMark (tameMarking (2 + 2 * h) q) j).σ = 1
    rw [headHandleMark_sigma]
    change (tameMarking (2 + 2 * h) q).x _ = 1
    exact tameMarking_x _
  have hcore : ∀ i : Fin 3, s (coreLetter h i) = 1 := by
    intro i
    change headHandleMark (tameMarking (2 + 2 * h) q) j (coreLetter h i) = 1
    rw [headHandleMark_coreLetter]
    change (tameMarking (2 + 2 * h) q).x _ = 1
    exact tameMarking_x _
  have htau : s.τ ^ᶻ omega2 = 1 := by
    simpa [s] using tameMarking_tau_zpowHat_omega2
      (n := 2 + 2 * h) hq0 hqe
  have hhandle : s.eval (handlesW h) = 1 := by
    rw [eval_handlesW, MarkedCore.handleWord, List.prod_eq_one]
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    have hv : s (handleV k) = 1 := by
      change headHandleMark (tameMarking (2 + 2 * h) q) j (handleV k) = 1
      rw [headHandleMark_handleV]
      change (tameMarking (2 + 2 * h) q).x _ = 1
      exact tameMarking_x _
    rw [hv]
    simp [commP]
  have hdelta : ∀ i : Fin 3,
      s.eval (GQ2.Dyadic.Words.MCompact.deltaC h i) = s.τ ^ᶻ omega2 := by
    intro i
    rw [eval_deltaC, hcore]
    simp
  have hE := eval_eRevW_eq_eBlock (α := α) s
  rw [hdelta, hdelta] at hE
  rw [eval_mCompact_factors, hhandle, mul_one, Marking.eval_def, mFactors,
    PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.eval_zpow, PWord.eval_comm, PWord.eval_inv, PWord.eval_conj, PWord.eval_gen,
    PWord.eval_prodList, PWord.eval_omega2PowHat, ← Marking.eval_def, eval_sigma2W,
    hE, a0W, j2W, hcore, hsigma, Marking.apply_tau, inv_one, one_conjR,
    commR_one_right, one_mul, mul_one]
  rw [← zpow_mul, ← mul_assoc, ← zpow_add,
    show (-(mOf α : ℤ) * 2 + 2 * (mOf α : ℤ)) = 0 by ring, zpow_zero, one_mul]
  rw [htau]
  simp [eBlock]

/-- This exchange crosses the tame/wild partition, so it is not a boundary-preserving alphabet
relabeling. -/
theorem headHandleSwap_not_preserves_wild {h : ℕ} (j : Fin h) :
    ¬ ∀ i : Fin (2 + 2 * h + 1),
      ∃ k : Fin (2 + 2 * h + 1), headHandleSwap j (.wild i) = .wild k := by
  intro H
  obtain ⟨k, hk⟩ := H ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩
  change headHandleSwap j (handleU j) = .wild k at hk
  rw [headHandleSwap_handleU_self] at hk
  cases hk

#print axioms eval_pro2_headHandleCompactW
#print axioms tameSpecializes_headHandleCompactW
#print axioms headHandleSwap_not_preserves_wild

end


end GQ2.Dyadic.Instances.EvenMHeadHandleSource
