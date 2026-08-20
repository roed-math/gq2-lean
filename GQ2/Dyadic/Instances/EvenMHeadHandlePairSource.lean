/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleSource

/-!
# Promoting a strict handle pair to the even-M core

The head-only exchange of W345 puts the selected `U` in the compact-M `C` slot, but crosses
the remaining partners.  The uniform source needed by the strict handle normal form exchanges
the complete pairs `(sigma,x₂)` and `(U_j,V_j)`.

The resulting word has the ordinary tame specialization.  At the pro-2 boundary it is exactly
the compact-M core on the selected handle pair, while the former core pair becomes the chosen
handle factor.  The exchange still crosses the tame/wild partition, so this source is genuinely
outside the equivalent-presentation route ruled out by W343.

This module remains structural: it identifies the correct general source word and boundary
relation but does not assert its exact-lifting, Stokes, scalar, or determinant certificate.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairSource

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Words
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Instances.EvenMHeadHandleSource

/-- Exchange the compact-M partner `x₂` with the second letter of the chosen handle. -/
def tailHandleSwap {h : ℕ} (j : Fin h) :
    Generator (2 + 2 * h) ≃ Generator (2 + 2 * h) :=
  Equiv.swap (coreLetter h 2) (handleV j)

@[simp] theorem tailHandleSwap_coreTwo {h : ℕ} (j : Fin h) :
    tailHandleSwap j (coreLetter h 2) = handleV j :=
  Equiv.swap_apply_left _ _

@[simp] theorem tailHandleSwap_handleV_self {h : ℕ} (j : Fin h) :
    tailHandleSwap j (handleV j) = coreLetter h 2 :=
  Equiv.swap_apply_right _ _

private theorem coreLetter_ne_handleV {h : ℕ} (i : Fin 3) (j : Fin h) :
    coreLetter h i ≠ handleV j := by
  intro H
  have E := congrArg (Generator.equivFin (2 + 2 * h)) H
  simp [coreLetter, handleV, Generator.equivFin] at E
  have := i.isLt
  omega

@[simp] theorem tailHandleSwap_sigma {h : ℕ} (j : Fin h) :
    tailHandleSwap j .sigma = .sigma := by
  apply Equiv.swap_apply_of_ne_of_ne <;> simp [coreLetter, handleV]

@[simp] theorem tailHandleSwap_tau {h : ℕ} (j : Fin h) :
    tailHandleSwap j .tau = .tau := by
  apply Equiv.swap_apply_of_ne_of_ne <;> simp [coreLetter, handleV]

@[simp] theorem tailHandleSwap_coreZero {h : ℕ} (j : Fin h) :
    tailHandleSwap j (coreLetter h 0) = coreLetter h 0 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro H
    have E := congrArg (Generator.equivFin (2 + 2 * h)) H
    simp [coreLetter, Generator.equivFin] at E
  · exact coreLetter_ne_handleV 0 j

@[simp] theorem tailHandleSwap_coreOne {h : ℕ} (j : Fin h) :
    tailHandleSwap j (coreLetter h 1) = coreLetter h 1 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro H
    have E := congrArg (Generator.equivFin (2 + 2 * h)) H
    simp [coreLetter, Generator.equivFin] at E
  · exact coreLetter_ne_handleV 1 j

private theorem handleU_ne_handleV {h : ℕ} (k j : Fin h) :
    handleU k ≠ handleV j := by
  intro H
  have E := congrArg (Generator.equivFin (2 + 2 * h)) H
  simp [handleU, handleV, Generator.equivFin] at E
  omega

private theorem coreTwo_ne_handleU {h : ℕ} (k : Fin h) :
    coreLetter h 2 ≠ handleU k := by
  intro H
  have E := congrArg (Generator.equivFin (2 + 2 * h)) H
  simp [coreLetter, handleU, Generator.equivFin] at E
  omega

@[simp] theorem tailHandleSwap_handleU {h : ℕ} (j k : Fin h) :
    tailHandleSwap j (handleU k) = handleU k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact (coreTwo_ne_handleU k).symm
  · exact handleU_ne_handleV k j

private theorem handleV_injective {h : ℕ} : Function.Injective (@handleV h) := by
  intro j k H
  apply Fin.ext
  simpa [handleV] using congrArg (fun g => Generator.equivFin (2 + 2 * h) g) H

@[simp] theorem tailHandleSwap_handleV {h : ℕ} (j k : Fin h) :
    tailHandleSwap j (handleV k) = if k = j then coreLetter h 2 else handleV k := by
  classical
  by_cases H : k = j
  · subst k
    simp
  · rw [if_neg H]
    apply Equiv.swap_apply_of_ne_of_ne
    · exact (coreLetter_ne_handleV 2 k).symm
    · exact fun E => H (handleV_injective E)

/-- Precompose a marking by the second half of the pair exchange. -/
def tailHandleMark {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) : Marking (2 + 2 * h) G :=
  ⟨fun g => t (tailHandleSwap j g)⟩

@[simp] theorem tailHandleMark_sigma {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) : (tailHandleMark t j).σ = t.σ := by
  rfl

@[simp] theorem tailHandleMark_tau {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) : (tailHandleMark t j).τ = t.τ := by
  rfl

@[simp] theorem tailHandleMark_coreZero {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) :
    tailHandleMark t j (coreLetter h 0) = t (coreLetter h 0) := by
  simp [tailHandleMark]

@[simp] theorem tailHandleMark_coreOne {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) :
    tailHandleMark t j (coreLetter h 1) = t (coreLetter h 1) := by
  simp [tailHandleMark]

@[simp] theorem tailHandleMark_coreTwo {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j : Fin h) :
    tailHandleMark t j (coreLetter h 2) = t (handleV j) := by
  rfl

@[simp] theorem tailHandleMark_handleU {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j k : Fin h) :
    tailHandleMark t j (handleU k) = t (handleU k) := by
  simp [tailHandleMark]

@[simp] theorem tailHandleMark_handleV {h : ℕ} {G : Type*} [Group G]
    (t : Marking (2 + 2 * h) G) (j k : Fin h) :
    tailHandleMark t j (handleV k) =
      if k = j then t (coreLetter h 2) else t (handleV k) := by
  classical
  simp only [tailHandleMark, Marking.coe_mk, tailHandleSwap_handleV]
  split <;> rfl

/-- Exchange the whole compact-M core pair `(sigma,x₂)` with a selected handle pair. -/
def headHandlePairCompactW (α : ℕ) {h : ℕ} (j : Fin h) :
    PWord (Generator (2 + 2 * h)) :=
  PWord.subst (fun g => .gen (tailHandleSwap j g)) (headHandleCompactW α j)

theorem eval_headHandlePairCompactW {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {α h : ℕ} (j : Fin h) (t : Marking (2 + 2 * h) G) :
    t.eval (headHandlePairCompactW α j) =
      (tailHandleMark t j).eval (headHandleCompactW α j) := by
  rw [Marking.eval_def, headHandlePairCompactW, PWord.eval_subst, Marking.eval_def]
  rfl

theorem pro2_subst_tailHandleSwap {h : ℕ} (j : Fin h)
    (w : PWord (Generator (2 + 2 * h))) :
    pro2 (PWord.subst (fun g => .gen (tailHandleSwap j g)) w) =
      PWord.subst (fun g => .gen (tailHandleSwap j g)) (pro2 w) := by
  induction w with
  | one => rfl
  | gen g =>
      cases g with
      | sigma => rfl
      | tau => simp
      | wild i =>
          rw [PWord.subst_gen, pro2_gen_wild, PWord.subst_gen]
          have Htau : tailHandleSwap j (Generator.wild i) ≠ Generator.tau := by
            intro H
            have := (tailHandleSwap j).injective
              (H.trans (tailHandleSwap_tau j).symm)
            simp at this
          cases E : tailHandleSwap j (Generator.wild i) with
          | sigma => rfl
          | tau => exact (Htau E).elim
          | wild k => rfl
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

/-- The full pair swap has exactly the desired pro-2 relator: the selected handle pair becomes
the compact-M core pair and the old core pair becomes that handle. -/
theorem eval_pro2_headHandlePairCompactW {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {α h : ℕ} (hα : 1 ≤ α) (j : Fin h) (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (headHandlePairCompactW α j)) =
      MarkedCore.mWord α
          ((t (coreLetter h 0))⁻¹ * (t (handleU j)) ^ (-(mOf α : ℤ)))
          (t (coreLetter h 1)) (t (handleU j)) (t (handleV j)) *
        MarkedCore.handleWord
          (fun k => if k = j then t.σ else t (handleU k))
          (fun k => if k = j then t (coreLetter h 2) else t (handleV k)) := by
  rw [headHandlePairCompactW, pro2_subst_tailHandleSwap, Marking.eval_def,
    PWord.eval_subst]
  simp only [PWord.eval_gen]
  change (tailHandleMark t j).eval (pro2 (headHandleCompactW α j)) = _
  simpa using eval_pro2_headHandleCompactW hα j (tailHandleMark t j)

theorem tailHandleMark_tameMarking {h q : ℕ} (j : Fin h) :
    tailHandleMark (tameMarking (2 + 2 * h) q) j = tameMarking (2 + 2 * h) q := by
  ext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      change (tameMarking (2 + 2 * h) q) (tailHandleSwap j (.wild i)) = 1
      cases E : tailHandleSwap j (.wild i) with
      | sigma =>
          exfalso
          have H := (tailHandleSwap j).injective
            (E.trans (tailHandleSwap_sigma j).symm)
          simp at H
      | tau =>
          exfalso
          have H := (tailHandleSwap j).injective
            (E.trans (tailHandleSwap_tau j).symm)
          simp at H
      | wild k => rfl

/-- The pair-swapped source retains the ordinary tame quotient. -/
theorem tameSpecializes_headHandlePairCompactW {α h q : ℕ} (j : Fin h)
    (hq0 : q ≠ 0) (hqe : Even q) :
    TameSpec.TameSpecializes (2 + 2 * h) q (headHandlePairCompactW α j) := by
  rw [TameSpec.tameSpecializes_iff, eval_headHandlePairCompactW,
    tailHandleMark_tameMarking]
  exact tameSpecializes_headHandleCompactW j hq0 hqe

/-- The full pair exchange remains outside the tame/wild-preserving relabeling class. -/
theorem headHandlePairSwap_not_preserves_wild {h : ℕ} (j : Fin h) :
    ¬ ∀ i : Fin (2 + 2 * h + 1),
      ∃ k : Fin (2 + 2 * h + 1),
        tailHandleSwap j (headHandleSwap j (.wild i)) = .wild k := by
  intro H
  obtain ⟨k, hk⟩ := H ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩
  change tailHandleSwap j (headHandleSwap j (handleU j)) = .wild k at hk
  rw [headHandleSwap_handleU_self, tailHandleSwap_sigma] at hk
  cases hk

#print axioms eval_pro2_headHandlePairCompactW
#print axioms tameSpecializes_headHandlePairCompactW
#print axioms headHandlePairSwap_not_preserves_wild

end

end GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
