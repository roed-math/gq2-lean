/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.MarkedCore.NPlaneFilteredDerivative
import GQ2.Dyadic.MarkedCore.HandleMix

/-!
# Actual paired slots of the arbitrary-rank N derivative

The partner involution exchanges the two entries of every adjacent pair,
including the two core pairs and all handles. The single-slot formula below
is a pure group identity for the literal derivative word: it has no depth,
commutativity, exponent-two, or surjectivity premise.
-/

namespace GQ2.Dyadic.MarkedCore
open GQ2

/-- Adjacent-pair partner on the actual N core alphabet. -/
def nPartner {h : ℕ} (i : Fin (coreRank h)) : Fin (coreRank h) :=
  ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
    have hi := i.isLt
    simp only [coreRank] at hi ⊢
    split_ifs <;> omega⟩

theorem nPartner_involutive {h : ℕ} : Function.Involutive (nPartner (h := h)) := by
  intro i
  apply Fin.ext
  simp only [nPartner]
  split_ifs <;> omega

@[simp] theorem nPartner_zero (h : ℕ) : nPartner (0 : Fin (coreRank h)) = 1 := by
  apply Fin.ext
  change (if ((0 : Fin (coreRank h)) : ℕ) % 2 = 0 then
    ((0 : Fin (coreRank h)) : ℕ) + 1 else ((0 : Fin (coreRank h)) : ℕ) - 1) =
      ((1 : Fin (coreRank h)) : ℕ)
  rw [coreVal_zero, coreVal_one]
  decide

@[simp] theorem nPartner_one (h : ℕ) : nPartner (1 : Fin (coreRank h)) = 0 := by
  rw [← nPartner_zero h, nPartner_involutive]

@[simp] theorem nPartner_two (h : ℕ) : nPartner (2 : Fin (coreRank h)) = 3 := by
  apply Fin.ext
  change (if ((2 : Fin (coreRank h)) : ℕ) % 2 = 0 then
    ((2 : Fin (coreRank h)) : ℕ) + 1 else ((2 : Fin (coreRank h)) : ℕ) - 1) =
      ((3 : Fin (coreRank h)) : ℕ)
  rw [coreVal_two, coreVal_three]
  decide

@[simp] theorem nPartner_three (h : ℕ) : nPartner (3 : Fin (coreRank h)) = 2 := by
  rw [← nPartner_two h, nPartner_involutive]

@[simp] theorem nPartner_handleU {h : ℕ} (j : Fin h) :
    nPartner (handleIdxU j) = handleIdxV j := by
  apply Fin.ext
  simp [nPartner, handleIdxU_val, handleIdxV_val]
  omega

@[simp] theorem nPartner_handleV {h : ℕ} (j : Fin h) :
    nPartner (handleIdxV j) = handleIdxU j := by
  rw [← nPartner_handleU j, nPartner_involutive]

theorem nPartner_ne_self {h : ℕ} (i : Fin (coreRank h)) : nPartner i ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  simp only [nPartner] at hv
  split_ifs at hv <;> omega

/-- Exhaustiveness of the four core slots and the uniformly indexed handles. -/
theorem nCoreIndex_cases {h : ℕ} (i : Fin (coreRank h)) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      ∃ j : Fin h, i = handleIdxU j ∨ i = handleIdxV j := by
  have hi := i.isLt
  simp only [coreRank] at hi
  by_cases hsmall : i.val < 4
  · have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hc with he | he | he | he
    · exact Or.inl (Fin.ext (he.trans (coreVal_zero h).symm))
    · exact Or.inr (Or.inl (Fin.ext (he.trans (coreVal_one h).symm)))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext (he.trans (coreVal_two h).symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (he.trans (coreVal_three h).symm)))))
  · let j : Fin h := ⟨(i.val - 4) / 2, by omega⟩
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨j, ?_⟩)))
    by_cases hp : i.val % 2 = 0
    · left
      apply Fin.ext
      simp only [handleIdxU_val, j]
      omega
    · right
      apply Fin.ext
      simp only [handleIdxV_val, j]
      omega

section SingleSlots
variable {H : Type*} [Group H] {h : ℕ}

private theorem handleDerivative_single_core (m : Fin (coreRank h) → H)
    (i : Fin (coreRank h)) (hi : i.val < 4) (z : H) :
    nFilteredHandleDerivative (fun j => m (handleIdxU j)) (fun j => m (handleIdxV j))
      (fun j => (Pi.mulSingle i z : Fin (coreRank h) → H) (handleIdxU j))
      (fun j => (Pi.mulSingle i z : Fin (coreRank h) → H) (handleIdxV j)) = 1 := by
  unfold nFilteredHandleDerivative
  apply List.prod_eq_one
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  simp [handleIdxU_ne_of_val_lt j hi,
    handleIdxV_ne_of_val_lt j hi, commP]

private theorem derivative_single_core (m : Fin (coreRank h) → H)
    (i : Fin (coreRank h)) (hi : i.val < 4) (z : H) :
    nFilteredDerivative m (Pi.mulSingle i z) =
      (if i = 0 then z^2 * commP z (m 0) else 1) * commP z (m (nPartner i)) := by
  have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    rcases nCoreIndex_cases i with h0 | h1 | h2 | h3 | ⟨j, hu | hv⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr h3))
    · exact False.elim ((handleIdxU_ne_of_val_lt j hi) hu.symm)
    · exact False.elim ((handleIdxV_ne_of_val_lt j hi) hv.symm)
  rw [nFilteredDerivative, handleDerivative_single_core m i hi z, mul_one]
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [nFilteredCoreDerivative, Pi.mulSingle_apply, Fin.ext_iff,
      coreVal_zero, coreVal_one, coreVal_two, coreVal_three,
      nPartner_zero, nPartner_one, nPartner_two, nPartner_three] <;>
    norm_num [commP]

private theorem derivative_single_handleU (m : Fin (coreRank h) → H) (j : Fin h) (z : H) :
    nFilteredDerivative m (Pi.mulSingle (handleIdxU j) z) = commP z (m (handleIdxV j)) := by
  have hcore : nFilteredCoreDerivative (m 0) (m 1) (m 2) (m 3)
      ((Pi.mulSingle (handleIdxU j) z : Fin (coreRank h) → H) 0)
      ((Pi.mulSingle (handleIdxU j) z : Fin (coreRank h) → H) 1)
      ((Pi.mulSingle (handleIdxU j) z : Fin (coreRank h) → H) 2)
      ((Pi.mulSingle (handleIdxU j) z : Fin (coreRank h) → H) 3) = 1 := by
    simp only [nFilteredCoreDerivative, Pi.mulSingle_apply, Fin.ext_iff,
      handleIdxU_val, coreVal_zero, coreVal_one, coreVal_two, coreVal_three]
    split_ifs <;> first | omega | simp [commP]
  rw [nFilteredDerivative, hcore, one_mul, nFilteredHandleDerivative]
  rw [List.prod_map_eq_pow_single j _ (fun j' hj' _ => ?_), List.count_finRange, pow_one]
  · simp [handleIdxU_ne_handleIdxV, commP]
  · have hU : handleIdxU j' ≠ handleIdxU j := fun he => hj' (handleIdxU_injective he)
    have hV : handleIdxV j' ≠ handleIdxU j := Ne.symm (handleIdxU_ne_handleIdxV j j')
    simp [hU, hV, commP]

private theorem derivative_single_handleV (m : Fin (coreRank h) → H) (j : Fin h) (z : H) :
    nFilteredDerivative m (Pi.mulSingle (handleIdxV j) z) = commP z (m (handleIdxU j)) := by
  have hcore : nFilteredCoreDerivative (m 0) (m 1) (m 2) (m 3)
      ((Pi.mulSingle (handleIdxV j) z : Fin (coreRank h) → H) 0)
      ((Pi.mulSingle (handleIdxV j) z : Fin (coreRank h) → H) 1)
      ((Pi.mulSingle (handleIdxV j) z : Fin (coreRank h) → H) 2)
      ((Pi.mulSingle (handleIdxV j) z : Fin (coreRank h) → H) 3) = 1 := by
    simp only [nFilteredCoreDerivative, Pi.mulSingle_apply, Fin.ext_iff,
      handleIdxV_val, coreVal_zero, coreVal_one, coreVal_two, coreVal_three]
    split_ifs <;> first | omega | simp [commP]
  rw [nFilteredDerivative, hcore, one_mul, nFilteredHandleDerivative]
  rw [List.prod_map_eq_pow_single j _ (fun j' hj' _ => ?_), List.count_finRange, pow_one]
  · simp [handleIdxU_ne_handleIdxV, commP]
  · have hU : handleIdxU j' ≠ handleIdxV j := handleIdxU_ne_handleIdxV j' j
    have hV : handleIdxV j' ≠ handleIdxV j := fun he => hj' (handleIdxV_injective he)
    simp [hU, hV, commP]

/-- The exact contribution of any one actual slot, uniformly in every rank. -/
theorem nFilteredDerivative_mulSingle (m : Fin (coreRank h) → H)
    (i : Fin (coreRank h)) (z : H) :
    nFilteredDerivative m (Pi.mulSingle i z) =
      (if i = 0 then z^2 * commP z (m 0) else 1) * commP z (m (nPartner i)) := by
  rcases nCoreIndex_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl | rfl⟩
  · exact derivative_single_core m 0 (by rw [coreVal_zero]; omega) z
  · exact derivative_single_core m 1 (by rw [coreVal_one]; omega) z
  · exact derivative_single_core m 2 (by rw [coreVal_two]; omega) z
  · exact derivative_single_core m 3 (by rw [coreVal_three]; omega) z
  · rw [derivative_single_handleU, nPartner_handleU, if_neg
      (handleIdxU_ne_of_val_lt j (by rw [coreVal_zero]; omega)), one_mul]
  · rw [derivative_single_handleV, nPartner_handleV, if_neg
      (handleIdxV_ne_of_val_lt j (by rw [coreVal_zero]; omega)), one_mul]

end SingleSlots

#print axioms nPartner
#print axioms nPartner_involutive
#print axioms nPartner_zero
#print axioms nPartner_one
#print axioms nPartner_two
#print axioms nPartner_three
#print axioms nPartner_handleU
#print axioms nPartner_handleV
#print axioms nPartner_ne_self
#print axioms nCoreIndex_cases
#print axioms nFilteredDerivative_mulSingle

end GQ2.Dyadic.MarkedCore
