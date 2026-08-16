/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcCertificateLevel
import GQ2.Dyadic.MarkedCore.NFrameExists

/-!
# Primitive positive-level Npc plane coordinates

The exact lower half of the marked level says that `nu` attains `2^r` on `ker chi`.  In a
general-handle N-frame this does not force the original `(sigma,x2)` quotient row to be
primitive: the primitive coordinate may lie on a handle.  This module first proves that some
non-cyclotomic marked coordinate has unit quotient, then uses the exact Eichler moves to transfer
a primitive handle coordinate into `x2`.

The headline `exists_dnPlanePrimitive_of_level_exact` therefore produces a chi-preserving core
automorphism after which `NpcPlanePrimitiveAtLevel` holds.  No transitivity or marked-frame axiom
is assumed; the transfer is realized by the existing `frameEichlerU`/`frameEichlerV` lifts.

No new axiom is introduced.  Every public declaration has the standard axiom set
`[propext, Classical.choice, Quot.sound]`.
-/

namespace GQ2.Dyadic.Instances.NpcPlanePrimitive

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.SectionThree
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.NpcCertificateLevel
open scoped GQ2.SectionThree.TopAbInstances

private theorem parity_sum {I : Type*} [Fintype I] (f : I → ℤ_[2]) :
    mParityZ (∑ i, f i) = ∑ i, mParityZ (f i) := by
  classical
  have hs : ∀ s : Finset I, mParityZ (∑ i ∈ s, f i) = ∑ i ∈ s, mParityZ (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [mParityZ_add, ih]
  exact hs Finset.univ

private theorem toAdd_prod {I : Type*} [Fintype I] (f : I → Multiplicative ℤ_[2]) :
    toAdd (∏ i, f i) = ∑ i, toAdd (f i) := by
  classical
  have hs : ∀ s : Finset I, toAdd (∏ i ∈ s, f i) = ∑ i ∈ s, toAdd (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [toAdd_mul, ih]
  exact hs Finset.univ

private theorem parity_eq_zero_of_not_isUnit {a : ℤ_[2]} (ha : ¬ IsUnit a) :
    mParityZ a = 0 := by
  by_contra h
  apply ha
  apply mIsUnit_of_parity_one
  revert h
  generalize mParityZ a = z
  revert z
  decide

private theorem exists_isUnit_left_of_sum_eq_one {I : Type*} [Fintype I]
    (a b : I → ℤ_[2]) (hsum : (∑ i, a i * b i) = 1) :
    ∃ i, IsUnit (a i) := by
  classical
  by_contra h
  push Not at h
  have hpar := congrArg mParityZ hsum
  rw [parity_sum] at hpar
  have hzero : (∑ i, mParityZ (a i * b i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [mParityZ_mul, parity_eq_zero_of_not_isUnit (h i), zero_mul]
  rw [hzero, mParityZ_one] at hpar
  exact zero_ne_one hpar

/-- An exact level value on `ker chiN` forces a unit quotient on `sigma`, `x2`, or a handle. -/
theorem unit_quotient_marked_cases_of_chiKer_exact
    {alpha r h : ℕ} (halpha : 2 ≤ alpha)
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]))
    (q : Fin (coreRank h) → ℤ_[2])
    (hq : ∀ i : Fin (coreRank h), i ≠ 0 → i ≠ 1 →
      toAdd (nu' (dnGen alpha h i)) = 2 ^ r * q i)
    (x : (DN alpha h : Type)) (hxchi : chiN alpha h x = 1)
    (hxnu : toAdd (nu' x) = 2 ^ r) :
    IsUnit (q 2) ∨ IsUnit (q 3) ∨
      (∃ j : Fin h, IsUnit (q (handleIdxU j))) ∨
      ∃ j : Fin h, IsUnit (q (handleIdxV j)) := by
  classical
  obtain ⟨c, hc⟩ := nDNab_coord alpha h (abMk x)
  have hchi_word : zpowZtwo isProP_two_unitsPadicInt (nUnit alpha) (c 1) = 1 := by
    let hrel : (coreMark 1 (nUnit alpha) 1 1 : Fin (coreRank h) → ℤ_[2]ˣ) 0 ^
        (2 + 2 ^ alpha) = 1 := by rw [coreMark_zero, one_pow]
    have hab : nCoordHom alpha h isProP_two_unitsPadicInt
        (coreMark 1 (nUnit alpha) 1 1) hrel (nAbWord alpha h c) = 1 := by
      rw [← hc, nCoordHom, abLiftG_abMk]
      exact hxchi
    rw [nCoordHom_word,
      mProd_single _ _ _ 1 (fun i hi => by
        rw [coreMark_apply]
        have hv := mCoreVal_ne_one hi
        split_ifs <;> rfl), coreMark_one] at hab
    exact hab
  have hc1 : c 1 = 0 := by
    apply nUnit_zpowZtwo_injective halpha
    rw [zpowZtwo_zero]
    exact hchi_word
  have hnu_word : toAdd (nu' x) = ∑ i, c i * toAdd (nu' (dnGen alpha h i)) := by
    rw [← abLiftG_abMk nu' x, hc, nAbWord, map_prod, toAdd_prod]
    apply Finset.sum_congr rfl
    intro i hi
    rw [toAdd_map_zpowZtwo, abLiftG_abMk]
  let q' : Fin (coreRank h) → ℤ_[2] := fun i => if i = 0 ∨ i = 1 then 0 else q i
  have hfactor : toAdd (nu' x) = 2 ^ r * ∑ i, q' i * c i := by
    rw [hnu_word, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      rw [show dnGen alpha h 0 = dnX0 alpha h from rfl, nChar_dnX0, toAdd_one, mul_zero]
      simp [q']
    by_cases hi1 : i = 1
    · subst i
      rw [hc1, zero_mul]
      simp [q']
    rw [hq i hi0 hi1]
    simp only [q', hi0, hi1, or_false, ↓reduceIte]
    ring
  have hsum : (∑ i, q' i * c i) = 1 := by
    rw [hxnu] at hfactor
    apply mul_left_cancel₀ (pow_ne_zero r (by norm_num : (2 : ℤ_[2]) ≠ 0))
    simpa using hfactor.symm
  obtain ⟨i, hi⟩ := exists_isUnit_left_of_sum_eq_one q' c hsum
  have hi0 : i ≠ 0 := by
    intro e
    subst i
    exact (not_isUnit_zero : ¬ IsUnit (0 : ℤ_[2])) hi
  have hi1 : i ≠ 1 := by
    intro e
    subst i
    have hq' : q' 1 = 0 := by simp [q']
    exact (not_isUnit_zero : ¬ IsUnit (0 : ℤ_[2])) (hq' ▸ hi)
  have hiq : IsUnit (q i) := by simpa [q', hi0, hi1] using hi
  rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact absurd rfl hi0
  · exact absurd rfl hi1
  · exact Or.inl hiq
  · exact Or.inr (Or.inl hiq)
  · exact Or.inr (Or.inr (Or.inl ⟨j, hiq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, hiq⟩))

/-- Exact level data can be moved by a chi-preserving Eichler automorphism so that the
divided `(sigma,x2)` row is primitive. -/
theorem exists_dnPlanePrimitive_of_level_exact
    {alpha r h : ℕ} (halpha : 2 ≤ alpha)
    (nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : NpcChiKerLevel alpha r h nu')
    (x : (DN alpha h : Type)) (hxchi : chiN alpha h x = 1)
    (hxnu : toAdd (nu' x) = 2 ^ r) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ z, chiN alpha h (Psi z) = chiN alpha h z) ∧
      NpcPlanePrimitiveAtLevel alpha r h (nu'.comp (autHom Psi)) := by
  classical
  have hkerGen : ∀ i : Fin (coreRank h), i ≠ 0 → i ≠ 1 →
      chiN alpha h (dnGen alpha h i) = 1 := by
    intro i hi0 hi1
    rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact absurd rfl hi0
    · exact absurd rfl hi1
    · exact chiN_dnSigma alpha h
    · exact chiN_dnX2 alpha h
    · exact chiN_handleU alpha h j
    · exact chiN_handleV alpha h j
  let q : Fin (coreRank h) → ℤ_[2] := fun i =>
    if hi0 : i = 0 then 0 else if hi1 : i = 1 then 0 else
      Classical.choose (hlev _ (hkerGen i hi0 hi1))
  have hq : ∀ i : Fin (coreRank h), i ≠ 0 → i ≠ 1 →
      toAdd (nu' (dnGen alpha h i)) = 2 ^ r * q i := by
    intro i hi0 hi1
    simp only [q, dif_neg hi0, dif_neg hi1]
    exact Classical.choose_spec (hlev _ (hkerGen i hi0 hi1))
  have hq2 := hq 2
    (Fin.ne_of_val_ne (by rw [coreVal_two, coreVal_zero]; omega)) nCoreTwo_ne_one
  have hq3 := hq 3
    (Fin.ne_of_val_ne (by rw [coreVal_three, coreVal_zero]; omega)) nCoreThree_ne_one
  by_cases hu2 : IsUnit (q 2)
  · refine ⟨ContinuousMulEquiv.refl _, fun _ => rfl, q 2, q 3, ?_, ?_, Or.inl hu2⟩
    · exact hq2
    · exact hq3
  by_cases hu3 : IsUnit (q 3)
  · refine ⟨ContinuousMulEquiv.refl _, fun _ => rfl, q 2, q 3, ?_, ?_, Or.inr hu3⟩
    · exact hq2
    · exact hq3
  obtain hU | hV := (unit_quotient_marked_cases_of_chiKer_exact
    halpha nu' q hq x hxchi hxnu).resolve_left hu2 |>.resolve_left hu3
  · obtain ⟨j, hj⟩ := hU
    obtain ⟨Psi, hmem, hbridge⟩ := exists_dnRealizes alpha h
      (frameEichlerV_mem_clearGens j (1 : ℤ_[2]))
    have hsigma := congrFun (hbridge nu') 2
    have hx2 := congrFun (hbridge nu') 3
    rw [frameEnd_apply, frameEichlerV_two] at hsigma
    rw [frameEnd_apply, frameEichlerV_three, one_smul] at hx2
    simp only [nuFrame_apply] at hx2
    have hqU := hq (handleIdxU j)
      (Fin.ne_of_val_ne (by rw [handleIdxU_val, coreVal_zero]; omega)) (nHandleIdxU_ne_one j)
    have hnew : IsUnit (q 3 + q (handleIdxU j)) := by
      apply mIsUnit_of_parity_one
      rw [mParityZ_add, parity_eq_zero_of_not_isUnit hu3, mParityZ_of_isUnit hj, zero_add]
    refine ⟨Psi, chiN_of_mem_dnClearAuts alpha h hmem,
      q 2, q 3 + q (handleIdxU j), ?_, ?_, Or.inr hnew⟩
    · change toAdd (nu' (Psi (dnGen alpha h 2))) = 2 ^ r * q 2
      simpa only [nuFrame_apply] using hsigma.trans hq2
    · change toAdd (nu' (Psi (dnGen alpha h 3))) =
        2 ^ r * (q 3 + q (handleIdxU j))
      rw [hx2, hq3, hqU]
      ring
  · obtain ⟨j, hj⟩ := hV
    obtain ⟨Psi, hmem, hbridge⟩ := exists_dnRealizes alpha h
      (frameEichlerU_mem_clearGens j (1 : ℤ_[2]))
    have hsigma := congrFun (hbridge nu') 2
    have hx2 := congrFun (hbridge nu') 3
    rw [frameEnd_apply, frameEichlerU_two] at hsigma
    rw [frameEnd_apply, frameEichlerU_three, one_smul] at hx2
    simp only [nuFrame_apply] at hx2
    have hqV := hq (handleIdxV j)
      (Fin.ne_of_val_ne (by rw [handleIdxV_val, coreVal_zero]; omega)) (nHandleIdxV_ne_one j)
    have hnew : IsUnit (q 3 - q (handleIdxV j)) := by
      apply mIsUnit_of_parity_one
      rw [mParityZ_sub, parity_eq_zero_of_not_isUnit hu3, mParityZ_of_isUnit hj, zero_add]
    refine ⟨Psi, chiN_of_mem_dnClearAuts alpha h hmem,
      q 2, q 3 - q (handleIdxV j), ?_, ?_, Or.inr hnew⟩
    · change toAdd (nu' (Psi (dnGen alpha h 2))) = 2 ^ r * q 2
      simpa only [nuFrame_apply] using hsigma.trans hq2
    · change toAdd (nu' (Psi (dnGen alpha h 3))) =
        2 ^ r * (q 3 - q (handleIdxV j))
      rw [hx2, hq3, hqV]
      ring

#print axioms unit_quotient_marked_cases_of_chiKer_exact
#print axioms exists_dnPlanePrimitive_of_level_exact

end
end GQ2.Dyadic.Instances.NpcPlanePrimitive
