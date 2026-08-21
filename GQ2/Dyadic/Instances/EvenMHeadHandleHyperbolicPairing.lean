/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleMixedPairing

namespace GQ2.Dyadic

/-!
# A hyperbolic repair of the promoted head-handle plane

The core-only shear of W355 supplies a partner for the displaced `V` direction, but a general
source must treat both directions of the promoted handle uniformly.  Here the finite Nielsen
move sends the compact promoted `U` letter backward to `sigma * U`.  Consequently the two
original handle coordinates occupy a standard hyperbolic plane in the substituted compact
word.

The two headline identities include both source relators and are exact:

* primal `V` against dual `U` evaluates to `lam v`;
* primal `U` against dual `V` evaluates to `lam v`.

The proof is independent of rank, ramification class, exponent resolver, and the action of
`tau`.  Non-handle factors are one-sided pure; the sole surviving charge is the selected
handle commutator.
-/

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.GammaRPWordNielsen
open Instances.GammaRPWordNielsenElementary
open Instances.EvenMHeadHandleMixed
open Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairNoGo
open Instances.EvenMHeadHandleSource
open Instances.EvenMHeadHandlePairSource

namespace Instances.EvenMHeadHandleHyperbolic

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
  [DistribMulAction C A]

def headHandleHyperbolicNielsen (j : Fin h) : PWordNielsenPair (2 + 2 * h) :=
  GammaRPWordNielsenElementary.PWordNielsenPair.trans
    (headHandlePairNielsen j)
    (rightMulNielsen (handleU j) .sigma (by simp [handleU]))

def headHandleHyperbolicW (alpha : ℕ) (j : Fin h) :
    PWord (Generator (2 + 2 * h)) :=
  PWord.subst (headHandleHyperbolicNielsen j).backward
    (Words.MCompact.mCompactW alpha h)

theorem headHandleHyperbolicNielsen_backward_of_ne (j : Fin h)
    (g : Generator (2 + 2 * h)) (hg : g ≠ handleU j) :
    (headHandleHyperbolicNielsen j).backward g =
      .gen (headHandlePairSwap j g) := by
  change PWord.subst (headHandlePairNielsen j).backward
    (rightMulBackward (handleU j) .sigma g) = _
  rw [rightMulBackward, if_neg hg, PWord.subst_gen]
  change PWord.gen ((headHandlePairSwap j).symm g) = _
  rw [headHandlePairSwap_symm]

@[simp] theorem headHandleHyperbolicNielsen_backward_handleU (j : Fin h) :
    (headHandleHyperbolicNielsen j).backward (handleU j) =
      .mul (.gen .sigma) (.gen (handleU j)) := by
  change PWord.subst (headHandlePairNielsen j).backward
    (rightMulBackward (handleU j) .sigma (handleU j)) = _
  rw [rightMulBackward, if_pos rfl, PWord.subst_mul, PWord.subst_gen,
    PWord.subst_gen]
  change PWord.mul (PWord.gen ((headHandlePairSwap j).symm (handleU j)))
    (PWord.gen ((headHandlePairSwap j).symm .sigma)) = _
  rw [headHandlePairSwap_symm, headHandlePairSwap_handleU_self,
    headHandlePairSwap_sigma]

@[simp] theorem headHandleHyperbolicNielsen_backward_tau (j : Fin h) :
    (headHandleHyperbolicNielsen j).backward .tau = .gen .tau := by
  rw [headHandleHyperbolicNielsen_backward_of_ne j .tau (by simp [handleU])]
  rw [headHandlePairSwap_tau]

@[simp] theorem headHandleHyperbolicNielsen_backward_sigma (j : Fin h) :
    (headHandleHyperbolicNielsen j).backward .sigma = .gen (handleU j) := by
  rw [headHandleHyperbolicNielsen_backward_of_ne j .sigma (by simp [handleU])]
  congr 1
  exact headHandlePairSwap_sigma j

@[simp] theorem headHandleHyperbolicNielsen_backward_handleV (j : Fin h) :
    (headHandleHyperbolicNielsen j).backward (handleV j) =
      .gen (coreLetter h 2) := by
  rw [headHandleHyperbolicNielsen_backward_of_ne j (handleV j)
    (by simp [handleV, handleU])]
  congr 1
  exact headHandlePairSwap_handleV_self j

@[simp] theorem headHandleHyperbolicNielsen_backward_coreZero (j : Fin h) :
    (headHandleHyperbolicNielsen j).backward (coreLetter h 0) =
      .gen (coreLetter h 0) := by
  rw [headHandleHyperbolicNielsen_backward_of_ne j (coreLetter h 0)
    (Certificates.MCompact.handleU_ne_coreLetter j 0).symm]
  congr 1
  rw [headHandlePairSwap]
  change tailHandleSwap j (headHandleSwap j (coreLetter h 0)) = coreLetter h 0
  rw [headHandleSwap_coreLetter, tailHandleSwap_coreZero]

@[simp] theorem headHandleHyperbolicNielsen_backward_coreOne (j : Fin h) :
    (headHandleHyperbolicNielsen j).backward (coreLetter h 1) =
      .gen (coreLetter h 1) := by
  rw [headHandleHyperbolicNielsen_backward_of_ne j (coreLetter h 1)
    (Certificates.MCompact.handleU_ne_coreLetter j 1).symm]
  congr 1
  rw [headHandlePairSwap]
  change tailHandleSwap j (headHandleSwap j (coreLetter h 1)) = coreLetter h 1
  rw [headHandleSwap_coreLetter, tailHandleSwap_coreOne]

@[simp] theorem headHandleHyperbolicNielsen_backward_coreTwo (j : Fin h) :
    (headHandleHyperbolicNielsen j).backward (coreLetter h 2) =
      .gen (handleV j) := by
  rw [headHandleHyperbolicNielsen_backward_of_ne j (coreLetter h 2)
    (Certificates.MCompact.handleU_ne_coreLetter j 2).symm]
  congr 1
  exact headHandlePairSwap_coreTwo j

def pairUSlot (j : Fin h) (v : A) : Fin h × Fin 2 → A :=
  Function.update 0 (j, 0) v

@[simp] private theorem pairUSlot_self (j : Fin h) (v : A) :
    pairUSlot j v (j, 0) = v := by simp [pairUSlot]

@[simp] private theorem pairUSlot_one (j k : Fin h) (v : A) :
    pairUSlot j v (k, 1) = 0 := by simp [pairUSlot]

def hyperXU (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) :=
  headHandlePairRamNormal t j 0 0 (pairUSlot j v)

def hyperXV (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) :=
  headHandlePairRamNormal t j 0 0 (pairVSlot j v)

def hyperYU (t : Marking (2 + 2 * h) C) (j : Fin h) (lam : ElemDual A) :=
  headHandlePairRamNormal t j 0 0 (pairUSlot j lam)

def hyperYV (t : Marking (2 + 2 * h) C) (j : Fin h) (lam : ElemDual A) :=
  headHandlePairRamNormal t j 0 0 (pairVSlot j lam)

private def hyperHeis (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h)
    (g : Generator (2 + 2 * h)) : HeisLift A C :=
  heisEvalZ ⇑t x y E E₂ ((headHandleHyperbolicNielsen j).backward g)

private def hyperMark (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h) :
    Marking (2 + 2 * h) C := ⟨fun g ↦ (hyperHeis t x y E E₂ j g).g⟩

private def hyperPrimal (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h) :=
  fun g ↦ (hyperHeis t x y E E₂ j g).a

private def hyperDual (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h) :=
  fun g ↦ (hyperHeis t x y E E₂ j g).l

private theorem hyperHeis_z_eq_zero
    (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) :
    ∀ g, (hyperHeis t x y E E₂ j g).z = 0 := by
  intro g
  by_cases hg : g = handleU j
  · subst g
    rw [hyperHeis, headHandleHyperbolicNielsen_backward_handleU,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen]
    simp [hxσ, hyσ, HeisLift.mul_z]
  · rw [hyperHeis, headHandleHyperbolicNielsen_backward_of_ne j g hg,
      heisEvalZ_gen]

private theorem hyperHeis_eq_heisGen
    (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) :
    hyperHeis t x y E E₂ j =
      heisGen ⇑(hyperMark t x y E E₂ j)
        (hyperPrimal t x y E E₂ j) (hyperDual t x y E E₂ j) := by
  funext g
  apply HeisLift.ext <;>
    simp [hyperMark, hyperPrimal, hyperDual,
      hyperHeis_z_eq_zero t x y E E₂ j hxσ hyσ]

private theorem hyperMark_wild_trivial
    (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (j : Fin h)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    ∀ (i : Fin (2 + 2 * h + 1)) (a : A),
      (hyperMark t x y E E₂ j).x i • a = a := by
  intro i a
  change (hyperHeis t x y E E₂ j (.wild i)).g • a = a
  by_cases hi : (Generator.wild i : Generator (2 + 2 * h)) = handleU j
  · rw [hi, hyperHeis, headHandleHyperbolicNielsen_backward_handleU,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen]
    change (t.σ * t (handleU j)) • a = a
    rw [mul_smul, hs]
    exact hwild ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩ a
  · rw [hyperHeis, headHandleHyperbolicNielsen_backward_of_ne j (.wild i) hi,
      heisEvalZ_gen]
    exact pairSwap_wild_trivial t j hs hwild i a

@[simp] private theorem hyperVU_primal_handleU
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hyperPrimal t (hyperXV t j v) (hyperYU t j lam) E E₂ j (handleU k) = 0 := by
  by_cases hk : k = j
  · subst k
    rw [hyperPrimal, hyperHeis, headHandleHyperbolicNielsen_backward_handleU,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen, HeisLift.mul_a]
    simp [hyperXV, pairVSlot_zero]
  · have hne : handleU k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleU, Generator.equivFin] at H'
      exact hk (Fin.ext (by omega))
    rw [hyperPrimal, hyperHeis,
      headHandleHyperbolicNielsen_backward_of_ne j (handleU k) hne,
      heisEvalZ_gen]
    simp [hyperXV, headHandlePairSwap, pairVSlot_zero, hk]

@[simp] private theorem hyperVU_dual_handleU
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hs : ∀ a : A, t.σ • a = a) :
    hyperDual t (hyperXV t j v) (hyperYU t j lam) E E₂ j (handleU k) =
      if k = j then lam else 0 := by
  by_cases hk : k = j
  · subst k
    rw [hyperDual, hyperHeis, headHandleHyperbolicNielsen_backward_handleU,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen, HeisLift.mul_l]
    have hsD : t.σ • lam = lam := elemDual_smul_eq_self hs lam
    simp [hyperYU, pairUSlot, hsD]
  · have hne : handleU k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleU, Generator.equivFin] at H'
      exact hk (Fin.ext (by omega))
    rw [hyperDual, hyperHeis,
      headHandleHyperbolicNielsen_backward_of_ne j (handleU k) hne,
      heisEvalZ_gen]
    simp [hyperYU, headHandlePairSwap, pairUSlot, hk]

@[simp] private theorem hyperVU_primal_handleV
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hyperPrimal t (hyperXV t j v) (hyperYU t j lam) E E₂ j (handleV k) =
      if k = j then v else 0 := by
  by_cases hk : k = j
  · subst k
    rw [hyperPrimal, hyperHeis, headHandleHyperbolicNielsen_backward_handleV,
      heisEvalZ_gen]
    simp [hyperXV, pairVSlot]
  · have hne : handleV k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleV, handleU, Generator.equivFin] at H'
      omega
    rw [hyperPrimal, hyperHeis,
      headHandleHyperbolicNielsen_backward_of_ne j (handleV k) hne,
      heisEvalZ_gen]
    simp [hyperXV, headHandlePairSwap, pairVSlot, hk]

@[simp] private theorem hyperVU_dual_handleV
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hyperDual t (hyperXV t j v) (hyperYU t j lam) E E₂ j (handleV k) = 0 := by
  by_cases hk : k = j
  · subst k
    rw [hyperDual, hyperHeis, headHandleHyperbolicNielsen_backward_handleV,
      heisEvalZ_gen]
    simp [hyperYU, pairUSlot]
  · have hne : handleV k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleV, handleU, Generator.equivFin] at H'
      omega
    rw [hyperDual, hyperHeis,
      headHandleHyperbolicNielsen_backward_of_ne j (handleV k) hne,
      heisEvalZ_gen]
    simp [hyperYU, headHandlePairSwap, pairUSlot, hk]

private theorem hyperVU_primalZero_mFactors
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hs : ∀ a : A, t.σ • a = a) (alpha : ℕ) :
    PrimalZero (hyperPrimal t (hyperXV t j v) (hyperYU t j lam) E E₂ j)
      (PWord.prodList (Words.MCompact.mFactors alpha h)) := by
  have hsInv : t.σ⁻¹ • v = v := inv_smul_eq_iff.mpr (hs v).symm
  rw [primalZero_prodList]
  intro w hw
  simp only [Words.MCompact.mFactors, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [PrimalZero, hyperPrimal, hyperHeis, hyperXV, Words.MCompact.a0W,
      sigma2W, PWord.omega2Pow, Words.MCompact.j2W, Words.MCompact.eRevW,
      Words.MCompact.deltaC, pairVSlot, hsInv]

theorem heisZ_headHandleHyperbolicW_VU
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    (heisEvalZ ⇑t (hyperXV t j v) (hyperYU t j lam) E E₂
      (headHandleHyperbolicW alpha j)).z = lam v := by
  rw [headHandleHyperbolicW]
  change (PWord.evalZ (heisGen ⇑t (hyperXV t j v) (hyperYU t j lam)) E E₂
    (PWord.subst (headHandleHyperbolicNielsen j).backward
      (Words.MCompact.mCompactW alpha h))).z = lam v
  rw [PWord.evalZ_subst]
  change (PWord.evalZ
    (hyperHeis t (hyperXV t j v) (hyperYU t j lam) E E₂ j) E E₂
      (Words.MCompact.mCompactW alpha h)).z = lam v
  rw [hyperHeis_eq_heisGen t (hyperXV t j v) (hyperYU t j lam) E E₂ j
    (by simp [hyperXV]) (by simp [hyperYU])]
  let s := hyperMark t (hyperXV t j v) (hyperYU t j lam) E E₂ j
  let b := hyperPrimal t (hyperXV t j v) (hyperYU t j lam) E E₂ j
  let c := hyperDual t (hyperXV t j v) (hyperYU t j lam) E E₂ j
  change (heisEvalZ ⇑s b c E E₂ (Words.MCompact.mCompactW alpha h)).z = lam v
  have hswild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), s.x i • a = a :=
    hyperMark_wild_trivial t _ _ E E₂ j hs hwild
  have hP := heisEvalZ_mem_heisPrimPure_of_primalZero ⇑s b c E E₂
    (PWord.prodList (Words.MCompact.mFactors alpha h))
    (hyperVU_primalZero_mFactors t j v lam E E₂ hs alpha)
  have hPz : ((Words.MCompact.mFactors alpha h).map
      (heisEvalZ ⇑s b c E E₂)).prod.z = 0 := by
    rw [← heisEvalZ_prodList]
    exact hP.2
  have hH := Certificates.MCompact.heisF_handlesW_mem s b c E E₂ hswild
  have hHz := Certificates.MCompact.heisF_handlesW_z s b c E E₂ hswild
  have hsum : (∑ k, (c (handleU k) (b (handleV k))
      + c (handleV k) (b (handleU k)))) = lam v := by
    rw [Finset.sum_eq_single j]
    · simp [b, c, hs]
    · intro k _ hk
      simp [b, c, hs, hk]
    · simp
  rw [Words.MCompact.mCompactW, heisEvalZ_prodList, List.map_append,
    List.prod_append, Certificates.MCompact.heisEvalZ_handleTailW]
  rw [heisMul_z_of_a_eq_zero _ _ hH.1, hPz, hHz, hsum, zero_add]

private def DualZero (y : Generator (2 + 2 * h) → ElemDual A) :
    PWord (Generator (2 + 2 * h)) → Prop
  | .one => True
  | .gen g => y g = 0
  | .mul u v => DualZero y u ∧ DualZero y v
  | .inv u => DualZero y u
  | .conj u v => DualZero y u ∧ DualZero y v
  | .comm u v => DualZero y u ∧ DualZero y v
  | .zpow u _ => DualZero y u
  | .z2pow u _ => DualZero y u
  | .profPow u _ => DualZero y u

private theorem dualZero_prodList (y : Generator (2 + 2 * h) → ElemDual A) :
    ∀ ws, DualZero y (PWord.prodList ws) ↔ ∀ w ∈ ws, DualZero y w := by
  intro ws
  induction ws with
  | nil => simp [PWord.prodList, DualZero]
  | cons w ws ih => simp [PWord.prodList, DualZero, ih]

private theorem heisEvalZ_mem_heisDualPure_of_dualZero
    (mu : Generator (2 + 2 * h) → C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    ∀ w, DualZero y w →
      heisEvalZ mu x y E E₂ w ∈ NProcyclicRam.heisDualPure A C := by
  intro w hw
  induction w with
  | one => exact (NProcyclicRam.heisDualPure A C).one_mem
  | gen g =>
      rw [heisEvalZ_gen]
      exact ⟨hw, rfl⟩
  | mul u v hu hv =>
      rw [heisEvalZ_mul]
      exact mul_mem (hu hw.1) (hv hw.2)
  | inv u hu =>
      rw [heisEvalZ_inv]
      exact inv_mem (hu hw)
  | conj u v hu hv =>
      rw [heisEvalZ_conj, conjR]
      exact mul_mem (mul_mem (inv_mem (hv hw.2)) (hu hw.1)) (hv hw.2)
  | comm u v hu hv =>
      rw [heisEvalZ_comm, commR]
      exact mul_mem (mul_mem (mul_mem (inv_mem (hu hw.1)) (inv_mem (hv hw.2)))
        (hu hw.1)) (hv hw.2)
  | zpow u k hu =>
      rw [heisEvalZ_zpow]
      exact zpow_mem (hu hw) k
  | z2pow u z hu =>
      change PWord.evalZ (heisGen mu x y) E E₂ (.z2pow u z) ∈
        NProcyclicRam.heisDualPure A C
      rw [PWord.evalZ_z2pow]
      exact zpow_mem (hu hw) (E₂ z)
  | profPow u z hu =>
      rw [heisEvalZ_profPow]
      exact zpow_mem (hu hw) (E z)

@[simp] private theorem hyperUV_primal_handleU
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hs : ∀ a : A, t.σ • a = a) :
    hyperPrimal t (hyperXU t j v) (hyperYV t j lam) E E₂ j (handleU k) =
      if k = j then v else 0 := by
  by_cases hk : k = j
  · subst k
    rw [hyperPrimal, hyperHeis, headHandleHyperbolicNielsen_backward_handleU,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen, HeisLift.mul_a]
    simp [hyperXU, pairUSlot, hs]
  · have hne : handleU k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleU, Generator.equivFin] at H'
      exact hk (Fin.ext (by omega))
    rw [hyperPrimal, hyperHeis,
      headHandleHyperbolicNielsen_backward_of_ne j (handleU k) hne,
      heisEvalZ_gen]
    simp [hyperXU, headHandlePairSwap, pairUSlot, hk]

@[simp] private theorem hyperUV_dual_handleU
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hyperDual t (hyperXU t j v) (hyperYV t j lam) E E₂ j (handleU k) = 0 := by
  by_cases hk : k = j
  · subst k
    rw [hyperDual, hyperHeis, headHandleHyperbolicNielsen_backward_handleU,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen, HeisLift.mul_l]
    simp [hyperYV, pairVSlot_zero]
  · have hne : handleU k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleU, Generator.equivFin] at H'
      exact hk (Fin.ext (by omega))
    rw [hyperDual, hyperHeis,
      headHandleHyperbolicNielsen_backward_of_ne j (handleU k) hne,
      heisEvalZ_gen]
    simp [hyperYV, headHandlePairSwap, pairVSlot_zero, hk]

@[simp] private theorem hyperUV_primal_handleV
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hyperPrimal t (hyperXU t j v) (hyperYV t j lam) E E₂ j (handleV k) = 0 := by
  by_cases hk : k = j
  · subst k
    rw [hyperPrimal, hyperHeis, headHandleHyperbolicNielsen_backward_handleV,
      heisEvalZ_gen]
    simp [hyperXU, pairUSlot]
  · have hne : handleV k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleV, handleU, Generator.equivFin] at H'
      omega
    rw [hyperPrimal, hyperHeis,
      headHandleHyperbolicNielsen_backward_of_ne j (handleV k) hne,
      heisEvalZ_gen]
    simp [hyperXU, headHandlePairSwap, pairUSlot, hk]

@[simp] private theorem hyperUV_dual_handleV
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hyperDual t (hyperXU t j v) (hyperYV t j lam) E E₂ j (handleV k) =
      if k = j then lam else 0 := by
  by_cases hk : k = j
  · subst k
    rw [hyperDual, hyperHeis, headHandleHyperbolicNielsen_backward_handleV,
      heisEvalZ_gen]
    simp [hyperYV, pairVSlot]
  · have hne : handleV k ≠ handleU j := by
      intro H
      have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleV, handleU, Generator.equivFin] at H'
      omega
    rw [hyperDual, hyperHeis,
      headHandleHyperbolicNielsen_backward_of_ne j (handleV k) hne,
      heisEvalZ_gen]
    simp [hyperYV, headHandlePairSwap, pairVSlot, hk]

private theorem hyperUV_dualZero_mFactors
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A)
    (lam : ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hs : ∀ a : A, t.σ • a = a) (alpha : ℕ) :
    DualZero (hyperDual t (hyperXU t j v) (hyperYV t j lam) E E₂ j)
      (PWord.prodList (Words.MCompact.mFactors alpha h)) := by
  have hsD : ∀ mu : ElemDual A, t.σ • mu = mu := elemDual_smul_eq_self hs
  have hsInvD : t.σ⁻¹ • lam = lam := inv_smul_eq_iff.mpr (hsD lam).symm
  rw [dualZero_prodList]
  intro w hw
  simp only [Words.MCompact.mFactors, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [DualZero, hyperDual, hyperHeis, hyperYV, Words.MCompact.a0W,
      sigma2W, PWord.omega2Pow, Words.MCompact.j2W, Words.MCompact.eRevW,
      Words.MCompact.deltaC, pairVSlot, hsInvD]

theorem heisZ_headHandleHyperbolicW_UV
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    (heisEvalZ ⇑t (hyperXU t j v) (hyperYV t j lam) E E₂
      (headHandleHyperbolicW alpha j)).z = lam v := by
  rw [headHandleHyperbolicW]
  change (PWord.evalZ (heisGen ⇑t (hyperXU t j v) (hyperYV t j lam)) E E₂
    (PWord.subst (headHandleHyperbolicNielsen j).backward
      (Words.MCompact.mCompactW alpha h))).z = lam v
  rw [PWord.evalZ_subst]
  change (PWord.evalZ
    (hyperHeis t (hyperXU t j v) (hyperYV t j lam) E E₂ j) E E₂
      (Words.MCompact.mCompactW alpha h)).z = lam v
  rw [hyperHeis_eq_heisGen t (hyperXU t j v) (hyperYV t j lam) E E₂ j
    (by simp [hyperXU]) (by simp [hyperYV])]
  let s := hyperMark t (hyperXU t j v) (hyperYV t j lam) E E₂ j
  let b := hyperPrimal t (hyperXU t j v) (hyperYV t j lam) E E₂ j
  let c := hyperDual t (hyperXU t j v) (hyperYV t j lam) E E₂ j
  change (heisEvalZ ⇑s b c E E₂ (Words.MCompact.mCompactW alpha h)).z = lam v
  have hswild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), s.x i • a = a :=
    hyperMark_wild_trivial t _ _ E E₂ j hs hwild
  have hP := heisEvalZ_mem_heisDualPure_of_dualZero ⇑s b c E E₂
    (PWord.prodList (Words.MCompact.mFactors alpha h))
    (hyperUV_dualZero_mFactors t j v lam E E₂ hs alpha)
  have hPz : ((Words.MCompact.mFactors alpha h).map
      (heisEvalZ ⇑s b c E E₂)).prod.z = 0 := by
    rw [← heisEvalZ_prodList]
    exact hP.2
  have hPl : ((Words.MCompact.mFactors alpha h).map
      (heisEvalZ ⇑s b c E E₂)).prod.l = 0 := by
    rw [← heisEvalZ_prodList]
    exact hP.1
  have hHz := Certificates.MCompact.heisF_handlesW_z s b c E E₂ hswild
  have hsum : (∑ k, (c (handleU k) (b (handleV k))
      + c (handleV k) (b (handleU k)))) = lam v := by
    rw [Finset.sum_eq_single j]
    · simp [b, c, hs]
    · intro k _ hk
      simp [b, c, hs, hk]
    · simp
  rw [Words.MCompact.mCompactW, heisEvalZ_prodList, List.map_append,
    List.prod_append, Certificates.MCompact.heisEvalZ_handleTailW]
  rw [heisMul_z_of_l_eq_zero _ _ hPl, hPz, hHz, hsum, zero_add]

def headHandleHyperbolicRawFamily (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha h q : ℕ) (j : Fin h) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  fun l ↦ heisToFree E E₂
    (gammaFam (2 + 2 * h) q (headHandleHyperbolicW alpha j) l)

theorem heisEta1_headHandleHyperbolicRawFamily_VU
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha q : ℕ)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    heisEta1 ⇑t (headHandleHyperbolicRawFamily E E₂ alpha h q j)
      (hyperXV t j v) (hyperYU t j lam) = lam v := by
  rw [heisEta1_apply, Fin.sum_univ_two]
  change (FreeGroup.lift (heisGen ⇑t (hyperXV t j v) (hyperYU t j lam))
      (heisToFree E E₂ (tameRelW (2 + 2 * h) q))).z
    + (FreeGroup.lift (heisGen ⇑t (hyperXV t j v) (hyperYU t j lam))
      (heisToFree E E₂ (headHandleHyperbolicW alpha j))).z = lam v
  rw [← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]
  rw [heisZ_tameRelW_eq_zero_of_tame_offsets_zero t _ _ E E₂
      (by simp [hyperXV]) (by simp [hyperXV])
      (by simp [hyperYU]) (by simp [hyperYU]),
    zero_add]
  exact heisZ_headHandleHyperbolicW_VU t j v lam E E₂ alpha hs hwild

theorem heisEta1_headHandleHyperbolicRawFamily_UV
    (t : Marking (2 + 2 * h) C) (j : Fin h) (v : A) (lam : ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha q : ℕ)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    heisEta1 ⇑t (headHandleHyperbolicRawFamily E E₂ alpha h q j)
      (hyperXU t j v) (hyperYV t j lam) = lam v := by
  rw [heisEta1_apply, Fin.sum_univ_two]
  change (FreeGroup.lift (heisGen ⇑t (hyperXU t j v) (hyperYV t j lam))
      (heisToFree E E₂ (tameRelW (2 + 2 * h) q))).z
    + (FreeGroup.lift (heisGen ⇑t (hyperXU t j v) (hyperYV t j lam))
      (heisToFree E E₂ (headHandleHyperbolicW alpha j))).z = lam v
  rw [← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]
  rw [heisZ_tameRelW_eq_zero_of_tame_offsets_zero t _ _ E E₂
      (by simp [hyperXU]) (by simp [hyperXU])
      (by simp [hyperYV]) (by simp [hyperYV]),
    zero_add]
  exact heisZ_headHandleHyperbolicW_UV t j v lam E E₂ alpha hs hwild

end EvenMHeadHandleHyperbolic
end Instances
end
end GQ2.Dyadic

section AxiomAudit

open GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolic

#print axioms headHandleHyperbolicNielsen
#print axioms headHandleHyperbolicW
#print axioms headHandleHyperbolicNielsen_backward_of_ne
#print axioms headHandleHyperbolicNielsen_backward_handleU
#print axioms headHandleHyperbolicNielsen_backward_tau
#print axioms headHandleHyperbolicNielsen_backward_sigma
#print axioms headHandleHyperbolicNielsen_backward_handleV
#print axioms headHandleHyperbolicNielsen_backward_coreZero
#print axioms headHandleHyperbolicNielsen_backward_coreOne
#print axioms headHandleHyperbolicNielsen_backward_coreTwo
#print axioms pairUSlot
#print axioms hyperXU
#print axioms hyperXV
#print axioms hyperYU
#print axioms hyperYV
#print axioms heisZ_headHandleHyperbolicW_VU
#print axioms heisZ_headHandleHyperbolicW_UV
#print axioms headHandleHyperbolicRawFamily
#print axioms heisEta1_headHandleHyperbolicRawFamily_VU
#print axioms heisEta1_headHandleHyperbolicRawFamily_UV

end AxiomAudit
