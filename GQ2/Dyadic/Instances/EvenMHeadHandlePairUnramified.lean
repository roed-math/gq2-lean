/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicRawCore
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicRawHelpers
import GQ2.Dyadic.Instances.EvenMHeadHandlePairNielsenStokes
import GQ2.Dyadic.Instances.EvenMHeadHandlePairFox
import GQ2.Dyadic.Instances.N0M0ScalarStokes
import GQ2.Dyadic.Instances.TameCorrectionStokes

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramified

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandleSource Instances.EvenMHeadHandlePairSource
open Instances.EvenMHeadHandlePairCore Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandleHyperbolicRawHelpers
open Instances.EvenMHeadHandleHyperbolicRawCore

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

private theorem coreOnlyMark_handleU (t : Marking (2 + 2 * h) C) (j : Fin h) :
    coreOnlyMark t (handleU j) = 1 := by
  change (if 3 + 2 * (j : ℕ) < 3 then _ else 1) = 1
  rw [if_neg (by omega)]

private theorem coreOnlyMark_handleV (t : Marking (2 + 2 * h) C) (j : Fin h) :
    coreOnlyMark t (handleV j) = 1 := by
  change (if 4 + 2 * (j : ℕ) < 3 then _ else 1) = 1
  rw [if_neg (by omega)]

theorem heisZ_mCompact_coreOnly_of_zeroV
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (x : Generator (2 + 2 * h) → A) (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha : ℕ)
    (hV : ∀ (k : Fin h) (a : A), t (handleV k) • a = a)
    (hU : ∀ k : Fin h, k ≠ j → ∀ a : A, t (handleU k) • a = a)
    (hxV : x (handleV j) = 0) (hyV : y (handleV j) = 0) :
    (heisEvalZ ⇑t x y E E₂ (MCompact.mCompactW alpha h)).z =
      (heisEvalZ ⇑(coreOnlyMark t) x y E E₂ (MCompact.mCompactW alpha h)).z := by
  have ht := heisHandles_zeroV t j x y E E₂ hV hU hxV hyV
  have hs := heisHandles_zeroV (coreOnlyMark t) j x y E E₂
    (by intro k a; rw [coreOnlyMark_handleV, one_smul])
    (by intro k hk a; rw [coreOnlyMark_handleU, one_smul]) hxV hyV
  simp only [MCompact.mCompactW, heisEvalZ_prodList, List.map_append, List.prod_append,
    MCompact.heisEvalZ_handleTailW]
  rw [heisMul_z_of_a_eq_zero _ _ ht.1.1, heisMul_z_of_a_eq_zero _ _ hs.1.1,
    ht.2, hs.2]
  congr 1

private theorem pair_coreZero (j : Fin h) :
    headHandlePairSwap j (coreLetter h 0) = coreLetter h 0 := by
  simp [headHandlePairSwap]

private theorem pair_coreOne (j : Fin h) :
    headHandlePairSwap j (coreLetter h 1) = coreLetter h 1 := by
  simp [headHandlePairSwap]

private theorem pair_core_trivial (t : Marking (2 + 2 * h) C) (j : Fin h)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    ∀ (i : Fin 3) (a : A), t (headHandlePairSwap j (coreLetter h i)) • a = a := by
  intro i a
  rcases i with ⟨i, hi⟩
  interval_cases i
  · change t (headHandlePairSwap j (coreLetter h 0)) • a = a
    rw [pair_coreZero]
    exact hwild _ a
  · change t (headHandlePairSwap j (coreLetter h 1)) • a = a
    rw [pair_coreOne]
    exact hwild _ a
  · change t (headHandlePairSwap j (coreLetter h 2)) • a = a
    rw [headHandlePairSwap_coreTwo]
    exact hwild _ a

/-- The raw pair source has the ordinary compact-M pairing on unramified normal cochains. -/
theorem heisEta1_headHandlePair_normal_unram
    {alpha q : ℕ} (t : Marking (2 + 2 * h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a) (hα : 2 ≤ alpha)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₀ lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A) :
    heisEta1 ⇑t (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l))
      (evenNormal h d₀ d₁ z) (evenNormal h lam₀ lam₁ mu) =
      lam₀ (d₀ + d₁) + lam₁ d₀ +
        ∑ k, (mu (k, 0) (z (k, 1)) + mu (k, 1) (z (k, 0))) := by
  let x := evenNormal h d₀ d₁ z
  let y := evenNormal h lam₀ lam₁ mu
  let s : Marking (2 + 2 * h) C := ⟨fun g => t (headHandlePairSwap j g)⟩
  let b := fun g => x (headHandlePairSwap j g)
  let c := fun g => y (headHandlePairSwap j g)
  have hV : ∀ (k : Fin h) (a : A), s (handleV k) • a = a := by
    intro k a
    by_cases hk : k = j
    · subst k
      change t (headHandlePairSwap j (handleV j)) • a = a
      rw [headHandlePairSwap_handleV_self]
      exact hwild _ a
    · change t (headHandlePairSwap j (handleV k)) • a = a
      rw [headHandlePairSwap]
      simp only [Equiv.trans_apply, headHandleSwap_handleV, tailHandleSwap_handleV, hk, if_false]
      exact hwild _ a
  have hU : ∀ k : Fin h, k ≠ j → ∀ a : A, s (handleU k) • a = a := by
    intro k hk a
    change t (headHandlePairSwap j (handleU k)) • a = a
    rw [headHandlePairSwap]
    simp only [Equiv.trans_apply, headHandleSwap_handleU, hk, if_false, tailHandleSwap_handleU]
    exact hwild _ a
  have hbV : b (handleV j) = 0 := by simp [b, x]
  have hcV : c (handleV j) = 0 := by simp [c, y]
  have hs : ∀ a : A, (coreOnlyMark s).σ • a = a := by
    intro a
    change t (headHandlePairSwap j .sigma) • a = a
    rw [headHandlePairSwap_sigma]
    exact hwild _ a
  have hcore := coreOnlyMark_wild_trivial s (pair_core_trivial t j hwild)
  have htau : ∀ a : A, (coreOnlyMark s).τ • a = a := by
    intro a
    change t (headHandlePairSwap j .tau) • a = a
    rw [headHandlePairSwap_tau]
    exact hτ a
  have hS₂ : ∀ a : A, (MCompact.sigma2Z (coreOnlyMark s) b c E E₂).g • a = a := by
    intro a
    rw [MCompact.sigma2Z_g]
    exact mem_trivAct.mp (zpow_mem (mem_trivAct.mpr hs) _) a
  rw [heisEta1_apply, Fin.sum_univ_two]
  simp only [gammaFam_zero, gammaFam_one, ← heisEvalZ_eq_lift]
  rw [heisZ_tameRelW_eq_zero_of_tame_offsets_zero t _ _ E E₂
    (by simp) (by simp) (by simp) (by simp), zero_add]
  rw [headHandlePairCompactW_eq_nielsenBackward]
  change (PWord.evalZ (heisGen ⇑t x y) E E₂
    (PWord.subst (headHandlePairNielsen j).backward (MCompact.mCompactW alpha h))).z = _
  rw [PWord.evalZ_subst]
  have hmap : (fun g => PWord.evalZ (heisGen ⇑t x y) E E₂
      ((headHandlePairNielsen j).backward g)) = heisGen ⇑s b c := by
    funext g
    change heisGen ⇑t x y ((headHandlePairSwap j).symm g) = _
    rw [headHandlePairSwap_symm]
    rfl
  rw [hmap]
  change (heisEvalZ ⇑s b c E E₂ (MCompact.mCompactW alpha h)).z = _
  rw [heisZ_mCompact_coreOnly_of_zeroV s j b c E E₂ alpha hV hU hbV hcV,
    MCompact.heisZ_mCompact_res_one (coreOnlyMark s) b c E E₂ hA₂ hcore htau
      hS₂ hα (by simp [b, x]) (by simp [c, y]) hE he]
  have hz : ∀ a : A, a + (coreOnlyMark s).σ • a = 0 := by
    intro a
    rw [hs]
    exact hA₂ a
  simp only [hz, map_zero, add_zero]
  let F := fun k : Fin h => mu (k, 0) (z (k, 1)) + mu (k, 1) (z (k, 0))
  have hsum : c .sigma (b (coreLetter h 2)) + c (coreLetter h 2) (b .sigma) +
      ∑ k, (c (handleU k) (b (handleV k)) + c (handleV k) (b (handleU k))) = ∑ k, F k := by
    have hj : c .sigma (b (coreLetter h 2)) + c (coreLetter h 2) (b .sigma) = F j := by
      simp [b, c, x, y, F]
    rw [hj]
    calc
      F j + ∑ k, (c (handleU k) (b (handleV k)) + c (handleV k) (b (handleU k))) =
          ∑ k, ((if k = j then F j else 0) +
            (c (handleU k) (b (handleV k)) + c (handleV k) (b (handleU k)))) := by
              simp [Finset.sum_add_distrib]
      _ = ∑ k, F k := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkj : k = j
        · subst k
          simp [b, c, x, y]
        · have hu : headHandlePairSwap j (handleU k) = handleU k := by
            simp [headHandlePairSwap, hkj]
          have hv : headHandlePairSwap j (handleV k) = handleV k := by
            simp [headHandlePairSwap, hkj]
          simp [b, c, x, y, hu, hv, hkj, F]
  rw [add_assoc _ _ (∑ k, (c (handleU k) (b (handleV k)) + c (handleV k) (b (handleU k)))),
    hsum]
  simp only [b, c, x, y, pair_coreZero, pair_coreOne, evenNormal_coreLetter,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_add]
  dsimp only [F]
  abel

theorem heisD1_headHandlePair_unram_apply [Finite C] [Finite A]
    {alpha q : ℕ} (t : Marking (2 + 2 * h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q)
    (hres : ResolverLifts E (WordLift A C)) (x : Generator (2 + 2 * h) → A) :
    heisD1 ⇑t (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l)) x =
      ![t.σ⁻¹ • x .tau, x .tau + (x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2))] := by
  funext l
  fin_cases l
  · simp only [heisD1_apply, ← heisEvalZ_eq_lift]
    exact (heisEvalZ_a_eq_foxD hres ⇑t x 0 _).trans
      (Certificates.foxD_tameRelW_unram t _ _ hA₂ hτ hq x)
  · simp only [heisD1_apply, ← heisEvalZ_eq_lift]
    exact (heisEvalZ_a_eq_foxD hres ⇑t x 0 _).trans
      (foxD_headHandlePairCompactW_unram t x E E₂ alpha j hA₂ hwild hτ)

theorem headHandlePairStokesDuality_unramified [Finite C] [Finite A]
    {alpha q : ℕ} (t : Marking (2 + 2 * h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q) (hα : 2 ≤ alpha)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (hr : ∀ l : Fin 2, FreeGroup.lift ⇑t (heisToFree E E₂
      (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l)) = 1)
    (hend : IsStokesEndpoint (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l))) :
    StokesDuality ⇑t (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l)) A := by
  apply evenUnramifiedStokesDuality_of_row t _ hA₂ hr hend
    (heisD1_headHandlePair_unram_apply t j E E₂ hA₂ hwild hτ hq hresA)
    (heisD1_headHandlePair_unram_apply t j E E₂
      (fun lam => lam.add_self_eq_zero)
      (fun i lam => elemDual_smul_eq_self (hwild i) lam)
      (fun lam => elemDual_smul_eq_self hτ lam) hq hresD)
    (heisEta1_headHandlePair_normal_unram t j E E₂ hA₂ hwild hτ hα hE he)
    hwild hτ hσfpf

#print axioms heisD1_headHandlePair_unram_apply
#print axioms headHandlePairStokesDuality_unramified
#print axioms heisZ_mCompact_coreOnly_of_zeroV
#print axioms heisEta1_headHandlePair_normal_unram

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramified

