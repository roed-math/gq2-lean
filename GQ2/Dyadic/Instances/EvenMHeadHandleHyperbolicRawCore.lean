/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMRamifiedRow

/-!
# The ramified compact core with free sigma offsets

When the sigma base acts trivially, the parity of the compact-M exponent removes its
first jets from the leading square and commutator.  Conjugation by these even powers
preserves the ramified delta jets and central charges.  The reversed correction block
therefore cancels the leading x-zero diagonal, leaving the standard compact-M core
pairing even when both sigma offsets are arbitrary.

This supplies the core calculation needed after promoting a handle into the tame head;
the selected handle base itself need not act trivially in that application.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Words.MCompact
open Certificates.MCompact

namespace Instances.EvenMHeadHandleHyperbolicRawCore

variable {h alpha : ℕ} {C A : Type*} [Group C] [Finite C]
  [AddCommGroup A] [Finite A] [DistribMulAction C A]

omit [Finite C] [Finite A] in
private theorem heisJ2_trivial_of_zero_coreTwo
    (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A) (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hcore2 : ∀ a : A, t (coreLetter h 2) • a = a)
    (hxτ : x .tau = 0) (hyτ : y .tau = 0)
    (hx2 : x (coreLetter h 2) = 0) (hy2 : y (coreLetter h 2) = 0) :
    heisEvalZ ⇑t x y E E₂ (j2W h) ∈ heisTrivial A C := by
  have hX : heisEvalZ ⇑t x y E E₂ (.gen (coreLetter h 2)) ∈ heisTrivial A C := by
    rw [heisEvalZ_gen]
    exact ⟨hx2, hy2, rfl⟩
  have hT : heisEvalZ ⇑t x y E E₂ (.gen .tau) ∈ heisTrivial A C := by
    rw [heisEvalZ_gen]
    exact ⟨hxτ, hyτ, rfl⟩
  have hXg : ∀ a : A,
      (heisEvalZ ⇑t x y E E₂ (.gen (coreLetter h 2))).g • a = a := hcore2
  rw [j2W, heisEvalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    heisEvalZ_inv, heisEvalZ_conj, PWord.omega2Pow, heisEvalZ_profPow]
  apply mul_mem
  · exact inv_mem (heisConjR_mem_heisTrivial hXg hX)
  · apply zpow_mem
    rw [heisEvalZ_prodList]
    simpa using mul_mem hX hT

private theorem heisERev_ram_sigma_trivial
    (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A) (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hS₂ : ∀ a : A, (sigma2Z t x y E E₂).g • a = a)
    (hα : 2 ≤ alpha)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C) :
    (heisEvalZ ⇑t x y E E₂ (eRevW alpha h)).a = 0 ∧
    (heisEvalZ ⇑t x y E E₂ (eRevW alpha h)).l = 0 ∧
    (heisEvalZ ⇑t x y E E₂ (eRevW alpha h)).z =
      y (coreLetter h 1) (x (coreLetter h 1))
        + y (coreLetter h 0) (x (coreLetter h 0)) := by
  have hd := fun i ↦ MCompactRam.heisEvalZ_deltaCert_ram t x y E E₂
    hA₂ hwild hτfpf hTodd hresA hresD hres i
  have hc : ∀ (i : Fin 3) (n : ℕ), Even n →
      let p := heisEvalZ ⇑t x y E E₂
        (.conj (Words.MCompact.deltaC h i) (.zpow sigma2W (n : ℤ)))
      p.a = x (coreLetter h i) ∧ p.l = y (coreLetter h i) ∧
        p.z = (heisEvalZ ⇑t x y E E₂ (Words.MCompact.deltaC h i)).z ∧
        ∀ a : A, p.g • a = a := by
    intro i n hn
    dsimp only
    have hj := (heisZ_sigma2Pow_jetZero t x y E E₂ hA₂ hS₂ hn).1
    have hg : ∀ a : A,
        (heisEvalZ ⇑t x y E E₂ (.zpow sigma2W (n : ℤ))).g⁻¹ • a = a := by
      rw [heisEvalZ_zpow, sigma2Z_def, heisZpow_g]
      exact mem_trivAct.mp (inv_mem (zpow_mem (mem_trivAct.mpr hS₂) _))
    rw [heisEvalZ_conj, heisConjR_of_trivial _ _ (hd i).2.2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hg _).trans (hd i).1
    · exact (elemDual_smul_eq_self hg _).trans (hd i).2.1
    · change _ + _ + _ = _
      rw [hj.1, hj.2, ElemDual.zero_apply, map_zero, add_zero, add_zero]
    · exact mem_trivAct.mp (trivAct_conjR (mem_trivAct.mpr (hd i).2.2) _)
  have h1 := hc 1 (2 * mOf alpha) (even_two_mul _)
  have h2 := hc 1 (mOf alpha) (even_mOf hα)
  have h3 := hc 0 (mOf alpha) (even_mOf hα)
  have hev : heisEvalZ ⇑t x y E E₂ (eRevW alpha h) =
      heisEvalZ ⇑t x y E E₂
        (.conj (Words.MCompact.deltaC h 1) (.zpow sigma2W ((2 * mOf alpha : ℕ) : ℤ))) *
      (heisEvalZ ⇑t x y E E₂
        (.conj (Words.MCompact.deltaC h 1) (.zpow sigma2W (mOf alpha : ℤ))) *
      (heisEvalZ ⇑t x y E E₂
        (.conj (Words.MCompact.deltaC h 0) (.zpow sigma2W (mOf alpha : ℤ))) *
       heisEvalZ ⇑t x y E E₂ (Words.MCompact.deltaC h 0))) := by
    simp [eRevW, heisEvalZ_one]
  rw [hev]
  obtain ⟨ha, hl, hz⟩ := heisMul_four_of_trivial _ _ _ _ h1.2.2.2 h2.2.2.2 h3.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [ha, h1.1, h2.1, h3.1, (hd 0).1, hA₂, add_zero, hA₂]
  · rw [hl, h1.2.1, h2.2.1, h3.2.1, (hd 0).2.1,
      ElemDual.add_self_eq_zero, add_zero, ElemDual.add_self_eq_zero]
  · rw [hz, h1.2.2.1, h2.2.2.1, h3.2.2.1,
      h2.1, h3.1, (hd 0).1,
      h1.2.1, h2.2.1, h3.2.1]
    generalize (heisEvalZ ⇑t x y E E₂ (Words.MCompact.deltaC h 1)).z = c₁
    generalize (heisEvalZ ⇑t x y E E₂ (Words.MCompact.deltaC h 0)).z = c₂
    generalize y (coreLetter h 1) (x (coreLetter h 1)) = c₃
    generalize y (coreLetter h 1) (x (coreLetter h 0)) = c₄
    generalize y (coreLetter h 0) (x (coreLetter h 0)) = c₅
    revert c₁ c₂ c₃ c₄ c₅
    decide

/-- The ramified compact core formula permits arbitrary sigma offsets when its base
acts trivially.  The parity of the compact exponent eliminates all extra sigma jets. -/
theorem heisZ_mFactors_ram_sigma_trivial
    (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A) (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hα : 2 ≤ alpha)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hxτ : x .tau = 0) (hyτ : y .tau = 0)
    (hx2 : x (coreLetter h 2) = 0) (hy2 : y (coreLetter h 2) = 0)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C) :
    (heisEvalZ ⇑t x y E E₂ (PWord.prodList (mFactors alpha h))).z =
      y (coreLetter h 1) (x (coreLetter h 1)) +
        (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0))) := by
  have hS₂ : ∀ a : A, (sigma2Z t x y E E₂).g • a = a := by
    rw [sigma2Z_g]
    exact mem_trivAct.mp (zpow_mem (mem_trivAct.mpr hs) _)
  have h1 := heisF_leadingSquare t x y E E₂ hA₂ hwild hS₂ hα
  have h2 := heisF_leadingComm t x y E E₂ hA₂ hwild hS₂ hα
  have h3 := heisZ_sigma2Pow_two_mul t x y E E₂ hA₂ hS₂ hα
  have h4 := heisJ2_trivial_of_zero_coreTwo t x y E E₂
    (fun a ↦ hwild _ a) hxτ hyτ hx2 hy2
  have h5 := heisERev_ram_sigma_trivial t x y E E₂ hA₂ hwild hS₂
    hα hτfpf hTodd hresA hresD hres
  rw [heisEvalZ_prodList]
  simp only [mFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [h1, h2, h3]
  simp only [HeisLift.mul_z, ElemDual.zero_apply,
    zero_add, add_zero, h4.2.1, h4.2.2, h5.2.2]
  generalize y (coreLetter h 0) (x (coreLetter h 0)) = c₁
  generalize y (coreLetter h 1) (x (coreLetter h 1)) = c₂
  generalize y (coreLetter h 0) (x (coreLetter h 1)) = c₃
  generalize y (coreLetter h 1) (x (coreLetter h 0)) = c₄
  revert c₁ c₂ c₃ c₄
  decide

omit [Finite C] [Finite A] in
theorem heisHandles_zeroV
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (x : Generator (2 + 2 * h) → A) (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hV : ∀ (k : Fin h) (a : A), t (handleV k) • a = a)
    (hU : ∀ k : Fin h, k ≠ j → ∀ a : A, t (handleU k) • a = a)
    (hxV : x (handleV j) = 0) (hyV : y (handleV j) = 0) :
    heisEvalZ ⇑t x y E E₂ (Words.handlesW h) ∈ heisJetZero A C ∧
    (heisEvalZ ⇑t x y E E₂ (Words.handlesW h)).z =
      ∑ k, (y (handleU k) (x (handleV k)) + y (handleV k) (x (handleU k))) := by
  have hc : ∀ k : Fin h,
      let p := heisEvalZ ⇑t x y E E₂ (.comm (.gen (handleU k)) (.gen (handleV k)))
      p ∈ heisJetZero A C ∧
        p.z = y (handleU k) (x (handleV k)) + y (handleV k) (x (handleU k)) := by
    intro k
    dsimp only
    rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen]
    by_cases hk : k = j
    · subst k
      rw [heisCommR_of_trivial_right _ _ (hV j)]
      simp [hxV, hyV]
    · rw [heisCommR_of_trivial _ _ (hU k hk) (hV k)]
      exact ⟨⟨rfl, rfl⟩, rfl⟩
  rw [Words.handlesW]
  have hm : ∀ w ∈ (List.finRange h).map (fun k ↦
      (PWord.comm (.gen (handleU k)) (.gen (handleV k)) :
        PWord (Generator (2 + 2 * h)))),
      heisEvalZ ⇑t x y E E₂ w ∈ heisJetZero A C := by
    intro w hw
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hw
    exact (hc k).1
  refine ⟨(heisEvalZ_prodList_jetZero ⇑t x y E E₂ hm).1, ?_⟩
  rw [(heisEvalZ_prodList_jetZero ⇑t x y E E₂ hm).2,
    List.map_map, Fin.sum_univ_def]
  congr 1
  exact List.map_congr_left (fun k _ ↦ (hc k).2)


#print axioms heisHandles_zeroV
#print axioms heisZ_mFactors_ram_sigma_trivial

end Instances.EvenMHeadHandleHyperbolicRawCore
end
end GQ2.Dyadic
