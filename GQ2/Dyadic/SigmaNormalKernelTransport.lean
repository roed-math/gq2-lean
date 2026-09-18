/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameNormalStokes

/-!
# Cocycle kernels from doubly normalized comparisons

At an unramified simple nontrivial action, the tame row kills tau and a coboundary
kills sigma. Thus a comparison only on sigma=tau=0 determines the complete kernel.
This avoids requiring equality of first differentials away from normal cochains.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH Count Certificates

private theorem kernel_imp_of_sigma_tau_normal
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0) (htau : ∀ a : A, t.τ • a=a) (hq : Even q)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (R R' : PWord (Generator n))
    (hsq : ∀ a : A, heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k))
      (heisD0 ⇑t a)=0)
    (hsq' : ∀ a : A, heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k))
      (heisD0 ⇑t a)=0)
    (hcomp : ∀ x : Generator n → A, x .sigma=0 → x .tau=0 →
      (heisEvalZ ⇑t x 0 E E₂ R).a=(heisEvalZ ⇑t x 0 E E₂ R').a)
    (x : Generator n → A)
    (hx : heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) x=0) :
    heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) x=0 := by
  have hxτ := tau_eq_zero_of_gammaFam_cocycle_unram t E E₂ hA₂ htau hq R x hx
  obtain ⟨a, ha⟩ := surjective_smul_sub_of_fixedPointFree hsigma (x .sigma)
  let y := x - heisD0 (⇑t) a
  have hyσ : y .sigma=0 := by simp [y, heisD0_apply, ha]
  have hyτ : y .tau=0 := by simp [y, heisD0_apply, htau, hxτ]
  have hy : heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) y=0 := by
    rw [map_sub, hx, hsq a, sub_self]
  have hy' : heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) y=0 := by
    funext k
    fin_cases k
    · exact congrFun hy 0
    · have hk := congrFun hy (1 : Fin 2)
      change (FreeGroup.lift (heisGen (⇑t) y 0) (heisToFree E E₂ R')).a = 0
      simp only [heisD1_apply, gammaFam_one, ← heisEvalZ_eq_lift, Pi.zero_apply] at hk ⊢
      rw [← hcomp y hyσ hyτ]
      exact hk
  rw [map_sub, hsq' a, sub_zero] at hy'
  exact hy'

/-- The normal comparison only needs the chain-square identities, not actual raw relator
death in a nonfaithful coefficient group. -/
theorem heisD1_gammaFam_kernel_iff_of_sigma_tau_normal_of_square
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0) (htau : ∀ a : A, t.τ • a=a) (hq : Even q)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (R R' : PWord (Generator n))
    (hsq : ∀ a : A, heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k))
      (heisD0 ⇑t a)=0)
    (hsq' : ∀ a : A, heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k))
      (heisD0 ⇑t a)=0)
    (hcomp : ∀ x : Generator n → A, x .sigma=0 → x .tau=0 →
      (heisEvalZ ⇑t x 0 E E₂ R).a=(heisEvalZ ⇑t x 0 E E₂ R').a)
    (x : Generator n → A) :
    heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) x=0 ↔
      heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) x=0 :=
  ⟨kernel_imp_of_sigma_tau_normal t E E₂ hA₂ htau hq hsigma R R' hsq hsq' hcomp x,
   kernel_imp_of_sigma_tau_normal t E E₂ hA₂ htau hq hsigma R' R hsq' hsq
     (fun y hs ht ↦ (hcomp y hs ht).symm) x⟩

/-- Equality of first jets on sigma=tau=0 identifies the entire cocycle kernels. -/
theorem heisD1_gammaFam_kernel_iff_of_sigma_tau_normal
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0) (htau : ∀ a : A, t.τ • a=a) (hq : Even q)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (R R' : PWord (Generator n))
    (hr : ∀ k, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam n q R k))=1)
    (hr' : ∀ k, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam n q R' k))=1)
    (hcomp : ∀ x : Generator n → A, x .sigma=0 → x .tau=0 →
      (heisEvalZ ⇑t x 0 E E₂ R).a=(heisEvalZ ⇑t x 0 E E₂ R').a)
    (x : Generator n → A) :
    heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) x=0 ↔
      heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) x=0 :=
  heisD1_gammaFam_kernel_iff_of_sigma_tau_normal_of_square t E E₂ hA₂ htau hq
    hsigma R R' (heisD1_comp_heisD0 ⇑t _ hr) (heisD1_comp_heisD0 ⇑t _ hr') hcomp x

/-- A normal form is unchanged when both the cocycle kernel and coboundary map agree. -/
theorem normalForm_of_same_kernel
    {ι ρ C A W : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A] [Fintype ι]
    (c : ι → C) (w w' : ρ → FreeGroup ι) (normal : W → (ι → A))
    (hkernel : ∀ x, heisD1 (A := A) c w x=0 ↔ heisD1 c w' x=0)
    (hmem : ∀ p, heisD1 c w (normal p)=0)
    (hnf : ∀ x, heisD1 (A := A) c w x=0 →
      ∃! p, x-normal p ∈ Set.range (heisD0 c)) :
    (∀ p, heisD1 c w' (normal p)=0) ∧
      ∀ x, heisD1 (A := A) c w' x=0 →
        ∃! p, x-normal p ∈ Set.range (heisD0 c) :=
  ⟨fun p ↦ (hkernel _).mp (hmem p), fun x hx ↦ hnf x ((hkernel x).mpr hx)⟩

#print axioms heisD1_gammaFam_kernel_iff_of_sigma_tau_normal
#print axioms heisD1_gammaFam_kernel_iff_of_sigma_tau_normal_of_square
#print axioms normalForm_of_same_kernel

end
end GQ2.Dyadic
