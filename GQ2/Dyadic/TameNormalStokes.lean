/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.StokesKernelTransport
import GQ2.Dyadic.Instances.LEvenQStokes

/-!
# Stokes transport from comparison on tau-normal cochains

The canonical tame row is invertible in the tau coordinate on an elementary
unramified module. Thus every cocycle is tau-normal, and word comparisons on
tau-normal cochains identify the kernels and the pairings on cycles.

Two complementary transport theorems handle the simple-module branches. When
both first differentials are surjective, finiteness transfers surjectivity.
When every generator acts trivially, actual relator death and the Stokes
endpoint force both rows to be the tau coordinate; the ranges therefore agree.
Neither argument assumes equality of Fox maps in the general unramified case.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH Count Certificates

/-- The canonical tame row forces every unramified cocycle to vanish at tau. -/
theorem tau_eq_zero_of_gammaFam_cocycle_unram
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0) (htau : ∀ a : A, t.τ • a=a) (hq : Even q)
    (R : PWord (Generator n)) (x : Generator n → A)
    (hx : heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) x=0) :
    x .tau = 0 := by
  have hk := congrFun hx (0 : Fin 2)
  simp only [heisD1_apply, gammaFam_zero, ← heisEvalZ_eq_lift,
    heisA_tameRelW_unram t x 0 E E₂ hA₂ htau hq, Pi.zero_apply] at hk
  have hs := congrArg (fun a : A ↦ t.σ • a) hk
  rwa [smul_zero, smul_inv_smul] at hs

/-- Agreement on tau-normal first jets determines the entire cocycle kernel. -/
theorem heisD1_gammaFam_kernel_iff_of_normal
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0) (htau : ∀ a : A, t.τ • a=a) (hq : Even q)
    (R R' : PWord (Generator n))
    (hcomp : ∀ x : Generator n → A, x .tau=0 →
      (heisEvalZ ⇑t x 0 E E₂ R).a=(heisEvalZ ⇑t x 0 E E₂ R').a)
    (x : Generator n → A) :
    heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) x=0 ↔
      heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) x=0 := by
  constructor
  · intro hx
    have ht := tau_eq_zero_of_gammaFam_cocycle_unram t E E₂ hA₂ htau hq R x hx
    funext k
    fin_cases k
    · exact congrFun hx 0
    · have hk := congrFun hx (1 : Fin 2)
      change (FreeGroup.lift (heisGen (⇑t) x 0) (heisToFree E E₂ R')).a = 0
      simp only [heisD1_apply, gammaFam_one, ← heisEvalZ_eq_lift, Pi.zero_apply] at hk ⊢
      rw [← hcomp x ht]
      exact hk
  · intro hx
    have ht := tau_eq_zero_of_gammaFam_cocycle_unram t E E₂ hA₂ htau hq R' x hx
    funext k
    fin_cases k
    · exact congrFun hx 0
    · have hk := congrFun hx (1 : Fin 2)
      change (FreeGroup.lift (heisGen (⇑t) x 0) (heisToFree E E₂ R)).a = 0
      simp only [heisD1_apply, gammaFam_one, ← heisEvalZ_eq_lift, Pi.zero_apply] at hk ⊢
      rw [hcomp x ht]
      exact hk

/-- A normal central-charge comparison gives the traced pairing comparison. -/
theorem heisEta1_gammaFam_eq_of_normal
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R R' : PWord (Generator n))
    (hcomp : ∀ (x : Generator n → A) (y : Generator n → ElemDual A),
      x .tau=0 → y .tau=0 →
      (heisEvalZ ⇑t x y E E₂ R).z=(heisEvalZ ⇑t x y E E₂ R').z)
    (x : Generator n → A) (y : Generator n → ElemDual A)
    (hx : x .tau=0) (hy : y .tau=0) :
    heisEta1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) x y =
      heisEta1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) x y := by
  simp only [heisEta1_apply, Fin.sum_univ_two, gammaFam_zero, gammaFam_one,
    ← heisEvalZ_eq_lift]
  rw [hcomp x y hx hy]

/-- Normal comparisons transport Stokes duality in the surjective branch. -/
theorem stokesDuality_gammaFam_of_normal_comparison_of_surjective
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0) (htau : ∀ a : A, t.τ • a=a) (hq : Even q)
    (R R' : PWord (Generator n))
    (hcompA : ∀ x : Generator n → A, x .tau=0 →
      (heisEvalZ ⇑t x 0 E E₂ R).a=(heisEvalZ ⇑t x 0 E E₂ R').a)
    (hcompD : ∀ y : Generator n → ElemDual A, y .tau=0 →
      (heisEvalZ ⇑t y 0 E E₂ R).a=(heisEvalZ ⇑t y 0 E E₂ R').a)
    (hcompZ : ∀ (x : Generator n → A) (y : Generator n → ElemDual A),
      x .tau=0 → y .tau=0 →
      (heisEvalZ ⇑t x y E E₂ R).z=(heisEvalZ ⇑t x y E E₂ R').z)
    (hsurjA : Function.Surjective (heisD1 (A := A) ⇑t
      (fun k ↦ heisToFree E E₂ (gammaFam n q R k))))
    (hsurjD : Function.Surjective (heisD1 (A := ElemDual A) ⇑t
      (fun k ↦ heisToFree E E₂ (gammaFam n q R k))))
    (H : StokesDuality ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) A) :
    StokesDuality ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) A := by
  have htauD : ∀ y : ElemDual A, t.τ • y=y := by
    intro y
    ext a
    rw [ElemDual.smul_apply, inv_smul_eq_iff.mpr (htau a).symm]
  apply stokesDuality_of_same_kernels_pairing_of_surjective ⇑t _ _
    (heisD1_gammaFam_kernel_iff_of_normal t E E₂ hA₂ htau hq R R' hcompA)
    (heisD1_gammaFam_kernel_iff_of_normal t E E₂ ElemDual.add_self_eq_zero
      htauD hq R R' hcompD) hsurjA hsurjD
  · intro x y hx hy
    exact heisEta1_gammaFam_eq_of_normal t E E₂ R R' hcompZ x y
      (tau_eq_zero_of_gammaFam_cocycle_unram t E E₂ hA₂ htau hq R x hx)
      (tau_eq_zero_of_gammaFam_cocycle_unram t E E₂ ElemDual.add_self_eq_zero htauD hq R y hy)
  · exact H

/-- With trivial action, relator death and the endpoint force both rows to be tau. -/
theorem heisD1_gammaFam_eq_diagonal_of_trivial_action
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator n) (a : A), t g • a=a) (hq : Even q)
    (R : PWord (Generator n))
    (hr : ∀ k, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam n q R k))=1)
    (hend : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R k)))
    (x : Generator n → A) :
    heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) x = fun _ ↦ x .tau := by
  let w := fun k ↦ heisToFree E E₂ (gammaFam n q R k)
  have hz : ∑ k, heisD1 ⇑t w x k = 0 := by
    by_contra hne
    obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hne
    have hs := DFunLike.congr_fun (stokes_square₁ ⇑t w hr hend x) lam
    have hd0 : heisD0 ⇑t lam = 0 := by
      funext g
      change t g • lam - lam = 0
      have hfix : t g • lam = lam := by
        ext a
        rw [ElemDual.smul_apply, inv_smul_eq_iff.mpr (htriv g a).symm]
      rw [hfix, sub_self]
    change heisEta1 ⇑t w x (heisD0 ⇑t lam) = lam (∑ k, heisD1 ⇑t w x k) at hs
    rw [hd0, map_zero] at hs
    exact hlam hs.symm
  have hzero : heisD1 ⇑t w x 0 = x .tau := by
    change (FreeGroup.lift (heisGen (⇑t) x 0) (heisToFree E E₂ (tameRelW n q))).a = _
    rw [← heisEvalZ_eq_lift, heisA_tameRelW_unram t x 0 E E₂ hA₂ (htriv .tau) hq]
    exact inv_smul_eq_iff.mpr (htriv .sigma (x .tau)).symm
  have hone : heisD1 ⇑t w x 1 = x .tau := by
    apply add_left_cancel (a := x .tau)
    rw [← hzero, ← Fin.sum_univ_two, hz, hzero, hA₂]
  funext k
  fin_cases k
  · exact hzero
  · exact hone

/-- For trivial actions, only the normal central-charge comparison is needed. -/
theorem stokesDuality_gammaFam_of_normal_comparison_of_trivial_action
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator n) (a : A), t g • a=a) (hq : Even q)
    (R R' : PWord (Generator n))
    (hr : ∀ k, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam n q R k))=1)
    (hr' : ∀ k, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam n q R' k))=1)
    (hend : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R k)))
    (hend' : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)))
    (hcompZ : ∀ (x : Generator n → A) (y : Generator n → ElemDual A),
      x .tau=0 → y .tau=0 →
      (heisEvalZ ⇑t x y E E₂ R).z=(heisEvalZ ⇑t x y E E₂ R').z)
    (H : StokesDuality ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) A) :
    StokesDuality ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) A := by
  have htrivD : ∀ (g : Generator n) (y : ElemDual A), t g • y=y := by
    intro g y
    ext a
    rw [ElemDual.smul_apply, inv_smul_eq_iff.mpr (htriv g a).symm]
  have hdA : heisD1 (A := A) ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) =
      heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) := by
    apply AddMonoidHom.ext
    intro x
    rw [heisD1_gammaFam_eq_diagonal_of_trivial_action t E E₂ hA₂ htriv hq R hr hend x,
      heisD1_gammaFam_eq_diagonal_of_trivial_action t E E₂ hA₂ htriv hq R' hr' hend' x]
  have hdD : heisD1 (A := ElemDual A) ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) =
      heisD1 ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R' k)) := by
    apply AddMonoidHom.ext
    intro y
    rw [heisD1_gammaFam_eq_diagonal_of_trivial_action t E E₂ ElemDual.add_self_eq_zero htrivD hq R hr hend y,
      heisD1_gammaFam_eq_diagonal_of_trivial_action t E E₂ ElemDual.add_self_eq_zero htrivD hq R' hr' hend' y]
  apply stokesDuality_of_same_kernels_ranges_pairing ⇑t _ _
    (fun x ↦ by rw [hdA]) (fun y ↦ by rw [hdD])
    (by rw [hdA]) (by rw [hdD])
  · intro x y hx hy
    exact heisEta1_gammaFam_eq_of_normal t E E₂ R R' hcompZ x y
      (tau_eq_zero_of_gammaFam_cocycle_unram t E E₂ hA₂ (htriv .tau) hq R x hx)
      (tau_eq_zero_of_gammaFam_cocycle_unram t E E₂ ElemDual.add_self_eq_zero (htrivD .tau) hq R y hy)
  · exact H

#print axioms tau_eq_zero_of_gammaFam_cocycle_unram
#print axioms heisD1_gammaFam_kernel_iff_of_normal
#print axioms heisEta1_gammaFam_eq_of_normal
#print axioms stokesDuality_gammaFam_of_normal_comparison_of_surjective
#print axioms heisD1_gammaFam_eq_diagonal_of_trivial_action
#print axioms stokesDuality_gammaFam_of_normal_comparison_of_trivial_action

end
end GQ2.Dyadic

