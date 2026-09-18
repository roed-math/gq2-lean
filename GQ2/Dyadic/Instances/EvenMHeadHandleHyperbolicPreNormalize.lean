/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicNormalize

namespace GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicPreNormalize

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore

/-- A unit U row permits clearing D while restoring the paired V row to zero.
Every row other than D and that V row is unchanged. -/
theorem exists_clearD_of_unitHandle
    {alpha h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (j : Fin h) (u : ℤ_[2]ˣ)
    (hU : toAdd (nu (dmGen alpha h (handleIdxU j))) = (u : ℤ_[2]))
    (hV : nu (dmGen alpha h (handleIdxV j)) = 1) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      nu (Psi (dmD alpha h)) = 1 ∧
      nu (Psi (dmGen alpha h (handleIdxV j))) = 1 ∧
      (∀ i : Fin (coreRank h), i ≠ 3 → i ≠ handleIdxV j →
        nu (Psi (dmGen alpha h i)) = nu (dmGen alpha h i)) := by
  let d : ℤ_[2] := toAdd (nu (dmD alpha h))
  let c : ℤ_[2] := toAdd (nu (dmC alpha h))
  let x : ℤ_[2] := -(d * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
  let k : ℤ_[2] := -(x * c * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
  let F : Function.End (Fin (coreRank h) → ℤ_[2]) :=
    frameEnd (frameTauV j k) * frameEnd (frameEichlerV j x)
  have hF : F ∈ Submonoid.closure (frameClearGens h) :=
    mul_mem (Submonoid.subset_closure (frameTauV_mem_clearGens j k))
      (frameEichlerV_mem_clearGens j x)
  obtain ⟨Psi, hmem, hbridge⟩ := exists_dmRealizes alpha h hF
  have huinv : ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (u : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨Psi, chiM_of_mem_dmClearAuts alpha h hmem, ?_, ?_, ?_⟩
  · apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    have H := congrFun (hbridge nu) 3
    change toAdd (nu (Psi (dmD alpha h))) =
      frameTauV j k (frameEichlerV j x (nuFrame nu (dmGen alpha h))) 3 at H
    rw [frameTauV_of_ne j _ _ (Ne.symm (handleIdxU_ne_three j))
      (Ne.symm (handleIdxV_ne_three j)), frameEichlerV_three, smul_eq_mul] at H
    simp only [nuFrame_apply] at H
    rw [H, hU]
    change d + x * (u : ℤ_[2]) = 0
    dsimp only [x]
    rw [neg_mul, mul_assoc, huinv, mul_one, add_neg_cancel]
  · apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    have H := congrFun (hbridge nu) (handleIdxV j)
    change toAdd (nu (Psi (dmGen alpha h (handleIdxV j)))) =
      frameTauV j k (frameEichlerV j x (nuFrame nu (dmGen alpha h)))
        (handleIdxV j) at H
    rw [frameTauV_handleV_self, frameEichlerV_handleV_self,
      frameEichlerV_handleU, smul_eq_mul, smul_eq_mul] at H
    simp only [nuFrame_apply] at H
    rw [H, hU, hV, toAdd_one, zero_add]
    change x * c + k * (u : ℤ_[2]) = 0
    change x * c + -(x * c * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * (u : ℤ_[2]) = 0
    calc
      x * c + -(x * c * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * (u : ℤ_[2]) =
          x * c - x * c * (((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (u : ℤ_[2])) := by ring
      _ = 0 := by rw [huinv, mul_one, sub_self]
  · intro i hi3 hiV
    apply Multiplicative.toAdd.injective
    have H := congrFun (hbridge nu) i
    change toAdd (nu (Psi (dmGen alpha h i))) =
      frameTauV j k (frameEichlerV j x (nuFrame nu (dmGen alpha h))) i at H
    by_cases hiU : i = handleIdxU j
    · subst i
      rw [frameTauV_handleU_self, frameEichlerV_handleU] at H
      exact H
    · rw [frameTauV_of_ne j _ _ hiU hiV,
        frameEichlerV_of_ne j _ _ hiV hi3] at H
      exact H

#print axioms exists_clearD_of_unitHandle

/-- Clearing D can precede the hyperbolic unit-head normalization. The resulting
marking has D and selected V equal to zero, U-C equal to one, and unchanged C. -/
theorem exists_hyperbolicUnitHead_clearD_of_strictHandle
    {alpha h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (j : Fin h)
    (hU : toAdd (nu (dmGen alpha h (handleIdxU j))) = 1)
    (hV : nu (dmGen alpha h (handleIdxV j)) = 1)
    (qC : ℤ_[2]) (hC : toAdd (nu (dmC alpha h)) = 2 * qC) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      nu (Psi (dmD alpha h)) = 1 ∧
      nu (Psi (dmGen alpha h (handleIdxV j))) = 1 ∧
      nu (Psi (dmC alpha h)) = nu (dmC alpha h) ∧
      toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) =
        1 + toAdd (nu (dmC alpha h)) ∧
      toAdd (nu (Psi (dmGen alpha h (handleIdxU j)) *
        (Psi (dmC alpha h))⁻¹)) = 1 ∧
      (∀ i : Fin (coreRank h), i ≠ 3 → i ≠ handleIdxU j → i ≠ handleIdxV j →
        nu (Psi (dmGen alpha h i)) = nu (dmGen alpha h i)) := by
  obtain ⟨Psi₁, hchi₁, hD₁, hV₁, hfix₁⟩ :=
    exists_clearD_of_unitHandle nu j 1 hU hV
  let nu₁ : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
    nu.comp ⟨Psi₁.toMonoidHom, Psi₁.continuous_toFun⟩
  have hU₁ : toAdd (nu₁ (dmGen alpha h (handleIdxU j))) = 1 := by
    change toAdd (nu (Psi₁ (dmGen alpha h (handleIdxU j)))) = 1
    rw [hfix₁ _ (handleIdxU_ne_three j) (handleIdxU_ne_handleIdxV j j), hU]
  have hC₁ : nu₁ (dmC alpha h) = nu (dmC alpha h) := by
    exact hfix₁ 2 (Fin.ne_of_val_ne (by rw [coreVal_two, coreVal_three]; omega))
      (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxV_val]; omega))
  have hC₁add : toAdd (nu₁ (dmC alpha h)) = 2 * qC := by rw [hC₁, hC]
  obtain ⟨Psi₂, hchi₂, hU₂, hV₂, hfix₂, hhead₂⟩ :=
    EvenMHeadHandleHyperbolicNormalize.exists_hyperbolicUnitHead_of_strictHandle
      nu₁ j hU₁ hV₁ qC hC₁add
  refine ⟨Psi₂.trans Psi₁, ?_, ?_, hV₂, ?_, ?_, ?_, ?_⟩
  · intro x
    change chiM alpha h (Psi₁ (Psi₂ x)) = chiM alpha h x
    rw [hchi₁, hchi₂]
  · change nu₁ (Psi₂ (dmGen alpha h 3)) = 1
    rw [hfix₂ 3 (Ne.symm (handleIdxU_ne_three j))
      (Ne.symm (handleIdxV_ne_three j))]
    exact hD₁
  · change nu₁ (Psi₂ (dmGen alpha h 2)) = nu (dmC alpha h)
    rw [hfix₂ 2
      (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxU_val]; omega))
      (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxV_val]; omega))]
    exact hC₁
  · change toAdd (nu₁ (Psi₂ (dmGen alpha h (handleIdxU j)))) = _
    rw [hU₂, hC₁]
  · change toAdd (nu (Psi₁ (Psi₂ (dmGen alpha h (handleIdxU j))) *
      (Psi₁ (Psi₂ (dmC alpha h)))⁻¹)) = 1
    rw [← map_inv Psi₁, ← map_mul Psi₁]
    exact hhead₂
  · intro i hi3 hiU hiV
    change nu₁ (Psi₂ (dmGen alpha h i)) = nu (dmGen alpha h i)
    rw [hfix₂ i hiU hiV]
    exact hfix₁ i hi3 hiV

#print axioms exists_hyperbolicUnitHead_clearD_of_strictHandle

end
end GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicPreNormalize

