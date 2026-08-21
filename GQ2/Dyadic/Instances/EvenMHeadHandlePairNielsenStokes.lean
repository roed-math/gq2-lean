/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.StokesNielsen
import GQ2.Dyadic.Instances.EvenMHeadHandlePairStokes

/-!
# Stokes invariance of the uniform wild normalization

The rank-generic wild shear remains an inverse free substitution under every integer resolver.
The general Nielsen invariance theorem therefore removes this normalization from the Stokes
problem uniformly in the rank, word, coefficient, and finite level.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize

noncomputable section

open GQ2 GQ2.Dyadic GQ2.FoxH
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize

theorem wildShear_resolved_backward_forward
    {n : ℕ} (k : Fin (n + 1) → ℤ_[2])
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (g : Generator n) :
    FreeGroup.lift
      (fun j ↦ heisToFree E E₂ ((wildShearNielsen k).forward j))
      (heisToFree E E₂ ((wildShearNielsen k).backward g)) =
        FreeGroup.of g := by
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      simp [wildShearNielsen, wildShearForward, wildShearBackward,
        heisToFree, mul_assoc]

theorem wildShear_resolved_forward_backward
    {n : ℕ} (k : Fin (n + 1) → ℤ_[2])
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (g : Generator n) :
    FreeGroup.lift
      (fun j ↦ heisToFree E E₂ ((wildShearNielsen k).backward j))
      (heisToFree E E₂ ((wildShearNielsen k).forward g)) =
        FreeGroup.of g := by
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      simp [wildShearNielsen, wildShearForward, wildShearBackward,
        heisToFree, mul_assoc]

theorem gammaFam_subst_wildShearBackward
    {n q : ℕ} (k : Fin (n + 1) → ℤ_[2])
    (R : PWord (Generator n)) (l : Fin 2) :
    gammaFam n q (PWord.subst (wildShearNielsen k).backward R) l =
      PWord.subst (wildShearNielsen k).backward (gammaFam n q R l) := by
  fin_cases l
  · simp [gammaFam, tameRelW, wildShearNielsen, wildShearBackward]
  · rfl

/-- The uniform wild normalization is Stokes-invariant at every finite resolver. -/
theorem stokesDuality_wildShearBackward_iff
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A]
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (c : Generator n → C) (R : PWord (Generator n))
    (k : Fin (n + 1) → ℤ_[2])
    (hend : IsStokesEndpoint (fun l : Fin 2 ↦
      heisToFree E E₂ (gammaFam n q R l))) :
    StokesDuality c (fun l : Fin 2 ↦ heisToFree E E₂
        (gammaFam n q (PWord.subst (wildShearNielsen k).backward R) l)) A ↔
      StokesDuality
        (freeSubstMark c (fun g ↦ heisToFree E E₂
          ((wildShearNielsen k).backward g)))
        (fun l : Fin 2 ↦ heisToFree E E₂ (gammaFam n q R l)) A := by
  have H := stokesDuality_heisToFree_subst_iff (A := A) E E₂ c
    (gammaFam n q R) (wildShearNielsen k).backward
      (wildShearNielsen k).forward
    (wildShear_resolved_backward_forward k E E₂)
    (wildShear_resolved_forward_backward k E E₂) hend
  simpa only [← gammaFam_subst_wildShearBackward] using H

#print axioms wildShear_resolved_backward_forward
#print axioms wildShear_resolved_forward_backward
#print axioms gammaFam_subst_wildShearBackward
#print axioms stokesDuality_wildShearBackward_iff

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize

