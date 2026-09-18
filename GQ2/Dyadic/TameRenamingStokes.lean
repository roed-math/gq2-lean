/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameNormalStokes

/-!
# Restoring the canonical tame row after a tau-fixing renaming

For a trivial action, a generator renaming fixing tau changes neither the
canonical tame Fox row nor the tame pairing on tau-normal cycles. Thus a
full-family Stokes theorem can be converted into the theorem with only its
wild word renamed and its tame word restored. The renaming need not be
invertible for this comparison; invertibility belongs to the input theorem.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH Count Certificates

/-- Heisenberg evaluation commutes with an arbitrary alphabet renaming. -/
theorem heisEvalZ_subst_gen
    {n : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (f : Generator n → Generator n)
    (R : PWord (Generator n)) :
    heisEvalZ ⇑t x y E E₂ (PWord.subst (fun g ↦ .gen (f g)) R) =
      heisEvalZ (fun g ↦ t (f g)) (fun g ↦ x (f g)) (fun g ↦ y (f g)) E E₂ R := by
  change PWord.evalZ _ E E₂ (PWord.subst _ R) = PWord.evalZ _ E E₂ R
  rw [PWord.evalZ_subst]
  rfl

/-- Restoring the canonical tame word preserves both Fox rows for a trivial action. -/
theorem heisD1_gammaFam_subst_gen_of_trivial_action
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator n) (a : A), t g • a=a) (hq : Even q)
    (f : Generator n → Generator n) (hf : f .tau=.tau) (R : PWord (Generator n)) :
    heisD1 (A := A) ⇑t (fun k ↦ heisToFree E E₂
      (PWord.subst (fun g ↦ .gen (f g)) (gammaFam n q R k))) =
    heisD1 ⇑t (fun k ↦ heisToFree E E₂
      (gammaFam n q (PWord.subst (fun g ↦ .gen (f g)) R) k)) := by
  apply AddMonoidHom.ext
  intro x
  funext k
  fin_cases k
  · change (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree E E₂ (PWord.subst (fun g ↦ .gen (f g)) (tameRelW n q)))).a =
      (FreeGroup.lift (heisGen (⇑t) x 0) (heisToFree E E₂ (tameRelW n q))).a
    rw [← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift, heisEvalZ_subst_gen]
    let s : Marking n C := ⟨fun g ↦ t (f g)⟩
    change (heisEvalZ ⇑s (fun g ↦ x (f g)) 0 E E₂ (tameRelW n q)).a = _
    rw [heisA_tameRelW_unram s _ _ _ _ hA₂ (htriv (f .tau)) hq,
      heisA_tameRelW_unram t _ _ _ _ hA₂ (htriv .tau) hq]
    change (t (f .sigma))⁻¹ • x (f .tau) = t.σ⁻¹ • x .tau
    rw [hf, inv_smul_eq_iff.mpr (htriv (f .sigma) (x .tau)).symm]
    exact (inv_smul_eq_iff.mpr (htriv .sigma (x .tau)).symm).symm
  · rfl

/-- A full renamed-family scalar Stokes theorem implies its canonical-tame version. -/
theorem stokesDuality_gammaFam_subst_gen_of_trivial_action
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator n) (a : A), t g • a=a) (hq : Even q)
    (f : Generator n → Generator n) (hf : f .tau=.tau) (R : PWord (Generator n))
    (H : StokesDuality ⇑t (fun k ↦ heisToFree E E₂
      (PWord.subst (fun g ↦ .gen (f g)) (gammaFam n q R k))) A) :
    StokesDuality ⇑t (fun k ↦ heisToFree E E₂
      (gammaFam n q (PWord.subst (fun g ↦ .gen (f g)) R) k)) A := by
  have htrivD : ∀ (g : Generator n) (y : ElemDual A), t g • y=y :=
    fun g ↦ HeisLift.smul_elemdual_trivial _ (htriv g)
  have hdA := heisD1_gammaFam_subst_gen_of_trivial_action t E E₂ hA₂ htriv hq f hf R
  have hdD := heisD1_gammaFam_subst_gen_of_trivial_action t E E₂
    ElemDual.add_self_eq_zero htrivD hq f hf R
  apply stokesDuality_of_same_kernels_ranges_pairing ⇑t _ _
    (fun x ↦ by rw [hdA]) (fun y ↦ by rw [hdD]) (by rw [hdA]) (by rw [hdD])
  · intro x y hx hy
    rw [hdA] at hx
    rw [hdD] at hy
    have hxτ := tau_eq_zero_of_gammaFam_cocycle_unram t E E₂ hA₂ (htriv .tau) hq _ x hx
    have hyτ := tau_eq_zero_of_gammaFam_cocycle_unram t E E₂ ElemDual.add_self_eq_zero
      (htrivD .tau) hq _ y hy
    simp only [heisEta1_apply, Fin.sum_univ_two, gammaFam_zero, gammaFam_one,
      ← heisEvalZ_eq_lift]
    congr 1
    rw [heisEvalZ_subst_gen]
    let s : Marking n C := ⟨fun g ↦ t (f g)⟩
    change (heisEvalZ ⇑s (fun g ↦ x (f g)) (fun g ↦ y (f g)) E E₂ (tameRelW n q)).z = _
    rw [heisZ_tameRelW_unram s _ _ _ _ hA₂ (htriv (f .tau)) hq,
      heisZ_tameRelW_unram t _ _ _ _ hA₂ (htriv .tau) hq]
    simp [hf, hxτ, hyτ]
  · exact H

#print axioms heisEvalZ_subst_gen
#print axioms heisD1_gammaFam_subst_gen_of_trivial_action
#print axioms stokesDuality_gammaFam_subst_gen_of_trivial_action

end
end GQ2.Dyadic

