/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenHeisPure

/-!
# Heisenberg congruence through the acting quotient

The jet and central coordinates of a resolved word depend on its base elements only
through their actions on the coefficient group. This congruence packages that fact
without choosing a faithful acting quotient or changing the finite resolver.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH

variable {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- Equal first jets and central charge, with equal action of the base elements. -/
def HeisActionEq (p q : HeisLift A C) : Prop :=
  p.a = q.a ∧ p.l = q.l ∧ p.z = q.z ∧ ∀ a : A, p.g • a = q.g • a

namespace HeisActionEq

theorem refl (p : HeisLift A C) : HeisActionEq p p := ⟨rfl, rfl, rfl, fun _ ↦ rfl⟩

theorem symm {p q : HeisLift A C} (h : HeisActionEq p q) : HeisActionEq q p :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun a ↦ (h.2.2.2 a).symm⟩

theorem trans {p q r : HeisLift A C} (h : HeisActionEq p q) (k : HeisActionEq q r) :
    HeisActionEq p r :=
  ⟨h.1.trans k.1, h.2.1.trans k.2.1, h.2.2.1.trans k.2.2.1,
    fun a ↦ (h.2.2.2 a).trans (k.2.2.2 a)⟩

private theorem inv_action {g h : C} (H : ∀ a : A, g • a = h • a) :
    ∀ a : A, g⁻¹ • a = h⁻¹ • a := by
  intro a
  apply inv_smul_eq_iff.mpr
  rw [H, smul_inv_smul]

private theorem dual_action {g h : C} (H : ∀ a : A, g • a = h • a) :
    ∀ lam : ElemDual A, g • lam = h • lam := by
  intro lam
  ext a
  simp only [ElemDual.smul_apply, inv_action H]

theorem mul {p q r s : HeisLift A C} (h : HeisActionEq p q) (k : HeisActionEq r s) :
    HeisActionEq (p * r) (q * s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [HeisLift.mul_a, h.1, k.1, h.2.2.2]
  · simp only [HeisLift.mul_l, h.2.1, k.2.1, dual_action h.2.2.2]
  · simp only [HeisLift.mul_z, h.2.2.1, k.2.2.1, h.2.1, k.1, h.2.2.2]
  · intro a
    simp only [HeisLift.mul_g, mul_smul, k.2.2.2, h.2.2.2]

theorem inv {p q : HeisLift A C} (h : HeisActionEq p q) :
    HeisActionEq p⁻¹ q⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [HeisLift.inv_a, h.1, inv_action h.2.2.2]
  · simp only [HeisLift.inv_l, h.2.1, dual_action (inv_action h.2.2.2)]
  · simp only [HeisLift.inv_z, h.1, h.2.1, h.2.2.1]
  · exact inv_action h.2.2.2

theorem pow {p q : HeisLift A C} (h : HeisActionEq p q) (n : ℕ) :
    HeisActionEq (p ^ n) (q ^ n) := by
  induction n with
  | zero => simp only [pow_zero]; exact refl 1
  | succ n ih => simpa only [pow_succ] using ih.mul h

theorem zpow {p q : HeisLift A C} (h : HeisActionEq p q) (n : ℤ) :
    HeisActionEq (p ^ n) (q ^ n) := by
  cases n with
  | ofNat n =>
      change HeisActionEq (p ^ (n : ℤ)) (q ^ (n : ℤ))
      simpa only [zpow_natCast] using h.pow n
  | negSucc n => simpa only [zpow_negSucc] using (h.pow (n+1)).inv

theorem evalZ {X : Type*} (f g : X → HeisLift A C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (h : ∀ i, HeisActionEq (f i) (g i))
    (w : PWord X) : HeisActionEq (PWord.evalZ f E E₂ w) (PWord.evalZ g E E₂ w) := by
  induction w with
  | one => exact refl 1
  | gen i => exact h i
  | mul u v hu hv => exact hu.mul hv
  | inv u hu => exact hu.inv
  | conj u v hu hv => exact (hv.inv.mul hu).mul hv
  | comm u v hu hv => exact ((hu.inv.mul hv.inv).mul hu).mul hv
  | zpow u n hu => exact hu.zpow n
  | z2pow u z hu => exact hu.zpow (E₂ z)
  | profPow u z hu => exact hu.zpow (E z)

end HeisActionEq

#print axioms HeisActionEq
#print axioms HeisActionEq.refl
#print axioms HeisActionEq.symm
#print axioms HeisActionEq.trans
#print axioms HeisActionEq.mul
#print axioms HeisActionEq.inv
#print axioms HeisActionEq.pow
#print axioms HeisActionEq.zpow
#print axioms HeisActionEq.evalZ

end
end GQ2.Dyadic

