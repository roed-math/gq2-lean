/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenHeisPure
import GQ2.Dyadic.Certificates.M0

/-!
# The compact core against a pure dual head

For every valid compact-M exponent, dual offsets supported only at the head give a zero dual
jet and one central contribution: evaluation of the head dual on the third core coordinate.
The other factors vanish by the evenness of the compact exponent. The theorem permits
arbitrary primal offsets and arbitrary tame-inertia action; it does not assume a ramified
normal form. It supplies the core half of the promoted pure-U detection argument.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH
open Count Certificates Words

namespace Instances.EvenMHeadHandleHyperbolicPureHead

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
  [DistribMulAction C A]

private def dualPure (A C : Type*) [AddCommGroup A] [Group C] [DistribMulAction C A] :
    Subgroup (HeisLift A C) where
  carrier := {p | p.l = 0 ∧ p.z = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := fun {p q} hp hq =>
    ⟨by rw [HeisLift.mul_l, hp.1, hq.1, smul_zero, add_zero],
     by rw [HeisLift.mul_z, hp.2, hq.2, hp.1, ElemDual.zero_apply, add_zero, add_zero]⟩
  inv_mem' := fun {p} hp =>
    ⟨by rw [HeisLift.inv_l, hp.1, smul_zero, neg_zero],
     by rw [HeisLift.inv_z, hp.1, hp.2, ElemDual.zero_apply, add_zero]⟩

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

private theorem heisEvalZ_dualPure_of_dualZero
    (mu : Generator (2 + 2 * h) → C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    ∀ w, DualZero y w →
      heisEvalZ mu x y E E₂ w ∈ dualPure A C := by
  intro w hw
  induction w with
  | one => exact (dualPure A C).one_mem
  | gen g => rw [heisEvalZ_gen]; exact ⟨hw, rfl⟩
  | mul u v hu hv => rw [heisEvalZ_mul]; exact mul_mem (hu hw.1) (hv hw.2)
  | inv u hu => rw [heisEvalZ_inv]; exact inv_mem (hu hw)
  | conj u v hu hv =>
      rw [heisEvalZ_conj, conjR]
      exact mul_mem (mul_mem (inv_mem (hv hw.2)) (hu hw.1)) (hv hw.2)
  | comm u v hu hv =>
      rw [heisEvalZ_comm, commR]
      exact mul_mem (mul_mem (mul_mem (inv_mem (hu hw.1)) (inv_mem (hv hw.2)))
        (hu hw.1)) (hv hw.2)
  | zpow u k hu => rw [heisEvalZ_zpow]; exact zpow_mem (hu hw) k
  | z2pow u z hu =>
      change PWord.evalZ (heisGen mu x y) E E₂ (.z2pow u z) ∈ _
      rw [PWord.evalZ_z2pow]
      exact zpow_mem (hu hw) (E₂ z)
  | profPow u z hu => rw [heisEvalZ_profPow]; exact zpow_mem (hu hw) (E z)

private theorem dualPure_conj_jetZero (p r : HeisLift A C)
    (hp : p ∈ dualPure A C) (hr : r ∈ heisJetZero A C) :
    conjR p r ∈ dualPure A C := by
  obtain ⟨hpl, hpz⟩ := hp
  obtain ⟨hra, hrl⟩ := hr
  constructor
  · simp [conjR, HeisLift.mul_l, HeisLift.inv_l, hpl, hrl]
  · simp [conjR, HeisLift.mul_z, HeisLift.inv_z, HeisLift.mul_l,
      HeisLift.inv_l, hpl, hrl, hra, hpz,
      CharTwo.add_self_eq_zero]

theorem mFactors_dual_head
    {alpha : ℕ} (t : Marking (2 + 2 * h) C)
    (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0) (hα : 2 ≤ alpha)
    (hs : ∀ a : A, t.σ • a = a)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hyτ : y .tau = 0) (hycore : ∀ i : Fin 3, y (coreLetter h i) = 0) :
    let P := heisEvalZ ⇑t x y E E₂
      (PWord.prodList (Words.MCompact.mFactors alpha h))
    P.l = 0 ∧ P.z = y .sigma (x (coreLetter h 2)) := by
  have hS₂ : ∀ a : A, (Certificates.MCompact.sigma2Z t x y E E₂).g • a = a := by
    intro a
    rw [Certificates.MCompact.sigma2Z_g]
    exact mem_trivAct.mp (zpow_mem (mem_trivAct.mpr hs) _) a
  have h1 := Certificates.MCompact.heisF_leadingSquare t x y E E₂ hA₂ hwild hS₂ hα
  have h2 := Certificates.MCompact.heisF_leadingComm t x y E E₂ hA₂ hwild hS₂ hα
  have h3 := Certificates.MCompact.heisZ_sigma2Pow_two_mul t x y E E₂ hA₂ hS₂ hα
  have hM := (Certificates.MCompact.heisZ_sigma2Pow_jetZero t x y E E₂
    hA₂ hS₂ (Words.MCompact.even_mOf hα)).1
  have h2M := (Certificates.MCompact.heisZ_sigma2Pow_jetZero t x y E E₂
    hA₂ hS₂ (even_two_mul (Words.MCompact.mOf alpha))).1
  have hδ (i : Fin 3) : heisEvalZ ⇑t x y E E₂
      (Words.MCompact.deltaC h i) ∈ dualPure A C := by
    apply heisEvalZ_dualPure_of_dualZero
    simp [Words.MCompact.deltaC, DualZero, PWord.omega2Pow, hyτ, hycore]
  have hErev : heisEvalZ ⇑t x y E E₂ (Words.MCompact.eRevW alpha h) ∈
      dualPure A C := by
    rw [Words.MCompact.eRevW, heisEvalZ_prodList]
    apply Subgroup.list_prod_mem
    intro p hp
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rw [heisEvalZ_conj]
      apply dualPure_conj_jetZero _ _ (hδ 1)
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h2M
    · rw [heisEvalZ_conj]
      exact dualPure_conj_jetZero _ _ (hδ 1) hM
    · rw [heisEvalZ_conj]
      exact dualPure_conj_jetZero _ _ (hδ 0) hM
    · exact hδ 0
  have hδ2 : heisEvalZ ⇑t x y E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau])) ∈
      dualPure A C := by
    apply heisEvalZ_dualPure_of_dualZero
    simp [DualZero, PWord.omega2Pow, hyτ, hycore]
  simp only [PWord.prodList_cons, PWord.prodList_nil] at hδ2
  have hconj := heisConjR_of_trivial
    (heisGen ⇑t x y (coreLetter h 2)) (heisGen ⇑t x y .sigma)
    (Certificates.trivAct_coreLetter t hwild 2 |> mem_trivAct.mp)
  dsimp only [heisGen] at hconj
  have hJ : (heisEvalZ ⇑t x y E E₂ (Words.MCompact.j2W h)).l = 0 ∧
      (heisEvalZ ⇑t x y E E₂ (Words.MCompact.j2W h)).z =
        y .sigma (x (coreLetter h 2)) := by
    rw [Words.MCompact.j2W, PWord.prodList_cons, PWord.prodList_cons,
      PWord.prodList_nil, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one,
      heisEvalZ_inv, heisEvalZ_conj, heisEvalZ_gen, heisEvalZ_gen, hconj]
    constructor
    · simp [HeisLift.mul_l, HeisLift.inv_l, hycore, hδ2.1]
    · simp [HeisLift.mul_z, HeisLift.inv_z, HeisLift.inv_l,
        hycore, hδ2.2]
  dsimp only
  rw [Words.MCompact.mFactors]
  simp only [PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_one, mul_one]
  rw [h1, h2, h3]
  constructor
  · simp [HeisLift.mul_l, hJ.1, hErev.1]
  · simp [HeisLift.mul_z, hycore, hJ.1, hJ.2, hErev.2]

#print axioms mFactors_dual_head

end Instances.EvenMHeadHandleHyperbolicPureHead
end
end GQ2.Dyadic

