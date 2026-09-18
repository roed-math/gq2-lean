/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenHeisPure
import GQ2.Dyadic.Instances.TameInertiaPrimeToTwoCorrection

/-!
# Tame correction on normalized cochains

Appending any power of a letter with zero primal and dual offsets leaves both first jets and
the Heisenberg central coordinate unchanged. The base value may change. In particular this
applies to either tame-inertia correction on tau-normalized cochains, with no assumption that
the uncorrected relator dies. These are normal-pairing comparisons, not a theorem asserting
unconditional Stokes invariance under tame correction.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic.Count

variable {C A X : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- Right multiplication by a pure-base lift changes only the base coordinate. -/
theorem heisMul_pure (p : HeisLift A C) (g : C) :
    p * heisPure g = ⟨p.a, p.l, p.z, p.g * g⟩ := by
  apply HeisLift.ext <;>
    simp [HeisLift.mul_a, HeisLift.mul_l, HeisLift.mul_z, HeisLift.mul_g]

/-- A fourth power has no offsets when its base acts trivially and coefficients are
elementary. No finiteness assumption or order bound is needed. -/
theorem heisPow_four_of_trivial
    (hA₂ : ∀ a : A, a + a = 0) (p : HeisLift A C)
    (hp : ∀ a : A, p.g • a = a) :
    p ^ (4 : ℕ) = heisPure (p.g ^ (4 : ℕ)) := by
  rw [heisPow_of_trivial p hp]
  apply HeisLift.ext
  · change 4 • p.a = 0
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, two_nsmul, hA₂]
  · change 4 • p.l = 0
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, two_nsmul]
    exact (2 • p.l).add_self_eq_zero
  · change 4 • p.z + (4 : ℕ).choose 2 • p.l p.a = 0
    rw [show Nat.choose 4 2 = 6 by decide,
      nsmul_zmod2_even (show Even 4 by decide),
      nsmul_zmod2_even (show Even 6 by decide), add_zero]
  · rfl

/-- Every integer exponent divisible by four is second-order invisible at a trivial base. -/
theorem heisZpow_of_four_dvd
    (hA₂ : ∀ a : A, a + a = 0) (p : HeisLift A C)
    (hp : ∀ a : A, p.g • a = a) {k : ℤ} (hk : 4 ∣ k) :
    p ^ k = heisPure (p.g ^ k) := by
  obtain ⟨m, rfl⟩ := hk
  rw [zpow_mul, show p ^ (4 : ℤ) = p ^ (4 : ℕ) from rfl,
    heisPow_four_of_trivial hA₂ p hp, ← map_zpow,
    show p.g ^ (4 : ℕ) = p.g ^ (4 : ℤ) from (zpow_natCast p.g 4).symm,
    ← zpow_mul]

/-- A resolved appended inverse power is invisible on cochains normalized at its letter. -/
theorem heisEvalZ_mul_inv_profPow_gen_of_offsets_zero
    (c : X → C) (x : X → A) (y : X → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (R : PWord X) (i : X) (z : Zhat)
    (hx : x i = 0) (hy : y i = 0) :
    heisEvalZ c x y E E₂ (.mul R (.inv (.profPow (.gen i) z))) =
      heisEvalZ c x y E E₂ R * heisPure ((c i ^ E z)⁻¹) := by
  rw [heisEvalZ_mul, heisEvalZ_inv, heisEvalZ_profPow,
    heisEvalZ_gen_of_offsets_zero c x y E E₂ i hx hy, ← map_zpow, ← map_inv]

/-- The three offset coordinates are unchanged even when the correction changes the base. -/
theorem heisEvalZ_tameCorrection_coordinates
    {n : ℕ} (c : Generator n → C) (x : Generator n → A)
    (y : Generator n → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R : PWord (Generator n)) (z : Zhat) (hx : x .tau = 0) (hy : y .tau = 0) :
    let p := heisEvalZ c x y E E₂ R
    let p' := heisEvalZ c x y E E₂ (.mul R (.inv (.profPow (.gen .tau) z)))
    p'.a = p.a ∧ p'.l = p.l ∧ p'.z = p.z := by
  dsimp only
  rw [heisEvalZ_mul_inv_profPow_gen_of_offsets_zero c x y E E₂ R .tau z hx hy,
    heisMul_pure]
  exact ⟨rfl, rfl, rfl⟩

/-- Tame correction preserves the entire first differential on tau-normalized cochains. -/
theorem heisD1_gammaFam_tameCorrection
    {n q : ℕ} (c : Generator n → C) (x : Generator n → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (R : PWord (Generator n))
    (z : Zhat) (hx : x .tau = 0) :
    heisD1 c (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam n q (.mul R (.inv (.profPow (.gen .tau) z))) l)) x =
    heisD1 c (fun l : Fin 2 ↦ heisToFree E E₂ (gammaFam n q R l)) x := by
  funext l
  fin_cases l
  · rfl
  · simp only [heisD1_apply, ← heisEvalZ_eq_lift]
    exact (heisEvalZ_tameCorrection_coordinates c x 0 E E₂ R z hx rfl).1

/-- Tame correction preserves the traced normal pairing for arbitrary resolved exponents. -/
theorem heisEta1_gammaFam_tameCorrection
    {n q : ℕ} (c : Generator n → C) (x : Generator n → A)
    (y : Generator n → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R : PWord (Generator n)) (z : Zhat) (hx : x .tau = 0) (hy : y .tau = 0) :
    heisEta1 c (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam n q (.mul R (.inv (.profPow (.gen .tau) z))) l)) x y =
    heisEta1 c (fun l : Fin 2 ↦ heisToFree E E₂ (gammaFam n q R l)) x y := by
  simp only [heisEta1_apply, Fin.sum_univ_two, gammaFam_zero, gammaFam_one,
    ← heisEvalZ_eq_lift]
  rw [(heisEvalZ_tameCorrection_coordinates c x y E E₂ R z hx hy).2.2]

theorem heisEta1_tamePrimeToTwoCorrectedWord
    {n q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (c : Generator n → C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q)
    (hx : x .tau = 0) (hy : y .tau = 0) :
    heisEta1 c (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam n q (tamePrimeToTwoCorrectedWord hq0 hqe R hR) l)) x y =
    heisEta1 c (fun l : Fin 2 ↦ heisToFree E E₂ (gammaFam n q R l)) x y :=
  heisEta1_gammaFam_tameCorrection c x y E E₂ R
    (tamePrimeToTwoCorrectionExponent hq0 hqe R hR) hx hy

/-- If tau acts trivially, a correction exponent divisible by four preserves all three
offset coordinates on every cochain, not just normalized cochains. -/
theorem heisEvalZ_tameCorrection_coordinates_of_trivial_tau
    {n : ℕ} (c : Generator n → C) (x : Generator n → A)
    (y : Generator n → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R : PWord (Generator n)) (z : Zhat)
    (hA₂ : ∀ a : A, a + a = 0) (htau : ∀ a : A, c .tau • a = a)
    (hz : 4 ∣ E z) :
    let p := heisEvalZ c x y E E₂ R
    let p' := heisEvalZ c x y E E₂ (.mul R (.inv (.profPow (.gen .tau) z)))
    p'.a = p.a ∧ p'.l = p.l ∧ p'.z = p.z := by
  dsimp only
  rw [heisEvalZ_mul, heisEvalZ_inv, heisEvalZ_profPow,
    heisZpow_of_four_dvd hA₂ _ htau hz, ← map_inv, heisMul_pure]
  exact ⟨rfl, rfl, rfl⟩

/-- The first differential is unchanged by a four-divisible correction at trivial tau. -/
theorem heisD1_gammaFam_tameCorrection_of_trivial_tau
    {n q : ℕ} (c : Generator n → C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (R : PWord (Generator n)) (z : Zhat)
    (hA₂ : ∀ a : A, a + a = 0) (htau : ∀ a : A, c .tau • a = a)
    (hz : 4 ∣ E z) :
    heisD1 (A := A) c (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam n q (.mul R (.inv (.profPow (.gen .tau) z))) l)) =
    heisD1 (A := A) c (fun l : Fin 2 ↦ heisToFree E E₂ (gammaFam n q R l)) := by
  apply AddMonoidHom.ext
  intro x
  funext l
  fin_cases l
  · rfl
  · simp only [heisD1_apply, ← heisEvalZ_eq_lift]
    exact (heisEvalZ_tameCorrection_coordinates_of_trivial_tau
      c x 0 E E₂ R z hA₂ htau hz).1

/-- The full traced pairing is unchanged by a four-divisible correction at trivial tau. -/
theorem heisEta1_gammaFam_tameCorrection_of_trivial_tau
    {n q : ℕ} (c : Generator n → C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (R : PWord (Generator n)) (z : Zhat)
    (hA₂ : ∀ a : A, a + a = 0) (htau : ∀ a : A, c .tau • a = a)
    (hz : 4 ∣ E z) :
    heisEta1 (A := A) c (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam n q (.mul R (.inv (.profPow (.gen .tau) z))) l)) =
    heisEta1 (A := A) c (fun l : Fin 2 ↦ heisToFree E E₂ (gammaFam n q R l)) := by
  apply AddMonoidHom.ext
  intro x
  apply ElemDual.ext
  intro y
  simp only [heisEta1_apply, Fin.sum_univ_two, gammaFam_zero, gammaFam_one,
    ← heisEvalZ_eq_lift]
  rw [(heisEvalZ_tameCorrection_coordinates_of_trivial_tau
    c x y E E₂ R z hA₂ htau hz).2.2]

/-- On an unramified coefficient module, a four-divisible tame correction preserves the
entire Stokes ladder. Neither word is required to have trivial base value for this comparison. -/
theorem stokesDuality_gammaFam_tameCorrection_iff_of_trivial_tau
    {n q : ℕ} (c : Generator n → C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (R : PWord (Generator n)) (z : Zhat)
    (hA₂ : ∀ a : A, a + a = 0) (htau : ∀ a : A, c .tau • a = a)
    (hz : 4 ∣ E z) :
    StokesDuality c (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam n q (.mul R (.inv (.profPow (.gen .tau) z))) l)) A ↔
    StokesDuality c (fun l : Fin 2 ↦ heisToFree E E₂ (gammaFam n q R l)) A := by
  unfold StokesDuality
  rw [heisD1_gammaFam_tameCorrection_of_trivial_tau c E E₂ R z hA₂ htau hz,
    heisD1_gammaFam_tameCorrection_of_trivial_tau c E E₂ R z
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero)
      (smul_elemDual_of_trivial htau) hz,
    heisEta1_gammaFam_tameCorrection_of_trivial_tau c E E₂ R z hA₂ htau hz]

#print axioms heisEvalZ_tameCorrection_coordinates
#print axioms heisD1_gammaFam_tameCorrection
#print axioms heisEta1_gammaFam_tameCorrection
#print axioms heisEta1_tamePrimeToTwoCorrectedWord
#print axioms heisZpow_of_four_dvd
#print axioms stokesDuality_gammaFam_tameCorrection_iff_of_trivial_tau

end
end GQ2.Dyadic
