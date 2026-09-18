/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseOddCertificates
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite polynomial inverse of the actual odd-head polar operator

For an additive automorphism U on an exponent-two group with U^(2^k)=1,
J=1+U+U⁻¹ satisfies J^(2^k)=1. Its inverse is both J^(2^k-1) and the finite
sum of (U+U⁻¹)^i for i<2^k. Multiplication here is composition of additive
endomorphisms. Both products are checked, without a finiteness hypothesis on V.
The final equalities identify these operations with the existing certificate's
inverse and edge map; no replacement isometry or quadratic identity is assumed.
-/

namespace GQ2.Dyadic.Instances.WordPhaseOddPolynomialInverse
noncomputable section
open Instances.WordPhaseOddCertificates

variable {V : Type} [AddCommGroup V]

/-- The literal Wall map viewed in the composition ring of additive endomorphisms. -/
abbrev wallEnd (U : V ≃+ V) : AddMonoid.End V := wallPolarHom U

private abbrev actionEnd (U : V ≃+ V) : AddMonoid.End V := U.toAddMonoidHom

private theorem end_add_self (h2 : ∀ v : V, v+v=0) (f : AddMonoid.End V) : f+f=0 :=
  AddMonoidHom.ext fun v => h2 (f v)

private theorem end_add_pow_twoPower (h2 : ∀ v : V, v+v=0)
    (f g : AddMonoid.End V) (hfg : Commute f g) (k : ℕ) :
    (f+g)^(2^k)=f^(2^k)+g^(2^k) := by
  have htwo : (2 : AddMonoid.End V)=0 := by
    ext v
    change 2 • v=0
    rw [two_nsmul, h2]
  simpa only [Nat.cast_ofNat, htwo, zero_mul, add_zero] using
    hfg.add_pow_prime_pow_eq' Nat.prime_two k

private theorem action_inverse_commute (U : V ≃+ V) :
    Commute (actionEnd U) (actionEnd U.symm) := by
  apply AddMonoidHom.ext
  intro v
  exact (U.apply_symm_apply v).trans (U.symm_apply_apply v).symm

private theorem action_period (U : V ≃+ V) {m : ℕ} (hm : (⇑U)^[m]=id) :
    (actionEnd U)^m=(1 : AddMonoid.End V) := by
  ext v
  change (⇑U)^[m] v=v
  rw [hm]
  rfl

private theorem inverse_action_period (U : V ≃+ V) {m : ℕ} (hm : (⇑U)^[m]=id) :
    (actionEnd U.symm)^m=(1 : AddMonoid.End V) := by
  have hprod : actionEnd U * actionEnd U.symm=(1 : AddMonoid.End V) := by
    ext v
    exact U.apply_symm_apply v
  have H := (action_inverse_commute U).mul_pow m
  rw [hprod, one_pow, action_period U hm, one_mul] at H
  exact H.symm

/-- The nonconstant part K=U+U⁻¹ of the odd-head operator. -/
def nilpotentPart (U : V ≃+ V) : AddMonoid.End V :=
  actionEnd U+actionEnd U.symm

@[simp] theorem nilpotentPart_apply (U : V ≃+ V) (v : V) :
    nilpotentPart U v=U v+U.symm v := rfl

/-- The actual action period is a nilpotence bound for K, not a nilpotency-class test. -/
theorem nilpotentPart_pow_eq_zero (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (k : ℕ) (hU : (⇑U)^[2^k]=id) : (nilpotentPart U)^(2^k)=0 := by
  rw [nilpotentPart, end_add_pow_twoPower h2 _ _ (action_inverse_commute U),
    action_period U hU, inverse_action_period U hU]
  exact end_add_self h2 1

/-- Frobenius gives the literal J the same two-power period as U. -/
theorem wallPolarHom_pow_eq_one (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (k : ℕ) (hU : (⇑U)^[2^k]=id) : (wallEnd U)^(2^k)=(1 : AddMonoid.End V) := by
  have hJ : wallEnd U=(1 : AddMonoid.End V)+nilpotentPart U := by
    ext v
    exact add_assoc _ _ _
  rw [hJ]
  rw [end_add_pow_twoPower h2 _ _ (Commute.one_left _), one_pow,
    nilpotentPart_pow_eq_zero U h2 k hU, add_zero]

/-- Finite operator polynomial J^(2^k-1), with multiplication meaning composition. -/
def inversePowerPolynomial (U : V ≃+ V) (k : ℕ) : AddMonoid.End V :=
  (wallEnd U)^(2^k-1)

theorem wall_mul_inversePowerPolynomial (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (k : ℕ) (hU : (⇑U)^[2^k]=id) :
    wallEnd U * inversePowerPolynomial U k=(1 : AddMonoid.End V) := by
  rw [inversePowerPolynomial, ← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow]
  exact wallPolarHom_pow_eq_one U h2 k hU

theorem inversePowerPolynomial_mul_wall (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (k : ℕ) (hU : (⇑U)^[2^k]=id) :
    inversePowerPolynomial U k * wallEnd U=(1 : AddMonoid.End V) := by
  rw [inversePowerPolynomial, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
  exact wallPolarHom_pow_eq_one U h2 k hU

/-- A displayed finite sum in U and U⁻¹, without a chosen finite-bijection inverse. -/
def inverseSumPolynomial (U : V ≃+ V) (k : ℕ) : AddMonoid.End V :=
  ∑ i ∈ Finset.range (2^k), (nilpotentPart U)^i

/-- Vector-level spelling using only a finite sum and iterated additions/actions. -/
theorem inverseSumPolynomial_apply (U : V ≃+ V) (k : ℕ) (v : V) :
    inverseSumPolynomial U k v =
      ∑ i ∈ Finset.range (2^k), (fun w => U w+U.symm w)^[i] v := by
  let ev : AddMonoid.End V →+ V :=
    { toFun := fun f => f v, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change ev (∑ i ∈ Finset.range (2^k), (nilpotentPart U)^i)=_
  rw [map_sum]
  rfl

private theorem wall_eq_one_sub (U : V ≃+ V) (h2 : ∀ v : V, v+v=0) :
    wallEnd U=(1 : AddMonoid.End V)-nilpotentPart U := by
  have hn : -(nilpotentPart U)=nilpotentPart U :=
    neg_eq_of_add_eq_zero_left (end_add_self h2 (nilpotentPart U))
  rw [sub_eq_add_neg, hn]
  ext v
  exact add_assoc _ _ _

theorem wall_mul_inverseSumPolynomial (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (k : ℕ) (hU : (⇑U)^[2^k]=id) :
    wallEnd U * inverseSumPolynomial U k=(1 : AddMonoid.End V) := by
  rw [inverseSumPolynomial, wall_eq_one_sub U h2, mul_neg_geom_sum,
    nilpotentPart_pow_eq_zero U h2 k hU, sub_zero]

theorem inverseSumPolynomial_mul_wall (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (k : ℕ) (hU : (⇑U)^[2^k]=id) :
    inverseSumPolynomial U k * wallEnd U=(1 : AddMonoid.End V) := by
  rw [inverseSumPolynomial, wall_eq_one_sub U h2, geom_sum_mul_neg,
    nilpotentPart_pow_eq_zero U h2 k hU, sub_zero]

theorem inversePowerPolynomial_eq_sum (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (k : ℕ) (hU : (⇑U)^[2^k]=id) :
    inversePowerPolynomial U k=inverseSumPolynomial U k := by
  calc
    inversePowerPolynomial U k = inversePowerPolynomial U k *
        (wallEnd U * inverseSumPolynomial U k) := by
      rw [wall_mul_inverseSumPolynomial U h2 k hU, mul_one]
    _ = inverseSumPolynomial U k := by
      rw [← mul_assoc, inversePowerPolynomial_mul_wall U h2 k hU, one_mul]

/-- Explicit inverse-data equivalence, valid even without finite V. -/
def polynomialWallEquiv (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (k : ℕ) (hU : (⇑U)^[2^k]=id) : V ≃+ V where
  toFun := wallPolarHom U
  invFun := inverseSumPolynomial U k
  left_inv v := congrArg (fun f : AddMonoid.End V => f v)
    (inverseSumPolynomial_mul_wall U h2 k hU)
  right_inv v := congrArg (fun f : AddMonoid.End V => f v)
    (wall_mul_inverseSumPolynomial U h2 k hU)
  map_add' := (wallPolarHom U).map_add

/-- The existing certificate uses exactly this polynomial inverse. -/
theorem wallPolarEquiv_symm_eq_sum [Finite V] (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (hU2 : ∃ n, (⇑U)^[2^n]=id) (k : ℕ) (hU : (⇑U)^[2^k]=id) (v : V) :
    (wallPolarEquiv U h2 hU2).symm v=inverseSumPolynomial U k v := by
  apply (wallPolarEquiv U h2 hU2).injective
  rw [AddEquiv.apply_symm_apply]
  exact (congrArg (fun f : AddMonoid.End V => f v)
    (wall_mul_inverseSumPolynomial U h2 k hU)).symm

theorem wallPolarEquiv_symm_eq_power [Finite V] (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (hU2 : ∃ n, (⇑U)^[2^n]=id) (k : ℕ) (hU : (⇑U)^[2^k]=id) (v : V) :
    (wallPolarEquiv U h2 hU2).symm v=inversePowerPolynomial U k v := by
  rw [inversePowerPolynomial_eq_sum U h2 k hU]
  exact wallPolarEquiv_symm_eq_sum U h2 hU2 k hU v

/-- Direct application at the existing existential two-power hypothesis. -/
theorem wallPolarEquiv_symm_eq_chosen_sum [Finite V] (U : V ≃+ V)
    (h2 : ∀ v : V, v+v=0) (hU2 : ∃ n, (⇑U)^[2^n]=id) (v : V) :
    (wallPolarEquiv U h2 hU2).symm v=
      inverseSumPolynomial U (Classical.choose hU2) v :=
  wallPolarEquiv_symm_eq_sum U h2 hU2 _ (Classical.choose_spec hU2) v

/-- The original record's cross edge is the displayed polynomial in its head slot. -/
theorem oddCross_eq_polynomial [Finite V] (U : V ≃+ V) (h2 : ∀ v : V, v+v=0)
    (hU2 : ∃ n, (⇑U)^[2^n]=id) (k : ℕ) (hU : (⇑U)^[2^k]=id) (h : ℕ) (v : V) :
    oddCross h (wallPolarEquiv U h2 hU2) v=(inverseSumPolynomial U k v,0) := by
  change ((wallPolarEquiv U h2 hU2).symm v,0)=(inverseSumPolynomial U k v,0)
  rw [wallPolarEquiv_symm_eq_sum U h2 hU2 k hU v]

#print axioms nilpotentPart_pow_eq_zero
#print axioms wallPolarHom_pow_eq_one
#print axioms wall_mul_inversePowerPolynomial
#print axioms inversePowerPolynomial_mul_wall
#print axioms wall_mul_inverseSumPolynomial
#print axioms inverseSumPolynomial_mul_wall
#print axioms inversePowerPolynomial_eq_sum
#print axioms inverseSumPolynomial_apply
#print axioms polynomialWallEquiv
#print axioms wallPolarEquiv_symm_eq_sum
#print axioms wallPolarEquiv_symm_eq_power
#print axioms wallPolarEquiv_symm_eq_chosen_sum
#print axioms oddCross_eq_polynomial

end
end GQ2.Dyadic.Instances.WordPhaseOddPolynomialInverse
