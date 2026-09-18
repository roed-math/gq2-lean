/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaNormalFoxPolynomialInverse
import GQ2.Dyadic.SigmaRamifiedFoxElimination

/-!
# A finite polynomial for the ramified Fox pivot inverse

The ramified pivot is `U = S⁻¹(T-1)`.  Since `T-1 = T(1-T⁻¹)`, its
inverse is `(1-T⁻¹)⁻¹ T⁻¹ S`.  The polynomial inverse of the unramified-type
factor therefore gives the literal sum `∑ j < m/2, T^(-(2*j+2)) S` when
`m` is an odd period of the tau action.  No commutation of sigma and tau is used.
-/

namespace GQ2.Dyadic.SigmaRamifiedFoxPolynomialInverse
noncomputable section
open GQ2 SigmaNormalFoxElimination SigmaNormalFoxPolynomialInverse
open SigmaRamifiedFoxElimination

variable {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- `T-1 = T(1-T⁻¹)` as an equality of the existing additive equivalences.
This factorization does not require exponent two. -/
theorem tauSubOne_eq_oneSubInvAction_trans [Finite A] (tau : C)
    (hfpf : ∀ a : A, tau • a=a → a=0) :
    tauSubOne tau hfpf = (oneSubInvAction tau hfpf).trans (actionEquiv tau) := by
  ext a
  simp only [tauSubOne_apply, AddEquiv.trans_apply, oneSubInvAction_apply]
  change tau • a-a = tau • (a-tau⁻¹ • a)
  rw [smul_sub, smul_inv_smul]

/-- The order of inverse composition is fixed explicitly before introducing the
finite polynomial. -/
theorem tauSubOne_symm_eq_oneSubInvAction [Finite A] (tau : C)
    (hfpf : ∀ a : A, tau • a=a → a=0) (a : A) :
    (tauSubOne tau hfpf).symm a = (oneSubInvAction tau hfpf).symm (tau⁻¹ • a) := by
  rw [tauSubOne_eq_oneSubInvAction_trans]
  rfl

/-- Explicit inverse of `T-1` for any supplied odd action period. -/
theorem tauSubOne_symm_eq_polynomial_of_odd [Finite A] (tau : C) (m : ℕ)
    (hm : Odd m) (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, tau • a=a → a=0)
    (hperiod : ∀ a : A, tau^m • a=a) (a : A) :
    (tauSubOne tau hfpf).symm a =
      ∑ j ∈ Finset.range (m/2), (tau⁻¹)^(2*j+2) • a := by
  rw [tauSubOne_symm_eq_oneSubInvAction,
    oneSubInvAction_symm_eq_polynomial_of_odd tau m hm hA₂ hfpf hperiod]
  simp only [oddInversePolynomial_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_smul, ← pow_succ]

/-- `U⁻¹ = ∑ j < m/2, T^(-(2*j+2)) S`.  Sigma is applied first;
there is no sigma/tau commutation hypothesis. -/
theorem sigmaPivot_symm_eq_polynomial_of_odd [Finite A] (sigma tau : C) (m : ℕ)
    (hm : Odd m) (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, tau • a=a → a=0)
    (hperiod : ∀ a : A, tau^m • a=a) (a : A) :
    (sigmaPivot sigma tau hfpf).symm a =
      ∑ j ∈ Finset.range (m/2), (tau⁻¹)^(2*j+2) • (sigma • a) := by
  rw [sigmaPivot_symm_apply]
  exact tauSubOne_symm_eq_polynomial_of_odd tau m hm hA₂ hfpf hperiod (sigma • a)

/-- Canonical action-order polynomial for the tau pivot, derived from the actual
two-primary-trivial action hypothesis rather than ambient odd order. -/
theorem tauSubOne_symm_eq_actionPolynomial [Finite C] [Finite A] (tau : C)
    (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, tau • a=a → a=0)
    (htau₂ : ∀ a : A, powOmega2 tau • a=a) (a : A) :
    (tauSubOne tau hfpf).symm a =
      ∑ j ∈ Finset.range (orderOf (MulAction.toPermHom C A tau)/2),
        (tau⁻¹)^(2*j+2) • a := by
  exact tauSubOne_symm_eq_polynomial_of_odd tau _
    (odd_actionOrder_of_powOmega2_trivial tau htau₂) hA₂ hfpf
    (pow_actionOrder_smul tau) a

/-- The displayed inverse of the existing ramified row pivot, with the canonical
odd tau-action order and no additional action hypotheses. -/
theorem sigmaPivot_symm_eq_actionPolynomial [Finite C] [Finite A] (sigma tau : C)
    (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, tau • a=a → a=0)
    (htau₂ : ∀ a : A, powOmega2 tau • a=a) (a : A) :
    (sigmaPivot sigma tau hfpf).symm a =
      ∑ j ∈ Finset.range (orderOf (MulAction.toPermHom C A tau)/2),
        (tau⁻¹)^(2*j+2) • (sigma • a) := by
  rw [sigmaPivot_symm_apply]
  exact tauSubOne_symm_eq_actionPolynomial tau hA₂ hfpf htau₂ (sigma • a)

#print axioms tauSubOne_eq_oneSubInvAction_trans
#print axioms tauSubOne_symm_eq_oneSubInvAction
#print axioms tauSubOne_symm_eq_polynomial_of_odd
#print axioms sigmaPivot_symm_eq_polynomial_of_odd
#print axioms tauSubOne_symm_eq_actionPolynomial
#print axioms sigmaPivot_symm_eq_actionPolynomial

end
end GQ2.Dyadic.SigmaRamifiedFoxPolynomialInverse
