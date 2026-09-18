/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaNormalFoxRows

/-!
# A finite polynomial for the unramified Fox pivot inverse

If the action of sigma has odd period `2*k+1`, the inverse of `1-sigma⁻¹`
on an exponent-two module without sigma-fixed vectors is the literal finite sum
`sigma⁻¹ + sigma⁻³ + ... + sigma⁻(2*k-1)`.  The proof uses the vanishing of the
full cyclic norm, not a bounded-rank or finite-case calculation.
-/

namespace GQ2.Dyadic.SigmaNormalFoxPolynomialInverse
noncomputable section
open GQ2 FoxH SigmaNormalFoxElimination

variable {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- The odd inverse-power polynomial, with `k` summands. -/
def oddInversePolynomial (sigma : C) (k : ℕ) : A →+ A where
  toFun a := ∑ j ∈ Finset.range k, (sigma⁻¹) ^ (2*j+1) • a
  map_zero' := by simp
  map_add' a b := by simp [smul_add, Finset.sum_add_distrib]

@[simp] theorem oddInversePolynomial_apply (sigma : C) (k : ℕ) (a : A) :
    oddInversePolynomial sigma k a =
      ∑ j ∈ Finset.range k, (sigma⁻¹) ^ (2*j+1) • a := rfl

private theorem sum_odd_even (f : ℕ → A) (k : ℕ) :
    ∑ i ∈ Finset.range (2*k+1), f i =
      f 0 + ∑ j ∈ Finset.range k, (f (2*j+1) + f (2*j+2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hn : 2*(k+1)+1 = (2*k+1)+1+1 := by omega
    rw [hn, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have hn' : 2*k+1+1 = 2*k+2 := by omega
    rw [hn']
    abel

/-- Pairing adjacent positive powers writes the full norm as `1+P+sigma⁻¹*P`. -/
theorem norm_eq_one_add_polynomial (sigma : C) (k : ℕ) (a : A) :
    ∑ i ∈ Finset.range (2*k+1), (sigma⁻¹)^i • a =
      a + oddInversePolynomial sigma k a +
        sigma⁻¹ • oddInversePolynomial sigma k a := by
  rw [sum_odd_even]
  simp only [pow_zero, one_smul, oddInversePolynomial_apply,
    Finset.sum_add_distrib, Finset.smul_sum]
  have hp : ∀ j : ℕ, (sigma⁻¹)^(2*j+2) • a =
      sigma⁻¹ • ((sigma⁻¹)^(2*j+1) • a) := by
    intro j
    rw [show 2*j+2 = (2*j+1)+1 by omega, pow_succ', mul_smul]
  simp only [hp]
  abel

/-- The polynomial is a right inverse of the unramified pivot.  Finiteness of the
module or the acting group is not required once an odd action period is given. -/
theorem sub_inv_smul_polynomial (sigma : C) (k : ℕ)
    (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, sigma • a=a → a=0)
    (hperiod : ∀ a : A, sigma^(2*k+1) • a=a) (a : A) :
    oddInversePolynomial sigma k a -
      sigma⁻¹ • oddInversePolynomial sigma k a = a := by
  have hfpf' : ∀ a : A, sigma⁻¹ • a=a → a=0 :=
    fun a ha => hfpf a (inv_smul_eq_iff.mp ha).symm
  have hperiod' : (sigma⁻¹)^(2*k+1) • a=a := by
    rw [inv_pow]
    exact inv_smul_eq_iff.mpr (hperiod a).symm
  have hnorm := WordLift.sum_pow_smul_eq_zero hfpf' hperiod'
  rw [norm_eq_one_add_polynomial] at hnorm
  have hneg (b : A) : -b=b := by
    exact neg_eq_of_add_eq_zero_left (hA₂ b)
  rw [sub_eq_add_neg, hneg]
  have hp := eq_neg_of_add_eq_zero_right (show a +
      (oddInversePolynomial sigma k a + sigma⁻¹ • oddInversePolynomial sigma k a)=0 by
    simpa only [add_assoc] using hnorm)
  simpa only [hneg] using hp

/-- The same finite polynomial is also a left inverse, without finiteness. -/
theorem polynomial_sub_inv_smul (sigma : C) (k : ℕ)
    (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, sigma • a=a → a=0)
    (hperiod : ∀ a : A, sigma^(2*k+1) • a=a) (a : A) :
    oddInversePolynomial sigma k (a-sigma⁻¹ • a)=a := by
  have hcomm : oddInversePolynomial sigma k (sigma⁻¹ • a) =
      sigma⁻¹ • oddInversePolynomial sigma k a := by
    simp only [oddInversePolynomial_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_smul, ← mul_smul, ← pow_succ, pow_succ']
  rw [map_sub, hcomm]
  exact sub_inv_smul_polynomial sigma k hA₂ hfpf hperiod a

/-- The pivot as an additive equivalence with the displayed polynomial as its
literal inverse.  Unlike finite bijectivity, this construction works on any
exponent-two module with the stated odd period and fixed-point-free action. -/
def polynomialPivotEquiv (sigma : C) (k : ℕ)
    (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, sigma • a=a → a=0)
    (hperiod : ∀ a : A, sigma^(2*k+1) • a=a) : A ≃+ A where
  toFun a := a-sigma⁻¹ • a
  invFun := oddInversePolynomial sigma k
  left_inv := polynomial_sub_inv_smul sigma k hA₂ hfpf hperiod
  right_inv := sub_inv_smul_polynomial sigma k hA₂ hfpf hperiod
  map_add' a b := by rw [smul_add]; abel

@[simp] theorem polynomialPivotEquiv_symm_apply (sigma : C) (k : ℕ)
    (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, sigma • a=a → a=0)
    (hperiod : ∀ a : A, sigma^(2*k+1) • a=a) (a : A) :
    (polynomialPivotEquiv sigma k hA₂ hfpf hperiod).symm a =
      ∑ j ∈ Finset.range k, (sigma⁻¹)^(2*j+1) • a := rfl

/-- The finite polynomial is exactly the inverse already used by the unramified
Fox elimination, so the existing row certificate needs no change. -/
theorem oneSubInvAction_symm_eq_polynomial [Finite A] (sigma : C) (k : ℕ)
    (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, sigma • a=a → a=0)
    (hperiod : ∀ a : A, sigma^(2*k+1) • a=a) (a : A) :
    (oneSubInvAction sigma hfpf).symm a = oddInversePolynomial sigma k a := by
  apply (oneSubInvAction sigma hfpf).injective
  rw [AddEquiv.apply_symm_apply, oneSubInvAction_apply,
    sub_inv_smul_polynomial sigma k hA₂ hfpf hperiod]

/-- The previous finite-bijectivity pivot and the polynomial pivot are the same
additive equivalence, including their inverse operations. -/
theorem oneSubInvAction_eq_polynomialPivotEquiv [Finite A] (sigma : C) (k : ℕ)
    (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, sigma • a=a → a=0)
    (hperiod : ∀ a : A, sigma^(2*k+1) • a=a) :
    oneSubInvAction sigma hfpf = polynomialPivotEquiv sigma k hA₂ hfpf hperiod := by
  ext a
  rfl

/-- The same inverse written in terms of an arbitrary odd period `m`. -/
theorem oneSubInvAction_symm_eq_polynomial_of_odd [Finite A] (sigma : C) (m : ℕ)
    (hm : Odd m) (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, sigma • a=a → a=0)
    (hperiod : ∀ a : A, sigma^m • a=a) (a : A) :
    (oneSubInvAction sigma hfpf).symm a = oddInversePolynomial sigma (m/2) a := by
  have hm' : m = 2*(m/2)+1 := by
    have := Nat.odd_iff.mp hm
    omega
  apply oneSubInvAction_symm_eq_polynomial sigma (m/2) hA₂ hfpf
  simpa only [← hm'] using hperiod

/-- Trivial two-primary projection forces odd order in a finite group. -/
theorem odd_orderOf_of_powOmega2_eq_one {G : Type*} [Group G] [Finite G]
    (g : G) (hg : powOmega2 g=1) : Odd (orderOf g) := by
  rcases Nat.even_or_odd (orderOf g) with heven | hodd
  · have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
    have hfac : (orderOf g).factorization 2 ≠ 0 :=
      (Nat.prime_two.factorization_pos_of_dvd hn heven.two_dvd).ne'
    have hoddω : Odd (omega2Exp (orderOf g)) :=
      Nat.odd_iff.mpr ((omega2Exp_modEq_one hn hfac).of_dvd (dvd_pow_self 2 hfac))
    have hord : orderOf g ∣ omega2Exp (orderOf g) :=
      orderOf_dvd_of_pow_eq_one hg
    exact False.elim ((Nat.not_even_iff_odd.mpr hoddω)
      (even_iff_two_dvd.mpr (heven.two_dvd.trans hord)))
  · exact hodd

/-- The canonical period of the actual finite sigma action is odd when its
two-primary part acts trivially.  Sigma itself need not have odd order in `C`. -/
theorem odd_actionOrder_of_powOmega2_trivial [Finite C] [Finite A] (sigma : C)
    (hsigma₂ : ∀ a : A, powOmega2 sigma • a=a) :
    Odd (orderOf (MulAction.toPermHom C A sigma)) := by
  apply odd_orderOf_of_powOmega2_eq_one
  rw [← powOmega2_map]
  ext a
  exact hsigma₂ a

/-- The action order, rather than the potentially larger order in the ambient
base group, is an action period. -/
theorem pow_actionOrder_smul [Finite A] (sigma : C) (a : A) :
    sigma ^ orderOf (MulAction.toPermHom C A sigma) • a=a := by
  have hp : MulAction.toPermHom C A
      (sigma ^ orderOf (MulAction.toPermHom C A sigma))=1 := by
    rw [map_pow, pow_orderOf_eq_one]
  exact congrArg (fun f : Equiv.Perm A => f a) hp

/-- Closed finite-sum formula for the inverse in the current unramified Fox
matrix, with no chosen period and no new action hypothesis. -/
theorem oneSubInvAction_symm_eq_actionPolynomial [Finite C] [Finite A] (sigma : C)
    (hA₂ : ∀ a : A, a+a=0)
    (hfpf : ∀ a : A, sigma • a=a → a=0)
    (hsigma₂ : ∀ a : A, powOmega2 sigma • a=a) (a : A) :
    (oneSubInvAction sigma hfpf).symm a =
      ∑ j ∈ Finset.range (orderOf (MulAction.toPermHom C A sigma)/2),
        (sigma⁻¹)^(2*j+1) • a := by
  exact oneSubInvAction_symm_eq_polynomial_of_odd sigma _
    (odd_actionOrder_of_powOmega2_trivial sigma hsigma₂) hA₂ hfpf
    (pow_actionOrder_smul sigma) a

#print axioms oddInversePolynomial
#print axioms norm_eq_one_add_polynomial
#print axioms sub_inv_smul_polynomial
#print axioms polynomial_sub_inv_smul
#print axioms polynomialPivotEquiv
#print axioms polynomialPivotEquiv_symm_apply
#print axioms oneSubInvAction_symm_eq_polynomial
#print axioms oneSubInvAction_eq_polynomialPivotEquiv
#print axioms oneSubInvAction_symm_eq_polynomial_of_odd
#print axioms odd_orderOf_of_powOmega2_eq_one
#print axioms odd_actionOrder_of_powOmega2_trivial
#print axioms pow_actionOrder_smul
#print axioms oneSubInvAction_symm_eq_actionPolynomial

end
end GQ2.Dyadic.SigmaNormalFoxPolynomialInverse
