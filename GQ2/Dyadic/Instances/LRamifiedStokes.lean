/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.LRamifiedHessian
import GQ2.Dyadic.Instances.LHandleCoordinates

/-!
# Ramified Stokes duality for the generic `L_sq` word

This file assembles the first-order companion to `LRamifiedHessian`.  The tame row is kept at
an arbitrary exponent `q`; after the `tau` coordinate is killed, its pivot is independent of
`q`.  The wild row factors through the degree-one core and kills the first core-wild coordinate.
Together these give the ramified normal form used by the middle-degree Stokes pairing.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words.LSq Certificates.MProcyclic

/-! ## The uniform resolver at first order -/

/-- The coefficient-independent Heisenberg level also resolves the primal split lift. -/
theorem resolverLifts_uniformWordLift_ramified
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A]
    [DistribMulAction C A] (hA₂ : ∀ a : A, a + a = 0) :
    ResolverLifts
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (WordLift A C) := by
  intro p
  rw [zpow_natCast]
  apply powOmega2_pow_eq p
  · exact (WordLift.orderOf_dvd_two_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g) p).trans ⟨2, by ring⟩
  · exact (fourMulExponent_ne_zero_and_even C).1

/-! ## The two ramified Fox rows -/

set_option maxHeartbeats 800000 in
/-- The complete first differential of the uniform `L_sq` word on a ramified elementary
module.  The first component is the arbitrary-`q` tame row and the second component is the
handle-stable ramified wild row. -/
theorem heisD1_lSqFam_ramified_apply
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (x : Generator (2 * h + 1) → A) :
    heisD1 ⇑t
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (4 * Monoid.exponent C))) x
      = ![
          t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          t.σ⁻¹ • x (coreLetter h 0)] := by
  funext k
  fin_cases k
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (tameRelW (2 * h + 1) q))).a =
        t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau
    rw [← heisEvalZ_eq_lift,
      heisEvalZ_a_eq_foxD (resolverLifts_uniformWordLift_ramified hA₂),
      Certificates.foxD_tameRelW_of_tameRel t _ _ ht]
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (lSqW h))).a = t.σ⁻¹ • x (coreLetter h 0)
    rw [← heisEvalZ_eq_lift,
      heisEvalZ_a_eq_foxD (resolverLifts_uniformWordLift_ramified hA₂),
      Certificates.LSq.foxD_lSq_ram t _ _ hA₂ hwild hτfpf hTodd]

/-- The ramified first differential is onto: the tame row pivots on `sigma`, and the wild row
pivots independently on the first core-wild coordinate. -/
theorem heisD1_lSqFam_surjective_ramified
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a) :
    Function.Surjective
      (heisD1 (A := A) ⇑t
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (4 * Monoid.exponent C)))) := by
  intro r
  obtain ⟨v, hv⟩ := tameSigmaColumn_surjective_of_fixedPointFree t hτfpf (r 0)
  let x : Generator (2 * h + 1) → A := fun g ↦
    if g = .sigma then v
    else if g = coreLetter h 0 then t.σ • r 1
    else 0
  refine ⟨x, ?_⟩
  rw [heisD1_lSqFam_ramified_apply t hA₂ ht hwild hτfpf hTodd]
  funext k
  fin_cases k
  · change t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
        - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau = r 0
    have hσcore : (.sigma : Generator (2 * h + 1)) ≠ coreLetter h 0 :=
      Certificates.LSq.sigma_ne_coreLetter_zero h
    have hτσ : (.tau : Generator (2 * h + 1)) ≠ .sigma := by simp
    have hτcore : (.tau : Generator (2 * h + 1)) ≠ coreLetter h 0 :=
      Certificates.LSq.tau_ne_coreLetter_zero h
    simp only [x, if_pos, if_neg hτσ, if_neg hτcore,
      zero_add, smul_zero, Finset.sum_const_zero, sub_zero]
    exact hv
  · change t.σ⁻¹ • x (coreLetter h 0) = r 1
    have hcoreσ : coreLetter h 0 ≠ (.sigma : Generator (2 * h + 1)) :=
      (Certificates.LSq.sigma_ne_coreLetter_zero h).symm
    simp [x, hcoreσ]

end

end GQ2.Dyadic
