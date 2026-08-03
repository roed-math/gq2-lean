/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.LEvenQStokes

/-!
# The ramified Hessian of the generic `L_sq` word

This file isolates the second-order calculation which is not covered by the unramified
closed form in `Certificates.L`.  On the ramified normal representative only the `x₁` wild
coordinate survives.  The tame word therefore has zero central coordinate for every exponent
`q`, while the wild word is Roe's corrected relator and has Hessian operator
`1 + sigma2 + sigma2⁻¹`.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words.LSq Certificates.MProcyclic

/-! ## The tame term vanishes on wild-supported offsets -/

/-- If the primal and dual offsets vanish on `sigma` and `tau`, the tame relator is evaluated
entirely in the base slice of the Heisenberg extension.  In particular its central coordinate
vanishes, for every exponent `q` and every resolver. -/
theorem heisZ_tameRelW_eq_zero_of_tame_offsets_zero
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (x : Generator n → A) (y : Generator n → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hxσ : x .sigma = 0) (hxτ : x .tau = 0)
    (hyσ : y .sigma = 0) (hyτ : y .tau = 0) :
    (heisEvalZ ⇑t x y E E₂ (tameRelW n q)).z = 0 := by
  rw [tameRelW, heisEvalZ_mul, heisEvalZ_inv, heisEvalZ_conj,
    heisEvalZ_zpow, heisEvalZ_gen, heisEvalZ_gen]
  simp only [hxσ, hxτ, hyσ, hyτ]
  change
    (conjR (secHom (A := A) t.τ) (secHom (A := A) t.σ)
      * (secHom (A := A) t.τ ^ (q : ℤ))⁻¹).z = 0
  simp only [conjR, ← map_mul, ← map_inv, ← map_zpow]
  rfl

/-! ## The base ramified formula -/

set_option maxHeartbeats 1600000 in
/-- The generic `L_sq` Stokes middle map on the ramified `x₁`-supported normal
representatives.  The formula holds for every tame exponent `q`: all `q`-dependence lies in the
tame relator, whose central coordinate vanishes on these representatives. -/
theorem heisEta1_lSqFam_zero_ramified_x1Supported
    {q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : _root_.GQ2.Marking C) (hA₂ : ∀ a : A, a + a = 0)
    (hx0 : ∀ a : A, t.x₀ • a = a) (hx1 : ∀ a : A, t.x₁ • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (d : A) (lam : ElemDual A) :
    heisEta1 (⇑(Marking.ofQ2 t))
        (Certificates.LSqStokes.lSqFam 0 q
          (omega2Exp (4 * Monoid.exponent C)))
        (q2Offsets (x1Supported d))
        (q2Offsets (x1Supported (V := ElemDual A) lam))
      = lam (d + t.sigma2 • d + t.sigma2⁻¹ • d) := by
  have htame :
      (heisEvalZ (⇑(Marking.ofQ2 t))
        (q2Offsets (x1Supported d))
        (q2Offsets (x1Supported (V := ElemDual A) lam))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
        (tameRelW 1 q)).z = 0 := by
    apply heisZ_tameRelW_eq_zero_of_tame_offsets_zero
    all_goals rfl
  rw [heisEta1_apply, Fin.sum_univ_two,
    Certificates.LSqStokes.lSqFam_zero, Certificates.LSqStokes.lSqFam_one,
    ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift, htame, zero_add,
    heisEvalZ_lSqW_zero_eq_wildValueR hA₂,
    heisMarking_wildValueR_z_ramified t d lam hA₂ hx0 hx1 hτfpf hTodd]

/-! ## Handle stabilization without a ramification-class hypothesis -/

/-- The second-order handle decomposition is class-independent.  The earlier
`heisZ_lSq_handle_stable` was proved by comparing two unramified closed forms and therefore
carried a `tau`-triviality hypothesis.  At word level no such hypothesis is needed: the handle
tail has zero first jet, so multiplying it onto the core introduces no cross term. -/
theorem heisZ_lSq_handle_stable_of_wild_trivial
    {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (x : Generator (2 * h + 1) → A)
    (y : Generator (2 * h + 1) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a) :
    (heisEvalZ ⇑t x y E E₂ (lSqW h)).z
      = (heisEvalZ ⇑(LSq.coreMarking t) (LSq.coreRestrict h A x)
            (LSq.coreRestrict h (ElemDual A) y) E E₂ (lSqW 0)).z
        + ∑ j, (y (handleU j) (x (handleV j))
          + y (handleV j) (x (handleU j))) := by
  have hHmem := Certificates.LSqStokes.heisF_lSqHandles_mem t x y E E₂ hwild
  have hHz := Certificates.LSqStokes.heisF_lSqHandles_z t x y E E₂ hwild
  rw [lSqW, heisEvalZ_prodList, List.map_append, List.prod_append,
    Certificates.LSqStokes.heisEvalZ_lSqHandleTail]
  rw [heisMul_z_of_a_eq_zero _ _ hHmem.1, hHz]
  congr 1

set_option maxHeartbeats 1600000 in
/-- The full ramified Hessian formula in degree `2h+1`, on a representative whose core is
Roe's `x₁`-supported normal form.  The remaining `2h` coordinates contribute exactly the
standard hyperbolic planes.  This is independent of the even tame exponent (indeed of `q`
altogether). -/
theorem heisEta1_lSqFam_ramified_core_x1Supported
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (x : Generator (2 * h + 1) → A)
    (y : Generator (2 * h + 1) → ElemDual A)
    (d : A) (lam : ElemDual A)
    (hxcore : LSq.coreRestrict h A x = q2Offsets (x1Supported d))
    (hycore : LSq.coreRestrict h (ElemDual A) y =
      q2Offsets (x1Supported (V := ElemDual A) lam)) :
    heisEta1 ⇑t
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (4 * Monoid.exponent C))) x y
      = lam (d + (Marking.toQ2 (LSq.coreMarking t)).sigma2 • d
          + (Marking.toQ2 (LSq.coreMarking t)).sigma2⁻¹ • d)
        + ∑ j, (y (handleU j) (x (handleV j))
          + y (handleV j) (x (handleU j))) := by
  let e := omega2Exp (4 * Monoid.exponent C)
  have hxσ : x .sigma = 0 := by
    have hcoord := congrFun hxcore Generator.sigma
    simpa [Certificates.LSqStokes.coreRestrict_sigma, q2Offsets, x1Supported] using hcoord
  have hxτ : x .tau = 0 := by
    have hcoord := congrFun hxcore Generator.tau
    simpa [Certificates.LSqStokes.coreRestrict_tau, q2Offsets, x1Supported] using hcoord
  have hyσ : y .sigma = 0 := by
    have hcoord := congrFun hycore Generator.sigma
    simpa [Certificates.LSqStokes.coreRestrict_sigma, q2Offsets, x1Supported] using hcoord
  have hyτ : y .tau = 0 := by
    have hcoord := congrFun hycore Generator.tau
    simpa [Certificates.LSqStokes.coreRestrict_tau, q2Offsets, x1Supported] using hcoord
  have htame :
      (heisEvalZ ⇑t x y (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
        (tameRelW (2 * h + 1) q)).z = 0 :=
    heisZ_tameRelW_eq_zero_of_tame_offsets_zero t x y _ _ hxσ hxτ hyσ hyτ
  have hcoreWild :
      (heisEvalZ ⇑(LSq.coreMarking t) (LSq.coreRestrict h A x)
        (LSq.coreRestrict h (ElemDual A) y)
        (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) (lSqW 0)).z
        = lam (d + (Marking.toQ2 (LSq.coreMarking t)).sigma2 • d
          + (Marking.toQ2 (LSq.coreMarking t)).sigma2⁻¹ • d) := by
    rw [hxcore, hycore, ← Marking.ofQ2_toQ2 (LSq.coreMarking t)]
    rw [heisEvalZ_lSqW_zero_eq_wildValueR hA₂]
    apply heisMarking_wildValueR_z_ramified
      (Marking.toQ2 (LSq.coreMarking t)) d lam hA₂
    · exact fun a ↦ LSq.coreMarking_hwild t hwild 0 a
    · exact fun a ↦ LSq.coreMarking_hwild t hwild 1 a
    · exact hτfpf
    · exact hTodd
  rw [Certificates.LSqStokes.heisEta1_lSqFam_apply (t := t) (x := x) (y := y),
    htame, zero_add,
    heisZ_lSq_handle_stable_of_wild_trivial t x y _ _ hwild, hcoreWild]

/-- Left nondegeneracy of the ramified base pairing, now for every tame exponent `q`.  This is
the direct word-level consequence of the formula above and Roe's already-proved injectivity of
`1 + sigma2 + sigma2⁻¹`; it uses neither Tate duality nor continuous cohomology. -/
theorem lSqFam_zero_ramified_pairing_separates_left
    {q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : _root_.GQ2.Marking C) (hA₂ : ∀ a : A, a + a = 0)
    (hx0 : ∀ a : A, t.x₀ • a = a) (hx1 : ∀ a : A, t.x₁ • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    {d : A} (hd : d ≠ 0) :
    ∃ lam : ElemDual A,
      heisEta1 (⇑(Marking.ofQ2 t))
          (Certificates.LSqStokes.lSqFam 0 q
            (omega2Exp (4 * Monoid.exponent C)))
          (q2Offsets (x1Supported d))
          (q2Offsets (x1Supported (V := ElemDual A) lam)) ≠ 0 := by
  have hop := pairingR_operator_injective (V := A) t hA₂
  have hne : d + t.sigma2 • d + t.sigma2⁻¹ • d ≠ 0 := by
    intro hz
    apply hd
    apply hop
    simpa using hz
  obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hne
  refine ⟨lam, ?_⟩
  rw [heisEta1_lSqFam_zero_ramified_x1Supported t hA₂ hx0 hx1 hτfpf hTodd]
  exact hlam


end

end GQ2.Dyadic
