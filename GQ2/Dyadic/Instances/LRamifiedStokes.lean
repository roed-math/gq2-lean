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

/-! ## Ramified normal coordinates -/

/-- A ramified normal cochain: the core is supported on `x₁`, while the handle coordinates
are arbitrary. -/
def lSqRamifiedNormal (h : ℕ) {A : Type*} [AddCommGroup A]
    (d : A) (z : Fin h × Fin 2 → A) : Generator (2 * h + 1) → A :=
  (lSqCoreHandleAddEquiv h A).symm (q2Offsets (x1Supported d), z)

@[simp] theorem lSqRamifiedNormal_core
    (h : ℕ) {A : Type*} [AddCommGroup A]
    (d : A) (z : Fin h × Fin 2 → A) :
    LSq.coreRestrict h A (lSqRamifiedNormal h d z) = q2Offsets (x1Supported d) := by
  rw [← lSqCoreHandleAddEquiv_fst]
  simp [lSqRamifiedNormal]

@[simp] theorem lSqRamifiedNormal_handleU
    {h : ℕ} {A : Type*} [AddCommGroup A]
    (d : A) (z : Fin h × Fin 2 → A) (j : Fin h) :
    lSqRamifiedNormal h d z (handleU j) = z (j, 0) := by
  have hh := congrArg (fun p : (Generator 1 → A) × (Fin h × Fin 2 → A) ↦ p.2 (j, 0))
    ((lSqCoreHandleAddEquiv h A).apply_symm_apply (q2Offsets (x1Supported d), z))
  change ((lSqCoreHandleAddEquiv h A) (lSqRamifiedNormal h d z)).2 (j, 0) = z (j, 0) at hh
  rw [lSqCoreHandleAddEquiv_snd_zero] at hh
  exact hh

@[simp] theorem lSqRamifiedNormal_handleV
    {h : ℕ} {A : Type*} [AddCommGroup A]
    (d : A) (z : Fin h × Fin 2 → A) (j : Fin h) :
    lSqRamifiedNormal h d z (handleV j) = z (j, 1) := by
  have hh := congrArg (fun p : (Generator 1 → A) × (Fin h × Fin 2 → A) ↦ p.2 (j, 1))
    ((lSqCoreHandleAddEquiv h A).apply_symm_apply (q2Offsets (x1Supported d), z))
  change ((lSqCoreHandleAddEquiv h A) (lSqRamifiedNormal h d z)).2 (j, 1) = z (j, 1) at hh
  rw [lSqCoreHandleAddEquiv_snd_one] at hh
  exact hh

@[simp] theorem lSqRamifiedNormal_sigma
    (h : ℕ) {A : Type*} [AddCommGroup A]
    (d : A) (z : Fin h × Fin 2 → A) :
    lSqRamifiedNormal h d z .sigma = 0 := by
  have hcoord := congrFun (lSqRamifiedNormal_core h d z) Generator.sigma
  simpa [Certificates.LSqStokes.coreRestrict_sigma, q2Offsets, x1Supported] using hcoord

@[simp] theorem lSqRamifiedNormal_tau
    (h : ℕ) {A : Type*} [AddCommGroup A]
    (d : A) (z : Fin h × Fin 2 → A) :
    lSqRamifiedNormal h d z .tau = 0 := by
  have hcoord := congrFun (lSqRamifiedNormal_core h d z) Generator.tau
  simpa [Certificates.LSqStokes.coreRestrict_tau, q2Offsets, x1Supported] using hcoord

@[simp] theorem lSqRamifiedNormal_core_zero
    (h : ℕ) {A : Type*} [AddCommGroup A]
    (d : A) (z : Fin h × Fin 2 → A) :
    lSqRamifiedNormal h d z (coreLetter h 0) = 0 := by
  have hcoord := congrFun (lSqRamifiedNormal_core h d z) (coreLetter 0 0)
  change lSqRamifiedNormal h d z (coreLetter h 0) =
    q2Offsets (x1Supported d) (coreLetter 0 0) at hcoord
  simpa [q2Offsets, x1Supported, coreLetter, Marking.apply_wild] using hcoord

@[simp] theorem lSqRamifiedNormal_core_one
    (h : ℕ) {A : Type*} [AddCommGroup A]
    (d : A) (z : Fin h × Fin 2 → A) :
    lSqRamifiedNormal h d z (coreLetter h 1) = d := by
  have hcoord := congrFun (lSqRamifiedNormal_core h d z) (coreLetter 0 1)
  change lSqRamifiedNormal h d z (coreLetter h 1) =
    q2Offsets (x1Supported d) (coreLetter 0 1) at hcoord
  simpa [q2Offsets, x1Supported, coreLetter, Marking.apply_wild] using hcoord

/-- `TameRelAt q` is exactly death of the resolved tame relator, independently of the chosen
resolver. -/
theorem evalZ_tameRelW_eq_one_of_tameRelAt
    {n q : ℕ} {C : Type*} [Group C]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (ht : t.TameRelAt q) :
    PWord.evalZ ⇑t E E₂ (tameRelW n q) = 1 := by
  rw [tameRelW, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
    PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, zpow_natCast]
  change conjR t.τ t.σ * (t.τ ^ q)⁻¹ = 1
  rw [ht, mul_inv_cancel]

set_option maxHeartbeats 1600000 in
/-- Every ramified degree-one cocycle has a unique normal representative consisting of one
`x₁` core coordinate and the `h` hyperbolic handle pairs.  The proof is the arbitrary-`q`
version of Roe's ramified normal form: the wild row kills `x₀`, a coboundary kills `tau`, and
then the q-independent tame pivot kills `sigma`. -/
theorem lSqFam_ramified_normalForm
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hL : PWord.evalZ ⇑t
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) (lSqW h) = 1) :
    ∀ x,
      heisD1 ⇑t
          (Certificates.LSqStokes.lSqFam h q
            (omega2Exp (4 * Monoid.exponent C))) x = 0 →
        ∃! p : A × (Fin h × Fin 2 → A),
          x - lSqRamifiedNormal h p.1 p.2 ∈ Set.range (heisD0 ⇑t) := by
  let e := omega2Exp (4 * Monoid.exponent C)
  let w := Certificates.LSqStokes.lSqFam h q e
  have hr : ∀ k, FreeGroup.lift (⇑t) (w k) = 1 := by
    intro k
    fin_cases k
    · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr
        (evalZ_tameRelW_eq_one_of_tameRelAt t _ _ ht)
    · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hL
  have hTsurj : Function.Surjective (fun v : A ↦ t.τ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hτfpf
  have hcoreTriv : ∀ (i : Fin 2) (a : A), t (coreLetter h i) • a = a := by
    intro i a
    exact hwild _ a
  have hhandleUTriv : ∀ (j : Fin h) (a : A), t (handleU j) • a = a := by
    intro j a
    exact hwild _ a
  have hhandleVTriv : ∀ (j : Fin h) (a : A), t (handleV j) • a = a := by
    intro j a
    exact hwild _ a
  intro x hx
  have hxcore0 : x (coreLetter h 0) = 0 := by
    have hz := congrFun hx 1
    rw [heisD1_lSqFam_ramified_apply t hA₂ ht hwild hτfpf hTodd] at hz
    have hz' : t.σ⁻¹ • x (coreLetter h 0) = 0 := by simpa using hz
    rw [← smul_inv_smul t.σ (x (coreLetter h 0)), hz', smul_zero]
  obtain ⟨v, hv⟩ := hTsurj (x .tau)
  let x' := x - heisD0 (⇑t) v
  have hx' : heisD1 (⇑t) w x' = 0 := by
    change heisD1 (⇑t) w (x - heisD0 (⇑t) v) = 0
    rw [map_sub, hx, heisD1_comp_heisD0 (⇑t) w hr v, sub_zero]
  have hx'τ : x' .tau = 0 := by
    simp [x', heisD0_apply, hv]
  have hx'core0 : x' (coreLetter h 0) = 0 := by
    simp [x', heisD0_apply, hcoreTriv, hxcore0]
  have hx'σ : x' .sigma = 0 := by
    have hz := congrFun hx' 0
    rw [heisD1_lSqFam_ramified_apply t hA₂ ht hwild hτfpf hTodd] at hz
    have hz' : t.σ⁻¹ • (t.τ • x' .sigma - x' .sigma) = 0 := by
      simpa [hx'τ] using hz
    have hdiff : t.τ • x' .sigma - x' .sigma = 0 := by
      have h := congrArg (t.σ • ·) hz'
      simpa using h
    exact hτfpf _ (sub_eq_zero.mp hdiff)
  let z := (lSqCoreHandleAddEquiv h A x).2
  let p₀ : A × (Fin h × Fin 2 → A) := (x (coreLetter h 1), z)
  have hnormal : lSqRamifiedNormal h p₀.1 p₀.2 = x' := by
    apply (lSqCoreHandleAddEquiv h A).injective
    apply Prod.ext
    · funext g
      cases g with
      | sigma => simpa [p₀] using hx'σ.symm
      | tau => simpa [p₀] using hx'τ.symm
      | wild i =>
          fin_cases i
          · simpa [p₀] using hx'core0.symm
          · simp [p₀, x', heisD0_apply, hcoreTriv]
    · funext jk
      rcases jk with ⟨j, k⟩
      fin_cases k
      · simp [p₀, z, x', heisD0_apply, hhandleUTriv]
      · simp [p₀, z, x', heisD0_apply, hhandleVTriv]
  refine ⟨p₀, ?_, ?_⟩
  · refine ⟨v, ?_⟩
    rw [hnormal]
    simp [x']
  · intro p hp
    obtain ⟨u, hu⟩ := hp
    apply Prod.ext
    · have hc := congrFun hu (coreLetter h 1)
      rw [heisD0_apply, hcoreTriv, sub_self] at hc
      simp only [Pi.sub_apply, lSqRamifiedNormal_core_one] at hc
      exact (sub_eq_zero.mp hc.symm).symm
    · funext jk
      rcases jk with ⟨j, k⟩
      fin_cases k
      · have hc := congrFun hu (handleU j)
        rw [heisD0_apply, hhandleUTriv, sub_self] at hc
        simp only [Pi.sub_apply, lSqRamifiedNormal_handleU] at hc
        have hp := (sub_eq_zero.mp hc.symm).symm
        simpa [p₀, z] using hp
      · have hc := congrFun hu (handleV j)
        rw [heisD0_apply, hhandleVTriv, sub_self] at hc
        simp only [Pi.sub_apply, lSqRamifiedNormal_handleV] at hc
        have hp := (sub_eq_zero.mp hc.symm).symm
        simpa [p₀, z] using hp

end

end GQ2.Dyadic
