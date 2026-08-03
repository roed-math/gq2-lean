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

@[simp] theorem lSqRamifiedNormal_zero
    (h : ℕ) {A : Type*} [AddCommGroup A] :
    lSqRamifiedNormal h (0 : A) (0 : Fin h × Fin 2 → A) = 0 := by
  have hx : x1Supported (0 : A) = 0 := by
    funext i
    fin_cases i <;> simp [x1Supported]
  rw [lSqRamifiedNormal, hx, q2Offsets_zero]
  exact (lSqCoreHandleAddEquiv h A).symm.map_zero

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

/-! ## The pairing on normal coordinates -/

/-- Every ramified normal cochain is a cocycle. -/
theorem heisD1_lSqRamifiedNormal_eq_zero
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (d : A) (z : Fin h × Fin 2 → A) :
    heisD1 ⇑t
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (4 * Monoid.exponent C)))
        (lSqRamifiedNormal h d z) = 0 := by
  rw [heisD1_lSqFam_ramified_apply t hA₂ ht hwild hτfpf hTodd]
  funext k
  fin_cases k <;> simp

set_option maxHeartbeats 1600000 in
/-- On normal coordinates the middle Stokes map is the invertible Roe core operator plus `h`
standard hyperbolic planes. -/
theorem heisEta1_lSqFam_ramified_normal
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (d : A) (z : Fin h × Fin 2 → A)
    (lam : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A) :
    heisEta1 ⇑t
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (4 * Monoid.exponent C)))
        (lSqRamifiedNormal h d z) (lSqRamifiedNormal h lam mu)
      = lam (d + (Marking.toQ2 (LSq.coreMarking t)).sigma2 • d
          + (Marking.toQ2 (LSq.coreMarking t)).sigma2⁻¹ • d)
        + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0))) := by
  simpa using
    (heisEta1_lSqFam_ramified_core_x1Supported t hA₂ hwild hτfpf hTodd
      (lSqRamifiedNormal h d z) (lSqRamifiedNormal h lam mu) d lam
      (lSqRamifiedNormal_core h d z) (lSqRamifiedNormal_core h lam mu))

/-- The normal-coordinate pairing separates every nonzero primal coordinate. -/
theorem lSqFam_ramified_normal_pairing_separates_left
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (p : A × (Fin h × Fin 2 → A)) (hp : p ≠ 0) :
    ∃ r : ElemDual A × (Fin h × Fin 2 → ElemDual A),
      heisEta1 ⇑t
          (Certificates.LSqStokes.lSqFam h q
            (omega2Exp (4 * Monoid.exponent C)))
          (lSqRamifiedNormal h p.1 p.2)
          (lSqRamifiedNormal h r.1 r.2) ≠ 0 := by
  classical
  by_cases hd : p.1 = 0
  · have hz : p.2 ≠ 0 := by
      intro hz
      apply hp
      exact Prod.ext hd (by simpa using hz)
    obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.mp hz
    obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hjk
    fin_cases k
    · let mu : Fin h × Fin 2 → ElemDual A := Pi.single (j, 1) lam
      refine ⟨(0, mu), ?_⟩
      rw [heisEta1_lSqFam_ramified_normal t hA₂ hwild hτfpf hTodd, hd]
      have hsum : ∑ x, (mu (x, 0) (p.2 (x, 1)) + mu (x, 1) (p.2 (x, 0))) =
          lam (p.2 (j, 0)) := by
        rw [Finset.sum_eq_single j]
        · simp [mu]
        · intro b _ hbj
          simp [mu, hbj]
        · simp
      rw [hsum]
      simpa using hlam
    · let mu : Fin h × Fin 2 → ElemDual A := Pi.single (j, 0) lam
      refine ⟨(0, mu), ?_⟩
      rw [heisEta1_lSqFam_ramified_normal t hA₂ hwild hτfpf hTodd, hd]
      have hsum : ∑ x, (mu (x, 0) (p.2 (x, 1)) + mu (x, 1) (p.2 (x, 0))) =
          lam (p.2 (j, 1)) := by
        rw [Finset.sum_eq_single j]
        · simp [mu]
        · intro b _ hbj
          simp [mu, hbj]
        · simp
      rw [hsum]
      simpa using hlam
  · let t₀ := Marking.toQ2 (LSq.coreMarking t)
    have hop := pairingR_operator_injective (V := A) t₀ hA₂
    have hne : p.1 + t₀.sigma2 • p.1 + t₀.sigma2⁻¹ • p.1 ≠ 0 := by
      intro hzero
      apply hd
      apply hop
      simp [hzero]
    obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hne
    refine ⟨(lam, 0), ?_⟩
    rw [heisEta1_lSqFam_ramified_normal t hA₂ hwild hτfpf hTodd]
    simpa [t₀] using hlam

/-- The normal-coordinate pairing also separates every nonzero dual coordinate. -/
theorem lSqFam_ramified_normal_pairing_separates_right
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (r : ElemDual A × (Fin h × Fin 2 → ElemDual A)) (hr : r ≠ 0) :
    ∃ p : A × (Fin h × Fin 2 → A),
      heisEta1 ⇑t
          (Certificates.LSqStokes.lSqFam h q
            (omega2Exp (4 * Monoid.exponent C)))
          (lSqRamifiedNormal h p.1 p.2)
          (lSqRamifiedNormal h r.1 r.2) ≠ 0 := by
  classical
  by_cases hlam : r.1 = 0
  · have hmu : r.2 ≠ 0 := by
      intro hmu
      apply hr
      exact Prod.ext hlam (by simpa using hmu)
    obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.mp hmu
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hjk
    fin_cases k
    · let z : Fin h × Fin 2 → A := Pi.single (j, 1) a
      refine ⟨(0, z), ?_⟩
      rw [heisEta1_lSqFam_ramified_normal t hA₂ hwild hτfpf hTodd, hlam]
      have hsum : ∑ x, (r.2 (x, 0) (z (x, 1)) + r.2 (x, 1) (z (x, 0))) =
          r.2 (j, 0) a := by
        rw [Finset.sum_eq_single j]
        · simp [z]
        · intro b _ hbj
          simp [z, hbj]
        · simp
      rw [hsum]
      simpa using ha
    · let z : Fin h × Fin 2 → A := Pi.single (j, 0) a
      refine ⟨(0, z), ?_⟩
      rw [heisEta1_lSqFam_ramified_normal t hA₂ hwild hτfpf hTodd, hlam]
      have hsum : ∑ x, (r.2 (x, 0) (z (x, 1)) + r.2 (x, 1) (z (x, 0))) =
          r.2 (j, 1) a := by
        rw [Finset.sum_eq_single j]
        · simp [z]
        · intro b _ hbj
          simp [z, hbj]
        · simp
      rw [hsum]
      simpa using ha
  · obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hlam
    let t₀ := Marking.toQ2 (LSq.coreMarking t)
    have hopsurj := Finite.injective_iff_surjective.mp
      (pairingR_operator_injective (V := A) t₀ hA₂)
    obtain ⟨d, hd⟩ := hopsurj a
    refine ⟨(d, 0), ?_⟩
    rw [heisEta1_lSqFam_ramified_normal t hA₂ hwild hτfpf hTodd,
      show d + t₀.sigma2 • d + t₀.sigma2⁻¹ • d = a from hd]
    simpa [t₀] using ha

/-! ## Stokes assembly -/

/-- Cardinality of middle cohomology from a unique family of normal representatives. -/
theorem card_stokesH1_of_normalForm
    {K₀ K₁ K₂ P : Type*} [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂]
    [Finite K₁] [Finite P]
    (d₀ : K₀ →+ K₁) (d₁ : K₁ →+ K₂) (normal : P → K₁)
    (hmem : ∀ p, d₁ (normal p) = 0)
    (hnf : ∀ x, d₁ x = 0 → ∃! p, x - normal p ∈ Set.range d₀) :
    Nat.card (StokesH1 d₀ d₁) = Nat.card P := by
  have key : ∀ (a b : ↥d₁.ker),
      stokesH1Mk d₀ d₁ a = stokesH1Mk d₀ d₁ b ↔
        b.val - a.val ∈ Set.range d₀ := by
    intro a b
    show QuotientAddGroup.mk a = QuotientAddGroup.mk b ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -a.val + b.val ∈ d₀.range ↔ b.val - a.val ∈ Set.range d₀
    rw [show -a.val + b.val = b.val - a.val from by abel]
    exact AddMonoidHom.mem_range
  refine (Nat.card_eq_of_bijective
    (fun p ↦ stokesH1Mk d₀ d₁ ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩)
    ⟨?_, ?_⟩).symm
  · intro p p' hpp
    rw [key] at hpp
    obtain ⟨p₀, -, huniq⟩ := hnf (normal p) (hmem p)
    have hp : p = p₀ := huniq p (show normal p - normal p ∈ Set.range d₀ from
      ⟨0, by simp⟩)
    have hp' : p' = p₀ := huniq p' (by
      obtain ⟨v, hv⟩ := hpp
      refine ⟨-v, ?_⟩
      rw [map_neg, hv]
      abel)
    exact hp.trans hp'.symm
  · intro H
    obtain ⟨x, rfl⟩ := stokesH1Mk_surjective d₀ d₁ H
    obtain ⟨p, hp, -⟩ := hnf x.val (AddMonoidHom.mem_ker.mp x.2)
    exact ⟨p, (key ⟨normal p, AddMonoidHom.mem_ker.mpr (hmem p)⟩ x).mpr hp⟩

/-- Fixed-point-free `tau` makes the bottom differential injective. -/
theorem heisD0_injective_of_tau_fixedPointFree
    {n : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking n C) (hτfpf : ∀ a : A, t.τ • a = a → a = 0) :
    Function.Injective (heisD0 (A := A) ⇑t) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply hτfpf a
  have hcoord := congrFun ha Generator.tau
  change t.τ • a - a = 0 at hcoord
  exact sub_eq_zero.mp hcoord

set_option maxHeartbeats 2400000 in
/-- **Ramified Stokes duality for the improved uniform `L_sq` presentation.**

This is stronger than the simple-module theorem needed by devissage: it assumes directly the
ramified action facts supplied by simplicity, and proves the six Stokes clauses for every finite
elementary module satisfying them.  The tame relation remains q-parametric; no specialization
to Roe's `q = 2` complex is used. -/
theorem lSqStokesDuality_ramified
    {h q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2 * h + 1) C) (hA₂ : ∀ a : A, a + a = 0)
    (hq : Even q) (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hL : PWord.evalZ ⇑t
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) (lSqW h) = 1) :
    StokesDuality ⇑t
      (Certificates.LSqStokes.lSqFam h q
        (omega2Exp (4 * Monoid.exponent C))) A := by
  classical
  let e := omega2Exp (4 * Monoid.exponent C)
  let w := Certificates.LSqStokes.lSqFam h q e
  have hr : ∀ k, FreeGroup.lift (⇑t) (w k) = 1 := by
    intro k
    fin_cases k
    · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr
        (evalZ_tameRelW_eq_one_of_tameRelAt t _ _ ht)
    · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hL
  have he : Odd e := odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
  have hend : IsStokesEndpoint w := Certificates.LSqStokes.lSq_isStokesEndpoint hq he
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hwildD : ∀ (i : Fin (2 * h + 1 + 1)) (lam : ElemDual A), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  have hToddD : ∀ lam : ElemDual A, powOmega2 t.τ • lam = lam :=
    fun lam ↦ elemDual_smul_eq_self hTodd lam
  have hd₀A := heisD0_injective_of_tau_fixedPointFree t hτfpf
  have hd₀D := heisD0_injective_of_tau_fixedPointFree (A := ElemDual A) t hτfpfD
  have hd₁A : Function.Surjective (heisD1 (A := A) (⇑t) w) :=
    heisD1_lSqFam_surjective_ramified t hA₂ ht hwild hτfpf hTodd
  have hd₁D : Function.Surjective (heisD1 (A := ElemDual A) (⇑t) w) :=
    heisD1_lSqFam_surjective_ramified t hA₂D ht hwildD hτfpfD hToddD
  have hnfA := lSqFam_ramified_normalForm t hA₂ ht hwild hτfpf hTodd hL
  have hnfD := lSqFam_ramified_normalForm (A := ElemDual A) t hA₂D ht hwildD hτfpfD hToddD hL
  have hmemA : ∀ p : A × (Fin h × Fin 2 → A),
      heisD1 (⇑t) w (lSqRamifiedNormal h p.1 p.2) = 0 :=
    fun p ↦ heisD1_lSqRamifiedNormal_eq_zero t hA₂ ht hwild hτfpf hTodd p.1 p.2
  have hmemD : ∀ r : ElemDual A × (Fin h × Fin 2 → ElemDual A),
      heisD1 (⇑t) w (lSqRamifiedNormal h r.1 r.2) = 0 :=
    fun r ↦ heisD1_lSqRamifiedNormal_eq_zero t hA₂D ht hwildD hτfpfD hToddD r.1 r.2
  have hs₀ := stokes_square₀ (A := A) (⇑t) w hr hend
  have hs₁ := stokes_square₁ (A := A) (⇑t) w hr hend
  apply (stokesDuality_iff_cohomologyBijections (⇑t) w A hr hend).mpr
  refine ⟨?_, ?_, ?_⟩
  · have htargetInj : Function.Injective
        (dualMap (heisD1 (A := ElemDual A) (⇑t) w)) :=
      dualMap_injective _ hd₁D
    constructor
    · intro a b _
      apply Subtype.ext
      have ha0 : a.val = 0 := hd₀A (by
        rw [AddMonoidHom.mem_ker.mp a.2, map_zero])
      have hb0 : b.val = 0 := hd₀A (by
        rw [AddMonoidHom.mem_ker.mp b.2, map_zero])
      rw [ha0, hb0]
    · intro y
      have hy0 : y.val = 0 := htargetInj (by
        rw [AddMonoidHom.mem_ker.mp y.2, map_zero])
      refine ⟨0, ?_⟩
      apply Subtype.ext
      simp [hy0]
  · have h1inj : Function.Injective (stokesH1Map hs₀ hs₁) := by
      rw [injective_iff_map_eq_zero]
      intro H hH
      obtain ⟨x, rfl⟩ := stokesH1Mk_surjective
        (heisD0 (A := A) (⇑t)) (heisD1 (⇑t) w) H
      obtain ⟨p, hp, -⟩ := hnfA x.val (AddMonoidHom.mem_ker.mp x.2)
      by_cases hp0 : p = 0
      · rw [hp0] at hp
        simp only [Prod.fst_zero, Prod.snd_zero, lSqRamifiedNormal_zero, sub_zero] at hp
        exact (stokesH1Mk_eq_zero_iff
          (heisD0 (A := A) (⇑t)) (heisD1 (⇑t) w) x).mpr hp
      · obtain ⟨r, hpair⟩ :=
          lSqFam_ramified_normal_pairing_separates_left (q := q)
            t hA₂ hwild hτfpf hTodd p hp0
        let y := lSqRamifiedNormal h r.1 r.2
        have hy : heisD1 (A := ElemDual A) (⇑t) w y = 0 := hmemD r
        rw [stokesH1Mk, stokesH1Map, QuotientAddGroup.map_mk,
          QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hH
        obtain ⟨xi, hxi⟩ := AddMonoidHom.mem_range.mp hH
        have hvan : heisEta1 (⇑t) w x.val y = 0 := by
          have heq := DFunLike.congr_fun hxi y
          rw [dualMap_apply, hy, map_zero] at heq
          exact heq.symm
        obtain ⟨v, hv⟩ := hp
        have hxrepr : x.val = lSqRamifiedNormal h p.1 p.2 + heisD0 (⇑t) v := by
          rw [hv]
          abel
        have hsame : heisEta1 (⇑t) w x.val y =
            heisEta1 (⇑t) w (lSqRamifiedNormal h p.1 p.2) y := by
          rw [hxrepr, map_add]
          change heisEta1 (⇑t) w (lSqRamifiedNormal h p.1 p.2) y +
            heisEta1 (⇑t) w (heisD0 (⇑t) v) y =
              heisEta1 (⇑t) w (lSqRamifiedNormal h p.1 p.2) y
          rw [heisEta1_comp_d0 (⇑t) w hr hend v y, hy, map_zero]
          simp
        exact (hpair (hsame ▸ hvan)).elim
    have hcardA : Nat.card (StokesH1 (heisD0 (A := A) (⇑t)) (heisD1 (⇑t) w)) =
        Nat.card (A × (Fin h × Fin 2 → A)) :=
      card_stokesH1_of_normalForm _ _
        (fun p : A × (Fin h × Fin 2 → A) ↦ lSqRamifiedNormal h p.1 p.2)
        hmemA hnfA
    have hcardD : Nat.card
        (StokesH1 (heisD0 (A := ElemDual A) (⇑t))
          (heisD1 (A := ElemDual A) (⇑t) w)) =
        Nat.card (ElemDual A × (Fin h × Fin 2 → ElemDual A)) :=
      card_stokesH1_of_normalForm _ _
        (fun r : ElemDual A × (Fin h × Fin 2 → ElemDual A) ↦
          lSqRamifiedNormal h r.1 r.2) hmemD hnfD
    have hcoordCard : Nat.card (A × (Fin h × Fin 2 → A)) =
        Nat.card (ElemDual A × (Fin h × Fin 2 → ElemDual A)) := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fun, card_elemDual hA₂]
    have htargetCard : Nat.card
        (StokesH1 (dualMap (heisD1 (A := ElemDual A) (⇑t) w))
          (dualMap (heisD0 (A := ElemDual A) (⇑t)))) =
        Nat.card (StokesH1 (heisD0 (A := ElemDual A) (⇑t))
          (heisD1 (A := ElemDual A) (⇑t) w)) := by
      rw [Nat.card_eq_of_bijective _ (wordH1_target_uc (A := A) (⇑t) w hr),
        card_elemDual (stokesH1_two_torsion _ _ wordDual_two_torsion)]
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨h1inj, hcardA.trans (hcoordCard.trans (hcardD.symm.trans htargetCard.symm))⟩
  · have htargetSurj : Function.Surjective
        (dualMap (heisD0 (A := ElemDual A) (⇑t))) :=
      dualMap_surjective wordDual_two_torsion _ hd₀D
    have hsourceZero : ∀ z : StokesH2 (heisD1 (A := A) (⇑t) w), z = 0 := by
      intro z
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        (AddMonoidHom.mem_range.mpr (hd₁A a))
    have htargetZero : ∀ z : StokesH2
        (dualMap (heisD0 (A := ElemDual A) (⇑t))), z = 0 := by
      intro z
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        (AddMonoidHom.mem_range.mpr (htargetSurj a))
    constructor
    · intro a b _
      rw [hsourceZero a, hsourceZero b]
    · intro y
      refine ⟨0, ?_⟩
      rw [map_zero, htargetZero y]

end

end GQ2.Dyadic
