/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.N0M0UnramifiedStokes

/-!
# Ramified Stokes duality for the uniform compact-`M` word

On a ramified elementary coefficient the compact-`M` word has *exactly* the compact-`N` first
Fox row, `−S⁻¹·a(x₂)` (`foxD_mCompact_ram`): the `𝓔`-correction block cancels the
`A₀²[A₀,x₁]` contribution over `𝔽₂`.  So the whole first-order half of the normal-form route —
surjectivity of the differential, and the unique normal representative with coordinates
`A × A × (Fin h × Fin 2 → A)` — is shared with the compact-`N` row, and is proved here once, for
an arbitrary resolved family with that row.

What is **not** shared is the second-order value.  The compact-`N` word's `τ`-carrying factor is
second-order trivial on normal offsets, so its row is a sum of jet-zero factors
(`heisZ_nCompact_normalOffsets`); the compact-`M` word's `A₀ = x₀⁻¹σ₂^{−m}` carries the operator
`S₂^{−m}`, and `powOmega2 t.σ` need *not* act trivially on a ramified simple module.  (Witness:
`C = ⟨τ⟩ ⋊ ⟨σ⟩` with `τ` of order `3` and `σ` of order `2` inverting it, `A = 𝔽₄` with `σ` the
Frobenius: `τ` is fixed-point free, `powOmega2 τ = 1`, and `powOmega2 σ = σ` is nontrivial.)

The residual input is therefore isolated below as `RamifiedNormalPairingSeparates`: left
nondegeneracy of the traced pairing on the ramified normal coordinates.  Everything else on the
compact-`M` ramified row is proved.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic

variable {h α q : ℕ}

/-! ## The shared ramified row

`![S⁻¹(a(τ) + (T−1)a(σ)) − N_q(T)a(τ), −S⁻¹·a(x₂)]` — the arbitrary-`q` tame row and the single
`x₂`-pivot both compact even words have on a ramified module. -/

variable {C A : Type*} [Group C] [AddCommGroup A] [Finite A] [DistribMulAction C A]

/-- Surjectivity of a differential with the shared ramified row. -/
theorem heisD1_surjective_of_ramified_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          -(t.σ⁻¹ • x (coreLetter h 2))])
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0) :
    Function.Surjective (heisD1 (A := A) ⇑t w) := by
  classical
  intro r
  obtain ⟨v, hv⟩ := tameSigmaColumn_surjective_of_fixedPointFree t hτfpf (r 0)
  let x : Generator (2 + 2 * h) → A := fun g ↦
    if g = .sigma then v
    else if g = coreLetter h 2 then -(t.σ • r 1) else 0
  refine ⟨x, ?_⟩
  rw [hrow x]
  funext k
  have hσx2 : (.sigma : Generator (2 + 2 * h)) ≠ coreLetter h 2 :=
    Certificates.sigma_ne_coreLetter_two h
  have hτσ : (.tau : Generator (2 + 2 * h)) ≠ .sigma := by simp
  have hτx2 : (.tau : Generator (2 + 2 * h)) ≠ coreLetter h 2 :=
    Certificates.tau_ne_coreLetter_two h
  fin_cases k
  · change t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
        - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau = r 0
    simp only [x, if_pos, if_neg hτσ, if_neg hτx2,
      zero_add, smul_zero, Finset.sum_const_zero, sub_zero]
    exact hv
  · change -(t.σ⁻¹ • x (coreLetter h 2)) = r 1
    have hx2 : x (coreLetter h 2) = -(t.σ • r 1) := by simp [x, hσx2.symm]
    rw [hx2, smul_neg, inv_smul_smul, neg_neg]

omit [Finite A] in
/-- Every ramified normal cochain is a cocycle for the shared ramified row. -/
theorem heisD1_evenNormal_eq_zero_of_ramified_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          -(t.σ⁻¹ • x (coreLetter h 2))])
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    heisD1 ⇑t w (evenNormal h d₀ d₁ z) = 0 := by
  rw [hrow]
  funext k
  fin_cases k <;> simp

set_option maxHeartbeats 1600000 in
/-- The ramified normal form for the shared ramified row: the wild pivot kills `x₂`, a
coboundary kills `tau`, and the `q`-independent tame pivot kills `sigma`. -/
theorem evenNormalForm_of_ramified_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          -(t.σ⁻¹ • x (coreLetter h 2))])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 → ∃! p : A × A × (Fin h × Fin 2 → A),
      x - evenNormal h p.1 p.2.1 p.2.2 ∈ Set.range (heisD0 ⇑t) := by
  have hTsurj : Function.Surjective (fun v : A ↦ t.τ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hτfpf
  have hcoreTriv : ∀ (i : Fin 3) (a : A), t (coreLetter h i) • a = a := fun i a ↦ hwild _ a
  have hhandleUTriv : ∀ (j : Fin h) (a : A), t (handleU j) • a = a := fun j a ↦ hwild _ a
  have hhandleVTriv : ∀ (j : Fin h) (a : A), t (handleV j) • a = a := fun j a ↦ hwild _ a
  intro x hx
  have hxcore2 : x (coreLetter h 2) = 0 := by
    have hz := congrFun hx 1
    rw [hrow x] at hz
    have hz' : t.σ⁻¹ • x (coreLetter h 2) = 0 := by
      have hh : -(t.σ⁻¹ • x (coreLetter h 2)) = (0 : A) := by simpa using hz
      rwa [neg_eq_zero] at hh
    rw [← smul_inv_smul t.σ (x (coreLetter h 2)), hz', smul_zero]
  obtain ⟨v, hv⟩ := hTsurj (x .tau)
  let x' := x - heisD0 (⇑t) v
  have hx' : heisD1 (⇑t) w x' = 0 := by
    change heisD1 (⇑t) w (x - heisD0 (⇑t) v) = 0
    rw [map_sub, hx, heisD1_comp_heisD0 (⇑t) w hr v, sub_zero]
  have hx'τ : x' .tau = 0 := by
    simp [x', heisD0_apply, hv]
  have hx'core2 : x' (coreLetter h 2) = 0 := by
    simp [x', heisD0_apply, hcoreTriv, hxcore2]
  have hx'σ : x' .sigma = 0 := by
    have hz := congrFun hx' 0
    rw [hrow x'] at hz
    have hz' : t.σ⁻¹ • (t.τ • x' .sigma - x' .sigma) = 0 := by
      simpa [hx'τ] using hz
    have hdiff : t.τ • x' .sigma - x' .sigma = 0 := by
      have hs := congrArg (t.σ • ·) hz'
      simpa using hs
    exact hτfpf _ (sub_eq_zero.mp hdiff)
  let z := (EvenCore.coreHandleAddEquiv h A x).2
  let p₀ : A × A × (Fin h × Fin 2 → A) := (x (coreLetter h 0), x (coreLetter h 1), z)
  have hnormal : evenNormal h p₀.1 p₀.2.1 p₀.2.2 = x' := by
    apply (EvenCore.coreHandleAddEquiv h A).injective
    apply Prod.ext
    · funext g
      cases g with
      | sigma => simpa [p₀] using hx'σ.symm
      | tau => simpa [p₀] using hx'τ.symm
      | wild i =>
          fin_cases i
          · simp [p₀, x', heisD0_apply, hcoreTriv]
          · simp [p₀, x', heisD0_apply, hcoreTriv]
          · simpa [p₀] using hx'core2.symm
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
    · have hc := congrFun hu (coreLetter h 0)
      rw [heisD0_apply, hcoreTriv, sub_self] at hc
      simp only [Pi.sub_apply, evenNormal_coreLetter, Matrix.cons_val_zero] at hc
      exact (sub_eq_zero.mp hc.symm).symm
    · apply Prod.ext
      · have hc := congrFun hu (coreLetter h 1)
        rw [heisD0_apply, hcoreTriv, sub_self] at hc
        simp only [Pi.sub_apply, evenNormal_coreLetter, Matrix.cons_val_one,
          Matrix.cons_val_zero] at hc
        exact (sub_eq_zero.mp hc.symm).symm
      · funext jk
        rcases jk with ⟨j, k⟩
        fin_cases k
        · have hc := congrFun hu (handleU j)
          rw [heisD0_apply, hhandleUTriv, sub_self] at hc
          simp only [Pi.sub_apply, evenNormal_handleU] at hc
          have hpj := (sub_eq_zero.mp hc.symm).symm
          simpa [p₀, z] using hpj
        · have hc := congrFun hu (handleV j)
          rw [heisD0_apply, hhandleVTriv, sub_self] at hc
          simp only [Pi.sub_apply, evenNormal_handleV] at hc
          have hpj := (sub_eq_zero.mp hc.symm).symm
          simpa [p₀, z] using hpj

set_option maxHeartbeats 3200000 in
/-- **Stokes duality for a shared-ramified-row even complex.**  The word enters only through its
first Fox row and through left nondegeneracy of the traced pairing on the normal coordinates. -/
theorem evenRamifiedStokesDuality_of_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) (hend : IsStokesEndpoint w)
    (hrowA : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          -(t.σ⁻¹ • x (coreLetter h 2))])
    (hrowD : ∀ y : Generator (2 + 2 * h) → ElemDual A, heisD1 ⇑t w y
      = ![t.σ⁻¹ • (y .tau + t.τ • y .sigma - y .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • y .tau,
          -(t.σ⁻¹ • y (coreLetter h 2))])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hsep : ∀ p : A × A × (Fin h × Fin 2 → A), p ≠ 0 →
      ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        heisEta1 ⇑t w (evenNormal h p.1 p.2.1 p.2.2)
          (evenNormal h r.1 r.2.1 r.2.2) ≠ 0) :
    StokesDuality ⇑t w A := by
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  exact evenNormalStokesDuality t w hA₂ hr hend
    (heisD0_injective_of_tau_fixedPointFree t hτfpf)
    (heisD0_injective_of_tau_fixedPointFree (A := ElemDual A) t hτfpfD)
    (heisD1_surjective_of_ramified_row t w hrowA hτfpf)
    (heisD1_surjective_of_ramified_row (A := ElemDual A) t w hrowD hτfpfD)
    (fun p ↦ heisD1_evenNormal_eq_zero_of_ramified_row t w hrowA p.1 p.2.1 p.2.2)
    (fun r ↦ heisD1_evenNormal_eq_zero_of_ramified_row (A := ElemDual A) t w hrowD
      r.1 r.2.1 r.2.2)
    (evenNormalForm_of_ramified_row t w hrowA hwild hτfpf hr)
    (evenNormalForm_of_ramified_row (A := ElemDual A) t w hrowD hwildD hτfpfD hr)
    hsep

/-! ## The compact-`M` ramified row -/

set_option maxHeartbeats 800000 in
/-- The complete first differential of the uniform compact-`M` word on a ramified elementary
module: literally the compact-`N` pair of rows. -/
theorem heisD1_mCompactFam_ramified_apply [Finite C]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (x : Generator (2 + 2 * h) → A) :
    heisD1 ⇑t (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) x
      = ![
          t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          -(t.σ⁻¹ • x (coreLetter h 2))] := by
  funext k
  fin_cases k
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
          (tameRelW (2 + 2 * h) q))).a =
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
          (Words.MCompact.mCompactW α h))).a = -(t.σ⁻¹ • x (coreLetter h 2))
    rw [← heisEvalZ_eq_lift,
      heisEvalZ_a_eq_foxD (resolverLifts_uniformWordLift_ramified hA₂),
      Certificates.MCompact.foxD_mCompact_ram t _ _ hA₂ hwild hτfpf hTodd]

set_option maxHeartbeats 3200000 in
/-- **Ramified Stokes duality for the uniform compact-`M` presentation, from the residual
pairing input.**  Every first-order ingredient is discharged; the hypothesis `hsep` is exactly
left nondegeneracy of the traced pairing on the ramified normal coordinates, whose evaluation
is the missing second-order row `heisZ_mCompact_ram`. -/
theorem mCompactStokesDuality_ramified_of_separation [Finite C]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (hq : Even q) (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hM : PWord.evalZ ⇑t
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (Words.MCompact.mCompactW α h) = 1)
    (hsep : ∀ p : A × A × (Fin h × Fin 2 → A), p ≠ 0 →
      ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        heisEta1 ⇑t (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
          (evenNormal h p.1 p.2.1 p.2.2) (evenNormal h r.1 r.2.1 r.2.2) ≠ 0) :
    StokesDuality ⇑t
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) A := by
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  have hToddD : ∀ lam : ElemDual A, powOmega2 t.τ • lam = lam :=
    fun lam ↦ elemDual_smul_eq_self hTodd lam
  have hr : ∀ k, FreeGroup.lift (⇑t)
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)) k) = 1 := by
    intro k
    fin_cases k
    · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr
        (evalZ_tameRelW_eq_one_of_tameRelAt t _ _ ht)
    · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hM
  have he : Odd (omega2Exp (4 * Monoid.exponent C)) :=
    odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
      (fourMulExponent_ne_zero_and_even C).2
  exact evenRamifiedStokesDuality_of_row t _ hA₂ hr
    (Certificates.MCompact.mCompact_isStokesEndpoint hq he)
    (heisD1_mCompactFam_ramified_apply t hA₂ ht hwild hτfpf hTodd)
    (heisD1_mCompactFam_ramified_apply (A := ElemDual A) t hA₂D ht hwildD hτfpfD hToddD)
    hwild hτfpf hsep

end

end GQ2.Dyadic
