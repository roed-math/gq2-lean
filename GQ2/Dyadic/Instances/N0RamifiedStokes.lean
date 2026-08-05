/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.LRamifiedStokes
import GQ2.Dyadic.Instances.EvenHandleCoordinates

/-!
# Ramified Stokes duality for the uniform compact-`N` word

The odd row's ramified certificate (`LRamifiedStokes`) proves Stokes duality for `L_sq` by the
normal-form route: the first differential is onto, every degree-one cocycle has a unique normal
representative, the middle pairing separates both sides of the normal coordinates, and
`card_stokesH1_of_normalForm` turns that into the middle cardinality identity.

This file runs the same route for the compact-`N` branch word

```
R_{N,α,0} = x₀^{2+2^α} · [x₀,x₁] · x₂^{-σ} · (x₂τ)^{ω₂} · H_h,    α ≥ 2.
```

Two things change relative to the odd row.

* The wild pivot moves from `x₀` to `x₂`: on a ramified module the whole word collapses to
  `−S⁻¹·a(x₂)` (`foxD_nCompact_ram`), so the surviving core is the **two**-dimensional
  `(x₀, x₁)` block rather than the one-dimensional `x₁` block of `L_sq`.  The middle
  cohomology therefore has normal coordinates `A × A × (Fin h × Fin 2 → A)`.
* The core pairing is no longer Roe's operator `1 + σ₂ + σ₂⁻¹` but the constant unimodular
  matrix `((1,1),(1,0))`: the `x₀`-diagonal comes from `x₀^{2+2^α}` (odd binomial exactly at
  `α ≥ 2`) and the cross from the commutator `[x₀,x₁]`.  Nothing in it depends on the marking,
  which is why the `α ≥ 2` hypothesis is the only arithmetic input.

The second-order value used here is **new**: every existing compact-`N` Stokes row assumes `τ`
acts trivially.  On a normal representative, though, no `τ`-hypothesis is needed at all — the
`τ`-carrying factor `(x₂τ)^{ω₂}` lies in the second-order trivial subgroup as soon as the
offsets vanish on `τ` and `x₂`, which is exactly the normal-form condition.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic

variable {h α q : ℕ}

/-! ## Normal cochains of the even alphabet -/

/-- An offset vector on the degree-`2` core supported on the three wild letters. -/
def evenCoreOffsets {A : Type*} [AddCommGroup A] (d : Fin 3 → A) : Generator 2 → A
  | .sigma => 0
  | .tau => 0
  | .wild i => d i

@[simp] theorem evenCoreOffsets_sigma {A : Type*} [AddCommGroup A] (d : Fin 3 → A) :
    evenCoreOffsets d .sigma = 0 := rfl

@[simp] theorem evenCoreOffsets_tau {A : Type*} [AddCommGroup A] (d : Fin 3 → A) :
    evenCoreOffsets d .tau = 0 := rfl

@[simp] theorem evenCoreOffsets_wild {A : Type*} [AddCommGroup A] (d : Fin 3 → A) (i : Fin 3) :
    evenCoreOffsets d (.wild i) = d i := rfl

theorem evenCoreOffsets_zero {A : Type*} [AddCommGroup A] :
    evenCoreOffsets (0 : Fin 3 → A) = 0 := by
  funext g
  cases g <;> rfl

/-- A ramified normal cochain of the compact-`N` complex: the core is supported on `x₀` and
`x₁`, while the handle coordinates are arbitrary. -/
def evenNormal (h : ℕ) {A : Type*} [AddCommGroup A]
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) : Generator (2 + 2 * h) → A :=
  (EvenCore.coreHandleAddEquiv h A).symm (evenCoreOffsets ![d₀, d₁, 0], z)

@[simp] theorem evenNormal_core (h : ℕ) {A : Type*} [AddCommGroup A]
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    EvenCore.coreRestrict h A (evenNormal h d₀ d₁ z) = evenCoreOffsets ![d₀, d₁, 0] := by
  rw [← EvenCore.coreHandleAddEquiv_fst]
  simp [evenNormal]

@[simp] theorem evenNormal_sigma (h : ℕ) {A : Type*} [AddCommGroup A]
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) : evenNormal h d₀ d₁ z .sigma = 0 :=
  congrFun (evenNormal_core h d₀ d₁ z) Generator.sigma

@[simp] theorem evenNormal_tau (h : ℕ) {A : Type*} [AddCommGroup A]
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) : evenNormal h d₀ d₁ z .tau = 0 :=
  congrFun (evenNormal_core h d₀ d₁ z) Generator.tau

@[simp] theorem evenNormal_coreLetter (h : ℕ) {A : Type*} [AddCommGroup A]
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) (i : Fin 3) :
    evenNormal h d₀ d₁ z (coreLetter h i) = ![d₀, d₁, 0] i :=
  congrFun (evenNormal_core h d₀ d₁ z) (Generator.wild i)

@[simp] theorem evenNormal_handleU {h : ℕ} {A : Type*} [AddCommGroup A]
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) (j : Fin h) :
    evenNormal h d₀ d₁ z (handleU j) = z (j, 0) := by
  have hh := congrArg (fun p : (Generator 2 → A) × (Fin h × Fin 2 → A) ↦ p.2 (j, 0))
    ((EvenCore.coreHandleAddEquiv h A).apply_symm_apply
      (evenCoreOffsets ![d₀, d₁, 0], z))
  change ((EvenCore.coreHandleAddEquiv h A) (evenNormal h d₀ d₁ z)).2 (j, 0) = z (j, 0) at hh
  rw [EvenCore.coreHandleAddEquiv_snd_zero] at hh
  exact hh

@[simp] theorem evenNormal_handleV {h : ℕ} {A : Type*} [AddCommGroup A]
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) (j : Fin h) :
    evenNormal h d₀ d₁ z (handleV j) = z (j, 1) := by
  have hh := congrArg (fun p : (Generator 2 → A) × (Fin h × Fin 2 → A) ↦ p.2 (j, 1))
    ((EvenCore.coreHandleAddEquiv h A).apply_symm_apply
      (evenCoreOffsets ![d₀, d₁, 0], z))
  change ((EvenCore.coreHandleAddEquiv h A) (evenNormal h d₀ d₁ z)).2 (j, 1) = z (j, 1) at hh
  rw [EvenCore.coreHandleAddEquiv_snd_one] at hh
  exact hh

@[simp] theorem evenNormal_zero (h : ℕ) {A : Type*} [AddCommGroup A] :
    evenNormal h (0 : A) (0 : A) (0 : Fin h × Fin 2 → A) = 0 := by
  have hx : (![(0 : A), 0, 0] : Fin 3 → A) = 0 := by
    funext i
    fin_cases i <;> rfl
  rw [evenNormal, hx, evenCoreOffsets_zero]
  exact (EvenCore.coreHandleAddEquiv h A).symm.map_zero

/-! ## The two ramified compact-`N` Fox rows -/

set_option maxHeartbeats 800000 in
/-- The complete first differential of the uniform compact-`N` word on a ramified elementary
module: the arbitrary-`q` tame row, and the wild row reduced to its single `x₂` pivot. -/
theorem heisD1_nCompactFam_ramified_apply
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a) (hα : 1 ≤ α)
    (x : Generator (2 + 2 * h) → A) :
    heisD1 ⇑t (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) x
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
          (nCompactW α h))).a = -(t.σ⁻¹ • x (coreLetter h 2))
    rw [← heisEvalZ_eq_lift,
      heisEvalZ_a_eq_foxD (resolverLifts_uniformWordLift_ramified hA₂),
      Certificates.foxD_nCompact_ram t _ _ hA₂ hwild hτfpf hTodd hα]

/-- The ramified compact-`N` first differential is onto: the tame row pivots on `sigma` and the
wild row pivots independently on `x₂`. -/
theorem heisD1_nCompactFam_surjective_ramified
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a) (hα : 1 ≤ α) :
    Function.Surjective
      (heisD1 (A := A) ⇑t (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))) := by
  intro r
  obtain ⟨v, hv⟩ := tameSigmaColumn_surjective_of_fixedPointFree t hτfpf (r 0)
  let x : Generator (2 + 2 * h) → A := fun g ↦
    if g = .sigma then v
    else if g = coreLetter h 2 then -(t.σ • r 1) else 0
  refine ⟨x, ?_⟩
  rw [heisD1_nCompactFam_ramified_apply t hA₂ ht hwild hτfpf hTodd hα]
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
    have hx2 : x (coreLetter h 2) = -(t.σ • r 1) := by
      simp [x, hσx2.symm]
    rw [hx2, smul_neg, inv_smul_smul, neg_neg]

/-! ## The ramified second-order row on normal offsets

Every existing compact-`N` second-order row assumes `τ` acts trivially.  The following one does
not: it assumes instead that the offsets vanish on `τ` and on `x₂`, which is exactly the
condition satisfied by the normal representatives.  Under it the two `τ`-carrying factors are
second-order trivial, so the row is the `x₀`-diagonal, the `(x₀,x₁)`-cross and the handle
planes, with no ramification-class hypothesis whatever.
-/

set_option maxHeartbeats 800000 in
/-- **The compact-`N` second-order row on normal offsets.**  No hypothesis on `τ`: the
`(x₂τ)^{ω₂}` factor is second-order trivial once the offsets vanish on `τ` and `x₂`. -/
theorem heisZ_nCompact_normalOffsets
    {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hα : 2 ≤ α)
    (hxτ : x .tau = 0) (hx2 : x (coreLetter h 2) = 0)
    (hyτ : y .tau = 0) (hy2 : y (coreLetter h 2) = 0) :
    (heisEvalZ ⇑t x y E E₂ (nCompactW α h)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 0) (x (coreLetter h 1)) + y (coreLetter h 1) (x (coreLetter h 0)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have e1 := Certificates.heisF_leadingPow t x y E E₂ hA₂ hwild hα
  have e2 := Certificates.heisF_leadingComm t x y E E₂ hwild
  have e3 := Certificates.heisF_invConjX2 t x y E E₂ hwild
  have e5mem := Certificates.heisF_handlesW_mem t x y E E₂ hwild
  have e5z := Certificates.heisF_handlesW_z t x y E E₂ hwild
  have hinner : heisEvalZ ⇑t x y E E₂
      (PWord.prodList [.gen (coreLetter h 2), .gen .tau])
        ∈ Certificates.MCompact.heisTrivial A C := by
    rw [Certificates.heisF_deltaInner t x y E E₂ hwild]
    refine ⟨?_, ?_, ?_⟩
    · show x (coreLetter h 2) + x .tau = 0
      rw [hx2, hxτ, add_zero]
    · show y (coreLetter h 2) + y .tau = 0
      rw [hy2, hyτ, add_zero]
    · show y (coreLetter h 2) (x .tau) = 0
      rw [hy2]; rfl
  have e4 : heisEvalZ ⇑t x y E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))
        ∈ Certificates.MCompact.heisTrivial A C := by
    rw [PWord.omega2Pow, heisEvalZ_profPow]
    exact zpow_mem hinner _
  have h1jz : heisEvalZ ⇑t x y E E₂ (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α))
      ∈ heisJetZero A C := by rw [e1]; exact ⟨rfl, rfl⟩
  have h2jz : heisEvalZ ⇑t x y E E₂ (.comm (.gen (coreLetter h 0)) (.gen (coreLetter h 1)))
      ∈ heisJetZero A C := by rw [e2]; exact ⟨rfl, rfl⟩
  have h3jz : heisEvalZ ⇑t x y E E₂ (.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)))
      ∈ heisJetZero A C := by
    rw [e3]
    exact ⟨by show -(t.σ⁻¹ • x (coreLetter h 2)) = 0; rw [hx2, smul_zero, neg_zero],
      by show -(t.σ⁻¹ • y (coreLetter h 2)) = 0; rw [hy2, smul_zero, neg_zero]⟩
  have hmem : ∀ w ∈ ([.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α),
      .comm (.gen (coreLetter h 0)) (.gen (coreLetter h 1)),
      .inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)),
      PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]),
      handlesW h] : List (PWord (Generator (2 + 2 * h)))),
      heisEvalZ ⇑t x y E E₂ w ∈ heisJetZero A C := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact h1jz
    · exact h2jz
    · exact h3jz
    · exact ⟨e4.1, e4.2.1⟩
    · exact e5mem
  rw [nCompactW, (heisEvalZ_prodList_jetZero ⇑t x y E E₂ hmem).2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [e1, e2, e3, e4.2.2, e5z, hx2, hy2]
  simp only [ElemDual.zero_apply, map_zero, add_zero, zero_add]
  abel

/-! ## The middle pairing on normal coordinates -/

/-- Every ramified normal cochain is a compact-`N` cocycle. -/
theorem heisD1_evenNormal_eq_zero
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a) (hα : 1 ≤ α)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    heisD1 ⇑t (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
        (evenNormal h d₀ d₁ z) = 0 := by
  rw [heisD1_nCompactFam_ramified_apply t hA₂ ht hwild hτfpf hTodd hα]
  funext k
  fin_cases k <;> simp

set_option maxHeartbeats 800000 in
/-- On normal coordinates the compact-`N` middle Stokes map is the constant unimodular core
matrix `((1,1),(1,0))` plus `h` standard hyperbolic planes. -/
theorem heisEta1_nCompactFam_normal
    {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) (hα : 2 ≤ α)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₀ lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A) {e : ℕ} :
    heisEta1 ⇑t (nCompactFam α h q e) (evenNormal h d₀ d₁ z) (evenNormal h lam₀ lam₁ mu)
      = lam₀ (d₀ + d₁) + lam₁ d₀
        + ∑ j, (mu (j, 0) (z (j, 1)) + mu (j, 1) (z (j, 0))) := by
  have htame : (heisEvalZ ⇑t (evenNormal h d₀ d₁ z) (evenNormal h lam₀ lam₁ mu)
      (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ)) (tameRelW (2 + 2 * h) q)).z = 0 := by
    apply heisZ_tameRelW_eq_zero_of_tame_offsets_zero <;> simp
  rw [Certificates.heisEta1_nCompactFam_apply t _ _, htame, zero_add,
    heisZ_nCompact_normalOffsets t _ _ _ _ hA₂ hwild hα (by simp) (by simp) (by simp) (by simp)]
  simp only [evenNormal_coreLetter, evenNormal_handleU, evenNormal_handleV,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_add]
  abel

/-- The normal-coordinate pairing separates every nonzero primal coordinate. -/
theorem nCompactFam_normal_pairing_separates_left
    {C A : Type*} [Group C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) (hα : 2 ≤ α)
    (p : A × A × (Fin h × Fin 2 → A)) (hp : p ≠ 0) {e : ℕ} :
    ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
      heisEta1 ⇑t (nCompactFam α h q e)
          (evenNormal h p.1 p.2.1 p.2.2) (evenNormal h r.1 r.2.1 r.2.2) ≠ 0 := by
  classical
  by_cases hd₀ : p.1 = 0
  · by_cases hd₁ : p.2.1 = 0
    · have hz : p.2.2 ≠ 0 := by
        intro hz
        exact hp (Prod.ext hd₀ (Prod.ext hd₁ (by simpa using hz)))
      obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.mp hz
      obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hjk
      fin_cases k
      · refine ⟨(0, 0, Pi.single (j, 1) lam), ?_⟩
        rw [heisEta1_nCompactFam_normal t hA₂ hwild hα, hd₀, hd₁]
        have hsum : ∑ b, ((Pi.single (j, 1) lam : Fin h × Fin 2 → ElemDual A) (b, 0)
              (p.2.2 (b, 1))
            + (Pi.single (j, 1) lam : Fin h × Fin 2 → ElemDual A) (b, 1) (p.2.2 (b, 0)))
            = lam (p.2.2 (j, 0)) := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hbj
            simp [hbj]
          · simp
        rw [hsum]
        simpa using hlam
      · refine ⟨(0, 0, Pi.single (j, 0) lam), ?_⟩
        rw [heisEta1_nCompactFam_normal t hA₂ hwild hα, hd₀, hd₁]
        have hsum : ∑ b, ((Pi.single (j, 0) lam : Fin h × Fin 2 → ElemDual A) (b, 0)
              (p.2.2 (b, 1))
            + (Pi.single (j, 0) lam : Fin h × Fin 2 → ElemDual A) (b, 1) (p.2.2 (b, 0)))
            = lam (p.2.2 (j, 1)) := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hbj
            simp [hbj]
          · simp
        rw [hsum]
        simpa using hlam
    · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hd₁
      refine ⟨(lam, 0, 0), ?_⟩
      rw [heisEta1_nCompactFam_normal t hA₂ hwild hα, hd₀]
      simpa using hlam
  · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ hd₀
    refine ⟨(0, lam, 0), ?_⟩
    rw [heisEta1_nCompactFam_normal t hA₂ hwild hα]
    simpa using hlam

/-- The normal-coordinate pairing separates every nonzero dual coordinate. -/
theorem nCompactFam_normal_pairing_separates_right
    {C A : Type*} [Group C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) (hα : 2 ≤ α)
    (r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A)) (hr : r ≠ 0) {e : ℕ} :
    ∃ p : A × A × (Fin h × Fin 2 → A),
      heisEta1 ⇑t (nCompactFam α h q e)
          (evenNormal h p.1 p.2.1 p.2.2) (evenNormal h r.1 r.2.1 r.2.2) ≠ 0 := by
  classical
  by_cases hlam₀ : r.1 = 0
  · by_cases hlam₁ : r.2.1 = 0
    · have hmu : r.2.2 ≠ 0 := by
        intro hmu
        exact hr (Prod.ext hlam₀ (Prod.ext hlam₁ (by simpa using hmu)))
      obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.mp hmu
      obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hjk
      fin_cases k
      · refine ⟨(0, 0, Pi.single (j, 1) a), ?_⟩
        rw [heisEta1_nCompactFam_normal t hA₂ hwild hα, hlam₀, hlam₁]
        have hsum : ∑ b, (r.2.2 (b, 0) ((Pi.single (j, 1) a : Fin h × Fin 2 → A) (b, 1))
            + r.2.2 (b, 1) ((Pi.single (j, 1) a : Fin h × Fin 2 → A) (b, 0)))
            = r.2.2 (j, 0) a := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hbj
            simp [hbj]
          · simp
        rw [hsum]
        simpa using ha
      · refine ⟨(0, 0, Pi.single (j, 0) a), ?_⟩
        rw [heisEta1_nCompactFam_normal t hA₂ hwild hα, hlam₀, hlam₁]
        have hsum : ∑ b, (r.2.2 (b, 0) ((Pi.single (j, 0) a : Fin h × Fin 2 → A) (b, 1))
            + r.2.2 (b, 1) ((Pi.single (j, 0) a : Fin h × Fin 2 → A) (b, 0)))
            = r.2.2 (j, 1) a := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hbj
            simp [hbj]
          · simp
        rw [hsum]
        simpa using ha
    · obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hlam₁
      refine ⟨(a, 0, 0), ?_⟩
      rw [heisEta1_nCompactFam_normal t hA₂ hwild hα, hlam₀]
      simpa using ha
  · obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hlam₀
    refine ⟨(0, a, 0), ?_⟩
    rw [heisEta1_nCompactFam_normal t hA₂ hwild hα]
    simpa using ha

/-! ## The ramified normal form -/

set_option maxHeartbeats 1600000 in
/-- Every ramified degree-one cocycle of the compact-`N` complex has a unique normal
representative: the wild row kills `x₂`, a coboundary kills `tau`, and the `q`-independent tame
pivot then kills `sigma`, leaving the two core coordinates `x₀, x₁` and the `h` handle pairs. -/
theorem nCompactFam_ramified_normalForm
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a) (hα : 1 ≤ α)
    (hr : ∀ k, FreeGroup.lift ⇑t
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C)) k) = 1) :
    ∀ x, heisD1 ⇑t (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) x = 0 →
      ∃! p : A × A × (Fin h × Fin 2 → A),
        x - evenNormal h p.1 p.2.1 p.2.2 ∈ Set.range (heisD0 ⇑t) := by
  have hTsurj : Function.Surjective (fun v : A ↦ t.τ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hτfpf
  have hcoreTriv : ∀ (i : Fin 3) (a : A), t (coreLetter h i) • a = a := fun i a ↦ hwild _ a
  have hhandleUTriv : ∀ (j : Fin h) (a : A), t (handleU j) • a = a := fun j a ↦ hwild _ a
  have hhandleVTriv : ∀ (j : Fin h) (a : A), t (handleV j) • a = a := fun j a ↦ hwild _ a
  intro x hx
  have hxcore2 : x (coreLetter h 2) = 0 := by
    have hz := congrFun hx 1
    rw [heisD1_nCompactFam_ramified_apply t hA₂ ht hwild hτfpf hTodd hα] at hz
    have hz' : t.σ⁻¹ • x (coreLetter h 2) = 0 := by
      have hh : -(t.σ⁻¹ • x (coreLetter h 2)) = (0 : A) := by
        simpa using hz
      rwa [neg_eq_zero] at hh
    rw [← smul_inv_smul t.σ (x (coreLetter h 2)), hz', smul_zero]
  obtain ⟨v, hv⟩ := hTsurj (x .tau)
  let x' := x - heisD0 (⇑t) v
  have hx' : heisD1 (⇑t) (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) x' = 0 := by
    change heisD1 (⇑t) _ (x - heisD0 (⇑t) v) = 0
    rw [map_sub, hx, heisD1_comp_heisD0 (⇑t) _ hr v, sub_zero]
  have hx'τ : x' .tau = 0 := by
    simp [x', heisD0_apply, hv]
  have hx'core2 : x' (coreLetter h 2) = 0 := by
    simp [x', heisD0_apply, hcoreTriv, hxcore2]
  have hx'σ : x' .sigma = 0 := by
    have hz := congrFun hx' 0
    rw [heisD1_nCompactFam_ramified_apply t hA₂ ht hwild hτfpf hTodd hα] at hz
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

/-! ## Stokes assembly -/

set_option maxHeartbeats 3200000 in
/-- **Ramified Stokes duality for the uniform compact-`N` presentation.**

The hypotheses are exactly the ramified action facts supplied by simplicity of the coefficient
module, plus `α ≥ 2` (the binomial `C(2 + 2^α, 2)` must be odd for the `x₀`-diagonal to survive)
and relator death at the uniform resolver.  The tame exponent stays `q`-parametric. -/
theorem nCompactStokesDuality_ramified
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (hq : Even q) (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a) (hα : 2 ≤ α)
    (hN : PWord.evalZ ⇑t
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ)) (nCompactW α h) = 1) :
    StokesDuality ⇑t (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) A := by
  classical
  let e := omega2Exp (4 * Monoid.exponent C)
  let w := nCompactFam α h q e
  have hr : ∀ k, FreeGroup.lift (⇑t) (w k) = 1 := by
    intro k
    fin_cases k
    · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr
        (evalZ_tameRelW_eq_one_of_tameRelAt t _ _ ht)
    · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hN
  have he : Odd e := odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
  have hend : IsStokesEndpoint w :=
    Certificates.nCompact_isStokesEndpoint (by omega) hq he
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  have hToddD : ∀ lam : ElemDual A, powOmega2 t.τ • lam = lam :=
    fun lam ↦ elemDual_smul_eq_self hTodd lam
  have hd₀A := heisD0_injective_of_tau_fixedPointFree t hτfpf
  have hd₀D := heisD0_injective_of_tau_fixedPointFree (A := ElemDual A) t hτfpfD
  have hd₁A : Function.Surjective (heisD1 (A := A) (⇑t) w) :=
    heisD1_nCompactFam_surjective_ramified t hA₂ ht hwild hτfpf hTodd (by omega)
  have hd₁D : Function.Surjective (heisD1 (A := ElemDual A) (⇑t) w) :=
    heisD1_nCompactFam_surjective_ramified t hA₂D ht hwildD hτfpfD hToddD (by omega)
  have hnfA := nCompactFam_ramified_normalForm t hA₂ ht hwild hτfpf hTodd (by omega) hr
  have hnfD := nCompactFam_ramified_normalForm (A := ElemDual A) t hA₂D ht hwildD hτfpfD
    hToddD (by omega) hr
  have hmemA : ∀ p : A × A × (Fin h × Fin 2 → A),
      heisD1 (⇑t) w (evenNormal h p.1 p.2.1 p.2.2) = 0 :=
    fun p ↦ heisD1_evenNormal_eq_zero t hA₂ ht hwild hτfpf hTodd (by omega) p.1 p.2.1 p.2.2
  have hmemD : ∀ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
      heisD1 (⇑t) w (evenNormal h r.1 r.2.1 r.2.2) = 0 :=
    fun r ↦ heisD1_evenNormal_eq_zero t hA₂D ht hwildD hτfpfD hToddD (by omega) r.1 r.2.1 r.2.2
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
        simp only [Prod.fst_zero, Prod.snd_zero, evenNormal_zero, sub_zero] at hp
        exact (stokesH1Mk_eq_zero_iff
          (heisD0 (A := A) (⇑t)) (heisD1 (⇑t) w) x).mpr hp
      · obtain ⟨r, hpair⟩ :=
          nCompactFam_normal_pairing_separates_left (q := q) (e := e)
            t hA₂ hwild hα p hp0
        let y := evenNormal h r.1 r.2.1 r.2.2
        have hy : heisD1 (A := ElemDual A) (⇑t) w y = 0 := hmemD r
        rw [stokesH1Mk, stokesH1Map, QuotientAddGroup.map_mk,
          QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hH
        obtain ⟨xi, hxi⟩ := AddMonoidHom.mem_range.mp hH
        have hvan : heisEta1 (⇑t) w x.val y = 0 := by
          have heq := DFunLike.congr_fun hxi y
          rw [dualMap_apply, hy, map_zero] at heq
          exact heq.symm
        obtain ⟨v, hv⟩ := hp
        have hxrepr : x.val = evenNormal h p.1 p.2.1 p.2.2 + heisD0 (⇑t) v := by
          rw [hv]
          abel
        have hsame : heisEta1 (⇑t) w x.val y =
            heisEta1 (⇑t) w (evenNormal h p.1 p.2.1 p.2.2) y := by
          rw [hxrepr, map_add]
          change heisEta1 (⇑t) w (evenNormal h p.1 p.2.1 p.2.2) y +
            heisEta1 (⇑t) w (heisD0 (⇑t) v) y =
              heisEta1 (⇑t) w (evenNormal h p.1 p.2.1 p.2.2) y
          rw [heisEta1_comp_d0 (⇑t) w hr hend v y, hy, map_zero]
          simp
        exact (hpair (hsame ▸ hvan)).elim
    have hcardA : Nat.card (StokesH1 (heisD0 (A := A) (⇑t)) (heisD1 (⇑t) w)) =
        Nat.card (A × A × (Fin h × Fin 2 → A)) :=
      card_stokesH1_of_normalForm _ _
        (fun p : A × A × (Fin h × Fin 2 → A) ↦ evenNormal h p.1 p.2.1 p.2.2)
        hmemA hnfA
    have hcardD : Nat.card
        (StokesH1 (heisD0 (A := ElemDual A) (⇑t))
          (heisD1 (A := ElemDual A) (⇑t) w)) =
        Nat.card (ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A)) :=
      card_stokesH1_of_normalForm _ _
        (fun r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A) ↦
          evenNormal h r.1 r.2.1 r.2.2) hmemD hnfD
    have hcoordCard : Nat.card (A × A × (Fin h × Fin 2 → A)) =
        Nat.card (ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A)) := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
        Nat.card_fun, Nat.card_fun, card_elemDual hA₂]
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
