/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairFox
import GQ2.Dyadic.Instances.EvenTwistedNormalStokes

/-!
# Normal coordinates for the all-rank ramified head-handle pair row

The ramified Fox row of the pair source is

`-a(V_j) + a(x₂) - sigma⁻¹ * a(x₂)`.

Thus `x₂` is a free coordinate and the selected `V_j` coordinate is determined by it.  This
file records that parametrisation, proves its first-order normal-form properties for an abstract
two-relator family with the displayed row, and packages the remaining Stokes input as a single
pairing-separation statement.  Every result is uniform in the rank and selected handle.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairSource

variable {h q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-! ## The displaced-head normal cochain -/

/-- Handle coordinates for the ramified pair normal form.  The selected `V` coordinate is
determined by the value stored in its coordinate slot. -/
def headHandlePairRamHandles (t : Marking (2 + 2 * h) C) (j : Fin h)
    (z : Fin h × Fin 2 → A) : Fin h × Fin 2 → A :=
  Function.update z (j, 1) (z (j, 1) - t.σ⁻¹ • z (j, 1))

/-- The ramified pair normal cochain.  The free slot `z(j,1)` is placed at `x₂`; its
selected `V_j` value is the displaced-head difference. -/
def headHandlePairRamNormal (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) : Generator (2 + 2 * h) → A :=
  (EvenCore.coreHandleAddEquiv h A).symm
    (evenCoreOffsets ![d₀, d₁, z (j, 1)], headHandlePairRamHandles t j z)

omit [Finite A] in
@[simp] theorem headHandlePairRamNormal_core
    (t : Marking (2 + 2 * h) C) (j : Fin h) (d₀ d₁ : A)
    (z : Fin h × Fin 2 → A) :
    EvenCore.coreRestrict h A (headHandlePairRamNormal t j d₀ d₁ z) =
      evenCoreOffsets ![d₀, d₁, z (j, 1)] := by
  rw [← EvenCore.coreHandleAddEquiv_fst]
  simp [headHandlePairRamNormal]

omit [Finite A] in
@[simp] theorem headHandlePairRamNormal_sigma
    (t : Marking (2 + 2 * h) C) (j : Fin h) (d₀ d₁ : A)
    (z : Fin h × Fin 2 → A) : headHandlePairRamNormal t j d₀ d₁ z .sigma = 0 :=
  congrFun (headHandlePairRamNormal_core t j d₀ d₁ z) Generator.sigma

omit [Finite A] in
@[simp] theorem headHandlePairRamNormal_tau
    (t : Marking (2 + 2 * h) C) (j : Fin h) (d₀ d₁ : A)
    (z : Fin h × Fin 2 → A) : headHandlePairRamNormal t j d₀ d₁ z .tau = 0 :=
  congrFun (headHandlePairRamNormal_core t j d₀ d₁ z) Generator.tau

omit [Finite A] in
@[simp] theorem headHandlePairRamNormal_coreLetter
    (t : Marking (2 + 2 * h) C) (j : Fin h) (d₀ d₁ : A)
    (z : Fin h × Fin 2 → A) (i : Fin 3) :
    headHandlePairRamNormal t j d₀ d₁ z (coreLetter h i) = ![d₀, d₁, z (j, 1)] i :=
  congrFun (headHandlePairRamNormal_core t j d₀ d₁ z) (Generator.wild i)

omit [Finite A] in
@[simp] theorem headHandlePairRamNormal_handleU
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (d₀ d₁ : A)
    (z : Fin h × Fin 2 → A) :
    headHandlePairRamNormal t j d₀ d₁ z (handleU k) = z (k, 0) := by
  have hh := congrArg
    (fun p : (Generator 2 → A) × (Fin h × Fin 2 → A) ↦ p.2 (k, 0))
    ((EvenCore.coreHandleAddEquiv h A).apply_symm_apply
      (evenCoreOffsets ![d₀, d₁, z (j, 1)], headHandlePairRamHandles t j z))
  change ((EvenCore.coreHandleAddEquiv h A) (headHandlePairRamNormal t j d₀ d₁ z)).2
    (k, 0) = headHandlePairRamHandles t j z (k, 0) at hh
  rw [EvenCore.coreHandleAddEquiv_snd_zero] at hh
  rw [hh, headHandlePairRamHandles, Function.update_of_ne]
  intro heq
  exact Fin.zero_ne_one (congrArg Prod.snd heq)

omit [Finite A] in
@[simp] theorem headHandlePairRamNormal_handleV_self
    (t : Marking (2 + 2 * h) C) (j : Fin h) (d₀ d₁ : A)
    (z : Fin h × Fin 2 → A) :
    headHandlePairRamNormal t j d₀ d₁ z (handleV j) =
      z (j, 1) - t.σ⁻¹ • z (j, 1) := by
  have hh := congrArg
    (fun p : (Generator 2 → A) × (Fin h × Fin 2 → A) ↦ p.2 (j, 1))
    ((EvenCore.coreHandleAddEquiv h A).apply_symm_apply
      (evenCoreOffsets ![d₀, d₁, z (j, 1)], headHandlePairRamHandles t j z))
  change ((EvenCore.coreHandleAddEquiv h A) (headHandlePairRamNormal t j d₀ d₁ z)).2
    (j, 1) = headHandlePairRamHandles t j z (j, 1) at hh
  rw [EvenCore.coreHandleAddEquiv_snd_one] at hh
  simpa [headHandlePairRamHandles] using hh

omit [Finite A] in
@[simp] theorem headHandlePairRamNormal_handleV_of_ne
    (t : Marking (2 + 2 * h) C) (j k : Fin h) (hkj : k ≠ j) (d₀ d₁ : A)
    (z : Fin h × Fin 2 → A) :
    headHandlePairRamNormal t j d₀ d₁ z (handleV k) = z (k, 1) := by
  have hh := congrArg
    (fun p : (Generator 2 → A) × (Fin h × Fin 2 → A) ↦ p.2 (k, 1))
    ((EvenCore.coreHandleAddEquiv h A).apply_symm_apply
      (evenCoreOffsets ![d₀, d₁, z (j, 1)], headHandlePairRamHandles t j z))
  change ((EvenCore.coreHandleAddEquiv h A) (headHandlePairRamNormal t j d₀ d₁ z)).2
    (k, 1) = headHandlePairRamHandles t j z (k, 1) at hh
  rw [EvenCore.coreHandleAddEquiv_snd_one] at hh
  rw [hh, headHandlePairRamHandles, Function.update_of_ne]
  intro heq
  exact hkj (congrArg Prod.fst heq)

omit [Finite A] in
@[simp] theorem headHandlePairRamNormal_zero
    (t : Marking (2 + 2 * h) C) (j : Fin h) :
    headHandlePairRamNormal t j (0 : A) 0 0 = 0 := by
  apply (EvenCore.coreHandleAddEquiv h A).injective
  apply Prod.ext
  · funext g
    cases g with
    | sigma => simp
    | tau => simp
    | wild i => fin_cases i <;> simp
  · funext jk
    rcases jk with ⟨k, l⟩
    fin_cases l
    · simp
    · by_cases hkj : k = j
      · subst k; simp
      · simp [headHandlePairRamNormal_handleV_of_ne, hkj]

/-! ## The abstract ramified pair row -/

/-- The two-relator first differential occurring after the head-handle pair exchange in the
ramified branch. -/
def IsHeadHandlePairRamRow (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (j : Fin h)
    (A : Type*) [AddCommGroup A] [DistribMulAction C A] : Prop :=
  ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x = ![
    t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
      - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
    -x (handleV j) + (x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2))]

/-- The raw pair source reflected through a chosen pair of exponent resolvers. -/
def headHandlePairRawFamily (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha h q : ℕ) (j : Fin h) : Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  fun l ↦ heisToFree E E₂ (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l)

/-- The concrete reflected raw pair family has the abstract ramified pair row. -/
theorem isHeadHandlePairRamRow_raw
    [Finite C] {alpha : ℕ} (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ)
    (j : Fin h) (hA₂ : ∀ a : A, a + a = 0) (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hres : ResolverLifts E (WordLift A C)) :
    IsHeadHandlePairRamRow (q := q) t (headHandlePairRawFamily E E₂ alpha h q j) j A := by
  intro x
  funext k
  fin_cases k
  · change (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree E E₂ (tameRelW (2 + 2 * h) q))).a = _
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hres,
      Certificates.foxD_tameRelW_of_tameRel t E E₂ ht]
    simp
  · change (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree E E₂ (headHandlePairCompactW alpha j))).a = _
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hres,
      foxD_headHandlePairCompactW_ram t x E E₂ alpha j hA₂ hwild hτfpf hTodd]
    simp

omit [Finite A] in
/-- Every displaced-head normal cochain is a cocycle for the ramified pair row. -/
theorem heisD1_headHandlePairRamNormal_eq_zero
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (j : Fin h) (hrow : IsHeadHandlePairRamRow (q := q) t w j A)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    heisD1 ⇑t w (headHandlePairRamNormal t j d₀ d₁ z) = 0 := by
  rw [hrow]
  funext k
  fin_cases k
  · simp
  · simp

/-- The ramified pair differential is onto: its two pivots are `sigma` in the tame row and the
selected `V` handle in the wild row. -/
theorem heisD1_surjective_of_headHandlePairRamRow
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (j : Fin h) (hrow : IsHeadHandlePairRamRow (q := q) t w j A)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0) :
    Function.Surjective (heisD1 (A := A) ⇑t w) := by
  classical
  intro r
  obtain ⟨v, hv⟩ := tameSigmaColumn_surjective_of_fixedPointFree t hτfpf (r 0)
  let x : Generator (2 + 2 * h) → A := fun g ↦
    if g = .sigma then v else if g = handleV j then -r 1 else 0
  have hσV : (.sigma : Generator (2 + 2 * h)) ≠ handleV j := by simp [handleV]
  have hτσ : (.tau : Generator (2 + 2 * h)) ≠ .sigma := by simp
  have hτV : (.tau : Generator (2 + 2 * h)) ≠ handleV j := by simp [handleV]
  have hx2σ : coreLetter h 2 ≠ (.sigma : Generator (2 + 2 * h)) := by simp [coreLetter]
  have hx2V : coreLetter h 2 ≠ handleV j :=
    (Certificates.handleV_ne_coreLetter j 2).symm
  refine ⟨x, ?_⟩
  rw [hrow x]
  funext k
  fin_cases k
  · change t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
        - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau = r 0
    simp only [x, if_pos, if_neg hτσ, if_neg hτV,
      zero_add, smul_zero, Finset.sum_const_zero, sub_zero]
    exact hv
  · change -x (handleV j) +
      (x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2)) = r 1
    simp [x, hσV.symm, hx2σ, hx2V]

/-- Every cocycle of a ramified pair row has a unique displaced-head normal representative. -/
theorem headHandlePairRamNormalForm_of_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (j : Fin h) (hrow : IsHeadHandlePairRamRow (q := q) t w j A)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 →
      ∃! p : A × A × (Fin h × Fin 2 → A),
        x - headHandlePairRamNormal t j p.1 p.2.1 p.2.2 ∈ Set.range (heisD0 ⇑t) := by
  have hTsurj : Function.Surjective (fun v : A ↦ t.τ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hτfpf
  have hcoreTriv : ∀ (i : Fin 3) (a : A), t (coreLetter h i) • a = a :=
    fun i a ↦ hwild _ a
  have hhandleUTriv : ∀ (k : Fin h) (a : A), t (handleU k) • a = a :=
    fun k a ↦ hwild _ a
  have hhandleVTriv : ∀ (k : Fin h) (a : A), t (handleV k) • a = a :=
    fun k a ↦ hwild _ a
  intro x hx
  have hxV : x (handleV j) =
      x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2) := by
    have hz := congrFun hx 1
    rw [hrow x] at hz
    have hd : (x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2))
        - x (handleV j) = 0 := by
      simpa [sub_eq_add_neg, add_comm] using hz
    exact (sub_eq_zero.mp hd).symm
  obtain ⟨v, hv⟩ := hTsurj (x .tau)
  let x' := x - heisD0 (⇑t) v
  have hx' : heisD1 (⇑t) w x' = 0 := by
    change heisD1 (⇑t) w (x - heisD0 (⇑t) v) = 0
    rw [map_sub, hx, heisD1_comp_heisD0 (⇑t) w hr v, sub_zero]
  have hx'τ : x' .tau = 0 := by
    simp [x', heisD0_apply, hv]
  have hx'σ : x' .sigma = 0 := by
    have hz := congrFun hx' 0
    rw [hrow x'] at hz
    have hz' : t.σ⁻¹ • (t.τ • x' .sigma - x' .sigma) = 0 := by
      simpa [hx'τ] using hz
    have hdiff : t.τ • x' .sigma - x' .sigma = 0 := by
      have hs := congrArg (t.σ • ·) hz'
      simpa using hs
    exact hτfpf _ (sub_eq_zero.mp hdiff)
  let z₀ := (EvenCore.coreHandleAddEquiv h A x).2
  let z := Function.update z₀ (j, 1) (x (coreLetter h 2))
  let p₀ : A × A × (Fin h × Fin 2 → A) :=
    (x (coreLetter h 0), x (coreLetter h 1), z)
  have hnormal : headHandlePairRamNormal t j p₀.1 p₀.2.1 p₀.2.2 = x' := by
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
          · rw [EvenCore.coreHandleAddEquiv_fst]
            show ![p₀.1, p₀.2.1, p₀.2.2 (j, 1)] 2 = x' (coreLetter h 2)
            simp [p₀, z, x', heisD0_apply, hcoreTriv]
    · funext jk
      rcases jk with ⟨k, l⟩
      have hl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
      rcases hl with rfl | rfl
      · rw [EvenCore.coreHandleAddEquiv_snd_zero]
        simp [p₀, z, z₀, x', heisD0_apply, hhandleUTriv,
          headHandlePairRamNormal_handleU]
      · rw [EvenCore.coreHandleAddEquiv_snd_one]
        by_cases hkj : k = j
        · subst k
          simp [p₀, z, hxV, x', heisD0_apply, hhandleVTriv]
        · simp [headHandlePairRamNormal_handleV_of_ne, hkj, p₀, z, z₀, x',
            heisD0_apply, hhandleVTriv]
  refine ⟨p₀, ?_, ?_⟩
  · refine ⟨v, ?_⟩
    rw [hnormal]
    simp [x']
  · intro p hp
    obtain ⟨u, hu⟩ := hp
    apply Prod.ext
    · have hc := congrFun hu (coreLetter h 0)
      rw [heisD0_apply, hcoreTriv, sub_self] at hc
      simp only [Pi.sub_apply, headHandlePairRamNormal_coreLetter,
        Matrix.cons_val_zero] at hc
      exact (sub_eq_zero.mp hc.symm).symm
    · apply Prod.ext
      · have hc := congrFun hu (coreLetter h 1)
        rw [heisD0_apply, hcoreTriv, sub_self] at hc
        simp only [Pi.sub_apply, headHandlePairRamNormal_coreLetter,
          Matrix.cons_val_one, Matrix.cons_val_zero] at hc
        exact (sub_eq_zero.mp hc.symm).symm
      · funext jk
        rcases jk with ⟨k, l⟩
        fin_cases l
        · have hc := congrFun hu (handleU k)
          rw [heisD0_apply, hhandleUTriv, sub_self] at hc
          simp only [Pi.sub_apply, headHandlePairRamNormal_handleU] at hc
          have hpk := (sub_eq_zero.mp hc.symm).symm
          simpa [p₀, z, z₀] using hpk
        · by_cases hkj : k = j
          · subst k
            have hc := congrFun hu (coreLetter h 2)
            rw [heisD0_apply, hcoreTriv, sub_self] at hc
            simp only [Pi.sub_apply, headHandlePairRamNormal_coreLetter,
              Matrix.cons_val_two] at hc
            have hpj := (sub_eq_zero.mp hc.symm).symm
            simpa [p₀, z] using hpj
          · have hc := congrFun hu (handleV k)
            rw [heisD0_apply, hhandleVTriv, sub_self] at hc
            simp only [Pi.sub_apply,
              headHandlePairRamNormal_handleV_of_ne t j k hkj] at hc
            have hpk := (sub_eq_zero.mp hc.symm).symm
            simpa [p₀, z, z₀, hkj] using hpk

/-- Stokes duality for the ramified pair row reduces to separation of the traced pairing on the
displaced-head normal coordinates.  All first-order and end-complex inputs are discharged here. -/
theorem headHandlePairRamStokesDuality_of_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (j : Fin h) (hA₂ : ∀ a : A, a + a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) (hend : IsStokesEndpoint w)
    (hrowA : IsHeadHandlePairRamRow (q := q) t w j A)
    (hrowD : IsHeadHandlePairRamRow (q := q) t w j (ElemDual A))
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hsep : ∀ p : A × A × (Fin h × Fin 2 → A), p ≠ 0 →
      ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        heisEta1 ⇑t w (headHandlePairRamNormal t j p.1 p.2.1 p.2.2)
          (headHandlePairRamNormal t j r.1 r.2.1 r.2.2) ≠ 0) :
    StokesDuality ⇑t w A := by
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  exact evenNormalStokesDuality_of_normalMap t w
    (fun p ↦ headHandlePairRamNormal t j p.1 p.2.1 p.2.2)
    (fun r ↦ headHandlePairRamNormal t j r.1 r.2.1 r.2.2)
    hA₂ hr hend (by simp)
    (heisD0_injective_of_tau_fixedPointFree t hτfpf)
    (heisD0_injective_of_tau_fixedPointFree (A := ElemDual A) t hτfpfD)
    (heisD1_surjective_of_headHandlePairRamRow t w j hrowA hτfpf)
    (heisD1_surjective_of_headHandlePairRamRow (A := ElemDual A) t w j hrowD hτfpfD)
    (fun p ↦ heisD1_headHandlePairRamNormal_eq_zero t w j hrowA p.1 p.2.1 p.2.2)
    (fun r ↦ heisD1_headHandlePairRamNormal_eq_zero
      (A := ElemDual A) t w j hrowD r.1 r.2.1 r.2.2)
    (headHandlePairRamNormalForm_of_row t w j hrowA hwild hτfpf hr)
    (headHandlePairRamNormalForm_of_row
      (A := ElemDual A) t w j hrowD hwildD hτfpfD hr)
    hsep

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.headHandlePairRamNormal_zero
#print axioms GQ2.Dyadic.isHeadHandlePairRamRow_raw
#print axioms GQ2.Dyadic.heisD1_headHandlePairRamNormal_eq_zero
#print axioms GQ2.Dyadic.heisD1_surjective_of_headHandlePairRamRow
#print axioms GQ2.Dyadic.headHandlePairRamNormalForm_of_row
#print axioms GQ2.Dyadic.headHandlePairRamStokesDuality_of_row

end AxiomAudit
