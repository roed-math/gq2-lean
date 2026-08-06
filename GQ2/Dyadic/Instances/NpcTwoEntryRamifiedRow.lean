/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenTwistedNormalStokes

/-!
# The two-entry ramified row on the even alphabet

The two compact even rows have the *one*-entry ramified wild row `−S⁻¹·a(x₂)`, so their ramified
cocycles are the `x₂`-free cochains `evenNormal`.  Both procyclic rows have a **two**-entry
ramified wild row: for the corrected procyclic-`N` word
(`Certificates.NProcyclic.foxD_npc_ram`)

```
D(R_{N,α,r,η}) = (A⁻¹ − 1)·a(x₀) − B⁻¹·a(x₂),   A = S^{E(η̂)},  B = S^{2^r},
```

and the procyclic-`M` dictionary is triangular in the same way.  So the `x₂`-coordinate of a
cocycle is not zero but the *twist* `B(A⁻¹ − 1)·x₀` of the free `x₀`-coordinate.

This file records that lane once, word-independently, in the shape both procyclic rows need:

* `evenTwistedNormal h g u` — the normal cochain with `x₂ = u⁻¹·(g·x₀ − x₀)`, reducing to
  `evenNormal` exactly when `g` acts trivially;
* surjectivity of a differential with the two-entry row (the `x₂`-column is still a pivot,
  because `u` acts invertibly);
* the twisted normal form, and the fact that twisted normal cochains are cocycles;
* the assembled Stokes-duality statement, whose only remaining input is left nondegeneracy of the
  traced pairing on the twisted coordinates.

Everything is stated for arbitrary `g u : C`, so the arithmetic of `E(η̂)` and `2^r` never
enters; only the *shape* of the row does.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic

variable {h q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A] [DistribMulAction C A]

/-! ## The twisted normal cochains -/

/-- **The twisted ramified normal cochain**: the core is supported on `x₀`, `x₁` and the
determined coordinate `x₂ = u⁻¹·(g·x₀ − x₀)`, while the handle coordinates are free. -/
def evenTwistedNormal (h : ℕ) {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (g u : C) (d₀ d₁ : A) (z : Fin h × Fin 2 → A) : Generator (2 + 2 * h) → A :=
  (EvenCore.coreHandleAddEquiv h A).symm
    (evenCoreOffsets ![d₀, d₁, u⁻¹ • (g • d₀ - d₀)], z)

variable (g u : C)

omit [Finite A] in
@[simp] theorem evenTwistedNormal_core (h : ℕ) (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    EvenCore.coreRestrict h A (evenTwistedNormal h g u d₀ d₁ z)
      = evenCoreOffsets ![d₀, d₁, u⁻¹ • (g • d₀ - d₀)] := by
  rw [← EvenCore.coreHandleAddEquiv_fst]
  simp [evenTwistedNormal]

omit [Finite A] in
@[simp] theorem evenTwistedNormal_sigma (h : ℕ) (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    evenTwistedNormal h g u d₀ d₁ z .sigma = 0 :=
  congrFun (evenTwistedNormal_core g u h d₀ d₁ z) Generator.sigma

omit [Finite A] in
@[simp] theorem evenTwistedNormal_tau (h : ℕ) (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    evenTwistedNormal h g u d₀ d₁ z .tau = 0 :=
  congrFun (evenTwistedNormal_core g u h d₀ d₁ z) Generator.tau

omit [Finite A] in
@[simp] theorem evenTwistedNormal_coreLetter (h : ℕ) (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (i : Fin 3) :
    evenTwistedNormal h g u d₀ d₁ z (coreLetter h i) = ![d₀, d₁, u⁻¹ • (g • d₀ - d₀)] i :=
  congrFun (evenTwistedNormal_core g u h d₀ d₁ z) (Generator.wild i)

omit [Finite A] in
@[simp] theorem evenTwistedNormal_handleU {h : ℕ} (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (j : Fin h) : evenTwistedNormal h g u d₀ d₁ z (handleU j) = z (j, 0) := by
  have hh := congrArg (fun p : (Generator 2 → A) × (Fin h × Fin 2 → A) ↦ p.2 (j, 0))
    ((EvenCore.coreHandleAddEquiv h A).apply_symm_apply
      (evenCoreOffsets ![d₀, d₁, u⁻¹ • (g • d₀ - d₀)], z))
  change ((EvenCore.coreHandleAddEquiv h A) (evenTwistedNormal h g u d₀ d₁ z)).2 (j, 0)
    = z (j, 0) at hh
  rw [EvenCore.coreHandleAddEquiv_snd_zero] at hh
  exact hh

omit [Finite A] in
@[simp] theorem evenTwistedNormal_handleV {h : ℕ} (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (j : Fin h) : evenTwistedNormal h g u d₀ d₁ z (handleV j) = z (j, 1) := by
  have hh := congrArg (fun p : (Generator 2 → A) × (Fin h × Fin 2 → A) ↦ p.2 (j, 1))
    ((EvenCore.coreHandleAddEquiv h A).apply_symm_apply
      (evenCoreOffsets ![d₀, d₁, u⁻¹ • (g • d₀ - d₀)], z))
  change ((EvenCore.coreHandleAddEquiv h A) (evenTwistedNormal h g u d₀ d₁ z)).2 (j, 1)
    = z (j, 1) at hh
  rw [EvenCore.coreHandleAddEquiv_snd_one] at hh
  exact hh

omit [Finite A] in
@[simp] theorem evenTwistedNormal_zero (h : ℕ) :
    evenTwistedNormal h g u (0 : A) (0 : A) (0 : Fin h × Fin 2 → A) = 0 := by
  have hx : (![(0 : A), 0, u⁻¹ • (g • (0 : A) - 0)] : Fin 3 → A) = 0 := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · show u⁻¹ • (g • (0 : A) - 0) = 0
      rw [smul_zero, sub_zero, smul_zero]
  rw [evenTwistedNormal, hx, evenCoreOffsets_zero]
  exact (EvenCore.coreHandleAddEquiv h A).symm.map_zero

/-! ## The two-entry ramified row -/

/-- The shape of a two-entry ramified differential: the arbitrary-`q` tame row, and a wild row
with an `x₀`-coboundary entry and an invertible `x₂`-pivot. -/
def IsTwoEntryRamifiedRow (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (q : ℕ) (g u : C)
    (A : Type*) [AddCommGroup A] [DistribMulAction C A] : Prop :=
  ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
    = ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
        (g • x (coreLetter h 0) - x (coreLetter h 0)) - u • x (coreLetter h 2)]

/-- Surjectivity of a differential with the two-entry ramified row: the tame row pivots on
`sigma` and the wild row pivots independently on `x₂`, because `u` acts invertibly. -/
theorem heisD1_surjective_of_twoEntry_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : IsTwoEntryRamifiedRow t w q g u A)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0) :
    Function.Surjective (heisD1 (A := A) ⇑t w) := by
  classical
  intro r
  obtain ⟨v, hv⟩ := tameSigmaColumn_surjective_of_fixedPointFree t hτfpf (r 0)
  let x : Generator (2 + 2 * h) → A := fun gg ↦
    if gg = .sigma then v
    else if gg = coreLetter h 2 then -(u⁻¹ • r 1) else 0
  refine ⟨x, ?_⟩
  rw [hrow x]
  funext k
  have hσx2 : (.sigma : Generator (2 + 2 * h)) ≠ coreLetter h 2 :=
    Certificates.sigma_ne_coreLetter_two h
  have hτσ : (.tau : Generator (2 + 2 * h)) ≠ .sigma := by simp
  have hτx2 : (.tau : Generator (2 + 2 * h)) ≠ coreLetter h 2 :=
    Certificates.tau_ne_coreLetter_two h
  have hx0σ : coreLetter h 0 ≠ (.sigma : Generator (2 + 2 * h)) := by
    simp [coreLetter]
  have hx0x2 : coreLetter h 0 ≠ coreLetter h 2 := by
    simp [coreLetter, Fin.ext_iff]
  fin_cases k
  · change t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
        - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau = r 0
    simp only [x, if_pos, if_neg hτσ, if_neg hτx2,
      zero_add, smul_zero, Finset.sum_const_zero, sub_zero]
    exact hv
  · change (g • x (coreLetter h 0) - x (coreLetter h 0)) - u • x (coreLetter h 2) = r 1
    have hx0 : x (coreLetter h 0) = 0 := by simp [x, hx0σ, hx0x2]
    have hx2 : x (coreLetter h 2) = -(u⁻¹ • r 1) := by simp [x, hσx2.symm]
    rw [hx0, hx2, smul_zero, sub_zero, zero_sub, smul_neg, smul_inv_smul, neg_neg]

omit [Finite A] in
/-- Every twisted normal cochain is a cocycle for the two-entry ramified row. -/
theorem heisD1_evenTwistedNormal_eq_zero
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : IsTwoEntryRamifiedRow t w q g u A)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    heisD1 ⇑t w (evenTwistedNormal h g u d₀ d₁ z) = 0 := by
  rw [hrow]
  funext k
  fin_cases k
  · simp
  · change (g • (evenTwistedNormal h g u d₀ d₁ z) (coreLetter h 0)
        - (evenTwistedNormal h g u d₀ d₁ z) (coreLetter h 0))
      - u • (evenTwistedNormal h g u d₀ d₁ z) (coreLetter h 2) = 0
    rw [evenTwistedNormal_coreLetter, evenTwistedNormal_coreLetter]
    show (g • d₀ - d₀) - u • (u⁻¹ • (g • d₀ - d₀)) = 0
    rw [smul_inv_smul, sub_self]

set_option maxHeartbeats 1600000 in
/-- **The twisted ramified normal form.**  A coboundary kills `tau`, the `q`-independent tame
pivot then kills `sigma`, and the wild row determines `x₂` from `x₀`, leaving the free
coordinates `x₀`, `x₁` and the `h` handle pairs. -/
theorem evenTwistedNormalForm_of_twoEntry_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : IsTwoEntryRamifiedRow t w q g u A)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 → ∃! p : A × A × (Fin h × Fin 2 → A),
      x - evenTwistedNormal h g u p.1 p.2.1 p.2.2 ∈ Set.range (heisD0 ⇑t) := by
  have hTsurj : Function.Surjective (fun v : A ↦ t.τ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hτfpf
  have hcoreTriv : ∀ (i : Fin 3) (a : A), t (coreLetter h i) • a = a := fun i a ↦ hwild _ a
  have hhandleUTriv : ∀ (j : Fin h) (a : A), t (handleU j) • a = a := fun j a ↦ hwild _ a
  have hhandleVTriv : ∀ (j : Fin h) (a : A), t (handleV j) • a = a := fun j a ↦ hwild _ a
  intro x hx
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
  have hx'core2 : x' (coreLetter h 2) = u⁻¹ • (g • x' (coreLetter h 0) - x' (coreLetter h 0)) := by
    have hz := congrFun hx' 1
    rw [hrow x'] at hz
    have hz' : (g • x' (coreLetter h 0) - x' (coreLetter h 0))
        - u • x' (coreLetter h 2) = 0 := by simpa using hz
    have hz'' : u • x' (coreLetter h 2) = g • x' (coreLetter h 0) - x' (coreLetter h 0) :=
      (sub_eq_zero.mp hz').symm
    rw [← hz'', inv_smul_smul]
  let z := (EvenCore.coreHandleAddEquiv h A x).2
  let p₀ : A × A × (Fin h × Fin 2 → A) := (x (coreLetter h 0), x (coreLetter h 1), z)
  have hcore0 : x' (coreLetter h 0) = x (coreLetter h 0) := by
    simp [x', heisD0_apply, hcoreTriv]
  have hnormal : evenTwistedNormal h g u p₀.1 p₀.2.1 p₀.2.2 = x' := by
    apply (EvenCore.coreHandleAddEquiv h A).injective
    apply Prod.ext
    · funext gg
      cases gg with
      | sigma => simpa [p₀] using hx'σ.symm
      | tau => simpa [p₀] using hx'τ.symm
      | wild i =>
          fin_cases i
          · simp [p₀, x', heisD0_apply, hcoreTriv]
          · simp [p₀, x', heisD0_apply, hcoreTriv]
          · rw [EvenCore.coreHandleAddEquiv_fst]
            show ![p₀.1, p₀.2.1, u⁻¹ • (g • p₀.1 - p₀.1)] 2 = x' (coreLetter h 2)
            rw [hx'core2, hcore0]
            rfl
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
    obtain ⟨uu, hu⟩ := hp
    apply Prod.ext
    · have hc := congrFun hu (coreLetter h 0)
      rw [heisD0_apply, hcoreTriv, sub_self] at hc
      simp only [Pi.sub_apply, evenTwistedNormal_coreLetter, Matrix.cons_val_zero] at hc
      exact (sub_eq_zero.mp hc.symm).symm
    · apply Prod.ext
      · have hc := congrFun hu (coreLetter h 1)
        rw [heisD0_apply, hcoreTriv, sub_self] at hc
        simp only [Pi.sub_apply, evenTwistedNormal_coreLetter, Matrix.cons_val_one,
          Matrix.cons_val_zero] at hc
        exact (sub_eq_zero.mp hc.symm).symm
      · funext jk
        rcases jk with ⟨j, k⟩
        fin_cases k
        · have hc := congrFun hu (handleU j)
          rw [heisD0_apply, hhandleUTriv, sub_self] at hc
          simp only [Pi.sub_apply, evenTwistedNormal_handleU] at hc
          have hpj := (sub_eq_zero.mp hc.symm).symm
          simpa [p₀, z] using hpj
        · have hc := congrFun hu (handleV j)
          rw [heisD0_apply, hhandleVTriv, sub_self] at hc
          simp only [Pi.sub_apply, evenTwistedNormal_handleV] at hc
          have hpj := (sub_eq_zero.mp hc.symm).symm
          simpa [p₀, z] using hpj

set_option maxHeartbeats 3200000 in
/-- **Stokes duality for a two-entry ramified even row.**  Every first-order ingredient is
discharged from the row shape alone; the only remaining input is left nondegeneracy of the traced
pairing on the twisted normal coordinates. -/
theorem evenTwoEntryRamifiedStokesDuality_of_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) (hend : IsStokesEndpoint w)
    (hrowA : IsTwoEntryRamifiedRow t w q g u A)
    (hrowD : IsTwoEntryRamifiedRow t w q g u (ElemDual A))
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hsep : ∀ p : A × A × (Fin h × Fin 2 → A), p ≠ 0 →
      ∃ r : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        heisEta1 ⇑t w (evenTwistedNormal h g u p.1 p.2.1 p.2.2)
          (evenTwistedNormal h g u r.1 r.2.1 r.2.2) ≠ 0) :
    StokesDuality ⇑t w A := by
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual A, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf lam hlam
  exact evenNormalStokesDuality_of_normalMap t w
    (fun p ↦ evenTwistedNormal h g u p.1 p.2.1 p.2.2)
    (fun r ↦ evenTwistedNormal h g u r.1 r.2.1 r.2.2)
    hA₂ hr hend (by simp [evenTwistedNormal_zero g u h])
    (heisD0_injective_of_tau_fixedPointFree t hτfpf)
    (heisD0_injective_of_tau_fixedPointFree (A := ElemDual A) t hτfpfD)
    (heisD1_surjective_of_twoEntry_row g u t w hrowA hτfpf)
    (heisD1_surjective_of_twoEntry_row g u t w hrowD hτfpfD)
    (fun p ↦ heisD1_evenTwistedNormal_eq_zero g u t w hrowA p.1 p.2.1 p.2.2)
    (fun r ↦ heisD1_evenTwistedNormal_eq_zero g u t w hrowD r.1 r.2.1 r.2.2)
    (evenTwistedNormalForm_of_twoEntry_row g u t w hrowA hwild hτfpf hr)
    (evenTwistedNormalForm_of_twoEntry_row g u t w hrowD hwildD hτfpfD hr)
    hsep

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.evenTwistedNormal_zero
#print axioms GQ2.Dyadic.heisD1_surjective_of_twoEntry_row
#print axioms GQ2.Dyadic.heisD1_evenTwistedNormal_eq_zero
#print axioms GQ2.Dyadic.evenTwistedNormalForm_of_twoEntry_row
#print axioms GQ2.Dyadic.evenTwoEntryRamifiedStokesDuality_of_row

end AxiomAudit
