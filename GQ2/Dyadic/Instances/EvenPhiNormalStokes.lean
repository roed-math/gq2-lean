/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.NpcTwoEntryRamifiedRow

/-!
# The operator-twisted normal form on the even alphabet

`NpcTwoEntryRamifiedRow` records the *ramified* two-entry lane, whose `x₂`-coordinate is
`u⁻¹·(g − 1)x₀` for two group elements `g, u`.  The procyclic-`N` **unramified** wild row

```
D(R_{N,α,r,η}) = (A⁻¹ − 1)·a(x₀) + a(τ) + (1 − B⁻¹)·a(x₂)
```

(`Certificates.Npc.foxD_npc_unram`) determines `x₂` from `x₀` too, but through
`(1 − B⁻¹)⁻¹(A⁻¹ − 1)`, whose first factor is *not* the action of a group element: on a simple
module the operator `1 − B⁻¹` is invertible but its inverse is only an additive endomorphism.

So this file records the same lane once more with the twist an arbitrary `Φ : A →+ A`
constrained only by the relation it must satisfy,

`Φ a − u·Φ a = g·a − a`,

which is exactly "`Φ` solves the cocycle equation".  Everything below is word-independent; only
the *shape* of the row enters.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic

variable {h q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A] [DistribMulAction C A]

/-! ## The operator-twisted normal cochains -/

/-- **The operator-twisted normal cochain**: the core is supported on `x₀`, `x₁` and the
determined coordinate `x₂ = Φ x₀`, while the handle coordinates are free. -/
def evenPhiNormal (h : ℕ) {A : Type*} [AddCommGroup A] (Φ : A →+ A) (d₀ d₁ : A)
    (z : Fin h × Fin 2 → A) : Generator (2 + 2 * h) → A :=
  (EvenCore.coreHandleAddEquiv h A).symm (evenCoreOffsets ![d₀, d₁, Φ d₀], z)

variable (Φ : A →+ A)

omit [Finite A] in
@[simp] theorem evenPhiNormal_core (h : ℕ) (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    EvenCore.coreRestrict h A (evenPhiNormal h Φ d₀ d₁ z)
      = evenCoreOffsets ![d₀, d₁, Φ d₀] := by
  rw [← EvenCore.coreHandleAddEquiv_fst]
  simp [evenPhiNormal]

omit [Finite A] in
@[simp] theorem evenPhiNormal_sigma (h : ℕ) (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    evenPhiNormal h Φ d₀ d₁ z .sigma = 0 :=
  congrFun (evenPhiNormal_core Φ h d₀ d₁ z) Generator.sigma

omit [Finite A] in
@[simp] theorem evenPhiNormal_tau (h : ℕ) (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    evenPhiNormal h Φ d₀ d₁ z .tau = 0 :=
  congrFun (evenPhiNormal_core Φ h d₀ d₁ z) Generator.tau

omit [Finite A] in
@[simp] theorem evenPhiNormal_coreLetter (h : ℕ) (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (i : Fin 3) :
    evenPhiNormal h Φ d₀ d₁ z (coreLetter h i) = ![d₀, d₁, Φ d₀] i :=
  congrFun (evenPhiNormal_core Φ h d₀ d₁ z) (Generator.wild i)

omit [Finite A] in
@[simp] theorem evenPhiNormal_handleU {h : ℕ} (d₀ d₁ : A) (z : Fin h × Fin 2 → A) (j : Fin h) :
    evenPhiNormal h Φ d₀ d₁ z (handleU j) = z (j, 0) := by
  have hh := congrArg (fun p : (Generator 2 → A) × (Fin h × Fin 2 → A) ↦ p.2 (j, 0))
    ((EvenCore.coreHandleAddEquiv h A).apply_symm_apply
      (evenCoreOffsets ![d₀, d₁, Φ d₀], z))
  change ((EvenCore.coreHandleAddEquiv h A) (evenPhiNormal h Φ d₀ d₁ z)).2 (j, 0)
    = z (j, 0) at hh
  rw [EvenCore.coreHandleAddEquiv_snd_zero] at hh
  exact hh

omit [Finite A] in
@[simp] theorem evenPhiNormal_handleV {h : ℕ} (d₀ d₁ : A) (z : Fin h × Fin 2 → A) (j : Fin h) :
    evenPhiNormal h Φ d₀ d₁ z (handleV j) = z (j, 1) := by
  have hh := congrArg (fun p : (Generator 2 → A) × (Fin h × Fin 2 → A) ↦ p.2 (j, 1))
    ((EvenCore.coreHandleAddEquiv h A).apply_symm_apply
      (evenCoreOffsets ![d₀, d₁, Φ d₀], z))
  change ((EvenCore.coreHandleAddEquiv h A) (evenPhiNormal h Φ d₀ d₁ z)).2 (j, 1)
    = z (j, 1) at hh
  rw [EvenCore.coreHandleAddEquiv_snd_one] at hh
  exact hh

omit [Finite A] in
@[simp] theorem evenPhiNormal_zero (h : ℕ) :
    evenPhiNormal h Φ (0 : A) (0 : A) (0 : Fin h × Fin 2 → A) = 0 := by
  have hx : (![(0 : A), 0, Φ 0] : Fin 3 → A) = 0 := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · show Φ 0 = 0
      rw [map_zero]
  rw [evenPhiNormal, hx, evenCoreOffsets_zero]
  exact (EvenCore.coreHandleAddEquiv h A).symm.map_zero

/-! ## The three-entry unramified row -/

/-- The shape of the procyclic unramified differential: the `sigma⁻¹`-pivoted tame row, and a
wild row with an `x₀`-coboundary entry, the `τ`-entry and an `x₂`-block `1 − u`. -/
def IsPhiUnramRow (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (g u : C)
    (A : Type*) [AddCommGroup A] [DistribMulAction C A] : Prop :=
  ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
    = ![t.σ⁻¹ • x .tau,
        (g • x (coreLetter h 0) - x (coreLetter h 0)) + x .tau
          + (x (coreLetter h 2) - u • x (coreLetter h 2))]

variable (g u : C)

omit [Finite A] in
/-- Surjectivity of a differential with the `Φ`-unramified row: the tame row pivots on `tau`
through the bijection `σ⁻¹`, and the wild row pivots independently on `x₂` because `1 − u` is
onto. -/
theorem heisD1_surjective_of_phiUnram_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : IsPhiUnramRow t w g u A)
    (husurj : Function.Surjective (fun a : A ↦ a - u • a)) :
    Function.Surjective (heisD1 (A := A) ⇑t w) := by
  classical
  intro rr
  obtain ⟨v, hv⟩ := husurj (rr 1 - (t.σ • rr 0))
  let x : Generator (2 + 2 * h) → A := fun gg ↦
    if gg = .tau then t.σ • rr 0 else if gg = coreLetter h 2 then v else 0
  have hτx2 : (.tau : Generator (2 + 2 * h)) ≠ coreLetter h 2 :=
    Certificates.tau_ne_coreLetter_two h
  have hx0τ : coreLetter h 0 ≠ (.tau : Generator (2 + 2 * h)) := by
    simp [coreLetter]
  have hx0x2 : coreLetter h 0 ≠ coreLetter h 2 := by
    simp [coreLetter, Fin.ext_iff]
  have hxτ : x .tau = t.σ • rr 0 := by simp [x]
  have hxx2 : x (coreLetter h 2) = v := by simp [x, hτx2.symm]
  have hxx0 : x (coreLetter h 0) = 0 := by simp [x, hx0τ, hx0x2]
  refine ⟨x, ?_⟩
  rw [hrow x]
  funext k
  fin_cases k
  · change t.σ⁻¹ • x .tau = rr 0
    rw [hxτ, inv_smul_smul]
  · change (g • x (coreLetter h 0) - x (coreLetter h 0)) + x .tau
        + (x (coreLetter h 2) - u • x (coreLetter h 2)) = rr 1
    rw [hxx0, hxτ, hxx2, smul_zero, sub_zero]
    change v - u • v = rr 1 - t.σ • rr 0 at hv
    rw [hv]
    abel

omit [Finite A] in
/-- Every `Φ`-normal cochain is a cocycle, as soon as `Φ` solves the cocycle equation. -/
theorem heisD1_evenPhiNormal_eq_zero
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : IsPhiUnramRow t w g u A) (Φ : A →+ A)
    (hΦ : ∀ a : A, Φ a - u • Φ a = a - g • a)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    heisD1 ⇑t w (evenPhiNormal h Φ d₀ d₁ z) = 0 := by
  rw [hrow]
  funext k
  fin_cases k
  · simp
  · change (g • (evenPhiNormal h Φ d₀ d₁ z) (coreLetter h 0)
        - (evenPhiNormal h Φ d₀ d₁ z) (coreLetter h 0))
      + (evenPhiNormal h Φ d₀ d₁ z) .tau
      + ((evenPhiNormal h Φ d₀ d₁ z) (coreLetter h 2)
        - u • (evenPhiNormal h Φ d₀ d₁ z) (coreLetter h 2)) = 0
    rw [evenPhiNormal_coreLetter, evenPhiNormal_coreLetter, evenPhiNormal_tau]
    show (g • d₀ - d₀) + 0 + (Φ d₀ - u • Φ d₀) = 0
    rw [hΦ, add_zero]
    abel

set_option maxHeartbeats 1600000 in
/-- **The operator-twisted normal form.**  The tame row kills `tau`, the wild row determines
`x₂` from `x₀` (because `1 − u` is injective), and a `sigma`-coboundary kills `sigma`. -/
theorem evenPhiNormalForm_of_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : IsPhiUnramRow t w g u A) (Φ : A →+ A)
    (hΦ : ∀ a : A, Φ a - u • Φ a = a - g • a)
    (huinj : ∀ a : A, a - u • a = 0 → a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 → ∃! p : A × A × (Fin h × Fin 2 → A),
      x - evenPhiNormal h Φ p.1 p.2.1 p.2.2 ∈ Set.range (heisD0 ⇑t) := by
  have hSsurj : Function.Surjective (fun v : A ↦ t.σ • v - v) :=
    surjective_smul_sub_of_fixedPointFree hσfpf
  have hcoreTriv : ∀ (i : Fin 3) (a : A), t (coreLetter h i) • a = a := fun i a ↦ hwild _ a
  have hhandleUTriv : ∀ (j : Fin h) (a : A), t (handleU j) • a = a := fun j a ↦ hwild _ a
  have hhandleVTriv : ∀ (j : Fin h) (a : A), t (handleV j) • a = a := fun j a ↦ hwild _ a
  intro x hx
  rw [hrow x] at hx
  have hxτ : x .tau = 0 := by
    have hz : t.σ⁻¹ • x .tau = 0 := by simpa using congrFun hx 0
    rw [← smul_inv_smul t.σ (x .tau), hz, smul_zero]
  have hxcore2 : x (coreLetter h 2) = Φ (x (coreLetter h 0)) := by
    have hz : (g • x (coreLetter h 0) - x (coreLetter h 0)) + x .tau
        + (x (coreLetter h 2) - u • x (coreLetter h 2)) = 0 := by simpa using congrFun hx 1
    rw [hxτ, add_zero] at hz
    have h1 : Φ (x (coreLetter h 0)) - u • Φ (x (coreLetter h 0))
        = x (coreLetter h 0) - g • x (coreLetter h 0) := hΦ _
    have hz' : (x (coreLetter h 2) - Φ (x (coreLetter h 0)))
        - u • (x (coreLetter h 2) - Φ (x (coreLetter h 0))) = 0 := by
      rw [smul_sub]
      rw [show x (coreLetter h 2) - Φ (x (coreLetter h 0))
            - (u • x (coreLetter h 2) - u • Φ (x (coreLetter h 0)))
          = ((g • x (coreLetter h 0) - x (coreLetter h 0))
              + (x (coreLetter h 2) - u • x (coreLetter h 2)))
            - ((Φ (x (coreLetter h 0)) - u • Φ (x (coreLetter h 0)))
              - (x (coreLetter h 0) - g • x (coreLetter h 0))) from by abel]
      rw [hz, h1, sub_self, sub_zero]
    exact sub_eq_zero.mp (huinj _ hz')
  obtain ⟨v, hv⟩ := hSsurj (x .sigma)
  let x' := x - heisD0 (⇑t) v
  have hx'σ : x' .sigma = 0 := by
    simp [x', heisD0_apply, hv]
  have hx'τ : x' .tau = 0 := by
    simp [x', heisD0_apply, hτ, hxτ]
  have hcore0 : x' (coreLetter h 0) = x (coreLetter h 0) := by
    simp [x', heisD0_apply, hcoreTriv]
  have hx'core2 : x' (coreLetter h 2) = Φ (x' (coreLetter h 0)) := by
    rw [hcore0, ← hxcore2]
    simp [x', heisD0_apply, hcoreTriv]
  let z := (EvenCore.coreHandleAddEquiv h A x).2
  let p₀ : A × A × (Fin h × Fin 2 → A) := (x (coreLetter h 0), x (coreLetter h 1), z)
  have hnormal : evenPhiNormal h Φ p₀.1 p₀.2.1 p₀.2.2 = x' := by
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
            show ![p₀.1, p₀.2.1, Φ p₀.1] 2 = x' (coreLetter h 2)
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
      simp only [Pi.sub_apply, evenPhiNormal_coreLetter, Matrix.cons_val_zero] at hc
      exact (sub_eq_zero.mp hc.symm).symm
    · apply Prod.ext
      · have hc := congrFun hu (coreLetter h 1)
        rw [heisD0_apply, hcoreTriv, sub_self] at hc
        simp only [Pi.sub_apply, evenPhiNormal_coreLetter, Matrix.cons_val_one,
          Matrix.cons_val_zero] at hc
        exact (sub_eq_zero.mp hc.symm).symm
      · funext jk
        rcases jk with ⟨j, k⟩
        fin_cases k
        · have hc := congrFun hu (handleU j)
          rw [heisD0_apply, hhandleUTriv, sub_self] at hc
          simp only [Pi.sub_apply, evenPhiNormal_handleU] at hc
          have hpj := (sub_eq_zero.mp hc.symm).symm
          simpa [p₀, z] using hpj
        · have hc := congrFun hu (handleV j)
          rw [heisD0_apply, hhandleVTriv, sub_self] at hc
          simp only [Pi.sub_apply, evenPhiNormal_handleV] at hc
          have hpj := (sub_eq_zero.mp hc.symm).symm
          simpa [p₀, z] using hpj

omit [Finite A] in
/-- `1 − u` is injective exactly when `u` is fixed-point free. -/
theorem oneSub_injective_of_fpf (hufpf : ∀ a : A, u • a = a → a = 0) (a : A)
    (ha : a - u • a = 0) : a = 0 :=
  hufpf a (sub_eq_zero.mp ha).symm

/-- `1 − u` is onto on a finite module on which `u` is fixed-point free. -/
theorem oneSub_surjective_of_fpf (hufpf : ∀ a : A, u • a = a → a = 0) :
    Function.Surjective (fun a : A ↦ a - u • a) := by
  have hs : Function.Surjective (fun a : A ↦ u • a - a) :=
    surjective_smul_sub_of_fixedPointFree hufpf
  intro a
  obtain ⟨v, hv⟩ := hs (-a)
  refine ⟨v, ?_⟩
  change v - u • v = a
  change u • v - v = -a at hv
  rw [← neg_sub, hv, neg_neg]

set_option maxHeartbeats 3200000 in
/-- **Stokes duality for an operator-twisted even row.**  Every first-order ingredient comes
from the row shape and the cocycle equation; the only remaining input is left nondegeneracy of
the traced pairing on the `Φ`-normal coordinates. -/
theorem evenPhiStokesDuality_of_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) (hend : IsStokesEndpoint w)
    (hrowA : IsPhiUnramRow t w g u A) (hrowD : IsPhiUnramRow t w g u (ElemDual A))
    (Φ : A →+ A) (ΦD : ElemDual A →+ ElemDual A)
    (hΦ : ∀ a : A, Φ a - u • Φ a = a - g • a)
    (hΦD : ∀ lam : ElemDual A, ΦD lam - u • ΦD lam = lam - g • lam)
    (hufpf : ∀ a : A, u • a = a → a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0)
    (hsep : ∀ p : A × A × (Fin h × Fin 2 → A), p ≠ 0 →
      ∃ rr : ElemDual A × ElemDual A × (Fin h × Fin 2 → ElemDual A),
        heisEta1 ⇑t w (evenPhiNormal h Φ p.1 p.2.1 p.2.2)
          (evenPhiNormal h ΦD rr.1 rr.2.1 rr.2.2) ≠ 0) :
    StokesDuality ⇑t w A := by
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual A), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτD : ∀ lam : ElemDual A, t.τ • lam = lam := fun lam ↦ elemDual_smul_eq_self hτ lam
  have hσfpfD : ∀ lam : ElemDual A, t.σ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hσfpf lam hlam
  have hufpfD : ∀ lam : ElemDual A, u • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hufpf lam hlam
  exact evenNormalStokesDuality_of_normalMap t w
    (fun p ↦ evenPhiNormal h Φ p.1 p.2.1 p.2.2)
    (fun rr ↦ evenPhiNormal h ΦD rr.1 rr.2.1 rr.2.2)
    hA₂ hr hend (by simp [evenPhiNormal_zero Φ h])
    (heisD0_injective_of_sigma_fixedPointFree t hσfpf)
    (heisD0_injective_of_sigma_fixedPointFree (A := ElemDual A) t hσfpfD)
    (heisD1_surjective_of_phiUnram_row g u t w hrowA (oneSub_surjective_of_fpf u hufpf))
    (heisD1_surjective_of_phiUnram_row (A := ElemDual A) g u t w hrowD
      (oneSub_surjective_of_fpf u hufpfD))
    (fun p ↦ heisD1_evenPhiNormal_eq_zero g u t w hrowA Φ hΦ p.1 p.2.1 p.2.2)
    (fun rr ↦ heisD1_evenPhiNormal_eq_zero (A := ElemDual A) g u t w hrowD ΦD hΦD
      rr.1 rr.2.1 rr.2.2)
    (evenPhiNormalForm_of_row g u t w hrowA Φ hΦ (oneSub_injective_of_fpf u hufpf)
      hwild hτ hσfpf)
    (evenPhiNormalForm_of_row (A := ElemDual A) g u t w hrowD ΦD hΦD
      (oneSub_injective_of_fpf u hufpfD) hwildD hτD hσfpfD)
    hsep

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.evenPhiNormal_zero
#print axioms GQ2.Dyadic.heisD1_surjective_of_phiUnram_row
#print axioms GQ2.Dyadic.heisD1_evenPhiNormal_eq_zero
#print axioms GQ2.Dyadic.oneSub_surjective_of_fpf
#print axioms GQ2.Dyadic.evenPhiNormalForm_of_row
#print axioms GQ2.Dyadic.evenPhiStokesDuality_of_row

end AxiomAudit
