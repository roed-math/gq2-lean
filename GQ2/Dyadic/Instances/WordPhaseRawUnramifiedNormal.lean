/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramified
import GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes
import GQ2.Dyadic.Instances.WordPhaseModel

namespace GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Words.Mpc GQ2.Dyadic.MProcyclicUnram
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramified
open GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes

variable {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
  [DistribMulAction C A] {alpha r pp h q : ℕ}

omit [Finite C] in
private theorem evenNormalForm_rowOnly
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x
      = ![t.σ⁻¹ • x .tau, x .tau + (x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2))])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 → ∃! p : A × A × (Fin h × Fin 2 → A),
      x - evenNormal h p.1 p.2.1 p.2.2 ∈ Set.range (heisD0 ⇑t) := by
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
  have hxcore2 : x (coreLetter h 2) = 0 := by
    have hz : x .tau + (x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2)) = 0 := by
      simpa using congrFun hx 1
    rw [hxτ, zero_add, sub_eq_zero] at hz
    exact sigmaInv_fixedPointFree t hσfpf _ hz.symm
  obtain ⟨v, hv⟩ := hSsurj (x .sigma)
  let x' := x - heisD0 (⇑t) v
  have hx'σ : x' .sigma = 0 := by
    simp [x', heisD0_apply, hv]
  have hx'τ : x' .tau = 0 := by
    simp [x', heisD0_apply, hτ, hxτ]
  have hx'core2 : x' (coreLetter h 2) = 0 := by
    simp [x', heisD0_apply, hcoreTriv, hxcore2]
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

omit [Finite C] in
/-- Compact normal forms depend only on the two Fox rows, not on actual relator death. -/
theorem compactPhaseNormalForm_of_row
    (t : Marking (2 + 2 * h) C) (w : Fin 2 → FreeGroup (Generator (2 + 2 * h)))
    (hrow : ∀ x : Generator (2 + 2 * h) → A, heisD1 ⇑t w x =
      ![t.σ⁻¹ • x .tau, x .tau + (x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2))])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    ∀ x, heisD1 (A := A) ⇑t w x = 0 →
      ∃! p : (A × A) × (Fin h → A × A),
        x - wPmCompactPhaseNormal h p ∈ Set.range (heisD0 ⇑t) := by
  intro x hx
  obtain ⟨r, hr0, hu⟩ := evenNormalForm_rowOnly t w hrow hwild hτ hσfpf x hx
  refine ⟨wPmCompactCoordsEquiv h A r, ?_, ?_⟩
  · change x - wPmCompactPhaseNormal h (wPmCompactCoordsEquiv h A r) ∈ _
    rw [wPmCompactPhaseNormal_coordsEquiv]
    exact hr0
  · intro p hp
    have hpr : (wPmCompactCoordsEquiv h A).symm p = r := by
      refine hu _ ?_
      exact hp
    rw [← hpr, Equiv.apply_symm_apply]

/-- Raw pair normal coordinates are cocycles at every handle rank. -/
theorem headHandlePair_compactPhaseNormal_mem
    (t : Marking (2 + 2 * h) C) (j : Fin h) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q)
    (hres : ResolverLifts E (WordLift A C))
    (p : (A × A) × (Fin h → A × A)) :
    heisD1 ⇑t (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l))
      (wPmCompactPhaseNormal h p) = 0 :=
  wPm_heisD1_compactPhaseNormal_eq_zero t _
    (heisD1_headHandlePair_unram_apply t j E E₂ hA₂ hwild hτ hq hres) p

/-- Each raw pair cocycle has exactly one compact normal coordinate modulo coboundaries. -/
theorem headHandlePair_compactPhaseNormalForm
    (t : Marking (2 + 2 * h) C) (j : Fin h) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a) (hq : Even q)
    (hres : ResolverLifts E (WordLift A C))
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    ∀ x, heisD1 (A := A) ⇑t (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l)) x = 0 →
      ∃! p : (A × A) × (Fin h → A × A),
        x - wPmCompactPhaseNormal h p ∈ Set.range (heisD0 ⇑t) :=
  compactPhaseNormalForm_of_row t _
    (heisD1_headHandlePair_unram_apply t j E E₂ hA₂ hwild hτ hq hres)
    hwild hτ hσfpf

/-- A semantic Mpc unit acting as sigma has precisely the compact unramified row. -/
theorem heisD1_mpcUnit_compact_unramified_apply
    (t : Marking (2 + 2 * h) C) (eta : ℤ_[2]ˣ) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0) (halpha : 1 ≤ alpha) (hq : Even q)
    (hres : ResolverLifts E (WordLift A C))
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hS₂ : ∀ a : A, powOmega2 t.σ • a = a)
    (hη : ∀ a : A, (t.σ ^ E (etaHatZ (eta : ℤ_[2]))) • a = t.σ • a)
    (x : Generator (2 + 2 * h) → A) :
    heisD1 ⇑t (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (mpcWUnit alpha r pp eta h) l)) x =
      ![t.σ⁻¹ • x .tau, x .tau + (x (coreLetter h 2) - t.σ⁻¹ • x (coreLetter h 2))] := by
  rw [mpcUnit_resolvedFamily_eq_lit,
    heisD1_mpcFamOf_unramified_apply (u := t.σ ^ E (etaHatZ (eta : ℤ_[2])))
      t E E₂ hres hA₂ halpha hq hwild hτ hS₂ rfl]
  have hi (a : A) : (t.σ ^ E (etaHatZ (eta : ℤ_[2])))⁻¹ • a = t.σ⁻¹ • a := by
    apply (MulAction.injective (t.σ ^ E (etaHatZ (eta : ℤ_[2]))))
    dsimp only
    rw [smul_inv_smul, hη, smul_inv_smul]
  rw [hi]

/-- Semantic Mpc compact normal coordinates are cocycles, with the actual unit action exposed. -/
theorem mpcUnit_compactPhaseNormal_mem
    (t : Marking (2 + 2 * h) C) (eta : ℤ_[2]ˣ) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0) (halpha : 1 ≤ alpha) (hq : Even q)
    (hres : ResolverLifts E (WordLift A C))
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hS₂ : ∀ a : A, powOmega2 t.σ • a = a)
    (hη : ∀ a : A, (t.σ ^ E (etaHatZ (eta : ℤ_[2]))) • a = t.σ • a)
    (p : (A × A) × (Fin h → A × A)) :
    heisD1 ⇑t (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (mpcWUnit alpha r pp eta h) l))
      (wPmCompactPhaseNormal h p) = 0 :=
  wPm_heisD1_compactPhaseNormal_eq_zero t _
    (heisD1_mpcUnit_compact_unramified_apply t eta E E₂ hA₂ halpha hq hres hwild hτ hS₂ hη) p

/-- Each semantic Mpc cocycle has a unique compact normal representative. -/
theorem mpcUnit_compactPhaseNormalForm
    (t : Marking (2 + 2 * h) C) (eta : ℤ_[2]ˣ) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0) (halpha : 1 ≤ alpha) (hq : Even q)
    (hres : ResolverLifts E (WordLift A C))
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hS₂ : ∀ a : A, powOmega2 t.σ • a = a)
    (hη : ∀ a : A, (t.σ ^ E (etaHatZ (eta : ℤ_[2]))) • a = t.σ • a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    ∀ x, heisD1 (A := A) ⇑t (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (mpcWUnit alpha r pp eta h) l)) x = 0 →
      ∃! p : (A × A) × (Fin h → A × A),
        x - wPmCompactPhaseNormal h p ∈ Set.range (heisD0 ⇑t) :=
  compactPhaseNormalForm_of_row t _
    (heisD1_mpcUnit_compact_unramified_apply t eta E E₂ hA₂ halpha hq hres hwild hτ hS₂ hη)
    hwild hτ hσfpf

end
end GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal

#print axioms GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal.headHandlePair_compactPhaseNormal_mem
#print axioms GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal.compactPhaseNormalForm_of_row
#print axioms GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal.headHandlePair_compactPhaseNormalForm
#print axioms GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal.heisD1_mpcUnit_compact_unramified_apply
#print axioms GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal.mpcUnit_compactPhaseNormal_mem
#print axioms GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal.mpcUnit_compactPhaseNormalForm
