/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicPairing

/-!
# Hyperbolic substitution on displaced-head normal coordinates

These induced markings and offsets evaluate the backward Nielsen substitution exactly.
The coordinate formulas retain the action of the original sigma; in particular the selected
U base may act nontrivially.  Only its complementary core and handle bases inherit wild
triviality.  The API is shared by the general raw pairing and its pure-coordinate tests.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandleSource Instances.EvenMHeadHandlePairSource
open Instances.EvenMHeadHandlePairCore Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairNoGo Instances.EvenMHeadHandleHyperbolic

namespace Instances.EvenMHeadHandleHyperbolicRawNormal

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

private theorem handleU_ne_handleU (j k : Fin h) (hkj : k ≠ j) :
    handleU k ≠ (handleU j : Generator (2 + 2 * h)) := by
  intro H
  have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
  simp [handleU, Generator.equivFin] at H'
  exact hkj (Fin.ext (by omega))

private theorem handleV_ne_handleU (j k : Fin h) :
    handleV k ≠ (handleU j : Generator (2 + 2 * h)) := by
  intro H
  have H' := congrArg (Generator.equivFin (2 + 2 * h)) H
  simp [handleV, handleU, Generator.equivFin] at H'
  omega

def rawMark (t : Marking (2 + 2 * h) C) (j : Fin h) :
    Marking (2 + 2 * h) C :=
  ⟨fun g ↦ if g = handleU j then t.σ * t (handleU j)
    else t (headHandlePairSwap j g)⟩

def rawOffset (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) : Generator (2 + 2 * h) → A :=
  fun g ↦ if g = handleU j then t.σ • z (j, 0)
    else headHandlePairRamNormal t j d₀ d₁ z (headHandlePairSwap j g)

@[simp] theorem rawMark_sigma (t : Marking (2 + 2 * h) C) (j : Fin h) :
    (rawMark t j).σ = t (handleU j) := by
  change (if (.sigma : Generator (2 + 2 * h)) = handleU j
    then t.σ * t (handleU j) else t (headHandlePairSwap j .sigma)) = _
  rw [if_neg (by simp [handleU]), headHandlePairSwap_sigma]

@[simp] theorem rawMark_tau (t : Marking (2 + 2 * h) C) (j : Fin h) :
    (rawMark t j).τ = t.τ := by
  change (if (.tau : Generator (2 + 2 * h)) = handleU j
    then t.σ * t (handleU j) else t (headHandlePairSwap j .tau)) = _
  rw [if_neg (by simp [handleU]), headHandlePairSwap_tau]
  rfl

theorem rawMark_core_trivial (t : Marking (2 + 2 * h) C) (j : Fin h)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    ∀ (i : Fin 3) (a : A), rawMark t j (coreLetter h i) • a = a := by
  intro i a
  change (if coreLetter h i = handleU j then _ else _) • a = a
  rw [if_neg (Certificates.MCompact.handleU_ne_coreLetter j i).symm]
  have hc : ∀ (i : Fin 3) (a : A), t (coreLetter h i) • a = a :=
    fun i a ↦ hwild _ a
  have hv : ∀ (k : Fin h) (a : A), t (handleV k) • a = a :=
    fun k a ↦ hwild _ a
  fin_cases i
  · change t (headHandlePairSwap j (coreLetter h 0)) • a = a
    simpa [headHandlePairSwap] using hc 0 a
  · change t (headHandlePairSwap j (coreLetter h 1)) • a = a
    simpa [headHandlePairSwap] using hc 1 a
  · change t (headHandlePairSwap j (coreLetter h 2)) • a = a
    simpa using hv j a

theorem rawMark_handleV_trivial (t : Marking (2 + 2 * h) C) (j k : Fin h)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    ∀ a : A, rawMark t j (handleV k) • a = a := by
  intro a
  change (if handleV k = handleU j then _ else _) • a = a
  rw [if_neg (handleV_ne_handleU j k)]
  by_cases hk : k = j
  · subst k
    rw [headHandlePairSwap_handleV_self]
    exact hwild _ a
  · have heq : headHandlePairSwap j (handleV k) = handleV k := by
      simp [headHandlePairSwap, hk]
    rw [heq]
    exact hwild _ a

theorem rawMark_handleU_trivial (t : Marking (2 + 2 * h) C) (j k : Fin h)
    (hk : k ≠ j)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a) :
    ∀ a : A, rawMark t j (handleU k) • a = a := by
  intro a
  change (if handleU k = handleU j then _ else _) • a = a
  rw [if_neg (handleU_ne_handleU j k hk)]
  have heq : headHandlePairSwap j (handleU k) = handleU k := by
    simp [headHandlePairSwap, hk]
  rw [heq]
  exact hwild _ a

@[simp] theorem rawOffset_tau (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) : rawOffset t j d₀ d₁ z .tau = 0 := by
  have hne : (.tau : Generator (2 + 2 * h)) ≠ handleU j := by simp [handleU]
  simp [rawOffset, hne]

@[simp] theorem rawOffset_coreZero (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    rawOffset t j d₀ d₁ z (coreLetter h 0) = d₀ := by
  simp [rawOffset, (Certificates.MCompact.handleU_ne_coreLetter j 0).symm,
    headHandlePairSwap]

@[simp] theorem rawOffset_coreOne (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    rawOffset t j d₀ d₁ z (coreLetter h 1) = d₁ := by
  simp [rawOffset, (Certificates.MCompact.handleU_ne_coreLetter j 1).symm,
    headHandlePairSwap]

theorem rawOffset_coreTwo (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) (hz : z (j, 1) = 0) :
    rawOffset t j d₀ d₁ z (coreLetter h 2) = 0 := by
  simp [rawOffset, (Certificates.MCompact.handleU_ne_coreLetter j 2).symm, hz]

theorem rawOffset_handleU (t : Marking (2 + 2 * h) C) (j k : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) (hk : k ≠ j) :
    rawOffset t j d₀ d₁ z (handleU k) = z (k, 0) := by
  simp [rawOffset, handleU_ne_handleU j k hk, headHandlePairSwap, hk]

@[simp] theorem rawOffset_handleV (t : Marking (2 + 2 * h) C) (j k : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    rawOffset t j d₀ d₁ z (handleV k) = z (k, 1) := by
  by_cases hk : k = j
  · subst k
    simp [rawOffset, handleV_ne_handleU]
  · simp [rawOffset, handleV_ne_handleU, headHandlePairSwap, hk]

theorem heisEvalZ_backward_rawNormal
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₀ lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (g : Generator (2 + 2 * h)) :
    heisEvalZ ⇑t (headHandlePairRamNormal t j d₀ d₁ z)
      (headHandlePairRamNormal t j lam₀ lam₁ mu) E E₂
      ((headHandleHyperbolicNielsen j).backward g) =
    heisGen ⇑(rawMark t j) (rawOffset t j d₀ d₁ z)
      (rawOffset t j lam₀ lam₁ mu) g := by
  by_cases hg : g = handleU j
  · subst g
    rw [headHandleHyperbolicNielsen_backward_handleU,
      heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen]
    apply HeisLift.ext <;> simp [rawMark, rawOffset, heisGen]
  · rw [headHandleHyperbolicNielsen_backward_of_ne j g hg, heisEvalZ_gen]
    apply HeisLift.ext <;> simp [rawMark, rawOffset, heisGen, hg]

@[simp] theorem rawOffset_sigma (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) : rawOffset t j d₀ d₁ z .sigma = z (j, 0) := by
  have hne : (.sigma : Generator (2 + 2 * h)) ≠ handleU j := by simp [handleU]
  simp [rawOffset, hne]

@[simp] theorem rawOffset_handleU_self (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    rawOffset t j d₀ d₁ z (handleU j) = t.σ • z (j, 0) := by
  simp [rawOffset]

theorem rawOffset_coreTwo_eq (t : Marking (2 + 2 * h) C) (j : Fin h)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) :
    rawOffset t j d₀ d₁ z (coreLetter h 2) = z (j, 1) - t.σ⁻¹ • z (j, 1) := by
  simp [rawOffset, (Certificates.MCompact.handleU_ne_coreLetter j 2).symm]

#print axioms rawMark
#print axioms rawOffset
#print axioms rawMark_sigma
#print axioms rawMark_tau
#print axioms rawMark_core_trivial
#print axioms rawMark_handleV_trivial
#print axioms rawMark_handleU_trivial
#print axioms rawOffset_sigma
#print axioms rawOffset_tau
#print axioms rawOffset_coreZero
#print axioms rawOffset_coreOne
#print axioms rawOffset_coreTwo
#print axioms rawOffset_coreTwo_eq
#print axioms rawOffset_handleU
#print axioms rawOffset_handleU_self
#print axioms rawOffset_handleV
#print axioms heisEvalZ_backward_rawNormal

end Instances.EvenMHeadHandleHyperbolicRawNormal
end
end GQ2.Dyadic

