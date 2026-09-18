/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicRawNormal
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicFox
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicRawCore
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicRawHelpers

/-!
# The raw hyperbolic normal pairing off the promoted V coordinate

For arbitrary sigma action, the raw family's normal pairing restricts to the ordinary
compact-M core plus its handle planes when both promoted V slots vanish.  Under the
backward substitution, the compact sigma base is a wild letter and acts trivially.  The
core theorem allows its offsets to remain arbitrary, while the selected handle's zero
right offsets eliminate its contribution regardless of its left base action.

Together with pure-coordinate tests, this is the rank-uniform separation input for the
raw family with its unchanged tame relator.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandleSource Instances.EvenMHeadHandlePairSource
open Instances.EvenMHeadHandlePairCore Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairNoGo Instances.EvenMHeadHandleHyperbolic
open Instances.EvenMHeadHandleHyperbolicRawHelpers
open Instances.EvenMHeadHandleHyperbolicRawNormal
open Instances.EvenMHeadHandleHyperbolicRawCore

namespace Instances.EvenMHeadHandleHyperbolicRawPairing

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- The compact-M normal pairing on the zero-V complement, with arbitrary sigma action. -/
theorem heisEta1_headHandleHyperbolicRawFamily_normal_zeroV
    [Finite C] [Finite A] {alpha q : ℕ}
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hα : 2 ≤ alpha)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A)
    (lam₀ lam₁ : ElemDual A) (mu : Fin h × Fin 2 → ElemDual A)
    (hz : z (j, 1) = 0) (hmu : mu (j, 1) = 0) :
    heisEta1 ⇑t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j)
      (headHandlePairRamNormal t j d₀ d₁ z)
      (headHandlePairRamNormal t j lam₀ lam₁ mu) =
    lam₁ d₁ + (lam₀ d₁ + lam₁ d₀)
      + ∑ k, (mu (k, 0) (z (k, 1)) + mu (k, 1) (z (k, 0))) := by
  rw [heisEta1_apply, Fin.sum_univ_two]
  change (FreeGroup.lift (heisGen ⇑t (headHandlePairRamNormal t j d₀ d₁ z)
      (headHandlePairRamNormal t j lam₀ lam₁ mu))
      (heisToFree E E₂ (tameRelW (2 + 2 * h) q))).z
    + (FreeGroup.lift (heisGen ⇑t (headHandlePairRamNormal t j d₀ d₁ z)
      (headHandlePairRamNormal t j lam₀ lam₁ mu))
      (heisToFree E E₂ (headHandleHyperbolicW alpha j))).z = _
  rw [← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]
  rw [heisZ_tameRelW_eq_zero_of_tame_offsets_zero t _ _ E E₂
    (by simp) (by simp) (by simp) (by simp), zero_add]
  rw [headHandleHyperbolicW]
  change (PWord.evalZ (heisGen ⇑t (headHandlePairRamNormal t j d₀ d₁ z)
      (headHandlePairRamNormal t j lam₀ lam₁ mu)) E E₂
    (PWord.subst (headHandleHyperbolicNielsen j).backward
      (Words.MCompact.mCompactW alpha h))).z = _
  rw [PWord.evalZ_subst]
  have hmap : (fun g ↦ heisEvalZ ⇑t (headHandlePairRamNormal t j d₀ d₁ z)
      (headHandlePairRamNormal t j lam₀ lam₁ mu) E E₂
      ((headHandleHyperbolicNielsen j).backward g)) =
      heisGen ⇑(rawMark t j) (rawOffset t j d₀ d₁ z)
        (rawOffset t j lam₀ lam₁ mu) := by
    funext g
    exact heisEvalZ_backward_rawNormal t j d₀ d₁ z lam₀ lam₁ mu E E₂ g
  change (PWord.evalZ (fun g ↦ heisEvalZ ⇑t
    (headHandlePairRamNormal t j d₀ d₁ z) (headHandlePairRamNormal t j lam₀ lam₁ mu)
    E E₂ ((headHandleHyperbolicNielsen j).backward g)) E E₂
    (Words.MCompact.mCompactW alpha h)).z = _
  rw [hmap]
  let s := rawMark t j
  let b := rawOffset t j d₀ d₁ z
  let c := rawOffset t j lam₀ lam₁ mu
  change (heisEvalZ ⇑s b c E E₂ (Words.MCompact.mCompactW alpha h)).z = _
  have hcore : (heisEvalZ ⇑s b c E E₂
      (PWord.prodList (Words.MCompact.mFactors alpha h))).z =
      lam₁ d₁ + (lam₀ d₁ + lam₁ d₀) := by
    rw [← heisEvalZ_mFactors_coreOnly]
    rw [EvenMHeadHandleHyperbolicRawCore.heisZ_mFactors_ram_sigma_trivial
      (coreOnlyMark s) b c E E₂ hA₂
      (by
        intro a
        change (coreOnlyMark (rawMark t j)).σ • a = a
        rw [coreOnlyMark_sigma, rawMark_sigma]
        exact hwild _ a)
      (coreOnlyMark_wild_trivial s (rawMark_core_trivial t j hwild)) hα
      (by simpa [s] using hτfpf) (by simpa [s] using hTodd)
      (by simp [b]) (by simp [c])
      (rawOffset_coreTwo t j d₀ d₁ z hz) (rawOffset_coreTwo t j lam₀ lam₁ mu hmu)
      hresA hresD hres]
    simp [b, c]
  have hH := heisHandles_zeroV s j b c E E₂
    (fun k ↦ rawMark_handleV_trivial t j k hwild)
    (fun k hk ↦ rawMark_handleU_trivial t j k hk hwild)
    (by simp [b, hz]) (by simp [c, hmu])
  have hsum : (∑ k, (c (handleU k) (b (handleV k)) + c (handleV k) (b (handleU k)))) =
      ∑ k, (mu (k, 0) (z (k, 1)) + mu (k, 1) (z (k, 0))) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = j
    · subst k
      simp [b, c, hz, hmu]
    · simp [b, c, rawOffset_handleU, hk]
  rw [Words.MCompact.mCompactW, heisEvalZ_prodList, List.map_append, List.prod_append,
    Certificates.MCompact.heisEvalZ_handleTailW, heisMul_z_of_a_eq_zero _ _ hH.1.1,
    ← heisEvalZ_prodList, hcore, hH.2, hsum]

#print axioms heisEta1_headHandleHyperbolicRawFamily_normal_zeroV

end Instances.EvenMHeadHandleHyperbolicRawPairing
end
end GQ2.Dyadic

