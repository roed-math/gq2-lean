/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicRawNormal
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicFox
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicRawHelpers
import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicPureHead

namespace GQ2.Dyadic

/-!
# Pure-U detection for the raw hyperbolic family

Against a pure dual U normal, an arbitrary primal normal evaluates to the selected
V coordinate. This calculation does not assume the original sigma action trivial.
In the transported compact word, the core contributes the displacement
`lam (v - sigma⁻¹ • v)` and the handle tail contributes `lam (sigma⁻¹ • v)`.
Their sum is `lam v`, independently of the quadratic term on the V-V block.

Only exponent two, alpha at least two, and trivial wild action are required.
-/

noncomputable section
open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandlePairCore Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairSource Instances.EvenMHeadHandleHyperbolic
open Instances.EvenMHeadHandleHyperbolicRawHelpers
open Instances.EvenMHeadHandleHyperbolicRawNormal

namespace Instances.EvenMHeadHandleHyperbolicRawDetection

variable {h : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- Pure dual U detects the selected primal V coordinate for arbitrary sigma action. -/
theorem heisEta1_headHandleHyperbolicRawFamily_normal_pureU
    {alpha q : ℕ} (t : Marking (2 + 2 * h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0) (hα : 2 ≤ alpha)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (d₀ d₁ : A) (z : Fin h × Fin 2 → A) (lam : ElemDual A) :
    heisEta1 ⇑t
      (EvenMHeadHandleHyperbolicFox.headHandleHyperbolicRawFamily E E₂ alpha h q j)
      (headHandlePairRamNormal t j d₀ d₁ z) (hyperYU t j lam) = lam (z (j, 1)) := by
  rw [heisEta1_apply, Fin.sum_univ_two]
  change (FreeGroup.lift (heisGen ⇑t (headHandlePairRamNormal t j d₀ d₁ z)
      (hyperYU t j lam)) (heisToFree E E₂ (tameRelW (2 + 2 * h) q))).z
    + (FreeGroup.lift (heisGen ⇑t (headHandlePairRamNormal t j d₀ d₁ z)
      (hyperYU t j lam)) (heisToFree E E₂ (headHandleHyperbolicW alpha j))).z = _
  rw [← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]
  rw [heisZ_tameRelW_eq_zero_of_tame_offsets_zero t _ _ E E₂
    (by simp) (by simp) (by simp [hyperYU]) (by simp [hyperYU]), zero_add]
  rw [headHandleHyperbolicW]
  change (PWord.evalZ (heisGen ⇑t (headHandlePairRamNormal t j d₀ d₁ z)
      (headHandlePairRamNormal t j 0 0 (pairUSlot j lam))) E E₂
    (PWord.subst (headHandleHyperbolicNielsen j).backward
      (Words.MCompact.mCompactW alpha h))).z = _
  rw [PWord.evalZ_subst]
  have hmap : (fun g ↦ heisEvalZ ⇑t (headHandlePairRamNormal t j d₀ d₁ z)
      (headHandlePairRamNormal t j 0 0 (pairUSlot j lam)) E E₂
      ((headHandleHyperbolicNielsen j).backward g)) =
      heisGen ⇑(rawMark t j) (rawOffset t j d₀ d₁ z)
        (rawOffset t j 0 0 (pairUSlot j lam)) := by
    funext g
    exact heisEvalZ_backward_rawNormal t j d₀ d₁ z 0 0 (pairUSlot j lam) E E₂ g
  change (PWord.evalZ (fun g ↦ heisEvalZ ⇑t
    (headHandlePairRamNormal t j d₀ d₁ z)
    (headHandlePairRamNormal t j 0 0 (pairUSlot j lam))
    E E₂ ((headHandleHyperbolicNielsen j).backward g)) E E₂
    (Words.MCompact.mCompactW alpha h)).z = _
  rw [hmap]
  let s := rawMark t j
  let b := rawOffset t j d₀ d₁ z
  let c := rawOffset t j 0 0 (pairUSlot j lam)
  change (heisEvalZ ⇑s b c E E₂ (Words.MCompact.mCompactW alpha h)).z = _
  have hcore := EvenMHeadHandleHyperbolicPureHead.mFactors_dual_head
    (coreOnlyMark s) b c E E₂ hA₂ hα
    (by simpa [s] using (mem_trivAct.mp (Certificates.trivAct_handleU t hwild j)))
    (coreOnlyMark_wild_trivial s (rawMark_core_trivial t j hwild))
    (by simp [c]) (by intro i; fin_cases i <;> simp [c, rawOffset_coreTwo_eq, pairUSlot])
  dsimp only at hcore
  rw [heisEvalZ_mFactors_coreOnly] at hcore
  have hH := heisEvalZ_handlesW_of_right_trivial_dual_zero s b c E E₂
    (fun k ↦ rawMark_handleV_trivial t j k hwild)
    (by intro k; simp [c, pairUSlot])
  have hsum : (∑ k, c (handleU k) (b (handleV k))) =
      lam (t.σ⁻¹ • z (j, 1)) := by
    rw [Finset.sum_eq_single j]
    · simp [b, c, rawOffset_handleU_self, pairUSlot, ElemDual.smul_apply]
    · intro k _ hk
      simp [c, rawOffset_handleU, hk, pairUSlot]
    · simp
  rw [Words.MCompact.mCompactW, heisEvalZ_prodList, List.map_append, List.prod_append,
    Certificates.MCompact.heisEvalZ_handleTailW]
  have hPl : ((Words.MCompact.mFactors alpha h).map (heisEvalZ ⇑s b c E E₂)).prod.l = 0 := by
    rw [← heisEvalZ_prodList]
    exact hcore.1
  rw [heisMul_z_of_l_eq_zero _ _ hPl, ← heisEvalZ_prodList, hcore.2, hH.2, hsum]
  simp [b, c, rawOffset_coreTwo_eq, pairUSlot, map_sub]

#print axioms heisEta1_headHandleHyperbolicRawFamily_normal_pureU

end Instances.EvenMHeadHandleHyperbolicRawDetection
end
end GQ2.Dyadic

