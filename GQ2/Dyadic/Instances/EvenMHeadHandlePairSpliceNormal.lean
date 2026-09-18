/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaNormalSpliceTransport
import GQ2.Dyadic.Instances.WordPhaseRawUnramifiedNormal
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
import GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes

/-! # Compact normal coordinates for the actual unramified pair splice -/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceNormal
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates MarkedCore Words
open Instances.EvenMHeadHandlePairSource Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNormalize Instances.EvenMHeadHandlePairSpliceSupply
open Instances.EvenMHeadHandlePairUnramified Instances.GammaRCorePresentationNuNormalize
open Instances.WordPhaseModel Instances.WordPhaseRawUnramifiedNormal
open Instances.MpcSemanticUnramifiedStokes

/-- The real normalized, corrected splice has the compact normal form. There is no
relator-death hypothesis on the raw pair word in the original, possibly nonfaithful group. -/
theorem headHandlePairSplice_compactNormal
    {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hq : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2 + 2 * h) q
        (headHandlePairSpliceW alpha h q halpha hq0 hq j nuP) (4 * Monoid.exponent C) l)=1) :
    let w := pinnedResolvedFamily (2 + 2 * h) q
      (headHandlePairSpliceW alpha h q halpha hq0 hq j nuP) (4 * Monoid.exponent C)
    (∀ p : (A × A) × (Fin h → A × A), heisD1 ⇑t w (wPmCompactPhaseNormal h p)=0) ∧
      ∀ x, heisD1 (A := A) ⇑t w x=0 →
        ∃! p, x-wPmCompactPhaseNormal h p ∈ Set.range (heisD0 ⇑t) := by
  let E := omegaPinnedLevelZhatResolver (4 * Monoid.exponent C)
  let E₂ := omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)
  let k := wildNuCoefficient nuP (headHandlePairCorePresentation alpha h halpha j).mark
  let R := headHandlePairCompactW alpha j
  let w := fun l ↦ heisToFree E E₂ (gammaFam (2 + 2 * h) q R l)
  have hres := omegaPinnedLevelZhatResolver_fourMulExponent_wordLift (C := C) hA₂
  have hrow := heisD1_headHandlePair_unram_apply (alpha := alpha) t j E E₂
    hA₂ hwild htau hq hres
  have hsq (a : A) : heisD1 ⇑t w (heisD0 ⇑t a)=0 := by
    rw [hrow]
    have hcore : t (coreLetter h 2) • a=a := hwild _ a
    funext l
    fin_cases l <;> simp [heisD0_apply, htau, hcore]
  have hs (i : Fin (2 + 2 * h + 1)) (a : A) :
      t.σ ^ E (padicOmega2 (k i)) • a=a := by
    rw [omegaPinnedLevelZhatResolver_spec (fourMulExponent_ne_zero_and_even C).1
      (fun c : C ↦ (Monoid.order_dvd_exponent c).trans (dvd_mul_left _ _))]
    exact zpowHat_padicOmega2_smul_of_powOmega2 t.σ (k i) hsigma2 a
  have hk := kernel_iff_normalizedCorrectedSplice_unramified_of_square t E E₂ k
    hA₂ hwild htau hq hsigma hs (omegaPinnedLevelZhatResolver_omega2 _)
    (omega2Exp_fourMulExponent_mod_four C)
    (tamePrimeToTwoCorrectionExponent hq0 hq
      (headHandlePairNormalizedW alpha h halpha j nuP)
      (tame_eval_headHandlePairNormalized_mem_inertia halpha j nuP))
    R (Words.MCompact.mCompactW alpha h) hsq hr
  exact normalForm_of_same_kernel ⇑t w _ (wPmCompactPhaseNormal h)
    (fun x ↦ (hk x).symm)
    (headHandlePair_compactPhaseNormal_mem t j E E₂ hA₂ hwild htau hq hres)
    (headHandlePair_compactPhaseNormalForm t j E E₂ hA₂ hwild htau hq hres hsigma)

#print axioms headHandlePairSplice_compactNormal

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceNormal
