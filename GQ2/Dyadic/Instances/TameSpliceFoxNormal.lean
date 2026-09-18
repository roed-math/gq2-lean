/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaNormalSpliceFox
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
import GQ2.Dyadic.Instances.MpcMobileUnramifiedComparison

/-!
# Reduced Fox matrices of the actual pair and mobile splice words

These are uniform actual-word specializations of the explicit triangular row elimination.
The source is normalized, prime-to-two corrected and spliced before its tau coefficient is
read. No matrix equality with the raw source is asserted, and no raw relator-death premise
is needed. All evaluations use the pinned coefficient-independent finite resolver.
-/

namespace GQ2.Dyadic.Instances.TameSpliceFoxNormal
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates MarkedCore Words
open Certificates.MProcyclic SigmaNormalFoxElimination
open Instances.GammaRCorePresentationNuNormalize
open Instances.EvenMHeadHandlePairSource Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairSpliceSupply
open Instances.MpcSemanticUnramifiedStokes Instances.MpcMobileNuSource
open Instances.MpcMobileUnramifiedComparison
open MProcyclicUnram Words.Mpc

variable {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
  [TopologicalSpace C] [DiscreteTopology C]
  [AddCommGroup A] [Finite A] [DistribMulAction C A]

/-- The normalized pair source has identity pivots at tau and x2 after the displayed
invertible row operations, uniformly in alpha, h and the promoted handle. -/
theorem pairSplice_reducedFox
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)
        (4 * Monoid.exponent C) l)=1)
    (x : Generator (2+2*h) → A) :
    let d := heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)
        (4 * Monoid.exponent C))
    rowElimination (actionEquiv t.σ⁻¹) (oneSubInvAction t.σ hsigma)
      (tauColumn d) (d x) = ![x .tau, x (.wild (x2Idx h))] := by
  let E := omegaPinnedLevelZhatResolver (4 * Monoid.exponent C)
  let E₂ := omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)
  let k := wildNuCoefficient nuP (headHandlePairCorePresentation alpha h halpha j).mark
  have hs : ∀ (i : Fin (2+2*h+1)) (a : A), t.σ ^ E (padicOmega2 (k i)) • a=a := by
    intro i a
    rw [omegaPinnedLevelZhatResolver_spec (fourMulExponent_ne_zero_and_even C).1
      (fun c : C ↦ (Monoid.order_dvd_exponent c).trans (dvd_mul_left _ _))]
    exact zpowHat_padicOmega2_smul_of_powOmega2 t.σ (k i) hsigma2 a
  have hres := omegaPinnedLevelZhatResolver_fourMulExponent_wordLift (C := C) hA₂
  apply normalizedCorrectedSplice_reduced_rows t E E₂ k _
    (headHandlePairCompactW alpha j) (MCompact.mCompactW alpha h) (x2Idx h)
    hA₂ hwild htau hqe hsigma hs
    (omegaPinnedLevelZhatResolver_omega2 _) (omega2Exp_fourMulExponent_mod_four C) hres hr
  intro y _hys hyt
  rw [heisEvalZ_a_eq_foxD hres,
    foxD_headHandlePairCompactW_unram t y E E₂ alpha j hA₂ hwild htau, hyt, zero_add]
  rfl

#print axioms pairSplice_reducedFox

/-- The same explicit normal matrix for arbitrary semantic mobile units, every level,
head charge and handle count. No rational display of the two-adic unit is required. -/
theorem mobileSplice_reducedFox {r p : ℕ}
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) (4 * Monoid.exponent C) l)=1)
    (x : Generator (2+2*h) → A) :
    let d := heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) (4 * Monoid.exponent C))
    rowElimination (actionEquiv t.σ⁻¹) (oneSubInvAction t.σ hsigma)
      (tauColumn d) (d x) = ![x .tau, x (.wild (x2Idx h))] := by
  let E := omegaPinnedLevelZhatResolver (4 * Monoid.exponent C)
  let E₂ := omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)
  let k := wildNuCoefficient nuP
    (Instances.MProcyclicCore.mpcCorePresentationUnit alpha r p eta h halpha).mark
  have hs : ∀ (i : Fin (2+2*h+1)) (a : A), t.σ ^ E (padicOmega2 (k i)) • a=a := by
    intro i a
    rw [omegaPinnedLevelZhatResolver_spec (fourMulExponent_ne_zero_and_even C).1
      (fun c : C ↦ (Monoid.order_dvd_exponent c).trans (dvd_mul_left _ _))]
    exact zpowHat_padicOmega2_smul_of_powOmega2 t.σ (k i) hsigma2 a
  have hres := omegaPinnedLevelZhatResolver_fourMulExponent_wordLift (C := C) hA₂
  apply normalizedCorrectedSplice_reduced_rows t E E₂ k _
    (mpcWUnit alpha r p eta h) (MCompact.mCompactW alpha h) (x2Idx h)
    hA₂ hwild htau hqe hsigma hs
    (omegaPinnedLevelZhatResolver_omega2 _) (omega2Exp_fourMulExponent_mod_four C) hres hr
  intro y _hys hyt
  have hword : heisEvalZ ⇑t y 0 E E₂ (mpcWUnit alpha r p eta h) =
      heisEvalZ ⇑t y 0 E E₂ (mpcW alpha r p (.lit (E (etaHatZ (eta : ℤ_[2])))) h) := by
    unfold heisEvalZ
    rw [mpcWUnit, ← mpcWAt_etaDisplay]
    apply evalZ_mpcWAt_congr
    rfl
  have heta (a : A) : t.σ ^ E (etaHatZ (eta : ℤ_[2])) • a = t.σ • a :=
    pinned_eta_smul_eq_sigma t.σ (eta : ℤ_[2]) hsigma2 a
  have hinv (a : A) : (t.σ ^ E (etaHatZ (eta : ℤ_[2])))⁻¹ • a = t.σ⁻¹ • a := by
    apply inv_smul_eq_iff.mpr
    rw [heta, smul_inv_smul]
  rw [hword, heisEvalZ_a_eq_foxD hres,
    foxD_mpcW_unram_of_eq t E E₂ y halpha r p
      (u := t.σ ^ E (etaHatZ (eta : ℤ_[2]))) rfl hA₂ hwild htau hsigma2,
    hyt, zero_add, hinv]
  rfl

#print axioms mobileSplice_reducedFox

end
end GQ2.Dyadic.Instances.TameSpliceFoxNormal
