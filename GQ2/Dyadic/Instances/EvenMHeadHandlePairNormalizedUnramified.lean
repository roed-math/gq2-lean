/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramified
import GQ2.Dyadic.Instances.OmegaPinnedLevelResolver
import GQ2.Dyadic.Instances.OmegaPinnedLevelResolverParity

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalizedUnramified

noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandleSource Instances.EvenMHeadHandlePairSource
open Instances.EvenMHeadHandlePairCore Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairUnramified
open Instances.GammaRCorePresentationNuNormalize
open GQ2.Dyadic.MarkedCore

theorem headHandlePair_isStokesEndpoint
    {alpha h q : ℕ} (j : Fin h) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hq : Even q) (he : Odd (E omega2)) :
    IsStokesEndpoint (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l)) := by
  have H := isStokesEndpoint_gammaFam_subst_subst_of_tau (E₂ := E₂) (MCompact.mCompactW alpha h)
    (mCompactOf_isStokesEndpoint hq he) (headHandlePairNielsen j).backward
    PWord.gen (headHandlePairNielsen_backward_tau j) rfl
  have hid : PWord.subst PWord.gen (headHandlePairCompactW alpha j) =
      headHandlePairCompactW alpha j := by
    induction (headHandlePairCompactW alpha j) <;> simp_all
  simpa only [← headHandlePairCompactW_eq_nielsenBackward, hid] using H

theorem evalZ_headHandlePair_of_wild_tau_one
    {alpha h : ℕ} {C : Type*} [Group C]
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hwild : ∀ i, t.x i = 1) (htau : t.τ = 1) :
    PWord.evalZ ⇑t E E₂ (headHandlePairCompactW alpha j) = 1 := by
  rw [headHandlePairCompactW_eq_nielsenBackward, PWord.evalZ_subst]
  let s : Generator (2 + 2 * h) → C := fun g => t (headHandlePairSwap j g)
  have hm : (fun g => PWord.evalZ ⇑t E E₂ ((headHandlePairNielsen j).backward g)) = s := by
    funext g
    change t ((headHandlePairSwap j).symm g) = s g
    rw [headHandlePairSwap_symm]
  rw [hm]
  have hs : s .sigma = 1 := by
    change t (headHandlePairSwap j .sigma) = 1
    rw [headHandlePairSwap_sigma]
    exact hwild _
  have ht : s .tau = 1 := htau
  have hc : ∀ i : Fin 3, s (coreLetter h i) = 1 := by
    intro i
    rcases i with ⟨i, hi⟩
    interval_cases i
    · change t (headHandlePairSwap j (coreLetter h 0)) = 1
      simp only [headHandlePairSwap, Equiv.trans_apply, headHandleSwap_coreLetter,
        tailHandleSwap_coreZero]
      exact hwild _
    · change t (headHandlePairSwap j (coreLetter h 1)) = 1
      simp only [headHandlePairSwap, Equiv.trans_apply, headHandleSwap_coreLetter,
        tailHandleSwap_coreOne]
      exact hwild _
    · change t (headHandlePairSwap j (coreLetter h 2)) = 1
      rw [headHandlePairSwap_coreTwo]
      exact hwild _
  have hv : ∀ k : Fin h, s (handleV k) = 1 := by
    intro k
    by_cases hk : k = j
    · subst k
      change t (headHandlePairSwap j (handleV j)) = 1
      rw [headHandlePairSwap_handleV_self]
      exact hwild _
    · simp only [s, headHandlePairSwap, Equiv.trans_apply, headHandleSwap_handleV,
        tailHandleSwap_handleV, hk, if_false]
      exact hwild _
  have hh : PWord.evalZ s E E₂ (handlesW h) = 1 := by
    simp [handlesW, PWord.evalZ_prodList, List.map_map, Function.comp_def,
      PWord.evalZ_comm, PWord.evalZ_gen, hv]
  have htail : ((handleTailW h).map (PWord.evalZ s E E₂)).prod = 1 := by
    cases h with
    | zero => rfl
    | succ h => simpa [handleTailW] using hh
  simp [MCompact.mCompactW, PWord.evalZ_prodList,
    MCompact.mFactors, MCompact.a0W, sigma2W, MCompact.j2W, MCompact.eRevW,
    MCompact.deltaC, PWord.omega2Pow, PWord.evalZ_prodList, hs, ht, hc, htail,
    PWord.evalZ_zpow, PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_comm,
    PWord.evalZ_gen, PWord.evalZ_profPow]

theorem headHandlePairStokesDuality_pinned_unramified
    {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (j : Fin h)
    (hA₂ : ∀ a : A, a + a = 0) (hwild : ∀ i, t.x i = 1)
    (htau : t.τ = 1) (hq : Even q) (hα : 2 ≤ alpha)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    StokesDuality ⇑t (fun l : Fin 2 => heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C))
      (gammaFam (2 + 2 * h) q (headHandlePairCompactW alpha j) l)) A := by
  refine headHandlePairStokesDuality_unramified t j _ _ hA₂
    (by intro i a; rw [hwild, one_smul])
    (by intro a; rw [htau, one_smul]) hq hα hσfpf
    (omegaPinnedLevelZhatResolver_fourMulExponent_wordLift hA₂)
    (omegaPinnedLevelZhatResolver_fourMulExponent_wordLift (fun lam => lam.add_self_eq_zero))
    (omegaPinnedLevelZhatResolver_omega2 _) (omega2Exp_fourMulExponent_mod_four C) ?_ ?_
  · intro l
    rw [← evalZ_eq_lift_heisToFree]
    fin_cases l
    · change PWord.evalZ ⇑t _ _ (tameRelW _ q) = 1
      simp [tameRelW, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
        PWord.evalZ_zpow, PWord.evalZ_gen, show t .tau = 1 from htau]
    · exact evalZ_headHandlePair_of_wild_tau_one t j _ _ hwild htau
  · apply headHandlePair_isStokesEndpoint j _ _ hq
    rw [omegaPinnedLevelZhatResolver_omega2]
    exact_mod_cast (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
      (fourMulExponent_ne_zero_and_even C).2)

theorem freeSubstMark_wildShear_eq_of_powOmega2_eq_one
    {n : ℕ} {C : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    (t : Marking n C) (k : Fin (n + 1) → ℤ_[2])
    (hσ : powOmega2 t.σ = 1) :
    freeSubstMark ⇑t (fun g => heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C))
      ((wildShearNielsen k).backward g)) = ⇑t := by
  funext g
  cases g with
  | sigma => change FreeGroup.lift ⇑t (FreeGroup.of .sigma) = _; simp
  | tau => change FreeGroup.lift ⇑t (FreeGroup.of .tau) = _; simp
  | wild i =>
      change FreeGroup.lift ⇑t (FreeGroup.of (.wild i) *
        FreeGroup.of .sigma ^ omegaPinnedLevelZhatResolver
          (4 * Monoid.exponent C) (padicOmega2 (k i))) = _
      simp only [map_mul, map_zpow, FreeGroup.lift_apply_of]
      rw [omegaPinnedLevelZhatResolver_spec (fourMulExponent_ne_zero_and_even C).1
        (fun c : C => (Monoid.order_dvd_exponent c).trans (dvd_mul_left _ _))]
      rw [zpowHat_padicOmega2, padicOmega2Exp, mul_comm, pow_mul]
      change t (.wild i) * powOmega2 t.σ ^ _ = t (.wild i)
      rw [hσ, one_pow, mul_one]

theorem headHandlePairNormalizedStokesDuality_pinned_unramified
    {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a + a = 0) (hwild : ∀ i, t.x i = 1)
    (htau : t.τ = 1) (hσ : powOmega2 t.σ = 1) (hq : Even q) (hα : 2 ≤ alpha)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    StokesDuality ⇑t (fun l : Fin 2 => heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C))
      (gammaFam (2 + 2 * h) q (headHandlePairNormalizedW alpha h halpha j nuP) l)) A := by
  unfold headHandlePairNormalizedW
  apply (stokesDuality_wildShearBackward_iff _ _ _ _ _
    (headHandlePair_isStokesEndpoint j _ _ hq (by
      rw [omegaPinnedLevelZhatResolver_omega2]
      exact_mod_cast (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
        (fourMulExponent_ne_zero_and_even C).2)))).mpr
  rw [freeSubstMark_wildShear_eq_of_powOmega2_eq_one t _ hσ]
  exact headHandlePairStokesDuality_pinned_unramified t j hA₂ hwild htau hq hα hσfpf

theorem headHandlePairPrimeStokesDuality_pinned_unramified
    {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a + a = 0) (hwild : ∀ i, t.x i = 1)
    (htau : t.τ = 1) (hσ : powOmega2 t.σ = 1)
    (hq0 : q ≠ 0) (hq : Even q) (hα : 2 ≤ alpha)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    StokesDuality ⇑t (fun l : Fin 2 => heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C))
      (gammaFam (2 + 2 * h) q
        (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP) l)) A := by
  unfold headHandlePairPrimeCorrectedW tamePrimeToTwoCorrectedWord
  apply (stokesDuality_gammaFam_tameCorrection_iff_of_trivial_tau _ _ _ _ _ hA₂
    (by intro a; rw [show t .tau = 1 from htau, one_smul])
    (omegaPinnedLevelZhatResolver_four_dvd_tameCorrection
      (fourMulExponent_ne_zero_and_even C).1 (dvd_mul_right _ _) hq0 hq _ _)).mpr
  exact headHandlePairNormalizedStokesDuality_pinned_unramified t halpha j nuP
    hA₂ hwild htau hσ hq hα hσfpf

#print axioms headHandlePairStokesDuality_pinned_unramified
#print axioms freeSubstMark_wildShear_eq_of_powOmega2_eq_one
#print axioms headHandlePairNormalizedStokesDuality_pinned_unramified
#print axioms headHandlePairPrimeStokesDuality_pinned_unramified
#print axioms headHandlePair_isStokesEndpoint
#print axioms evalZ_headHandlePair_of_wild_tau_one
end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalizedUnramified

