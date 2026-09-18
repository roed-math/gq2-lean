/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalizedUnramified
import GQ2.Dyadic.Instances.TameSpliceActionImage
import GQ2.Dyadic.TameSpliceUnramifiedStokes
import GQ2.Dyadic.Instances.N0M0CompactBranches
import GQ2.Dyadic.Instances.EvenMHeadHandlePairScalar

/-!
# Complete finite-coefficient Stokes supply for the normalized M0 splice

The structural source is the genuinely normalized, prime-to-two-corrected pair word.
Its unramified scalar and sigma-fixed-point-free branches are transported through the
actual wild shear, then through the tame splice. The independent compact-M ramified
supply and action-image devissage complete Stokes duality for every finite elementary
coefficient. All statements are uniform in the rank and contain no class table or
residual row, pairing, or Stokes hypothesis.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairSplice
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates Words Certificates.MProcyclic
open Instances.EvenMHeadHandlePairSource Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNormalize Instances.EvenMHeadHandlePairUnramified
open Instances.EvenMHeadHandlePairNormalizedUnramified
open Instances.EvenMHeadHandlePairScalar
open Instances.GammaRCorePresentationNuNormalize
open GQ2.Dyadic.MarkedCore RowActionImage

theorem headHandlePairPrime_pinned_endpoint
    {alpha h q N : ℕ} (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hq : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0) :
    IsStokesEndpoint (pinnedResolvedFamily (2 + 2 * h) q
      (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP) N) := by
  let E := omegaPinnedLevelZhatResolver N
  let E₂ := omegaPinnedLevelZtwoResolver N
  let R := headHandlePairNormalizedW alpha h halpha j nuP
  let hR := tame_eval_headHandlePairNormalized_mem_inertia (q := q) halpha j nuP
  let k := wildNuCoefficient nuP (headHandlePairCorePresentation alpha h halpha j).mark
  have he : Odd (E omega2) := by
    dsimp [E]
    rw [omegaPinnedLevelZhatResolver_omega2]
    exact_mod_cast odd_omega2Exp hN hNtwo
  have hnorm : IsStokesEndpoint (fun l : Fin 2 => heisToFree E E₂
      (gammaFam (2 + 2 * h) q R l)) := by
    have H := isStokesEndpoint_gammaFam_subst_subst_of_tau (E₂ := E₂)
      (MCompact.mCompactW alpha h) (mCompactOf_isStokesEndpoint hq he)
      (headHandlePairNielsen j).backward (wildShearNielsen k).backward
      (headHandlePairNielsen_backward_tau j) rfl
    simpa only [R, headHandlePairNormalizedW, ← headHandlePairCompactW_eq_nielsenBackward] using H
  have htwo : 2 ∣ N := by
    by_contra hh
    exact hNtwo (Nat.factorization_eq_zero_of_not_dvd hh)
  have hcorr : Even (E (tamePrimeToTwoCorrectionExponent hq0 hq R hR)) := by
    apply even_iff_two_dvd.mpr
    exact omegaPinnedLevelZhatResolver_twoPow_dvd_of_primeToTwo (a := 1) hN htwo
      (maxProPMk_tamePrimeToTwoCorrectionExponent hq0 hq R hR)
  intro i
  have H := hnorm i
  rw [Fin.sum_univ_two] at H ⊢
  change Multiplicative.toAdd (heisEps i (heisToFree E E₂ (tameRelW _ q))) +
    Multiplicative.toAdd (heisEps i (heisToFree E E₂
      (tamePrimeToTwoCorrectedWord hq0 hq R hR))) = 0
  have heps : heisEps i (heisToFree E E₂
      (tamePrimeToTwoCorrectedWord hq0 hq R hR)) = heisEps i (heisToFree E E₂ R) := by
    rw [tamePrimeToTwoCorrectedWord, heisToFree, PWord.evalZ_mul, PWord.evalZ_inv,
      PWord.evalZ_profPow, PWord.evalZ_gen, map_mul, map_inv, map_zpow,
      mult_zmod2_even_zpow _ hcorr, inv_one, mul_one]
  rw [heps]
  exact H

theorem heisD1_headHandlePairNormalized_surjective
    {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a + a = 0) (hwild : ∀ i, t.x i = 1)
    (htau : t.τ = 1) (hσ : powOmega2 t.σ = 1) (hq : Even q)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    Function.Surjective (heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2 + 2 * h) q
        (headHandlePairNormalizedW alpha h halpha j nuP) (4 * Monoid.exponent C))) := by
  let E := omegaPinnedLevelZhatResolver (4 * Monoid.exponent C)
  let E₂ := omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)
  let k := wildNuCoefficient nuP (headHandlePairCorePresentation alpha h halpha j).mark
  let phi := fun g => heisToFree E E₂ ((wildShearNielsen k).backward g)
  let psi := fun g => heisToFree E E₂ ((wildShearNielsen k).forward g)
  let w := pinnedResolvedFamily (2 + 2 * h) q (headHandlePairCompactW alpha j)
    (4 * Monoid.exponent C)
  have hs : Function.Surjective (heisD1 (A := A) ⇑t w) :=
    heisD1_surjective_of_unramified_row t w
      (heisD1_headHandlePair_unram_apply t j E E₂ hA₂
        (by intro i a; rw [hwild, one_smul])
        (by intro a; rw [htau, one_smul]) hq
        (omegaPinnedLevelZhatResolver_fourMulExponent_wordLift hA₂)) hσfpf
  let e := freeSubstPrimalEquiv (A := A) ⇑t phi psi
    (wildShear_resolved_backward_forward k E E₂) (wildShear_resolved_forward_backward k E E₂)
  intro v
  obtain ⟨u, hu⟩ := hs v
  obtain ⟨x, hx⟩ := e.surjective u
  refine ⟨x, ?_⟩
  have hd := heisD1_freeSubst ⇑t w phi x
  rw [show freeSubstMark ⇑t phi = ⇑t from
    freeSubstMark_wildShear_eq_of_powOmega2_eq_one t k hσ] at hd
  change freeSubstPrimal ⇑t phi x = u at hx
  rw [hx, hu] at hd
  have hw : pinnedResolvedFamily (2 + 2 * h) q
      (headHandlePairNormalizedW alpha h halpha j nuP) (4 * Monoid.exponent C) =
      fun l => FreeGroup.lift phi (w l) := by
    funext l
    exact congrArg (heisToFree E E₂) (gammaFam_subst_wildShearBackward k _ l) |>.trans
      (heisToFree_subst E E₂ _ _)
  rw [hw]
  exact hd

theorem heisD1_headHandlePairPrime_surjective
    {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a + a = 0) (hwild : ∀ i, t.x i = 1)
    (htau : t.τ = 1) (hσ : powOmega2 t.σ = 1) (hq0 : q ≠ 0) (hq : Even q)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) :
    Function.Surjective (heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2 + 2 * h) q
        (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP)
          (4 * Monoid.exponent C))) := by
  unfold pinnedResolvedFamily headHandlePairPrimeCorrectedW tamePrimeToTwoCorrectedWord
  rw [heisD1_gammaFam_tameCorrection_of_trivial_tau _ _ _ _ _ hA₂
    (by intro a; rw [show t .tau = 1 from htau, one_smul])
    (omegaPinnedLevelZhatResolver_four_dvd_tameCorrection
      (fourMulExponent_ne_zero_and_even C).1 (dvd_mul_right _ _) hq0 hq _ _)]
  exact heisD1_headHandlePairNormalized_surjective t halpha j nuP
    hA₂ hwild htau hσ hq hσfpf

theorem headHandlePairPrimeStokesDuality_pinned_scalar
    {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a + a = 0) (hwild : ∀ i, t.x i = 1)
    (htau : t.τ = 1) (hσ : powOmega2 t.σ = 1)
    (hq0 : q ≠ 0) (hq : Even q) (hα : 2 ≤ alpha)
    (hσtriv : ∀ a : A, t.σ • a = a) :
    StokesDuality ⇑t (pinnedResolvedFamily (2 + 2 * h) q
      (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP)
        (4 * Monoid.exponent C)) A := by
  unfold pinnedResolvedFamily headHandlePairPrimeCorrectedW tamePrimeToTwoCorrectedWord
  apply (stokesDuality_gammaFam_tameCorrection_iff_of_trivial_tau _ _ _ _ _ hA₂
    (by intro a; rw [show t .tau = 1 from htau, one_smul])
    (omegaPinnedLevelZhatResolver_four_dvd_tameCorrection
      (fourMulExponent_ne_zero_and_even C).1 (dvd_mul_right _ _) hq0 hq _ _)).mpr
  unfold headHandlePairNormalizedW
  apply (stokesDuality_wildShearBackward_iff _ _ _ _ _
    (headHandlePair_isStokesEndpoint j _ _ hq (by
      rw [omegaPinnedLevelZhatResolver_omega2]
      exact_mod_cast (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
        (fourMulExponent_ne_zero_and_even C).2)))).mpr
  rw [freeSubstMark_wildShear_eq_of_powOmega2_eq_one t _ hσ]
  exact headHandlePairStokesDuality_pinned_scalar t j hA₂ hwild htau hq hα hσtriv

private theorem evalZ_one_of_mark_one {n : ℕ} {C : Type*} [Group C]
    (t : Marking n C) (ht : ∀ g, t g = 1) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (w : PWord (Generator n)) : PWord.evalZ ⇑t E E₂ w = 1 := by
  induction w <;> simp_all [PWord.evalZ]

/-- The corrected, normalized pair source supplies the unramified half of its tame splice
on every simple finite action image, with no residual row or pairing premise. -/
theorem unramifiedActionImageStokes_headHandlePairSplice
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hα : 2 ≤ alpha)
    (hq0 : q ≠ 0) (hq : Even q) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    let R := headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP
    UnramifiedActionImageStokes (2 + 2 * h) q (tameSplice R (MCompact.mCompactW alpha h))
      (pinnedResolvedFamily (2 + 2 * h) q (tameSplice R (MCompact.mCompactW alpha h))) := by
  dsimp only
  let R := headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP
  let W := tameSplice R (MCompact.mCompactW alpha h)
  intro M _ _ _ _ _ _ hM₂ hsimple hτ
  let C := ActionImage (2 + 2 * h) q W M
  let t := actionImageMarking (2 + 2 * h) q W M
  let E := omegaPinnedLevelZhatResolver (4 * Monoid.exponent C)
  let E₂ := omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)
  have hwild : ∀ i, t.x i = 1 := fun i =>
    actionImage_eq_one_of_smul_eq (t.x i) (actionImage_wild_smul hM₂ hsimple i)
  have htau : t.τ = 1 := actionImage_eq_one_of_smul_eq t.τ hτ
  have hσ : powOmega2 t.σ = 1 := actionImage_eq_one_of_smul_eq _
    (actionImage_sigma_powOmega2_smul_trivial hM₂ hsimple hτ)
  have hend : IsStokesEndpoint (pinnedResolvedFamily (2 + 2 * h) q R
      (4 * Monoid.exponent C)) := headHandlePairPrime_pinned_endpoint halpha hq0 hq j nuP
    (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2
  rcases actionImage_sigma_split_or_fixedPointFree hM₂ hsimple hτ with hscalar | hfpf
  · have htriv : ∀ (g : Generator (2 + 2 * h)) (a : M), t g • a = a := by
      intro g a
      cases g with
      | sigma => exact hscalar a
      | tau => change t.τ • a = a; rw [htau, one_smul]
      | wild i => change t.x i • a = a; rw [hwild, one_smul]
    have ht : ∀ g, t g = 1 := fun g => actionImage_eq_one_of_smul_eq _ (htriv g)
    have hdeath (Q : PWord (Generator (2 + 2 * h))) :
        ∀ l, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam (2 + 2 * h) q Q l)) = 1 := by
      intro l
      rw [← evalZ_eq_lift_heisToFree]
      exact evalZ_one_of_mark_one t ht E E₂ _
    exact stokesDuality_tameSplice_of_trivial_action t E E₂ hM₂ htriv hq
      (omegaPinnedLevelZhatResolver_omega2 _) (omega2Exp_fourMulExponent_mod_four C)
      R (MCompact.mCompactW alpha h) (hdeath R) (hdeath W) hend
      (isStokesEndpoint_tameSplice hend (pinned_mCompact_endpoint hq
        (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2))
      (headHandlePairPrimeStokesDuality_pinned_scalar t halpha j nuP hM₂ hwild htau hσ
        hq0 hq hα hscalar)
  · apply stokesDuality_tameSplice_unramified_of_surjective t E E₂ hM₂
      (by intro i a; rw [hwild, one_smul])
      (by intro a; rw [htau, one_smul]) hq
      (omegaPinnedLevelZhatResolver_omega2 _) (omega2Exp_fourMulExponent_mod_four C)
      R (MCompact.mCompactW alpha h)
    · exact heisD1_headHandlePairPrime_surjective t halpha j nuP
        hM₂ hwild htau hσ hq0 hq hfpf
    · exact heisD1_headHandlePairPrime_surjective t halpha j nuP
        (fun lam => lam.add_self_eq_zero) hwild htau hσ hq0 hq
        (fun lam hlam => elemDual_fpf hfpf lam hlam)
    · exact headHandlePairPrimeStokesDuality_pinned_unramified t halpha j nuP
        hM₂ hwild htau hσ hq0 hq hα hfpf

/-- All finite elementary coefficients are now supplied for the rank-uniform M0 splice. -/
theorem pushedStokesDuality_headHandlePairSplice
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hα : 2 ≤ alpha)
    (hq0 : q ≠ 0) (hq : Even q) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (tameSplice
        (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP)
        (MCompact.mCompactW alpha h))) : Type) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g => rho (gammaGen (2 + 2 * h) q (tameSplice
      (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP)
      (MCompact.mCompactW alpha h)) g))
      (pinnedResolvedFamily (2 + 2 * h) q (tameSplice
        (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hq j nuP)
        (MCompact.mCompactW alpha h)) (4 * Monoid.exponent C)) A :=
  pushedStokesDuality_tameSplice_mCompact hq0 hq
    (headHandlePairPrimeCorrectedW_specializes alpha h q halpha hq0 hq j nuP)
    (fun _N hN hNtwo => headHandlePairPrime_pinned_endpoint halpha hq0 hq j nuP hN hNtwo)
    (unramifiedActionImageStokes_headHandlePairSplice halpha hα hq0 hq j nuP) rho A hA₂

#print axioms headHandlePairPrimeStokesDuality_pinned_scalar
#print axioms unramifiedActionImageStokes_headHandlePairSplice
#print axioms pushedStokesDuality_headHandlePairSplice
#print axioms headHandlePairPrime_pinned_endpoint
#print axioms heisD1_headHandlePairNormalized_surjective
#print axioms heisD1_headHandlePairPrime_surjective
end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairSplice

