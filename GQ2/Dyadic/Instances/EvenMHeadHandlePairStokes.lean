/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairTame
import GQ2.Dyadic.Instances.FiniteStokesResolver

/-!
# Uniform Stokes data for the normalized even-M source

The all-rank head-handle normalization is obtained from compact `M` by two substitutions which
fix `tau`.  Its mod-two endpoint therefore agrees with compact `M`.  Combining this observation
with the prime-to-two tame correction and the universal finite resolver gives, for every finite
target, a single resolved relator family satisfying the Stokes endpoint.

The construction is uniform in the rank, handle count, word, and finite target.  No frozen
class, field, or finite-stage argument occurs here.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates
open GQ2.Dyadic.Certificates.MCompact
open GQ2.Dyadic.Words
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairCore
open GQ2.Dyadic.Instances.GammaRPWordNielsen
open GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

theorem heisEps_heisToFree_subst_tameRelW
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (n q : ℕ)
    (phi : Generator n → PWord (Generator n))
    (htau : phi Generator.tau = .gen Generator.tau) (i : Generator n) :
    heisEps i (heisToFree E E₂ (PWord.subst phi (tameRelW n q))) =
      heisEps i (heisToFree E E₂ (tameRelW n q)) := by
  rw [heisToFree, PWord.evalZ_subst, tameRelW,
    PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
    PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen,
    map_mul, map_conjR, conjR_eq_self_of_comm, map_inv, map_zpow]
  rw [htau, PWord.evalZ_gen]
  rw [PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
    PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen,
    map_mul, map_conjR, conjR_eq_self_of_comm, map_inv, map_zpow]

theorem mCompactOf_isStokesEndpoint
    {alpha h q : ℕ} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    (hqe : Even q) (he : Odd (E omega2)) :
    IsStokesEndpoint (fun l : Fin 2 ↦
      heisToFree E E₂ (gammaFam (2 + 2 * h) q (mCompactW alpha h) l)) := by
  intro i
  rw [Fin.sum_univ_two]
  simp only [gammaFam_zero, gammaFam_one]
  have htame : heisEps i (heisToFree E E₂ (tameRelW (2 + 2 * h) q))
      = heisEps i (FreeGroup.of Generator.tau)
        * (heisEps i (FreeGroup.of Generator.tau) ^ (q : ℤ))⁻¹ := by
    rw [tameRelW, heisToFree, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
      PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR,
      conjR_eq_self_of_comm, map_inv, map_zpow]
  have hwild : heisEps i (heisToFree E E₂ (mCompactW alpha h))
      = (heisEps i (FreeGroup.of (coreLetter h 2)))⁻¹
        * (heisEps i (FreeGroup.of (coreLetter h 2))
            * heisEps i (FreeGroup.of Generator.tau)) ^ (E omega2 : ℤ) := by
    rw [mCompactW, heisToFree, PWord.evalZ_prodList, List.map_append, List.prod_append]
    simp only [mFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      map_mul]
    rw [PWord.evalZ_zpow, heisEps_sq, PWord.evalZ_comm, monoidHom_commR_eq_one,
      PWord.evalZ_zpow, heisEps_even_zpow, heisEps_eRevW,
      show ((handleTailW h).map (PWord.evalZ FreeGroup.of E E₂)).prod
        = PWord.evalZ FreeGroup.of E E₂ (handlesW h) by
        cases h with
        | zero => rfl
        | succ n => simp only [handleTailW, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil, mul_one],
      handlesW_eq, Certificates.heisEps_handlesW]
    simp only [one_mul, mul_one]
    rw [show j2W h = PWord.mul (.inv (.conj (.gen (coreLetter h 2)) (.gen .sigma)))
        (PWord.mul (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]))
          PWord.one) from rfl]
    rw [PWord.evalZ_mul, PWord.evalZ_mul, PWord.evalZ_one, mul_one, map_mul,
      PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, PWord.evalZ_gen, map_inv,
      map_conjR, conjR_eq_self_of_comm, PWord.omega2Pow, PWord.evalZ_profPow, map_zpow,
      PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalZ_mul,
      PWord.evalZ_mul, PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_one, mul_one, map_mul]
  rw [htame, hwild]
  simp only [Certificates.heisEps_of, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd]
  rw [zsmul_natCast_zmod2_even hqe, zsmul_zmod2_odd he, CharTwo.neg_eq, CharTwo.neg_eq]
  abel_nf
  simp [CharTwo.two_eq_zero]

theorem mCompact_stokesResolver_isStokesEndpoint
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {alpha h q : ℕ} (hqe : Even q) :
    IsStokesEndpoint (fun l : Fin 2 ↦
      heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q)
        (gammaFam (2 + 2 * h) q (mCompactW alpha h) l)) := by
  exact mCompactOf_isStokesEndpoint hqe (stokesZhatResolver_omega2_odd Q)

theorem isStokesEndpoint_gammaFam_subst_subst_of_tau
    {n q : ℕ} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    (R : PWord (Generator n))
    (H0 : IsStokesEndpoint (fun l : Fin 2 ↦
      heisToFree E E₂ (gammaFam n q R l)))
    (phi psi : Generator n → PWord (Generator n))
    (hphi : phi Generator.tau = .gen Generator.tau)
    (hpsi : psi Generator.tau = .gen Generator.tau) :
    IsStokesEndpoint (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam n q (PWord.subst psi (PWord.subst phi R)) l)) := by
  have H1 := isStokesEndpoint_heisToFree_subst H0 phi
  have H2 := isStokesEndpoint_heisToFree_subst H1 psi
  intro i
  have H := H2 i
  rw [Fin.sum_univ_two] at H ⊢
  simp only [gammaFam_zero, gammaFam_one] at H ⊢
  have htameBoth : heisEps i
      (heisToFree E E₂
        (PWord.subst psi (PWord.subst phi (tameRelW n q)))) =
      heisEps i (heisToFree E E₂ (tameRelW n q)) := by
    rw [GQ2.Dyadic.Certificates.MProcyclic.subst_subst]
    apply heisEps_heisToFree_subst_tameRelW
    rw [hphi, PWord.subst_gen, hpsi]
  rw [← htameBoth]
  exact H

theorem headHandlePairNormalized_stokesResolver_isStokesEndpoint
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    IsStokesEndpoint (fun l : Fin 2 ↦
      heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q)
        (gammaFam (2 + 2 * h) q
          (headHandlePairNormalizedW alpha h halpha j nuP) l)) := by
  let k := wildNuCoefficient nuP
    (headHandlePairCorePresentation alpha h halpha j).mark
  let pairPhi := (headHandlePairNielsen j).backward
  let wildPhi := (wildShearNielsen k).backward
  have htauPair : pairPhi (.tau : Generator (2 + 2 * h)) = .gen .tau := by
    exact headHandlePairNielsen_backward_tau j
  have htauWild : wildPhi (.tau : Generator (2 + 2 * h)) = .gen .tau := by
    rfl
  have hword : headHandlePairNormalizedW alpha h halpha j nuP =
      PWord.subst wildPhi (PWord.subst pairPhi (mCompactW alpha h)) := by
    rw [headHandlePairNormalizedW]
    change PWord.subst wildPhi (headHandlePairCompactW alpha j) = _
    rw [headHandlePairCompactW_eq_nielsenBackward]
  rw [hword]
  exact isStokesEndpoint_gammaFam_subst_subst_of_tau (mCompactW alpha h)
    (mCompact_stokesResolver_isStokesEndpoint hqe) pairPhi wildPhi htauPair htauWild

noncomputable def headHandlePairPrimeCorrectedW
    (alpha h q : ℕ) (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    PWord (Generator (2 + 2 * h)) :=
  tamePrimeToTwoCorrectedWord hq0 hqe
    (headHandlePairNormalizedW alpha h halpha j nuP)
    (tame_eval_headHandlePairNormalized_mem_inertia (q := q) halpha j nuP)

theorem headHandlePairPrimeCorrectedW_specializes
    (alpha h q : ℕ) (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    TameSpec.TameSpecializes (2 + 2 * h) q
      (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP) := by
  exact tamePrimeToTwoCorrectedWord_specializes hq0 hqe _ _

noncomputable def headHandlePairPrimeCorrectedFlexibleCore
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hU : nuP (dmGen alpha h (handleIdxU j)) = ztwoOne) :
    FlexibleCoreLeavesRN (2 + 2 * h)
      (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP)
      (DM alpha h) nuP := by
  let C := headHandlePairNormalizedFlexibleCore halpha j nuP hU
  refine
    { presentation := CorePresentation.ofPrimeToTwoTameCorrection C.presentation
        hq0 hqe (tame_eval_headHandlePairNormalized_mem_inertia (q := q) halpha j nuP)
      nu_sigma := C.nu_sigma
      nu_wild := C.nu_wild }

noncomputable def headHandlePairPrimeResolvedFamily
    (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (alpha h q : ℕ) (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  fun l ↦ heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q)
    (gammaFam (2 + 2 * h) q
      (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP) l)

theorem resolvesAt_and_endpoint_headHandlePairPrime
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    ResolvesAt
        (gammaFam (2 + 2 * h) q
          (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP))
        (headHandlePairPrimeResolvedFamily Q alpha h q halpha hq0 hqe j nuP) Q ∧
      IsStokesEndpoint
        (headHandlePairPrimeResolvedFamily Q alpha h q halpha hq0 hqe j nuP) := by
  constructor
  · exact resolvesAt_stokesResolvers Q _
  · apply isStokesEndpoint_primeToTwoCorrection Q hq0 hqe
    exact headHandlePairNormalized_stokesResolver_isStokesEndpoint halpha hqe j nuP

#print axioms heisEps_heisToFree_subst_tameRelW
#print axioms mCompact_stokesResolver_isStokesEndpoint
#print axioms headHandlePairNormalized_stokesResolver_isStokesEndpoint
#print axioms headHandlePairPrimeCorrectedW_specializes
#print axioms headHandlePairPrimeCorrectedFlexibleCore
#print axioms resolvesAt_and_endpoint_headHandlePairPrime

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize
