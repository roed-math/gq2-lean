/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMobileNuSource
import GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes
import GQ2.Dyadic.Instances.OmegaPinnedLevelResolverParity
import GQ2.Dyadic.Instances.TameCorrectionStokes
import GQ2.Dyadic.Instances.TameSpliceActionImage
import GQ2.Dyadic.TameSpliceUnramifiedStokes
import GQ2.Dyadic.Instances.GammaRUniformStokesSupply

/-!
# Uniform Stokes supply for the mobile Mpc tame splice

The normalized, tame-corrected Mpc word supplies the unramified branch; the compact-M
template supplies the ramified branch through the tame splice. Both the profinite word and
the integer family at each finite level are independent of the coefficient module.
-/

namespace GQ2.Dyadic.Instances.MpcMobileSpliceSupply
noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.Words GQ2.Dyadic.RowActionImage
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Instances.MpcMobileNuSource
open GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

private theorem d1_surjective_of_stokes_of_sigma_fpf
    {n : ℕ} {C A : Type} [Group C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking n C) (w : Fin 2 → FreeGroup (Generator n))
    (hσ : ∀ a : A, t.σ • a = a → a = 0) (H : StokesDuality ⇑t w A) :
    Function.Surjective (heisD1 (A := A) ⇑t w) := by
  have hinj := heisD0_injective_of_sigma_fixedPointFree (A := ElemDual A) t
    (elemDual_fpf hσ)
  have hsurj := dualMap_surjective
    (fun x : Generator n → ElemDual A ↦ funext fun g ↦ (x g).add_self_eq_zero)
    (heisD0 (A := ElemDual A) ⇑t) hinj
  intro x
  exact H.h2_inj x (hsurj _)

private theorem pinned_relators_of_eval
    {n q : ℕ} {C : Type} [Group C] [Finite C] [TopologicalSpace C] [DiscreteTopology C]
    (t : Marking n C) (R : PWord (Generator n)) (ht : t.TameRelAt q)
    (hR : t.eval R = 1) :
    ∀ l, FreeGroup.lift ⇑t (pinnedResolvedFamily n q R (4 * Monoid.exponent C) l) = 1 := by
  intro l
  unfold pinnedResolvedFamily
  rw [← evalZ_eq_lift_heisToFree]
  rw [← PWord.eval_eq_evalZ _ _ _ _
    (resolvedAt_omegaPinnedLevelResolvers (fourMulExponent_ne_zero_and_even C).1
      (fun c : C ↦ (Monoid.order_dvd_exponent c).trans (dvd_mul_left _ _)) _ _)]
  fin_cases l
  · change t.eval (tameRelW n q) = 1
    rw [Certificates.eval_tameRelW, ht, mul_inv_cancel]
  · exact hR

/-- Prime-to-two tame correction preserves the pinned endpoint at every nonzero even level. -/
theorem pinned_endpoint_tameCorrection
    {n q N : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (R : PWord (Generator n)) (hR : (tameMarking n q).eval R ∈ inertiaPartQ q)
    (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0)
    (hend : IsStokesEndpoint (pinnedResolvedFamily n q R N)) :
    IsStokesEndpoint (pinnedResolvedFamily n q (tamePrimeToTwoCorrectedWord hq0 hqe R hR) N) := by
  have htwo : 2 ∣ N := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hN).mpr
    (Nat.one_le_iff_ne_zero.mpr hNtwo)
  have heven : Even (omegaPinnedLevelZhatResolver N
      (tamePrimeToTwoCorrectionExponent hq0 hqe R hR)) := by
    apply even_iff_two_dvd.mpr
    exact omegaPinnedLevelZhatResolver_twoPow_dvd_of_primeToTwo (a := 1) hN htwo
      (maxProPMk_tamePrimeToTwoCorrectionExponent hq0 hqe R hR)
  intro i
  have H := hend i
  rw [Fin.sum_univ_two] at H ⊢
  have heps : heisEps i (heisToFree (omegaPinnedLevelZhatResolver N)
      (omegaPinnedLevelZtwoResolver N) (tamePrimeToTwoCorrectedWord hq0 hqe R hR)) =
      heisEps i (heisToFree (omegaPinnedLevelZhatResolver N)
        (omegaPinnedLevelZtwoResolver N) R) := by
    rw [tamePrimeToTwoCorrectedWord, heisToFree, PWord.evalZ_mul,
      PWord.evalZ_inv, PWord.evalZ_profPow, PWord.evalZ_gen,
      map_mul, map_inv, map_zpow,
      Certificates.MProcyclic.mult_zmod2_even_zpow _ heven]
    simp
  change Multiplicative.toAdd (heisEps i
      (heisToFree (omegaPinnedLevelZhatResolver N) (omegaPinnedLevelZtwoResolver N)
        (tameRelW n q))) + Multiplicative.toAdd (heisEps i
      (heisToFree (omegaPinnedLevelZhatResolver N) (omegaPinnedLevelZtwoResolver N)
        (tamePrimeToTwoCorrectedWord hq0 hqe R hR))) = 0
  rw [heps]
  exact H

/-- The actual corrected mobile source has the endpoint uniformly in the finite level. -/
theorem mpcMobileTameCorrected_endpoint
    {alpha r p h q N : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0) :
    IsStokesEndpoint (pinnedResolvedFamily (2 + 2 * h) q
      (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) N) := by
  apply pinned_endpoint_tameCorrection hq0 hqe _ _ hN hNtwo
  exact mpcUnitShearedLevelFamily_endpoint eta _ halpha hqe hN hNtwo

private theorem normalized_relators_unramified
    {alpha r p h q : ℕ} {C : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    (t : Marking (2 + 2 * h) C) (hq0 : q ≠ 0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (ht : t.TameRelAt q) (hwild : ∀ i, t.x i = 1) (htau : t.τ = 1) :
    ∀ l, FreeGroup.lift ⇑t (pinnedResolvedFamily (2 + 2 * h) q
      (mpcMobileNormalizedW alpha r p h eta halpha nuP) (4 * Monoid.exponent C) l) = 1 := by
  apply pinned_relators_of_eval t _ ht
  have H := eval_eq_one_of_tameSpecializes_of_wild_eq_one t ht hwild
    (mpcMobileTameCorrectedW_specializes (r := r) (p := p) hq0 hqe eta halpha nuP)
  have hone (z : Zhat) : (1 : C) ^ᶻ z = 1 := by
    have hfun : (fun w : Zhat ↦ (1 : C) ^ᶻ w) = fun _ ↦ 1 := by
      apply Zhat.funext_ofInt (continuous_zpowHat _) continuous_const
      intro k
      rw [zpowHat_ofInt, one_zpow]
    exact congrFun hfun z
  simpa only [mpcMobileTameCorrectedW, tamePrimeToTwoCorrectedWord,
    Marking.eval_mul, Marking.eval_inv, Marking.eval_profPow, Marking.eval_gen,
    show t .tau = 1 from htau, hone, inv_one, mul_one] using H

/-- The corrected mobile source supplies the sigma-fixed-point-free unramified branch. -/
theorem mpcMobileTameCorrected_stokes_unramified_fpf
    {alpha r p h q : ℕ} {C A : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hq0 : q ≠ 0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a + a = 0) (ht : t.TameRelAt q)
    (hwild : ∀ i, t.x i = 1) (htau : t.τ = 1)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0) (hσodd : Odd (orderOf t.σ)) :
    StokesDuality ⇑t (pinnedResolvedFamily (2 + 2 * h) q
      (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
      (4 * Monoid.exponent C)) A := by
  unfold pinnedResolvedFamily mpcMobileTameCorrectedW tamePrimeToTwoCorrectedWord
  apply (stokesDuality_gammaFam_tameCorrection_iff_of_trivial_tau _ _ _ _ _ hA₂
    (by intro a; rw [show t .tau = 1 from htau, one_smul])
    (omegaPinnedLevelZhatResolver_four_dvd_tameCorrection
      (fourMulExponent_ne_zero_and_even C).1 (dvd_mul_right _ _) hq0 hqe _ _)).mpr
  apply stokesDuality_mpcUnit_sheared_unramified_fpf_uniform t eta _ hA₂ halpha hqe
  · intro i a
    rw [hwild, one_smul]
  · intro a
    rw [htau, one_smul]
  · exact hσfpf
  · exact hσodd
  · exact normalized_relators_unramified t hq0 hqe eta halpha nuP ht hwild htau

/-- The corrected mobile source supplies the scalar branch, uniformly for alpha at least two. -/
theorem mpcMobileTameCorrected_stokes_scalar
    {alpha r p h q : ℕ} {C A : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hq0 : q ≠ 0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA₂ : ∀ a : A, a + a = 0) (halpha2 : 2 ≤ alpha) (ht : t.TameRelAt q)
    (hwild : ∀ i, t.x i = 1) (htau : t.τ = 1)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (a : A), t g • a = a) :
    StokesDuality ⇑t (pinnedResolvedFamily (2 + 2 * h) q
      (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
      (4 * Monoid.exponent C)) A := by
  unfold pinnedResolvedFamily mpcMobileTameCorrectedW tamePrimeToTwoCorrectedWord
  apply (stokesDuality_gammaFam_tameCorrection_iff_of_trivial_tau _ _ _ _ _ hA₂
    (htriv .tau) (omegaPinnedLevelZhatResolver_four_dvd_tameCorrection
      (fourMulExponent_ne_zero_and_even C).1 (dvd_mul_right _ _) hq0 hqe _ _)).mpr
  apply stokesDuality_mpcUnit_sheared_scalar_uniform t eta _ hA₂ halpha2 hqe htriv
  exact normalized_relators_unramified t hq0 hqe eta halpha nuP ht hwild htau

/-- The full unramified simple action-image branch for the actual mobile Mpc splice. -/
theorem unramifiedActionImageStokes_mpcMobileTameSplice
    {alpha r p h q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    UnramifiedActionImageStokes (2 + 2 * h) q
      (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
        (MCompact.mCompactW alpha h))
      (pinnedResolvedFamily (2 + 2 * h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h))) := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτ
  let R := mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP
  let W := tameSplice R (MCompact.mCompactW alpha h)
  let C := ActionImage (2 + 2 * h) q W M
  let t := actionImageMarking (2 + 2 * h) q W M
  have hwildA : ∀ (i : Fin (2 + 2 * h + 1)) (a : M), t.x i • a = a :=
    actionImage_wild_smul hM₂ hsimple
  have htauA : ∀ a : M, t.τ • a = a := hτ
  have hwild : ∀ i, t.x i = 1 := fun i ↦
    actionImage_eq_one_of_smul_eq (t.x i) (hwildA i)
  have htau : t.τ = 1 := actionImage_eq_one_of_smul_eq t.τ htauA
  have ht : t.TameRelAt q := actionImage_tameRelAt
  have hspec : TameSpec.TameSpecializes (2 + 2 * h) q R :=
    mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuP
  have hend : IsStokesEndpoint
      (pinnedResolvedFamily (2 + 2 * h) q R (4 * Monoid.exponent C)) :=
    mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP
      (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2
  change StokesDuality ⇑t (pinnedResolvedFamily (2 + 2 * h) q W
    (4 * Monoid.exponent C)) M
  rcases actionImage_sigma_split_or_fixedPointFree hM₂ hsimple hτ with hσ | hσfpf
  · have htriv := marking_smul_trivial_of_split t hwildA htauA hσ
    apply stokesDuality_tameSplice_of_trivial_action t _ _ hM₂ htriv hqe
      (omegaPinnedLevelZhatResolver_omega2 _) (omega2Exp_fourMulExponent_mod_four C)
      R (MCompact.mCompactW alpha h)
    · exact pinned_relators_of_eval t R ht
        (eval_eq_one_of_tameSpecializes_of_wild_eq_one t ht hwild hspec)
    · exact pinned_relators_of_eval t W ht
        (eval_eq_one_of_tameSpecializes_of_wild_eq_one t ht hwild
          (tameSpecializes_tameSplice hspec (tameSpecializes_mCompact hq0 hqe alpha h)))
    · exact hend
    · exact isStokesEndpoint_tameSplice hend
        (pinned_mCompact_endpoint hqe (fourMulExponent_ne_zero_and_even C).1
          (fourMulExponent_ne_zero_and_even C).2)
    · exact mpcMobileTameCorrected_stokes_scalar t hq0 hqe eta halpha nuP
        hM₂ halpha2 ht hwild htau htriv
  · have hσodd : Odd (orderOf t.σ) :=
      actionImage_unramified_orderOf_sigma_odd hM₂ hsimple hτ
    have hStokes : StokesDuality ⇑t
        (pinnedResolvedFamily (2 + 2 * h) q R (4 * Monoid.exponent C)) M :=
      mpcMobileTameCorrected_stokes_unramified_fpf t hq0 hqe eta halpha nuP
        hM₂ ht hwild htau hσfpf hσodd
    have hσfpfD : ∀ lam : ElemDual M, t.σ • lam = lam → lam = 0 := elemDual_fpf hσfpf
    have hStokesD : StokesDuality ⇑t
        (pinnedResolvedFamily (2 + 2 * h) q R (4 * Monoid.exponent C)) (ElemDual M) :=
      mpcMobileTameCorrected_stokes_unramified_fpf t hq0 hqe eta halpha nuP
        ElemDual.add_self_eq_zero ht hwild htau hσfpfD hσodd
    exact stokesDuality_tameSplice_unramified_of_surjective t _ _ hM₂ hwildA htauA hqe
      (omegaPinnedLevelZhatResolver_omega2 _) (omega2Exp_fourMulExponent_mod_four C)
      R (MCompact.mCompactW alpha h)
      (d1_surjective_of_stokes_of_sigma_fpf t _ hσfpf hStokes)
      (d1_surjective_of_stokes_of_sigma_fpf t _ hσfpfD hStokesD) hStokes

/-- All simple elementary action-image coefficients are supplied by the mobile Mpc splice. -/
theorem simpleActionImageStokes_mpcMobileTameSplice
    {alpha r p h q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    SimpleActionImageStokes (2 + 2 * h) q
      (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
        (MCompact.mCompactW alpha h))
      (pinnedResolvedFamily (2 + 2 * h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h))) :=
  simpleActionImageStokes_of_branches
    (unramifiedActionImageStokes_mpcMobileTameSplice hq0 hqe eta halpha halpha2 nuP)
    (ramifiedActionImageStokes_tameSplice_mCompact hq0 hqe
      (mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuP)
      (fun _ hN hNtwo ↦ mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP hN hNtwo))

/-- Uniform pushed Stokes duality, with no remaining analytic input, for the mobile Mpc splice. -/
theorem pushedStokesDuality_mpcMobileTameSplice
    {alpha r p h q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h))) : Type) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g ↦ rho (gammaGen (2 + 2 * h) q
      (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
        (MCompact.mCompactW alpha h)) g))
      (pinnedResolvedFamily (2 + 2 * h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) (4 * Monoid.exponent C)) A :=
  pushedStokesDuality_tameSplice_mCompact hq0 hqe
    (mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuP)
    (fun _ hN hNtwo ↦ mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP hN hNtwo)
    (unramifiedActionImageStokes_mpcMobileTameSplice hq0 hqe eta halpha halpha2 nuP)
    rho A hA₂

/-- The complete coefficient-independent Stokes interface for the mobile source. -/
theorem mpcMobileTameSplice_uniformStokesSupply
    {alpha r p h q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    UniformStokesSupply (2 + 2 * h) q
      (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
        (MCompact.mCompactW alpha h))
      (pinnedResolvedFamily (2 + 2 * h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h))) where
  level := pinnedLevelResolver_tameSplice_mCompact hqe
    (fun _ hN hNtwo ↦ mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP hN hNtwo)
  stokes := fun _ _ _ _ _ rho A _ _ _ hA₂ ↦
    pushedStokesDuality_mpcMobileTameSplice hq0 hqe eta halpha halpha2 nuP rho A hA₂

/-- The splice retains the actual normalized complete pro-2 core and its original nu-map. -/
def mpcMobileTameSplice_core
    {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q) (alpha r p h : ℕ)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hD : ztwoIota (nuP (dmD alpha h)) = Multiplicative.ofAdd (eta : ℤ_[2])) :
    FlexibleCoreLeavesRN (2 + 2 * h)
      (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
        (MCompact.mCompactW alpha h)) (DM alpha h) nuP :=
  GQ2.Dyadic.FlexibleCoreLeavesRN.ofTameSplice
    (mpcMobileTameCorrectedCore hq0 hqe alpha r p h eta halpha nuP hD) _

#print axioms pinned_endpoint_tameCorrection
#print axioms mpcMobileTameCorrected_endpoint
#print axioms mpcMobileTameCorrected_stokes_unramified_fpf
#print axioms mpcMobileTameCorrected_stokes_scalar
#print axioms unramifiedActionImageStokes_mpcMobileTameSplice
#print axioms simpleActionImageStokes_mpcMobileTameSplice
#print axioms pushedStokesDuality_mpcMobileTameSplice
#print axioms mpcMobileTameSplice_uniformStokesSupply
#print axioms mpcMobileTameSplice_core

end
end GQ2.Dyadic.Instances.MpcMobileSpliceSupply
