/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcPairings
import GQ2.Dyadic.Instances.EvenMHeadHandlePairNielsenStokes
import GQ2.Dyadic.Instances.FiniteLevelProfiniteResolver
import GQ2.Dyadic.SelectedEta
import GQ2.Dyadic.Instances.OmegaPinnedLevelResolver

/-!
# Unramified Stokes duality for semantic Mpc and its normalized wild shears

The actual D-coordinate used by `MpcMobileNuSource` need not have a rational display. At one
finite resolver its semantic eta-power nevertheless becomes a literal integer power. This
exact free-word identity lets the existing all-rank displayed Fox rows and normal pairings
apply without a global `MpcDisplayFor` hypothesis.

Both unramified branches are proved: sigma fixed-point-free, and fully scalar. Simultaneous
wild shears are handled by genuine Nielsen transport. Their pulled-back wild actions are
proved trivial from the triviality of the 2-primary sigma action in the unramified branch;
no analogous ramified assertion is made. The uniform endpoints use a coefficient-independent
resolver at `4 * exponent C`, discharge every resolver/jet condition, and quantify over an
arbitrary 2-adic unit, arbitrary shear vector, level and handle count.

The only group-relator premise is death of the actual resolved sheared family. This module
does not identify a corrected or shadow-glued family with that family without a separate
comparison theorem, and does not assert the remaining source-certificate clauses.
-/

namespace GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes

noncomputable section

open GQ2 GQ2.Dyadic GQ2.FoxH GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Certificates.MProcyclic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.MProcyclicUnram GQ2.Dyadic.MProcyclicNormal
open GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize
open GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize

/-- Only the resolved value of the semantic D-word matters in the Mpc construction. -/
theorem evalZ_mpcWAt_congr
    {C : Type*} [Group C] {h : ℕ} (c : Generator (2 + 2 * h) → C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (alpha r p : ℕ)
    {D D' : PWord (Generator (2 + 2 * h))}
    (hD : PWord.evalZ c E E₂ D = PWord.evalZ c E E₂ D') :
    PWord.evalZ c E E₂ (mpcWAt alpha r p h D) =
      PWord.evalZ c E E₂ (mpcWAt alpha r p h D') := by
  simp only [mpcWAt, PWord.evalZ_prodList, List.map_append, List.prod_append,
    linFactorsAt, hatFactorsAt, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, PWord.evalZ_comm, hD]

/-- At a fixed resolver every semantic unit has an exact literal free-word display. -/
theorem mpcUnit_resolvedFamily_eq_lit
    (alpha r p h q : ℕ) (eta : ℤ_[2]ˣ) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam (2 + 2 * h) q (mpcWUnit alpha r p eta h) l)) =
      mpcFamOf alpha r p h q (.lit (E (etaHatZ (eta : ℤ_[2])))) E E₂ := by
  funext l
  fin_cases l
  · rfl
  · change heisToFree E E₂ (mpcWAt alpha r p h
        (.profPow (.gen .sigma) (etaHatZ (eta : ℤ_[2])))) =
      heisToFree E E₂ (mpcW alpha r p (.lit (E (etaHatZ (eta : ℤ_[2])))) h)
    rw [← mpcWAt_etaDisplay]
    apply evalZ_mpcWAt_congr
    rfl

/-- The semantic arbitrary-unit family has the usual Stokes endpoint. -/
theorem mpcUnit_resolvedFamily_endpoint
    {alpha r p h q : ℕ} (eta : ℤ_[2]ˣ) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hα : 1 ≤ alpha) (hq : Even q) (he : Odd (E omega2)) :
    IsStokesEndpoint (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam (2 + 2 * h) q (mpcWUnit alpha r p eta h) l)) := by
  rw [mpcUnit_resolvedFamily_eq_lit]
  exact mpcOf_isStokesEndpoint hα hq he _

/-- The sigma-fixed-point-free branch for semantic Mpc, with both Fox rows and pairing supplied. -/
theorem stokesDuality_mpcUnit_unramified_fpf
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] {alpha r p h q e : ℕ}
    (t : Marking (2 + 2 * h) C) (eta : ℤ_[2]ˣ)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0) (hα : 1 ≤ alpha) (hq : Even q)
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (hliftA : ResolverLifts E (WordLift A C))
    (hliftD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hS₂ : ∀ a : A, powOmega2 t.σ • a = a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0)
    (hη : ∀ a : A, (t.σ ^ E (etaHatZ (eta : ℤ_[2]))) • a = t.σ • a)
    (hr : ∀ l, FreeGroup.lift ⇑t (heisToFree E E₂
      (gammaFam (2 + 2 * h) q (mpcWUnit alpha r p eta h) l)) = 1) :
    StokesDuality ⇑t (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam (2 + 2 * h) q (mpcWUnit alpha r p eta h) l)) A := by
  have hr' : ∀ l, FreeGroup.lift ⇑t
      (mpcFamOf alpha r p h q (.lit (E (etaHatZ (eta : ℤ_[2])))) E E₂ l) = 1 := by
    intro l
    rw [← mpcUnit_resolvedFamily_eq_lit]
    exact hr l
  rw [mpcUnit_resolvedFamily_eq_lit]
  have hodd : Odd (E omega2) := by
    rw [hE]
    have heodd : Odd e := Nat.odd_iff.mpr (by omega)
    exact_mod_cast heodd
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hwildD : ∀ i (lam : ElemDual A), t.x i • lam = lam :=
    fun i ↦ elemDual_smul_eq_self (hwild i)
  have hτD : ∀ lam : ElemDual A, t.τ • lam = lam := elemDual_smul_eq_self hτ
  have hS₂D : ∀ lam : ElemDual A, powOmega2 t.σ • lam = lam := elemDual_smul_eq_self hS₂
  refine evenUnramifiedStokesDuality_of_smul_row t _
    (t.σ ^ E (etaHatZ (eta : ℤ_[2]))) hA₂ hr'
    (mpcOf_isStokesEndpoint hα hq hodd _) ?_ ?_ ?_ hwild hτ hσfpf ?_
  · exact heisD1_mpcFamOf_unramified_apply t E E₂ hliftA hA₂ hα hq hwild hτ hS₂ rfl
  · exact heisD1_mpcFamOf_unramified_apply t E E₂ hliftD hA₂D hα hq hwildD hτD hS₂D rfl
  · intro d₀ d₁ z lam₀ lam₁ mu
    exact heisEta1_mpcFamOf_evenNormal t E E₂ hA₂ hwild hτ
      (fun a ↦ by rw [hres]; exact hS₂ a) hE he d₀ d₁ z lam₀ lam₁ mu
  · intro a ha
    exact hσfpf a ((hη a).symm.trans ha)

/-- Scalar Stokes duality for semantic Mpc at any odd eta jet. -/
theorem stokesDuality_mpcUnit_scalar
    {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] {alpha r p h q e : ℕ}
    (t : Marking (2 + 2 * h) C) (eta : ℤ_[2]ˣ)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a + a = 0) (hα : 2 ≤ alpha) (hq : Even q)
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (hηodd : Odd (E (etaHatZ (eta : ℤ_[2]))))
    (hliftA : ResolverLifts E (WordLift A C))
    (hliftD : ResolverLifts E (WordLift (ElemDual A) C))
    (htriv : ∀ (g : Generator (2 + 2 * h)) (a : A), t g • a = a)
    (hr : ∀ l, FreeGroup.lift ⇑t (heisToFree E E₂
      (gammaFam (2 + 2 * h) q (mpcWUnit alpha r p eta h) l)) = 1) :
    StokesDuality ⇑t (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam (2 + 2 * h) q (mpcWUnit alpha r p eta h) l)) A := by
  have hr' : ∀ l, FreeGroup.lift ⇑t
      (mpcFamOf alpha r p h q (.lit (E (etaHatZ (eta : ℤ_[2])))) E E₂ l) = 1 := by
    intro l
    rw [← mpcUnit_resolvedFamily_eq_lit]
    exact hr l
  rw [mpcUnit_resolvedFamily_eq_lit]
  have hodd : Odd (E omega2) := by
    rw [hE]
    have heodd : Odd e := Nat.odd_iff.mpr (by omega)
    exact_mod_cast heodd
  have hA₂D : ∀ lam : ElemDual A, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have htrivD : ∀ g (lam : ElemDual A), t g • lam = lam :=
    fun g ↦ elemDual_smul_eq_self (htriv g)
  have hjet := (oddDisplayJet_lit hηodd).oddJetAt E
  exact evenScalarStokesDuality_of_separation t _ hA₂ hr'
    (mpcOf_isStokesEndpoint (by omega) hq hodd _)
    (heisD0_eq_zero_of_split t htriv) (heisD0_eq_zero_of_split t htrivD)
    (heisD1_mpcFamOf_tauRow_of_split t E E₂ hliftA hA₂ (by omega) hq htriv)
    (heisD1_mpcFamOf_tauRow_of_split t E E₂ hliftD hA₂D (by omega) hq htrivD)
    (fun p hp ↦ mpc_scalarNormal_pairing_separates_left t E E₂ hA₂ htriv hE he hα hq
      hjet.1 (fun u w ↦ hjet.2 t E₂ hA₂ htriv u w) p hp)

/-- Every 2-primary power acts trivially when the 2-primary part does. -/
theorem zpowHat_padicOmega2_smul_of_powOmega2
    {C A : Type} [Group C] [Finite C] [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [DistribMulAction C A] (x : C) (z : ℤ_[2])
    (hx : ∀ a : A, powOmega2 x • a = a) (a : A) :
    (x ^ᶻ padicOmega2 z) • a = a := by
  rw [zpowHat_padicOmega2, padicOmega2Exp, mul_comm, pow_mul]
  have hp (n : ℕ) : (powOmega2 x) ^ n • a = a := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hx, ih]
  exact hp _

/-- The actual lower marking induced by the resolved inverse wild shear. -/
def shearedMark {n : ℕ} {C : Type*} [Group C]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (k : Fin (n + 1) → ℤ_[2]) : Marking n C :=
  ⟨freeSubstMark ⇑t (fun g ↦ heisToFree E E₂ ((wildShearNielsen k).backward g))⟩

@[simp] theorem shearedMark_sigma {n : ℕ} {C : Type*} [Group C]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (k : Fin (n + 1) → ℤ_[2]) : (shearedMark t E E₂ k).σ = t.σ := by
  change FreeGroup.lift ⇑t (FreeGroup.of .sigma) = t.σ
  simp

@[simp] theorem shearedMark_tau {n : ℕ} {C : Type*} [Group C]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (k : Fin (n + 1) → ℤ_[2]) : (shearedMark t E E₂ k).τ = t.τ := by
  change FreeGroup.lift ⇑t (FreeGroup.of .tau) = t.τ
  simp

@[simp] theorem shearedMark_wild {n : ℕ} {C : Type*} [Group C]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (k : Fin (n + 1) → ℤ_[2]) (i : Fin (n + 1)) :
    (shearedMark t E E₂ k).x i = t.x i * t.σ ^ E (padicOmega2 (k i)) := by
  change FreeGroup.lift ⇑t (FreeGroup.of (.wild i) *
    FreeGroup.of .sigma ^ E (padicOmega2 (k i))) = _
  simp

/-- Relator death transports through the actual resolved substitution. -/
theorem shearedMark_relators
    {n q : ℕ} {C : Type*} [Group C]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (k : Fin (n + 1) → ℤ_[2]) (R : PWord (Generator n))
    (hr : ∀ l, FreeGroup.lift ⇑t (heisToFree E E₂
      (gammaFam n q (PWord.subst (wildShearNielsen k).backward R) l)) = 1) :
    ∀ l, FreeGroup.lift ⇑(shearedMark t E E₂ k)
      (heisToFree E E₂ (gammaFam n q R l)) = 1 := by
  intro l
  have H := hr l
  rw [gammaFam_subst_wildShearBackward, heisToFree_subst, lift_lift_freeSubst] at H
  exact H

/-- The normalized wild shear preserves the unramified fixed-point-free branch. -/
theorem stokesDuality_mpcUnit_sheared_unramified_fpf
    {C A : Type} [Group C] [Finite C] [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A] {alpha r p h q e : ℕ}
    (t : Marking (2 + 2 * h) C) (eta : ℤ_[2]ˣ)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (k : Fin (2 + 2 * h + 1) → ℤ_[2])
    (hA₂ : ∀ a : A, a + a = 0) (hα : 1 ≤ alpha) (hq : Even q)
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (hliftA : ResolverLifts E (WordLift A C))
    (hliftD : ResolverLifts E (WordLift (ElemDual A) C))
    (hres : ResolverLifts E C)
    (hpadic : ∀ z : ℤ_[2], t.σ ^ E (padicOmega2 z) = t.σ ^ᶻ padicOmega2 z)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hS₂ : ∀ a : A, powOmega2 t.σ • a = a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0)
    (hη : ∀ a : A, (t.σ ^ E (etaHatZ (eta : ℤ_[2]))) • a = t.σ • a)
    (hr : ∀ l, FreeGroup.lift ⇑t (heisToFree E E₂
      (gammaFam (2 + 2 * h) q
        (PWord.subst (wildShearNielsen k).backward (mpcWUnit alpha r p eta h)) l)) = 1) :
    StokesDuality ⇑t (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam (2 + 2 * h) q
        (PWord.subst (wildShearNielsen k).backward (mpcWUnit alpha r p eta h)) l)) A := by
  have hodd : Odd (E omega2) := by
    rw [hE]
    have heodd : Odd e := Nat.odd_iff.mpr (by omega)
    exact_mod_cast heodd
  apply (stokesDuality_wildShearBackward_iff E E₂ ⇑t _ k
    (mpcUnit_resolvedFamily_endpoint eta E E₂ hα hq hodd)).mpr
  change StokesDuality ⇑(shearedMark t E E₂ k) _ A
  apply stokesDuality_mpcUnit_unramified_fpf (shearedMark t E E₂ k) eta E E₂
    hA₂ hα hq hE he hliftA hliftD hres
  · intro i a
    rw [shearedMark_wild, mul_smul, hpadic,
      zpowHat_padicOmega2_smul_of_powOmega2 t.σ (k i) hS₂, hwild]
  · simpa using hτ
  · simpa using hS₂
  · simpa using hσfpf
  · simpa using hη
  · exact shearedMark_relators t E E₂ k _ hr

/-- The normalized wild shear preserves the scalar branch. -/
theorem stokesDuality_mpcUnit_sheared_scalar
    {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] {alpha r p h q e : ℕ}
    (t : Marking (2 + 2 * h) C) (eta : ℤ_[2]ˣ)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (k : Fin (2 + 2 * h + 1) → ℤ_[2])
    (hA₂ : ∀ a : A, a + a = 0) (hα : 2 ≤ alpha) (hq : Even q)
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (hηodd : Odd (E (etaHatZ (eta : ℤ_[2]))))
    (hliftA : ResolverLifts E (WordLift A C))
    (hliftD : ResolverLifts E (WordLift (ElemDual A) C))
    (htriv : ∀ (g : Generator (2 + 2 * h)) (a : A), t g • a = a)
    (hr : ∀ l, FreeGroup.lift ⇑t (heisToFree E E₂
      (gammaFam (2 + 2 * h) q
        (PWord.subst (wildShearNielsen k).backward (mpcWUnit alpha r p eta h)) l)) = 1) :
    StokesDuality ⇑t (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam (2 + 2 * h) q
        (PWord.subst (wildShearNielsen k).backward (mpcWUnit alpha r p eta h)) l)) A := by
  have hodd : Odd (E omega2) := by
    rw [hE]
    have heodd : Odd e := Nat.odd_iff.mpr (by omega)
    exact_mod_cast heodd
  apply (stokesDuality_wildShearBackward_iff E E₂ ⇑t _ k
    (mpcUnit_resolvedFamily_endpoint eta E E₂ (by omega) hq hodd)).mpr
  change StokesDuality ⇑(shearedMark t E E₂ k) _ A
  apply stokesDuality_mpcUnit_scalar (shearedMark t E E₂ k) eta E E₂
    hA₂ hα hq hE he hηodd hliftA hliftD
  · intro g a
    cases g with
    | sigma =>
      change (shearedMark t E E₂ k).σ • a = a
      rw [shearedMark_sigma]
      exact htriv .sigma a
    | tau =>
      change (shearedMark t E E₂ k).τ • a = a
      rw [shearedMark_tau]
      exact htriv .tau a
    | wild i =>
      change (shearedMark t E E₂ k).x i • a = a
      rw [shearedMark_wild, mul_smul]
      have hs : t.σ ∈ trivAct C A := mem_trivAct.mpr (htriv .sigma)
      rw [mem_trivAct.mp ((trivAct C A).zpow_mem hs _)]
      exact htriv (.wild i) a
  · exact shearedMark_relators t E E₂ k _ hr

/-- A coefficient-independent resolved family for every semantic Mpc wild shear. -/
def mpcUnitShearedLevelFamily (alpha r p h q : ℕ) (eta : ℤ_[2]ˣ)
    (k : Fin (2 + 2 * h + 1) → ℤ_[2]) (N : ℕ) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  fun l ↦ heisToFree (omegaPinnedLevelZhatResolver N) (omegaPinnedLevelZtwoResolver N)
    (gammaFam (2 + 2 * h) q
      (PWord.subst (wildShearNielsen k).backward (mpcWUnit alpha r p eta h)) l)

/-- Uniform unramified fixed-point-free Stokes duality with every resolver premise discharged. -/
theorem stokesDuality_mpcUnit_sheared_unramified_fpf_uniform
    {C A : Type} [Group C] [Finite C] [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup A] [Finite A] [DistribMulAction C A] {alpha r p h q : ℕ}
    (t : Marking (2 + 2 * h) C) (eta : ℤ_[2]ˣ)
    (k : Fin (2 + 2 * h + 1) → ℤ_[2])
    (hA₂ : ∀ a : A, a + a = 0) (hα : 1 ≤ alpha) (hq : Even q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτ : ∀ a : A, t.τ • a = a)
    (hσfpf : ∀ a : A, t.σ • a = a → a = 0)
    (hσodd : Odd (orderOf t.σ))
    (hr : ∀ l, FreeGroup.lift ⇑t
      (mpcUnitShearedLevelFamily alpha r p h q eta k (4 * Monoid.exponent C) l) = 1) :
    StokesDuality ⇑t
      (mpcUnitShearedLevelFamily alpha r p h q eta k (4 * Monoid.exponent C)) A := by
  have hN := (fourMulExponent_ne_zero_and_even C).1
  have hord (c : C) : orderOf c ∣ 4 * Monoid.exponent C :=
    (Monoid.order_dvd_exponent c).trans ⟨4, by ring⟩
  apply stokesDuality_mpcUnit_sheared_unramified_fpf t eta
    (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
    (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)) k
    hA₂ hα hq (omegaPinnedLevelZhatResolver_omega2 _)
    (omega2Exp_fourMulExponent_mod_four C)
    (omegaPinnedLevelZhatResolver_fourMulExponent_wordLift hA₂)
    (omegaPinnedLevelZhatResolver_fourMulExponent_wordLift
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero))
    (omegaPinnedLevelZhatResolver_fourMulExponent_base C)
    (fun z ↦ omegaPinnedLevelZhatResolver_spec hN hord (padicOmega2 z) t.σ)
    hwild hτ (fun a ↦ by rw [powOmega2_eq_one_of_odd hσodd, one_smul]) hσfpf
  · intro a
    rw [omegaPinnedLevelZhatResolver_spec hN hord, zpowHat_etaHatZ_of_odd hσodd]
  · exact hr

/-- Uniform scalar Stokes duality with every resolver and eta-parity premise discharged. -/
theorem stokesDuality_mpcUnit_sheared_scalar_uniform
    {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] {alpha r p h q : ℕ}
    (t : Marking (2 + 2 * h) C) (eta : ℤ_[2]ˣ)
    (k : Fin (2 + 2 * h + 1) → ℤ_[2])
    (hA₂ : ∀ a : A, a + a = 0) (hα : 2 ≤ alpha) (hq : Even q)
    (htriv : ∀ (g : Generator (2 + 2 * h)) (a : A), t g • a = a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (mpcUnitShearedLevelFamily alpha r p h q eta k (4 * Monoid.exponent C) l) = 1) :
    StokesDuality ⇑t
      (mpcUnitShearedLevelFamily alpha r p h q eta k (4 * Monoid.exponent C)) A := by
  exact stokesDuality_mpcUnit_sheared_scalar t eta
    (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
    (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)) k
    hA₂ hα hq (omegaPinnedLevelZhatResolver_omega2 _)
    (omega2Exp_fourMulExponent_mod_four C)
    (omegaPinnedLevelZhatResolver_etaHatZ_odd (fourMulExponent_ne_zero_and_even C).1 eta)
    (omegaPinnedLevelZhatResolver_fourMulExponent_wordLift hA₂)
    (omegaPinnedLevelZhatResolver_fourMulExponent_wordLift
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero)) htriv hr

/-- The uniform sheared family has the Stokes endpoint at every nonzero even level. -/
theorem mpcUnitShearedLevelFamily_endpoint
    {alpha r p h q N : ℕ} (eta : ℤ_[2]ˣ) (k : Fin (2 + 2 * h + 1) → ℤ_[2])
    (hα : 1 ≤ alpha) (hq : Even q) (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0) :
    IsStokesEndpoint (mpcUnitShearedLevelFamily alpha r p h q eta k N) := by
  have hodd : Odd (omegaPinnedLevelZhatResolver N omega2) := by
    rw [omegaPinnedLevelZhatResolver_omega2]
    exact_mod_cast odd_omega2Exp hN hNtwo
  have hbase := mpcUnit_resolvedFamily_endpoint (r := r) (p := p) (h := h)
    eta (omegaPinnedLevelZhatResolver N) (omegaPinnedLevelZtwoResolver N) hα hq hodd
  have H := isStokesEndpoint_heisToFree_subst hbase (wildShearNielsen k).backward
  intro i
  have Hi := H i
  simpa only [mpcUnitShearedLevelFamily, ← gammaFam_subst_wildShearBackward] using Hi

/-- The uniform sheared family resolves in every finite target killed by the level. -/
theorem mpcUnitShearedLevelFamily_resolves
    {alpha r p h q N : ℕ} (eta : ℤ_[2]ˣ) (k : Fin (2 + 2 * h + 1) → ℤ_[2])
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N) :
    ResolvesAt
      (gammaFam (2 + 2 * h) q
        (PWord.subst (wildShearNielsen k).backward (mpcWUnit alpha r p eta h)))
      (mpcUnitShearedLevelFamily alpha r p h q eta k N) Q :=
  resolvesAt_omegaPinnedLevelResolvers hN hord _

#print axioms mpcUnit_resolvedFamily_eq_lit
#print axioms mpcUnit_resolvedFamily_endpoint
#print axioms stokesDuality_mpcUnit_unramified_fpf
#print axioms stokesDuality_mpcUnit_scalar
#print axioms stokesDuality_mpcUnit_sheared_unramified_fpf_uniform
#print axioms stokesDuality_mpcUnit_sheared_scalar_uniform
#print axioms mpcUnitShearedLevelFamily_endpoint
#print axioms mpcUnitShearedLevelFamily_resolves

end
end GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes
