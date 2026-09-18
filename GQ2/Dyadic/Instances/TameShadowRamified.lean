/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.StokesJetZero
import GQ2.Dyadic.Certificates.Mpc
import GQ2.Dyadic.TameShadowWord
import GQ2.Dyadic.Instances.StokesWordComparison

/-!
# Ramified first jets of tame averaging

The two-primary power of a lift whose base has odd fixed-point-free action has zero primal
and dual jet. This supplies the averaging projection used to separate structural pro-2
presentation data from the ramified Stokes template.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates

/-- The canonical tame relator has no wild exponent, so an endpoint word has even wild
exponents before shadowing. -/
theorem heisEps_wild_eq_one_of_gammaFam_endpoint
    {n q : ℕ} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ} {R : PWord (Generator n)}
    (hend : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R k)))
    (i : Fin (n + 1)) : heisEps (.wild i) (heisToFree E E₂ R) = 1 := by
  have ht : heisEps (.wild i) (heisToFree E E₂ (tameRelW n q)) = 1 := by
    simp [heisToFree, tameRelW, heisEps, conjR]
  have H := hend (.wild i)
  simp only [Fin.sum_univ_two, gammaFam_zero, gammaFam_one, ht, toAdd_one,
    zero_add] at H
  exact Multiplicative.toAdd.injective H

variable {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- The two-primary power has zero first jets at an odd fixed-point-free base action.
Its central coordinate is deliberately not asserted to vanish. -/
theorem heisZpow_jetZero_of_oddFixedPointFree
    (p : HeisLift A C) (E : Zhat → ℤ)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hfpf : ∀ a : A, p.g • a = a → a = 0)
    (hodd : ∀ a : A, powOmega2 p.g • a = a) :
    p ^ E omega2 ∈ heisJetZero A C := by
  constructor
  · have h := congrArg WordLift.u (map_zpow (heisPrimal (A := A) (C := C)) p
      (E omega2))
    change (p ^ E omega2).a = ((heisPrimal p) ^ E omega2).u at h
    rw [h, hresA]
    exact WordLift.powOmega2_u_of_oddFixedPointFree _ hfpf hodd
  · have h := congrArg WordLift.u (map_zpow (MProcyclic.heisDual (A := A) (C := C)) p
      (E omega2))
    change (p ^ E omega2).l = ((MProcyclic.heisDual p) ^ E omega2).u at h
    rw [h, hresD]
    exact WordLift.powOmega2_u_of_oddFixedPointFree _
      (fun lam hlam ↦ elemDual_fpf hfpf lam hlam)
      (smul_elemDual_of_trivial hodd)

/-- Multiplying a trivially acting wild base by tau retains tau's fixed-point-free odd action. -/
theorem heisZpow_mul_tau_jetZero
    (p t : HeisLift A C) (E : Zhat → ℤ)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hp : ∀ a : A, p.g • a = a)
    (hfpf : ∀ a : A, t.g • a = a → a = 0)
    (hodd : ∀ a : A, powOmega2 t.g • a = a) :
    (p * t) ^ E omega2 ∈ heisJetZero A C := by
  apply heisZpow_jetZero_of_oddFixedPointFree _ E hresA hresD
  · intro a ha
    apply hfpf a
    simpa only [HeisLift.mul_g, mul_smul, hp] using ha
  · exact WordLift.powOmega2_smul_of_trivial_mul p.g t.g hp hodd

/-- At an actually trivial wild base, the shadow generator is central. Offsets at sigma
and tau are unrestricted; only the action hypotheses on tau are used. -/
theorem heisEvalZ_tameShadowSubst_wild_central
    {n : ℕ} (c : Generator n → C) (x : Generator n → A)
    (y : Generator n → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hwild : ∀ i, c (.wild i) = 1)
    (hfpf : ∀ a : A, c .tau • a = a → a = 0)
    (hodd : ∀ a : A, powOmega2 (c .tau) • a = a) (i : Fin (n + 1)) :
    let p := heisEvalZ c x y E E₂ (tameShadowSubst (.wild i))
    p.a = 0 ∧ p.l = 0 ∧ p.g = 1 := by
  have ht := heisZpow_jetZero_of_oddFixedPointFree
    (heisGen c x y .tau) E hresA hresD hfpf hodd
  have hwt := heisZpow_mul_tau_jetZero
    (heisGen c x y (.wild i)) (heisGen c x y .tau) E hresA hresD
    (by intro a; change c (.wild i) • a = a; rw [hwild, one_smul]) hfpf hodd
  have hp : heisEvalZ c x y E E₂ (tameShadowSubst (.wild i)) ∈
      heisJetZero A C := mul_mem hwt (inv_mem ht)
  refine ⟨hp.1, hp.2, ?_⟩
  rw [heisEvalZ_g]
  simp [tameShadowSubst, hwild]

/-- A ramified shadow vanishes on every cochain when its pure-sigma evaluation dies and
its wild exponents are even. In particular no normal-form restriction is needed. -/
theorem heisEvalZ_tameShadow_eq_one
    {n : ℕ} (c : Generator n → C) (x : Generator n → A)
    (y : Generator n → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R : PWord (Generator n))
    (hresA : ResolverLifts E (WordLift A C))
    (hresD : ResolverLifts E (WordLift (ElemDual A) C))
    (hwild : ∀ i, c (.wild i) = 1)
    (hfpf : ∀ a : A, c .tau • a = a → a = 0)
    (hodd : ∀ a : A, powOmega2 (c .tau) • a = a)
    (heven : ∀ i, heisEps (.wild i) (heisToFree E E₂ R) = 1)
    (hkill : PWord.evalZ
      (fun g : Generator n ↦ match g with | .sigma => heisGen c x y .sigma | _ => 1)
      E E₂ R = 1) :
    heisEvalZ c x y E E₂ (tameShadow R) = 1 := by
  let p : Generator n → HeisLift A C :=
    fun g ↦ heisEvalZ c x y E E₂ (tameShadowSubst g)
  change PWord.evalZ (heisGen c x y) E E₂ (PWord.subst tameShadowSubst R) = 1
  rw [PWord.evalZ_subst, evalZ_eq_lift_heisToFree]
  change FreeGroup.lift p (heisToFree E E₂ R) = 1
  apply heisWord_eq_one_of_central_normalization
  · have hnorm : (fun g ↦ (⟨(p g).a, (p g).l, 0, (p g).g⟩ : HeisLift A C)) =
        (fun g : Generator n ↦ match g with | .sigma => heisGen c x y .sigma | _ => 1) := by
      funext g
      cases g with
      | sigma => rfl
      | tau => rfl
      | wild i =>
          have hp := heisEvalZ_tameShadowSubst_wild_central c x y E E₂
            hresA hresD hwild hfpf hodd i
          change (⟨(p (.wild i)).a, (p (.wild i)).l, 0, (p (.wild i)).g⟩ : HeisLift A C) = 1
          change (p (.wild i)).a = 0 ∧ (p (.wild i)).l = 0 ∧ (p (.wild i)).g = 1 at hp
          rw [hp.1, hp.2.1, hp.2.2]
          rfl
    rw [hnorm, ← evalZ_eq_lift_heisToFree]
    exact hkill
  · intro g
    cases g with
    | sigma => exact Or.inr rfl
    | tau => exact Or.inr rfl
    | wild i => exact Or.inl (heven i)

local instance shadowHeisTopology
    {D B : Type} [Group D] [AddCommGroup B] : TopologicalSpace (HeisLift B D) := ⊥

local instance shadowHeisDiscrete
    {D B : Type} [Group D] [AddCommGroup B] : DiscreteTopology (HeisLift B D) := ⟨rfl⟩

/-- Tame specialization supplies the pure-sigma equation, so endpoint shadows vanish
identically on all ramified cochains. -/
theorem heisEvalZ_tameShadow_eq_one_of_tameSpecializes
    {D B : Type} [Group D] [Finite D] [AddCommGroup B] [Finite B]
    [DistribMulAction D B] {n q : ℕ}
    (c : Generator n → D) (x : Generator n → B) (y : Generator n → ElemDual B)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (R : PWord (Generator n))
    (hresA : ResolverLifts E (WordLift B D))
    (hresD : ResolverLifts E (WordLift (ElemDual B) D))
    (hwild : ∀ i, c (.wild i) = 1)
    (hfpf : ∀ a : B, c .tau • a = a → a = 0)
    (hodd : ∀ a : B, powOmega2 (c .tau) • a = a)
    (hend : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R k)))
    (hspec : TameSpec.TameSpecializes n q R)
    (hresolve : ∀ p : HeisLift B D, PWord.ResolvedAt
      (fun g : Generator n ↦ match g with | .sigma => p | _ => 1) E E₂ R) :
    heisEvalZ c x y E E₂ (tameShadow R) = 1 := by
  apply heisEvalZ_tameShadow_eq_one c x y E E₂ R hresA hresD hwild hfpf hodd
  · exact heisEps_wild_eq_one_of_gammaFam_endpoint hend
  · exact evalZ_pureSigma_of_tameSpecializes hspec (heisGen c x y .sigma)
      E E₂ (hresolve _)

/-- On ramified coefficients the splice is exactly its analytic template in the full
Heisenberg lift, on arbitrary cochains. -/
theorem heisEvalZ_tameSplice_ramified
    {D B : Type} [Group D] [Finite D] [AddCommGroup B] [Finite B]
    [DistribMulAction D B] {n q : ℕ}
    (c : Generator n → D) (x : Generator n → B) (y : Generator n → ElemDual B)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (R H : PWord (Generator n))
    (hresA : ResolverLifts E (WordLift B D))
    (hresD : ResolverLifts E (WordLift (ElemDual B) D))
    (hwild : ∀ i, c (.wild i) = 1)
    (hfpf : ∀ a : B, c .tau • a = a → a = 0)
    (hodd : ∀ a : B, powOmega2 (c .tau) • a = a)
    (hendR : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R k)))
    (hendH : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q H k)))
    (hspecR : TameSpec.TameSpecializes n q R)
    (hspecH : TameSpec.TameSpecializes n q H)
    (hresolveR : ∀ p : HeisLift B D, PWord.ResolvedAt
      (fun g : Generator n ↦ match g with | .sigma => p | _ => 1) E E₂ R)
    (hresolveH : ∀ p : HeisLift B D, PWord.ResolvedAt
      (fun g : Generator n ↦ match g with | .sigma => p | _ => 1) E E₂ H) :
    heisEvalZ c x y E E₂ (tameSplice R H) = heisEvalZ c x y E E₂ H := by
  rw [tameSplice, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_inv,
    heisEvalZ_tameShadow_eq_one_of_tameSpecializes c x y E E₂ R hresA hresD
      hwild hfpf hodd hendR hspecR hresolveR,
    heisEvalZ_tameShadow_eq_one_of_tameSpecializes c x y E E₂ H hresA hresD
      hwild hfpf hodd hendH hspecH hresolveH, one_mul, inv_one, mul_one]

/-- General ramified Stokes gluing: the structural word can be replaced by any other
tame-specializing endpoint word without changing the template's Stokes ladder. -/
theorem stokesDuality_tameSplice_ramified_iff
    {D B : Type} [Group D] [Finite D] [AddCommGroup B] [Finite B]
    [DistribMulAction D B] {n q : ℕ}
    (c : Generator n → D) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (R H : PWord (Generator n))
    (hresA : ResolverLifts E (WordLift B D))
    (hresD : ResolverLifts E (WordLift (ElemDual B) D))
    (hwild : ∀ i, c (.wild i) = 1)
    (hfpf : ∀ a : B, c .tau • a = a → a = 0)
    (hodd : ∀ a : B, powOmega2 (c .tau) • a = a)
    (hendR : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R k)))
    (hendH : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q H k)))
    (hspecR : TameSpec.TameSpecializes n q R)
    (hspecH : TameSpec.TameSpecializes n q H)
    (hresolveR : ∀ p : HeisLift B D, PWord.ResolvedAt
      (fun g : Generator n ↦ match g with | .sigma => p | _ => 1) E E₂ R)
    (hresolveH : ∀ p : HeisLift B D, PWord.ResolvedAt
      (fun g : Generator n ↦ match g with | .sigma => p | _ => 1) E E₂ H) :
    StokesDuality c (fun k ↦ heisToFree E E₂ (gammaFam n q (tameSplice R H) k)) B ↔
      StokesDuality c (fun k ↦ heisToFree E E₂ (gammaFam n q H k)) B := by
  apply stokesDuality_iff_of_heisWord_coordinates
  intro x y k
  fin_cases k
  · exact ⟨rfl, rfl, rfl⟩
  · have h := heisEvalZ_tameSplice_ramified c x y E E₂ R H hresA hresD
      hwild hfpf hodd hendR hendH hspecR hspecH hresolveR hresolveH
    rw [heisEvalZ_eq_lift, heisEvalZ_eq_lift] at h
    exact ⟨congrArg HeisLift.a h, congrArg HeisLift.l h, congrArg HeisLift.z h⟩

#print axioms heisZpow_jetZero_of_oddFixedPointFree
#print axioms heisZpow_mul_tau_jetZero
#print axioms heisEvalZ_tameShadowSubst_wild_central
#print axioms heisEvalZ_tameShadow_eq_one
#print axioms heisEps_wild_eq_one_of_gammaFam_endpoint
#print axioms heisEvalZ_tameShadow_eq_one_of_tameSpecializes
#print axioms heisEvalZ_tameSplice_ramified
#print axioms stokesDuality_tameSplice_ramified_iff

end
end GQ2.Dyadic
