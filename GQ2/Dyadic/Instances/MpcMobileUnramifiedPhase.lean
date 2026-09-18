/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes
import GQ2.Dyadic.Instances.MpcUnramifiedHandleHessian
import GQ2.Dyadic.Instances.MpcMobileSpliceSupply
import GQ2.Dyadic.Instances.GammaRUniformWordPhaseSeam
import GQ2.Dyadic.TameHessianNormalization

/-!
# The arbitrary-unit unramified mobile-Mpc quadratic phase

The semantic unit exponent is resolved in the full kappa0 central extension, not just in the
Heisenberg pairing. At each resolver its literal integer value gives an exact equality of
group words. The resulting quadratic formula is uniform in the unit, procyclic level,
integer head charge and handle count. Its factor-set charge is retained explicitly until the
actual two-primary sigma element is proved to be one.
-/

namespace GQ2.Dyadic.Instances.MpcMobileUnramifiedPhase
noncomputable section

open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix GQ2.FoxH
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count GQ2.Dyadic.LSquare GQ2.Dyadic.Certificates
open GQ2.Dyadic.Instances.MpcSemanticUnramifiedStokes
open GQ2.Dyadic.Instances.MpcUnramifiedHandleHessian
open GQ2.Dyadic.Instances.WordPhase GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.MpcMobileNuSource
open GQ2.Dyadic.MarkedCore

/-- Semantic eta-to-literal reduction holds in the full central extension, including its fibre. -/
theorem hessRelZ_mpcUnit_eq_lit
    {C : Type} [Group C] {h : ℕ} (c : Generator (2 + 2 * h) → C)
    (kappa : WordCoh.TwoCocycle C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha r p : ℕ) (eta : ℤ_[2]ˣ) :
    hessRelZ c kappa E E₂ (mpcWUnit alpha r p eta h) =
      hessRelZ c kappa E E₂
        (mpcW alpha r p (.lit (E (etaHatZ (eta : ℤ_[2])))) h) := by
  unfold hessRelZ hessEvalZ
  apply congrArg WordCoh.CentExt.fib
  rw [mpcWUnit, ← mpcWAt_etaDisplay]
  apply evalZ_mpcWAt_congr
  rfl

section Phase

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
  {h : ℕ} (s : C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- The full arbitrary-unit Hessian, with its honest factor-set charge still visible. -/
theorem hessRelZ_mpcUnit_unramified_handles
    [Finite C] [Finite V] (hV₂ : ∀ v : V, v + v = 0)
    {alpha : ℕ} (halpha : 2 ≤ alpha) (r p : ℕ) (eta : ℤ_[2]ˣ)
    (v : Fin (2 + 2 * h + 1) → V) (hv2 : v (Certificates.x2Idx h) = 0)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark s 1 v) (kappa0Cocycle dat hdat)
        E E₂ (mpcWUnit alpha r p eta h) =
      q0 (v (Certificates.x0Idx h)) +
        polar q0 (v (Certificates.x0Idx h)) (v (Certificates.x1Idx h)) +
        dat.m ((s ^ E omega2) ^ p) (v (Certificates.x0Idx h)) +
        ∑ j, polar q0 (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j)) := by
  rw [hessRelZ_mpcUnit_eq_lit]
  exact hessRelZ_mpcW_unramified_handles dat hdat s v E E₂ hV₂
    halpha r p _ hv2 hS₂ hE he

/-- The arbitrary-unit phase in compact normal coordinates. -/
theorem hessRelZ_mpcUnit_unramified_compactPhase
    [Finite C] [Finite V] (hV₂ : ∀ v : V, v + v = 0)
    {alpha : ℕ} (halpha : 2 ≤ alpha) (r p : ℕ) (eta : ℤ_[2]ˣ)
    (z : (V × V) × (Fin h → V × V))
    (hS₂ : ∀ v : V, (s ^ E omega2) • v = v) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark s 1
        (fun i ↦ wPmCompactPhaseNormal h z (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E₂ (mpcWUnit alpha r p eta h) =
      wPhCompactWallHandlePhase q0 h z + dat.m ((s ^ E omega2) ^ p) z.1.1 := by
  rw [hessRelZ_mpcUnit_eq_lit]
  exact hessRelZ_mpcW_unramified_compactPhase dat hdat s E E₂ hV₂
    halpha r p _ z hS₂ hE he

/-- Actual two-primary sigma triviality removes the factor-set charge, not only its polar form. -/
theorem hessRelZ_mpcUnit_unramified_compactPhase_of_sigma2_one
    [Finite C] [Finite V] (hV₂ : ∀ v : V, v + v = 0)
    {alpha : ℕ} (halpha : 2 ≤ alpha) (r p : ℕ) (eta : ℤ_[2]ˣ)
    (z : (V × V) × (Fin h → V × V)) (hS₂ : s ^ E omega2 = 1) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark s 1
        (fun i ↦ wPmCompactPhaseNormal h z (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E₂ (mpcWUnit alpha r p eta h) =
      wPhCompactWallHandlePhase q0 h z := by
  rw [hessRelZ_mpcUnit_unramified_compactPhase dat hdat s E E₂ hV₂ halpha r p eta z
    (fun v ↦ by rw [hS₂, one_smul]) hE he, hS₂, one_pow, hdat.m_one, add_zero]

/-- The resulting honest quadratic phase has the standard even-degree Gauss sum. -/
theorem gaussSum_mpcUnit_unramified_compactPhase
    [Finite C] [Fintype V] (hV₂ : ∀ v : V, v + v = 0)
    {alpha : ℕ} (halpha : 2 ≤ alpha) (r p : ℕ) (eta : ℤ_[2]ˣ)
    (hS₂ : s ^ E omega2 = 1) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (hquad : IsQuadraticFp2 q0) (hns : Nonsingular q0) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m)) :
    QuadraticFp2.gaussSum (fun z : (V × V) × (Fin h → V × V) ↦
      hessRelZ (Certificates.hessMark s 1
        (fun i ↦ wPmCompactPhaseNormal h z (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E₂ (mpcWUnit alpha r p eta h)) =
      (standardNumerics (2 * h + 2)).gaussRam m := by
  have H : (fun z : (V × V) × (Fin h → V × V) ↦
      hessRelZ (Certificates.hessMark s 1
        (fun i ↦ wPmCompactPhaseNormal h z (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E₂ (mpcWUnit alpha r p eta h)) =
      wPhCompactWallHandlePhase q0 h := by
    funext z
    exact hessRelZ_mpcUnit_unramified_compactPhase_of_sigma2_one dat hdat s E E₂ hV₂
      halpha r p eta z hS₂ hE he
  rw [H]
  exact wPh_compactWallHandlePhase_gaussSum_standardRam hquad hns hcard h

end Phase

section Mobile

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q0 : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
  [Finite C] [Finite V] {alpha r p h q : ℕ}

/-- The actual normalized, corrected, spliced source has the compact quadratic phase. -/
theorem hessRelZ_mpcMobileTameSplice_unramified_compactPhase
    (hq0 : q ≠ 0) (hqe : Even q) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (halpha2 : 2 ≤ alpha) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (s : C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hV₂ : ∀ v : V, v + v = 0)
    (z : (V × V) × (Fin h → V × V)) (hS₂ : s ^ E omega2 = 1)
    (hSk : ∀ a : ℤ_[2], s ^ E (padicOmega2 a) = 1)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark s 1
        (fun i ↦ wPmCompactPhaseNormal h z (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E₂
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) = wPhCompactWallHandlePhase q0 h z := by
  let mu := Certificates.hessMark s 1
    (fun i ↦ wPmCompactPhaseNormal h z (Generator.wild i))
  have H : hessEvalZ mu (kappa0Cocycle dat hdat) E E₂
      (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
        (MCompact.mCompactW alpha h)) =
      hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ (mpcWUnit alpha r p eta h) := by
    rw [hessEvalZ_tameSplice_unramified dat hdat mu E E₂ hV₂ rfl
      (fun _ ↦ rfl) hE he]
    unfold mpcMobileTameCorrectedW tamePrimeToTwoCorrectedWord
    rw [hessEvalZ_tauCorrection_of_tau_one mu _ E E₂ rfl]
    unfold mpcMobileNormalizedW
    exact hessEvalZ_wildShearBackward_of_sigma_normal dat hdat mu E E₂ _ rfl
      (fun i ↦ hSk _) _
  change (hessEvalZ mu (kappa0Cocycle dat hdat) E E₂ _).fib = _
  rw [H]
  exact hessRelZ_mpcUnit_unramified_compactPhase_of_sigma2_one dat hdat s E E₂ hV₂
    halpha2 r p eta z hS₂ hE he

/-- The actual mobile splice, rather than just its polarized model, has the required Gauss sum. -/
theorem gaussSum_mpcMobileTameSplice_unramified_compactPhase
    [Fintype V] (hq0 : q ≠ 0) (hqe : Even q) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (halpha2 : 2 ≤ alpha) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (s : C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hV₂ : ∀ v : V, v + v = 0)
    (hS₂ : s ^ E omega2 = 1) (hSk : ∀ a : ℤ_[2], s ^ E (padicOmega2 a) = 1)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (hquad : IsQuadraticFp2 q0) (hns : Nonsingular q0) {m : ℕ}
    (hcard : Fintype.card V = 2 ^ (2 * m)) :
    QuadraticFp2.gaussSum (fun z : (V × V) × (Fin h → V × V) ↦
      hessRelZ (Certificates.hessMark s 1
        (fun i ↦ wPmCompactPhaseNormal h z (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E₂
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h))) = (standardNumerics (2 * h + 2)).gaussRam m := by
  have H : (fun z : (V × V) × (Fin h → V × V) ↦
      hessRelZ (Certificates.hessMark s 1
        (fun i ↦ wPmCompactPhaseNormal h z (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E₂
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h))) = wPhCompactWallHandlePhase q0 h := by
    funext z
    exact hessRelZ_mpcMobileTameSplice_unramified_compactPhase dat hdat hq0 hqe eta
      halpha halpha2 nuP s E E₂ hV₂ z hS₂ hSk hE he
  rw [H]
  exact wPh_compactWallHandlePhase_gaussSum_standardRam hquad hns hcard h

end Mobile

#print axioms hessRelZ_mpcUnit_eq_lit
#print axioms hessRelZ_mpcUnit_unramified_handles
#print axioms hessRelZ_mpcUnit_unramified_compactPhase
#print axioms hessRelZ_mpcUnit_unramified_compactPhase_of_sigma2_one
#print axioms gaussSum_mpcUnit_unramified_compactPhase
#print axioms hessRelZ_mpcMobileTameSplice_unramified_compactPhase
#print axioms gaussSum_mpcMobileTameSplice_unramified_compactPhase

end
end GQ2.Dyadic.Instances.MpcMobileUnramifiedPhase
