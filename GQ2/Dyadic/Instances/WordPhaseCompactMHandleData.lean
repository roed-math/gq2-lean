/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Certificates.M0Assembly
import GQ2.Dyadic.Instances.MpcJetGeneral
import GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedData

/-!
# Compact-M phase data with handles

This file extends the honest ramified compact-M Hessian calculation from handle count zero to
arbitrary handle count.  The core calculation is unchanged; the handle tail contributes the
central hyperbolic sum through `MpcJet.evalFin_handlesW`.  It also records the existing
general-h unramified calculation in compact phase coordinates and carries both branches through
the graph-Hessian trace seam.
-/

namespace GQ2.Dyadic.Certificates.MCompactRamified

noncomputable section

open GQ2 GQ2.FoxH GQ2.QuadraticFp2
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Certificates.MpcJet

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- The honest ramified compact-M evaluation at arbitrary handle count. -/
theorem evalFin_mCompact_ramified_handles {h : ℕ} [Finite C] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (alpha : ℕ) (s u : C)
    (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (vv : Fin (2 + 2 * h + 1) → V) (hv2 : vv (coreIdx h 2) = 0)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂
        (mCompactW alpha h)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (q (vv (coreIdx h 1)) +
            polar q (vv (coreIdx h 0)) (vv (coreIdx h 1)) +
            ∑ j, polar q (vv (Certificates.hIdxU j))
              (vv (Certificates.hIdxV j))) := by
  let K : C := (powOmega2 s) ^ (mOf alpha)
  let p₀ : ZMod 2 := NpcJet.powCharge dat u (vv (coreIdx h 0)) (orderOf u)
  let p₁ : ZMod 2 := NpcJet.powCharge dat u (vv (coreIdx h 1)) (orderOf u)
  have hqinv : ∀ (g : C) (v : V), q (g • v) = q v :=
    Certificates.LSqStokes.factorSet_q_invariant dat hdat hV2
  have htail : ((handleTailW h).map
      (PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ ·)).prod =
      PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (handlesW h) := by
    match h with
    | 0 => simp [handleTailW, handlesW]
    | h + 1 => simp [handleTailW]
  rw [mCompactW, evalFin_prodList, List.map_append, List.prod_append, htail,
    evalFin_handlesW dat hdat hV2 s u vv E E₂]
  simp only [mFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [PWord.evalFin_zpow, PWord.evalFin_comm,
    evalFin_a0W_hess dat hdat s u vv E E₂ alpha,
    PWord.evalFin_gen, hessLift_coreLetter,
    show 2 * (mOf alpha : ℤ) = ((2 * mOf alpha : ℕ) : ℤ) by norm_num,
    evalFin_sigma2Pow_hess dat hdat s u vv E E₂ (2 * mOf alpha),
    evalFin_j2W_one dat hdat s u hu hVu vv hv2 E E₂,
    evalFin_eRevW_hess dat hdat hV2 s u hu hVu vv E E₂ alpha]
  have hK2 : (powOmega2 s) ^ (2 * mOf alpha) = K ^ 2 := by
    dsimp only [K]
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [hK2]
  rw [show WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (q (vv (coreIdx h 1)) +
          polar q (vv (coreIdx h 0)) (vv (coreIdx h 1)) +
          ∑ j, polar q (vv (Certificates.hIdxU j))
            (vv (Certificates.hIdxV j))) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (q (vv (coreIdx h 1)) +
            polar q (vv (coreIdx h 0)) (vv (coreIdx h 1))) *
        WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (∑ j, polar q (vv (Certificates.hIdxU j))
            (vv (Certificates.hIdxV j))) by
      rw [centExt_incl_mul]]
  have hc := coreCancellation dat hdat hV2 hqinv K
    (vv (coreIdx h 0)) (vv (coreIdx h 1)) p₀ p₁
  rw [← hc]
  have hline2 : hessLine dat hdat (K ^ 2) = hessLine dat hdat K ^ 2 := by
    simpa only [pow_two] using (hessLine_mul dat hdat K K).symm
  rw [hline2]
  dsimp only [K, p₀, p₁]
  simp only [one_mul]
  group

/-- The arbitrary-h `hessRelZ` form of `evalFin_mCompact_ramified_handles`. -/
theorem hessRelZ_mCompact_ramified_handles {h : ℕ} [Finite C] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (alpha : ℕ) (s u : C)
    (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (vv : Fin (2 + 2 * h + 1) → V) (hv2 : vv (coreIdx h 2) = 0)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : Certificates.MProcyclic.ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat) E E₂
        (mCompactW alpha h)
      = q (vv (coreIdx h 1)) +
          polar q (vv (coreIdx h 0)) (vv (coreIdx h 1)) +
          ∑ j, polar q (vv (Certificates.hIdxU j))
            (vv (Certificates.hIdxV j)) := by
  rw [hessRelZ, hessEvalZ,
    Certificates.MProcyclic.evalZ_eq_evalFin_of_resolverLifts hres]
  change WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
    (PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂
      (mCompactW alpha h)) = _
  rw [evalFin_mCompact_ramified_handles dat hdat hV2 alpha s u hu hVu vv hv2 E E₂,
    WordCoh.CentExt.incl_fib]

end

end GQ2.Dyadic.Certificates.MCompactRamified


/-! ## Phase and trace bridges -/

namespace GQ2.Dyadic.Instances.WordPhaseCompactMHandleData

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseSeam
open GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedData
open GQ2.Dyadic.LSquare GQ2.QuadraticFp2

/-- The honest ramified compact-M endpoint before swapping the two head coordinates. -/
def wPcMRamifiedHandlePhase {V : Type} [AddCommGroup V] (q : V → ZMod 2) (h : ℕ) :
    (V × V) × (Fin h → V × V) → ZMod 2 :=
  fun p ↦ q p.1.2 + polar q p.1.1 p.1.2 +
    ∑ j, polar q (p.2 j).1 (p.2 j).2

/-- Swap only the compact head coordinates, leaving every handle plane fixed. -/
def wPcMRamifiedHandleSwap (V : Type) (h : ℕ) :
    ((V × V) × (Fin h → V × V)) ≃ ((V × V) × (Fin h → V × V)) :=
  Equiv.prodCongr (Equiv.prodComm V V) (Equiv.refl _)

/-- The ramified phase is the common compact wall-handle phase after the head swap. -/
theorem wPcMRamifiedHandlePhase_eq_compactWall_swap
    {V : Type} [AddCommGroup V] (q : V → ZMod 2) (h : ℕ)
    (p : (V × V) × (Fin h → V × V)) :
    wPcMRamifiedHandlePhase q h p =
      wPhCompactWallHandlePhase q h (wPcMRamifiedHandleSwap V h p) := by
  simp [wPcMRamifiedHandlePhase, wPhCompactWallHandlePhase,
    wPcMRamifiedHandleSwap, plusFormD, polar_comm]

/-- The existing P1 assembler supplies the arbitrary-h unramified endpoint. -/
theorem wPcM_hessRelZ_eq_compactWallPhase_P1_handles
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v + v = 0) {alpha h : ℕ} (halpha : 2 ≤ alpha) (s : C)
    (p : (V × V) × (Fin h → V × V))
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hsigma2 : ∀ v : V, (s ^ E omega2) • v = v)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ
        (Certificates.hessMark s 1
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E₂ (MCompact.mCompactW alpha h)
      = wPhCompactWallHandlePhase q0 h p := by
  rw [Certificates.MCompact.hessRelZ_mCompact_P1_res dat hdat hV2 halpha s
      (fun i : Fin (2 + 2 * h + 1) ↦
        wPmCompactPhaseNormal h p (Generator.wild i))
      (by
        show wPmCompactPhaseNormal h p (coreLetter h 2) = 0
        rw [wPmCompactPhaseNormal_coreLetter]
        rfl)
      E E₂ hsigma2 hE he]
  show q0 (wPmCompactPhaseNormal h p (coreLetter h 0)) +
      polar q0 (wPmCompactPhaseNormal h p (coreLetter h 0))
        (wPmCompactPhaseNormal h p (coreLetter h 1)) +
      ∑ j, polar q0 (wPmCompactPhaseNormal h p (handleU j))
        (wPmCompactPhaseNormal h p (handleV j)) = _
  rw [wPmCompactPhaseNormal_coreLetter, wPmCompactPhaseNormal_coreLetter]
  simp only [wPmCompactPhaseNormal_handleU, wPmCompactPhaseNormal_handleV,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- The honest ramified Hessian in arbitrary-h compact normal coordinates. -/
theorem wPcM_hessRelZ_eq_ramifiedHandlePhase
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q0 dat) [Finite C] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) {alpha h : ℕ} (s u : C)
    (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (p : (V × V) × (Fin h → V × V))
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : Certificates.MProcyclic.ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ
        (Certificates.hessMark s u
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E₂ (MCompact.mCompactW alpha h)
      = wPcMRamifiedHandlePhase q0 h p := by
  rw [Certificates.MCompactRamified.hessRelZ_mCompact_ramified_handles
    dat hdat hV2 alpha s u hu hVu
      (fun i : Fin (2 + 2 * h + 1) ↦
        wPmCompactPhaseNormal h p (Generator.wild i))
      (by
        show wPmCompactPhaseNormal h p (coreLetter h 2) = 0
        rw [wPmCompactPhaseNormal_coreLetter]
        rfl)
      E E₂ hres]
  show q0 (wPmCompactPhaseNormal h p (coreLetter h 1)) +
      polar q0 (wPmCompactPhaseNormal h p (coreLetter h 0))
        (wPmCompactPhaseNormal h p (coreLetter h 1)) +
      ∑ j, polar q0 (wPmCompactPhaseNormal h p (handleU j))
        (wPmCompactPhaseNormal h p (handleV j)) = _
  rw [wPmCompactPhaseNormal_coreLetter, wPmCompactPhaseNormal_coreLetter]
  simp only [wPmCompactPhaseNormal_handleU, wPmCompactPhaseNormal_handleV,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- The graph-Hessian trace reaches the ramified arbitrary-h phase on an honest head. -/
theorem wPcM_QZero_eq_ramifiedHandlePhase_of_headMark
    {alpha h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
        (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    (hdat : IsEquivariantFactorSet DD.qbar DD.dat)
    (hq : Even q) (hq0 : q ≠ 0) (halpha : 2 ≤ alpha) (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) (.wild i)) = 1)
    (htauOdd : Odd (orderOf (rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau))))
    (htauFpf : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau) • v = v → v = 0)
    (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i))
      = wPmCompactPhaseNormal h p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
        (ZMod 2) := scalarActionZmodTwo _
    letI : ContinuousSMul
        ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
        (ZMod 2) := scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPcMRamifiedHandlePhase DD.qbar h p := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR (2 + 2 * h) q (MCompact.mCompactW alpha h) : ProfiniteGrp) : Type)
      (ZMod 2) := scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  set E : Zhat → ℤ := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : ℤ)
  set E₂ : ℤ_[2] → ℤ := fun _ ↦ (omega2Exp (4 * Monoid.exponent L) : ℤ)
  have hcval : ∀ i, c.c
      (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i) =
        wPmCompactPhaseNormal h p i := fun i ↦ congrFun hc i
  have hmark :
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) i)) =
        Certificates.hessMark (h := h)
          (rho0 DD rho
            (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma))
          (rho0 DD rho
            (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau))
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma h p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau h p)) rfl
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  have hres : MProcyclic.ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle DD.dat hdat)) := by
    simpa only [E, L] using
      wPcM_resolverLifts_graphTrace DD.dat hdat (Vmod_exp2 DD)
  rw [wPs_QZero_eq_mCompact_graphHessianTrace
      (α := alpha) (h := h) (q := q) rho hdat hq hq0 halpha c]
  rw [show (fun _ : Zhat ↦
        (omega2Exp (4 * Monoid.exponent L) : ℤ)) = E from rfl,
    show (fun _ : ℤ_[2] ↦
        (omega2Exp (4 * Monoid.exponent L) : ℤ)) = E₂ from rfl,
    hmark, wPs_hessRelZ_tameRelW_hessMark_eq_zero DD.dat hdat _ _ _ E E₂,
    zero_add,
    wPcM_hessRelZ_eq_ramifiedHandlePhase DD.dat hdat (Vmod_exp2 DD)
      (s := rho0 DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .sigma))
      (u := rho0 DD rho
        (gammaGen (2 + 2 * h) q (MCompact.mCompactW alpha h) .tau))
      htauOdd htauFpf p E E₂ hres]

/-! ## Axiom audit -/

#print axioms GQ2.Dyadic.Certificates.MCompactRamified.evalFin_mCompact_ramified_handles
#print axioms GQ2.Dyadic.Certificates.MCompactRamified.hessRelZ_mCompact_ramified_handles
#print axioms wPcMRamifiedHandlePhase
#print axioms wPcMRamifiedHandleSwap
#print axioms wPcMRamifiedHandlePhase_eq_compactWall_swap
#print axioms wPcM_hessRelZ_eq_compactWallPhase_P1_handles
#print axioms wPcM_hessRelZ_eq_ramifiedHandlePhase
#print axioms wPcM_QZero_eq_ramifiedHandlePhase_of_headMark

end

end GQ2.Dyadic.Instances.WordPhaseCompactMHandleData
