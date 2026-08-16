/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcHandlePhaseData

/-!
# Unramified procyclic-M Hessians with handles and arbitrary display

The displayed procyclic letter evaluates on an unramified Hessian marking to a pure line for
all three EtaDisplay constructors.  Consequently the full arbitrary-display, arbitrary-handle
Mpc Hessian differs from the common compact wall-handle phase only by its factor-set charge.

This file is purely word-side.  Graph-trace and affine charge-removal consumers live in
MpcUnramifiedHandleComparison.
-/

namespace GQ2.Dyadic.Instances.MpcUnramifiedHandleHessian

noncomputable section

open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix GQ2.FoxH
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Certificates.MCompact
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Instances.MpcUnramifiedHessian
open GQ2.Dyadic.Instances.MpcHandlePhaseData
open GQ2.Dyadic.Instances.MpcWordPhaseSeam
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

section Word

variable {h : ℕ} (s : C) (vv : Fin (2 + 2 * h + 1) → V)
  (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)

private noncomputable abbrev mu :=
  WordCoh.lift (Certificates.hessMark s (1 : C) vv) (kappa0Cocycle dat hdat)

/-- Every Mpc display evaluates on an unramified Hessian marking to a pure line. -/
theorem evalZ_etaDisplay_isLine (eta : EtaDisplay) :
    IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2
        (eta.toPWord (n := 2 + 2 * h))) := by
  cases eta with
  | one => exact evalZ_etaOne_isLine dat hdat s vv E E2
  | lit k =>
      rw [EtaDisplay.toPWord, PWord.evalZ_zpow]
      exact IsHessLine.zpow dat hdat ⟨s, rfl⟩ k
  | hat num den =>
      rw [EtaDisplay.toPWord, PWord.evalZ_profPow]
      exact IsHessLine.zpow dat hdat ⟨s, rfl⟩
        (E (Export.RawSpec.toZhat (.etahat num den)))

/-- The linear copy has the same Hessian charge for every display. -/
theorem evalZ_linFactors_hasCharge_display (hV2 : ∀ v : V, v + v = 0)
    (hv2 : vv (Certificates.x2Idx h) = 0)
    (hS2 : ∀ v : V, (s ^ E omega2) • v = v) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    {alpha : ℕ} (halpha : 2 ≤ alpha) (r pp : ℕ) (eta : EtaDisplay) :
    HasHessCharge dat hdat
      (q (vv (Certificates.x0Idx h)) +
        polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h)) +
        dat.m ((s ^ E omega2) ^ pp) (vv (Certificates.x0Idx h)))
      (PWord.evalZ (mu dat hdat s vv) E E2
        (PWord.prodList (linFactors alpha r pp eta h))) := by
  let f1 : PWord (Generator (2 + 2 * h)) :=
    .zpow (aW h (GQ2.Dyadic.s r) (GQ2.Dyadic.m alpha)) ((2 : ℕ) : ℤ)
  let f2 : PWord (Generator (2 + 2 * h)) :=
    .comm (aW h (GQ2.Dyadic.s r) (GQ2.Dyadic.m alpha)) (bW h pp)
  let f3 : PWord (Generator (2 + 2 * h)) :=
    .zpow (c0W h (GQ2.Dyadic.s r)) ((2 ^ alpha : ℕ) : ℤ)
  let f4 : PWord (Generator (2 + 2 * h)) :=
    .comm (c0W h (GQ2.Dyadic.s r)) (eta.toPWord (n := 2 + 2 * h))
  let f5 : PWord (Generator (2 + 2 * h)) :=
    e01W h (pp + GQ2.Dyadic.s r * GQ2.Dyadic.m alpha)
      (GQ2.Dyadic.s r * GQ2.Dyadic.m alpha)
  let f6 : PWord (Generator (2 + 2 * h)) :=
    e2W h (GQ2.Dyadic.s r) (GQ2.Dyadic.m alpha) pp
  have h1 : HasHessCharge dat hdat (q (vv (Certificates.x0Idx h)))
      (PWord.evalZ (mu dat hdat s vv) E E2 f1) := by
    refine ⟨((((s ^ E omega2) ^ GQ2.Dyadic.s r) ^
      (-(GQ2.Dyadic.m alpha : ℤ))) ^ 2), ?_⟩
    exact evalZ_aSq dat hdat s vv E E2 hV2 hv2 hS2 halpha r
  have h2 : HasHessCharge dat hdat
      (polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h)) +
        dat.m ((s ^ E omega2) ^ pp) (vv (Certificates.x0Idx h)))
      (PWord.evalZ (mu dat hdat s vv) E E2 f2) := by
    refine ⟨1, ?_⟩
    exact evalZ_commAB dat hdat s vv E E2 hV2 hv2 hS2 halpha r pp
  have hc0 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 (c0W h (GQ2.Dyadic.s r))) := by
    rw [evalZ_c0W_line dat hdat s vv E E2 hv2]
    exact ⟨_, rfl⟩
  have h3 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 f3) := by
    rw [PWord.evalZ_zpow]
    exact IsHessLine.zpow dat hdat hc0 _
  have h4 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 f4) := by
    rw [PWord.evalZ_comm]
    exact IsHessLine.comm dat hdat hc0
      (evalZ_etaDisplay_isLine dat hdat s vv E E2 eta)
  have h5 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 f5) := by
    rw [evalZ_e01W_one dat hdat s vv E E2 hV2 hE he]
    exact isHessLine_one dat hdat
  have h6 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 f6) := by
    rw [evalZ_e2W_one dat hdat s vv E E2 hV2 hE he]
    exact isHessLine_one dat hdat
  have htail : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 f3 *
        (PWord.evalZ (mu dat hdat s vv) E E2 f4 *
          (PWord.evalZ (mu dat hdat s vv) E E2 f5 *
            (PWord.evalZ (mu dat hdat s vv) E E2 f6 * 1)))) :=
    IsHessLine.mul dat hdat h3 (IsHessLine.mul dat hdat h4
      (IsHessLine.mul dat hdat h5
        (IsHessLine.mul dat hdat h6 (isHessLine_one dat hdat))))
  have hall := HasHessCharge.mul dat hdat h1
    (HasHessCharge.mul dat hdat h2 htail.hasHessCharge_zero)
  simpa only [PWord.evalZ_prodList, linFactors, f1, f2, f3, f4, f5, f6,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, add_zero, add_assoc] using hall

/-- The replay copy stays on the Hessian line for every display. -/
theorem evalZ_hatFactors_isLine_display (hV2 : ∀ v : V, v + v = 0)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (alpha r pp : ℕ) (eta : EtaDisplay) :
    IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2
        (PWord.prodList (hatFactors alpha r pp eta h))) := by
  let a := aHatW h (GQ2.Dyadic.s r) (GQ2.Dyadic.m alpha)
  let b := bHatW h pp
  let c := c0HatW h (GQ2.Dyadic.s r)
  let d : PWord (Generator (2 + 2 * h)) := eta.toPWord
  let ee := e01W h (pp + GQ2.Dyadic.s r * GQ2.Dyadic.m alpha)
    (GQ2.Dyadic.s r * GQ2.Dyadic.m alpha)
  have ha := evalZ_aHatW_isLine dat hdat s vv E E2 hV2 hE he
    (GQ2.Dyadic.s r) (GQ2.Dyadic.m alpha)
  have hb := evalZ_bHatW_isLine dat hdat s vv E E2 hV2 hE he pp
  have hc : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 c) := by
    rw [evalZ_c0HatW_line dat hdat s vv E E2]
    exact ⟨_, rfl⟩
  have hd := evalZ_etaDisplay_isLine dat hdat s vv E E2 eta
  have hee : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 ee) := by
    rw [evalZ_e01W_one dat hdat s vv E E2 hV2 hE he]
    exact isHessLine_one dat hdat
  have h1 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 (.zpow a ((2 : ℕ) : ℤ))) := by
    rw [PWord.evalZ_zpow]
    exact IsHessLine.zpow dat hdat ha _
  have h2 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 (.comm a b)) := by
    rw [PWord.evalZ_comm]
    exact IsHessLine.comm dat hdat ha hb
  have h3 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 (.zpow c ((2 ^ alpha : ℕ) : ℤ))) := by
    rw [PWord.evalZ_zpow]
    exact IsHessLine.zpow dat hdat hc _
  have h4 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 (.comm c d)) := by
    rw [PWord.evalZ_comm]
    exact IsHessLine.comm dat hdat hc hd
  have hall := IsHessLine.mul dat hdat h1 (IsHessLine.mul dat hdat h2
    (IsHessLine.mul dat hdat h3 (IsHessLine.mul dat hdat h4
      (IsHessLine.mul dat hdat hee (isHessLine_one dat hdat)))))
  simpa only [PWord.evalZ_prodList, hatFactors, a, b, c, d, ee,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] using hall

/-- The displayed Mpc factorization in the resolver-driven denotation. -/
theorem evalZ_mpcW_factored (alpha r pp : ℕ) (eta : EtaDisplay) :
    PWord.evalZ (mu dat hdat s vv) E E2 (mpcW alpha r pp eta h) =
      PWord.evalZ (mu dat hdat s vv) E E2 (mpcLinW alpha r pp eta h) *
        PWord.evalZ (mu dat hdat s vv) E E2 (mpcHatW alpha r pp eta h) *
        PWord.evalZ (mu dat hdat s vv) E E2 (plusW h) *
        PWord.evalZ (mu dat hdat s vv) E E2 (handlesW h) := by
  have htail : ((handleTailW h).map
      (PWord.evalZ (mu dat hdat s vv) E E2 ·)).prod =
      PWord.evalZ (mu dat hdat s vv) E E2 (handlesW h) := by
    match h with
    | 0 => simp [handleTailW, handlesW]
    | h + 1 => simp [handleTailW]
  rw [mpcW, mpcLinW, mpcHatW, plusW, PWord.evalZ_prodList,
    PWord.evalZ_prodList, PWord.evalZ_prodList, PWord.evalZ_prodList,
    List.map_append, List.map_append, List.map_append, List.prod_append,
    List.prod_append, List.prod_append, htail]

/-- Honest arbitrary-display, arbitrary-h unramified Mpc Hessian formula. -/
theorem hessRelZ_mpcW_unramified_handles
    [Finite C] [Finite V] (hV2 : ∀ v : V, v + v = 0)
    {alpha : ℕ} (halpha : 2 ≤ alpha) (r pp : ℕ) (eta : EtaDisplay)
    (hv2 : vv (Certificates.x2Idx h) = 0)
    (hS2 : ∀ v : V, (s ^ E omega2) • v = v) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark s 1 vv)
        (kappa0Cocycle dat hdat) E E2 (mpcW alpha r pp eta h) =
      q (vv (Certificates.x0Idx h)) +
        polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h)) +
        dat.m ((s ^ E omega2) ^ pp) (vv (Certificates.x0Idx h)) +
        ∑ j, polar q (vv (Certificates.hIdxU j))
          (vv (Certificates.hIdxV j)) := by
  let coreCharge := q (vv (Certificates.x0Idx h)) +
    polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h)) +
    dat.m ((s ^ E omega2) ^ pp) (vv (Certificates.x0Idx h))
  let handleCharge := ∑ j, polar q (vv (Certificates.hIdxU j))
    (vv (Certificates.hIdxV j))
  have hlin : HasHessCharge dat hdat coreCharge
      (PWord.evalZ (mu dat hdat s vv) E E2 (mpcLinW alpha r pp eta h)) := by
    simpa only [mpcLinW, coreCharge] using
      evalZ_linFactors_hasCharge_display dat hdat s vv E E2 hV2 hv2 hS2
        hE he halpha r pp eta
  have hhat : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 (mpcHatW alpha r pp eta h)) := by
    simpa only [mpcHatW] using
      evalZ_hatFactors_isLine_display dat hdat s vv E E2 hV2 hE he alpha r pp eta
  have hplus : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E2 (plusW h)) := by
    rw [evalZ_plusW_one dat hdat s vv E E2 hV2 hE he]
    exact isHessLine_one dat hdat
  have hhandles : HasHessCharge dat hdat handleCharge
      (PWord.evalZ (mu dat hdat s vv) E E2 (handlesW h)) := by
    refine ⟨1, ?_⟩
    rw [Certificates.hess_handlesW_eval dat hdat hV2 s 1 vv E E2,
      hessLineZ_incl]
  have hall := HasHessCharge.mul dat hdat
    (HasHessCharge.mul dat hdat
      (HasHessCharge.mul dat hdat hlin hhat.hasHessCharge_zero)
      hplus.hasHessCharge_zero) hhandles
  have heval : HasHessCharge dat hdat (coreCharge + handleCharge)
      (PWord.evalZ (mu dat hdat s vv) E E2 (mpcW alpha r pp eta h)) := by
    rw [evalZ_mpcW_factored dat hdat s vv E E2 alpha r pp eta]
    simpa only [add_zero] using hall
  rw [hessRelZ, hessEvalZ]
  change (PWord.evalZ (mu dat hdat s vv) E E2
    (mpcW alpha r pp eta h)).fib = _
  rcases heval with ⟨g, hg⟩
  rw [hg, hessLineZ_fib]

/-- The arbitrary-display formula in compact normal coordinates. -/
theorem hessRelZ_mpcW_unramified_compactPhase
    [Finite C] [Finite V] (hV2 : ∀ v : V, v + v = 0)
    {alpha : ℕ} (halpha : 2 ≤ alpha) (r pp : ℕ) (eta : EtaDisplay)
    (p : (V × V) × (Fin h → V × V))
    (hS2 : ∀ v : V, (s ^ E omega2) • v = v) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ
        (Certificates.hessMark s 1
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E2 (mpcW alpha r pp eta h) =
      wPhCompactWallHandlePhase q h p +
        dat.m ((s ^ E omega2) ^ pp) p.1.1 := by
  rw [hessRelZ_mpcW_unramified_handles dat hdat s _ E E2 hV2
    halpha r pp eta
    (by
      show wPmCompactPhaseNormal h p (coreLetter h 2) = 0
      rw [wPmCompactPhaseNormal_coreLetter]
      rfl)
    hS2 hE he]
  show q (wPmCompactPhaseNormal h p (coreLetter h 0)) +
      polar q (wPmCompactPhaseNormal h p (coreLetter h 0))
        (wPmCompactPhaseNormal h p (coreLetter h 1)) +
      dat.m ((s ^ E omega2) ^ pp)
        (wPmCompactPhaseNormal h p (coreLetter h 0)) +
      ∑ j, polar q (wPmCompactPhaseNormal h p (handleU j))
        (wPmCompactPhaseNormal h p (handleV j)) = _
  rw [wPhCompactWallHandlePhase, plusFormD_apply,
    wPmCompactPhaseNormal_coreLetter, wPmCompactPhaseNormal_coreLetter]
  simp only [wPmCompactPhaseNormal_handleU, wPmCompactPhaseNormal_handleV,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

#print axioms evalZ_etaDisplay_isLine
#print axioms evalZ_linFactors_hasCharge_display
#print axioms evalZ_hatFactors_isLine_display
#print axioms evalZ_mpcW_factored
#print axioms hessRelZ_mpcW_unramified_handles
#print axioms hessRelZ_mpcW_unramified_compactPhase

end Word

end

end GQ2.Dyadic.Instances.MpcUnramifiedHandleHessian
