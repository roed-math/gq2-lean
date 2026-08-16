/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcWordPhaseData

/-!
# Procyclic-M phase data at arbitrary handle count

This module removes the handle-zero and canonical-display restrictions from the reusable
first-order Mpc phase layer.  Both unramified and ramified resolved families have scaled-pivot
rows and compact normal representatives at every handle count.  On the ramified branch the
word Hessian reaches the common compact wall-handle phase for every display, and the full source
comparison is reduced to the corresponding projected head-phase identity.

The unramified quadratic evaluation for a non-canonical display is deliberately not asserted
here; its factor-set charge is the remaining analytic input to that branch.
-/

namespace GQ2.Dyadic.Instances.MpcHandlePhaseData

noncomputable section

open GQ2 GQ2.FoxH GQ2.QuadraticFp2
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Words.Mpc GQ2.Dyadic.Certificates
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Certificates.MpcJet
open GQ2.Dyadic.MProcyclicExact GQ2.Dyadic.MProcyclicUnram
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-- Every displayed resolved Mpc family has a scaled unramified row.  The pivot is exposed
existentially because its value depends on the display-specific resolver. -/
theorem exists_resolvedFamily_unramified_smul_row
    {alpha r pp h q : ℕ} {eta : EtaDisplay}
    {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (t : Marking (2 + 2 * h) C) (hV2 : ∀ v : V, v + v = 0)
    (halpha : 1 ≤ alpha) (hq : Even q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (htau : ∀ v : V, t.τ • v = v)
    (hsigma2 : ∀ v : V, powOmega2 t.σ • v = v) :
    ∃ u : C, ∀ x : Generator (2 + 2 * h) → V,
      heisD1 ⇑t
          (resolvedFamily alpha r pp h q eta (4 * Monoid.exponent C)) x =
        ![t.σ⁻¹ • x .tau,
          x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))] := by
  obtain ⟨E, E2, hfam, hlift, -⟩ :=
    exists_resolver_resolvedFamily (alpha := alpha) (r := r) (pp := pp)
      (h := h) (q := q) (C := C) (A := V) (B := V) eta hV2 hV2
  let u := PWord.evalFin ⇑t E E2 (eta.toPWord (n := 2 + 2 * h))
  refine ⟨u, fun x ↦ ?_⟩
  rw [hfam]
  exact heisD1_mpcFamOf_unramified_apply t E E2 hlift hV2 halpha hq
    hwild htau hsigma2 rfl x

/-- Every displayed resolved Mpc family has a scaled ramified row.  The pivot is a unit, so
its exact exponent is irrelevant to the compact normal-form theorem. -/
theorem exists_resolvedFamily_ramified_smul_row
    {alpha r pp h q : ℕ} {eta : EtaDisplay}
    {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (t : Marking (2 + 2 * h) C) (hV2 : ∀ v : V, v + v = 0)
    (halpha : 1 ≤ alpha) (htame : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (htauFpf : ∀ v : V, t.τ • v = v → v = 0)
    (htauOdd : ∀ v : V, powOmega2 t.τ • v = v) :
    ∃ u : C, ∀ x : Generator (2 + 2 * h) → V,
      heisD1 ⇑t
          (resolvedFamily alpha r pp h q eta (4 * Monoid.exponent C)) x =
        ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
          u • x (coreLetter h 2)] := by
  obtain ⟨E, E2, hfam, hlift, -⟩ :=
    exists_resolver_resolvedFamily (alpha := alpha) (r := r) (pp := pp)
      (h := h) (q := q) (C := C) (A := V) (B := V) eta hV2 hV2
  obtain ⟨neta, heta⟩ := exists_zpow_evalFin_etaDisplay t E E2 eta
  let u := (powOmega2 t.σ) ^ (-(s r : ℤ)) * t.σ ^ (-neta)
  refine ⟨u, fun x ↦ ?_⟩
  rw [hfam]
  exact heisD1_mpcFamOf_ramified_apply t E E2 hlift hV2 halpha htame
    hwild htauFpf htauOdd heta x

/-- The displayed resolved family resolves the displayed Mpc relators at every handle count. -/
theorem resolvedFamily_resolves_wordLift_handles
    {alpha r pp h q : ℕ} {eta : EtaDisplay}
    {C V : Type} [Group C] [Finite C]
    [TopologicalSpace C] [DiscreteTopology C]
    [AddCommGroup V] [Finite V] [TopologicalSpace V] [DiscreteTopology V]
    [DistribMulAction C V] (hV2 : ∀ v : V, v + v = 0)
    (halpha : 1 ≤ alpha) (hq : Even q) :
    ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp eta h))
      (resolvedFamily alpha r pp h q eta (4 * Monoid.exponent C))
      (WordLift V C) := by
  have hb := resolvesAt_and_endpoint_uniformHeis
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
    (C := C) (A := V) hV2 halpha hq eta
  let incl : ContinuousMonoidHom (WordLift V C) (HeisLift V C) :=
    ⟨heisPrim, continuous_of_discreteTopology⟩
  exact hb.1.pullback incl heisPrim_injective

/-- The quotient marking satisfies the tame relation, independently of the Mpc display. -/
theorem marking_tameRel_handles
    {alpha r pp h q : ℕ} {eta : EtaDisplay}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp h q eta : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] :
    let t : Marking (2 + 2 * h) DD.C0 :=
      ⟨fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp eta h) i)⟩
    t.TameRelAt q := by
  let theta := Count.rho0Continuous DD rho
  let t : Marking (2 + 2 * h) DD.C0 :=
    ⟨fun i ↦ theta (gammaGen (2 + 2 * h) q (mpcW alpha r pp eta h) i)⟩
  have hrel := (isAdmissibleMarkedPresentation_gammaR
    (2 + 2 * h) q (mpcW alpha r pp eta h)).rel theta (0 : Fin 2)
  change PWord.eval ⇑t (tameRelW (2 + 2 * h) q) = 1 at hrel
  rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
  exact mul_inv_eq_one.mp hrel

/-- The arbitrary-h compact representative is closed for every scaled ramified pivot. -/
theorem compactNormal_closed_of_ramified_smul_row
    {h q : ℕ} {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → V, heisD1 ⇑t w x =
      ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
        u • x (coreLetter h 2)])
    (p : (V × V) × (Fin h → V × V)) :
    heisD1 ⇑t w (wPmCompactPhaseNormal h p) = 0 := by
  rw [wPmCompactPhaseNormal]
  exact heisD1_evenNormal_eq_zero_of_smul_row
    (h := h) (q := q) (C := C) (A := V) t w u hrow _ _ _

/-- The arbitrary-h compact representative is the unique normal form for a scaled ramified
pivot. -/
theorem compactNormalForm_of_ramified_smul_row
    {h q : ℕ} {C V : Type} [Group C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → V, heisD1 ⇑t w x =
      ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
        u • x (coreLetter h 2)])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (htauFpf : ∀ v : V, t.τ • v = v → v = 0)
    (hr : ∀ k, FreeGroup.lift ⇑t (w k) = 1) :
    ∀ x, heisD1 ⇑t w x = 0 →
      ∃! p : (V × V) × (Fin h → V × V),
        x - wPmCompactPhaseNormal h p ∈ Set.range (heisD0 ⇑t) := by
  intro x hx
  obtain ⟨coords, hcoords, huniq⟩ :=
    evenNormalForm_of_smul_row (h := h) (q := q) (C := C) (A := V)
      t w u hrow hwild htauFpf hr x hx
  refine ⟨wPmCompactCoordsEquiv h V coords, ?_, ?_⟩
  · show x - wPmCompactPhaseNormal h (wPmCompactCoordsEquiv h V coords) ∈ _
    rw [wPmCompactPhaseNormal_coordsEquiv]
    exact hcoords
  · intro p hp
    have hpc : (wPmCompactCoordsEquiv h V).symm p = coords := by
      refine huniq _ ?_
      show x - evenNormal h ((wPmCompactCoordsEquiv h V).symm p).1
        ((wPmCompactCoordsEquiv h V).symm p).2.1
        ((wPmCompactCoordsEquiv h V).symm p).2.2 ∈ _
      exact hp
    rw [← hpc, Equiv.apply_symm_apply]

/-- The arbitrary-h compact representative is closed for every scaled unramified pivot. -/
theorem compactNormal_closed_of_unramified_smul_row
    {h : ℕ} {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → V, heisD1 ⇑t w x =
      ![t.σ⁻¹ • x .tau,
        x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))])
    (p : (V × V) × (Fin h → V × V)) :
    heisD1 ⇑t w (wPmCompactPhaseNormal h p) = 0 := by
  rw [wPmCompactPhaseNormal]
  exact heisD1_evenNormal_eq_zero_of_unram_smul_row
    (h := h) (C := C) (A := V) t w u hrow _ _ _

/-- The arbitrary-h compact representative is the unique normal form for a scaled unramified
pivot. -/
theorem compactNormalForm_of_unramified_smul_row
    {h : ℕ} {C V : Type} [Group C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (t : Marking (2 + 2 * h) C)
    (w : Fin 2 → FreeGroup (Generator (2 + 2 * h))) (u : C)
    (hrow : ∀ x : Generator (2 + 2 * h) → V, heisD1 ⇑t w x =
      ![t.σ⁻¹ • x .tau,
        x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))])
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (htau : ∀ v : V, t.τ • v = v)
    (hsigmaFpf : ∀ v : V, t.σ • v = v → v = 0)
    (huFpf : ∀ v : V, u • v = v → v = 0) :
    ∀ x, heisD1 ⇑t w x = 0 →
      ∃! p : (V × V) × (Fin h → V × V),
        x - wPmCompactPhaseNormal h p ∈ Set.range (heisD0 ⇑t) := by
  intro x hx
  obtain ⟨coords, hcoords, huniq⟩ :=
    evenNormalForm_of_unram_smul_row (h := h) (C := C) (A := V)
      t w u hrow hwild htau hsigmaFpf huFpf x hx
  refine ⟨wPmCompactCoordsEquiv h V coords, ?_, ?_⟩
  · show x - wPmCompactPhaseNormal h (wPmCompactCoordsEquiv h V coords) ∈ _
    rw [wPmCompactPhaseNormal_coordsEquiv]
    exact hcoords
  · intro p hp
    have hpc : (wPmCompactCoordsEquiv h V).symm p = coords := by
      refine huniq _ ?_
      show x - evenNormal h ((wPmCompactCoordsEquiv h V).symm p).1
        ((wPmCompactCoordsEquiv h V).symm p).2.1
        ((wPmCompactCoordsEquiv h V).symm p).2.2 ∈ _
      exact hp
    rw [← hpc, Equiv.apply_symm_apply]

/-- The arbitrary-display ramified Mpc Hessian is the common compact wall-handle phase. -/
theorem hessRelZ_mpcW_ramified_compactPhase
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    {q0 : V → ZMod 2} (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q0 dat) [Finite C] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) {alpha r pp h : ℕ} {eta : EtaDisplay}
    (halpha : 1 ≤ alpha) (s u : C)
    (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (p : (V × V) × (Fin h → V × V))
    (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ) {neta : ℤ}
    (heta : ActsAsPow (lowerMark (h := h) s u).σ neta
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E2
        (eta.toPWord (n := 2 + 2 * h))) V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ
        (Certificates.hessMark s u
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)))
        (kappa0Cocycle dat hdat) E E2 (mpcW alpha r pp eta h) =
      wPhCompactWallHandlePhase q0 h p := by
  rw [hessRelZ_mpcW_handles dat hdat s u _ E E2 hV2 hu hVu
      (by
        show wPmCompactPhaseNormal h p (coreLetter h 2) = 0
        rw [wPmCompactPhaseNormal_coreLetter]
        rfl)
      halpha r pp heta hres]
  show q0 (wPmCompactPhaseNormal h p (coreLetter h 0)) +
      polar q0 (wPmCompactPhaseNormal h p (coreLetter h 0))
        (wPmCompactPhaseNormal h p (coreLetter h 1)) +
      ∑ j, polar q0 (wPmCompactPhaseNormal h p (handleU j))
        (wPmCompactPhaseNormal h p (handleV j)) = _
  rw [wPmCompactPhaseNormal_coreLetter, wPmCompactPhaseNormal_coreLetter]
  simp only [wPmCompactPhaseNormal_handleU, wPmCompactPhaseNormal_handleV,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- At arbitrary handle count and display, the ramified first-order lane reduces a source phase
comparison to the single head-phase identity. -/
noncomputable def comparison_ramified_of_headPhase_handles
    {alpha r pp h q : ℕ} {eta : EtaDisplay}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp h q eta : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r pp h q eta : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r pp h q eta : ProfiniteGrp) : Type) DD.Vmod]
    [DistribMulAction
      ((displayedGamma alpha r pp h q eta : ProfiniteGrp) : Type) (ZMod 2)]
    [ContinuousSMul
      ((displayedGamma alpha r pp h q eta : ProfiniteGrp) : Type) (ZMod 2)]
    (htriv : ∀
      (g : ((displayedGamma alpha r pp h q eta : ProfiniteGrp) : Type))
      (a : ZMod 2), g • a = a)
    (hcompat : ∀
      (g : ((displayedGamma alpha r pp h q eta : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp eta h) i)))
    (halpha : 1 ≤ alpha) (hq : Even q)
    (hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod),
      rho0 DD rho
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp eta h) (.wild i)) • v = v)
    (htauFpf : ∀ v : DD.Vmod,
      rho0 DD rho
        (gammaGen (2 + 2 * h) q (mpcW alpha r pp eta h) .tau) • v = v → v = 0)
    (htauOdd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen (2 + 2 * h) q (mpcW alpha r pp eta h) .tau)) • v = v)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho),
      (fun i ↦ c.c (gammaGen (2 + 2 * h) q (mpcW alpha r pp eta h) i)) =
          wPmCompactPhaseNormal h p →
      QZero DD rho c = wPhCompactWallHandlePhase DD.qbar h p) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  let theta := Count.rho0Continuous DD rho
  let t : Marking (2 + 2 * h) DD.C0 :=
    ⟨fun i ↦ theta (gammaGen (2 + 2 * h) q (mpcW alpha r pp eta h) i)⟩
  have hres : ResolvesAt
      (gammaFam (2 + 2 * h) q (mpcW alpha r pp eta h))
      (resolvedFamily alpha r pp h q eta (4 * Monoid.exponent DD.C0))
      (WordLift DD.Vmod DD.C0) :=
    resolvedFamily_resolves_wordLift_handles hA2 halpha hq
  have htame : t.TameRelAt q := marking_tameRel_handles rho
  have hex := exists_resolvedFamily_ramified_smul_row
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) (eta := eta)
    t hA2 halpha htame hwildAct htauFpf htauOdd
  let u := Classical.choose hex
  have hrow := Classical.choose_spec hex
  have hr : ∀ k, FreeGroup.lift ⇑t
      (resolvedFamily alpha r pp h q eta (4 * Monoid.exponent DD.C0) k) = 1 :=
    fun k ↦ Count.lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR
        (2 + 2 * h) q (mpcW alpha r pp eta h)) hres k
  exact wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
    (wPmCompactPhaseNormal h)
    (compactNormal_closed_of_ramified_smul_row t _ u hrow)
    (compactNormalForm_of_ramified_smul_row t _ u hrow hwildAct htauFpf hr)
    htriv (wPhCompactWallHandlePhase DD.qbar h) hphase

#print axioms compactNormal_closed_of_ramified_smul_row
#print axioms compactNormalForm_of_ramified_smul_row
#print axioms compactNormal_closed_of_unramified_smul_row
#print axioms compactNormalForm_of_unramified_smul_row
#print axioms exists_resolvedFamily_unramified_smul_row
#print axioms exists_resolvedFamily_ramified_smul_row
#print axioms resolvedFamily_resolves_wordLift_handles
#print axioms marking_tameRel_handles
#print axioms hessRelZ_mpcW_ramified_compactPhase
#print axioms comparison_ramified_of_headPhase_handles

end
end GQ2.Dyadic.Instances.MpcHandlePhaseData
