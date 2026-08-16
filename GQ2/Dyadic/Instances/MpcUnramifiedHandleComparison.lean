/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcUnramifiedHandleHessian
import GQ2.Dyadic.Instances.PlusFormLinearShift

/-!
# Unramified procyclic-M comparisons with handles and arbitrary display

This module carries the arbitrary-display Hessian through the graph trace, extends the affine
first-slot charge removal to compact wall-handle coordinates, and reduces the source comparison
to an explicit scaled unramified pivot row with a fixed-point-free pivot.  It does not assert
that projected boundary transport supplies that pivot premise.
-/

namespace GQ2.Dyadic.Instances.MpcUnramifiedHandleComparison

noncomputable section

open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix GQ2.FoxH
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Instances.MpcHandlePhaseData
open GQ2.Dyadic.Instances.MpcWordPhaseSeam
open GQ2.Dyadic.Instances.MpcUnramifiedHandleHessian
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.PlusFormLinearShift

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

section QZero

/-- The graph trace reaches the charged compact wall-handle phase on an honest unramified
head, at every display and handle count. -/
theorem wPmpc_QZero_eq_unramifiedCompactPhase_of_headMark
    {alpha r pp h qrel : ℕ} {eta : EtaDisplay}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    (halpha : 2 ≤ alpha) (hqrel : Even qrel)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)
    (hresolved :
      letI : Finite (SectionSix.SemiProd DD.C0 DD.Vmod) :=
        inferInstanceAs (Finite (DD.Vmod × DD.C0))
      letI : Finite (WordCoh.CentExt (kappa0Cocycle DD.dat DD.hdat)) :=
        inferInstance
      letI : TopologicalSpace
          (WordCoh.CentExt (kappa0Cocycle DD.dat DD.hdat)) := ⊥
      letI : DiscreteTopology
          (WordCoh.CentExt (kappa0Cocycle DD.dat DD.hdat)) := ⟨rfl⟩
      ∀ k, PWord.ResolvedAt
        (WordCoh.lift
          (fun i ↦ graphSemiProdHom c
            (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp eta h) i))
          (kappa0Cocycle DD.dat DD.hdat)) E E2
        (gammaFam (2 + 2 * h) qrel (mpcW alpha r pp eta h) k))
    (s : DD.C0) (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hmark :
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp eta h) i)) =
        Certificates.hessMark (h := h) s 1
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)))
    (hS2 : ∀ v : DD.Vmod, (s ^ E omega2) • v = v) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPhCompactWallHandlePhase DD.qbar h p +
      DD.dat.m ((s ^ E omega2) ^ pp) p.1.1 := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  rw [wPmpc_QZero_eq_graphHessianTrace rho DD.hdat (by omega) hqrel
      hcardH2 c E E2 hresolved, hmark]
  rw [GQ2.Dyadic.Instances.WordPhaseSeam.wPs_hessRelZ_tameRelW_hessMark_eq_zero
      DD.dat DD.hdat s 1 _ E E2,
    zero_add,
    hessRelZ_mpcW_unramified_compactPhase DD.dat DD.hdat s E E2
      (Vmod_exp2 DD) halpha r pp eta p hS2 hE he]

#print axioms wPmpc_QZero_eq_unramifiedCompactPhase_of_headMark

end QZero

section Shift

/-- A first-slot linear charge on the compact wall-handle phase is absorbed by translating
only the second head coordinate. -/
theorem exists_compactWallHandle_firstLinear_translation
    {V : Type} [AddCommGroup V] [Fintype V] {q0 : V → ZMod 2}
    (hq : IsQuadraticFp2 q0) (hns : Nonsingular q0)
    (ell : V →+ ZMod 2) (h : ℕ) :
    ∃ e : ((V × V) × (Fin h → V × V)) ≃
        ((V × V) × (Fin h → V × V)),
      ∀ p, wPhCompactWallHandlePhase q0 h p + ell p.1.1 =
        wPhCompactWallHandlePhase q0 h (e p) := by
  obtain ⟨e0, he0⟩ := exists_plusFormD_firstLinear_translation hq hns ell
  let e := Equiv.prodCongr e0 (Equiv.refl (Fin h → V × V))
  refine ⟨e, ?_⟩
  rintro ⟨p, z⟩
  change plusFormD q0 q0 p + (∑ j, polar q0 (z j).1 (z j).2) + ell p.1 =
    plusFormD q0 q0 (e0 p) + ∑ j, polar q0 (z j).1 (z j).2
  rw [← he0 p]
  abel

/-- Reindex a charged compact wall-handle comparison to the unshifted endpoint. -/
theorem SourceWordPhaseComparison.remove_compactWallHandle_firstLinear
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [DistribMulAction Gamma (ZMod 2)]
    {htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a}
    {V : Type} [AddCommGroup V] [Fintype V] {q0 : V → ZMod 2}
    (hq : IsQuadraticFp2 q0) (hns : Nonsingular q0)
    (ell : V →+ ZMod 2) (h : ℕ)
    (C0 : SourceWordPhaseComparison DD rho htriv
      ((V × V) × (Fin h → V × V))
      (fun p ↦ wPhCompactWallHandlePhase q0 h p + ell p.1.1)) :
    Nonempty (SourceWordPhaseComparison DD rho htriv
      ((V × V) × (Fin h → V × V))
      (wPhCompactWallHandlePhase q0 h)) := by
  obtain ⟨e, he⟩ :=
    exists_compactWallHandle_firstLinear_translation hq hns ell h
  exact ⟨{
    phaseEquiv := C0.phaseEquiv.trans e
    phase_eq := fun x ↦ by rw [C0.phase_eq, he]; rfl }⟩

/-- A trivially acting factor-set charge can be removed with all handle planes fixed. -/
theorem SourceWordPhaseComparison.remove_factorSetCharge_handles
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [DistribMulAction Gamma (ZMod 2)]
    {htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a}
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    [Fintype V] {q0 : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (hq : IsQuadraticFp2 q0) (hns : Nonsingular q0)
    (g : C) (hg : ∀ v : V, g • v = v) (h : ℕ)
    (C0 : SourceWordPhaseComparison DD rho htriv
      ((V × V) × (Fin h → V × V))
      (fun p ↦ wPhCompactWallHandlePhase q0 h p + dat.m g p.1.1)) :
    Nonempty (SourceWordPhaseComparison DD rho htriv
      ((V × V) × (Fin h → V × V))
      (wPhCompactWallHandlePhase q0 h)) := by
  simpa only [factorSetChargeHomOfTrivial_apply] using
    SourceWordPhaseComparison.remove_compactWallHandle_firstLinear hq hns
      (factorSetChargeHomOfTrivial dat hdat g hg) h C0

#print axioms exists_compactWallHandle_firstLinear_translation
#print axioms SourceWordPhaseComparison.remove_compactWallHandle_firstLinear
#print axioms SourceWordPhaseComparison.remove_factorSetCharge_handles

end Shift

section Comparison

/-- Once the display value supplies a fixed-point-free scaled pivot row, the arbitrary-display
unramified lane reaches the common compact wall-handle source comparison.  The Hessian charge
is removed by translating only the second head coordinate. -/
theorem exists_comparison_unramified_of_headPhase_handles
    {alpha r pp h qrel : ℕ} {eta : EtaDisplay}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) DD.Vmod]
    [DistribMulAction
      ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (ZMod 2)]
    [ContinuousSMul
      ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type) (ZMod 2)]
    (htriv : ∀
      (x : ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type))
      (a : ZMod 2), x • a = a)
    (hcompat : ∀
      (x : ((displayedGamma alpha r pp h qrel eta : ProfiniteGrp) : Type))
      (v : DD.Vmod), x • v = rho0 DD rho x • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp eta h) i)))
    (halpha : 1 ≤ alpha) (hqrel : Even qrel)
    (hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod),
      rho0 DD rho
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp eta h) (.wild i)) • v = v)
    (htauAct : ∀ v : DD.Vmod,
      rho0 DD rho
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp eta h) .tau) • v = v)
    (hsigmaFpf : ∀ v : DD.Vmod,
      rho0 DD rho
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp eta h) .sigma) • v = v → v = 0)
    (u : DD.C0)
    (hrow :
      let t : Marking (2 + 2 * h) DD.C0 :=
        ⟨fun i ↦ Count.rho0Continuous DD rho
          (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp eta h) i)⟩
      ∀ x : Generator (2 + 2 * h) → DD.Vmod,
        heisD1 ⇑t
            (resolvedFamily alpha r pp h qrel eta (4 * Monoid.exponent DD.C0)) x =
          ![t.σ⁻¹ • x .tau,
            x .tau + (x (coreLetter h 2) - u⁻¹ • x (coreLetter h 2))])
    (huFpf : ∀ v : DD.Vmod, u • v = v → v = 0)
    (g : DD.C0) (hg : ∀ v : DD.Vmod, g • v = v)
    (hquad : IsQuadraticFp2 DD.qbar) (hns : Nonsingular DD.qbar)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (c : VCocycle DD rho),
      (fun i ↦ c.c
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp eta h) i)) =
          wPmCompactPhaseNormal h p →
      QZero DD rho c = wPhCompactWallHandlePhase DD.qbar h p +
        DD.dat.m g p.1.1) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
      inferInstance
    Nonempty (SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h)) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod)) :=
    inferInstance
  let theta := Count.rho0Continuous DD rho
  let t : Marking (2 + 2 * h) DD.C0 :=
    ⟨fun i ↦ theta (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp eta h) i)⟩
  have hres : ResolvesAt
      (gammaFam (2 + 2 * h) qrel (mpcW alpha r pp eta h))
      (resolvedFamily alpha r pp h qrel eta (4 * Monoid.exponent DD.C0))
      (WordLift DD.Vmod DD.C0) :=
    resolvedFamily_resolves_wordLift_handles hA2 halpha hqrel
  let C0 : SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (fun p ↦ wPhCompactWallHandlePhase DD.qbar h p + DD.dat.m g p.1.1) :=
    wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
      (wPmCompactPhaseNormal h)
      (compactNormal_closed_of_unramified_smul_row t _ u hrow)
      (compactNormalForm_of_unramified_smul_row t _ u hrow hwildAct
        htauAct hsigmaFpf huFpf)
      htriv _ hphase
  exact SourceWordPhaseComparison.remove_factorSetCharge_handles
    DD.dat DD.hdat hquad hns g hg h C0

#print axioms exists_comparison_unramified_of_headPhase_handles

end Comparison

end

end GQ2.Dyadic.Instances.MpcUnramifiedHandleComparison
