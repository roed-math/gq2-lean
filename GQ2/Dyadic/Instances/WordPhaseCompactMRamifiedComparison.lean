/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedData

/-!
# Ramified compact-M source/word comparison

This file assembles the handle-free ramified compact-M Fox normal form and the honest
projected-head Hessian calculation into a source/word phase comparison.  The natural endpoint
coordinates are block-swapped; the exported comparison composes with `Equiv.prodComm` to use
the common compact endpoint `plusFormD qbar qbar`.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedComparison

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.WordPhaseSeam
open GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedData
open GQ2.Dyadic.LSquare

private def wPcMRamified_marking
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] :
    Marking 2 DD.C0 :=
  ⟨fun i ↦ Count.rho0Continuous DD rho
    (gammaGen 2 q (MCompact.mCompactW alpha 0) i)⟩

private theorem wPcMRamified_resolves
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    (hA2 : ∀ v : DD.Vmod, v + v = 0) :
    ResolvesAt (gammaFam 2 q (MCompact.mCompactW alpha 0))
      (MCompact.mCompactFam alpha 0 q
        (omega2Exp (4 * Monoid.exponent DD.C0))) (WordLift DD.Vmod DD.C0) := by
  have hbaseOrd : ∀ g : DD.C0, orderOf g ∣ Monoid.exponent DD.C0 :=
    fun g ↦ Monoid.order_dvd_exponent g
  have horder : ∀ p : WordLift DD.Vmod DD.C0,
      orderOf p ∣ 4 * Monoid.exponent DD.C0 := fun p ↦
    (WordLift.orderOf_dvd_two_mul hA2 hbaseOrd p).trans ⟨2, by ring⟩
  exact Count.resolvesAt_mCompactFam
    (Count.fourMulExponent_ne_zero_and_even DD.C0).1 horder alpha 0 q

private theorem wPcMRamified_tameRel
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] :
    (wPcMRamified_marking (DD := DD) rho).TameRelAt q := by
  let theta := Count.rho0Continuous DD rho
  let t := wPcMRamified_marking (DD := DD) rho
  have hrel := (isAdmissibleMarkedPresentation_gammaR
    2 q (MCompact.mCompactW alpha 0)).rel theta (0 : Fin 2)
  change PWord.eval ⇑t (tameRelW 2 q) = 1 at hrel
  rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
  exact mul_inv_eq_one.mp hrel

private def wPcMRamified_row
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildAct : ∀ (i : Fin 3) (v : DD.Vmod), rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i)) • v = v)
    (htauFpf : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v = v) :=
  @heisD1_mCompactFam_ramified_apply 0 alpha q DD.C0 DD.Vmod
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (wPcMRamified_marking (DD := DD) rho) hA2
    (wPcMRamified_tameRel (DD := DD) rho) hwildAct htauFpf hTodd

private theorem wPcMRamified_lowerRel
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    (hres : ResolvesAt (gammaFam 2 q (MCompact.mCompactW alpha 0))
      (MCompact.mCompactFam alpha 0 q
        (omega2Exp (4 * Monoid.exponent DD.C0))) (WordLift DD.Vmod DD.C0)) :
    ∀ k, FreeGroup.lift ⇑(wPcMRamified_marking (DD := DD) rho)
      (MCompact.mCompactFam alpha 0 q
      (omega2Exp (4 * Monoid.exponent DD.C0)) k) = 1 := by
  let theta := Count.rho0Continuous DD rho
  intro k
  exact Count.lower_rel (A := DD.Vmod) theta (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR 2 q (MCompact.mCompactW alpha 0)) hres k

private noncomputable def wPcMRamified_assemble
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) DD.Vmod]
    [DistribMulAction
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2)]
    [ContinuousSMul
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2)]
    (htriv : ∀
      (g : ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type))
      (a : ZMod 2), g • a = a)
    (hcompat : ∀
      (g : ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet 2)
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen 2 q (MCompact.mCompactW alpha 0) i)))
    (hres : ResolvesAt (gammaFam 2 q (MCompact.mCompactW alpha 0))
      (MCompact.mCompactFam alpha 0 q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift DD.Vmod DD.C0))
    (hrow : ∀ x : Generator 2 → DD.Vmod,
      heisD1 ⇑(wPcMRamified_marking (DD := DD) rho)
        (MCompact.mCompactFam alpha 0 q (omega2Exp (4 * Monoid.exponent DD.C0))) x =
        ![(wPcMRamified_marking (DD := DD) rho).σ⁻¹ •
            (x .tau + (wPcMRamified_marking (DD := DD) rho).τ • x .sigma - x .sigma)
            - ∑ i ∈ Finset.range q,
              ((wPcMRamified_marking (DD := DD) rho).τ ^ i) • x .tau,
          -((wPcMRamified_marking (DD := DD) rho).σ⁻¹ • x (coreLetter 0 2))])
    (hwildAct : ∀ (i : Fin 3) (v : DD.Vmod),
      (wPcMRamified_marking (DD := DD) rho).x i • v = v)
    (htauFpf : ∀ v : DD.Vmod,
      (wPcMRamified_marking (DD := DD) rho).τ • v = v → v = 0)
    (hr : ∀ k, FreeGroup.lift ⇑(wPcMRamified_marking (DD := DD) rho)
      (MCompact.mCompactFam alpha 0 q (omega2Exp (4 * Monoid.exponent DD.C0)) k) = 1)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) (c : VCocycle DD rho),
      (fun i ↦ c.c (gammaGen 2 q (MCompact.mCompactW alpha 0) i))
        = wPmCompactPhaseNormal 0 p →
      QZero DD rho c = wPcMRamifiedPhase DD.qbar p) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
      (wPcMRamifiedPhase DD.qbar) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) :=
    inferInstance
  exact wPmPhaseComparison_of_normalForm rho hcompat hres hA2 hwildTwo
    (wPmCompactPhaseNormal 0)
    (wPcMRamifiedNormal_closed (wPcMRamified_marking (DD := DD) rho)
      (MCompact.mCompactFam alpha 0 q (omega2Exp (4 * Monoid.exponent DD.C0))) hrow)
    (wPcMRamifiedNormal_form (wPcMRamified_marking (DD := DD) rho)
      (MCompact.mCompactFam alpha 0 q (omega2Exp (4 * Monoid.exponent DD.C0))) hrow
      hwildAct htauFpf hr)
    htriv (wPcMRamifiedPhase DD.qbar) hphase

/-- The natural handle-free ramified comparison, retaining the block-swapped endpoint
coordinates produced by the compact-M word. -/
noncomputable def wPcMComparison_ramifiedNatural
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) DD.Vmod]
    [DistribMulAction
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2)]
    [ContinuousSMul
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2)]
    (htriv : ∀
      (g : ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type))
      (a : ZMod 2), g • a = a)
    (hcompat : ∀
      (g : ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet 2)
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen 2 q (MCompact.mCompactW alpha 0) i)))
    (hwildAct : ∀ (i : Fin 3) (v : DD.Vmod), rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i)) • v = v)
    (htauFpf : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v = v)
    (hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) (c : VCocycle DD rho),
      (fun i ↦ c.c (gammaGen 2 q (MCompact.mCompactW alpha 0) i))
        = wPmCompactPhaseNormal 0 p →
      QZero DD rho c = wPcMRamifiedPhase DD.qbar p) :
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) :=
      inferInstance
    SourceWordPhaseComparison DD rho htriv
      ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod))
      (wPcMRamifiedPhase DD.qbar) := by
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) :=
    inferInstance
  let e := omega2Exp (4 * Monoid.exponent DD.C0)
  let theta := Count.rho0Continuous DD rho
  let t := wPcMRamified_marking (DD := DD) rho
  have hres : ResolvesAt (gammaFam 2 q (MCompact.mCompactW alpha 0))
      (MCompact.mCompactFam alpha 0 q e) (WordLift DD.Vmod DD.C0) := by
    simpa only [e] using wPcMRamified_resolves (DD := DD) hA2
  have hwildAct' : ∀ (i : Fin 3) (v : DD.Vmod), t.x i • v = v := hwildAct
  have htauFpf' : ∀ v : DD.Vmod, t.τ • v = v → v = 0 := htauFpf
  let hrow := wPcMRamified_row (DD := DD) rho hA2 hwildAct htauFpf hTodd
  have hr : ∀ k, FreeGroup.lift ⇑t (MCompact.mCompactFam alpha 0 q e k) = 1 := by
    simpa only [t, e] using wPcMRamified_lowerRel (DD := DD) rho hres
  exact wPcMRamified_assemble rho htriv hcompat hA2 hwildTwo hres hrow
    hwildAct' htauFpf' hr hphase

/-- The honest ramified projected-head comparison in the common compact-M endpoint
coordinates.  Projected oddness and fixed-point-freeness feed the Hessian calculation;
`hTodd` is the separate source-action hypothesis required by the Fox row. -/
noncomputable def wPcMComparison_ramifiedHead
    {alpha q : Nat}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hcompat : ∀
      (g : ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type))
      (v : DD.Vmod), g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet 2)
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen 2 q (MCompact.mCompactW alpha 0) i)))
    (hq0 : q ≠ 0) (hqe : Even q) (halpha : 2 ≤ alpha)
    (hwildHead : ∀ i : Fin 3, pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v = v → v = 0)
    (hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau)) • v = v) :
    letI := scalarActionZmodTwo
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
    SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      (DD.Vmod × DD.Vmod) (plusFormD DD.qbar DD.qbar) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((GammaR 2 q (MCompact.mCompactW alpha 0) : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  letI : Fintype ((DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) :=
    inferInstance
  letI : Fintype (DD.Vmod × DD.Vmod) := inferInstance
  have hwildAct : ∀ (i : Fin 3) (v : DD.Vmod), rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) (.wild i)) • v = v := by
    intro i v
    rw [hpi, hwildHead i, one_smul]
  have htauFpf : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen 2 q (MCompact.mCompactW alpha 0) .tau) • v = v → v = 0 := by
    intro v hv
    apply htauHeadFpf v
    rw [← hpi]
    exact hv
  have hphase : ∀
      (p : (DD.Vmod × DD.Vmod) × (Fin 0 → DD.Vmod × DD.Vmod)) (c : VCocycle DD rho),
      (fun i ↦ c.c (gammaGen 2 q (MCompact.mCompactW alpha 0) i))
        = wPmCompactPhaseNormal 0 p →
      QZero DD rho c = wPcMRamifiedPhase DD.qbar p :=
    fun p c hc ↦ wPcM_QZero_eq_ramifiedPhase_of_surjectiveHeadMark rho base hbase
      pi hpi hf hm hphi hqe hq0 halpha c hwildHead htauHeadOdd htauHeadFpf p hc
  let C := wPcMComparison_ramifiedNatural rho (scalarActionZmodTwo_triv _) hcompat hA2
    hwildTwo hwildAct htauFpf hTodd hphase
  refine {
    phaseEquiv := C.phaseEquiv.trans
      ((Equiv.prodUnique (DD.Vmod × DD.Vmod) (Fin 0 → DD.Vmod × DD.Vmod)).trans
        (Equiv.prodComm DD.Vmod DD.Vmod))
    phase_eq := fun x ↦ ?_ }
  rw [C.phase_eq]
  simp [wPcMRamifiedPhase, plusFormD, polar_comm]

/-! ## Axiom audit -/

#print axioms wPcMComparison_ramifiedNatural
#print axioms wPcMComparison_ramifiedHead

end

end GQ2.Dyadic.Instances.WordPhaseCompactMRamifiedComparison
