/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcUnramifiedProjectedComparison

/-!
# Projected ramified procyclic-M comparison

The genuine display-dependent graph resolver descends through the projected central extension.
Every display value acts as an integer power of sigma, so the arbitrary-h ramified Hessian and
source comparison reach the common compact wall-handle phase without an exposed display or
resolver premise.
-/

namespace GQ2.Dyadic.Instances.MpcRamifiedProjectedComparison

noncomputable section

open GQ2 GQ2.SectionSix GQ2.FoxH GQ2.QuadraticFp2
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Certificates.MpcJet
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Instances.MpcHandlePhaseData
open GQ2.Dyadic.Instances.MpcWordPhaseSeam
open GQ2.Dyadic.Instances.MpcUnramifiedProjectedData
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseModel

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-- The projected ramified graph trace is the common compact wall-handle phase. -/
theorem wPmpc_QZero_eq_ramifiedCompactPhase_of_projectedHeadMark
    {alpha r pp h qrel : ℕ} {d : EtaDisplay}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [TopologicalSpace Cbar]
    [DiscreteTopology Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (halpha : 2 ≤ alpha) (hqrel : Even qrel)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau)) • v = v → v = 0)
    (p : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)) =
        wPmCompactPhaseNormal h p) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = wPhCompactWallHandlePhase DD.qbar h p := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let graph := fun i ↦ graphSemiProdHom c
    (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)
  obtain ⟨E, E2, hresSource, hresolved⟩ :=
    wPmpc_exists_graphResolver
      (alpha := alpha) (r := r) (pp := pp) (h := h) (q := qrel)
      d DD.dat DD.hdat (Vmod_exp2 DD) graph
  let phi := semiProdProjHom (V := DD.Vmod) pi hpi
  have hcoc : (kappa0Cocycle base hbase).comap phi =
      kappa0Cocycle DD.dat DD.hdat :=
    (kappa0Cocycle_comap_semiProdProjHom
      base hbase DD.dat DD.hdat pi hpi hf hm).symm
  have hresComap : ResolverLifts E
      (WordCoh.CentExt ((kappa0Cocycle base hbase).comap phi)) := by
    rw [hcoc]
    exact hresSource
  have hresTarget : ResolverLifts E
      (WordCoh.CentExt (kappa0Cocycle base hbase)) :=
    resolverLifts_comap_target_of_surjective
      (kappa0Cocycle base hbase) phi hphi E hresComap
  have hcval : ∀ i, c.c
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i) =
        wPmCompactPhaseNormal h p i := fun i ↦ congrFun hc i
  let s := pi (rho0 DD rho
    (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .sigma))
  let u := pi (rho0 DD rho
    (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau))
  have hmark :
      (fun i ↦ phi (graphSemiProdHom c
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i))) =
        Certificates.hessMark (h := h) s u
          (fun i : Fin (2 + 2 * h + 1) ↦
            wPmCompactPhaseNormal h p (Generator.wild i)) := by
    funext i
    cases i with
    | sigma => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_sigma h p)) rfl
    | tau => exact Prod.ext ((hcval _).trans (wPmCompactPhaseNormal_tau h p)) rfl
    | wild i => exact Prod.ext (hcval _) (hwildHead i)
  have huOdd : Odd (orderOf u) := htauHeadOdd
  have huFpf : ∀ v : DD.Vmod, u • v = v → v = 0 := htauHeadFpf
  obtain ⟨neta, hetaEq⟩ :=
    MProcyclic.exists_zpow_evalFin_etaDisplay
      (lowerMark (h := h) s u) E E2 d
  have heta : ActsAsPow (lowerMark (h := h) s u).σ neta
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E2
        (d.toPWord (n := 2 + 2 * h))) DD.Vmod := by
    intro v
    rw [hetaEq]
  rw [wPmpc_QZero_eq_graphHessianTrace rho DD.hdat (by omega) hqrel
      hcardH2 c E E2 hresolved,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  rw [← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)) phi
      (tameRelW (2 + 2 * h) qrel),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E2
      (fun i ↦ graphSemiProdHom c
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)) phi
      (mpcW alpha r pp d h),
    hmark,
    GQ2.Dyadic.Instances.WordPhaseSeam.wPs_hessRelZ_tameRelW_hessMark_eq_zero
      base hbase s u _ E E2,
    zero_add,
    hessRelZ_mpcW_ramified_compactPhase base hbase (Vmod_exp2 DD)
      (by omega) s u huOdd huFpf p E E2 heta hresTarget]

/-- An honest ramified projected head supplies the common compact wall-handle comparison. -/
theorem exists_comparison_ramified_of_projectedHead_handles
    {alpha r pp h qrel : ℕ} {d : EtaDisplay}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) DD.Vmod]
    [ContinuousSMul
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [TopologicalSpace Cbar]
    [DiscreteTopology Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hcompat : ∀
      (x : ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type))
      (v : DD.Vmod), x • v = rho0 DD rho x • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) i)))
    (halpha : 2 ≤ alpha) (hqrel : Even qrel)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (hwildHead : ∀ i : Fin (2 + 2 * h + 1), pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) (.wild i))) = 1)
    (htauHeadOdd : Odd (orderOf (pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau)))))
    (htauHeadFpf : ∀ v : DD.Vmod, pi (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau)) • v = v → v = 0) :
    letI := scalarActionZmodTwo
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    Nonempty (SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h)) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r pp h qrel d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  have hwildAct : ∀ (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod),
      rho0 DD rho
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) (.wild i)) • v = v := by
    intro i v
    rw [hpi, hwildHead i, one_smul]
  have htauFpf : ∀ v : DD.Vmod,
      rho0 DD rho
        (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau) • v = v → v = 0 := by
    intro v hv
    apply htauHeadFpf v
    rw [← hpi]
    exact hv
  have hTodd : ∀ v : DD.Vmod, powOmega2 (rho0 DD rho
      (gammaGen (2 + 2 * h) qrel (mpcW alpha r pp d h) .tau)) • v = v := by
    intro v
    rw [hpi, powOmega2_map pi, powOmega2_eq_one_of_odd htauHeadOdd, one_smul]
  refine ⟨comparison_ramified_of_headPhase_handles rho
    (scalarActionZmodTwo_triv _) hcompat hA2 hwildTwo (by omega) hqrel
    hwildAct htauFpf hTodd ?_⟩
  intro p c hc
  exact wPmpc_QZero_eq_ramifiedCompactPhase_of_projectedHeadMark
    rho base hbase pi hpi hf hm hphi halpha hqrel hcardH2
      c hwildHead htauHeadOdd htauHeadFpf p hc

#print axioms wPmpc_QZero_eq_ramifiedCompactPhase_of_projectedHeadMark
#print axioms exists_comparison_ramified_of_projectedHead_handles

end
end GQ2.Dyadic.Instances.MpcRamifiedProjectedComparison
