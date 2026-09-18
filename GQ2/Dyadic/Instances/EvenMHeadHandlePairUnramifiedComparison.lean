/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceNormal
import GQ2.Dyadic.Instances.EvenMHeadHandlePairProjectedPhase

/-! # The actual pair-splice unramified source-to-phase comparison -/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramifiedComparison
noncomputable section
open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Certificates GQ2.Dyadic.LSquare
open Instances.WordPhase Instances.WordPhaseModel
open Instances.EvenMHeadHandlePairSpliceSupply Instances.EvenMHeadHandlePairSpliceNormal
open Instances.EvenMHeadHandlePairProjectedPhase

variable {alpha h q : ℕ} (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
  (hq0 : q ≠ 0) (hqe : Even q) (j : Fin h)
  (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)

local notation "W" => headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}

/-- All unramified normal-form, phase, and resolver inputs are supplied for the actual
changed pair source. Only the genuine projected boundary hypotheses remain. -/
def headHandlePairSplice_unramifiedComparison
    (rho : ContinuousMonoidHom ((GammaR (2 + 2 * h) q W) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction ((GammaR (2 + 2 * h) q W) : Type) DD.Vmod]
    [ContinuousSMul ((GammaR (2 + 2 * h) q W) : Type) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [TopologicalSpace Cbar]
    [DiscreteTopology Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (hcompat : ∀ (g : ((GammaR (2 + 2 * h) q W) : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hwildTwo : IsWildTwo (wildAlphabet (2 + 2 * h))
      (fun i ↦ Count.rho0Continuous DD rho (gammaGen (2 + 2 * h) q W i)))
    (htau : pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .tau)) = 1)
    (hwild : ∀ i : Fin (2 + 2 * h + 1),
      pi (rho0 DD rho (gammaGen (2 + 2 * h) q W (.wild i))) = 1)
    (hsigma : ∀ v : DD.Vmod, rho0 DD rho
      (gammaGen (2 + 2 * h) q W .sigma) • v = v → v = 0)
    (hsigma2 : powOmega2 (pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .sigma))) = 1) :
    letI := scalarActionZmodTwo ((GammaR (2 + 2 * h) q W) : Type)
    letI : Fintype DD.Vmod := Fintype.ofFinite _
    SourceWordPhaseComparison DD rho (scalarActionZmodTwo_triv _)
      ((DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
      (wPhCompactWallHandlePhase DD.qbar h) := by
  letI := scalarActionZmodTwo ((GammaR (2 + 2 * h) q W) : Type)
  letI := scalarActionZmodTwo_continuousSMul ((GammaR (2 + 2 * h) q W) : Type)
  letI : Fintype DD.Vmod := Fintype.ofFinite _
  let S := uniformStokesSupply_headHandlePairSplice halpha halpha2 hq0 hqe j nuP
  let theta := Count.rho0Continuous DD rho
  let t : Marking (2 + 2 * h) DD.C0 := ⟨fun i ↦ theta (gammaGen (2 + 2 * h) q W i)⟩
  have htauAct (v : DD.Vmod) : t.τ • v=v := by
    change rho0 DD rho (gammaGen (2 + 2 * h) q W .tau) • v=v
    rw [hpi, htau, one_smul]
  have hwildAct (i : Fin (2 + 2 * h + 1)) (v : DD.Vmod) : t.x i • v=v := by
    change rho0 DD rho (gammaGen (2 + 2 * h) q W (.wild i)) • v=v
    rw [hpi, hwild, one_smul]
  have hsigmaAct (v : DD.Vmod) : powOmega2 t.σ • v=v := by
    change powOmega2 (rho0 DD rho (gammaGen (2 + 2 * h) q W .sigma)) • v=v
    rw [hpi, powOmega2_map pi, hsigma2, one_smul]
  have hres := S.resolvesWord (C := DD.C0) (Vmod_exp2 DD)
  have hr := lower_rel theta (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q W) hres
  have hnormal := headHandlePairSplice_compactNormal t halpha hq0 hqe j nuP
    (Vmod_exp2 DD) hwildAct htauAct hsigma hsigmaAct hr
  exact wPmPhaseComparison_of_normalForm rho hcompat hres (Vmod_exp2 DD) hwildTwo
    (wPmCompactPhaseNormal h) hnormal.1 hnormal.2 (scalarActionZmodTwo_triv _)
    (wPhCompactWallHandlePhase DD.qbar h)
    (fun z c hc ↦ QZero_headHandlePairSplice_unramified_compactPhase halpha halpha2
      hq0 hqe j nuP rho base hbase pi hpi hf hm hphi c htau hwild hsigma2 z hc)

#print axioms headHandlePairSplice_unramifiedComparison

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairUnramifiedComparison
