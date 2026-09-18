/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSplicePhase
import GQ2.Dyadic.Instances.GammaRUniformProjectedPhaseSeam

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairProjectedPhase
noncomputable section

open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix GQ2.FoxH
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Certificates GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhase GQ2.Dyadic.Instances.WordPhaseModel
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSplicePhase

variable {alpha h q : ℕ} (halpha : 1 ≤ alpha) (halpha2 : 2 ≤ alpha)
  (hq0 : q ≠ 0) (hqe : Even q) (j : Fin h)
  (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)

local notation "W" => headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : DistribMulAction ((GammaR (2 + 2 * h) q W) : Type) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((GammaR (2 + 2 * h) q W) : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

include halpha2

/-- The actual normalized pair-splice source has the compact wall-handle phase after
an unramified head projection, at arbitrary handle rank and finite graph level. -/
theorem QZero_headHandlePairSplice_unramified_compactPhase
    (rho : ContinuousMonoidHom ((GammaR (2 + 2 * h) q W) : Type) (Bg ⧸ D.M))
    {Cbar : Type} [Group Cbar] [Finite Cbar] [TopologicalSpace Cbar]
    [DiscreteTopology Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (hphi : Function.Surjective (semiProdProjHom (V := DD.Vmod) pi hpi))
    (c : VCocycle DD rho)
    (htau : pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .tau)) = 1)
    (hwild : ∀ i : Fin (2 + 2 * h + 1),
      pi (rho0 DD rho (gammaGen (2 + 2 * h) q W (.wild i))) = 1)
    (hsigma2 : powOmega2 (pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .sigma))) = 1)
    (z : (DD.Vmod × DD.Vmod) × (Fin h → DD.Vmod × DD.Vmod))
    (hc : (fun i ↦ c.c (gammaGen (2 + 2 * h) q W i)) = wPmCompactPhaseNormal h z) :
    QZero DD rho c = wPhCompactWallHandlePhase DD.qbar h z := by
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let E := omegaPinnedLevelZhatResolver (4 * Monoid.exponent L)
  let E₂ := omegaPinnedLevelZtwoResolver (4 * Monoid.exponent L)
  let s := pi (rho0 DD rho (gammaGen (2 + 2 * h) q W .sigma))
  let phi : L →* Cbar :=
    (sdSnd : SemiProd Cbar DD.Vmod →* Cbar).comp (semiProdProjHom (V := DD.Vmod) pi hpi)
  have hsurj : Function.Surjective phi := by
    intro a
    obtain ⟨g, hg⟩ := hphi ((0, a) : SemiProd Cbar DD.Vmod)
    exact ⟨g, congrArg Prod.snd hg⟩
  have hN := (fourMulExponent_ne_zero_and_even L).1
  have hord (a : Cbar) : orderOf a ∣ 4 * Monoid.exponent L :=
    ((Monoid.order_dvd_exponent a).trans (MonoidHom.exponent_dvd hsurj)).trans ⟨4, by ring⟩
  have hSk (a : ℤ_[2]) : s ^ E (padicOmega2 a) = 1 :=
    zpow_resolved_padicOmega2_eq_one s E hsigma2
      (fun b ↦ omegaPinnedLevelZhatResolver_spec hN hord (padicOmega2 b) s) a
  have hcsigma : c.c (gammaGen (2 + 2 * h) q W .sigma) = 0 :=
    (congrFun hc .sigma).trans (wPmCompactPhaseNormal_sigma h z)
  have hctau : c.c (gammaGen (2 + 2 * h) q W .tau) = 0 :=
    (congrFun hc .tau).trans (wPmCompactPhaseNormal_tau h z)
  have hwildc : (fun i ↦ c.c (gammaGen (2 + 2 * h) q W (.wild i))) =
      (fun i ↦ wPmCompactPhaseNormal h z (.wild i)) := funext fun i ↦ congrFun hc (.wild i)
  rw [UniformStokesSupply.QZero_eq_pinned_projectedHessian_of_tameNormal
      (uniformStokesSupply_headHandlePairSplice halpha halpha2 hq0 hqe j nuP)
      (headHandlePairSpliceW_specializes halpha hq0 hqe j nuP)
      hqe rho base hbase pi hpi hf hm c hwild hcsigma hctau, htau, hwildc]
  exact hessRelZ_headHandlePairSplice_normal base hbase (Vmod_exp2 DD)
    halpha halpha2 hq0 hqe j nuP s z E E₂
    (omegaPinnedLevelZhatResolver_omega2 _) (omega2Exp_fourMulExponent_mod_four L) hSk

#print axioms QZero_headHandlePairSplice_unramified_compactPhase

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairProjectedPhase
