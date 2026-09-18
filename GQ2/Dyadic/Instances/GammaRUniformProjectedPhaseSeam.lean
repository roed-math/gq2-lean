/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRUniformWordPhaseSeam

/-!
# The graph trace after an actual head projection

For any uniformly Stokes even-alphabet source, a tame-normal cocycle and a factor-set head
projection reduce QZero to the branch-word Hessian on a Hessian marking. Only actual projected
wild base identities are used; trivial action is not substituted for these identities.
-/

namespace GQ2.Dyadic.UniformStokesSupply
noncomputable section
open GQ2 GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhaseSeam

variable {h q : ℕ} {R : PWord (Generator (2 + 2 * h))}
  {wOf : ℕ → Fin 2 → FreeGroup (Generator (2 + 2 * h))}
  {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : DistribMulAction ((GammaR (2 + 2 * h) q R) : Type) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((GammaR (2 + 2 * h) q R) : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The generic projected normal-graph seam, keeping the original graph resolver level. -/
theorem QZero_eq_pinned_projectedHessian_of_tameNormal
    (S : UniformStokesSupply (2 + 2 * h) q R wOf)
    (hspec : TameSpec.TameSpecializes (2 + 2 * h) q R) (hq : Even q)
    (rho : ContinuousMonoidHom ((GammaR (2 + 2 * h) q R) : Type) (Bg ⧸ D.M))
    {Cbar : Type} [Group Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (pi : DD.C0 →* Cbar)
    (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = pi cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hm : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (pi cc) v)
    (c : VCocycle DD rho)
    (hwild : ∀ i : Fin (2 + 2 * h + 1),
      pi (rho0 DD rho (gammaGen (2 + 2 * h) q R (.wild i))) = 1)
    (hcsigma : c.c (gammaGen (2 + 2 * h) q R .sigma) = 0)
    (hctau : c.c (gammaGen (2 + 2 * h) q R .tau) = 0) :
    QZero DD rho c =
      hessRelZ (Certificates.hessMark
        (pi (rho0 DD rho (gammaGen (2 + 2 * h) q R .sigma)))
        (pi (rho0 DD rho (gammaGen (2 + 2 * h) q R .tau)))
        (fun i ↦ c.c (gammaGen (2 + 2 * h) q R (.wild i))))
        (kappa0Cocycle base hbase)
        (omegaPinnedLevelZhatResolver (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)))
        (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod))) R := by
  let E := omegaPinnedLevelZhatResolver (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod))
  let E₂ := omegaPinnedLevelZtwoResolver (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod))
  let phi := semiProdProjHom (V := DD.Vmod) pi hpi
  let s := pi (rho0 DD rho (gammaGen (2 + 2 * h) q R .sigma))
  let u := pi (rho0 DD rho (gammaGen (2 + 2 * h) q R .tau))
  let v := fun i ↦ c.c (gammaGen (2 + 2 * h) q R (.wild i))
  have hmark : (fun i ↦ phi (graphSemiProdHom c (gammaGen (2 + 2 * h) q R i))) =
      Certificates.hessMark s u v := by
    funext i
    cases i with
    | sigma => exact Prod.ext hcsigma rfl
    | tau => exact Prod.ext hctau rfl
    | wild i => exact Prod.ext rfl (hwild i)
  rw [QZero_eq_pinned_graphHessianTrace S hspec hq rho DD.hdat c,
    kappa0Cocycle_comap_semiProdProjHom base hbase DD.dat DD.hdat pi hpi hf hm]
  change hessRelZ _ _ E E₂ _ + hessRelZ _ _ E E₂ _ = _
  rw [← hessRelZ_comap (kappa0Cocycle base hbase) E E₂
      (fun i ↦ graphSemiProdHom c (gammaGen (2 + 2 * h) q R i)) phi
      (Certificates.tameRelW (2 + 2 * h) q),
    ← hessRelZ_comap (kappa0Cocycle base hbase) E E₂
      (fun i ↦ graphSemiProdHom c (gammaGen (2 + 2 * h) q R i)) phi R,
    hmark, wPs_hessRelZ_tameRelW_hessMark_eq_zero base hbase s u v E E₂, zero_add]

#print axioms QZero_eq_pinned_projectedHessian_of_tameNormal

end
end GQ2.Dyadic.UniformStokesSupply
