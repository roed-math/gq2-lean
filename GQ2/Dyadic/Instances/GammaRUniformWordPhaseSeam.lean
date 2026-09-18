/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRUniformWordTrace
import GQ2.Dyadic.Instances.OmegaPinnedLevelResolver

/-!
# The quadratic obstruction-to-word-Hessian seam for an arbitrary source

The scalar trace orientation identifies QZero with the sum of the two evaluated graph
Hessians. This theorem makes no assumption on the syntax of the branch word. In particular,
the pinned resolver resolves every genuine profinite exponent in the full kappa0 central
extension at four times the exponent of the graph target.
-/

namespace GQ2.Dyadic.UniformStokesSupply
noncomputable section

open GQ2 GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.LSquare

/-- The pinned graph-target level resolves every word in the full extraspecial extension. -/
theorem kappa0_resolvedAt_pinned_uniform
    {C V X : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    [Finite C] [Finite V] [Finite (SectionSix.SemiProd C V)] {q0 : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v + v = 0)
    (m : X → SectionSix.SemiProd C V) (w : PWord X) :
    PWord.ResolvedAt (WordCoh.lift m (GQ2.Dyadic.kappa0Cocycle dat hdat))
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent (SectionSix.SemiProd C V)))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent (SectionSix.SemiProd C V))) w := by
  let L := SectionSix.SemiProd C V
  have hord : ∀ p : WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat),
      orderOf p ∣ 4 * Monoid.exponent L := by
    intro p
    rw [orderOf_dvd_iff_pow_eq_one]
    apply kappa0_pow_eq_one_of_snd_pow dat hdat hV2
    have hb : p.base ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one p.base
    calc
      p.base.2 ^ Monoid.exponent L = sdSnd (p.base ^ Monoid.exponent L) :=
        (map_pow (sdSnd : L →* C) p.base _).symm
      _ = 1 := by rw [hb]; exact map_one _
  exact resolvedAt_omegaPinnedLevelResolvers (fourMulExponent_ne_zero_and_even L).1 hord _ _

section Seam

variable {n q : ℕ} {R : PWord (Generator n)}
  {wOf : ℕ → Fin 2 → FreeGroup (Generator n)}
  {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
  [Finite DD.Vmod] [Finite DD.C0]

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : DistribMulAction ((GammaR n q R) : Type) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((GammaR n q R) : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The generic trace seam with explicit honest resolution in the full kappa0 extension. -/
theorem QZero_eq_graphHessianTrace_of_resolved
    (S : UniformStokesSupply n q R wOf) (hspec : TameSpec.TameSpecializes n q R)
    (hq : Even q) (rho : ContinuousMonoidHom ((GammaR n q R) : Type) (Bg ⧸ D.M))
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (c : VCocycle DD rho) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hresolved : ∀ k, PWord.ResolvedAt
      (WordCoh.lift (fun i ↦ graphSemiProdHom c (gammaGen n q R i))
        (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) E E₂ (gammaFam n q R k)) :
    QZero DD rho c =
      hessRelZ (fun i ↦ graphSemiProdHom c (gammaGen n q R i))
        (GQ2.Dyadic.kappa0Cocycle DD.dat hdat) E E₂ (Certificates.tameRelW n q) +
      hessRelZ (fun i ↦ graphSemiProdHom c (gammaGen n q R i))
        (GQ2.Dyadic.kappa0Cocycle DD.dat hdat) E E₂ R := by
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let W : Fin 2 → PWord (Generator n) := gammaFam n q R
  let gen : Generator n → ((GammaR n q R) : Type) := gammaGen n q R
  let graph : ContinuousMonoidHom ((GammaR n q R) : Type) L :=
    ⟨graphSemiProdHom c, continuous_graphSemiProdHom c⟩
  let kappa := GQ2.Dyadic.kappa0Cocycle DD.dat hdat
  let f : Z2 ((GammaR n q R) : Type) (ZMod 2) :=
    ⟨graphPullback DD.dat (fun g ↦ rho0 DD rho g) c.c,
      graphPullback_mem_Z2_of_cocycle (fun _ _ ↦ rfl) c⟩
  let orient := scalarH2TraceEquiv S hspec hq graph
  have htrace : QZero DD rho c =
      ∑ k, moduleObsFun W gen graph (fun _ _ ↦ rfl) f k := by
    rw [QZero]
    change iotaB f.1 = _
    rw [iotaB_eq_h2Equiv orient f]
    exact scalarH2TraceEquiv_mk S hspec hq graph f
  have hnorm : ∀ x y : ((GammaR n q R) : Type),
      moduleNormalize f.1 (x, y) = kappa.κ (graph x) (graph y) := by
    intro x y
    have h11 : f.1 (1, 1) = 0 := by
      change DD.dat.f (c.c 1) (rho0 DD rho 1 • c.c 1) +
        DD.dat.m (rho0 DD rho 1) (c.c 1) = 0
      rw [c.c_one, smul_zero, hdat.f_zero_left, map_one, hdat.m_one, add_zero]
    rw [moduleNormalize, h11, smul_zero, sub_zero]
    exact graphPullback_eq_dyadicKappa0_graph hdat c x y
  have hcoord : ∀ k, moduleObsFun W gen graph (fun _ _ ↦ rfl) f k =
      hessRelZ (fun i ↦ graph (gen i)) kappa E E₂ (W k) := by
    intro k
    exact moduleObsFun_eq_hessRelZ_of_normalized_pullback
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) W gen graph f kappa hnorm E E₂ k (hresolved k)
  rw [htrace, Fin.sum_univ_two, hcoord, hcoord]
  rfl

/-- The pinned trace seam has no word-syntax or unresolved exponent premise. -/
theorem QZero_eq_pinned_graphHessianTrace
    (S : UniformStokesSupply n q R wOf) (hspec : TameSpec.TameSpecializes n q R)
    (hq : Even q) (rho : ContinuousMonoidHom ((GammaR n q R) : Type) (Bg ⧸ D.M))
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (c : VCocycle DD rho) :
    QZero DD rho c =
      hessRelZ (fun i ↦ graphSemiProdHom c (gammaGen n q R i))
        (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)
        (omegaPinnedLevelZhatResolver (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)))
        (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)))
        (Certificates.tameRelW n q) +
      hessRelZ (fun i ↦ graphSemiProdHom c (gammaGen n q R i))
        (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)
        (omegaPinnedLevelZhatResolver (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod)))
        (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent (SectionSix.SemiProd DD.C0 DD.Vmod))) R := by
  apply QZero_eq_graphHessianTrace_of_resolved S hspec hq rho hdat c
  intro k
  exact kappa0_resolvedAt_pinned_uniform DD.dat hdat (Vmod_exp2 DD) _ _

end Seam

#print axioms kappa0_resolvedAt_pinned_uniform
#print axioms QZero_eq_graphHessianTrace_of_resolved
#print axioms QZero_eq_pinned_graphHessianTrace

end
end GQ2.Dyadic.UniformStokesSupply
