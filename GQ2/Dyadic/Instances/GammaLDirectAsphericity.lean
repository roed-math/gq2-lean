/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleAsphericityConverse
import GQ2.Dyadic.Instances.GammaLRelatorRealization
import GQ2.Dyadic.Instances.GammaLSimpleDirectSurjectivity

/-!
# Direct finite-extension asphericity at generating L targets

The generic converse in `HTwoModuleAsphericityConverse` turns the already-proved direct
simple-coefficient comparison theorem into an actual finite-extension statement.  For every
surjective finite target of `GammaL`, every simple elementary coefficient and every requested
pair of L-relator fibre labels is realized by a finite twisted module extension of an
action-compatible quotient.

This result is noncircular: it uses neither Tate duality, an Euler characteristic, a field
realization, nor a cohomological-dimension premise.  Surjectivity of the finite target remains
essential.  The existing direct simple proof uses it to ensure that simplicity is still visible
to the source action; an arbitrary map to an unnecessarily large finite group has no such
property.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

private theorem continuousSMul_comp_directAsphericity
    {G C A : Type} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A]
    (rho : ContinuousMonoidHom G C) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A ↦ p.1 • p.2) =
      (fun p : C × A ↦ p.1 • p.2) ∘ (fun p : G × A ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

section FixedCoefficient

variable {h q e : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wL" => lSqFam h q e

/-- For the improved L presentation, finite relator realization and finite-extension
asphericity are equivalent. -/
theorem lModuleFiniteExtensionAsphericity_iff_relatorRealization
    (rho : ContinuousMonoidHom GammaL C)
    (hres : ResolvesAt WL wL (WordLift A C)) :
    LModuleFiniteExtensionAsphericity (A := A) rho ↔
      LModuleRelatorRealization (A := A) (e := e) rho := by
  exact moduleFiniteExtensionAsphericity_iff_relatorRealization
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))
    rho (fun i ↦ rho (genL i)) wL (lFlexibleResolverSystem rho hres)

/-- Surjectivity of the canonical L comparison constructs finite extensions realizing every
relator fibre vector. -/
theorem lModuleFiniteExtensionAsphericity_of_h2Surjective
    (rho : ContinuousMonoidHom GammaL C)
    (hcompat : ∀ (g : GammaL) (a : A), g • a = rho g • a)
    (hA₂ : ∀ a : A, a + a = 0)
    (hres : ResolvesAt WL wL (WordLift A C))
    (hsurj : Function.Surjective
      (lModuleH2WordFlexible rho hcompat hA₂ hres)) :
    LModuleFiniteExtensionAsphericity (A := A) rho := by
  apply (lModuleFiniteExtensionAsphericity_iff_relatorRealization rho hres).2
  exact moduleRelatorRealization_of_surjective
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h))
    rho hcompat (fun U ↦ hwildLevel_gammaR U) hA₂
    (lFlexibleResolverSystem rho hres) hsurj

end FixedCoefficient

section DirectSimple

variable {h q : ℕ} {C V : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [DiscreteTopology V] [Finite V]
  [DistribMulAction ((gamma h q : Type)) V]
  [ContinuousSMul ((gamma h q : Type)) V]
  [DistribMulAction C V]

local notation "GammaL" => (gamma h q : Type)

/-- The direct simple dichotomy at a generating target, upgraded from map surjectivity to a
finite-extension realization theorem. -/
theorem lUniform_simpleFiniteExtensionAsphericity_of_surjective
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hcompat : ∀ (g : GammaL) (v : V), g • v = rho g • v)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (hq : Even q) :
    LModuleFiniteExtensionAsphericity (A := V) rho := by
  apply lModuleFiniteExtensionAsphericity_of_h2Surjective rho hcompat hV₂
    (lUniform_wordLift_resolver hV₂)
  exact lUniform_simpleH2WordFlexible_surjective_of_surjective
    rho hrho hcompat hV₂ hsimple hq

/-- Provider form: every simple elementary coefficient at a surjective finite target has the
finite-extension asphericity property, without Tate or CD-2 input. -/
theorem uniformSimpleExtensionAsphericitySingleProvider_of_surjective
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hq : Even q) : UniformSimpleExtensionAsphericitySingleProvider rho := by
  intro A _ _ _ hA₂ hsimple
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalAddGroup A := by infer_instance
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_directAsphericity rho (fun _ _ ↦ rfl)
  exact lUniform_simpleFiniteExtensionAsphericity_of_surjective
    rho hrho (fun _ _ ↦ rfl) hA₂ hsimple hq

end DirectSimple

end

end GQ2.Dyadic.LSquare
