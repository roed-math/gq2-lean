/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationModuleGlobal
import GQ2.Dyadic.Instances.GammaLAsphericityRightExact
import GQ2.Dyadic.Instances.GammaLRelationModuleResolver

/-!
# The relation-module route to H² right exactness and Tate duality for L

This file composes three independently proved bridges:

1. relation characters transgress to finite module cocycles;
2. the improved L word resolves both split and twisted module extensions uniformly;
3. a cocycle on a finite action target pulls back to the quotient by the target map's kernel.

The only remaining input is consequently the classical relation-module evaluation theorem:
arbitrary values on the two improved L relators extend to an equivariant character of the free
relation kernel.  Quantifying that statement over all elementary coefficients gives the exact
continuous H² right-exactness supply, and hence the already-assembled Tate-duality theorem.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

section FixedTarget

variable {h q : ℕ} {C A : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction ((gamma h q : Type)) A]
  [ContinuousSMul ((gamma h q : Type)) A]
  [DistribMulAction C A]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (Words.LSq.lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (Words.LSq.lSqW h)
local notation "wC" => lSqFam h q (omega2Exp (4 * Monoid.exponent C))

omit [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction GammaL A] [ContinuousSMul GammaL A] in
/-- Relation-module evaluation at a surjective finite L target supplies the global finite-level
realization predicate used by the canonical continuous-to-word H² comparison. -/
theorem lModuleRelatorRealization_of_relationModule
    (rho : ContinuousMonoidHom GammaL C) (hrho : Function.Surjective rho)
    (hA₂ : ∀ a : A, a + a = 0)
    (hRM : RelationModuleRelatorSurjective (A := A) wC
      (lUniform_rel_death rho)) :
    LModuleRelatorRealization (A := A)
      (e := omega2Exp (4 * Monoid.exponent C)) rho :=
  moduleRelatorRealization_of_target rho (fun _ ↦ rfl)
    (lRelatorRealization_of_relationModule rho hrho hA₂ hRM)

end FixedTarget

section UniformSupply

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- The remaining classical presentation-theoretic statement, uniformly over finite action
targets and elementary coefficients.  Unlike the H² and extension formulations, this predicate
mentions only the free relation kernel and its equivariant additive characters. -/
noncomputable abbrev UniformElementaryRelationModuleSurjectiveSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (hA₂ : ∀ a : A, a + a = 0) →
        RelationModuleRelatorSurjective (A := A)
          (lSqFam h q (omega2Exp (4 * Monoid.exponent C)))
          (lUniform_rel_death rho)

private theorem continuousSMul_comp_relationModuleGlobal
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

/-- The uniform relation-module theorem supplies the all-elementary finite relator-realization
condition, without continuous duality or a cohomological-dimension premise. -/
theorem uniformElementaryRelatorRealizationSurjectiveSupply_of_relationModule
    (hRM : UniformElementaryRelationModuleSurjectiveSupply (h := h) (q := q)) :
    UniformElementaryRelatorRealizationSurjectiveSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho A _ _ _ hA₂
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalAddGroup A := by infer_instance
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_relationModuleGlobal rho (fun _ _ ↦ rfl)
  exact lModuleRelatorRealization_of_relationModule rho hrho hA₂
    (hRM C rho hrho A hA₂)

/-- The classical relation-module supply implies the continuous H² right-exact/CD2 tail. -/
theorem gammaLH2RightExactSupply_of_relationModule
    (hRM : UniformElementaryRelationModuleSurjectiveSupply (h := h) (q := q)) :
    GammaLH2RightExactSupply h q :=
  gammaLH2RightExactSupply_of_allElementaryRelatorRealization
    (uniformElementaryRelatorRealizationSurjectiveSupply_of_relationModule hRM)

/-- At even `q`, the classical relation-module supply gives the full Tate-duality package for
the improved L presentation. -/
noncomputable def tateDualityG_of_relationModule
    (hq : Even q)
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hRM : UniformElementaryRelationModuleSurjectiveSupply (h := h) (q := q)) :
    TateDualityG GammaL 2 :=
  tateDualityG_of_gammaLH2RightExactSupply hq
    (gammaLH2RightExactSupply_of_relationModule hRM)

end UniformSupply

end

end GQ2.Dyadic.LSquare
