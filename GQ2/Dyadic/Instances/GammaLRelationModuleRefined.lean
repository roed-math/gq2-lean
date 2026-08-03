/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationModuleRefined
import GQ2.Dyadic.Instances.GammaLRelationModuleGlobal

/-!
# Refined relation-module realizations for the improved L presentation

Relation-module surjectivity at the finite action target is stronger than the continuous
comparison needs, and it can fail at small targets.  The exact finite realization predicate
allows passage to a deeper finite quotient `GammaL / V`, with `V` contained in the action
kernel.  At that quotient this file uses its own coefficient-independent improved L word

`lSqFam h q (omega2Exp (4 * exponent (GammaL / V)))`.

The refined word and the fixed action-target word need not be equal.  Their Fox-differential
ranges agree after base change because both resolve the same two profinite L relators.  Thus a
relation-module transgression at the deeper quotient realizes the fixed target word without
assuming a false fixed-target Fox basis.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Certificates.LSqStokes

section FixedRefinement

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
local notation "eC" => omega2Exp (4 * Monoid.exponent C)
local notation "wC" => lSqFam h q eC

local instance gammaLRefinedQuotientDiscreteTopology
    (V : OpenNormalSubgroup GammaL) : DiscreteTopology (GammaL ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

set_option maxHeartbeats 1000000 in
/-- Relation-module evaluation at an action-compatible deeper quotient realizes every relator
vector for the fixed action-target L word.  The quotient `V` is fixed in this theorem, so this
is the stronger single-refinement realization predicate `LModuleRelatorRealizationAt`. -/
theorem lModuleRelatorRealizationAt_of_refined_relationModule
    (rho : ContinuousMonoidHom GammaL C)
    (hA₂ : ∀ a : A, a + a = 0)
    (V : OpenNormalSubgroup GammaL)
    (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (hRM :
      letI : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      RelationModuleRelatorSurjective (A := A)
        (lSqFam h q
          (omega2Exp (4 * Monoid.exponent (GammaL ⧸ V.toSubgroup))))
        (lUniform_rel_death (GQ2.quotientMk V.toSubgroup))) :
    LModuleRelatorRealizationAt (A := A) (e := eC) rho V hV := by
  let rhoV : (GammaL ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  let wV : Fin 2 → FreeGroup (Generator (2 * h + 1)) :=
    lSqFam h q (omega2Exp (4 * Monoid.exponent (GammaL ⧸ V.toSubgroup)))
  have hgen : Subgroup.closure
      (Set.range (fun i ↦ QuotientGroup.mk' V.toSubgroup (genL i))) = ⊤ :=
    closure_range_lower_eq_top (GQ2.quotientMk V.toSubgroup) (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR
        (2 * h + 1) q (Words.LSq.lSqW h))
      (GQ2.quotientMk_surjective V.toSubgroup)
  have hfree : Function.Surjective (FreeGroup.lift
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (genL i))) :=
    freeGroup_lift_surjective_of_closure hgen
  exact moduleRelatorRealizationAt_of_refined_relationModule rho (fun _ ↦ rfl)
    V hV wV hgen hfree
    (lUniform_wordLift_resolver hA₂)
    (lUniform_wordLift_resolver hA₂)
    (lUniform_rel_death (GQ2.quotientMk V.toSubgroup)) hRM
    (fun _ ↦ lUniform_moduleExt_resolver hA₂ _)

/-- The same fixed refinement supplies the weaker vector-dependent realization condition. -/
theorem lModuleRelatorRealization_of_refined_relationModule
    (rho : ContinuousMonoidHom GammaL C)
    (hA₂ : ∀ a : A, a + a = 0)
    (V : OpenNormalSubgroup GammaL)
    (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (hRM :
      letI : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      RelationModuleRelatorSurjective (A := A)
        (lSqFam h q
          (omega2Exp (4 * Monoid.exponent (GammaL ⧸ V.toSubgroup))))
        (lUniform_rel_death (GQ2.quotientMk V.toSubgroup))) :
    LModuleRelatorRealization (A := A) (e := eC) rho :=
  moduleRelatorRealization_of_at WL genL rho (fun i ↦ rho (genL i)) wC V hV
    (lModuleRelatorRealizationAt_of_refined_relationModule rho hA₂ V hV hRM)

end FixedRefinement

section UniformRefinedSupply

variable {h q : ℕ}

local notation "GammaL" => (gamma h q : Type)

/-- A corrected uniform relation-module supply at finite refinements.

For each surjective finite action target and each elementary coefficient module, it chooses one
deeper finite quotient contained in the action kernel.  Relation-module evaluation at that
quotient is surjective for the quotient's own improved L word.  The quotient may depend on `C`,
`rho`, and `A`, but not on the requested relator vector.  Thus this is stronger than the exact
vector-dependent `ModuleRelatorRealization` predicate, while avoiding any fixed-target Fox or
relation-basis premise. -/
noncomputable abbrev UniformElementaryRefinedRelationModuleSurjectiveSupply : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom GammaL C), Function.Surjective rho →
    ∀ (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (hA₂ : ∀ a : A, a + a = 0) →
        ∃ (V : OpenNormalSubgroup GammaL)
          (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
          letI : DiscreteTopology (GammaL ⧸ V.toSubgroup) :=
            Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup
          letI : DistribMulAction (GammaL ⧸ V.toSubgroup) A :=
            DistribMulAction.compHom A (quotientActionHom rho V hV)
          RelationModuleRelatorSurjective (A := A)
            (lSqFam h q
              (omega2Exp (4 * Monoid.exponent (GammaL ⧸ V.toSubgroup))))
            (lUniform_rel_death (GQ2.quotientMk V.toSubgroup))

private theorem continuousSMul_comp_refinedRelationModule
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

/-- The refined relation-module supply gives the exact all-elementary relator-realization
interface.  The chosen quotient is forgotten after converting its relation characters into
finite module cocycles. -/
theorem uniformElementaryRelatorRealizationSurjectiveSupply_of_refinedRelationModule
    (hRM : UniformElementaryRefinedRelationModuleSurjectiveSupply (h := h) (q := q)) :
    UniformElementaryRelatorRealizationSurjectiveSupply (h := h) (q := q) := by
  intro C _ _ _ _ rho hrho A _ _ _ hA₂
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalAddGroup A := by infer_instance
  letI : DistribMulAction GammaL A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul GammaL A :=
    continuousSMul_comp_refinedRelationModule rho (fun _ _ ↦ rfl)
  obtain ⟨V, hV, hRMV⟩ := hRM C rho hrho A hA₂
  exact lModuleRelatorRealization_of_refined_relationModule rho hA₂ V hV hRMV

/-- The corrected refined relation-module supply implies the continuous H² right-exact tail. -/
theorem gammaLH2RightExactSupply_of_refinedRelationModule
    (hRM : UniformElementaryRefinedRelationModuleSurjectiveSupply (h := h) (q := q)) :
    GammaLH2RightExactSupply h q :=
  gammaLH2RightExactSupply_of_allElementaryRelatorRealization
    (uniformElementaryRelatorRealizationSurjectiveSupply_of_refinedRelationModule hRM)

/-- For even `q`, the corrected refined relation-module supply implies the full Tate-duality
package for the improved L presentation. -/
noncomputable def tateDualityG_of_refinedRelationModule
    (hq : Even q)
    [DistribMulAction GammaL (MuN 2)] [ContinuousSMul GammaL (MuN 2)]
    (hRM : UniformElementaryRefinedRelationModuleSurjectiveSupply (h := h) (q := q)) :
    TateDualityG GammaL 2 :=
  tateDualityG_of_gammaLH2RightExactSupply hq
    (gammaLH2RightExactSupply_of_refinedRelationModule hRM)

end UniformRefinedSupply

end

end GQ2.Dyadic.LSquare
