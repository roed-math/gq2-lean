/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationModule
import GQ2.Dyadic.Count.HTwoModuleFlexible

/-!
# Relation-module transgression after a finite refinement

A relation-module splitting at the finite *action target* is generally too strong.  The exact
continuous comparison permits a deeper finite quotient `G / V`, with `V ≤ ker rho`, and that
quotient may depend on the requested coefficient data.  This file feeds relation-module
transgression at such a refinement into `ModuleRelatorRealizationAt`.

The resolving word at the refinement may differ from the fixed target word.  The already-proved
resolver base-change theorem identifies their Fox-differential ranges because both resolve the
same profinite relator and the refined action factors through the target action.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic

section RefinedTarget

set_option maxHeartbeats 2000000

variable {iota rel : Type} [Fintype iota] [Fintype rel] [DecidableEq iota]
  {G A C : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]
  {gen : iota → G} {W : rel → PWord iota} {targetWord : rel → FreeGroup iota}
  {c : iota → C}

local instance relationModuleRefinedQuotientDiscreteTopology
    (V : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- Relation-module surjectivity at a deeper action-compatible finite quotient gives the exact
finite relator realization at that quotient.  Unlike `moduleRelatorRealization_of_target`, the
Schreier cocycle lives on `G / V`, not on the possibly much smaller action target `C`. -/
theorem moduleRelatorRealizationAt_of_refined_relationModule
    (rho : ContinuousMonoidHom G C)
    (hc0 : ∀ i, rho (gen i) = c i)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (refinedWord : rel → FreeGroup iota)
    (hgen : Subgroup.closure
      (Set.range (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) = ⊤)
    (hfree : Function.Surjective (FreeGroup.lift
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))))
    (hrefined :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ResolvesAt W refinedWord (WordLift A (G ⧸ V.toSubgroup)))
    (htarget : ResolvesAt W targetWord (WordLift A C))
    (hrel : ∀ k, FreeGroup.lift
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) (refinedWord k) = 1)
    (hRM :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      RelationModuleRelatorSurjective (A := A) refinedWord hrel)
    (hresExt :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ∀ chi : FreeRelationCharacter
          (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) A,
        ResolvesAt W refinedWord
          (ModuleExt (relationCharacterCocycle
            hfree chi))) :
    ModuleRelatorRealizationAt (A := A) W gen rho c targetWord V hV := by
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  have hc : ∀ i, rhoV (QuotientGroup.mk' V.toSubgroup (gen i)) = c i := by
    intro i
    rw [quotientActionHom_mk]
    exact hc0 i
  have hd : heisD1 (A := A)
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) refinedWord =
      heisD1 (A := A) c targetWord :=
    heisD1_eq_of_resolvers_action_map refinedWord rhoV (fun _ _ ↦ rfl)
      hc hrefined htarget
  intro r
  obtain ⟨z, hz⟩ := relatorRealization_of_relationModule W refinedWord hrefined
    hgen hrel hRM hresExt r
  refine ⟨z, ?_⟩
  rw [← hd]
  exact hz

end RefinedTarget

end

end GQ2.Dyadic.Count
