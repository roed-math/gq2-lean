/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationModuleRefined

/-!
# Vectorwise relation characters after finite refinement

`ModuleRelatorRealization` allows its finite quotient to depend on the requested relator
vector.  Consequently, a fixed-target relation-module splitting is stronger than the
continuous comparison needs (and can fail even at the trivial action target).

This file records the corresponding vectorwise transgression criterion.  For each requested
vector `r`, a witness may choose

* an open normal `V` contained in the action kernel,
* a new resolving word family on `G / V`, and
* one equivariant character of the relation kernel at `G / V`.

Only that one character has to extend the requested relator values, and only its transgressed
module extension has to resolve the profinite words.  Neither the quotient nor the word family
nor the character is uniform in `r`.

The weakest convenient witness asks the character values to agree with `r` modulo the *target*
Fox differential.  Exact realization is a special case.  Transgression realizes the character
values modulo the refined differential, and `heisD1_eq_of_resolvers_action_map` identifies the
refined and target differentials.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic

section OneCharacter

variable {X rel L A : Type} [Group L] [TopologicalSpace L]
  [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]
  {m : X → L}

/-- Transgressing one relation character realizes its own relator-value vector modulo the
word differential.  This is the vectorwise core of
`relatorRealization_of_relationModule`: no surjectivity statement about all relation
characters is used. -/
theorem relatorRealization_of_relationCharacter
    (W : rel → PWord X) (w : rel → FreeGroup X)
    (hres : ResolvesAt W w (WordLift A L))
    (hgen : Subgroup.closure (Set.range m) = ⊤)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (chi : FreeRelationCharacter m A)
    (hresExt : ResolvesAt W w
      (ModuleExt (relationCharacterCocycle
        (freeGroup_lift_surjective_of_closure hgen) chi))) :
    ∃ z : ModuleTwoCocycle L A,
      (fun k => moduleRel (W k) m z) -
          (fun k => chi.val ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩) ∈
        (heisD1 (A := A) m w).range := by
  let heval : Function.Surjective (FreeGroup.lift m) :=
    freeGroup_lift_surjective_of_closure hgen
  let z := relationCharacterCocycle heval chi
  let a : X → A := fun x => relationLiftCoord heval chi (FreeGroup.of x)
  refine ⟨z, ⟨-a, ?_⟩⟩
  funext k
  have hliftHom : FreeGroup.lift
      (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) =
      relationLift heval chi := by
    apply FreeGroup.ext_hom
    intro x
    rw [FreeGroup.lift_apply_of]
    exact (relationLift_of heval chi x).symm
  have hword : PWord.eval
      (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) (W k) =
      ModuleExt.incl z
        (chi.val ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩) := by
    calc
      PWord.eval (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) (W k) =
          FreeGroup.lift
            (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) (w k) :=
        (hresExt _ k).symm
      _ = relationLift heval chi (w k) :=
        congrArg (fun f => f (w k)) hliftHom
      _ = ModuleExt.incl z
          (chi.val ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩) :=
        relationLift_relation heval chi (w k) (hrel k)
  have hshift := moduleRel_shift W w m z hres a k
  rw [hword] at hshift
  simp only [Pi.sub_apply]
  rw [map_neg]
  have hz : heisD1 (A := A) m w a k + moduleRel (W k) m z =
      chi.val ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩ := by
    simpa using hshift.symm
  exact neg_eq_of_add_eq_zero_right (by rw [add_sub, hz, sub_self])

end OneCharacter

section VectorwiseRefinement

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

local instance relationModuleVectorwiseQuotientDiscreteTopology
    (V : OpenNormalSubgroup G) : DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- One vectorwise relation-character witness at an action-compatible finite refinement.

The character need only realize `r` modulo the target word differential.  The more familiar
condition `RelationCharacterRealizes word relation r character` implies `values_mod_range`
because zero belongs to that range. -/
structure RefinedRelationCharacterWitness
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (targetWord : rel → FreeGroup iota) (r : rel → A) where
  /-- The finite refinement, allowed to depend on `r`. -/
  V : OpenNormalSubgroup G
  /-- The refined quotient still acts through the fixed action target. -/
  hV : V.toSubgroup ≤ rho.toMonoidHom.ker
  /-- A quotient-dependent free-word resolver. -/
  word : rel → FreeGroup iota
  /-- The marked generators generate the refined quotient. -/
  generators : Subgroup.closure
    (Set.range (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) = ⊤
  /-- The selected words resolve the profinite relators in the refined word lift. -/
  resolves :
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    ResolvesAt W word (WordLift A (G ⧸ V.toSubgroup))
  /-- The selected words are relations at the refined marking. -/
  relation : ∀ k, FreeGroup.lift
    (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) (word k) = 1
  /-- The one relation character needed for this requested vector. -/
  character :
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    FreeRelationCharacter
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) A
  /-- Only the extension transgressed from `character` has to resolve the selected words. -/
  resolvesExtension :
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    ResolvesAt W word
      (ModuleExt (relationCharacterCocycle
        (freeGroup_lift_surjective_of_closure generators) character))
  /-- Character values agree with the requested vector modulo the fixed target differential. -/
  values_mod_range :
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    (fun k ↦ character.val
      ⟨word k, MonoidHom.mem_ker.mpr (relation k)⟩) - r ∈
        (heisD1 (A := A) c targetWord).range

/-- A sufficient relation-character criterion with the exact vectorwise quantifier shape:
every requested vector admits its own refinement and its own transgressible relation character.

This is not claimed to be necessary for `ModuleRelatorRealization`. -/
def VectorwiseRefinedRelationCharacterRealization
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (targetWord : rel → FreeGroup iota) : Prop :=
  ∀ r : rel → A,
    Nonempty (RefinedRelationCharacterWitness (gen := gen) (W := W)
      rho c targetWord r)

namespace RefinedRelationCharacterWitness

/-- Constructor for the common stronger input in which the relation character realizes the
requested vector exactly. -/
def ofRealizes
    (rho : ContinuousMonoidHom G C) (c : iota → C)
    (targetWord : rel → FreeGroup iota) (r : rel → A)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker)
    (word : rel → FreeGroup iota)
    (generators : Subgroup.closure
      (Set.range (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) = ⊤)
    (resolves :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ResolvesAt W word (WordLift A (G ⧸ V.toSubgroup)))
    (relation : ∀ k, FreeGroup.lift
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) (word k) = 1)
    (character :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      FreeRelationCharacter
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) A)
    (resolvesExtension :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ResolvesAt W word
        (ModuleExt (relationCharacterCocycle
          (freeGroup_lift_surjective_of_closure generators) character)))
    (realizes :
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      RelationCharacterRealizes word relation r character) :
    RefinedRelationCharacterWitness (gen := gen) (W := W)
      rho c targetWord r where
  V := V
  hV := hV
  word := word
  generators := generators
  resolves := resolves
  relation := relation
  character := character
  resolvesExtension := resolvesExtension
  values_mod_range := by
    letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
      DistribMulAction.compHom A (quotientActionHom rho V hV)
    have hzero : (fun k ↦ character.val
        ⟨word k, MonoidHom.mem_ker.mpr (relation k)⟩) - r = 0 := by
      funext k
      simp only [Pi.sub_apply, Pi.zero_apply]
      rw [realizes k, sub_self]
    rw [hzero]
    exact (heisD1 (A := A) c targetWord).range.zero_mem

end RefinedRelationCharacterWitness

omit [Fintype iota] [Fintype rel] [DecidableEq iota]
  [TotallyDisconnectedSpace G] [DistribMulAction G A] [ContinuousSMul G A] in
/-- Vectorwise refined relation characters give the finite relator-realization condition.

This theorem deliberately concludes `ModuleRelatorRealization`, not the stronger fixed-`V`
predicate `ModuleRelatorRealizationAt`: the witness quotient may depend on `r`.

Only this sound direction is claimed.  A general finite cocycle witness for
`ModuleRelatorRealization` has not been shown to be the transgression of a relation character
whose chosen free-word family also resolves in its module extension. -/
theorem moduleRelatorRealization_of_vectorwise_refined_relationCharacters
    (rho : ContinuousMonoidHom G C)
    (hc0 : ∀ i, rho (gen i) = c i)
    (htarget : ResolvesAt W targetWord (WordLift A C))
    (hsupply : VectorwiseRefinedRelationCharacterRealization
      (A := A) (gen := gen) (W := W) rho c targetWord) :
    ModuleRelatorRealization (A := A) W gen rho c targetWord := by
  intro r
  obtain ⟨S⟩ := hsupply r
  refine ⟨S.V, S.hV, ?_⟩
  let rhoV : (G ⧸ S.V.toSubgroup) →* C :=
    quotientActionHom rho S.V S.hV
  letI : DistribMulAction (G ⧸ S.V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  have hc : ∀ i,
      rhoV (QuotientGroup.mk' S.V.toSubgroup (gen i)) = c i := by
    intro i
    rw [quotientActionHom_mk]
    exact hc0 i
  have hd : heisD1 (A := A)
      (fun i ↦ QuotientGroup.mk' S.V.toSubgroup (gen i)) S.word =
      heisD1 (A := A) c targetWord :=
    heisD1_eq_of_resolvers_action_map S.word rhoV (fun _ _ ↦ rfl)
      hc S.resolves htarget
  obtain ⟨z, hz⟩ := relatorRealization_of_relationCharacter
    W S.word S.resolves S.generators S.relation S.character
      S.resolvesExtension
  refine ⟨z, ?_⟩
  rw [hd] at hz
  have hadd := (heisD1 (A := A) c targetWord).range.add_mem
    hz S.values_mod_range
  convert hadd using 1
  funext k
  simp only [Pi.sub_apply, Pi.add_apply]
  abel

end VectorwiseRefinement

end

end GQ2.Dyadic.Count
