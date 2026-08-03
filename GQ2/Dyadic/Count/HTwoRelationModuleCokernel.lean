/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoRelationModuleVectorwise

/-!
# Relation characters modulo the word differential

Exact arbitrary values on displayed relators are stronger than finite cocycle realization.
The latter only sees a relator vector modulo the image of the word differential `heisD1`.
This file records the corresponding fixed-target relation-character predicate and its sound
transgression theorem.

The predicate remains a *fixed-target* statement.  It should not be confused with
`VectorwiseRefinedRelationCharacterRealization`, where the finite quotient may depend on the
requested vector.  In particular, the fixed-target predicate can still fail at a small action
target even though the refined predicate, and hence the continuous comparison, may hold.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic

section FixedTarget

variable {X rel L A : Type} [Group L] [TopologicalSpace L]
  [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]
  {m : X → L}

/-- Fixed-target relation-character surjectivity after passing to the cokernel of the word
differential.  For every requested relator vector, one relation character has displayed values
congruent to that vector modulo `heisD1.range`.

Only this sufficient direction is used below; no converse or necessity claim is made. -/
def RelationModuleRelatorCokernelSurjective
    (w : rel → FreeGroup X)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1) : Prop :=
  ∀ r : rel → A, ∃ chi : FreeRelationCharacter m A,
    (fun k ↦ chi.val ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩) - r ∈
      (heisD1 (A := A) m w).range

/-- Exact relation-character coordinates imply the cokernel-valued criterion. -/
theorem relationModuleRelatorCokernelSurjective_of_surjective
    (w : rel → FreeGroup X)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (hRM : RelationModuleRelatorSurjective (A := A) w hrel) :
    RelationModuleRelatorCokernelSurjective (A := A) w hrel := by
  intro r
  obtain ⟨chi, hchi⟩ := hRM r
  refine ⟨chi, ?_⟩
  have hzero :
      (fun k ↦ chi.val ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩) - r = 0 := by
    funext k
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [hchi k, sub_self]
  rw [hzero]
  exact (heisD1 (A := A) m w).range.zero_mem

/-- The cokernel-valued relation-character criterion gives finite cocycle relator realization
at the same finite target.

Transgression first realizes the selected character values modulo `heisD1.range`.  Adding the
predicate's congruence from those values to the requested vector gives the desired result. -/
theorem relatorRealization_of_relationModuleCokernel
    (W : rel → PWord X) (w : rel → FreeGroup X)
    (hres : ResolvesAt W w (WordLift A L))
    (hgen : Subgroup.closure (Set.range m) = ⊤)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (hRM : RelationModuleRelatorCokernelSurjective (A := A) w hrel)
    (hresExt : ∀ chi : FreeRelationCharacter m A,
      ResolvesAt W w (ModuleExt (relationCharacterCocycle
        (freeGroup_lift_surjective_of_closure hgen) chi))) :
    ∀ r : rel → A, ∃ z : ModuleTwoCocycle L A,
      (fun k ↦ moduleRel (W k) m z) - r ∈
        (heisD1 (A := A) m w).range := by
  intro r
  obtain ⟨chi, hchi⟩ := hRM r
  obtain ⟨z, hz⟩ := relatorRealization_of_relationCharacter
    W w hres hgen hrel chi (hresExt chi)
  refine ⟨z, ?_⟩
  have hadd := (heisD1 (A := A) m w).range.add_mem hz hchi
  convert hadd using 1
  funext k
  simp only [Pi.sub_apply, Pi.add_apply]
  abel

end FixedTarget

end

end GQ2.Dyadic.Count
