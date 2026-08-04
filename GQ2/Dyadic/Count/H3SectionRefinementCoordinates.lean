/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteBarFoxReverse

/-!
# Relation-module reduction for section-refinement coordinates

The reverse finite bar comparison is natural across a quotient only up to the Fox derivative of
the normalized-section defect.  This file identifies exactly when that defect can be corrected
by the displayed presentation relators.

First, a general Fox-calculus lemma proves that every word in the abstract normal closure of a
relator family has derivative in the range of its finite Fox matrix.  Applied to the improved
square word, this constructs the required coordinate whenever each section-refinement defect
belongs to the normal closure of that one word.

The converse condition needed for the reverse comparison is weaker: only the derivatives of the
specific section defects need lie in the Fox range.  We prove that this restricted range condition
is equivalent to nonemptiness of `FiniteSectionRefinementRelatorCoordinates`, and specialize the
equivalence to actual open-normal quotients of `DSq h`.  This is strictly below the full
finite-to-completed bar--Fox assembly: it concerns degree-one refinement homotopies only, asks
nothing about arbitrary relation-kernel elements, and contains no degree-three primitive.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

variable {Q I rel : Type} [Group Q]

/-! ## Fox range and normal closure -/

/-- The range of a finite Fox matrix is stable under regular translation. -/
theorem modTwoFoxRelationMatrixLinear_range_translate
    (m : I → Q) (w : rel → FreeGroup I) (g : Q)
    {c : RegularModTwoRelationModule Q I}
    (hc : c ∈ (modTwoFoxRelationMatrixLinear m w).range) :
    regularModTwoTranslate Q I g c ∈
      (modTwoFoxRelationMatrixLinear m w).range := by
  obtain ⟨a, rfl⟩ := hc
  refine ⟨regularModTwoTranslate Q rel g a, ?_⟩
  rw [modTwoFoxRelationMatrixLinear_apply,
    modTwoFoxRelationMatrixLinear_apply,
    modTwoFoxRelationMatrix_translate]

/-- Free words which evaluate to one and whose mod-two Fox derivative lies in the displayed
Fox range. -/
def modTwoFoxRangeKernel (m : I → Q) (w : rel → FreeGroup I) :
    Subgroup (FreeGroup I) where
  carrier := {f | FreeGroup.lift m f = 1 ∧
    modTwoFoxDerivative m f ∈ (modTwoFoxRelationMatrixLinear m w).range}
  one_mem' := by
    constructor
    · simp
    · exact ⟨0, by simp [modTwoFoxRelationMatrixLinear_apply]⟩
  mul_mem' := by
    rintro a b ⟨haeval, ha⟩ ⟨hbeval, hb⟩
    constructor
    · simp [haeval, hbeval]
    · let ar : FreeRelationKernel m := ⟨a, haeval⟩
      let br : FreeRelationKernel m := ⟨b, hbeval⟩
      change modTwoFoxDerivative m (ar * br : FreeGroup I) ∈ _
      rw [modTwoFoxDerivative_mul_kernel]
      exact (modTwoFoxRelationMatrixLinear m w).range.add_mem ha hb
  inv_mem' := by
    rintro a ⟨haeval, ha⟩
    constructor
    · simp [haeval]
    · simp only [modTwoFoxDerivative, map_inv, WordLift.inv_u,
        lift_foxLift_g, haeval, inv_one, one_smul, ZModModule.neg_eq_self]
      exact ha

/-- The preceding Fox-range kernel is normal in the whole free group. -/
instance modTwoFoxRangeKernel_normal (m : I → Q) (w : rel → FreeGroup I) :
    (modTwoFoxRangeKernel m w).Normal where
  conj_mem n hn g := by
    rcases hn with ⟨hneval, hnfox⟩
    constructor
    · simp only [map_mul, map_inv, hneval]
      group
    · let nr : FreeRelationKernel m := ⟨n, hneval⟩
      have hfox := congrArg Multiplicative.toAdd
        (modTwoRelationFoxMap_conjugation m g nr)
      change modTwoFoxDerivative m (g * n * g⁻¹) =
        regularModTwoTranslate Q I (FreeGroup.lift m g)
          (modTwoFoxDerivative m n) at hfox
      rw [hfox]
      exact modTwoFoxRelationMatrixLinear_range_translate m w _ hnfox

/-- **Normal-closure Fox generation.** If all displayed relators evaluate to one, every word in
their abstract normal closure has its universal mod-two Fox derivative in the range of the
displayed finite Fox matrix. -/
theorem modTwoFoxDerivative_mem_range_of_mem_normalClosure
    (m : I → Q) (w : rel → FreeGroup I)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    {f : FreeGroup I} (hf : f ∈ Subgroup.normalClosure (Set.range w)) :
    modTwoFoxDerivative m f ∈ (modTwoFoxRelationMatrixLinear m w).range := by
  have hle : Subgroup.normalClosure (Set.range w) ≤ modTwoFoxRangeKernel m w :=
    Subgroup.normalClosure_le_normal <| by
      rintro _ ⟨k, rfl⟩
      refine ⟨hrel k, ?_⟩
      refine ⟨Finsupp.single ((1 : Q), k) 1, ?_⟩
      rw [modTwoFoxRelationMatrixLinear_apply,
        modTwoFoxRelationMatrix_basis]
  exact (hle hf).2

/-! ## Exact restricted range criterion -/

variable {Q' : Type} [Group Q']

/-- The strictly minimal generation statement for corrected degree-one naturality: only the
Fox derivatives of the normalized section-refinement defects must lie in the relator row's
range. -/
def SectionRefinementDefectsInFoxRange
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (w : rel → FreeGroup I) : Prop :=
  ∀ q,
    modTwoFoxDerivative (fun i ↦ phi (m i))
        (relationSectionRefinementDefect phi m heval heval' q).1 ∈
      (modTwoFoxRelationMatrixLinear (fun i ↦ phi (m i)) w).range

/-- The restricted range statement is exactly nonemptiness of the coordinate data used by the
corrected naturality theorem. -/
theorem nonempty_finiteSectionRefinementRelatorCoordinates_iff
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (w : rel → FreeGroup I) :
    Nonempty (FiniteSectionRefinementRelatorCoordinates
        phi m heval heval' rel w) ↔
      SectionRefinementDefectsInFoxRange phi m heval heval' w := by
  constructor
  · rintro ⟨C⟩ q
    refine ⟨C.coordinate q, ?_⟩
    simpa [modTwoFoxRelationMatrixLinear_apply] using C.fox q
  · intro hrange
    choose coordinate hcoordinate using hrange
    refine ⟨{
      coordinate := coordinate
      fox := fun q ↦ ?_
    }⟩
    simpa [modTwoFoxRelationMatrixLinear_apply] using hcoordinate q

/-- Abstract-normal-closure membership of every section defect is a sufficient, stronger
group-theoretic criterion for the restricted Fox-range condition. -/
theorem sectionRefinementDefectsInFoxRange_of_normalClosure
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (w : rel → FreeGroup I)
    (hrel : ∀ k, FreeGroup.lift (fun i ↦ phi (m i)) (w k) = 1)
    (hnormal : ∀ q,
      (relationSectionRefinementDefect phi m heval heval' q).1 ∈
        Subgroup.normalClosure (Set.range w)) :
    SectionRefinementDefectsInFoxRange phi m heval heval' w := by
  intro q
  exact modTwoFoxDerivative_mem_range_of_mem_normalClosure
    (fun i ↦ phi (m i)) w hrel (hnormal q)

/-- Consequently the normal-closure criterion constructs the exact degree-one refinement
coordinate data. -/
theorem nonempty_finiteSectionRefinementRelatorCoordinates_of_normalClosure
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (w : rel → FreeGroup I)
    (hrel : ∀ k, FreeGroup.lift (fun i ↦ phi (m i)) (w k) = 1)
    (hnormal : ∀ q,
      (relationSectionRefinementDefect phi m heval heval' q).1 ∈
        Subgroup.normalClosure (Set.range w)) :
    Nonempty (FiniteSectionRefinementRelatorCoordinates
      phi m heval heval' rel w) :=
  (nonempty_finiteSectionRefinementRelatorCoordinates_iff
    phi m heval heval' w).2
      (sectionRefinementDefectsInFoxRange_of_normalClosure
        phi m heval heval' w hrel hnormal)

end

end GQ2.Dyadic.Count
