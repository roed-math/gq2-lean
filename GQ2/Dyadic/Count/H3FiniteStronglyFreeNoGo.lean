/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteLevelFoxBoundary
import GQ2.Dyadic.Count.HTwoFoxStronglyFree

/-!
# Why finite-level strong freeness cannot prove completed Fox injectivity

The improved square relator has zero mod-two Fox row at the trivial quotient.  This file turns
that regression into sharp no-go theorems for the two existing finite-discrete interfaces:

* the actual one-relator Fox matrix at `Q = Unit` is not injective and has no equivariant left
  retraction;
* more intrinsically, the displayed relator is already trivial in
  `R/(R²[R,R])` at that target, so it cannot generate a split strongly-free regular summand.

Consequently neither `ModTwoFoxRelationRetraction` nor
`StronglyFreeModTwoRelatorSummand`, demanded separately at every finite quotient, can be the
Magnus--Labute input for the completed theorem.  The missing theorem must instead be an identity
theorem for the inverse limit (or a separated associated-graded argument), where a coefficient
which vanishes at a coarse quotient may be detected after refinement.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.FoxH GQ2.Dyadic GQ2.ContCoh
open GQ2.Dyadic.SqCore

/-- The trivial marking used by the terminal finite quotient of every completed presentation. -/
private def sqUnitMark (h : ℕ) : Fin (sqRank h) → Unit := fun _ => ()

/-- The improved discrete relator dies at the trivial marking. -/
private theorem sqUnitMark_relator (h : ℕ) :
    FreeGroup.lift (sqUnitMark h) (sqDiscreteRelator h) = 1 := by
  exact Subsingleton.elim _ _

/-- The source of the actual one-relator Fox row is nonzero even though the whole row vanishes
at the trivial quotient. -/
theorem not_injective_sqModTwoFoxRelationMatrixLinear_unit (h : ℕ) :
    ¬ Function.Injective (modTwoFoxRelationMatrixLinear
      (sqUnitMark h) (fun _ : Unit => sqDiscreteRelator h)) := by
  intro hinjective
  let e : RegularModTwoRelationModule Unit Unit :=
    Finsupp.single ((1 : Unit), ()) (1 : ZMod 2)
  have hezero : modTwoFoxRelationMatrixLinear
      (sqUnitMark h) (fun _ : Unit => sqDiscreteRelator h) e = 0 := by
    exact sqFiniteLevelModTwoFoxBoundary_unit_eq_zero h e
  have heq : e = 0 := hinjective (hezero.trans (map_zero _).symm)
  have hcoord := congrArg
    (fun c : RegularModTwoRelationModule Unit Unit => c ((1 : Unit), ())) heq
  simpa [e] using hcoord

/-- The actual one-relator Fox matrix at the trivial quotient admits no equivariant left
retraction. -/
theorem not_nonempty_sqModTwoFoxRelationRetraction_unit (h : ℕ) :
    ¬ Nonempty (ModTwoFoxRelationRetraction
      (sqUnitMark h) (fun _ : Unit => sqDiscreteRelator h)) := by
  apply not_nonempty_modTwoFoxRelationRetraction_of_not_injective
  intro hinjective
  let e : RegularModTwoRelationModule Unit Unit :=
    Finsupp.single ((1 : Unit), ()) (1 : ZMod 2)
  have hezero : modTwoFoxRelationMatrix
      (sqUnitMark h) (fun _ : Unit => sqDiscreteRelator h) e = 0 := by
    rw [← modTwoFoxRelationMatrixLinear_apply]
    exact sqFiniteLevelModTwoFoxBoundary_unit_eq_zero h e
  have heq : e = 0 := hinjective (hezero.trans (map_zero _).symm)
  have hcoord := congrArg
    (fun c : RegularModTwoRelationModule Unit Unit => c ((1 : Unit), ())) heq
  simpa [e] using hcoord

/-! ## Intrinsic failure of the finite strongly-free relation summand -/

/-- At a trivial marking, every free word belongs to the relation kernel. -/
private def sqUnitFreeToRelationKernel (h : ℕ) :
    FreeGroup (Fin (sqRank h)) →* FreeRelationKernel (sqUnitMark h) where
  toFun f := ⟨f, Subsingleton.elim _ _⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

/-- The canonical class of a free word in the elementary relation quotient at `Q = Unit`. -/
private def sqUnitRelationClass (h : ℕ) :
    FreeGroup (Fin (sqRank h)) →*
      FreeRelationModTwoQuotient (sqUnitMark h) :=
  (freeRelationModTwoMk (sqUnitMark h)).comp (sqUnitFreeToRelationKernel h)

/-- The improved relator has trivial class in `R/(R²[R,R])` at the trivial target.

This is stronger than the vanishing of its Fox derivative.  The quotient is commutative of
exponent two, while the relator's abelian collapse is `x⁻⁴y²`. -/
private theorem sqUnitRelationClass_sqDiscreteRelator (h : ℕ) :
    sqUnitRelationClass h (sqDiscreteRelator h) = 1 := by
  letI := freeRelationModTwoQuotientCommGroup (sqUnitMark h)
  have hlift : sqUnitRelationClass h = FreeGroup.lift
      (fun i => sqUnitRelationClass h (FreeGroup.of i)) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  rw [hlift, FreeGroup.lift_sqDiscreteRelator, sqRelWord_comm]
  have hsquare (z : FreeRelationModTwoQuotient (sqUnitMark h)) : z ^ 2 = 1 :=
    freeRelationModTwoQuotient_pow_two (sqUnitMark h) z
  rw [show 4 = 2 * 2 by omega, pow_mul]
  simp only [hsquare, inv_one, one_mul]

/-- The previous theorem written directly for the canonical relation-kernel element. -/
private theorem freeRelationModTwoMk_sqDiscreteRelator_unit (h : ℕ) :
    freeRelationModTwoMk (sqUnitMark h)
        ⟨sqDiscreteRelator h, MonoidHom.mem_ker.mpr (sqUnitMark_relator h)⟩ = 1 := by
  exact sqUnitRelationClass_sqDiscreteRelator h

/-- **Finite strong-freeness no-go.**  At the trivial quotient, the improved displayed relator
cannot generate a split regular summand of `R/(R²[R,R])`.

This rules out feeding the completed proof with the repository's existing finite-discrete
`StronglyFreeModTwoRelatorSummand` at every quotient.  The contradiction is intrinsic: the
displayed relator class is zero, whereas a strongly-free coordinate system must send it to the
nonzero regular basis vector. -/
theorem not_nonempty_sqStronglyFreeModTwoRelatorSummand_unit (h : ℕ) :
    ¬ Nonempty (StronglyFreeModTwoRelatorSummand
      (m := sqUnitMark h) (fun _ : Unit => sqDiscreteRelator h)
      (fun _ => sqUnitMark_relator h)) := by
  rintro ⟨B⟩
  let C := B.toModTwoRelationBasisCoordinates
  have hclass := freeRelationModTwoMk_sqDiscreteRelator_unit h
  have hcoord : C.coordinates
      ⟨sqDiscreteRelator h, MonoidHom.mem_ker.mpr (sqUnitMark_relator h)⟩ = 1 := by
    rw [← C.quotientCoordinates_mk, hclass, map_one]
  rw [C.relator ()] at hcoord
  have hone := congrArg
    (fun c : Multiplicative (RegularModTwoRelationModule Unit Unit) =>
      Multiplicative.toAdd c ((1 : Unit), ())) hcoord
  simpa using hone

end

end GQ2.Dyadic.Count
