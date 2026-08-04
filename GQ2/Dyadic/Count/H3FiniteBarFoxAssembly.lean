/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteLevelFoxBoundary
import GQ2.Dyadic.Count.ContinuousCochainFiniteLevel

/-!
# Finite-refinement assembly for the improved square presentation

Continuous degree-three cohomology is the direct limit of finite-quotient cohomology.  A finite
2-group quotient should therefore not be expected to have `H³ = 0` itself.  The exact target is
instead that every finite-level cocycle becomes a `d²` boundary after passage to some finer open
normal quotient.  `ContinuousCochainFiniteLevel` proves this target equivalent to
`ModTwoHThreeExact`.

This file ties that criterion to the actual improved square presentation.  Its finite Fox rows
are evaluated at the images of `SqCore.sqGen h`, and the resulting boundary square commutes under
every refinement.  Consequently the remaining finite bar--Fox calculation has one precise
output: construct `FiniteRefinementModTwoHThreeExact (SqCore.DSq h)` using these commuting rows.
Pointwise injectivity is neither used nor true (the row at the trivial quotient is zero).
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

/-- The actual improved-presentation generators in an open-normal quotient of `DSq h`. -/
def sqOpenQuotientMarking (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) ⧸ V.toSubgroup :=
  fun i ↦ QuotientGroup.mk' V.toSubgroup (sqGen h i)

/-- The actual quotient markings commute with refinement. -/
@[simp] theorem openNormalQuotientProj_sqOpenQuotientMarking
    (h : ℕ) {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup) (i : Fin (sqRank h)) :
    openNormalQuotientProj hWV (sqOpenQuotientMarking h W i) =
      sqOpenQuotientMarking h V i := by
  change openNormalQuotientProj hWV
      (QuotientGroup.mk' W.toSubgroup (sqGen h i)) =
    QuotientGroup.mk' V.toSubgroup (sqGen h i)
  exact openNormalQuotientProj_mk hWV (sqGen h i)

/-- The finite Fox boundary for the literal improved square relator commutes from a finer
open-normal quotient to a coarser one.  This is the quotient-indexed chain-map square needed by
any finite bar--Fox construction. -/
theorem sqOpenQuotientFoxBoundary_natural
    (h : ℕ) {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ W.toSubgroup) Unit) :
    regularModTwoPushforward (openNormalQuotientProj hWV) (Fin (sqRank h))
        ((sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h W)).map c) =
      (sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h V)).map
        (regularModTwoPushforward (openNormalQuotientProj hWV) Unit c) := by
  simpa only [openNormalQuotientProj_sqOpenQuotientMarking] using
    sqFiniteLevelModTwoFoxBoundary_natural
      (openNormalQuotientProj hWV) h (sqOpenQuotientMarking h W) c

/-- The finite-refinement bar--Fox target immediately supplies scalar `H³` exactness for the
actual improved square core. -/
theorem modTwoHThreeExact_DSq_of_finiteRefinement (h : ℕ)
    (S : FiniteRefinementModTwoHThreeExact (DSq h : Type)) :
    ModTwoHThreeExact (DSq h : Type) :=
  modTwoHThreeExact_of_finiteRefinement S

/-- Once the finite-refinement target is proved, scalarization gives the full finite-elementary
coefficient `H²` right-exactness theorem required downstream. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_finiteRefinement (h : ℕ)
    (S : FiniteRefinementModTwoHThreeExact (DSq h : Type)) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_modTwoHThreeExact h
    (modTwoHThreeExact_DSq_of_finiteRefinement h S)

end

end GQ2.Dyadic.Count
