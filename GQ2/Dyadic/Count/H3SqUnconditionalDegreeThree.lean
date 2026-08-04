/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteUniversalDegreeThreeComparison
import GQ2.Dyadic.Count.H3SqEventualRelationGeneration

/-!
# Unconditional square-presentation degree-three wrappers

`sqEventualRelationFoxGeneration` discharges the improved-relator generation premise in every
completed degree-three constructor.  This file records the resulting public constructor table:

* a universal bar syzygy has cofinal and eventual single-relator Fox range;
* a universal degree-three comparison has a completed single-relator syzygy boundary;
* adjoint cocycle cancellation has the same completed endpoint;
* fiberwise or cofinal compactness data has a nonempty completed endpoint;
* the syzygy-bar range and fully concrete transition-coherence hypotheses have that endpoint.

The stronger word-level normal-closure approximation is not used or changed.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh
open GQ2.Dyadic.SqCore

/-! ## Direct constructor wrappers -/

/-- Every compatible universal bar syzygy for the square presentation has exact cofinal
single-relator Fox range. -/
theorem sqUniversalBarFoxCofinalRange
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) :
    SqUniversalBarFoxCofinalRange S :=
  sqUniversalBarFoxCofinalRange_of_eventualRelationGeneration S
    (sqEventualRelationFoxGeneration h)

/-- Every compatible universal bar syzygy for the square presentation has the eventual range
needed by the completed compactness constructor. -/
theorem sqUniversalBarFoxEventualRange
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) :
    SqUniversalBarFoxEventualRange S :=
  sqUniversalBarFoxEventualRange_of_eventualRelationGeneration S
    (sqEventualRelationFoxGeneration h)

/-- A universal degree-three comparison for the improved square presentation automatically
produces its completed single-relator syzygy boundary. -/
noncomputable def
    SqFiniteInputUniversalDegreeThreeComparisonAt.completedSyzygyBoundaryOfSqPresentation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) :
    SqFiniteInputCompletedSyzygyBoundaryAt h V :=
  C.completedSyzygyBoundaryOfEventualGeneration
    (sqEventualRelationFoxGeneration h)

/-- Adjoint cocycle cancellation reaches the completed square-presentation endpoint without a
separate relation-generation argument. -/
noncomputable def
    SqFiniteInputCompletedSyzygyBoundaryAt.ofAdjointCocycleCancellationOfSqPresentation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (hcancel : SqFiniteInputUniversalAdjointCocycleCancellationAt U W hWV) :
    SqFiniteInputCompletedSyzygyBoundaryAt h V :=
  .ofAdjointCocycleCancellation U W hWV hcancel
    (sqEventualRelationFoxGeneration h)

/-- The compatible compactness output reaches the completed square-presentation endpoint
without carrying the now-discharged eventual-generation premise. -/
noncomputable def
    SqCompatibleUniversalCocycleCancellingSyzygyAt.completedSyzygyBoundaryOfSqPresentation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :
    SqFiniteInputCompletedSyzygyBoundaryAt h V :=
  S.completedSyzygyBoundary (sqEventualRelationFoxGeneration h)

/-! ## Compactness and concrete endpoint wrappers -/

/-- Fiberwise finite cofiltered compactness reaches the completed square-presentation
single-relator endpoint. -/
theorem nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_fibers_unconditional
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (hnonempty : ∀ U : OpenNormalSubgroup (DSq h : Type),
      Nonempty (SqUniversalCocycleOutputFiber h V U)) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  (nonempty_sqFiniteInputUniversalDegreeThreeComparisonAt_of_fibers
    h V hclosed hnonempty).map
      SqFiniteInputUniversalDegreeThreeComparisonAt.completedSyzygyBoundaryOfSqPresentation

/-- Cofinal local solvability and transition closure reach the completed square-presentation
single-relator endpoint unconditionally. -/
theorem nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_eventuallyNonempty_unconditional
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (heventual : SqUniversalCocycleOutputEventuallyNonempty h V) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_eventuallyNonempty
    h V hclosed heventual (sqEventualRelationFoxGeneration h)

/-- The concrete cofinal syzygy-bar range and transition closure reach the completed
square-presentation endpoint unconditionally. -/
theorem nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_syzygyBarCofinalRange_unconditional
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (hrange : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_syzygyBarCofinalRange
    h V hclosed hrange (sqEventualRelationFoxGeneration h)

/-- The fully concrete coherence hypotheses reach the completed square-presentation endpoint;
there is no remaining abstract relation-generation premise. -/
theorem nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_concreteCoherence_unconditional
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V)
    (hbar : SqUniversalBarInputTransitionRange h)
    (hcancel : SqUniversalBarInputCocycleCancellationTransitionKernel h V) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_concreteCoherence
    h V hlocal hbar hcancel (sqEventualRelationFoxGeneration h)

/-! ## Regression endpoint -/

/-- **Completed degree-three regression.**  The strongest current concrete inputs now imply the
actual completed single-improved-relator boundary package, with relation generation discharged
by the defining pro-two presentation itself. -/
theorem sqCompletedDegreeThree_concreteCoherence_regression
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V)
    (hbar : SqUniversalBarInputTransitionRange h)
    (hcancel : SqUniversalBarInputCocycleCancellationTransitionKernel h V) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_concreteCoherence_unconditional
    h V hlocal hbar hcancel

end

end GQ2.Dyadic.Count
