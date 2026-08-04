/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.CompletedModTwoFoxBoundary

/-!
# Compatible-family form of completed Fox injectivity

The completed one-relator Fox boundary is not injective quotient by quotient: at the trivial
quotient its whole row is zero.  Its meaningful injectivity statement is instead an assertion
about compatible families over *all* open normal quotients.

For the actual completed boundary of the improved square relator, this file proves that
injectivity is equivalent to a local finite-refinement statement.  Given a compatible relation
coefficient which is nonzero at `G/U`, some finer quotient `G/W`, `W ≤ U`, must detect it under
the Fox row.  This formulation is compatible with the zero row at the trivial quotient and is
the precise finite-refinement (Magnus--Labute) lemma still missing from the formalization.

The final constructors wire the already-proved nonsquareness of `sqRelator h` into that exact
lemma.  The lemma remains an explicit theorem parameter: no axiom, cohomological vanishing
statement, or pointwise finite-level injectivity premise is introduced.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.Count GQ2.Dyadic.SqCore

private abbrev SqRelationCompletion (h : ℕ) :=
  ModTwoCompletedRegularModule (DSq h : Type) Unit

private abbrev SqGeneratorCompletion (h : ℕ) :=
  ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h))

/-- The exact finite-refinement statement needed for completed Fox injectivity.

It does not ask the Fox row at `U` to detect the coordinate at `U`; it may pass to an
arbitrarily fine `W ≤ U`.  Thus the statement does not contradict
`sqFiniteLevelModTwoFoxBoundary_unit_eq_zero`. -/
def SqCompletedFoxRefinementDetection (h : ℕ) : Prop :=
  ∀ (c : SqRelationCompletion h) (U : OpenNormalSubgroup (DSq h : Type)),
    ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit U c ≠ 0 →
      ∃ (W : OpenNormalSubgroup (DSq h : Type)), W ≤ U ∧
        (sqFiniteLevelModTwoFoxBoundary h
            (fun i => QuotientGroup.mk' W.toSubgroup (sqGen h i))).map
          (ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit W c) ≠ 0

/-- Finite-refinement detection implies injectivity of the actual completed Fox boundary. -/
theorem sqCompletedModTwoFoxBoundary_injective_of_refinementDetection
    (h : ℕ) (hdetect : SqCompletedFoxRefinementDetection h) :
    Function.Injective (sqCompletedModTwoFoxBoundary h).map := by
  intro a b hab
  have hsub : (sqCompletedModTwoFoxBoundary h).map (a - b) = 0 := by
    calc
      (sqCompletedModTwoFoxBoundary h).map (a - b) =
          (sqCompletedModTwoFoxBoundary h).map a -
            (sqCompletedModTwoFoxBoundary h).map b :=
        LinearMap.map_sub (sqCompletedModTwoFoxBoundary h).map a b
      _ = 0 := sub_eq_zero.mpr hab
  have hsubzero : a - b = 0 := by
    apply ModTwoCompletedRegularModule.ext (DSq h : Type) Unit
    intro U
    by_contra hU
    obtain ⟨W, -, hW⟩ := hdetect (a - b) U hU
    have hcoord := congrArg
      (fun z : SqGeneratorCompletion h =>
        ModTwoCompletedRegularModule.coordinate (DSq h : Type)
          (Fin (sqRank h)) W z) hsub
    rw [sqCompletedModTwoFoxBoundary_coordinate] at hcoord
    exact hW (by simpa using hcoord)
  exact sub_eq_zero.mp hsubzero

/-- Conversely, injectivity gives finite-refinement detection.

If injectivity detects a compatible family at some quotient `V`, intersecting `V` with the
prescribed `U` produces a detecting quotient below `U`.  Compatibility prevents a nonzero Fox
coordinate at `V` from having zero Fox coordinate at that refinement. -/
theorem refinementDetection_of_sqCompletedModTwoFoxBoundary_injective
    (h : ℕ) (hinj : Function.Injective (sqCompletedModTwoFoxBoundary h).map) :
    SqCompletedFoxRefinementDetection h := by
  intro c U hcU
  have hc : c ≠ 0 := by
    intro hczero
    have hcoord := congrArg
      (fun z : SqRelationCompletion h =>
        ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit U z) hczero
    exact hcU (by simpa using hcoord)
  have hfc : (sqCompletedModTwoFoxBoundary h).map c ≠ 0 := by
    intro hfzero
    exact hc (hinj (hfzero.trans (map_zero (sqCompletedModTwoFoxBoundary h).map).symm))
  have hexists : ∃ V : OpenNormalSubgroup (DSq h : Type),
      ModTwoCompletedRegularModule.coordinate (DSq h : Type) (Fin (sqRank h)) V
        ((sqCompletedModTwoFoxBoundary h).map c) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hfc
    apply ModTwoCompletedRegularModule.ext (DSq h : Type) (Fin (sqRank h))
    intro V
    simpa using hall V
  obtain ⟨V, hV⟩ := hexists
  let W : OpenNormalSubgroup (DSq h : Type) := U ⊓ V
  refine ⟨W, inf_le_left, ?_⟩
  intro hW
  have hcompat := ModTwoCompletedRegularModule.coordinate_compatible
    (DSq h : Type) (Fin (sqRank h))
    ((sqCompletedModTwoFoxBoundary h).map c) (show W ≤ V from inf_le_right)
  rw [sqCompletedModTwoFoxBoundary_coordinate, hW, map_zero] at hcompat
  exact hV hcompat.symm

/-- **Exact completed-kernel criterion.**  Injectivity of the completed improved-square Fox
boundary is equivalent to finite-refinement detection of every nonzero compatible coordinate.

This equivalence isolates the genuine classical input without replacing it by the false claim
that each finite-level boundary is injective. -/
theorem sqCompletedModTwoFoxBoundary_injective_iff_refinementDetection (h : ℕ) :
    Function.Injective (sqCompletedModTwoFoxBoundary h).map ↔
      SqCompletedFoxRefinementDetection h := by
  constructor
  · exact refinementDetection_of_sqCompletedModTwoFoxBoundary_injective h
  · exact sqCompletedModTwoFoxBoundary_injective_of_refinementDetection h

/-- The exact square-relator specialization of the classical Magnus--Labute step.

The explicit theorem parameter says that nonsquareness in the free pro-two group forces
finite-refinement detection for the *actual* compatible Fox row.  The word-theoretic premise is
then discharged by the order-32 witness already formalized in `InitialForm.lean`. -/
theorem sqCompletedModTwoFoxBoundary_injective_of_nonSquare_refinement
    (h : ℕ)
    (magnusLabute :
      IsNonSquareInFreeProTwo (sqRelator h) → SqCompletedFoxRefinementDetection h) :
    Function.Injective (sqCompletedModTwoFoxBoundary h).map :=
  sqCompletedModTwoFoxBoundary_injective_of_refinementDetection h
    (magnusLabute (isNonSquareInFreeProTwo_sqRelator h))

/-- Package the refinement form of the Magnus--Labute theorem into the existing completed-Fox
injectivity interface.  This connects the concrete completed boundary to the continuous
one-relator asphericity route without adding a new structure field. -/
def nonSquareDSqFoxInjectivity_of_refinement
    (h : ℕ)
    (magnusLabute :
      IsNonSquareInFreeProTwo (sqRelator h) → SqCompletedFoxRefinementDetection h) :
    NonSquareDSqFoxInjectivity h
      (SqRelationCompletion h) (SqGeneratorCompletion h)
      (sqCompletedModTwoFoxBoundary h) where
  injective hnonsquare :=
    sqCompletedModTwoFoxBoundary_injective_of_refinementDetection h
      (magnusLabute hnonsquare)

/-- With a continuous bar--Fox comparison, the same finite-refinement lemma closes scalar
continuous `H³` for `DSq h`.  This is the end-to-end form of the remaining one-relator route. -/
theorem modTwoHThreeExact_DSq_of_sqCompletedFox_refinement
    (h : ℕ)
    (comparison : ContinuousModTwoBarFoxComparison
      (SqRelationCompletion h) (SqGeneratorCompletion h)
      (sqCompletedModTwoFoxBoundary h))
    (magnusLabute :
      IsNonSquareInFreeProTwo (sqRelator h) → SqCompletedFoxRefinementDetection h) :
    ModTwoHThreeExact (DSq h : Type) :=
  modTwoHThreeExact_DSq_of_completedFox h (sqCompletedModTwoFoxBoundary h) comparison
    (nonSquareDSqFoxInjectivity_of_refinement h magnusLabute)

end

end GQ2.ContCoh
