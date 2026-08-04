/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.CompletedRankOneFox
import GQ2.Dyadic.Count.H3AugmentationFiltration
import GQ2.Dyadic.Count.H3CompatibleFoxInjectivity
import GQ2.Dyadic.Count.H3FiniteBarFoxAssembly

/-!
# End-to-end reduction through the completed Fox row

This file composes the two honest lower-level inputs isolated by the completed one-relator
campaign:

* separation and associated-graded regularity for the actual completed Fox-derivative row;
* a finite-to-completed bar--Fox chain homotopy for the actual improved presentation.

The first input gives completed Fox injectivity.  The second converts that injectivity into
eventual finite-level primitives and hence continuous mod-two `H³` exactness.  Scalar
coefficient devissage then supplies the finite-elementary `H²` right-exactness used downstream.
No field below assumes injectivity, a primitive, or cohomological vanishing.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.Count GQ2.Dyadic.SqCore

/-- Separated augmentation powers and initial-form regularity of the actual improved Fox row
give injectivity of the actual completed Fox boundary. -/
theorem sqCompletedModTwoFoxBoundary_injective_of_augmentationInitialRegular
    (h : ℕ)
    (hsep : ModTwoCompletedAugmentationSeparated (G := DSq h))
    (hregular : CompletedRowAugmentationInitialRegular (DSq h : Type)
      (sqCompletedModTwoFoxDerivativeRow h)) :
    Function.Injective (sqCompletedModTwoFoxBoundary h).map := by
  apply (sqCompletedModTwoFoxBoundary_injective_iff_commonAnnihilator h).2
  exact completedRowCommonLeftAnnihilatorFree_of_augmentationInitialRegular
    (DSq h : Type) (sqCompletedModTwoFoxDerivativeRow h) hsep hregular

/-- The same initial-form hypotheses imply the exact compatible-family refinement-detection
criterion. -/
theorem sqCompletedFoxRefinementDetection_of_augmentationInitialRegular
    (h : ℕ)
    (hsep : ModTwoCompletedAugmentationSeparated (G := DSq h))
    (hregular : CompletedRowAugmentationInitialRegular (DSq h : Type)
      (sqCompletedModTwoFoxDerivativeRow h)) :
    SqCompletedFoxRefinementDetection h :=
  refinementDetection_of_sqCompletedModTwoFoxBoundary_injective h
    (sqCompletedModTwoFoxBoundary_injective_of_augmentationInitialRegular
      h hsep hregular)

/-- The two lower-level constructions yield the eventual finite-quotient primitive theorem. -/
theorem finiteRefinementModTwoHThreeExact_DSq_of_augmentation_barFox
    (h : ℕ)
    (hsep : ModTwoCompletedAugmentationSeparated (G := DSq h))
    (hregular : CompletedRowAugmentationInitialRegular (DSq h : Type)
      (sqCompletedModTwoFoxDerivativeRow h))
    (assembly : SqFiniteToCompletedBarFoxAssembly h) :
    FiniteRefinementModTwoHThreeExact (DSq h : Type) :=
  finiteRefinementModTwoHThreeExact_DSq_of_barFoxAssembly h
    (sqCompletedModTwoFoxBoundary_injective_of_augmentationInitialRegular
      h hsep hregular)
    assembly

/-- End-to-end scalar continuous `H³` exactness for the improved square core from the two
remaining classical constructions. -/
theorem modTwoHThreeExact_DSq_of_augmentation_barFox
    (h : ℕ)
    (hsep : ModTwoCompletedAugmentationSeparated (G := DSq h))
    (hregular : CompletedRowAugmentationInitialRegular (DSq h : Type)
      (sqCompletedModTwoFoxDerivativeRow h))
    (assembly : SqFiniteToCompletedBarFoxAssembly h) :
    ModTwoHThreeExact (DSq h : Type) :=
  modTwoHThreeExact_of_finiteRefinement
    (finiteRefinementModTwoHThreeExact_DSq_of_augmentation_barFox
      h hsep hregular assembly)

/-- The same two constructions supply the full finite-elementary coefficient `H²`
right-exactness theorem required by the maximal-pro-two package. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_augmentation_barFox
    (h : ℕ)
    (hsep : ModTwoCompletedAugmentationSeparated (G := DSq h))
    (hregular : CompletedRowAugmentationInitialRegular (DSq h : Type)
      (sqCompletedModTwoFoxDerivativeRow h))
    (assembly : SqFiniteToCompletedBarFoxAssembly h) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_modTwoHThreeExact h
    (modTwoHThreeExact_DSq_of_augmentation_barFox h hsep hregular assembly)

end

end GQ2.ContCoh
