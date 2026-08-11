/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8, Fable-5, and OpenAI Codex
-/
module

public import GQ2.Foundations.Axioms
public import GQ2.Foundations.LiteratureInputs

@[expose] public section

/-!
# Legacy literature-input provider

This module is the opt-in bridge from the nine historical axiom declarations to the generic
`LiteratureInputs` API.  Keeping it separate leaves `GQ2.Foundations.Axioms` axioms-only.
-/

namespace GQ2

/-- Importing this module selects the legacy axiom-backed literature inputs. -/
noncomputable instance axiomaticLiteratureInputs : LiteratureInputs where
  absGalQ2_isTopologicallyFinitelyGenerated :=
    Foundations.absGalQ2_isTopologicallyFinitelyGenerated
  absGalQ2_localEulerCharacteristic :=
    Foundations.absGalQ2_localEulerCharacteristic
  dyadicOrientation := dyadicOrientation
  localReciprocity := localReciprocity
  tateDualityAt := tateDualityAt
  peripheralCyclotomicAction := peripheralCyclotomicAction
  relativeStiefelWhitney_dyadic := relativeStiefelWhitney_dyadic
  tameQuotient := tameQuotient
  hilbertSymbol_normCriterion_finiteDyadic := hilbertSymbol_normCriterion_finiteDyadic

end GQ2
