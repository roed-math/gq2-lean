/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8, Fable-5, and OpenAI Codex
-/
import GQ2.PresentationLiteralWithInputs
import GQ2.Roe.MainWithInputs

/-!
# Axiom-free Comparator solution

Both results use only their explicit `LiteratureInputs` hypothesis and Lean's standard axioms.
Neither this module nor its import closure contains `GQ2.Foundations.Axioms`.
-/

open GQ2 in
/-- Theorem 1.2 from explicit literature inputs. -/
theorem challenge_main_presentation_literal_of_inputs [lit : LiteratureInputs] :
    Nonempty (ContinuousMulEquiv GammaA AbsGalQ2) :=
  GQ2.main_presentation_literal_of_inputs

open GQ2 in
/-- The unconditional Replacement theorem from explicit literature inputs. -/
theorem challenge_main_presentation_literal_roe_unconditional_of_inputs [lit : LiteratureInputs] :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  GQ2.main_presentation_literal_roe_unconditional_of_inputs
