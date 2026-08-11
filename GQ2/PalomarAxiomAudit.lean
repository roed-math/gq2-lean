/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8, Fable-5, and OpenAI Codex
-/
import SolutionPalomar

/-!
# Axiom audit for the explicit-hypothesis route

This audit deliberately imports only the Palomar solution.  It checks both that the legacy
literature-axiom declarations are absent from the imported environment and that the two exported
solutions depend on no axioms beyond Lean's standard three.  `LiteratureInputs` contributes an
ordinary typeclass parameter, not an axiom.
-/

open Lean

namespace GQ2.PalomarAxiomAudit

def legacyLiteratureAxioms : List Name :=
  [ "GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated".toName
  , "GQ2.Foundations.absGalQ2_localEulerCharacteristic".toName
  , "GQ2.dyadicOrientation".toName
  , "GQ2.localReciprocity".toName
  , "GQ2.tateDualityAt".toName
  , "GQ2.peripheralCyclotomicAction".toName
  , "GQ2.relativeStiefelWhitney_dyadic".toName
  , "GQ2.tameQuotient".toName
  , "GQ2.hilbertSymbol_normCriterion_finiteDyadic".toName ]

def solutionDeclarations : List Name :=
  [ ``challenge_main_presentation_literal_of_inputs
  , ``challenge_main_presentation_literal_roe_unconditional_of_inputs ]

def permittedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let present := legacyLiteratureAxioms.filter env.contains
  unless present.isEmpty do
    throwError "Palomar audit: legacy literature axioms entered the import closure: {present}"
  for n in solutionDeclarations do
    unless env.contains n do
      throwError "Palomar audit: missing solution declaration {n}"
    let axs ← collectAxioms n
    let unexpected := axs.filter fun a => !permittedAxioms.contains a
    unless unexpected.isEmpty do
      throwError "Palomar audit: {n} uses non-standard axioms: {unexpected}"
  IO.println "Palomar axiom audit: legacy axioms absent; both solutions use only the standard three"

end GQ2.PalomarAxiomAudit
