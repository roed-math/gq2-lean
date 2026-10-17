/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
import GQ2.TauCeti.Main

/-!
# Axiom audit for the Tau Ceti route

This audit deliberately imports only `GQ2.TauCeti.Main`. It checks that the nine legacy
literature-axiom declarations and the axiom-backed `LiteratureInputs` instance are absent from the
imported environment, and that the four Tau Ceti capstones depend on exactly Lean's standard three
axioms. The literature inputs enter as theorems and constructions proved from Tau Ceti
(`GQ2/TauCeti/Instance.lean`), so Tau Ceti's own axioms are part of this check: any `sorryAx` or
non-standard axiom in Tau Ceti's proofs of them would show up here.
-/

open Lean

namespace GQ2.TauCetiAxiomAudit

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

def legacyCompatibilityProviders : List Name :=
  ["GQ2.axiomaticLiteratureInputs".toName]

def capstones : List Name :=
  [ ``GQ2.main_presentation_literal_tauceti
  , ``GQ2.main_presentation_literal_roe_tauceti
  , ``GQ2.main_surjection_count_tauceti
  , ``GQ2.main_surjection_count_R_tauceti ]

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let present := legacyLiteratureAxioms.filter env.contains
  unless present.isEmpty do
    throwError "Tau Ceti audit: legacy literature axioms entered the import closure: {present}"
  let presentProviders := legacyCompatibilityProviders.filter env.contains
  unless presentProviders.isEmpty do
    throwError "Tau Ceti audit: legacy compatibility provider entered the import closure: {presentProviders}"
  for n in capstones do
    unless env.contains n do
      throwError "Tau Ceti audit: missing capstone {n}"
    let axs ← collectAxioms n
    let unexpected := axs.filter fun a => !standardAxioms.contains a
    unless unexpected.isEmpty do
      throwError "Tau Ceti audit: {n} uses non-standard axioms: {unexpected}"
    let missing := standardAxioms.filter fun a => !axs.contains a
    unless missing.isEmpty do
      throwError "Tau Ceti audit: {n} prints fewer than the standard three (missing {missing}); \
        the audit expects exactly propext, Classical.choice, Quot.sound"
  IO.println "Tau Ceti axiom audit: legacy axioms absent; the four capstones use exactly the standard three"

end GQ2.TauCetiAxiomAudit
