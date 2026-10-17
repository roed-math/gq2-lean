/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
import GQ2.Dyadic.GeneralMain
import GQ2.Foundations.TauCetiInstance

/-!
# Axiom audit for the dyadic Tau Ceti route (ticket C1')

Companion of `GQ2/TauCetiAxiomAudit.lean` for the `dyadic` branch.  Since ticket C1' of
`docs/dyadic/tauceti-discharge-plan.md` the two `K`-level inputs `GQ2.markedRecipAt` (B5-K) and
`GQ2.orientedTameQuotientAt` (B10-K) are definitions in `GQ2/Foundations/TauCetiInstance.lean` whose
bodies are the adapters `GQ2/TauCeti/B5K.lean` and `GQ2/TauCeti/B10K.lean`.  This file checks, in
the environment of the whole dyadic tree, that they and the W361 endpoint
`GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI` depend on exactly Lean's
standard three axioms, and that the environment contains no axiom constant in the `GQ2`
namespace (the textual census of `scripts/check_axioms.sh` check 1/3, re-checked on the elaborated
environment; Lean core's own axiom constants — `sorryAx`, the compiler's `lc*` constants, … — are
outside `GQ2` and their *uses* are policed separately).  Run by `scripts/check_axioms.sh` check 8.
-/

open Lean

namespace GQ2.DyadicTauCetiAxiomAudit

def endpoints : List Name :=
  [ ``GQ2.markedRecipAt
  , ``GQ2.orientedTameQuotientAt
  , ``GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical.exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI ]

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  for n in endpoints do
    unless env.contains n do
      throwError "dyadic Tau Ceti audit: missing endpoint {n}"
    let axs ← collectAxioms n
    let unexpected := axs.filter fun a => !standardAxioms.contains a
    unless unexpected.isEmpty do
      throwError "dyadic Tau Ceti audit: {n} uses non-standard axioms: {unexpected}"
    let missing := standardAxioms.filter fun a => !axs.contains a
    unless missing.isEmpty do
      throwError "dyadic Tau Ceti audit: {n} prints fewer than the standard three (missing {missing})"
  let stray := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    match ci with
    | .axiomInfo _ => if n.getRoot == `GQ2 then acc.push n else acc
    | _ => acc
  unless stray.isEmpty do
    throwError "dyadic Tau Ceti audit: axiom constants in the GQ2 namespace: {stray}"
  IO.println "dyadic Tau Ceti axiom audit: K-level inputs and the W361 endpoint at exactly the standard three; no GQ2 axiom constant"

end GQ2.DyadicTauCetiAxiomAudit
