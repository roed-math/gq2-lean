/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2

/-!
# Repo-wide axiom ledger

A batch `#print axioms` over **every** declaration under the `GQ2` namespace — the App. D
*certificate check*, done repo-wide rather than per-session.  For each theorem/def it collects the
axioms it transitively depends on, drops the standard three (`propext`, `Classical.choice`,
`Quot.sound`), maps the nine literature axioms (`GQ2/Foundations/Axioms.lean`) to their
B-labels, and reports:

* **certificate** — which declarations consume each B-axiom.  Compare this with the App. D rows in
  `docs/literature-axioms.md` §C.
* **gap map** — declarations still depending on `sorryAx`; this is expected to be empty.
* **alarm** — any *other* non-standard axiom.  Must be empty: a stray `axiom`, a `native_decide`
  (`Lean.ofReduceBool`), or a miscounted census would surface here.

Unlike the textual guard `scripts/check_axioms.sh`, this walks the elaborated environment directly,
so it reports transitive dependencies and covers the whole library, including `private` lemmas.

## Re-run

    lake build GQ2 && lake env lean GQ2/AxiomLedger.lean

Prints the ledger to stdout.  This file is intentionally **not** imported by `GQ2.lean`, so it never
runs during `lake build GQ2`.  If the axiom census (currently nine) ever changes, update `bAxioms`
below (and `scripts/check_axioms.sh`'s `EXPECTED_AXIOMS`, same commit).
-/

open Lean

namespace GQ2.AxiomLedger

/-- The nine literature axioms and their B-labels; see `GQ2/Foundations/Axioms.lean` for their
statements, citations, and encoding notes.  The quoted names make this file fail to compile if an
axiom is renamed or removed, keeping the ledger synchronized with the declarations it audits. -/
def bAxioms : List (Name × String) :=
  [ (``GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated, "B1")
  , (``GQ2.dyadicOrientation,                                     "B3c")
  , (``GQ2.localReciprocity,                                      "B5")
  , (``GQ2.tateDualityAt,                                         "B6")
  , (``GQ2.Foundations.absGalQ2_localEulerCharacteristic,         "B7")
  , (``GQ2.peripheralCyclotomicAction,                            "B8")
  , (``GQ2.evensKahn_dyadic,                                      "B9")
  , (``GQ2.tameQuotient,                                          "B10")
  , (``GQ2.hilbertSymbol_normCriterion_finiteDyadic,              "B11a") ]

/-- The three axioms every classical theorem is allowed to use. -/
def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- A theorem or definition whose user-facing name lies under `GQ2` (skips auto-generated
`_proof`/`match`/`eq` internals and the axioms themselves).  Lean stores a private declaration under
an internal `_private.<module>.0...` name, so normalize it before applying the namespace and
generated-name filters. -/
def isTracked (bnames : List Name) (n : Name) (info : ConstantInfo) : Bool :=
  let userName := privateToUserName n
  (`GQ2).isPrefixOf userName && !userName.isInternalDetail && !(bnames.contains n) &&
    (match info with | .thmInfo _ | .defnInfo _ => true | _ => false)

/-- Regression fixture for private-declaration coverage in `isTracked`. -/
private theorem privateTrackingRegression : True := True.intro

run_cmd do
  let env ← getEnv
  let bnames := bAxioms.map (·.1)
  let known := `sorryAx :: bnames
  -- collect (decl, its non-standard axioms) for every tracked declaration
  let cands : Array Name := env.constants.fold (init := #[]) fun acc n info =>
    if isTracked bnames n info then acc.push n else acc
  unless cands.contains ``privateTrackingRegression do
    throwError "axiom ledger regression: private declarations are not being tracked"
  let mut results : Array (Name × Array Name) := #[]
  let mut std3 := 0
  for n in cands do
    let nonStd := (← collectAxioms n).filter (fun a => !stdAxioms.contains a)
    if nonStd.isEmpty then std3 := std3 + 1 else results := results.push (n, nonStd)
  let byName (a : Array Name) : Array Name := a.qsort (·.toString < ·.toString)
  -- report
  let mut out := "\n=== GQ2 axiom ledger ===\n"
  out := out ++ s!"scanned {cands.size} tracked declarations under `GQ2` (theorems + defs)\n"
  out := out ++ s!"  {std3} at the standard three axioms only\n"
  out := out ++ s!"  {results.size} carry non-standard axioms (detailed below)\n"
  out := out ++ "\n--- certificate: consumers by B-axiom ---\n"
  for (axName, label) in bAxioms do
    let cs := byName <| results.filterMap fun (n, axs) => if axs.contains axName then some n else none
    out := out ++ s!"{label}  ({axName}) — {cs.size} consumer(s)\n"
    for c in cs do out := out ++ s!"    {c}\n"
  let sorryDecls := byName <| results.filterMap fun (n, axs) =>
    if axs.contains `sorryAx then some n else none
  out := out ++ s!"\n--- gap map: {sorryDecls.size} declaration(s) depend on `sorryAx` ---\n"
  for n in sorryDecls do out := out ++ s!"    {n}\n"
  let alarms := results.flatMap fun (n, axs) =>
    axs.filterMap fun a => if known.contains a then none else some s!"{n}  uses  {a}"
  out := out ++ s!"\n--- ALARM: {alarms.size} unknown non-standard axiom use(s) (must be 0) ---\n"
  for a in alarms.qsort (· < ·) do out := out ++ s!"    {a}\n"
  IO.println out

end GQ2.AxiomLedger

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Prop 1.1 = ⟦prop-markedDem⟧
  * Prop 3.2 = ⟦prop-tamequotient⟧
  * Thm 4.2 = ⟦thm-fixedframe⟧
-/
