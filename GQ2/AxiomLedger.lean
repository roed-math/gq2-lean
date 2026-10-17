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
`Quot.sound`), maps the literature axioms (`bAxioms`; **empty since the Tau Ceti discharge, ticket
C2, 2026-10-17**, when the nine former axioms became theorems proved from Tau Ceti and
`GQ2/Foundations/Axioms.lean` was deleted) to their B-labels, and reports:

* **legacy certificate** — which declarations consume each B-axiom.  With the compatibility
  instance, these uses are intentionally concentrated in the provider and legacy wrappers; field
  provenance for generic declarations is represented by their `LiteratureInputs` hypothesis.
* **explicit-input inventory** — a per-module count of declarations whose elaborated type mentions
  `LiteratureInputs`.  This makes accidental hypothesis propagation visible even though many
  proofs consume the class only transitively.
* **gap map** — declarations still depending on `sorryAx`.  **Currently empty, and expected to
  stay so**: the library is fully proved, and `scripts/check_axioms.sh`'s sorry allowlist is
  likewise empty (it last held the four `GQ2/Roe/Labute/` skeletons while the L-campaign was in
  flight, 2026-07-25 to 2026-07-26).  It fills only while a campaign's skeleton files are being
  filled, and even then no capstone may appear in it, which the terminal certificate below
  enforces.
* **alarm** — any *other* non-standard axiom.  Must be empty: a stray `axiom`, a `native_decide`
  (`Lean.ofReduceBool`), or a miscounted census would surface here.
* **terminal certificate** — the campaign capstones, *checked* rather than reported: each legacy
  capstone is free of `sorryAx` and of any axiom outside the census (now: outside the standard
  three) and matches its Γ_A/Γ_R twin; each explicit-input capstone and each Tau Ceti capstone
  (`GQ2/TauCeti/Main.lean`) uses only the standard three axioms.  Unlike the reports above, a
  violation here fails the command.

Unlike the textual guard `scripts/check_axioms.sh`, this walks the elaborated environment directly,
so it reports transitive dependencies and covers the whole library, including `private` lemmas.

## Re-run

    lake build GQ2 && lake env lean GQ2/AxiomLedger.lean

Prints the ledger to stdout.  This file is intentionally **not** imported by `GQ2.lean`, so it never
runs during `lake build GQ2`.  If the axiom census (currently zero) ever changes, update `bAxioms`
below (and `scripts/check_axioms.sh`'s `EXPECTED_AXIOMS`, same commit).
-/

open Lean

namespace GQ2.AxiomLedger

/-- The literature axioms and their B-labels.  **Empty since ticket C2 (2026-10-17):** the nine
former axioms (B1, B3c, B5, B6, B7, B8, B9, B10, B11a) are theorems/definitions proved from Tau Ceti
under their legacy names in `GQ2/Foundations/TauCetiInstance.lean`, so every consumer now reports
at the standard three, and any reappearing non-standard axiom lands in the ALARM section below. -/
def bAxioms : List (Name × String) := []

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

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

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

run_cmd do
  let env ← getEnv
  let bnames := bAxioms.map (·.1)
  let cands : Array (Name × Name) := env.constants.fold (init := #[]) fun acc n info =>
    if isTracked bnames n info && info.type.getUsedConstants.contains ``GQ2.LiteratureInputs then
      acc.push (moduleOf env n, privateToUserName n)
    else
      acc
  let cands := cands.qsort fun a b =>
    if a.1 == b.1 then a.2.toString < b.2.toString else a.1.toString < b.1.toString
  let mut out := s!"\n--- explicit LiteratureInputs inventory: {cands.size} declaration(s) ---\n"
  let mut previousModule : Option Name := none
  let mut moduleCount := 0
  let mut modules := 0
  for (modName, _) in cands do
    match previousModule with
    | none =>
        previousModule := some modName
        moduleCount := 1
    | some previous =>
        if previous == modName then
          moduleCount := moduleCount + 1
        else
          out := out ++ s!"{previous}: {moduleCount}\n"
          previousModule := some modName
          moduleCount := 1
          modules := modules + 1
  if let some previous := previousModule then
    out := out ++ s!"{previous}: {moduleCount}\n"
    modules := modules + 1
  out := out ++ s!"{modules} module(s) carry the hypothesis\n"
  IO.println out

/-! ### Terminal certificate

The three reports above are informational — they print what the library depends on.  This section
*checks* the campaign capstones and fails the command on a violation, so the capstones cannot
silently acquire a dependency between audits.  It is the environment-walking counterpart of check 5
in `scripts/check_axioms.sh`, and deliberately overlaps it: the script pins the exact expected axiom
set, this pins the properties that must hold whatever the census currently is.
-/

/-- The capstones the certificate compares as `(Γ_A twin, Γ_R twin)` pairs: the presentation
theorem's three layers — the literal profinite isomorphism, eq. (154), and the surjection-count
form — and then, against the same `Γ_A` theorem as the first row, the campaign's terminal
statement.

The `Γ_R` sides of the first three rows are hypothesis-parametrized by `BLabHypothesis` (the
Labute classification enters those capstones as an explicit binder, never as an axiom); a binder
contributes nothing to an axiom print, so the two sides of each pair are directly comparable.  The
fourth row carries no binder at all: `main_presentation_literal_roe_unconditional` is that
hypothesis *discharged*, by the theorem `GQ2.Roe.Labute.bLab` (L6, 2026-07-26).  Since both legacy
routes select the same `LiteratureInputs` instance (proved from Tau Ceti since ticket C2), twin
identity chiefly guards against a new off-census dependency in either wrapper; the explicit-input
certificate below is the stronger check on the generic proof terms. -/
def terminalPairs : List (Name × Name) :=
  [ (``GQ2.main_presentation_literal,         ``GQ2.main_presentation_literal_roe)
  , (``GQ2.SectionTen.eq_154,                 ``GQ2.eq_154_R)
  , (``GQ2.SectionTen.main_surjection_count', ``GQ2.main_surjection_count_R)
  , (``GQ2.main_presentation_literal,         ``GQ2.main_presentation_literal_roe_unconditional) ]

/-- `Γ_R`-side terminal declarations with no `Γ_A` twin to compare against: the bridge identifying
the two admissible-marking semantics (`admissibleCountR` vs `admissibleCount`). -/
def terminalSolo : List Name := [``GQ2.admissibleCountR_eq_admissibleCount]

/-- Explicit-hypothesis capstones.  Their literature dependencies occur in their theorem types as
the ordinary `[LiteratureInputs]` parameter, so their proof terms may use only the standard three
axioms. -/
def explicitInputTerminals : List Name :=
  [ ``GQ2.main_presentation_literal_of_inputs
  , ``GQ2.SectionTen.eq_154_of_inputs
  , ``GQ2.SectionTen.main_surjection_count_of_inputs
  , ``GQ2.eq_154_R_of_inputs
  , ``GQ2.main_surjection_count_R_of_inputs
  , ``GQ2.admissibleCountR_eq_admissibleCount_of_inputs
  , ``GQ2.main_presentation_literal_roe_of_inputs
  , ``GQ2.main_presentation_literal_roe_unconditional_of_inputs ]

run_cmd do
  let env ← getEnv
  let permitted := stdAxioms ++ bAxioms.map (·.1)
  let decls := terminalPairs.map (·.1) ++ terminalPairs.map (·.2) ++ terminalSolo
  let mut prints : Array (Name × Array Name) := #[]
  for n in decls do
    unless env.contains n do
      throwError "terminal certificate: unknown declaration {n} (renamed or removed?)"
    prints := prints.push (n, (← collectAxioms n).qsort (·.toString < ·.toString))
  let axiomsOf (n : Name) : Array Name := ((prints.find? (·.1 == n)).map (·.2)).getD #[]
  -- (i) no capstone may rest on a `sorry` or on anything outside the census …
  let mut bad : Array String := #[]
  for (n, axs) in prints do
    for a in axs do
      if a == `sorryAx then bad := bad.push s!"{n} depends on sorryAx"
      else unless permitted.contains a do bad := bad.push s!"{n} uses non-census axiom {a}"
  -- … and (ii) the Roe campaign may not widen the trust base of the theorem it replaces.
  for (a, r) in terminalPairs do
    unless axiomsOf a == axiomsOf r do
      bad := bad.push s!"{r} does not depend on the same axioms as its twin {a}"
  let mut out := "\n--- terminal certificate ---\n"
  for (a, r) in terminalPairs do
    let verdict := if axiomsOf a == axiomsOf r then "identical to twin" else "DIFFERS FROM TWIN"
    out := out ++ s!"{r}\n    {verdict} {a} ({(axiomsOf r).size} axioms)\n"
  for n in terminalSolo do
    out := out ++ s!"{n}\n    {(axiomsOf n).size} axioms, all in the census\n"
  out := out ++ s!"\n{bad.size} terminal violation(s) (must be 0)\n"
  IO.println out
  unless bad.isEmpty do
    let badMsg := String.intercalate "\n  " bad.toList
    throwError "terminal certificate FAILED:\n  {badMsg}"

/-- The capstones instantiated at the Tau Ceti literature bundle (`GQ2/TauCeti/Main.lean`, ticket
C1); like the explicit-input ones they must use only the standard three axioms. -/
def tauCetiTerminals : List Name :=
  [ ``GQ2.main_presentation_literal_tauceti
  , ``GQ2.main_presentation_literal_roe_tauceti
  , ``GQ2.main_surjection_count_tauceti
  , ``GQ2.main_surjection_count_R_tauceti ]

run_cmd do
  let env ← getEnv
  let mut bad : Array String := #[]
  for n in explicitInputTerminals ++ tauCetiTerminals do
    unless env.contains n do
      bad := bad.push s!"unknown explicit-input declaration {n}"
      continue
    let axs ← collectAxioms n
    for a in axs do
      unless stdAxioms.contains a do
        bad := bad.push s!"{n} uses non-standard axiom {a}"
  IO.println s!"\n--- explicit-input and Tau Ceti certificate ---\n{explicitInputTerminals.length + tauCetiTerminals.length} capstones checked; {bad.size} violation(s) (must be 0)"
  unless bad.isEmpty do
    let badMsg := String.intercalate "\n  " bad.toList
    throwError "explicit-input certificate FAILED:\n  {badMsg}"

end GQ2.AxiomLedger

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Prop 1.1 = ⟦prop-markedDem⟧
  * Prop 3.2 = ⟦prop-tamequotient⟧
  * Thm 4.2 = ⟦thm-fixedframe⟧
-/
