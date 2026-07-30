/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5

Statement-closure probe for the nine literature axioms.

For each axiom in `GQ2/Foundations/Axioms.lean` this computes the transitive set of
GQ2-project constants a reader must understand to know *what the axiom asserts*: starting
from the constants of the axiom's type, it recurses through definition values and structure
constructor types, but through theorems it recurses into the *statement only* — proof terms
are machine-checked and are pruned, following the Lean-Compass review model (`docs/atlas.md`).

Output: one JSON document on stdout, rendered to `docs/axiom-closure.md` by
`scripts/axiom_closure.py`.  Driver: `scripts/axiom_closure.sh` (run that; it needs a built
`GQ2.Foundations.Axioms`).
-/
import GQ2.Foundations.Axioms

open Lean

/-- The ten census axioms, in `GQ2/Foundations/Axioms.lean` order. -/
def censusAxioms : List Name := [
  `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated,
  `GQ2.Foundations.absGalQ2_localEulerCharacteristic,
  `GQ2.dyadicOrientation,
  `GQ2.localReciprocity,
  `GQ2.markedRecipAt,
  `GQ2.tateDualityAt,
  `GQ2.peripheralCyclotomicAction,
  `GQ2.relativeStiefelWhitney_dyadic,
  `GQ2.tameQuotient,
  `GQ2.hilbertSymbol_normCriterion_finiteDyadic]

def moduleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

def isGQ2 (env : Environment) (c : Name) : Bool :=
  (moduleOf env c).getRoot == `GQ2

/-- Auxiliaries that carry no independent review content: compiler-generated details,
structure eliminators/constructors (their content is reported through the structure itself),
and projection functions (reported through their structure). -/
def skipReport (env : Environment) (c : Name) : Bool :=
  c.isInternalDetail ||
  (env.getProjectionFnInfo? c).isSome ||
  (match env.find? c with | some (.ctorInfo _) => true | _ => false) ||
  [`rec, `recOn, `casesOn, `brecOn, `below, `ibelow, `noConfusion, `noConfusionType,
   `injEq, `sizeOf_spec, `mk].any (fun s => c.components.getLast? == some s)

/-- The constants to recurse into from `c`: always the type; for definitions also the value;
for inductives/structures also the constructor types (this is where structure fields live).
Theorem and axiom *proofs* are never traversed. -/
def constsToVisit (env : Environment) (c : Name) : Array Name := Id.run do
  let some ci := env.find? c | return #[]
  let mut es : Array Expr := #[ci.type]
  match ci with
  | .defnInfo v => es := es.push v.value
  | .inductInfo v =>
      for ctor in v.ctors do
        if let some cci := env.find? ctor then es := es.push cci.type
  | _ => pure ()
  let mut out : Array Name := #[]
  for e in es do
    out := out ++ e.getUsedConstants
  return out

/-- Transitive GQ2-constant closure of the statement of `root` (the root itself excluded). -/
partial def statementClosure (env : Environment) (root : Name) : List Name := Id.run do
  let mut visited : NameSet := {}
  let mut report : NameSet := {}
  let mut stack : Array Name := (env.find? root).map (·.type.getUsedConstants) |>.getD #[]
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if visited.contains c then
      continue
    visited := visited.insert c
    unless isGQ2 env c do
      continue
    unless skipReport env c do
      report := report.insert c
    stack := stack ++ constsToVisit env c
  return report.toList

def kindOf (env : Environment) (c : Name) : String :=
  match env.find? c with
  | some (.defnInfo _) => if isStructure env c then "structure" else "def"
  | some (.thmInfo _) => "theorem"
  | some (.axiomInfo _) => "axiom"
  | some (.inductInfo _) => if isStructure env c then "structure" else "inductive"
  | some (.opaqueInfo _) => "opaque"
  | some (.ctorInfo _) => "ctor"
  | _ => "?"

open Elab Command in
run_cmd do
  let env ← getEnv
  let mut axEntries : Array Json := #[]
  for ax in censusAxioms do
    unless env.contains ax do
      throwError "axiom closure probe: unknown declaration {ax}"
    let direct := ((env.find? ax).map (·.type.getUsedConstants) |>.getD #[]).toList.eraseDups
      |>.filter (fun c => isGQ2 env c && !skipReport env c)
    let closure := statementClosure env ax
    let mut entries : Array Json := #[]
    for c in (closure.toArray.qsort (fun a b => a.toString < b.toString)) do
      let doc ← findDocString? env c
      let docLine := (doc.map (fun s => ((s.splitOn "\n").headD "" |>.take 240).toString)).getD ""
      entries := entries.push <| Json.mkObj [
        ("name", Json.str c.toString),
        ("module", Json.str (moduleOf env c).toString),
        ("kind", Json.str (kindOf env c)),
        ("doc", Json.str docLine)]
    axEntries := axEntries.push <| Json.mkObj [
      ("axiom", Json.str ax.toString),
      ("module", Json.str (moduleOf env ax).toString),
      ("direct", Json.arr (direct.toArray.map (fun c => Json.str c.toString))),
      ("closure", Json.arr entries)]
  IO.println (Json.mkObj [("axioms", Json.arr axEntries)]).compress
