import GQ2

/-!
# Repo-wide axiom ledger  (ticket P-01)

A batch `#print axioms` over **every** declaration under the `GQ2` namespace — the App. D
*certificate check*, done repo-wide rather than per-session.  For each theorem/def it collects the
axioms it transitively depends on, drops the standard three (`propext`, `Classical.choice`,
`Quot.sound`), maps the twelve literature axioms (`GQ2/Foundations/Axioms.lean`) to their
B-labels, and reports:

* **certificate** — which declarations consume each B-axiom.  Diff this against the per-ticket `Ax`
  column in `docs/tickets.md` and the App. D rows in `docs/literature-axioms.md` §C (Prop 1.1 →
  `B3c,B4,B5,B7′`; Prop 3.2 → `B5`; Thm 4.2 → `B6,B7,B7′,B8,B9`; each proof ticket declares its
  allowed B-set).
* **gap map** — declarations still depending on `sorryAx` (the intentional open leaves; shrinks as
  proof tickets land, empty at step-2 end).
* **alarm** — any *other* non-standard axiom.  Must be empty: a stray `axiom`, a `native_decide`
  (`Lean.ofReduceBool`), or a miscounted census would surface here.

Unlike `.claude/tools/lean4/check_axioms.sh` (which cannot see namespaced/`private` decls — all of
ours are under `namespace GQ2`), this walks the elaborated environment directly, so it covers the
whole library including `private` lemmas.

## Re-run

    lake build GQ2 && lake env lean GQ2/AxiomLedger.lean

Prints the ledger to stdout.  This file is intentionally **not** imported by `GQ2.lean`, so it never
runs during `lake build GQ2`.  If the axiom census (currently 11) ever changes, update `bAxioms`
below (and `scripts/check_axioms.sh`'s `EXPECTED_AXIOMS`, same commit).
-/

open Lean

namespace GQ2.AxiomLedger

/-- The ten literature axioms → their B-labels (census 10 after the B10, B9′/B11, P-23
B11-split, P-15f1 B12/B13-addition, and 2026-07-09 B12/B7′/B13/B11b-discharge/B2-deletion census
decisions; see `GQ2/Foundations/Axioms.lean`).  Written with `` `` `` so the
file fails to compile if any axiom is renamed or removed — a free consistency check on the census.
(`dyadicNormCriterion` is a same-name *theorem*, since 2026-07-09 over **B11a alone** (its
`unramifiedQuadratic_units_are_norms` component — the former **B11b** — is now a same-name
*theorem* over the std-3 proof in `GQ2/UnramifiedQuadraticNorms.lean`, so it is absent here and
surfaces as a std-3 tracked declaration).  `kummerClassK_surjective` — the
former **B12** — is since 2026-07-09 a same-name *theorem* over the std-3 proof in
`GQ2/KummerSurjectivity.lean`, so it is absent too and surfaces as a std-3 tracked declaration.
`hilbertSymbol_dyadic` — the former **B7′** — is likewise since 2026-07-09 a same-name *theorem*
over the std-3 proof in `GQ2/HilbertSymbolDyadicClose.lean`.  `dyadicUnitFiltration` — the former
**B13** — is since 2026-07-09 a same-name *`noncomputable def`* over the std-3 proof in
`GQ2/UnitFiltrationCounts.lean` (built on `GQ2/UnitFiltrationTop.lean`), so it too is absent here
and surfaces as a std-3 tracked declaration.
The former **B2** `cyclotomicCharacter_two_surjective` was deleted the same day, unused.)

Citation-faithfulness tiers (adversarial review 2026-07-04; docstrings + `docs/review-packet.md`
§2): **direct** B1/B6/B7/B10 (B7′ until its discharge) · **classical + encoding** B5/B9
(B4 until its 2026-07-10 deletion, unused) ·
**composite interface** B3c/B8/B11a/B11b.  (B13, which postdated the review
[`docs/p15f1-axiom-proposal.md`], was discharged in-repo 2026-07-09 — B13 board.) -/
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

/-- A user-facing theorem or def under the `GQ2` namespace (skips auto-generated
`_proof`/`match`/`eq` internals and the axioms themselves). -/
def isTracked (bnames : List Name) (n : Name) (info : ConstantInfo) : Bool :=
  (`GQ2).isPrefixOf n && !n.isInternalDetail && !(bnames.contains n) &&
    (match info with | .thmInfo _ | .defnInfo _ => true | _ => false)

run_cmd do
  let env ← getEnv
  let bnames := bAxioms.map (·.1)
  let known := `sorryAx :: bnames
  -- collect (decl, its non-standard axioms) for every tracked declaration
  let cands : Array Name := env.constants.fold (init := #[]) fun acc n info =>
    if isTracked bnames n info then acc.push n else acc
  let mut results : Array (Name × Array Name) := #[]
  let mut std3 := 0
  for n in cands do
    let nonStd := (← collectAxioms n).filter (fun a => !stdAxioms.contains a)
    if nonStd.isEmpty then std3 := std3 + 1 else results := results.push (n, nonStd)
  let byName (a : Array Name) : Array Name := a.qsort (·.toString < ·.toString)
  -- report
  let mut out := "\n=== GQ2 axiom ledger (ticket P-01) ===\n"
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
