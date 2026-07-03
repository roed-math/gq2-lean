# Orbit-data refactor — ready-to-execute plan (unblocks the P-15 own-file splices)

## Why

Every P-15 own-file that *proves* a §6 orbit lemma (P-15c `ShapiroLedger`, P-15d
`RepIndependence`, …) imports `GQ2/SectionSix.lean` to reach the factor-set / orbit-data
**defs** (`FactorSet`, `graphPullback`, `RegRep`, `*OrbitDatum`, …).  So the intended
one-line splice back into `SectionSix` —

```lean
theorem lemma_6_15_free … := ShapiroLedger.lemma_6_15_free_aux …
```

— is a **circular import** (`SectionSix` would import `ShapiroLedger` which imports
`SectionSix`).  This blocks *every* P-15 own-file's splice, so their proved `_aux` lemmas sit
unconsumed and `SectionSix`'s statement `sorry`s remain.

The fix: move the orbit-data def-layer **down** into a new shared file both `SectionSix` and the
own-files import.  Then the own-files import the def-layer (not `SectionSix`), the cycle is
gone, and `SectionSix` can import the own-files and splice.

## Blocked until `SectionSix` is quiescent

This is a **structural edit of the hot co-owned `SectionSix`** (delete ~55 lines of stable
defs; add 2 imports + the splices).  It must be done when `SectionSix` has **no uncommitted
parallel work** (as of 2026-07-04 it had 43 uncommitted lines from parallel P-15 proof sessions
+ the dependent uncommitted `RepIndependence`).  Doing it mid-parallel would race/clobber those
sessions' work in the single shared worktree.  Execute this as a single focused commit once the
board shows the §6 proof sub-tickets committed.

## Step 1 — create `GQ2/OrbitData.lean`

Move these defs **verbatim** out of `SectionSix` into a new `GQ2/OrbitData.lean`, in the
**top-level `namespace GQ2`** (not `GQ2.SectionSix`) — this is the key that avoids editing the
own-files (see Step 3).

Imports: `import GQ2.QuadraticFp2` (provides `polar`, used by `IsEquivariantFactorSet`).  That
is all the def-layer needs (the defs are raw functions / structures over `ZMod 2`, `G ⧸ N`,
`finsum`; no cohomology).

Defs to move (current `SectionSix` line ranges):

| def | lines | note |
|---|---|---|
| `FactorSet` (structure) | 129–134 | `variable (C V) [Group C] [AddCommGroup V] [DistribMulAction C V]` |
| `IsEquivariantFactorSet` | 140–157 | uses `polar q` |
| `kappa0` | 161–162 | |
| `graphPullback` | 167–169 | |
| `FactorSet.comap` | 173–176 | |
| `RegRep` + `AddCommGroup`/`DistribMulAction` instances | 586–596 | `variable (N : Subgroup G) [N.Normal]` |
| `squareOrbitDatum` | 599–601 | |
| `freeOrbitDatum` | 605–607 | |
| `invOrbitDatum` | 613–618 | `open scoped Classical` for the `if` in `.m` |

Carry the two `variable` blocks (the `FactorSets` one and the `Shapiro`/`RegRep` one).  Keep
`open scoped Classical` in `OrbitData` for `invOrbitDatum`.

## Step 2 — edit `SectionSix`

* Add `import GQ2.OrbitData` (near the top) and `import GQ2.ShapiroLedger` (+ the other P-15
  own-files as their splices are wired: `RepIndependence`, …).
* **Delete** the moved defs (the rows above).  Everything else in `SectionSix` keeps referring
  to `graphPullback`/`FactorSet`/`RegRep`/… **unqualified** — since `SectionSix` is in
  `namespace GQ2` and the defs are now `GQ2.graphPullback` etc., the unqualified names still
  resolve.  (`open SectionSix` is no longer needed for them; nothing else changes.)
* Splice the proved own-file lemmas, e.g.
  `lemma_6_15_free … := ShapiroLedger.lemma_6_15_free_aux N hNo α β ghat`
  (proof irrelevance handles the `⟨…, by simpa …⟩` membership term).  Do the same for any
  other §6 lemma whose `_aux` lands (6.14 from `RepIndependence`, …).
* Remove the now-discharged files from `SORRY_ALLOWLIST` in `scripts/check_axioms.sh` **only
  when a file's last §6 sorry is gone** (the involution `sorry` keeps `SectionSix` allowlisted
  until P-15c's 105 lands too).

## Step 3 — own-files need **no edit** (the top-level-namespace trick)

`RepIndependence` is `namespace GQ2` + `open … SectionSix` and uses `graphPullback`, `kappa0`,
`FactorSet`, `IsEquivariantFactorSet` **unqualified**.  After the move to `namespace GQ2`, those
resolve to `GQ2.graphPullback` etc. (visible because `RepIndependence` is in `namespace GQ2`),
and they're available transitively (`RepIndependence` → `SectionSix` → `OrbitData`).  So
**leave the own-files untouched** — they keep importing `SectionSix` and Just Work.  (If any
own-file used a `SectionSix.`-qualified name for a moved def, change that one reference to
unqualified; none did as of 2026-07-04.)

`ShapiroLedger` (this session's own file) is the one exception worth switching now-ish, because
it is the file being spliced *into* `SectionSix`: change its `import GQ2.SectionSix` →
`import GQ2.OrbitData` + `import GQ2.Corestriction`, and drop `SectionSix` from its `open` list
(the orbit-data names then resolve to `GQ2.*`, and `lTrans`/`cor2Fun`/`H2ofFun` come from
`Corestriction`, `Z1`/`Z2`/`B2` from `Cohomology` which `Corestriction` re-exports).

## Step 4 — verify

`lake build GQ2` green; `scripts/check_axioms.sh` green (census 12); `#print axioms` of the
spliced `SectionSix` lemmas = std-3 for the free case (the `_aux` is std-3).  The whole point:
`SectionSix.lemma_6_15_free` loses its `sorry`.

## Net effect

`ShapiroLedger.lemma_6_15_free_aux` (proved, std-3) becomes `SectionSix.lemma_6_15_free`
(sorry removed), and the same wiring is ready for `RepIndependence`'s 6.14 and every other P-15
own-file — one shared refactor unblocks them all.
