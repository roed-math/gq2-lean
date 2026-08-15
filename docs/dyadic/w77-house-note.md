# W77-HOUSE: the disputed count-audit adjudicated, the genuine audit items, and watch round 14

Lane `claude/w77-house`, base `1d3d5a84`, cache at umbrella 4346 jobs green.
Verification of record: `scripts/mirror.sh` (`sweep`, `check`).  No `lake` command was run.

## Headline

**Ticket 1.  The quarantine was right and both HIGH claims are refuted.**  The disputed audit's
two figures, **325** for `GQ2.Dyadic.Main`'s closure and **19** unreachable modules, are *exactly*
what a plain `^import ` grep returns at this tree.  They are the wave-72 method trap reproduced
line for line: the 18 modules the audit names beyond `AxiomLedger` are the *same 18* that
`w72-house-note.md` §1.0 already records as its own first pass's spurious hits.  With the regex of
record the closure is **427** and the unreachable set is **{`GQ2.AxiomLedger`}**, at `4fff1592`
and at `1d3d5a84` alike.  **No NuSeeds-class finding.**  All 18 named modules are reachable, and
§1.3 shows the `public import` line that reaches each.

**Ticket 2.**  `GeneralAssembly.lean`'s 34 pins are now recorded in-file and all 34 print
`Classical.choice, Lean.trustCompiler, Quot.sound` (std-3, no campaign axiom).  The LamFrames
citation repair is applied at both shipped sites, and the wave-75 finding that produced it is
annotated as wrong at its source: `:300` is a `variable` line and `:301` is the *first* line of
the cleared-`u` docstring, not the second.  Of the six note-level items, **five applied, one
declined** (the `:1190` double-citation is not a defect).

**Ticket 3.  Staleness first, as the wave-76 process change requires.**  Two of the three wave-76
notes are overtaken by this wave's own siblings; the W76-BASE note's §4 falseness argument is
labelled as prose at its head but **not** at its two interior restatements, and one `GradedJoinBase`
docstring lets `GBaseResidual` read as refuted.  No identity headline over a containment in either
new module.

---

## Ticket 1: the disputed count-audit, adjudicated

### 1.0  Method, stated in full so it can be checked

The tree uses the Lean module system.  Aggregators re-export their parts with `public import`, so
the regex of record (`docs/dyadic/w72-house-note.md` §1.0) is

```text
^(?:public\s+|private\s+|meta\s+)*import(?:\s+all)?\s+([A-Za-z0-9_.]+)\s*$
```

I walked the graph over every `.lean` file at `GQ2.lean` or under `GQ2/`, mapping path to module
name, twice: once with that regex and once with a bare `^import\s+([A-Za-z0-9_.]+)\s*$`, so that
the disputed figures could be reproduced rather than merely contradicted.  Trees examined:
`4fff1592` (the audit's stated tree), `f0a71688` (the wave-75 base, for the third data point) and
`1d3d5a84` (this lane's base).  The two older trees were materialised with `git archive`, so the
walk never saw a working-tree edit.

### 1.1  The figures

| tree | `.lean` under `GQ2/` | incl. root | import lines, correct regex | plain `^import` | dropped |
|---|---|---|---|---|---|
| `4fff1592` | 929 | 930 | 3197 | 2611 | **586** |
| `f0a71688` | 932 | 933 | 3209 | 2623 | **586** |
| `1d3d5a84` | 936 | 937 | 3225 | 2639 | **586** |

| tree | Main closure, correct | Main closure, plain | unreachable, correct | unreachable, plain |
|---|---|---|---|---|
| `4fff1592` | **427** | 325 | **1** | 19 |
| `f0a71688` | 427 | 325 | **1** | 19 |
| `1d3d5a84` | **427** | 325 | **1** | 19 |

**Claim (a) is refuted.**  `GQ2.Dyadic.Main`'s transitive closure is **427**, not 325.  The
recorded figure was right.  325 is reproduced exactly by the plain grep, at all three trees.

**Claim (b) is refuted.**  Exactly **one** module is unreachable from `GQ2.lean`, namely
`GQ2.AxiomLedger`, which is deliberately excluded and must stay so.  19 is reproduced exactly by
the plain grep, at all three trees, and its extra 18 are the audit's 18 by name.

The invariant that makes the diagnosis certain: **586** import lines are dropped by the plain
regex at every one of the three trees, and 3225 - 2639 = 586 at this tree.  The audit's own
method note nowhere mentions `public import`.

### 1.2  Why 427 did not move while the tree grew by seven

Between `4fff1592` and `1d3d5a84` the tree gained seven modules and lost none:
`Dyadic/GeneralAssembly.lean`, `Dyadic/GeneralCertificates.lean`,
`Dyadic/Instances/EvenStratumRowFrame.lean`, `Dyadic/SqCore/GradedDeltaFunctionals.lean`,
`Dyadic/SqCore/GradedJoinBase.lean`, `Dyadic/SqCore/GradedUniformJoin.lean`,
`Dyadic/SqCore/GradedUniformTower.lean`.

The two closures are not merely equinumerous, they are the **same set**: `comm` of the sorted
closures at the two trees is empty in both directions.  Every one of the seven is reached from the
root `GQ2.lean` and from nowhere else outside its own family, so none enters `GQ2.Dyadic.Main`'s
closure.  This is a structural fact worth recording on its own: **`GQ2.Dyadic.Main` has not been
the aggregator for a landing in three waves**; `GQ2.lean` is.  Anyone using "in Main's closure" as
a proxy for "in the build" will be wrong about every wave-74-to-76 landing.

### 1.3  The 18 named modules are all reachable

Not one is a NuSeeds-class finding.  The reaching import line, one per module, all `public`:

| module | reached by |
|---|---|
| `GQ2.DeepCount.Bounds` | `GQ2/DeepCount.lean:9`, `GQ2/DeepCount/Transport.lean:8` |
| `GQ2.DeepCount.Finale` | `GQ2/DeepCount.lean:11` |
| `GQ2.DeepCount.Transport` | `GQ2/DeepCount.lean:10`, `GQ2/DeepCount/Finale.lean:8` |
| `GQ2.DevissageInduction` | `GQ2/DualityAssembly.lean:11`, `GQ2/CohomologyDevissage.lean:9`, `GQ2/Dyadic/Word/Stokes.lean:10` |
| `GQ2.EvensKahnDerived` | `GQ2/Foundations/Interfaces.lean:15` |
| `GQ2.GaussCount.Sign` | `GQ2/GaussCount.lean:9` |
| `GQ2.GaussCount.Wall` | `GQ2/GaussCount.lean:8`, `GQ2/GaussCount/Sign.lean:8`, `GQ2/Dyadic/Word/Phase.lean:8` |
| `GQ2.MixedBilinear` | `GQ2/TrivialSelfDual.lean:14`, `GQ2/Roe/FoxBasic.lean:9`, `GQ2/Devissage/Naturality.lean:9` |
| `GQ2.RamifiedPack.Basic` | `GQ2/RamifiedPack.lean:9`, `GQ2/RamifiedPack/Descent.lean:8` |
| `GQ2.RamifiedPack.Descent` | `GQ2/RamifiedPack.lean:10` |
| `GQ2.RegularSummand.Freeness` | `GQ2/RegularSummand.lean:9`, `GQ2/RegularSummand/Involution.lean:8` |
| `GQ2.RegularSummand.Involution` | `GQ2/RegularSummand.lean:10`, `GQ2/Dyadic/Projectivity.lean:8` |
| `GQ2.RegularSummand.Lifting` | `GQ2/RegularSummand.lean:11` |
| `GQ2.RegularSummand.Trace` | `GQ2/RegularSummand.lean:8`, `GQ2/RegularSummand/Freeness.lean:8` |
| `GQ2.Shapiro.Ledger.Involution` | `GQ2/Shapiro/Ledger.lean:9` |
| `GQ2.StiefelWhitney` | `GQ2/EvensKahnDerived.lean:9`, `GQ2/TraceForm.lean:9` |
| `GQ2.TraceForm` | `GQ2/EvensKahnDerived.lean:8`, `GQ2/Foundations/Axioms.lean:16` |
| `GQ2.TrivialSelfDual` | `GQ2/DualityAssembly.lean:9`, `GQ2/DevissageInduction.lean:9`, `GQ2/Roe/TrivialSelfDual.lean:11` |

Every reaching line is a `public import`, which is precisely why the plain grep lost them.

### 1.4  Documents corrected

The 427 was **not** wrong anywhere, so no document needed its numerator changed.  What the three
sites lacked was the as-of hash on the *denominator*, which has drifted 930 -> 937.  Annotations
applied:

* `docs/dyadic/w74-critical-path.md`, after §2.1's W76 annotation: the adjudication, the
  as-of-`4fff1592` reading of "427 of 930", and the current 936/937.  Also refreshes that
  annotation's own "69 now" for the `SqCore/Graded*` family, which is **70** at `1d3d5a84` (66 at
  `4fff1592`, 68 at `f0a71688`), still **zero** in the closure at every tree.
* `docs/dyadic/w74-house-note.md` §1.3, after the "427 of 930" sentence: same content.
* `docs/dyadic/w75-house-note.md`, on the "closure is 427" bullet: the adjudication, plus
  confirmation that that subsection's *own* recount (932 / 933 / 932 reachable, sole unreachable
  `GQ2.AxiomLedger`) reproduces exactly at `f0a71688`.

**One recommendation for the owner.**  The trap has now been fallen into twice by two independent
auditors, which is the signature of a missing tool rather than a careless reader.  The walk used
here is fifteen lines of Python; committing it under `scripts/` would make the next audit
mechanical.  I have not created it, because creating a script is outside a comment-only lane's
remit.
