# W72-HOUSE: the tree-wide manifest audit, and watch round 9

Lane `claude/w72-house`, base `e2e8917a`, cache at `6db3ee88`.
Verification of record: `scripts/mirror.sh` (sweep 5813 artifacts).
No `lake` command was run.

---

## Ticket 1: the manifest audit

### 1.0  A methodological warning, first

The tree uses the **Lean module system**.  Aggregator files such as `GQ2/DeepCount.lean`,
`GQ2/GaussCount.lean`, `GQ2/RegularSummand.lean`, `GQ2/RamifiedPack.lean` and
`GQ2/Shapiro/Ledger.lean` open with `module` and re-export their parts with

```text
public import GQ2.DeepCount.Filtration
```

A reachability check that greps for `^import ` and nothing else misses **every** `public import`
line (588 of the 3197 import lines in the tree) and therefore reports **20** unreachable modules
instead of the true 2.  My own first pass made exactly that error; it is recorded here because it
is the natural way to do this audit and it is wrong.  The regex of record is

```text
^(?:public\s+|private\s+|meta\s+)*import(?:\s+all)?\s+([A-Za-z0-9_.]+)\s*$
```

The 18 spurious hits were `GQ2.DeepCount.{Bounds,Finale,Transport}`,
`GQ2.GaussCount.{Sign,Wall}`, `GQ2.RamifiedPack.{Basic,Descent}`,
`GQ2.RegularSummand.{Freeness,Involution,Lifting,Trace}`, `GQ2.Shapiro.Ledger.Involution`,
`GQ2.DevissageInduction`, `GQ2.EvensKahnDerived`, `GQ2.MixedBilinear`, `GQ2.StiefelWhitney`,
`GQ2.TraceForm`, `GQ2.TrivialSelfDual`.  All are genuinely reachable.

### 1(a)  Physical modules vs reachability

923 `.lean` files under `GQ2/`.  **921 reachable** from `GQ2.lean`.  Two are not.

| module | lines | judgement |
| --- | --- | --- |
| `GQ2/AxiomLedger.lean` | 186 | **deliberately excluded** |
| `GQ2/Dyadic/SqCore/NuSeeds.lean` | 192 | **real wiring omission** |

**`GQ2.AxiomLedger` is deliberately excluded, and must stay excluded.**  Its only import is
`import GQ2` (line 6): it is the repo-wide batch `#print axioms` over everything, so registering
it in `GQ2.lean` would create an import cycle.  It is run standalone, and the docs say so:
`docs/dyadic/ax1-proposal.md:489` prescribes `lake env lean GQ2/AxiomLedger.lean` as a merge
gate, and `docs/adversarial-axioms-review.md:17`, `docs/tickets.md:84`,
`docs/roe-campaign-summary.md:203,244,273`, `docs/literature-axioms.md:180,435` all cite it as a
separately-run instrument.  No action.

**`GQ2.Dyadic.SqCore.NuSeeds` is a real wiring omission.**  Facts:

* It landed 2026-08-05 in `dd2d689b` ("chi-free seed search obstructs at the same weight 4, with
  an invariant") and has never been registered in `GQ2.lean`.
* Nothing in the tree imports it.  Its own two imports, `GQ2.Dyadic.SqCore.ChiFreeClearing` and
  `GQ2.Dyadic.SqCore.EichlerSeeds`, are both registered (`GQ2.lean:691` and `:690`).
* It is therefore **not built by CI**: `lakefile.toml` declares `defaultTargets = ["GQ2"]` and
  `lean_lib GQ2` with no `globs`, so only `GQ2.lean` is a root and only its transitive closure is
  built.  Eight declarations in this file have never been in a green build.
* It is **not a stub and not superseded**.  It is the companion module to
  `GQ2/Dyadic/SqCore/ChiFreeClearing.lean` and `docs/dyadic/chifree-clearing-note.md`, and it
  states the forced `x₁`-row (`SqNuSeed.nu_beta2`, `SqNuSeed.nu_x1`) and the exact admissible
  correction classes of the χ-free search.  `NuSeedWide.lean`, which sits next to it in
  `GQ2.lean` and landed later the same day, does **not** import it or subsume it.
* It typechecks clean today.  `scripts/mirror.sh check GQ2/Dyadic/SqCore/NuSeeds.lean` is `OK`,
  and its four `#print axioms` all report `[propext, Classical.choice, Quot.sound]`.  No `sorry`,
  no new axiom.  So the registration is safe to apply as-is.
* Secondary finding: the string `NuSeeds` appears in **no** `.md`, `.sh`, `.py` or `.yml` file in
  the repo.  `docs/dyadic/chifree-clearing-note.md` does not cite the module that formalises its
  balance table.  Flagged, not fixed: the note's prose is a lane record and rewriting it is not
  this lane's call.

#### The patch to `GQ2.lean` (NOT applied here; for the orchestrator to apply at merge)

`GQ2.lean` is not sorted lexicographically in any of its three blocks (73, 35 and 288 inversions
respectively), nor topologically (184 violations).  The actual convention is **landing order
within the block**.  `NuSeeds` (`dd2d689b`) landed after `ChiFreeClearing` (`49d869c6`) and
before `NuSeedWide` (`5a802bee`), all three on 2026-08-05, so the landing-order slot is between
them:

```diff
--- a/GQ2.lean
+++ b/GQ2.lean
@@ -689,6 +689,7 @@
 import GQ2.Dyadic.SqCore.EichlerReduction
 import GQ2.Dyadic.SqCore.EichlerSeeds
 import GQ2.Dyadic.SqCore.ChiFreeClearing
+import GQ2.Dyadic.SqCore.NuSeeds
 import GQ2.Dyadic.SqCore.NuSeedWide
 import GQ2.Dyadic.SqCore.JointClearing
 import GQ2.Dyadic.SqCore.PivotCoreMoves
```

In words: insert `import GQ2.Dyadic.SqCore.NuSeeds` as the new line 692, immediately after
`import GQ2.Dyadic.SqCore.ChiFreeClearing` (line 691) and immediately before
`import GQ2.Dyadic.SqCore.NuSeedWide` (line 692 before the patch).  One line added, nothing
removed.

### 1(b)  Every import line in `GQ2.lean` names an existing module, none duplicated

**Clean, in both respects.**  836 import lines, 836 distinct module names: no duplicate.  Every
one names a `.lean` file that exists.  No non-`GQ2` import.  No commented-out or malformed import
line.

Informational, not a defect: 788 of the 836 are *redundant as roots*, in that the module is also
reachable through another root.  That is expected for an explicit manifest and is not worth
changing; the 87 modules that are reachable but not listed are exactly the parts re-exported by
the aggregator files of §1.0, which is the intended pattern.

### 1(c)  Docs that claim to list modules

There is **no per-directory manifest file and no README** under `docs/dyadic/`.  What exists are
three file maps inside design memos, plus the ticket boards' "files owned" columns.  Checked in
both directions:

| doc | verdict |
| --- | --- |
| `docs/dyadic/nc-design.md` §4.1 "File map" | **MISMATCH, both directions. Annotated.** |
| `docs/dyadic/sq-design.md` §3.3 "File map and line estimates" | prospective; one file never built |
| `docs/dyadic/mc-design.md` §6 | not a map (Lean skeletons); clean |
| `docs/dyadic/cb-design.md` §5, `wl-recon.md`, `followup/*-plan.md` | ticket boards, prospective by construction |

**`nc-design.md` §4.1 is the one real discrepancy.**  It names a five-file split of
`GQ2/Dyadic/NpcJet/`; the directory was built with a *different* five-file split.  `Omega.lean`,
`Main.lean`, `Handles.lean` match; **`Blocks.lean` and `Delta.lean` do not exist**; **`Defs.lean`
and `Seams.lean` exist and are not in the map**.  I added a reality banner above the table rather
than rewriting the plan.

`sq-design.md` §3.3 plans four files for `GQ2/Dyadic/SqCore/`, which now has 87.  It is plainly a
lane design and reads as one; the only substantive point is that **`GQ2/Dyadic/SqCore/Sanity.lean`
(ticket SQ5) was never created**, so the stress pins it was to carry (the `q2.py` cross-check of
§R7 among them) have no home.  Left as a finding; that is an owner call, not a docs fix.

Two dangling Lean-side citations found while checking paths, both outside this round's wave scope
and both in files no wave-72 lane is touching, so recorded rather than fixed.  They are the two
`R6` hazards that `sq-design.md:681` already flags, and both are still live:

* **`GQ2/Roe/DRH2.lean` does not exist and never did**, but four docstrings cite it:
  `GQ2/Roe/DRWordCoh.lean:35`, `GQ2/Roe/DRWordCoh.lean:913`, `GQ2/Dyadic/Word/WordCoh.lean:1334`,
  `GQ2/Dyadic/Word/WordCoh.lean:1463`.  `docs/orchestration/roe-tickets.md:101` records the
  decision: "NO DRH2.lean (helpers private in DRDemushkin)".  The fix is to repoint all four at
  `GQ2/Roe/DRDemushkin.lean`.  (`sq-design.md` names only one of the four.)
* **`GQ2/Roe/Labute/TwoCentralTower.lean:65-66`** reads "Skeleton discipline: `sorry`s below are
  the L2 fill contract (exact inventory in the design memo); the non-`sorry` lemmas are L1 smoke
  tests."  The file contains **zero** `sorry`s; the only two occurrences of the string are in that
  sentence.  The L-campaign filled them at L6 (2026-07-26).  A docstring announcing `sorry`s in a
  sorry-free file is the worst-reading kind of stale prose, and it sits in a file the campaign
  cites for the `commP` / bracket identity.

---

## Ticket 2: watch round 9

Scope: the modules and notes of waves 69, 70 and 71, plus campaign-visible prose under
`docs/dyadic/`.

### 2.0  The known item: verified, corrected in five places

**The claim is false, and I confirmed it three ways.**  `grep` finds **17** files under
`GQ2/Dyadic/SqCore/` carrying `open scoped commutatorElement`; the tree's own diagnosis is
already written up at `GQ2/Dyadic/SqCore/Cores.lean` §"The bracket notation" (landed `f82cb316`,
wave 70) and `docs/dyadic/sq-design.md` §"Addendum (W70-HOUSE...)"; and `mirror.sh check` on
`GradedGammaThreeFour.lean`, which uses the bracket after opening the instance, is clean.
Mathlib makes `commutatorElement` a scoped instance deliberately, so `Bracket G G` is
unsynthesizable in *any* file at *any* namespace until that file opens it.  Nothing about
`GQ2.Dyadic.SqCore` is involved.  `commP a b = ⁅a⁻¹, b⁻¹⁆` is a **different function**, which is
the real reason the lanes are right to write `commP`; no note I checked conflates the two, and
`w70-cfour-note.md`, `w71-cfour-note.md` and `Cores.lean` all state the relation correctly.

Corrected, in the order the error propagated:

1. `docs/dyadic/w69-class4-note.md:42` (origin), 2. `docs/dyadic/w70-five-note.md:137`,
3. `docs/dyadic/w70-cfour-note.md:224`, 4. `docs/dyadic/w71-five-note.md:167` (the known item),
5. the count in `docs/dyadic/sq-design.md:797` and `GQ2/Dyadic/SqCore/Cores.lean:105`.

**The propagation is itself the finding, and it is intra-wave twice over:**

| note | written | the correction was on trunk at | verdict |
| --- | --- | --- | --- |
| `w70-five-note.md` | `ff13769e` 11:28:07 | `f82cb316` 11:26:18 (same wave) | falsified **two minutes** before it was written |
| `w70-cfour-note.md` | `14088969` 11:39:38 | `a4776cf0` 11:37:56 (same wave) | trunk had already retracted it; lane branched earlier so could not see it |
| `w71-five-note.md` | `ebdbabbe` 12:50:30 | in the lane's **own tree** (`f82cb316` is an ancestor) | the corrected `Cores.lean` paragraph was sitting in the lane's checkout |

Wave 71's house lane (`9b8e6f65`, "correct nine docstring claims across the wave-70 landings") ran
between the second and third rows and did not catch either.

**And the count that came with it was wrong when written, not merely stale.**
`Cores.lean:105` said "Ten files in this directory already do it".  Recomputing at `f82cb316`
itself gives **17**, and it is 17 today.  The orchestrator's own brief for this round repeats the
figure as "roughly ten".  The two neighbouring figures in the same paragraph are also off,
though only slightly and in the drifting direction: "77 `SqCore` modules that import this file"
was 78 at `f82cb316` and is **84** now; "439 modules that reach this file" was 442 and is
**451**.  All three corrected, with the recount dates attached so the next reader knows they are
snapshots.
