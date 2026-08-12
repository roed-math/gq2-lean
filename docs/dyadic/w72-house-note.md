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

Checked in both directions.  **One live discrepancy, already covered by 1(a)** (no doc lists
`NuSeeds`).  Otherwise the module-naming docs under `docs/dyadic/` cite modules rather than
enumerate them, and every module path I sampled from them resolves.  See §"1(c) detail" below.

---

## Ticket 2: watch round 9

*(written up below, after the ticket-1 bank)*
