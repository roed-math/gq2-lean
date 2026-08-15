# W72-HOUSE: the tree-wide manifest audit, and watch round 9

Lane `claude/w72-house`, base `e2e8917a`, cache at `6db3ee88`.
Verification of record: `scripts/mirror.sh` (sweep 5813 artifacts).
No `lake` command was run.

## Headline

**Ticket 1.**  923 modules under `GQ2/`, **921 reachable**.  `AxiomLedger` is deliberately
excluded and must stay so.  **`GQ2/Dyadic/SqCore/NuSeeds.lean` is a real wiring omission**: it
landed 2026-08-05, nothing imports it, and `lakefile.toml` roots only `GQ2.lean`, so its eight
declarations have never been in a green build.  It typechecks clean at std-3 today, so the
one-line patch in §1(a) is safe.  No duplicate and no dangling import line.  One doc file map
mismatches the tree in both directions.

**Ticket 2.**  **37** labelled findings **in §§2.2, 2.3, 2.4 and 2.4b** (12 high, 13 medium, 3
medium-low, 9 low), plus the known item of §2.0, **the severity-headed §2.1**, and the two
dangling Lean citations of §1(c).  The five worth reading first:

> **[W74-HOUSE, background sweep: scope added, figure kept.]**  The 37 is arithmetically exact
> under its own reading, and wave 73 §3.4(c) recounted it label by label and confirmed the
> breakdown.  What was missing is the **scope**: the count ranges over §§2.2-2.4b only, and two
> of the five items "worth reading first" sit outside it (§2.0, disclosed, and §2.1, which was
> not).  §2.1 is severity-headed ("Severity: high"), so a reader counting severity-headed
> findings gets **38**; including it would also make the breakdown 13 high, not 12.  Both
> readings existed in trunk and both are defensible; the scope clause above is what removes the
> ambiguity.  Note that wave 73 reported a *different* 38 (the 37 plus §2.4(e), which carries no
> severity), so "38" has meant two different sets and neither is the number to quote without
> saying which.

1. **A false census claim sitting on top of an axiom block.**
   `EvenStratumPoint.lean:371` says "Every declaration is expected std-3"; `mirror.sh` says five
   of them carry `tateDualityAt`, `hilbertSymbol_normCriterion_finiteDyadic` or
   `absGalQ2_localEulerCharacteristic`, and the module's own header says so too.  §2.4b(a).
2. **A quotation attributed to wave 69 that exists nowhere in the repository**, and on which a
   whole wave-70 module is premised.  §2.3(a).
3. **The refuted layer-agnostic claim was never taken back** in the module that makes it, even
   though wave 71 refuted it, told the owner, and ran a house lane in between.  Fixed here.
   §2.1.  And the same blind spot produced a **second, independent instance** in a wave-70 file
   that nobody has flagged: `cfourId_zLayer_le`, headlined "with no side condition", keeps two
   unrestricted universals that its own file's knob inventory cannot supply.  §2.3(c).
4. **A free-group identity is called class-four-only in three places**, so the two wave-70 files
   contradict each other about what class five loses.  §2.3(b).
5. **The bracket claim propagated through four notes over three waves**, and the count that came
   with it (`ten` files) was wrong when written: it was 17 then and is 17 now.  §2.0.

Nothing in this lane changes a statement.  Every edit is prose; the two module files touched are
comment-only and `mirror.sh check`-clean.

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

> **[W74-HOUSE, background sweep.]  This subsection is DISCHARGED and is now a historical
> record.**  `GQ2.Dyadic.SqCore.NuSeeds` was registered at `a515b437`, **32 minutes after this
> note was committed** (`f23d7d3c` 15:46:46, `a515b437` 16:19:13), in exactly the slot the patch
> below proposes; it lives at `GQ2.lean:692` today.  The present-tense claims below are corrected
> in place where they would otherwise read as live.  The counts are as of `f23d7d3c` and have
> since moved for legitimate reasons (see the as-of note in §1(b)).

923 `.lean` files under `GQ2/`, as of this note.  **921 reachable** from `GQ2.lean`.  Two were
not.

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

**`GQ2.Dyadic.SqCore.NuSeeds` was a real wiring omission** (registered at `a515b437`; see the
banner above).  Facts as of this note:

* It landed 2026-08-05 in `dd2d689b` ("chi-free seed search obstructs at the same weight 4, with
  an invariant") and had not been registered in `GQ2.lean` at any point since.
* Nothing in the tree imported it.  Its own two imports, `GQ2.Dyadic.SqCore.ChiFreeClearing` and
  `GQ2.Dyadic.SqCore.EichlerSeeds`, were both registered (`GQ2.lean:691` and `:690`).
* It was therefore **not built by CI**: `lakefile.toml` declares `defaultTargets = ["GQ2"]` and
  `lean_lib GQ2` with no `globs`, so only `GQ2.lean` is a root and only its transitive closure is
  built.  Eight declarations in this file had never been in a green build.
* It is **not a stub and not superseded**.  It is the companion module to
  `GQ2/Dyadic/SqCore/ChiFreeClearing.lean` and `docs/dyadic/chifree-clearing-note.md`, and it
  states the forced `x₁`-row (`SqNuSeed.nu_beta2`, `SqNuSeed.nu_x1`) and the exact admissible
  correction classes of the χ-free search.  `NuSeedWide.lean`, which sits next to it in
  `GQ2.lean` and landed later the same day, does **not** import it or subsume it.
* It typechecks clean today.  `scripts/mirror.sh check GQ2/Dyadic/SqCore/NuSeeds.lean` is `OK`,
  and its four `#print axioms` all report `[propext, Classical.choice, Quot.sound]`.  No `sorry`,
  no new axiom.  So the registration is safe to apply as-is.
* Secondary finding: the string `NuSeeds` appeared in **no** `.md`, `.sh`, `.py` or `.yml` file in
  the repo.  `docs/dyadic/chifree-clearing-note.md` does not cite the module that formalises its
  balance table.  Flagged, not fixed: the note's prose is a lane record and rewriting it is not
  this lane's call.  (No longer true of the repo: waves 73 and 74 discuss the module in their
  house notes, and `owner-items-2026-08-05.md` records it.  The `chifree-clearing-note.md` half
  stands and is annotated at W74-HOUSE.)

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
changing.

> **[W74-HOUSE, background sweep.]  The next figure was arithmetically wrong and its explanation
> was false.**  As written this paragraph said "the **87** modules that are reachable but not
> listed are exactly the parts re-exported by the aggregator files of §1.0".  Two defects.
> (i) The subtraction used the *physical* count, not the reachable one: `923 − 836 = 87`, but the
> note's own figures are `921` reachable and `836` listed, so the difference is **85**.  The 87
> silently counts the two unreachable modules as reachable.  (ii) "Exactly the parts re-exported"
> is false: recounted at wave 74's tree (929 physical, 843 listed, 928 reachable, 1 unreachable,
> so **85** reachable-but-not-listed), only **27** of the 85 are `public import` re-exports; the
> other 58 are ordinary transitive imports, among them `GQ2.Block.Char`,
> `GQ2.Dyadic.Count.H2Corestriction`, `GQ2.Phase140.GammaA.Foundation`, `GQ2.RStage.Local` and
> `GQ2.SectionNine.Induction`.  §1.0 itself names only 18 re-exports, which was already
> inconsistent with "exactly".  All figures in this subsection are **as of `f23d7d3c`**; the
> wave-74 recount is as of `4fff1592`.

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

### 2.1  NEW ITEM ONE, hypothesis satisfiability: the refuted claim was never taken back

**Severity: high.  Fixed in this lane.**

`GQ2/Dyadic/SqCore/GradedGammaThreeFour.lean` (wave 70) presented `gThreeFour_jacobi_of` as
layer-agnostic standing tooling.  Wave 71 refuted that in `GradedGammaFourFive.lean` §2 and told
the owner so in the memo ("Layer-agnostic turned out to have two meanings").  **Nobody went back
and corrected the module.**  Its last touch is `9b8e6f65`, wave 71's own house lane, which ran
*before* the refutation landed, so the file still carried the refuted claim at `e2e8917a`.

Wrong text, `GQ2/Dyadic/SqCore/GradedGammaThreeFour.lean:56-58` (module docstring):

> "And `gThreeFour_jacobi_of` isolates the passage from Hall-Witt to Jacobi as an implication
> over an arbitrary group, taking the two reductions as hypotheses.  So a run at any other layer
> supplies its own two facts and gets Jacobi without touching the word."

and `:165-170` (the docstring on the theorem itself):

> "Stated abstractly so that a run at any other layer supplies its own two facts and gets Jacobi,
> instead of redoing the Hall-Witt reduction."

Both false: `hcentral` and `hinvmid` are unrestricted universals over the ambient group, and at
`γ₄/γ₅` `hcentral` is *equivalent* to the vanishing of every left-normed fourfold bracket
(`gFourFive_hcentral_iff`), which the class-five calculus does not supply.  Corrected, with the
general lesson written into the module: **generality of binders is not reusability; what decides
reusability is whether the hypotheses are satisfiable at the other layer.**  Mirror-checked.

The line that makes this the exact round-8 blind spot is `GradedGammaThreeFour.lean:63-64`:

> "What is layer-agnostic here is the pair in `section HallWitt`, whose only binders are
> `{Q : Type*} [Group Q]`."

That sentence is a *binder* check, correctly performed, and it is what let the false claim
survive round 8.  Replaced.

### 2.2  Findings in the wave-71 modules (reported, not edited)

`GradedGammaFourFive.lean` and `GradedClassFourKnob.lean` are wave-71 `SqCore` landings that a
sibling lane may be building on this wave, so these are findings.  Each is verified against the
Lean.

**(a) HIGH.  `GQ2/Dyadic/SqCore/GradedClassFourKnob.lean:51-53` says `σ⁴` occurs in the relator.
It does not occur anywhere.**

> "The fourth powers `σ⁴` and `x₀⁴` occur in the frame's relator and in the generator relation
> alike and cancel, so they never reach the leftover"

The same sentence repeats at `:242-244`.  But `cfour_sqRelWord`
(`GQ2/Dyadic/SqCore/GradedClassFour.lean:500-502`) is

```text
  sqRelWord m = commP (m 0) (m 1) * m 1 ^ 4 * m 2 ^ 2 * commP (m 2) (commP (m 2) (m 0)) * handleWord …
```

and `sqArbBase_zero/one/two` (`ArbFrames.lean:445,450,455`) give `m 0 = σ`, `m 1 = x₀`,
`m 2 = x₁`.  The **only** fourth power in the relator is `x₀⁴`.  Upstream is the same:
`relBase_sqWord_free` has only `(b²)² = x₀⁴`.  The conclusion (`σ⁴` is not a direction the
leftover has) is right; the stated reason is not, and it is the reason a reader would reuse.
Correction: `x₀⁴` occurs in the relator and in the generator relation alike and cancels; `σ⁴`
never occurs at all.  Note the wave-71 note `w71-cfour-note.md:16-18` carries the same sentence
("The generators' fourth powers `σ⁴` and `x₀⁴` occur in the dressed frame's relator and in the
generator relation alike, and cancel"), so this is one claim in two places.

**(b) HIGH.  `GradedClassFourKnob.lean:93-96`'s "what is left" is incomplete, and it contradicts
its own lane note.**

> "What is left is the leftover's remaining factor `⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect nu'
> j`, the two class-four defects whose class-three images cancel, and the assembly of the knobs
> above into one correction tuple."

The leftover has five factors (`cfourKnob_leftover_eq`, and the display at `:44`), including
`A⁴ · ⁅A, x₀⁆²`.  `cfourKnob_pair_correction` delivers `A⁴ · ⁅⁅A, x₁⁆, A⁆ · ⁅x₁, ⁅x₁, A⁆⁆`.  So
**`⁅A, x₀⁆²` is delivered by nothing in the file**, and the residue `⁅⁅A, x₁⁆, A⁆` is left over
too.  The lane's own note has this right: `w71-cfour-note.md` §4 lists *three* remaining items,
the two defects, `⁅A, x₀⁆²`, and `⁅⁅A, x₁⁆, A⁆`.  The module's Verdict lists one.  A reader who
reads the module and not the note will think two thirds of the residue is gone.

**(c) MEDIUM.  `GradedClassFourKnob.lean:92-93` and `:18-19`: "reachable" is stronger than the
file's own two disclaimers.**

> "the `ad(x₁)²`-direction is reachable, though not by the argument that was recorded"

`:78-81` says of the residue "Reaching that residue is a separate step, **not** committed here",
and `:467` says "that it is reachable is not claimed here".  What is proved is that a *bundle*
containing the wanted term and an uncommitted residue is a knob.  The honest form is "reachable
modulo the residue `⁅⁅A, x₁⁆, A⁆`, which is not committed".  `w71-cfour-note.md:24` carries the
same unqualified "reachable", so again one claim in two places.

**(d) MEDIUM.  `GradedGammaFourFive.lean:40-42` states a consequence nothing proves.**

> "and that if it did hold then the Jacobi identity below would be an identity between three
> trivial elements"

No declaration says this and it does not follow from the cited `gFourFive_hcentral_iff`, whose
right-hand side is `∀ p q r t, commP (commP (commP p q) r) t = 1`, that is, every **left-normed**
fourfold bracket of arbitrary elements vanishes.  The Jacobi factors are `commP (commP p q) r`
with `p ∈ Y = lambdaImage G 2 5`, and `Y` is the *2-central* layer, so it contains squares as
well as brackets; such a factor is not literally a left-normed fourfold bracket, and the
implication needs an argument the file does not give.  Recommend either deleting the clause or
proving it.

**(e) MEDIUM.  `GradedGammaFourFive.lean:189` names the wrong slot, against the convention wave 70
fixed.**

> `/-- **Right additivity with a `T`-element in the near slot.** -/`

The statement is `commP p (y * q) = commP p q * commP p y` with `hy : y ∈ lambdaImage G 3 5`, so
`y` is in the **far** (right) slot.  `GradedGammaThreeFour.lean:116-117` fixes the convention
explicitly ("near = left slot, far = right slot") and its own parallel `gThreeFour_ad_right` is
docstring'd "in the far slot".  The module header repeats the error at `:29-30` ("with the near
slot moved from `Y` to `T`"), which is right for `ad_left` and wrong for `ad_right`.

**(f) MEDIUM, a count.  `GradedGammaFourFive.lean:12-13`: "two of its three declarations".**

`GradedGammaThreeFour.lean` has **14** declarations, 14 axiom pins.  The "three" is a confusion
with that file's own line 16, "in the three **forms** a class-four run consumes".  Correction:
"recorded two of its declarations".

**(g) LOW.  `GradedGammaFourFive.lean:39-40`, `:281`, `:104-105` say "every fourfold bracket";
`gFourFive_hcentral_iff` quantifies over left-normed ones only** (`⁅⁅⁅p,q⁆,r⁆,t⁆`, not
`⁅⁅p,q⁆,⁅r,t⁆⁆`).  Insert "left-normed".  Same phrase now appears in my own repair at
`GradedGammaThreeFour.lean`, where I wrote "left-normed" for exactly this reason.

**(h) LOW.  `GradedGammaFourFive.lean:28`, `:155`, `:436`: "every correction term ... is killed by
§1".**  Several are killed by centrality of `Z`, not by the `⁅T, Y⁆` vanishing:
`gFourFive_sq_dress` (`:496`), `gFourFive_drop_right` (`:487`), `gFourFive_sq_zLayer_dress`
(`:502`) all go through `cfive_commP_zLayer_left` with no use of `gFourFive_commP_vanish`.

**(i) LOW.  `GradedClassFourKnob.lean:123` and `:128` headline "The `λ`-row of a square doubles" /
"The `ν'`-row of a square doubles".**  The statements are only the implications
`nuLam h d = 1 → nuLam h (d ^ 2) = 1` and `nu' d = 1 → nu' (d ^ 2) = 1`.  The doubling is a step
of the proof, not the statement.  The "In particular" sentence that follows *is* the statement.

**(j) LOW.  `GradedClassFourKnob.lean:30-32`** says wave 68's dressing "is exactly row-trivial by
construction", dropping the two side conditions `cfourKnob_dressSq_admissible` actually carries
(`nu' (dsqSigma h) = ofAdd 1`, `nu' (dsqX0 h) = ofAdd 0`).  The declaration docstring at `:158-160`
is accurate; only the header drops them.

### 2.3  Findings in the wave-70 modules (reported, not edited)

Same reason: wave-70 `SqCore` landings that a sibling lane may be building on.  All verified
against the Lean.

**(a) HIGH.  A quotation attributed to wave 69 that has no source.**
`GQ2/Dyadic/SqCore/GradedRelatorBase.lean:13-14`:

> "Its closing analysis observed that the proof of that step "used no commutativity" and
> "should replay at every class"."

The first quotation is real: `docs/dyadic/w69-class4-note.md:80` has "**no commutativity is used
for that step**", and `GradedClassFour.lean:558` repeats it.  **The second occurs nowhere in the
repository.**  `grep -rn 'should replay' GQ2/ docs/` returns exactly one hit, this line itself.
The whole of `GradedRelatorBase.lean` is built on it ("This file carries out the replay"), and a
reader will go looking for a wave-69 commitment that was never made.  Correction: drop the second
quotation and say the replay is this file's own idea.  Minor, same sentence: the sourced quote is
in wave 69's **§4 header**, not its closing analysis, which is the `ANALYSIS, NOT COMMITTED` block
at `GradedClassFour.lean:110-131`.

**(b) HIGH.  A free-group identity called class-four-only, in three places.**
`GradedRelatorBase.lean:105-107`:

> "and `commP c (conjP c a) = commP c (commP c a)` needs the correction term of
> `cfour_commP_mul_right` to die.  Neither is available one class up, so it is this statement, not
> `cfour_sqWord`, that a class-five run starts from."

`commP c (conjP c a) = commP c (commP c a)` is **free**.  Wave 69's own proof
(`GradedClassFour.lean:491-493`) closes it with `cfour_commP_mul_right`, `cfour_comm_self` and
`cfour_one_comm`, and all three live in `GradedClassFour.lean`'s `section FreeIdentities` under
`variable {Q : Type*} [Group Q]` (`:154-191`): no level, no class, no topology.  By hand,
`conjP c a = c · w` with `w = commP c a`, and `commP c (c·w) = c⁻¹w⁻¹cw = commP c w`.  So only
`cfour_pow_four_inv` is class-four, and "Neither is available one class up" is wrong on one of the
two.  Repeated at `:53-54` ("the two simplifications ... are the class-four-only part") and
`:92-94` ("Two of its three steps are class-four facts").  `GradedClassFive.lean:350-354` states
the correct restricted version, so the two wave-70 files disagree with each other.  Consequence
worth flagging: `relBase_sqWord_free` could be stated with `commP c (commP c a)` over an arbitrary
group, which is stronger and contradicts the stated reason for leaving `conjP` in it.

**(c) HIGH.  A second instance of the round's NEW item, in a wave-70 file.**
`GQ2/Dyadic/SqCore/GradedClassFourIdentity.lean:524-528`:

> "⭐⭐ **Generation of the layer at `D_sq h`, with no side condition** ... it is the form a
> class-four witness search consumes: to reach the leftover it is enough to reach every square of
> `γ₂` and every bracket `commP γ₂ Q₄`."

`cfourId_zLayer_le` (`:529-533`) discharges only the **closedness** hypothesis of
`gThreeFour_zLayer_le`.  It still carries `hsq : ∀ y ∈ Y, y ^ 2 ∈ S` and
`hcomm : ∀ y ∈ Y, ∀ q, commP y q ∈ S`, both unrestricted universals, plus the requirement that
`S` be a *subgroup*.  Ask the round's question, what would have to hold to use it: §4's own knob
inventory (`:65-75`) reaches `commP c g` only for `g` **a frame letter**, five families, and
reaches `c²` only bundled with `commP c (m 2)`; and nothing shows the reachable knobs form a
subgroup.  So the sentence "it is enough to reach every square and every bracket" describes a
supply the file does not have.  Correction: headline to "with the closedness side condition
discharged", and say plainly that the gap between `hcomm` and the frame-letter inventory is the
open part.

**(d) HIGH.  A section header that contradicts its own module header.**
`GradedClassFourIdentity.lean:191`:

> `/-! ## §2 A `γ₂`-valued correction is free on the rows and on mod-2 independence -/`

against `:37-38` of the same file:

> "It is **not** free on the rows: `γ₂`-membership implies nothing about `λ` or `ν'`"

§2 contains exactly two declarations, `cfourId_twoCentral_le_index_two` and
`cfourId_modTwoIndep_mul`; neither mentions `nuLam` or `nu'`.  The module header is the correct
one, and the row-triviality hypothesis carried throughout the file is there precisely because the
§2 header is false.  Correction: delete "on the rows and".

**(e) HIGH.  Three attributions to wave 69 of statements wave 69 does not make.**
`GradedClassFive.lean:11-17` and `:269-270` credit wave 69 with recording the class-five loss and
with having "named two things the class-five analogue would need: `⁅γ₂, γ₃⁆ ≤ γ₅`, and a
non-abelian bookkeeping layer".  Wave 69 is `GradedClassFour.lean` plus
`docs/dyadic/w69-class4-note.md`.  The module mentions class five on exactly one line (`:860`,
"the residual would start at class five") and says nothing about `⁅γ₂, γ₃⁆ ≤ γ₅` or bookkeeping;
the note has neither phrase.  The observation is this file's own and should be claimed as such.
(The one quotation here that *is* accurate is "reorder at will", `GradedClassFour.lean:511`.)

**(f) MEDIUM.  `γ₄ ⊄ γ₅` asserted as committed, three lines after "nothing is refuted".**
`GradedClassFive.lean:78-79`:

> "What is committed is that the class-four *proof* of abelianness is unavailable one class up,
> since it delivers `⁅γ₂, γ₂⁆ ≤ γ₄` and `γ₄ ⊄ γ₅`"

Nothing proves `γ₄ ⊄ γ₅`, and over the file's binders (an arbitrary topological group) it is
false: for the trivial group all layers coincide.  `twoCentralSeries` is antitone
(`Roe/Labute/TwoCentralTower.lean:200`) and nothing makes it strict.  Correction: "`γ₄`-membership
does not imply `γ₅`-membership".

**(g) MEDIUM.  `cfourId_discreteTopology` docstring covers every level; the statement is level
four.**  `GradedClassFourIdentity.lean:513`: "Every level of the tower of `D_sq h` is discrete",
on `theorem cfourId_discreteTopology : DiscreteTopology (levelQuot (DSq h : Type) 4)`.  The cited
`discreteTopology_levelQuot` does give every level, and the proof supplies `4` as its last
argument, so generalising the statement to `(k : ℕ)` is a one-token change and is the better fix.
Same over-reach at `:107`.

**(h) MEDIUM.  "the entire class-four obligation" on a one-directional theorem.**
`GradedClassFourIdentity.lean:266-268` says "So the entire class-four obligation is: some
`γ₂`-valued, exactly row-trivial correction ... kills the relator one class up."
`cfourId_supply_of_reach` is `H → SqClassClearingSupply h 4`, sufficiency only, and
`SqClassClearingSupply h 4` quantifies over **all** admissible tuples, not only `γ₂`-corrections
of `bridgeTuple`.  This is the same criticism the file's own §1 (`:28-32`) makes of
`cfour_supply_of_eichDefect`.  `GradedRelatorBase.lean:386-389` already has the right wording.

**(i) MEDIUM-LOW.  A reason that contradicts a lemma the same file cites.**
`GradedRelatorBase.lean:45-46`: "because it is what buys the equality **on the nose** in a target
group where the layers are not normal".  `twoCentralSeries_normal`
(`Roe/Labute/TwoCentralTower.lean:189`, global instance at `:197`) says every layer of every
topological group is normal, and this file cites it at `:32-33`.  The target of
`relBase_relator_base_of_commuting` is a bare `[Group Q]`, which has no layers at all.

**(j) MEDIUM-LOW.  "the gap is real" is not committed.**  `GradedRelatorBase.lean:70-72` and
`:354-356`.  Asserting the gap needs `¬ RelBaseDefectDies h 3`, i.e. a selected `nu', j` with
`bridgeDefect nu' j ≠ 1`.  `bridgeDefect` is defined, shown central, shown of order at most two
and evaluated (`GradedBridge.lean:473-488`); nothing anywhere shows it nontrivial.

**(k) LOW, counts and placement.**  `GradedRelatorBase.lean:115-116` says `relBase_map_commP` is
too heavy to import `GradedTwo` "for two rewrites"; it is used **six** times (`:319` twice, `:323`
twice, `:331` twice).  `GradedRelatorBase.lean:254-255` says "no hypothesis survives into the
statement at all" of `relBase_relator_base_mem_iff`, which takes `[hN : N.Normal]` and uses it.
`GradedClassFive.lean:53-54` calls its list "the whole inventory" while the file's own Scope note
names two further wave-69 lemmas that do not survive.  `GradedClassFourIdentity.lean:79` cites
"Wave 69's §5" for material that is in wave 69's `ANALYSIS, NOT COMMITTED` header block.

**Clean in these two modules,** checked and confirmed: the subsumption claim at
`GradedGammaFourFive.lean:47-49` is **true** (`gFourFive_jacobi_of_forall` has binders,
hypotheses and conclusion identical to `gThreeFour_jacobi_of`, and `gFourFive_jacobi_of`'s six
hypotheses are genuinely pointwise, hence satisfiable one layer up, which is the whole point);
the §4 knob table is right row by row; the axiom pins are complete, in declaration order, and
match the notes exactly (49/49 and 21/21); and roughly forty cross-referenced `cfive_*`,
`cfour_*`, `gThreeFour_*`, `relBase_*` and `bridge_*` citations all say what the citing prose
says they say.

### 2.4  NEW ITEM TWO, intra-wave staleness

> **[W74-HOUSE, watch round 11.]  This subsection fell through the application passes.**  Wave 73
> applied §§2.2, 2.3 and 2.4b (33 findings) and said so accurately; **§2.4 was in nobody's scope**,
> so (a), (b) and (c) sat unapplied for two waves while every other section of this note was
> cleared.  All three are `EvenAlphaOne.lean` prose and all three were still live at `4fff1592`.
> **Applied at wave 74**, comment-only.  ((d) and (e) were self-applied by this lane when written
> and needed nothing.)  The process lesson is the one this subsection is about, turned on the
> audit itself: a scoped application pass leaves a residue unless the scope is reconciled against
> the finding list.

Beyond the bracket propagation of §2.0, which is the purest example this round produced:

**(a) HIGH.  `GQ2/Dyadic/Instances/EvenAlphaOne.lean` was left behind by its own wave, where its
sibling was not.**  Wave 70 landed `EvenAlphaOne.lean` at `52239a0b` (11:18:21) and
`MarkedCore/NFrameAlphaOne.lean` at `a3c34e59` (12:02:20), 44 minutes later.  `EvenAlphaOne.lean:668`
says:

> "The identification of the invariant as `q = 4` is **not** proved here: `demushkinQ` is a
> torsion count on the abelianization, and computing it at `α = 1` is a separate step that this
> file does not take."

Literally true of the file, and it stays true.  But the step *was* taken, in the same wave, and
`Instances/EvenDemushkin.lean:252-260` was updated to say so ("The `q`-invariant at `α = 1` is
**computed too**, later in the same wave ... An earlier merge note in this docstring recorded the
`q`-invariant as uncomputed.  That was true when written and was superseded within the same
wave").  `EvenAlphaOne.lean` got no such pointer.  One file of a pair was fixed.  The repair is a
sentence: "that step is `nFrame4_demushkinQ_DN_one` in `MarkedCore/NFrameAlphaOne.lean`, landed
later in this wave".

**(b) HIGH, and cross-wave.  `EvenAlphaOne.lean:673-675` records as open what wave 71 refuted.**

> "Whether the classification extends to `α = 1` is a question about the frame and stage layers
> above the model, and stays open."

Wave 71's `Instances/EvenStratumPoint.lean` proves `evenStratum_no_adaptedModelEquiv`: on the
whole third stratum, and at every handle count, there is **no** isomorphism carrying the field cup
form to `evenFrameGramModel h`, which is the shared step of all three even frame producers (I
verified "all three": `evenFrameAdaptedModelEquiv` is applied as a term at exactly
`StageAbstractionEvenEndpoint.lean:360`, `StageAbstractionEvenFrameCore.lean:803`,
`StageAbstractionEvenFrattiniFrameM.lean:646`).  The `α = 1` `N` core sits on that stratum, at the
one surviving point `imChiN 1 = evenRangePrin 2`, and `EvenAlphaOne.lean`'s own §11 says so.  So
the frame half of "stays open" is closed, negatively, for the committed route.

**(c) MEDIUM.  `EvenAlphaOne.lean:688-689` cites its own §10.3 for a claim about the wrong
frame.**

> "it does **not** by itself prove the classification there, which needs the frame and stage
> inputs that §10.3 says are missing at `α = 1`."

§10.3 (`:659-665`) is about `MarkedCore.NFrame` being empty.  The classification's frame is
`StageGeneric.Frame` (`Instances/StageAbstraction.lean:793`), a different structure with
generators, character rows and level-two generation and **no torsion slot at all**.  Wave 71's
`w71-stratum-note.md` §1(a) names exactly this conflation and prices a lane against it as a
non-item; I re-verified its supporting count, `NFrame` is taken as a *term* by exactly three
declarations tree-wide (`NFrame.toNDecomposition`, `demushkinQ_DN_nFrame`,
`demushkinQ_DN_one_nFrame4`), none in the stage layer.

**(d) MEDIUM.  Discharged-but-still-open: `w71-stratum-note.md` §5.**  It reported stale prose in
`EvenForwardRouteSkeleton.lean` "for the orchestrator", who fixed it later in the same wave at
`e6d10612`.  The note read as an open item.  Annotated in this lane.  One residue, reported not
fixed because that file may be in flight: the applied notice is headed
"⚠ **Corrected at wave 70**" (`EvenForwardRouteSkeleton.lean:81`), but the correction was applied
at **wave 71** against wave 70's landings.

**(e) The wave-69 headline, corrected here.**  `w69-class4-note.md` §0 called
`cfour_supply_of_eichDefect` "a reduction of the whole class-four obligation".  It is a sufficient
condition using the trivial dressing, and wave 70's own
`GradedClassFourIdentity.lean:24-31` proves its hypothesis forces `bridgeDefect nu' j = 1`, that
is, that wave 68 never needed the dressing it was built to construct.  Wave 70 calls the
hypothesis "not a plausible thing to prove"; the wave-69 note was never marked.  Marked now.

### 2.4b  Findings in the wave-70/71 `Instances` and `MarkedCore` modules (reported, not edited)

`EvenStratumPoint.lean`, `EvenAlphaOne.lean`, `NFrameAlphaOne.lean` and
`NFrameAlphaOneInvariants.lean` are squarely the subject matter of a sibling lane this wave, so
none of these is edited.  All verified against the Lean; the axiom one is machine-verified.

**(a) HIGH, machine-verified.  `GQ2/Dyadic/Instances/EvenStratumPoint.lean:371-372` states an
axiom scope its own module header contradicts and `mirror.sh` refutes.**

> "Every declaration is expected std-3 (`propext`, `Classical.choice`, `Quot.sound`)."

The module header at `:95-98` says the opposite and is right: "§4 and §7 add `tateDualityAt` and
`hilbertSymbol_normCriterion_finiteDyadic`, and §6 adds `tateDualityAt` and
`Foundations.absGalQ2_localEulerCharacteristic`."  My own `scripts/mirror.sh check` on the file
prints exactly that: `evenStratum_cup_self_eq_zero`, `evenStratum_no_adaptedModelEquiv` and its
two corollaries carry `hilbertSymbol_normCriterion_finiteDyadic` and `tateDualityAt`, and
`evenStratum_orientedEquivN_one_of_forwardGeneratorData` carries `tateDualityAt` and
`Foundations.absGalQ2_localEulerCharacteristic`.  This is the highest-risk line in the round: it
is a **census claim**, it sits directly above the `#print axioms` block, and it says "std-3" for
declarations that consume three census axioms.  Correction: delete the sentence, or replace it
with the header's per-section breakdown.

**(b) HIGH.  `EvenStratumPoint.lean:311-316` and `:70-71`: "ALONE", "exactly one `Prop`", "three
inputs".  The lemma has four hypotheses and one of them survives.**

> "The even classification at branch parameter `1` follows from the forward-generator datum
> ALONE.  Both other inputs of `nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData` are
> discharged here ... So the model layer at the surviving point is fully paid, and what remains is
> exactly one `Prop`."

`nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData`
(`Instances/EvenForwardRouteSkeleton.lean:406-408`) takes `(hα : 1 ≤ α)`,
`(hev : Module.finrank ℚ_[2] K = 2 + 2 * h)`, `(hmodel : NModelDemushkin α h)` and `(hdata : …)`:
**four**, not three.  The theorem immediately below the docstring still binds `hev`
(`EvenStratumPoint.lean:320`).  So two hypotheses remain, not one, and "ALONE" is wrong.  The
file's own display quote at `:76-77` has it right ("given `Nonempty (NForwardGeneratorData 1 h
χ_cyc)` **and** `[K : ℚ₂] = 2 + 2h`"), as does `w71-stratum-note.md:87-89`.  Only the headline
prose overreaches, which is the classic shape.

**(c) HIGH.  `EvenStratumPoint.lean:63-65`: "nowhere in the tree" is falsified by a committed
theorem.**

> "no declaration in this file, or anywhere in the tree, asserts or denies
> `Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)` at a third-stratum field."

`Instances/EvenUnramified.lean:341-343`, wave 69's own lane:
`evenUnram_isEmpty_orientedN {alpha} (halpha : 3 ≤ alpha) (hr : range … = evenRangePrin alpha)
(a h : ℕ) : IsEmpty (OrientedContinuousMulEquiv (chiN a h) (chiCycKTwo (K := K)))`.  At `a := 1`
this **denies** exactly that `Nonempty`, at every third-stratum field of depth `α ≥ 3`.  The
intended scope is the surviving point, which sits at depth 2; the sentence overreaches to the
whole stratum.  Correction: "at the stratum's depth-2 point".

**(d) MEDIUM.  `GQ2/Dyadic/MarkedCore/NFrameAlphaOne.lean:27-28` points at the wrong section, and
that section says so.**  The header claims the invariant package `(rank, q) = (4 + 2h, 4)` is
closed "(§8)".  §8 (`:611-617`) opens by saying "The invariant package ... is **not** here", and
sends the reader to `Instances/NFrameAlphaOneInvariants.lean`, which the same header names
correctly 120 lines later.  Reads like a leftover from before the `ec8e6f9e` split.

**(e) MEDIUM.  `EvenStratumPoint.lean:17-18` and `:25-26` rebut a claim the wave-69 note did not
make.**  The header says the wave-69 note "priced two further replacements", the first being "a
`q = 4` frame **at the stage level**".  `docs/dyadic/w69-unram-note.md:112-117` prices **three**
items, and its first is explicitly the *abelianization* layer ("the abelianization torsion there
should be `Z/4`, not the `Z/2` that `NFrame` demands"), which is precisely what wave 70 supplied.
`NFrameAlphaOne.lean:108-110` states the same note correctly as three items.  So §1(a)'s "the
`q = 4` frame at the stage level is a non-item" knocks down a stage-level claim the note never
made.  The underlying finding, that `NFrame` and `StageGeneric.Frame` are different objects,
stands and is important; only the attribution is wrong.

**(f) MEDIUM.  `EvenStratumPoint.lean:155` (§2 header) and `:85`: "the `α = 1` parity table is the
zero table" is a whole-table claim proved at one entry.**  §2 contains exactly one theorem,
`evenStratum_parity_nUnit_one` (`:159`), the single value at the twisted index.  The `α ≥ 2`
analogue `evenDegreeN_parity_table` (`StageAbstractionEvenFrattiniFrameN.lean:203`) quantifies
over all `i : Fin (coreRank h)`; no `α = 1` analogue of that is proved.  The per-declaration
docstring at `:157-158` is correctly scoped; the section header is not.  Note
`w71-stratum-note.md:55-56` carries the same whole-table phrasing.

**(g) MEDIUM.  `EvenStratumPoint.lean:145-146`: "holds exactly on `α ≥ 2`" drops the binder the
theorem carries.**  `evenStratum_four_dvd_nUnit_add_one_iff` takes `(hα : 1 ≤ α)`, genuinely
consumed by the `omega` at `:151`.  `α = 0` is not covered.  The lane note keeps the caveat
(`w71-stratum-note.md:46`, "for α >= 1"); the module docstring drops it.

**(h) MEDIUM-LOW, intra-wave.  `NFrameAlphaOne.lean:93-95` describes a docstring that has since
been corrected, in the present tense.**

> "and `Instances/EvenDemushkin.lean`'s residual R1 records the `α = 1` `q`-invariant as
> uncomputed."

`EvenDemushkin.lean:252-260` now says the opposite and cites this very file
(`nFrame4_demushkinQ_DN_one`), having been corrected at `52ac5b7f`, wave 71.  The sentence's
point survives (the next clause says "§7 computes it, so both records are discharged"), but the
present tense is now false, and it is the reciprocal half of a fix that was applied on one side
only.  Correction: past tense.

**(i) LOW.  `GQ2/Dyadic/Instances/NFrameAlphaOneInvariants.lean:89` cites a file that does not
exist**: "the `H¹`-count of `EvenModel.lean`".  There is no `EvenModel.lean` under `GQ2/`;
`EvenModel` is a *namespace*, and `demushkinRank_DN` is at
`Instances/EvenModelH2.lean:482`.  The namespace-only citations elsewhere (`:15`,
`EvenAlphaOne.lean:19`) are fine.  This is the third dangling file citation this round, after the
four `GQ2/Roe/DRH2.lean` sites of §1(c).

**(j) LOW, systematic.  `EvenAlphaOne.lean:110` and `:124` cite three `Cores.lean` line numbers,
each off by exactly 3**: `diagCoeff` is at `Cores.lean:1215` (cited `:1212`),
`mWord_centLift_fib` at `:1392` (cited `:1389`), `nWord_centLift_fib` at `:1411` (cited `:1408`).
Three lines were inserted above them and the citations never moved.  Every other line citation
checked across these four files is exact.

**(k) LOW.  `EvenAlphaOne.lean:703-704` pairs the wrong section**: "§6 against `card_H2_DN` /
`card_H2_DM`" should be §7, whose `evenAlphaOne_card_H2_DN`/`_DM` (`:521`, `:543`) are the
analogues.  §6 is the inverse-Gram section.  And `NFrameAlphaOne.lean:11-12` cites only
`evenAlphaOne_isDemushkin_DN` for the two-row claim "both `α = 1` even cores Demushkin"; the `M`
half is `evenAlphaOne_isDemushkin_DM` (`EvenAlphaOne.lean:598`).

**(l) LOW.  `NFrameAlphaOne.lean:625-626`: "The two proofs share `dn_abRel` and nothing else".**
Both run through the same `abLiftG ∘ nLiftHom` coordinate homomorphism with the same `ℤ/4`
marking: `NFrameExists.lean:178-182`'s `nZ4Hom` and `NFrameAlphaOne.lean:339-343`'s `nFourTHom`,
where `nCoordHom` is *defined* as `abLiftG (nLiftHom …)` (`NFrameExists.lean:213-215`).  The file
itself records the duplication at `:69-71`.  The cross-check is still worth having; it is just not
independent in the way claimed.

**Clean in these four modules,** independently confirmed: every Gram matrix in `EvenAlphaOne.lean`
checks entry by entry against the Lean (the `α ≥ 2` matrix, the `α = 1` `N` and `M` matrices, the
inverse-Gram and its two correction slots); the `decide` inventory is exactly the four calls it
claims; the directional claims are all proved in the direction stated (`demushkinQ (DN 1 h) = 4`
with no frame hypothesis, `IsEmpty (NFrame 1 h)` derived *from* the invariant and not assumed,
`evenStratum_kappa_eq_zero` rather than `≠ 0`, `evenStratum_no_adaptedModelEquiv` a genuine
negation, both `α = 1` cores Demushkin at every handle count); the residual directions R1 FALSE /
R2 TRUE are correctly signed; and `NFrameAlphaOne.lean:80`'s "over 740 transitive importers" is
accurate on the module graph (`GQ2.Demushkin` has 770 transitive dependents).  One imprecision in
the safe direction, recorded for completeness: `evenStratum_no_adaptedModelEquiv` refutes only the
first conjunct of `evenFrameAdaptedModelEquiv`'s conclusion, so the refutation is *stronger* than
the docstring advertises.

### 2.5  Standing items: what came up clean

Said plainly, because a watch round that reports only hits is not a check.

* **Axiom and census claims: clean, machine-verified.**  Every axiom-pin claim in the wave-69, -70
  and -71 notes matches `mirror.sh check` exactly, including the four named `[propext]`-only
  exceptions of the wave-71 five note and the four named subset exceptions of the wave-70 five
  note.  The census is **11**, matching `EXPECTED_AXIOMS=11` in `scripts/check_axioms.sh` and the
  owner memo's "census 11".  `SORRY_ALLOWLIST` is empty and the tree has **zero** real `sorry`s:
  all 11 occurrences of the string under `GQ2/` are the word "sorry-free" in prose.
* **Cross-reference *names*: clean.**  Every backticked snake_case identifier in all seven wave
  notes resolves to a declaration or a structure field in the tree, except mathematical notation
  (`gamma_2`, `zeta_8`, `Q_k`), Lean features (`native_decide`) and mathlib names
  (`commutatorElement_def`).  No note cites a lemma that does not exist.
* **Counts: two hits, both the same mistake, both fixed.**  `w71-stratum-note.md` "19
  declarations, all pinning" (18, one unpinned) and `w69-unram-note.md` "All 31 declarations"
  (32, one unpinned).  Both count "declaration" as "declaration carrying a `#print axioms` line",
  which drops a `def` and an `abbrev` respectively.  The four SqCore lane notes' declaration
  counts (46, 21, 49, 21 + 27) are all **exact**.
* **Headline-versus-statement: one hit in the notes** (§2.4(e)), plus the module hits of §2.2 and
  §2.3.  The wave-71 stratum note's headline, the strongest of the round, is an exact reading of
  `evenStratum_no_adaptedModelEquiv` including both its hypotheses.
* **Conflation of `commP` with the element bracket: none found.**  `w70-cfour-note.md`,
  `w71-cfour-note.md` and `Cores.lean` all state `commP a b = ⁅a⁻¹, b⁻¹⁆` correctly.  This was
  worth checking separately from the elaboration claim, and it comes up clean.

---

## Verification record

* Base `e2e8917a`, lane branch `claude/w72-house`, shared cache at `6db3ee88`.
* `scripts/mirror.sh sweep` (5813 artifacts) once at lane start.  **No `lake` command was run.**
* `scripts/mirror.sh check` run on: `GQ2/Dyadic/SqCore/NuSeeds.lean` (the unwired module, clean,
  four pins all std-3), `GQ2/Dyadic/SqCore/Cores.lean` and
  `GQ2/Dyadic/SqCore/GradedGammaThreeFour.lean` (the two files I edited, comment-only, clean),
  and, as evidence for claims rather than as edits,
  `GQ2/Dyadic/Instances/EvenStratumPoint.lean`, `GQ2/Dyadic/Instances/EvenUnramified.lean`,
  `GQ2/Dyadic/SqCore/GradedClassFive.lean`, `GQ2/Dyadic/SqCore/GradedRelatorBase.lean`,
  `GQ2/Dyadic/SqCore/GradedClassFourIdentity.lean`,
  `GQ2/Dyadic/SqCore/GradedClassFourKnob.lean`, `GQ2/Dyadic/SqCore/GradedGammaFourFive.lean`.
  All clean.
* Both files I edited are byte-identical after comment stripping.  No statement, binder,
  hypothesis or proof was touched anywhere in this lane.
* No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth` introduced.
  Independently confirmed for the tree: `SORRY_ALLOWLIST` is empty, `EXPECTED_AXIOMS=11` matches
  the 11 `axiom` declarations in `GQ2/Foundations/Axioms.lean`, and every occurrence of the
  string `sorry` under `GQ2/` is the word "sorry-free" in prose.
* `GQ2.lean` **not edited**, per the lane.  The one-line patch is §1(a).

## Files edited

| file | what |
| --- | --- |
| `GQ2/Dyadic/SqCore/Cores.lean` | three counts (10→17, 77→84, 439→451), comment-only |
| `GQ2/Dyadic/SqCore/GradedGammaThreeFour.lean` | the refuted layer-agnostic claim, two docstrings |
| `docs/dyadic/w69-class4-note.md` | bracket claim at its origin; headline qualified |
| `docs/dyadic/w69-unram-note.md` | declaration count |
| `docs/dyadic/w70-cfour-note.md` | bracket claim; §4 withdrawal banner; layer-agnostic claim |
| `docs/dyadic/w70-five-note.md` | bracket claim; the `conjP` collapse is free, not class-four |
| `docs/dyadic/w71-five-note.md` | bracket claim (the known item) |
| `docs/dyadic/w71-stratum-note.md` | declaration count; §5 marked discharged |
| `docs/dyadic/sq-design.md` | two counts in the W70-HOUSE addendum |
| `docs/dyadic/nc-design.md` | file-map reality banner |

## For the wave-73 queue

1. ~~**Apply the `GQ2.lean` patch** of §1(a).  One line.  Until it lands,
   `GQ2/Dyadic/SqCore/NuSeeds.lean` is not built by CI.~~  **DISCHARGED at `a515b437`**, 32
   minutes after this note was committed, in the slot §1(a) proposed.
2. **The two `sq-design.md` R6 hazards are still live** and are cheap: repoint four docstrings
   from the nonexistent `GQ2/Roe/DRH2.lean` to `GQ2/Roe/DRDemushkin.lean`, and delete
   `GQ2/Roe/Labute/TwoCentralTower.lean:65-66`'s announcement of `sorry`s in a file that has
   none.  Both are in `GQ2/Roe/`, which plan A6 freezes, so they need an owner nod.
3. **A pass over the findings of §2.2, §2.3 and §2.4b** once the sibling lanes have merged.  They
   are prose-only and I wrote each one with its correction, so they are a single mechanical lane.
4. **Watch round 10 should keep both new items** and add a third, suggested by this round: **a
   claim fixed in one file is often half a fix**.  Three times this round the reciprocal citation
   was left stale (`EvenDemushkin` fixed but `EvenAlphaOne` and `NFrameAlphaOne` not; the module
   corrected but the lane note not, twice).  The check is: when you correct a claim, grep the
   claim's *subject* across the tree, not the file you are in.
