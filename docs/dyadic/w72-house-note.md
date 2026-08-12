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
