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

**Ticket 2.**  `GeneralAssembly.lean`'s **42** pins are now recorded in-file.  They are **not**
uniform: 34 print at most std-3 and **8 carry campaign axioms**, so the pins block states the
split rather than the tidy claim, which would have reproduced the campaign's own
`EvenStratumPoint.lean:371` defect.  The LamFrames repair is applied at both shipped sites, and
the wave-75 finding that produced it is annotated as **wrong** at its source.  Of the six
note-level items, **six applied, none declined**, but **two came back the other way**: the "29
findings" headline is right and the table under it is one short, and
`GradedDeltaFunctionals.lean`'s pin count did not drift at all.

**Ticket 3.  Staleness first, and it paid immediately.**  **The two wave-76 notes contradict each
other**, `w76-cert-note.md` §7 item 4 reporting `GeneralAssembly.lean` unregistered while
`w76-house-note.md` §4.2 item 4 strikes the same item as done, `a19fac5a`.  The house note is
right, and the cert note's claim was already false **at its own lane's base**.  Worse in the other
direction: `w76-house-note.md` §4.2's "all still live and none touched this wave" is wrong about
two items that its own sibling landed **five minutes before the note was committed**.  One
identity headline found, in `GradedJoinBase.lean`, and corrected.  The §4 falseness labelling
audited at every site and found **sound**, in the note, in the module and in the owner memo; no
docstring presents `GBaseResidual` as false.

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

---

## Ticket 2: the genuine audit items

### 2(a)  `GeneralAssembly.lean`: 42 pins recorded, and the file is not uniformly std-3

The module carried **zero** `#print axioms` lines.  A `§5 Axiom pins` block now records one pin
per declaration, 42 in declaration order, following the sibling convention (`/-! ## §N Axiom
pins -/`, a `section AxiomPins`, one line per declaration).  `mirror.sh check`: **OK**, 42 pins
printed, no error, no warning, no line over 100 characters added.

**What printed, and it is the finding.**  The obvious docstring to write was "all std-3", and it
would have been false.  Measured against the mirror at `1d3d5a84`:

| group | count | beyond `propext, Classical.choice, Quot.sound` |
| --- | --- | --- |
| definitions, structures, word/core rows, parity lemmas, all five `genAsm_branch_of_*` | **34** | none (`genAsm_degree_frozen` prints *no* axioms at all) |
| `genAsm_candidate_equiv_galK_of_supply`, `genAsm_candidate_equiv_galK`, `genAsm_rowEquiv_sqrt{Two,Five,Ten,NegTen}` | **6** | `tateDualityAt`, `absGalQ2_isTopologicallyFinitelyGenerated`, `absGalQ2_localEulerCharacteristic` |
| `genAsm_evenRoute_output` | **1** | those three plus `hilbertSymbol_normCriterion_finiteDyadic` |
| `genAsm_rowEquiv_sqrtNegTwo` | **1** | those four plus `relativeStiefelWhitney_dyadic` (the widest pin in the file) |

The split is clean and worth stating as content rather than bookkeeping: **the general branch
datum and its constructor table are axiom-free, and the campaign axioms enter only where a row is
identified with `G_K`.**  Had the block gone in with a blanket claim it would have reproduced
`EvenStratumPoint.lean:371` exactly, which is finding 1 of `w72-house-note.md`.

⚠ **Reported, not applied: `GeneralCertificates.lean` has the same defect and I was not permitted
to fix it.**  48 declarations, **zero** `#print axioms`, while `w76-cert-note.md` §6 reports a
full measurement of all 48 (1 + 1 + 44 + 1 + 1, which sums correctly).  The measurement exists
only in the note.  **[W78-HOUSE, ticket 1: APPLIED, and "48" is wrong.**  The file has **44**
declarations, and 44 pins are now recorded (`d19eb316`).  48 is the cert note's arithmetic taken
at face value: its "the other 44" should read "the other 40".  The four exceptional declarations
it names, and their four axiom sets, reproduce here **exactly**.  The right check was
declaration-count against the file, not internal consistency of the sum.]**  This is a wave-78 one-liner of exactly the shape applied here.  For
calibration: six of the seven modules added since `4fff1592` carry pins (42, 54, 103, 48, 65, 94);
`GeneralCertificates.lean` is the only one that does not.  The convention is a *landing*
convention, not a tree-wide one, since 350 of 626 `GQ2/Dyadic` modules carry no pins.

### 2(b)  The LamFrames citation: the wave-75 repair was itself wrong

Ground truth at `1d3d5a84`, where the region is unchanged since wave 73:

| line | content |
| --- | --- |
| `:293` | first line of the cleared-**`v`** docstring |
| `:295` | `noncomputable def sqEichV` |
| `:300` | `variable (h) in` |
| `:301` | first line of the cleared-**`u`** docstring |
| `:303` | `noncomputable def sqEichU` |

Round 11 shipped `:301`, and W75 amended it to `:300`.  **Both are wrong, in opposite ways**, and
the amendment was the worse of the two: `:300` is a `variable` line and cites nothing, whereas
`:301` at least lands on the cleared-`u` docstring.  W75's finding is also wrong in its own
wording twice over, calling `:301` "the second line of the cleared-`u` docstring" (it is the
first) and calling `:293` and `:300` "the two definitions" (neither is).  A third defect nobody
raised: the original pair `:293`, `:300` was **mis-ordered**, since both shipped sentences list
`U_j` before `V_j` while `:293` is the `V` site.

**Applied.**  Both shipped sites now cite the definitions, named, in the sentence's own order:

* `GQ2/Dyadic/SqCore/GradedClassFourCompose.lean:420-421`, verbatim before:
  ``(the same convention as `cfourCmp_comm_eichU`/`cfourCmp_comm_eichV` above, and as
  `LamFrames.lean:293`, `:300`)``; now ``... and as `sqEichU`/`sqEichV`,
  `LamFrames.lean:303`/`:295`)``.  `mirror.sh check`: **OK**.
* `docs/dyadic/w73-knob-note.md:91`, same substitution, with a W77 annotation recording why.
* `docs/dyadic/w75-house-note.md` §4.2(e) annotated as **wrong at its source**, and its two
  disposition rows (`:77`, `:81`) annotated so the amendment is not read as sound.

Two sites already had it right and are untouched: `w74-func-note.md:139` (`295,303`) and
`w76-base-note.md:153` (the range `:295-306`).  `w75-house-note.md` is the only source of the bad
pair.

### 2(c)  The six note-level items: all six accounted for, two corrected against the ticket

| # | item | verdict |
| --- | --- | --- |
| 1 | "29 findings" tallies 28 | **AMENDED.**  29 is right; the *table* is short by one |
| 2 | "seven sites" vs §2's enumeration | **APPLIED.**  Seven *files*, nineteen sites |
| 3 | "Five further commits" is seven | **APPLIED.**  Confirmed by `rev-list` |
| 4 | stale line counts | **APPLIED** as as-of drift, plus a new counting trap |
| 5 | the `:1190` double-citation | **APPLIED.**  It is a defect, and a second one |
| 6 | "exactly four defs" | **APPLIED**, and it misses five, not one |

**1.  The "29" is right; the table is one short.**  `w75-house-note.md` §3.1's findings column
sums to **28** (5 + 6 + 7 + 7 + 2 + 1).  But round 11's own enumeration in `w74-house-note.md` §4
is §4.2 **(a)-(k)** = 11, §4.3 **(a)-(h)** = 8, §4.4 (a)-(g) = 7, §4.5's three background bullets
= 3, total **29**, with §4.1's four correctly excluded as self-applied.  The short row is
``| §4.3(a)-(g) | 7 |``, which drops **§4.3(h)**, a finding round 11 raised in its own right about
`w73-stratum-note.md:225`; it is currently absorbed into the "(same 7)" second-sites row, where it
is not a second site of anything.  §2's disposition table above it already lists §4.3(h)
separately, so the note contradicts itself.  **The headline needed no change**, and changing it to
28 would have been the wrong fix.

**2.  "Seven sites" is seven files and nineteen sites.**  `w75-house-note.md:20` verbatim: "The
predecessor annotated seven sites; four more were found by the tree-wide grep".  §2's own list
gives 1 + 5 + 1 + 1 + 1 + 3 + 7 = **19 sites in 7 files**.  "Four more" is right, being four sites
in four files, so a reader comparing 7 against 4 is comparing files against sites.

**3.  Five is seven.**  `w75-house-note.md:615` verbatim: "inheriting `47094a9c`.  Five further
commits".  `git rev-list --count f0a71688..0add6034^2` is **8**, less the inherited `47094a9c`,
leaving **seven**: `aa8b9f65`, `0012ce42`, `e22752e4`, `f03b6d1c`, `6eceb48c`, `e3e05329`,
`314c5bb2`.  The last two landed after the sentence was written.  The wave-76 lane hit the same
defect in its own record and corrected it twice (`11fbbd75`, four to seven, then to ten); its own
record is now exactly right, verified here: **10 commits, 5 Lean modules, 10 docs**, all three
matching `git diff --stat`.

**4.  The line counts, plus a trap that is new.**  All three figures reproduce **exactly** at
`f0a71688`, so the subsection measured correctly and only its tree moved: `GradedUniformTower`
pins 94 (unchanged), `GradedDeltaFunctionals` 1749 lines (now **1757**),
`EvenStratumRowFrame` 1077 lines (now **1088**).  Applied as as-of dating.

⚠ **Correction against the ticket, and a live trap.**  `GradedDeltaFunctionals.lean`'s pin count
is **103 at both trees, unchanged**.  A naive `grep -c '#print axioms'` now returns **104**,
because a docstring bullet was added at `:111` reading "**§9 Axiom pins.** One `#print axioms` for
each of the file's declarations".  The extra hit is prose.  The bijection is intact and exact:
103 declarations, 103 pins, none unpinned, no pin naming anything outside the file, no duplicate.
Anchor at column zero or the next recount will report a phantom pin and read the bijection as
broken.

**5.  The `:1190` citation is a defect, and there are two sites.**  `w75-house-note.md:506`
verbatim: "``gDelta_chiSq_sq_of_nuLam`` and ``gDelta_chiSq_of_nuLam``
(``GradedDeltaFunctionals.lean:1190``)".  **One line number for two declarations**, and it
resolves to only the second: at `f0a71688` the pair is `:1180`/`:1190`.  The other site, `:304`,
cites `:1190` for that declaration alone and was correct.  Both have since moved to `:1188` and
`:1198`.  Annotated with both readings.

**6.  "Exactly four `def`s" misses five, not one.**  `w75-state-note.md:151` verbatim: "`GQ2/`
contains exactly four `def`s whose value is a branch row's `WordCertificate`".  Counting `def`s
whose **return type** is a bare `WordCertificate`, at the note's own `f0a71688`, gives **nine**.
Beyond the four named and the one converter named: `Count/Routine.lean:463` **`pilotSubstitute`**
(the transformer the ticket names), and three the ticket does not, each a frozen branch-row
certificate in its field's namespace: `Instances/Sqrt2.lean:128`, `Instances/Sqrt5.lean:104`,
`Instances/SqrtNeg10.lean:126`.  Excluding those three while naming `sqrtNegTwoWordCertificate`,
which is equally frozen at `(α, h) = (2, 0)`, is inconsistent.  The **table** below the sentence
is unaffected; what fails is the word "exactly" and the sentence's claim to be a census.  A
tightened reading is proposed in the annotation rather than imposed, since the note is a wave-75
record.

---

## Ticket 3: watch round 14

### 3.1  Staleness, run first.  Three findings, and two are within-wave

**(a) HIGH.  The two wave-76 notes contradict each other about registration, and one of them was
already wrong at its own base.**  `docs/dyadic/w76-cert-note.md:220-221`, verbatim:

> **Registration.**  Neither `GeneralAssembly.lean` nor `GeneralCertificates.lean` is in
> `GQ2.lean` (lane protocol forbade editing it).  A later wave should add both.

Against `docs/dyadic/w76-house-note.md:452`, verbatim: "registration of `GeneralAssembly.lean` -
**done**, `a19fac5a`, see §3.3.  Struck".  The house note is right.  `a19fac5a` landed at 04:18;
the cert lane's base is `97d51e93` at 04:59 and **contains it**, so "Neither" was false at the
lane's own base, not merely overtaken.  `GeneralCertificates` was registered by `b1bc9d48` at
05:35, one minute after the cert note was committed (`edd7dd7a`, 05:34).  At `1d3d5a84` both are
in `GQ2.lean` (`:857`, `:858`), as is `SqCore/GradedJoinBase.lean` (`:777`, by `681ce981` at
05:37).  Nothing is left of the item.  Annotated at the cert note.
**[W78-HOUSE: the finding stands; two of the three line numbers have drifted.**  At `e6bbd2b9`
`GradedJoinBase` is still `GQ2.lean:777`, but `GeneralAssembly` is `:858` and
`GeneralCertificates` `:859`, because `7be6d122` inserted `import GQ2.Dyadic.SqCore.GradedBaseDecide`
at `:778`.  `Instances.FieldBranchIdentification` is `:860` (`f2ae3e20`).  A one-line grep of
`GQ2.lean` beats a line number here, exactly as this item recommends.]**

**(b) HIGH.  `w76-house-note.md` §4.2 breaks the very rule that note's §4.5 lays down.**
`:443` verbatim: "`w75-state-note.md` §6, five items, **all still live and none touched this
wave**".  Items 1 and 2 were both landed by the sibling cert lane, merged at `13791421` (05:35),
**five minutes before this note was committed** (`bcd27b83`, 05:40):

* item 1, the core transport, is `WordCertificate.genCertTransport`, `GeneralCertificates.lean:310`;
* item 2's compact-`N` producer is `genCertNWordCertificate` (`:499`) at free `(α, h, q)`, its
  canonical twin (`:553`), the procyclic-`M` lift `genCertMpcWordCertificate` (`:645`), and the
  `Npc` producer said here to be needed "from scratch", `genCertNpcWordCertificate` (`:727`).

The note's own §4.5 is titled "Run the staleness check before the application pass, not after",
and diagnoses precisely this.  It ran the check over *its own edits* and not over the queue
section.  The residue is **one and a half items**, not five.

**(c) MEDIUM.  `w75-state-note.md` F2 is overtaken on three of five rows, by a module that cites
F2 by name.**  F2's headline, "The CAND layer has a free-parameter producer on one row out of
five", is no longer true: it is four of five, `L h` over `D_sq h` remaining the exception.
`GeneralCertificates.lean:705-711` quotes this note ("§3.1 (F2) records `Npc` as the one row with
**no** `CAND` producer at all") and then builds the producer, so the supersession is documented
on one side only.  The four new producers have the same posture as `mWordCertificate`
(clauses as hypotheses), so the comparison is like for like.  Two qualifications survive and are
recorded so they are not lost: the `Npc` producer is at the single display `⟨1, 1⟩`, and none of
the four is unconditional.  Annotated at the state note.

### 3.2  Interface blindness: what this wave's siblings settle

**(a) MEDIUM.  `3 + 2h` overstates the residual family by one, at every `h`.**  The W76-BASE
headline (`:18`) and `GradedJoinBase.lean`'s module docstring both count the family as `3 + 2h`
brackets `⁅⁅x₁, letter⁆, x₁⁆`.  The third non-handle letter is `x₁` itself and
`⁅⁅x₁, x₁⁆, x₁⁆` is trivial on the nose, so the genuine family is **`2 + 2h`**.  The sibling
decide lane proves exactly this, at every `h`, in one line
(`gDecide_triple_self`, via `cfour_comm_self` and `cfour_one_comm`), and derives
`GBaseXOneTriple 0 nu' ↔` the two classes at `σ` and `x₀`.  ⚠ Not in the tree at `1d3d5a84`;
flagged for wave 78 to reconcile when the sibling lands.  §4 and "What W77 needs" already use the
right number ("two layer classes"); it is the headline and the module that carry `3 + 2h`.

**[W78-HOUSE, ticket 2: RECONCILED, and this round's prediction was exact.**  The sibling landed
at `7be6d122` (merge `294a197a`).  `gDecide_triple_self` is at `GradedBaseDecide.lean:54`, at
every `h`, proved by `cfour_comm_self` then `cfour_one_comm`, and
`gDecide_residual_zero_iff` (`:64`) is the `h = 0` equivalence with the two classes at `σ` and
`x₀`.  Corrected in the tree at `GradedJoinBase.lean:72`, `:627` and `GradedBaseDecide.lean:11`;
annotated at `w76-base-note.md:18` and its item 2.  One qualification the fix carries that this
round's wording did not: `GBaseXOneTriple` is *indexed* by all `3 + 2h` letters, so the corrected
prose says `2 + 2h` **with content** rather than simply `2 + 2h`.]**

**(b) Recorded.**  The field lane's `Instances/FieldBranchIdentification.lean` is at §0 only, the
two already-closed rows restated; §§1-4 are planned in its docstring but not written.  Flagship
item 1 is therefore **in flight, not closed**, and wave 78 should not read the w76 queue's
"still the smallest genuinely-open item" as discharged.

⚠⚠ **[W78-HOUSE, ticket 3, STALENESS: HIGH.  This was already false when it was committed, and
it is the exact defect §3.1(b) above diagnoses in the predecessor.**  Timeline, all `08-15`:

| time | commit | state of the field module |
| --- | --- | --- |
| 06:06 | `62a8c05b` | opened, 126 lines: §0 only.  **This is the state described above.** |
| 06:14 | `dddd3734` | 398 lines, the residue-5 criterion and the three norm witnesses |
| 06:16 | `4e4a6541` | 544 lines, **all three remaining rows closed** |
| 06:22 | `c9881c4c` | 746 lines, the five rows composed into `GenAsmBranch` |
| 06:25 | `234ff5f1` | **merged into `dyadic`** |
| 06:28 | `9443a52b` | *this note is committed* |

So the module was complete and **already in `dyadic`** three minutes before this note recorded it
as unwritten.  The read was taken at lane start and never refreshed, which is precisely what
§4.5's rule (run staleness before the application pass) exists to prevent; this round applied that
rule to its own edits and to the w76 queue, and not to its own §3.2/§4.2 sibling readings.  The
correct finding is the opposite one: **flagship item 1 is closed at all five rows**, and the
verdict on it is in §4.2's annotation below.]**

### 3.3  Identity headlines over containments: one found

**MEDIUM.  `GradedJoinBase.lean` proves one direction and two docstrings claimed an identity.**
Verbatim before, at `:619-620`:

> ⭐⭐⭐ **`GJoinBase h` from the residual.**  Wave 75's first named input is exactly the
> `3 + 2h` brackets `⁅⁅x₁, letter⁆, x₁⁆`, at every selected marking.

and at `:71-72`: "So wave 75's first named input is now the `3 + 2h` brackets ..., **and nothing
else**."  Wave 75's first named input *is* `GJoinBase h`, so both sentences read as
`GJoinBase h ↔` the brackets.  What is proved is `gBase_joinBase_of_residual : GBaseResidual h →
GJoinBase h`, and no converse is in the file.  `gBase_residual_iff` is not one: it equates two
spellings of a single class at a fixed `c`.  The direction that fails matters here, because §4 of
the lane note argues for falseness; §4 is careful and argues directly that
`GTowerLayerReach h ν' 2` fails, which does reach `GJoinBase`, but a reader who took the docstring
literally would think refuting the brackets suffices.  **Corrected** to "discharged by", with the
direction and the non-converse spelled out.  `mirror.sh check`: **OK**, 48 pins, all exactly
std-3.  This is the fourth instance of the pattern in three rounds and the second in the
`SqCore/Graded*` family; the checklist item is earning its place.

`GeneralCertificates.lean` came up **clean** on the same scan: its three identity-flavoured
docstrings (`:392-400`, `:493-498`, and the `n = 1` acceptance test) all sit over statements that
are equalities or over descriptions of binders, and each checks out.

### 3.4  The specific check: the §4 falseness labelling is sound

Audited at every site a reader could take the argument for a theorem, and it holds at all of them:
the title (`:1`, "the case that it is false"); the Headline (`:18-19`, "the **argument** of §4
says"); the §4 heading (`:115`) with "**This is an argument, not a theorem**" immediately under
it, naming Labute's theorem and saying it is **not formalized in the tree**; the conclusion
(`:161-163`), stated as "**If** Labute's structure theorem holds for `D_sq h`, ..."; and the four
honesty markers, the third of which says a Lean refutation "needs the graded structure theorem,
which the tree does not have".  **No site states the falseness flatly.**

Checked outward, also clean.  `GradedJoinBase.lean` contains **one** occurrence of "false"
(`:45`), about the graded slogan `ad (x^{[2]}) = (ad x)²`, not about the residual; **no docstring
presents `GBaseResidual` as false**, and `:74-76` says the opposite outright.  The owner memo's
wave-76 block hedges correctly ("recorded as an argument rather than a theorem").  A tree-wide
grep of `docs/` finds no unhedged restatement.

One suggestion rather than a defect, recorded at the note: the Headline says the argument "says
that family is false" without saying that it rests on an unformalized structure theorem, and that
qualification is ninety lines further down.

### 3.5  Round 13's own work: re-verified, and it is clean

All five citation repairs of `0dbfe9b7` resolve exactly at `1d3d5a84`:
`cfiveJoin_ad_far_lambdaTwo` `:157` and `cfiveJoin_ad_far_all` `:278`
(`GradedClassFiveJoin.lean`); `MarkedCoreRealization` at `LabuteInterface.lean:313` with `:308` a
`variable` continuation as reported; `candidate_equiv_galK_of_supply` at `KSupply.lean:451`, after
`end KSupply` at `:380`; `gTowerTowXW` at `GradedUniformTower.lean:935`; `ztwoIota_lNu` at
`GammaLSylowPreimageRealizationBypass.lean:82`.  The `747d71b6` identity-headline annotation on
`gJoin_reach_le` is correct and well scoped.  The counts corrected by `11fbbd75` are now right.

### 3.6  What came up clean

Said in detail, because a round that reports only hits is not a check.

* `GradedJoinBase.lean`'s preamble reproduces exactly: **48 declarations, 48 pins**, a bijection,
  and every one prints exactly `[propext, Classical.choice, Quot.sound]`.
* `w76-cert-note.md` §6's axiom posture accounts for 1 + 1 + 44 + 1 + 1 = **48**, matching the
  file's 48 declarations.  (The pins themselves are not in the file; see §2(a).)
  ⚠ **[W78-HOUSE: WRONG, and it is a miss of this checklist item.**  The file has **44**
  declarations.  The sum was checked for internal consistency and never against the file, so a
  bad summand ("the other 44", which should be "the other 40") was ratified as a count.  The
  *content* of §6 is right: the same four declarations, the same four axiom sets, confirmed by
  the 44 pins now in the file.  A sum that agrees with itself is not a count.]**
* `w76-house-note.md`'s verification record is exact: 10 commits, 5 Lean modules, 10 docs, all
  three confirmed against `git diff --stat 97d51e93 e9f4d79f^2`.
* `w76-cert-note.md` §5's coverage table agrees with the tree row by row, including the two
  qualifications (`Npc` at `⟨1, 1⟩`; `N0` with no `α` bound).
* No em-dash was added to any prose in this lane; no line over 100 characters was added to any
  Lean file.

---

## Ticket 4 (report only): the shape of the W78 queue

### 4.1  The decide fork, and what each outcome leaves

The sibling lane is deciding `GBaseResidual` at `h = 0`, where the family is two classes,
`⁅x₁, σ⁆²` and `⁅x₁, x₀⁆²`.  Note first what is **invariant across all three outcomes**:
`GJoinSeparationAll h` and `GTowerKnobRealizable h` are the other two inputs of
`gBase_markTransitivity_of_residual`, they are independent of the base, and no outcome touches
them.  Whatever the fork returns, §4.3 below is still the wave-78 work.

1. **The two classes are reachable (§4 refuted).**  `GJoinBase 0` follows.  What is left is the
   step from `h = 0` to general `h`: the decide lane's construction would have to be run at the
   `2 + 2h` family, and the note's §4 counting argument says the obstruction it identifies is
   dimension-`2` at every `h`, so a positive answer at `h = 0` does *not* transfer for free.
   Expect a second ticket, not a closure.
2. **The two classes are unreachable (§4 confirmed inside Lean).**  `GJoinBase h` is false and the
   depth-`2` base is dead.  The re-cut is already scoped: `gTower_layerReach_of_base` runs from
   **any** `k ≥ 2`, and the note argues the depth-`2` counting does not repeat at depth `3`,
   because the admissible corrections' square parts then range over the row-trivial part of `γ₂`,
   far larger than `W`.  The wave-78 ticket is §§1-4 of `GradedJoinBase.lean` re-proved at
   `k = 3`, the only change being which `y ∈ gr₃` are row-trivial.  This is the outcome to plan
   for, since it is the one the argument predicts.
3. **Undecided.**  The finite class-`4` quotient of `D_sq 0` does not separate the classes, or is
   too large to decide.  Then the residual stays open exactly as wave 76 left it, and the third
   route in the note's "What W77 needs" becomes the live one: enlarge the inventory by admitting
   corrections whose square part is row-trivial only *modulo 2*, which grows `W` to all of `V` and
   closes the gap.  That is a question about `sqArbFrame`'s dressing clauses, not about the layer,
   so it is a different lane's subject matter.

### 4.2  The field lane's leftovers

The lane closes the three `DM 2 0` rows (`ℚ₂(√5)`, `ℚ₂(√10)`, `ℚ₂(√−10)`) by a single criterion,
one cyclotomic value `≡ 5 (mod 8)`, which excludes `imChiN 2` and `imChiM 3` together; the other
two rows were already closed at waves 67 and 68.  When it lands, flagship item 1 is discharged
**for the five frozen quadratic rows**.  What that does not do:

* it does not give the `α` pin at a general ramified-`i` `K`, which is what the general-degree
  statement needs.  The criterion is stated per field and its witnesses are explicit elements
  (`1 + 2√5`, `2 + √10`, `√−10`);
* the module is at §0 at `1d3d5a84`.  Wave 78 should confirm §§1-4 landed before treating item 1
  as struck, and should not inherit the w76 queue's description of it.

**[W78-HOUSE, ticket 3: CONFIRMED LANDED, and the second bullet is doubly wrong.**  The module
does not exist at `1d3d5a84` at all (`git cat-file -e` fails there); it is created by the field
lane, and by the time this note was written it was at 746 lines with all eight sections written.
See §3.2(b)'s table.  The first bullet **stands and is the important half**: the pin is per
field, by explicit witnesses, and gives nothing at a general ramified-`i` `K`.

**Verdict on the memo's Group A, checked item by item against `w74-critical-path.md` §3.**

* **A1 (branch identification per field): DISCHARGED at the five frozen quadratic rows.**
  `fieldId_hrange_sqrt{Five,Ten,NegTen}` prove `range chiCycKTwo = imChiM 2`, and the two older
  rows are re-exported.  All five are over the field's own `MarkedRecip` bundle, and the
  range identities print std-3, so the pin costs no arithmetic axiom.
* **A2 (the `KTwoN`/`KTwoM` adapter into the two record spellings): BYPASSED, not discharged.**
  The field lane's producers land in `GenAsmBranch K B`, which is `GeneralAssembly.lean`'s own
  record from **wave 76**, not in `Main.lean`'s `ResidualSqrtNegTwo` or the four `ResidualSqrt*`
  records that A2 names.  `Main.lean:352`'s pilot record still carries `fLab`, `piAb`, `hpiAb`,
  `hpiNu` and `horient : ∀ x, chiCycKAb K (piAb (fLab x)) = chiN 2 0 x`, the abelianization
  spelling, exactly as the memo found it at `4fff1592`; `grep` finds `GenAsmBranch` in two files
  only, `GeneralAssembly.lean` and `FieldBranchIdentification.lean`.  What performs the adapter
  is `KSupply.ofMarkedCoreRealization` inside `genAsm_candidate_equiv_galK`, plus §4.2's record
  map, and both predate this lane.  So the memo's own test, "until it is done the even route's
  output does not typecheck into either record", is **still failing for `Main.lean`'s records**,
  and A2 is discharged only on the new general-record path.
* Consequently the field note's "Group A is now empty of open mathematics" is **true on the
  general path and false on the committed one**.  It is not open *mathematics* either way (A2
  was always priced as a restatement), so the disagreement is about which records the campaign
  intends to ship, and that is an owner call, not a lane's.]**

### 4.3  Separation and realizability: untouched for three waves

Both are hypotheses everywhere in the tree; neither has a producer.

* **`GJoinSeparationAll h`** (`GradedUniformJoin.lean:994`), the `𝔽₂`-independence bookkeeping.
  Proved at `h = 0` (`:891`, `GJoinTowerSeparation 0 nu' k`).  The join note scopes two routes and
  calls each lane-sized.  This is the cheapest of the three graded items and the one most likely
  to close in a single lane.
* **`GTowerKnobRealizable h`**, wave 74's extraction interface, untouched by three waves now.  The
  ENGINE note's mod-2 far-slot route is still unexamined; `gJoin_chi_far` is the likely tool, in
  its corrected containment form.

Neither depends on the decide fork.  If the orchestrator wants a lane whose value does not turn on
an undecided question, these are the two.

### 4.4  The flagship's seven remaining items, once branch identification moves

`w74-critical-path.md`'s eight, less item 1:

* **item 5 with `hdet`** (item 7's named residual), the Gauss-`Z` determinant residue.  Schedule
  as one: the only place both sides of the two-sided architecture are carried and neither has a
  supplier lane.  ⚠⚠ both sides.  **The sharpest item on the list.**
* **item 3**, `ExactLiftingSemantics` at `G_K`, narrowed to one existential.
* **item 4**, `StokesDualityCertificate` at `G_K`.
* **item 6**, the four certificate-to-count bridges at `GammaR n q word`, four statements, uniform
  in the row.
* **item 7's other three**, `hsimp` (`PilotHsimp`) and `hsplit`/`hZcount` (`stageR136`).  `hsimp`
  is the high-leverage one.
* **item 2**, the `KTwoN`/`KTwoM` adapter, a restatement.
* **item 8**, the `nuP` construction for the four `M` rows, a build, hand-verified satisfiable.

One correction wave 78 should carry: **items 3, 4 and 6 are now the uniform residual on four even
rows rather than a per-row obligation**, because `GeneralCertificates.lean`'s four producers all
take the same four analytic clauses.  `w76-cert-note.md` §7 item 3 names the concrete next step,
closing the degree-spelling mismatch between `Instances/N0Exact.lean`'s `exactLifting` at
`2*h+2` and the record's `2+2*h`, "a cast, not a gap".

### 4.5  The owner items

* **The plan-A6 freeze on `GQ2/Roe/*`** is still open, carried from round 11 through W75 §8 item
  6, W76 §4.4 and this round.  Untouched here: nothing under `GQ2/Roe/` was touched.  **The oldest
  live owner item in the campaign.**
* **The 100-character question.**  Now recorded in the owner memo as a wave-76 minor item.  This
  lane held to 100 voluntarily and added no over-long line.  The state remains the least good one:
  no policy, but lanes behaving as though there is one.
* **Two owner calls carried from round 11 and W75, still untouched**: `chifree-clearing-note.md`'s
  rewrite, and `mc-design.md`'s third `q`.
* **`w75-house-note.md` §5.2's class-five mod-16 kit**, carried forward intact with its two
  scoping corrections.
* **New, small, and mine**: `GeneralCertificates.lean`'s 48 unrecorded pins (§2(a)), and the
  `3 + 2h` versus `2 + 2h` reconciliation once the decide lane lands (§3.2(a)).
  **[W78-HOUSE: BOTH STRUCK.**  The pins are recorded (`d19eb316`) and the reconciliation is
  applied (§3.2(a)'s annotation).  ⚠ **The pin figure was wrong**: the file has **44**
  declarations and now carries 44 pins, not 48.  48 is `w76-cert-note.md` §6's
  `1 + 1 + 44 + 1 + 1`, whose "other 44" should read "other 40"; this round checked that the sum
  was internally consistent and did not check it against the file.  See §3.6's third bullet.]**
* **New process suggestion, from ticket 1.**  Two independent auditors have now fallen into the
  `public import` trap.  The walk that avoids it is fifteen lines of Python.  Committing it under
  `scripts/` would make the next reachability audit mechanical rather than a matter of remembering
  `w72-house-note.md` §1.0.  Not created here: a comment-only lane should not add a script.

---

## Verification record

* Lane `claude/w77-house`, base `1d3d5a84`.  **Seven commits**, all path-limited, the last of
  them the one that sets this figure.  **Not pushed.**
* **No `lake` command was run**; `scripts/check_dyadic.sh`, `scripts/check_axioms.sh` and
  `scripts/check_ledger.sh` were not run.
* `scripts/mirror.sh sweep` once at lane start (**5883 artifacts**), then `scripts/mirror.sh
  check` on every edited Lean file after every edit.  **All three modules `OK`**, no errors, no
  warnings:

  ```
  GQ2/Dyadic/GeneralAssembly.lean               OK   (42 pins printed)
  GQ2/Dyadic/SqCore/GradedClassFourCompose.lean OK
  GQ2/Dyadic/SqCore/GradedJoinBase.lean         OK   (48 pins printed)
  ```

* **Comment-only discipline, verified mechanically.**  Each edited `.lean` file was
  comment-stripped (nested block comments, docstrings and line comments removed, string literals
  respected, whitespace collapsed) and compared against its content at the lane base `1d3d5a84`:

  ```
  GQ2/Dyadic/SqCore/GradedClassFourCompose.lean   IDENTICAL
  GQ2/Dyadic/SqCore/GradedJoinBase.lean           IDENTICAL
  GQ2/Dyadic/GeneralAssembly.lean                 one pure addition, 0 deletions
  ```

  For `GeneralAssembly.lean`, the wave's one non-comment edit and the lane's stated exception, the
  stripped diff is a **single addition hunk** with **zero deletions and zero modifications**, and
  the only tokens it adds besides the 42 `#print axioms` lines and their declaration names are
  `section`, `AxiomPins` and `end`.  So no statement, term, binder, name or proof changed anywhere
  in this lane.
* `GQ2.lean` was not touched.  Nothing under `GQ2/Roe/` was touched (plan A6).  Neither
  `SqCore/GradedBaseDecide.lean` nor `Instances/FieldBranchIdentification.lean` was created or
  touched; both were read from their sibling branches with `git show` only.
* No line over 100 characters was added to any Lean file.  No em-dash was added to any prose.
* Ticket 1's walk was run against `git archive` extractions of `4fff1592` and `f0a71688`, so it
  never saw a working-tree edit.

## Files edited

**Lean (3):** `Dyadic/GeneralAssembly.lean` (pins block added),
`Dyadic/SqCore/GradedClassFourCompose.lean` (comment-only),
`Dyadic/SqCore/GradedJoinBase.lean` (comment-only).

**Docs (9):** `w77-house-note.md` (new); `w73-knob-note.md`, `w74-critical-path.md`,
`w74-house-note.md`, `w75-house-note.md`, `w75-state-note.md`, `w76-base-note.md`,
`w76-cert-note.md`, `w76-house-note.md`.
