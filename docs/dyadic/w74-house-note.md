# W74-HOUSE: the critical-path trace, round 10 + the background sweep applied, and watch round 11

Lane `claude/w74-house`, base `4fff1592`, cache at `608d3ded`.
Verification of record: `scripts/mirror.sh` (sweep, check).  **No `lake` command was run**, and
`check_dyadic.sh` was not run either (wave 73 established that its default path invokes
`lake env lean` twice through `check_axioms.sh`).

## Headline

**Ticket 1.**  The dependency memo is `docs/dyadic/w74-critical-path.md`, summarised in §1 below.
Two results worth the orchestrator's attention:

> **The `alpha = 1` even stratum is OFF the critical path, and the conclusion is stronger than
> the briefing's.**  The `alpha = 1` point is not merely unused: it is **provably outside the
> standing ramified-`i` hypothesis**, by three committed statements and no unproved input.  I
> composed them and ran `mirror.sh check`: both compositions elaborate and print std-3.  But the
> briefing's *reason* is not the tree's, and is weaker.  Three corrections in §1.3.
>
> **The pilot row is one producer-generation behind.**  `ResidualSqrtNegTwo` carries three fields
> (`piAb`, `hpiAb`, `hpiNu`) that exist only because `SqrtNeg2.lean` calls the *abelianization*
> producer `marked_matching_certificate_KN`.  `LabuteInterface.lean:67`'s
> `marked_matching_certificate_KTwoN` needs none of them, and its orientation clause is exactly
> the shape the even route produces.  Statement change, so reported and not made.

**Ticket 2.**  All **38** reported findings applied or adjudicated: round 10's 29 (batch A) and
the nine background-sweep findings (batch B).  Every one re-verified against the Lean or the git
history before applying.  **All nine of batch B checked out**, three with corrections to the
finding itself (§3).  Batch A's applications are tabulated in §2.

**Ticket 3.**  Watch round 11 over the wave-73 landings: **33 findings** (3 high, 6 medium, 12
medium-low, 9 low, plus 3 background items outside the round's scope).  Four are applied here
because they are the second half of a ticket-2 fix; the other 29 are **reported for wave 75**,
which is the campaign's rhythm.  §4.  The one to read first:

> **The ledger gate's fixture hook can make `check_dyadic.sh` print "all checks passed" with no
> `lake` run**, contradicting both the script's own comment and the wave-73 house note, which say
> it "can never be used to make the gate appear to pass".  The `SKIP: L1` line is visible in the
> transcript, but the script still exits 0 and D6 reads only the exit code.  §4.4(a).  Fixing the
> *script* is a behaviour change and is not proposed; the prose is.

**Ticket 4.**  The two `q`s, `qOf K FF = 2^f` (residue cardinality) against `demushkinQ`
(abelianization torsion): §5.

---

## 1.  Ticket 1: the critical-path trace

Full memo: `docs/dyadic/w74-critical-path.md`.  What follows is the part the orchestrator needs
in one screen; the memo carries the field-by-field tables and every citation.

### 1.1  The shape

`ramifiedI_candidate_equiv_galK` (`Main.lean:670`) is one `cases` over `FrozenQuadRow` onto five
`rowEquiv_*` theorems, each of which is one instance headline re-read off the record.  There is
**no derivation between the records and the conclusion**, so the critical path is exactly
`FieldInputs` (6 fields) plus the five records: the pilot's 13, and 17 leaves per `M` row (9
fields, of which `KS : KSupply` expands to 9 more).  Recounted at this tree.

The five row cores are `DN 2 0`, `DM 3 0`, `DM 2 0`, `DMpc 2 1 0`, `DMpc 2 1 1`.  **Every row is
at `alpha >= 2` and at handle count `h = 0`.**  That single fact does most of the work below.

### 1.2  (a) Who owes what

Four workstreams.  Condensed:

| workstream | fields it owes | where |
| --- | --- | --- |
| **classification** (even route at even degree, sq/graded route at odd) | pilot `fLab`/`horient`/`hpair` (+ `piAb`/`hpiAb`/`hpiNu`); `KSupply.pro2`/`hpro2`/`ker_pro2`/`nu_compat` | 7 + 4 |
| **ASK** (`KSupply.lean`) | `hexact`/`hstokes` on the pilot; `exactLifting`/`stokes`/`determinant` inside each `KSupply` | 2 + 3 |
| **candidate-side clauses** | pilot `hsimp`/`hsplit`/`hZcount`/`hdet`; each `M` row's `exactLifting`/`stokes`/`scalar`/`determinant` and its `nuP` block | 4 + 8 |
| **already proved / pins** | `T`, `params*`, `ramifiedData`, `hdeg`, `hhom` | |

`ramified` is not on any workstream's list: it is the hypothesis that *selects* `K`.

### 1.3  (b) The `alpha = 1` decision: the orchestrator's conclusion is right, its reason is not

**Mechanically**: `GQ2.Dyadic.Main`'s transitive import closure is **427 of 930** `GQ2` modules,
and it contains none of `EvenStratumPoint`, `EvenStratumFrame`, `EvenStratumShift`,
`NFrameAlphaOne`, `EvenAlphaOne`, or any `SqCore/Graded*` module (68 of them).  That settles
"consume" literally but not usefully, since the records are hypotheses the classification
workstreams exist to discharge from outside.

**Mathematically**, and this is the real answer: a ramified-`i` field is **never** on the third
stratum, so the `alpha = 1` point is outside `FieldInputs.ramified` outright.  Three committed
statements:

1. `evenUnram_imChiN_eq_prin_iff` (`EvenUnramified.lean:236`) at `a = 1, alpha = 2`:
   `imChiN 1 = evenRangePrin 2`.
2. `evenUnram_range_eq_of_oriented` (`:117`) + `range_chiN` (`OrientationCorrection.lean:209`):
   an oriented equivalence with `chiN 1 h` forces `range chiCycKTwo = evenRangePrin 2`.
3. `evenRangeF_hasEqualNormValueGroups_of_range_eq_prin` (`EvenRangeModelFields.lean:890`),
   docstring *"The third stratum is exactly the unramified one"*: that range gives
   `HasEqualNormValueGroups K deltaI` for **every** `deltaI`, the literal negation of `ramified`.

I composed these into `w74_orientedN_one_forces_unramified` and
`w74_ramified_excludes_alphaOne` and ran `scripts/mirror.sh check`.  Both elaborate; both print
`[propext, Classical.choice, Quot.sound]`.  The check file is a lane artefact and was **not**
added to the tree (plan A6 freeze; the three sibling lanes own this wave's new modules).

**Three corrections to the briefing:**

* **(i) The `demushkinQ` route is conditional, the stratum route is not.**
  `demushkinQ (D_N 1 h) = 4` is unconditional (`NFrameAlphaOne.lean:614`), but
  `demushkinQ (G_K(2)) = 2` at a ramified-`i` field is **not**: `EvenDemushkinQ.lean:149` carries
  `hrecip : Function.Injective (proTwoReciprocityToTopAb B)`, completed-reciprocity injectivity,
  itself unproved.  So the briefing's argument buys the conclusion on credit; §1.3's does not.
* **(ii) "forcing `i ∈ K`" is not a tree implication.**  `EvenUnramified.lean:429`-`432` records
  explicitly that this direction *"is not available and is not true"*: a `K` with `K(i)/K`
  unramified quadratic has `i ∉ K`.  The tree has `i ∈ K ⟹ stratum` and `stratum ⟹ unramified`;
  the composite that matters never passes through `i ∈ K`.
* **(iii) `alpha = 1` is an `N`-only phenomenon.**  At `alpha = 1` the `M` row has
  `demushkinQ = 2`, the *same* as a ramified-`i` field (`EvenForwardRouteSkeleton.lean:85`-`87`),
  so the `q`-invariant argument does not exclude the `M` branch there at all.  What excludes it
  is `evenUnram_isEmpty_orientedM`: `imChiM a` contains `-1` and `evenRangePrin alpha` omits it.

**Verdict: the `alpha = 1` work is classification-completeness, and can be scheduled as such.**
Two caveats.  It remains load-bearing for the *paper*: `evenUnram_classification_conclusion_false`
(`EvenUnramified.lean:361`) shows the ramification binder on `parityFinal_evenClassification` is
necessary, and the stratum work is what locates that boundary.  And the same argument retires the
`alpha >= 3` third stratum too, so the programme's remaining value is entirely at the one
surviving point.

### 1.4  (c) The honest remaining-work list

A preliminary that changes how the list reads: **"close every record at every ramified-`i` `K`"
is not achievable and should not be the goal.**  `fLab`/`horient`/`hpair` and
`KSupply.pro2`/`hpro2`/`ker_pro2`/`nu_compat` *assert* that `G_K(2)` is the row's specific core at
the row's specific `(alpha, h)`.  No theorem supplies those at an arbitrary ramified-`i` `K`,
because such a `K` of the wrong degree or branch is not that row's field.  The achievable goal is:
close every record at every ramified-`i` `K` **that the row's branch identification places on that
row**.  Eight items:

1. **The branch identification per field**, `range chiCycKTwo = imChiN alpha` (resp. `imChiM`).
   The even route's output is *existential* (`parityFinal_evenClassification`: `∃ alpha >= 2`,
   `M ∨ N`); this is what pins it to the row.  `parityFinal_orientedEquivN_sqrtNegTwo`
   (`EvenParityModel.lean:257`) already takes it as `hrange`.  **Smallest genuinely-open item;
   gates all five rows.**
2. **The `KTwoN`/`KTwoM` adapter** into the two record spellings (§1.2 headline).  A restatement,
   not open mathematics, but until it exists the even route's output does not typecheck in.
3. `ExactLiftingSemantics` at `galKProfinite K`, `KSupply.lean:256`-`260` narrows this to **one
   existential**, the `K` analogue of `RadicalEdgeLocal.exists_good_twist`.
4. `StokesDualityCertificate` at `galKProfinite K`.
5. `AffineDeterminantCertificate` at `galKProfinite K`, the **LG5 ⇒ `GaussZResidueK` bridge**.
   ⚠⚠ `KSupply.lean` is explicit that this has **no `K` clone** and that inlining a hypothesis
   named after LG5 would have hidden the gap.
6. The four candidate-side analytic clauses at `GammaR` (AS1 divergence 4).  Uniform in the row,
   so four statements, not sixteen.
7. The pilot's four named residuals: `hsimp`, `hsplit`, `hZcount`, `hdet` (⚠⚠, no supplier lane).
8. The `nuP` block for the four `M` rows (ticket AS3-b), a build, not a proof.

**Sharpest single item: 5 / `hdet`.**  The Gauss-`Z` determinant residue is the only place where
*both* sides of the two-sided architecture are carried and neither has a supplier lane.

**Explicitly not on the list**, and worth saying out loud: the `alpha = 1` stratum;
`SqClassClearingSupply h k` at any class and `SqLamMarkTransitivity h` at any `h >= 1` (the
frozen table is `h = 0` on `M`/`N` cores, while the `Sq` core serves the `L` row / odd degree,
whose certificate is already unconditional); and `demushkinQ (G_K(2)) = 2` as such, which is a
hypothesis of the superseded `abstractEquiv_KTwoN/M` adapters (`LabuteInterface.lean:200`) and not
of the even route.

---

## 2.  Ticket 2, batch A: round 10's 29 findings

All 29 applied.  Every one was re-verified against the Lean before the edit, and **all 29 checked
out at the level of the defect**.  Two needed the finding itself corrected; one site turned out to
have been fixed already.

### 2.1  Where they landed

| source | findings | file | applied |
| --- | --- | --- | --- |
| §3.1 (a), (b), (h), (i), (l) | 5 | `SqCore/GradedClassFourDefect.lean` | 5 |
| §3.1 (d), (e), (f), (g), (j), (k), (m), (n), (o) | 9 | `SqCore/GradedClassFiveKnob.lean` | 9 |
| §3.1 (c) | 1 | `Instances/EvenStratumFrame.lean` (2 sites) | 1 |
| §3.2 (a)-(e), (g)-(i) | 8 | `SqCore/NuSeeds.lean` | 8 |
| §3.2 (f) | 1 | `docs/dyadic/chifree-clearing-note.md` | annotated, not rewritten |
| §3.3 (a)-(d) | 4 | `Instances/EvenStratumFrame.lean` | 4 |
| §3.4 (a) | 1 | `docs/dyadic/w72-stratum-note.md` (+ owner memo, already fixed) | 1 |

### 2.2  The three worth reading

**(i) The misplaced ⭐⭐⭐ docstring is moved, and the theorem under it got one.**
`GradedClassFourDefect.lean`'s ⭐⭐⭐ display stated `cfourDef_leftover_reduce`'s conclusion while
sitting on `cfourDef_relator_step`, which evaluates nothing and never calls `cfourDef_assemble`.
The display is now on `cfourDef_leftover_reduce`, and `cfourDef_relator_step` has a docstring
saying what it does: the correction pushed through `cfourId_dress_core` and `cfourId_leftover_eq`,
with the three correction factors still unevaluated.  Round 10's suggested fourth checklist item
("a docstring can be attached to the wrong declaration") is what found this; **it is worth keeping,
and round 11 ran it over the wave-73 landings**.

**(ii) "Five of the leftover's factors" is now right in all four places.**  Two of the five are
knob-internal and are not factors of the leftover: against `cfourKnob_leftover_eq`'s right-hand
side, `⁅⁅A, x₁⁆, A⁆` and `⁅⁅x₁, A⁆, x₀⁆` do not appear at all.  Corrected at
`GradedClassFourDefect.lean:53` and the moved display, and the column of
`w72-defects-note.md`'s table is retitled (batch B finding 5).  The module already had it right at
`cfourDef_assemble`'s own docstring, which is what made the diagnosis cheap.

**(iii) Round 9's "no side condition" defect, corrected at class four last wave, is corrected at
class five here.**  `GradedClassFiveKnob.lean`'s two `_dsq` headlines now read "with the closedness
side conditions discharged", which is what the module header said all along.  This is the third
consecutive wave in which grepping a corrected phrase found the same defect elsewhere.

### 2.3  Corrections to the findings themselves

* **§3.2(b) undercounts its own evidence.**  It says "§2's four declarations"; §2 has **five**
  (`SqNuAdmissible`, `SqNuAdmissible.nu_x1`, `sqNuAdmissible_nuSq`, and *two* unbundlings, which
  the finding itself enumerates).  The substance stands: none of the five is a necessity claim, so
  "exact" / "pinned exactly" is unsupported.  The count is not reproduced in the file.
* **§3.1(d) is a satisfiability finding, not a count finding**, and the applied text now says so.
  `hX` asks the far-slot set to generate topologically, and five letters cannot do that once
  `sqRank h = 3 + 2h > 5`, so the "five frame letters" reading leaves `cfiveSpan_ad_far_of_gens`
  with an unsatisfiable hypothesis at every `h ≥ 2`.  That is why the module header mattered even
  though the theorem's own docstring ("the finitely many frame letters") was already correct.
* **§3.4(a) had three live sites, not four.**  `owner-items-2026-08-05.md` was corrected by the
  owner at `f4a458a8`, in the same commit as the "seven waves" fix.  Two Lean sites and one note
  site remained and are done.
* **Line-number drift**, recorded so the next round does not re-derive it: §3.3(a)'s and §3.3(d)'s
  citations, and §3.1(m)'s `GradedGammaFourFive.lean:424` (the declaration is at `:432`).

### 2.4  What was reported and not applied

* **§3.2(f), `chifree-clearing-note.md`, stays an owner call.**  It is a 2026-08-05 lane record of
  what was *proposed*, and two modules have landed against it since (`NuSeeds.lean` the same day,
  `NuSeedWide.lean` 85 minutes later).  Rewriting the body would destroy the record; the file now
  carries a stale-banner naming both modules and saying which of its imperatives have been
  overtaken.  Round 9 flagged it, round 10 found the second module, and it is still not a lane's
  call to rewrite.
* **Nothing else.**  No round-10 finding required a statement change.

## 3.  Ticket 2, batch B: the nine background-sweep findings

**All nine verified.**  Six were exactly right; three needed the finding corrected before it could
be applied.  In the order given:

1. **VERIFIED.**  `w72-stratum-note.md` reported wave 71's `EvenForwardRouteSkeleton.lean:77-80`
   finding as "still unrepaired".  The repair landed at `e6d10612` (12:53:18), **3 h 12 min before
   the note was committed** (`60bfaab6`, 16:05:40), and `w72-house-note.md` §2.4b(d) marks it
   discharged, so trunk carried two contradicting notes for two waves.  Fixed.  The residue is
   also fixed: `EvenForwardRouteSkeleton.lean:81`'s notice was headed "Corrected at wave 70", and
   `e6d10612` sits on `dyadic` **after** both wave-71 merges, citing the wave-70 modules as its
   evidence, so the correction was applied at wave 71.
2. **VERIFIED, and the diagnosis is sharper than the finding.**  `w72-house-note.md`'s "87 modules
   reachable but not listed" came from subtracting the **physical** count from the listed count
   (`923 − 836 = 87`) rather than the reachable one (`921 − 836 = 85`), which silently counts the
   two unreachable modules as reachable.  Recounted at `4fff1592`: **929 physical, 843 listed, 928
   reachable, 1 unreachable, so 85 reachable-but-not-listed, of which only 27 are `public import`
   re-exports.**  The other 58 are ordinary transitive imports, so "exactly the parts re-exported"
   is false as well as miscounted.  §1.0 of that note names only 18 re-exports, which was already
   inconsistent.  All figures now carry their as-of commit.
3. **VERIFIED in all three parts.**  The three statements printed beside §6 carry `1 ≤ α`,
   `2 ≤ α`, and no `α` at all (fixed at `α = 1`, and it is wave 71's own statement rather than an
   analogue in another regime).  Corrected in the note and in the Lean comment at
   `EvenStratumFrame.lean:585`.  The blanket "every one of these is a subset" is deleted: the very
   next sentence computes a strict **superset**, and one table row (four statements) has no
   printed comparison at all.  The accurate per-statement comparison is kept.
4. **PARTIALLY CORRECT, and corrected in two notes.**  `w72-five-note.md:174`'s "unchanged from
   wave 71's list" is falsified as to "unchanged" but not as to the item: wave 71's item 3 is that
   no class-four-clearing frame is committed, and that survived wave 72 and survives today.  What
   moved is all three of wave 71's *leftover sub-items*, disposed of by `w72-defects-note.md` 8
   minutes later.  Both halves are now stated.  **And the same sentence recurs at
   `w73-five-note.md:152`**, which round 11 caught by grepping this fix; see §4.1.
5. **VERIFIED.**  `w72-defects-note.md`'s table column is retitled "corrected-relator factor" with
   the three leftover factors and the two knob-internal ones marked.  Same defect as batch A
   §3.1(b); the module's `cfourDef_assemble` docstring was the tiebreaker.
6. **PARTIALLY CORRECT: there were three readings, not two, and "38" was already taken.**  The 37
   is arithmetically exact and wave 73 recounted it label by label.  What was missing is the
   **scope**: it ranges over §§2.2-2.4b, and §2.1 is severity-headed, is promoted into the five
   "worth reading first", and is not among the exclusions the headline lists.  Counting
   severity-headed findings gives 38 with 13 high.  But wave 73 had already published a
   *different* 38 (the 37 plus the unsevered §2.4(e)).  **Adjudication: the figure stays 37, the
   scope is now stated, §2.1 is named among the exclusions, and both notes record that the two
   readings existed.**  Quoting "38" without saying which set is now the error to avoid.
7. **VERIFIED, exactly.**  Queue item 1 was discharged at `a515b437`, **32 min 27 s** after the
   note (`f23d7d3c` 15:46:46, `a515b437` 16:19:13), in the slot §1(a) proposed; the import sits at
   `GQ2.lean:692` today.  Marked discharged, and §1(a) carries a banner plus past-tense fixes.
   One wording caveat for the record: the note never contains the literal strings "is not
   registered" or "does not appear"; what it says is "has never been registered" and "appears in
   **no** ... file".
8. **VERIFIED** (the line is `:208`, not `:209`).  `GradedClassFourDefect.lean` has **38**
   declarations, 34 of them theorems with pins and 4 unpinned `def`s.  Restated as "38
   declarations, 34 axiom pins".  The disclosure below it says "three definitions ... and the
   `Prop`", four items in a sentence that says three, which is how a reader reconciling the two
   figures lands on 37; that is fixed too.
9. **VERIFIED CLEAN: zero stragglers.**  Four hits tree-wide for the "seven waves" family, and
   none is a straggler: two are the self-correction record in `owner-items-2026-08-05.md` (where
   "seven waves" appears in quotation marks as the retracted text, which is the right way to keep
   an error on the record), one is the corrected claim itself, and one is
   `w72-house-note.md:707`'s unrelated "all seven wave notes", a different denominator on a
   different subject.  `git log -S'seven waves'` confirms the correction landed at `f4a458a8`.

## 4.  Ticket 3: watch round 11

Scope: the wave-73 landings (`GradedClassFourCompose.lean`, `GradedClassFiveJoin.lean`,
`EvenStratumShift.lean`, `scripts/check_ledger.sh` with `check_dyadic.sh`'s D6 block, and the
three w73 lane notes).  The standing checklist was run in full and round 10's proposed fourth
item, **a docstring can be attached to the wrong declaration**, was run for the first time.

**Findings are REPORTED, not applied**, which is the campaign's rhythm: wave 73 reported round 10
and this wave applied it.  Four exceptions are applied here and marked, because each is the
*second half* of a fix this lane made under ticket 2 and leaving it would be the very defect the
half-a-fix rule exists to catch.

### 4.1  Applied here, because they are half-fixes of ticket 2's own edits

**(a) HIGH.  Wave 72's §2.4 fell through every application pass, and three findings sat unapplied
for two waves.**  `w72-house-note.md` carries six labelled sections; wave 73's ticket 1 covered
§2.2, §2.3 and §2.4b (33 findings) and said so accurately.  **§2.4 was in nobody's scope.**  Its
(d) and (e) were self-applied when written, but (a), (b) and (c) are `EvenAlphaOne.lean` prose and
all three were still live at `4fff1592`:

* `:668` said computing `demushkinQ` at `α = 1` "is a separate step that this file does not take",
  with no record that the step **was** taken later in the same wave by
  `nFrame4_demushkinQ_DN_one`.  Its sibling `EvenDemushkin.lean:252` was updated at the time; this
  file was not, which is exactly the asymmetry §2.4(a) reported.
* `:674` recorded the classification at `α = 1` as open in both halves; wave 71's
  `evenStratum_no_adaptedModelEquiv` closes the **frame** half negatively for the committed route.
* `:689` cited its own §10.3 for the missing frame inputs; §10.3 is about `MarkedCore.NFrame`, and
  the classification's frame is `StageGeneric.Frame`, a different structure with no torsion slot.
  `NFrame` is taken as a *term* by exactly three declarations tree-wide, none in the stage layer.

All three applied, comment-only.  The process lesson is §2.4's own subject turned on the audit:
**a scoped application pass leaves a residue unless the scope is reconciled against the finding
list.**  Round 12 should reconcile before it starts.

**(b) HIGH.  "Class four itself, unchanged" recurs at `w73-five-note.md:152`**, one wave after the
`w72-five-note.md:174` copy this lane corrected under batch B finding 4.  Found by grepping the
corrected phrase.  It was falsified **4 min 41 s** after the note landed (`56db0e02` 18:56:31,
`0063dc8c` 19:01:12) by the parallel W73-KNOB lane: `cfourCmp_core_reduce` turns the class-four
relator into `cfourDefCore nu' j` on the nose, and `cfourCmp_zLayer_le_triple` reduces the three
uniform questions to one.  The *lack* survives (`SqClassClearingSupply h 4` is still neither
discharged nor refuted); only "unchanged" is false.  Applied, with the companion sentence
("whether they are the same obstruction should not be assumed") now read against the owner's
wave-73 status, which records the convergence the other lane established.

**(c) MEDIUM.  All three wave-73 lane notes reported their module unregistered, and all three were
registered within about a minute.**  `959e22aa` 69 s after the five note, `5d7ce5c9` 73 s after the
knob note, `608d3ded` 73 s after the stratum note's final amendment.  So wave 72's `NuSeeds`
lesson took at the lane level *and* at the orchestrator level; what is missing is only the
annotation afterwards.  Annotated in all three.  **Null result attached**: recomputed at this tree,
the import closure of `GQ2.lean` is 928 of 929 modules and the single exclusion is
`GQ2.AxiomLedger`, which is deliberate.  There is no second `NuSeeds` today.

**(d) MEDIUM.  `w73-house-note.md`'s wave-74 queue item 1 was half-discharged 9 minutes after it
was written.**  It asked for the ledger gate to be run, because "whether the ledger passes today is
unverified by me".  The owner's wave-73 status (`4fff1592` 19:23:46, against the house merge
`78d14ece` 19:14:45) records the gate "exercised for the first time this wave: 32078 declarations,
no gap-map entries, no alarms, no terminal violations".  So the **ledger** ran and passed, and
§2.3's third bullet is superseded.  Corroboration that the figure is the wave-73 tree:
`32078 − 31954 = 124` against the wave's three new modules carrying 55, 35 and 33 declarations.
**What is not stated is whether it ran through D6**, which is what the item actually asked; if the
owner invoked `lake env lean GQ2/AxiomLedger.lean` directly, the four `sed` extractors remain
unexercised.  Annotated, and the item stands in that narrower form.

### 4.2  `GradedClassFiveJoin.lean` and `GradedClassFourCompose.lean`

**(a) MEDIUM.  `SqClassClearingSupply h 5` is said to be "conditional on class four"; it is not.**
`GradedClassFiveJoin.lean:79-81` and, second site, `w73-five-note.md:31`.  `SqClassClearingSupply
h k` (`GradedLimit.lean:236`) is a standalone per-class `Prop` and at `k = 5` mentions no
class-four object; `cfiveKnob_supply_of_reach` (`GradedGammaFourFive.lean:728`) binds only `H`,
and **its own docstring says the opposite of this file**: "No class-four witness is presupposed:
the base dressing is existentially quantified."  What is true is about the *assembly*:
`limFinal_markTransitivity_iff` consumes `∀ k, SqClassClearingSupply h k`, so class five alone
does not deliver the residual.  Correction: "…presupposing no class-four witness, and which enters
`limFinal_markTransitivity_iff` only alongside every other class, class four included."

**(b) MEDIUM.  The header says the pairing drives all four square families; two of them use no
pairing.**  `GradedClassFiveJoin.lean:56-58`.  Only families one and two run through
`cfiveJoin_pow_four_iff` (`:411`, `:419`); three and four are `cfiveJoin_defect_pt_iff` at a single
`x₁`-slot knob (`:427`, `:435`).  **The file contradicts its own header twice**, at the §6 section
docstring (`:374`) and at the family-three docstring (`:422`, "with no pairing"), and the lane note
has it right (`w73-five-note.md:71`).  Sub-item, LOW: the same sentence cites
`cfiveSpan_pair_correction` where the proof consumes `cfiveJoin_pair_correction` (`:395`), the §5
form with the second bracket already evaluated away.

**(c) MEDIUM-LOW.  A section pointer that drifted inside its own wave.**
`GradedClassFiveJoin.lean:117-119` says "the form the partial results of §5 need"; §5 is the
pairing and none of its four results touches `cfiveJoin_ad_far_mem`.  The consumers are §6's
`cfiveJoin_family_five_of_span` and `..._six_of_span`.  At the lane's first commit `bd4fd2a0` the
file had only §1-§4 and this was a forward reference; `22ad6762` landed the pairing as §5 and
pushed the families to §6, leaving the pointer one section short.  Worth noting that wave 73 fixed
two instances of exactly this class in other files (`d484d195`, `77113582`) while creating this
one.

**(d) MEDIUM-LOW.  "Unconditionally" on a theorem that binds two normalization hypotheses.**
`GradedClassFourCompose.lean:541`: "`cfourCmp_core_reduce` supplies such a correction
unconditionally".  It binds `hsigma` and `hx0` (`:493`).  Harmless in effect, because
`CfourCmpResidual` binds the same two, which is why they feed straight through; but
"unconditionally" is precisely the word this checklist exists to catch, and the lane note is
careful where the module is not ("at every selected marking and every handle").

**(e) MEDIUM-LOW.  A sign error in the parity display, which then makes "(mod γ₂)" too weak.**
`GradedClassFourCompose.lean:38` writes `+ 2·ν'(u_j)·ν'(v_j)·w`.  `bridgeDress` is
`u_j^{ν'(v_j)}·v_j^{ν'(u_j)}·w^{−2·ν'(u_j)·ν'(v_j)}` (`GradedBridge.lean:337`) and the cleared
letters are `V_j = v_j·w^{−ν'(v_j)}`, `U_j = w^{−ν'(u_j)}·u_j` (`LamFrames.lean:293`), correctly
restated **in this same file** at `:374` and `:384`.  With the sign fixed the displayed equality
holds exactly mod `γ₂`; as printed it holds only modulo squares, which the tag does not license.
Second site `:399-403` flips both signs again and reverses `U_j`'s factor order, defensible only
because it hedges with "modulo squares"; the file should not carry two conventions for the same two
letters.  Third site `w73-knob-note.md` §2 carries the display with the full hedge and is fine.

**(f) MEDIUM-LOW.  "The generation condition **is** mod-2 independence": only one direction is
committed.**  `GradedClassFiveJoin.lean:71`, and two more sites at `:563` and `:622`.
`cfiveJoin_topGen_of_modTwoIndep` (`:586`) proves `SqModTwoIndep → topGen` and nothing else.  The
converse is true mathematically but is nowhere in the tree.  The lane note is careful
(`w73-five-note.md:113`, "the density hypothesis is therefore `SqModTwoIndep`").  Correction:
"follows from".

**(g) MEDIUM-LOW, and it is the round's clearest ⚠ do-not-apply.**  `GradedClassFourCompose.lean:32`
and `:394`: the handle-pair correction's entries are said to be "`1` or `c`".
`cfourCmp_dress_reach` (`:410`) concludes only that both entries are *admissible*; `a, b ∈ {1, c}`
is a fact about the proof's four parity branches and **a consumer cannot use it**.  Making the
prose true would mean strengthening the conclusion, so the prose is what moves.  Second site:
`w73-knob-note.md` §2 states it as a displayed identity with `a, b ∈ {1, c}` as a side condition.

**(h) LOW.  `GradedClassFourCompose.lean:799` numbers its pins section §9 in a file whose sections
run §1 to §6.**  Across the 40 `SqCore` modules with a pins block this is the only numbering gap.

**(i) LOW.  An over-broad reason for stating all of §6 at `D_sq h`.**  `:83-85` says the §6 results
"consume discreteness of `Q₄` through `cfourId_isClosed`".  True of the three layer results, false
of `cfourCmpTest` (`:607`) and `cfourCmp_mem_test` (`:622`), which consume only lemmas stated over
an arbitrary topological group.  ⚠ Do not "fix" by generalizing `cfourCmpTest`; that is a statement
change.

**(j) LOW.  A containment described as an identity.**  `GradedClassFiveJoin.lean:133`: "the reached
far slots **are** the closed span of `X ∪ Y`".  `cfiveJoin_ad_far_lambdaTwo` proves one direction;
nothing shows a far slot outside the span is unreached.  The §1 section docstring at `:102` has it
right.

**(k) LOW.  A wave-71 pairing credited to wave 70's inventory.**  `GradedClassFourCompose.lean:704`.
`hbPow`'s element is the **product of two** wave-70 `x₁`-slot knobs by `cfourKnob_sq_knob_pair`,
whose own docstring says "this is the step the wave-70 §4 analysis was missing".  The bullet just
above names the pairing, so only the summary sentence drifts.

### 4.3  `EvenStratumShift.lean`

**(a) MEDIUM-LOW.  "Exactly the `zLayer`-valued ones" sits on a one-way inclusion.**  `:815-817`,
on `evenStratum_zLayerNeutral_reaches_iff`.  Only `zLayer`-valued ⇒ 0-neutral is proved
(`evenStratumNeutralOfZLayer`, `:802`); the converse does not follow, since
`EvenSharpNeutralCorrection` demands only `correction i ∈ lambdaImage G (k−1) (k+1)` plus a digit
condition, and a coordinate in `λ_{k−1} \ λ_k` can satisfy both.  **The module's own docstring has
the safe form at `:34`** ("the neutral corrections depth zero supplies for free all have trivial
shift word").  The downstream inference uses only the proved direction, so the mathematics is
sound.

**(b) MEDIUM-LOW.  A use-site pointer names the wrong subsection, in two places.**  `:531` says
`evenStratum_levelTwoGen_of_realizers`'s hypotheses are "exactly how §5.2 uses it"; its sole call
is at `:608`, inside §5.1's `evenStratum_frame_of_gramOne_modelEquiv`.  §5.2's only theorem calls
the two model-equivalence results and never the realizer lemma.  Second site
`w73-stratum-note.md:110`.

**(c) MEDIUM-LOW.  "Re-declared because the originals are `private`" is true of one helper and
false of the other.**  `:75`.  `evenStratumShiftAssemble` is statement-identical to the private
`evenRawShiftAssemble`.  `evenStratumShiftAssembleOne` is **not** a re-declaration: the private
`evenRawAssembleN` takes six elements with two commutation hypotheses, and the new lemma deletes
the `A` slot, the diagonal atom, leaving five elements, one hypothesis and a different conclusion.
That is the lane's own `α = 1` analogue, and calling it a re-declaration hides the one place the
`α = 1` shape shows up in the plumbing.

**(d) LOW.  §1's headline states the product in the opposite order to the theorem, with no
centrality to license the swap.**  `:121`: "the `α ≥ 2` core block is the `α = 1` one **times the
diagonal atom**"; `evenStratumShift_coreDbarWord_eq` puts the atom on the **left**, and carries no
depth hypothesis, so the atom is not known central.  §2's twin gets it right at `:171`, and the
theorem name `evenStratumShift_dbarWord_eq_diagonalAtom_mul` encodes that order.

**(e) LOW.  "`StageAbstractionEvenRawSpan.lean` §0" cites a section that does not exist, at five
sites.**  That file's headers run §1 to §6; the cited material is in its **module docstring**.  The
line numbers themselves resolve exactly and say what is claimed.  The label misdirects because the
repo does use `§0` as a real heading elsewhere (`AdmissibleR.lean:77`,
`OrientedTameBundle.lean:82`).  Sites: `EvenStratumShift.lean:15`, `w72-stratum-note.md:134` and
`:248` (which additionally cites "lines 44-45", one line short of the sentence),
`w73-stratum-note.md:16` and `:202`.  Inherited from wave 72 and propagated by wave 73.

**(f) LOW.  "Literal shift" applied to `evenRawDbarWord` inside the module that proves it is not
the literal shift at `α = 1`.**  `:779` and the §6 header bullet at `:707`.  The term is the repo's
own (`StageAbstractionEvenSharpHandles.lean:421`), so this is inherited rather than invented, and
the content is unaffected.  But §2 of this very file measures the gap.

**(g) LOW.  An unproved superlative.**  `:201`, "the smallest one does: the cyclic group of order
eight".  Nothing proves minimality, and read literally the smallest profinite group is trivial.
Second site `w73-stratum-note.md:41`.

**(h) MEDIUM-LOW, mine.  A shortened citation that does not resolve.**  `w73-stratum-note.md:225`
cites `evenRawShiftSpan_eq_zLayer`; the declaration is `evenRawShiftSpan_eq_zLayer_of_pureSquares`.
**Second site**, and presumably the source: `StageAbstractionEvenRawSpan.lean:57`'s own contents
list uses the same shortened name.

### 4.4  `scripts/check_ledger.sh` and `check_dyadic.sh`'s D6

**(a) HIGH, and the round's sharpest item.  The fixture hook is documented as unable to make the
gate pass.  It exits 0 and prints "all checks passed".**  Two sites:
`check_ledger.sh:66` ("It is not a way to pass the gate: L1 is explicitly marked skipped in the
output") and `w73-house-note.md:204` ("it can never be used to make the gate appear to pass").

In the fixture branch (`check_ledger.sh:80-86`) `fail` is never set; the branch only echoes
`SKIP: L1`.  L2/L3/L4 and the scanned count are then parsed **out of the fixture**, so on a clean
fixture the script prints `check_ledger: all checks passed` and exits **0**.  D6 keys on that exit
status alone (`check_dyadic.sh:319`), and the environment is inherited by `bash "$LEDGER_SCRIPT"`.
Therefore

```
GQ2_LEDGER_GATE=1 GQ2_LEDGER_FIXTURE=passing.txt bash scripts/check_dyadic.sh
```

prints `OK: scripts/check_ledger.sh passed`, then `check_dyadic: all checks passed`, exit 0, with
no `lake` run at D6.  An exported stale `GQ2_LEDGER_FIXTURE` green-lights the gate silently, and
**D6's comments never mention the variable**.  The transcript does carry the `SKIP: L1` line, so a
*reader* can tell; a script or a person reading the exit code cannot.

⚠ **Do not "fix" the sentence by fixing the script.**  Exiting non-zero under a fixture, or
refusing the fixture when `GQ2_LEDGER_GATE=1`, is a **behaviour** change.  The prose is what moves:
say that the skip is visible in the transcript but not in the exit code, that the exit code is what
D6 reads, and that the variable must never be set in a merge run; and name
`GQ2_LEDGER_FIXTURE` in D6's own comment as an inherited override that bypasses `lake`.

**(b) MEDIUM.  The `ax1-proposal.md` citation, at three sites: there is no §"Merge gate", and the
cited text is one *alternative* route's landing checklist.**  `check_ledger.sh:9`,
`check_dyadic.sh:69`, `w73-house-note.md:146`.  `ax1-proposal.md`'s headings run §1 to §8 with no
such section; `:489` is item 4 of **Route R** inside §7's census-flip checklist, and the
**recommended** Route D's gate item (`:468`) lists the full build, `check_axioms.sh` and zero
sorries, with no ledger.  `plan.md` §7's ten numbered merge gates do not list it either.  The
line-number citation is exact; only the characterisation over-generalises.  Supporting, and worth
its own look: that checklist is itself stale, saying "`EXPECTED_AXIOMS` stays **9**" against
`check_axioms.sh:28`'s `EXPECTED_AXIOMS=11` since the AX3/AX4 flips.

**(c) MEDIUM.  Both scripts justify D6's opt-in status by "lanes must never run `lake`", while the
default path they describe runs `lake env lean` twice.**  `check_ledger.sh:20-27` and
`check_dyadic.sh:18-22`, `:311`.  `check_dyadic.sh:173` runs `check_axioms.sh` unconditionally, and
that script's check 5 (`:280`) and check 5b (`:363`) both invoke `lake env lean`.  Wave 73's house
note records this as its protocol finding; **neither script does**, and the rule is stated nowhere
else.  D6 does not add to the exposure, so the prose fix is to say so.
⚠ Making the default path actually lake-free is a behaviour change to `check_axioms.sh`.

**(d) MEDIUM-LOW.  The note's self-skip description drops a disjunct and the nesting.**
`w73-house-note.md:211`: "Those blocks skip only when [two oleans] are missing."  Check 5's test is
`! command -v lake || [ ! -f …Roe/Main.olean ]`, so it also skips when `lake` is off PATH; and
check 5b sits **inside** check 5's else-branch, so its own olean test is nested, not conjoined.
("Both are present in this worktree" is correct.)

**(e) MEDIUM-LOW.  "One extra SKIP line" is four lines, and "naming the script and the flag" names
the environment variable, not the flag.**  `check_ledger.sh:31`, `check_dyadic.sh:26`.  The SKIP
branch is four `echo`s and never prints `--ledger`, which the same script calls "the flag" at
`:98`.  Also "exactly the checks it ran before this script landed" is not quite right for a
non-empty argv: the new argument loop exits 2 on any argument, where the pre-wave-73 script ignored
them.

**(f) MEDIUM-LOW.  L1's "already means" lists three causes; a nonzero exit has at least five.**
`check_ledger.sh:39`, repeated at `w73-house-note.md:149`.  `AxiomLedger.lean` also `throwError`s
on the private-tracking regression (`:88`) and on an unknown declaration (`:154`), and any
elaboration failure exits nonzero.  **The script's own FAIL text at `:96` already says the honest
version**, so this is a header/behaviour mismatch inside one file.

**(g) LOW.  D6's one-line summary omits the "missing line is a FAILURE" behaviour.**
`check_dyadic.sh:67`.  `check_ledger.sh` also fails when any report line is absent or reshaped, a
property its own header stresses at `:105`.

### 4.5  Background items, outside the round's scope, reported only

* **LOW-MEDIUM.  `GQ2/AxiomLedger.lean:14` and `:49` say "the nine literature axioms"**, against
  the same file's `:41` ("the axiom census (currently eleven)"), its own eleven `bAxioms` entries,
  the eleven `axiom` declarations in `GQ2/Foundations/Axioms.lean`, and
  `check_axioms.sh:28`'s `EXPECTED_AXIOMS=11`.  Eleven is right; the two "nine"s are stale at the
  AX3/AX4 flips.  **This is the file the new gate audits**, which is why it is worth the
  orchestrator's minute.
* **LOW.  `StageAbstractionEvenRawSpan.lean`'s Contents list (`:48-59`) is shifted against its own
  headers**: seven items against six sections, with its "§7 axiom pins" being the real §6.  Nothing
  downstream is wrong, because `EvenStratumShift.lean:74`'s citation is against the headers.
* **LOW, and it is a Lean-source item, not prose.**  `EvenStratumShift.lean:416`'s
  `private abbrev evenStratumPlane` is used nowhere in the file.  ⚠ Removing it changes the source,
  so it is reported only.

### 4.6  What came up clean

Said in detail, because a round that reports only hits is not a check.

* **Counts: clean, every one of them, and this is the round's strongest positive result.**
  Recounted independently at this tree:
  `GradedClassFiveJoin.lean` **33 declarations, 33 pins**, matching `w73-five-note.md` §7 exactly;
  `GradedClassFourCompose.lean` **35 and 35**, matching `w73-knob-note.md` §8 exactly;
  `EvenStratumShift.lean` **55 = 44 named public + 6 private + 5 anonymous instances**, with
  **47 pins = 44 + 3 comparison statements**, matching `w73-stratum-note.md`'s headline and its
  §4 sentence *both*.  Note the third of these is the count shape that batch B finding 8 caught
  wrong in the wave-72 note ("34 declarations" for 34 pinned theorems against 38 declarations), so
  the obvious question is whether that defect is systemic.  **It is not**: I re-derived
  `w71-cfour-note.md:199`'s "21 declarations, 21 axiom pins" (exact) and `w70-cfour-note.md:244`'s
  "46 declarations, 46 pins" (exact, and correctly summed across *two* modules, 14 in
  `GradedGammaThreeFour` plus 32 in `GradedClassFourIdentity`).  One-off, now corrected.
* **Lane bases: clean.**  `6a8fbc90` is an ancestor of the first commit of all three wave-73
  lanes, as all three notes claim.  All three lanes' code commits are single-file, so "New module;
  no edits to existing files" is exact in all three.
* **Citations in the three lane notes: clean but for one.**  I extracted every backticked
  snake_case identifier from the three notes and checked each against a 25 994-name index of the
  tree's declarations and structure fields.  The only genuine miss is the shortened name of
  §4.3(h).  Everything else that failed the index was
  mathematical notation (`U_j`, `u_j`, `c_U`, `Q_4`, `lambda_k`), a Lean tactic (`native_decide`)
  or a mathlib lemma (`continuous_of_discreteTopology`).  `w73-stratum-note.md`'s five-hash commit
  list was verified commit by commit and is exact, including that `a4d7ad06` is the stratum lane's
  own commit and not the house lane's despite sitting immediately below the house merge.
* **Headline-vs-statement on the two ⭐⭐⭐ headlines I checked by hand: clean.**
  `cfiveJoin_zLayer_le_iff` really is an `iff` in both directions with the four hypotheses the
  note's blockquote lists; `cfourCmp_core_reduce` really does conclude
  `sqRelWord (…) = cfourDefCore nu' j`, and although its §0 blockquote omits `hsigma`/`hx0`, §3 of
  the same note supplies them ("at every selected marking and every handle").
* **The docstring-on-the-wrong-declaration check, run for the first time on new landings: clean.**
  Round 10 found one instance in a wave-72 module and proposed the check; run over both wave-73
  graded modules it produced no hit.  The three findings it did produce (4.2(b), (c), (j)) are
  headline-vs-statement and pointer defects, not misattachment.
* **Hypothesis satisfiability: clean on both graded modules.**  `hgen` is not an unsatisfiable rank
  demand (it is discharged from `SqModTwoIndep`, which has committed witnesses); the knob clauses
  are met by the knob subgroup itself; the closedness clauses are genuinely free at `D_sq h`; and
  `cfourCmp_zLayer_le_gens` fires at `S = ⊤` and is consumed non-vacuously.  This matters because
  it is the item that produced batch A's §3.1(d).

## 5.  Ticket 4: the two `q`s

`qOf K FF = 2^f` (`OrientedTameBundle.lean:178`), the residue cardinality that the relator
`τ^σ = τ^q`, `GammaR n q word`, `candidateGroup 2 (qOf K FF) word` and `params.qK` all use, is
written `q_K` when the campaign is careful.  `demushkinQ` (`Demushkin.lean:224`), the order of the
torsion subgroup of the abelianization, is the other one.  I swept `docs/dyadic/` and the Lean
docstrings under `GQ2/Dyadic/` for bare `q` uses ambiguous between them.

**Fourteen sites disambiguated.**  Three are flatly wrong under the other reading, not merely
unclear:

1. **`Q₂(ζ₈)` "has `q = 8`"**, in two places, one of them a shipped module docstring
   (`w72-stratum-note.md:163`, `EvenStratumFrame.lean:488`).  True of `demushkinQ`; **false** of
   `q_K`, which is `2` there, `Q₂(ζ₈)/Q₂` being totally ramified of degree 4.  The sentence's own
   preceding clause is "about the family, not about fields", which pushes the reader into the
   field convention one word before contradicting it.  Both now say `demushkinQ` and give `q_K`.
2. **`SqCore/Rank3.lean:182`** overloads both letters in one clause: "`(p, rank, q, im χ) =
   (2, 3, 2, ℤ₂ˣ)`, the odd-rank `q = 2`, `f = 2` type".  That `f` is Labute's *image* invariant,
   not the residue degree of `q_K = 2^f`, so under the tame convention the pair reads `2 = 4`.
   The same file writes `τ^σ = τ^{q_K}` at `q_K = 2` thirty lines earlier.  Now spelled out.
3. **`owner-items-2026-08-05.md:165`**, the label "the `q = 4` ramified Arf sign", is the
   **residue cardinality** (its own §1 proves the Arf statement holds at `q = 2^f` only for `f`
   odd and is false at `q = 4`), while nineteen lines above, `:146`'s bare `q = 4` is
   `demushkinQ (D_N 1 h)`.  Two opposite invariants, same spelling, nineteen lines apart, and the
   label then recurs unglossed five more times several hundred lines later.  Glossed once at the
   label, which covers all five back-references.

Eleven more where the wording mimics the other invariant's defining formula or sits in a
Demushkin-primed run: `ev4b-stage-abstraction.md:296`, `w69-unram-note.md:24` and `:71`,
`NFrameAlphaOne.lean:103`, `EvenStratumFrame.lean:71`, `w71-stratum-note.md:143`,
`followup/glab-ksupply-plan.md:174`, `tickets.md:1850`, `sq-design.md:344`, `cb-design.md:528`.
The recurring shape is `q = 2^b` or `q = 2^α`, which is character for character `qOf K FF = 2^f`.

**Structural fix.**  The two notes that spend the most words on `q` (`w69-unram-note.md`,
`w72-stratum-note.md`) each carry exactly one gloss near the top and then run 100 to 150 lines on
bare `q`; that is why their tail-end sites are the ones that break.  Both now carry a two-line
gloss under the headline naming both invariants, which retires the rest of their bare uses at
once.  I checked before adding it that neither note uses bare `q` for the residue cardinality
anywhere.

**What came up clean, and it is most of the tree.**  Roughly 93 `q = N` sites and 40 bare
`` `q` `` sites in the docs, of which 21 were judged ambiguous; about 347 prose `q`-mentions in
the Lean docstrings, of which 14.  The reason the rest are safe is worth recording, because it is
a convention that works: on the tame side `q` is a *binder of the declaration the docstring
heads*, so the statement disambiguates the prose; and on the Demushkin side the campaign's habit
of putting "Demushkin", "Labute" or "torsion" in the same clause carries the reading.  Four files
are models of the practice and were left untouched: `followup/demushkin-q-status.md`, which states
the hazard outright and lists both definitions side by side; `followup/labute-interface-status.md`;
`ax3-proposal.md`, which writes `q_K` uniformly including in its per-field table; and `plan.md`
with `literature-axioms-dyadic.md`, whose `:144` even flags the adjacent trap ("never through
`qK`: `ℚ₂(√5)` has `q_K = 4` yet `i ∉ K`").

**One thing found and not fixed, for the owner.**  `mc-design.md:334` and `:358` use `q ∈ ℤ₂` for
the N6 automorphism parameter.  That is a **third** `q`, local to one table and unannounced.  It
is outside this ticket's two-way scope and outside a house lane's remit to rename, so it is
reported here only.

---

## 6.  Verification record

* Lane `claude/w74-house`, base `4fff1592`, cache at `608d3ded`.  Six commits, all path-limited.
  Not pushed.
* **No `lake` command was run.**  `scripts/check_dyadic.sh` was not run either, on wave 73's
  finding that its default path reaches `lake env lean` twice through `check_axioms.sh` check 5.
  That finding is confirmed here and is *still* the standing hazard (§4).
* `scripts/mirror.sh sweep` once at lane start, then `scripts/mirror.sh check` on every edited
  module after every edit and again at the final state.  **All eight modules `OK` at the final
  state.**
* **Comment-only discipline, verified mechanically.**  Every edited `.lean` file was
  comment-stripped (block comments, docstrings and line comments removed, blank lines dropped) and
  compared against its content at the lane base `4fff1592`.  **All eight print IDENTICAL**, so no
  statement, term, binder, name or proof changed anywhere in this lane:

  ```
  GQ2/Dyadic/Instances/EvenAlphaOne.lean              IDENTICAL
  GQ2/Dyadic/Instances/EvenForwardRouteSkeleton.lean  IDENTICAL
  GQ2/Dyadic/Instances/EvenStratumFrame.lean          IDENTICAL
  GQ2/Dyadic/MarkedCore/NFrameAlphaOne.lean           IDENTICAL
  GQ2/Dyadic/SqCore/GradedClassFiveKnob.lean          IDENTICAL
  GQ2/Dyadic/SqCore/GradedClassFourDefect.lean        IDENTICAL
  GQ2/Dyadic/SqCore/NuSeeds.lean                      IDENTICAL
  GQ2/Dyadic/SqCore/Rank3.lean                        IDENTICAL
  ```
* No new `.lean` file was created; `GQ2.lean` was not touched; nothing under `GQ2/Roe/` was
  touched (plan A6); nothing under the three sibling lanes' new-module paths was touched.
* No line over 100 characters was added to any Lean file, and no em-dash was added to any prose.
* The ticket-1(b) check file is a lane artefact and was deliberately **not** added to the tree.
  It imports `EvenUnramified` and `EvenParityModel` and needs four `open`s; §1.3 records what it
  states so it can be rebuilt in one minute.

## 7.  Files edited

**Lean (comment-only, 8):** `Instances/EvenAlphaOne.lean`,
`Instances/EvenForwardRouteSkeleton.lean`, `Instances/EvenStratumFrame.lean`,
`MarkedCore/NFrameAlphaOne.lean`, `SqCore/GradedClassFourDefect.lean`,
`SqCore/GradedClassFiveKnob.lean`, `SqCore/NuSeeds.lean`, `SqCore/Rank3.lean`.

**Docs (19):** `w74-critical-path.md` and `w74-house-note.md` (new); `w69-unram-note.md`,
`w71-stratum-note.md`, `w72-defects-note.md`, `w72-five-note.md`, `w72-house-note.md`,
`w72-stratum-note.md`, `w73-five-note.md`, `w73-house-note.md`, `w73-knob-note.md`,
`w73-stratum-note.md`, `chifree-clearing-note.md`, `cb-design.md`, `ev4b-stage-abstraction.md`,
`sq-design.md`, `tickets.md`, `followup/glab-ksupply-plan.md`, `owner-items-2026-08-05.md`.

## 8.  For the wave-75 queue

1. **Apply round 11's 29 reported findings** (§4.2 to §4.5).  All are prose-only.  Three carry a
   ⚠ marker because the *obvious* fix would change a Lean statement or a script's behaviour, and
   the prose is what must move: §4.2(g) (the handle-pair entries), §4.2(i) (`cfourCmpTest`'s
   generality) and §4.4(a) (the fixture hook).  Note that ten of the 29 have a **second site**, so
   the half-a-fix rule applies to nearly a third of the round.
2. **Decide the fixture hook** (§4.4(a)).  This is the one item that is not a documentation
   question underneath.  Either the prose changes to say the skip is visible only in the
   transcript, or the script changes to exit non-zero under a fixture; the second is an owner call
   because it is a behaviour change to a merge gate.  Whichever way it goes, `GQ2_LEDGER_FIXTURE`
   should be named in D6's own comment.
3. **`GQ2/AxiomLedger.lean:14` and `:49` say "nine literature axioms"; the census is eleven**
   (§4.5).  Two words, in the file the new gate audits, and `check_axioms.sh` has disagreed with
   it since 2026-07-29.
4. **Reconcile the finding list before the next application pass** (§4.1(a)).  Wave 72's §2.4 sat
   unapplied for two waves because wave 73's ticket scoped three sections of a six-section note
   and nothing checked the complement.  A one-line reconciliation at the top of the pass would
   have caught it.
5. **The two `GQ2/Roe/` R6 hazards remain live**, unchanged since round 9: four docstrings citing
   the nonexistent `GQ2/Roe/DRH2.lean`, and `TwoCentralTower.lean:65-66` announcing `sorry`s in a
   sorry-free file.  Still frozen by plan A6, still needing an owner nod.  This lane touched
   nothing under `GQ2/Roe/`.
6. **Two owner calls carried forward.**  `chifree-clearing-note.md`'s rewrite (§2.4), now
   annotated but not rewritten; and `mc-design.md`'s **third** `q`, the N6 automorphism parameter
   at `:334` and `:358` (§5).
7. **Round 12's checklist.**  Keep all four items, including round 10's fourth
   (a docstring can be attached to the wrong declaration), which came up clean on the wave-73
   landings but was cheap.  A fifth to consider, earned by §4.4(a) and §4.3(a): **a claim that
   something "can never" happen deserves the same reading as a headline that says
   "unconditionally"**.  Both of this round's HIGH prose findings outside §4.1 are of that shape.
