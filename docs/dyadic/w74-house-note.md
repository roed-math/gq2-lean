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

**Ticket 3.**  Watch round 11 over the wave-73 landings: **N findings** (see §4).

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
