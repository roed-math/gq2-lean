# W78-HOUSE: the certificate pins, the residual recount, and watch round 15

Lane `claude/w78-house`, base `e6bbd2b9`, cache at umbrella 4348 jobs green.
Verification of record: `scripts/mirror.sh` (`sweep`, `gen`, `check`).  **No `lake` command was
run.**

## Headline

**Ticket 1.**  `GeneralCertificates.lean`'s **44** pins are recorded.  Not 48: the wave-76 cert
note's `1 + 1 + 44 + 1 + 1` was a sum checked against itself, and its "the other 44" should read
"the other 40".  Every *set* that note states reproduces exactly.  The file is not uniformly
std-3 and the block says so: 42 print at most std-3, and the two `L`-row acceptance-test
statements carry the campaign axioms.

**Ticket 2.**  The residual family is `2 + 2h`, corrected at the three module sites.  The one
site left alone is `GradedBaseDecide.lean:62`, which says "`3 + 2h = 3` classes, the third
trivial" and is the same fact spelled the other way.

**Ticket 3.  Three findings at HIGH, and the sharpest is not any of the four named items.**

1. **The two hypotheses refuted in wave 77 are not marked where a reader meets them.**  The
   decide lane, correctly following new-files-only protocol, edited nothing.  So
   `GradedUniformJoin.lean` §8 still called `GJoinBase h` an open item "not discharged here",
   `GradedJoinBase.lean` still said "whether they hold is open", and **five ⭐⭐⭐ theorems in
   two committed modules now have a hypothesis nothing can supply**, with nothing at their site
   saying so.  Annotated at both definitions and both headers.
2. **The wave-77 house note recorded the field module as unwritten three minutes after the
   field lane merged it complete into `dyadic`.**  The same defect that round diagnosed in its
   own predecessor, in the section that is hardest to re-check: the sibling reading, not the
   edit list.
3. **`GJoinSeparationAll h` now has no live consumer at all**, and `GTowerKnobRealizable h` has
   several.  This inverts the wave-77 queue's advice, which recommended both as lanes whose
   value does not turn on the decide fork.

On the two named checks: the decide note's Lean claims all verify, with two file citations that
point at use sites; the field note's "Group A is now empty" is **true on the general-record path
and false on the committed one**, because A2 is bypassed rather than discharged.

---

## Ticket 1: the 44 pins of `GeneralCertificates.lean`

### 1.1  What went in

A `§9 Axiom pins` block, one pin per declaration in declaration order, following
`GeneralAssembly.lean`'s wave-77 convention exactly (`/-! ## §N Axiom pins -/`, a
`section AxiomPins`, one line per declaration, closed by `end AxiomPins`).  `mirror.sh check`:
**OK**, 44 pins printed, no error, no warning.

### 1.2  What printed, and the honest split

| group | count | beyond `propext, Classical.choice, Quot.sound` |
| --- | --- | --- |
| §§1-4 transports, `WordCertificate.genCertTransport`, all four row producers, the `L`-row plumbing | **42** | none.  Two print *less*: `genCert_L_zero_degree` prints **no** axioms, `genCertNCoreMark` prints `propext, Quot.sound` |
| `genCert_wordCertificate_nonempty_L_zero` | **1** | `dyadicOrientation`, `localReciprocity`, `peripheralCyclotomicAction` |
| `genCert_candidate_equiv_galK_L_zero` | **1** | those three plus `tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, `Foundations.absGalQ2_localEulerCharacteristic` |

The content worth stating rather than the bookkeeping: **the certificate plumbing and all four
row producers are axiom-free; the campaign axioms enter only at §5, the `L`-row acceptance
test**, which is the one place this module touches arithmetic rather than plumbing.  Each of the
two is exactly the print of its own input, so the transports cost zero axiom movement, as
`w76-cert-note.md` §6 says.

### 1.3  ⚠ HIGH-for-a-count: the file has 44 declarations, not 48

`w76-cert-note.md` §6 reads "the other **44** declarations".  The file has 44 declarations *in
total*, so after the four it names by name the remainder is **40**.  The bad summand then
propagated into `w77-house-note.md` twice, at §2(a) ("48 declarations, **zero** `#print axioms`")
and at §3.6, where it is listed under **what came up clean**:

> `w76-cert-note.md` §6's axiom posture accounts for 1 + 1 + 44 + 1 + 1 = **48**, matching the
> file's 48 declarations.

**A sum that agrees with itself is not a count.**  The check that was run was internal
consistency of the arithmetic; the check that was needed was `grep -c` against the file.  This is
the second time in two rounds that a figure entered the record by arithmetic rather than by
measurement (`w75-house-note.md`'s "29 findings" was the first, and there the arithmetic was the
thing that was right).  Annotated at all three sites, and the four axiom sets are confirmed.

---

## Ticket 2: `3 + 2h` to `2 + 2h`

### 2.1  The reconciliation, and it was predicted exactly

`gDecide_triple_self` is at `GradedBaseDecide.lean:54`, stated at every `h`, proved by
`cfour_comm_self` then `cfour_one_comm`: precisely the one line `w76-base-note.md` item 2 and
`w77-house-note.md` §3.2(a) each predicted.  `gDecide_residual_zero_iff` (`:64`) is the `h = 0`
equivalence with the two classes at `σ` and `x₀`.

### 2.2  One qualification the flagging rounds did not carry

`GBaseXOneTriple h ν'` is `∀ i : Fin (sqRank h), ⁅⁅x₁, xᵢ⁆, x₁⁆ ∈ gTowerReach h ν' 2`.  It is
therefore *indexed* by all `3 + 2h` letters; what is `2 + 2h` is the number of indices that carry
content.  The corrected prose says `2 + 2h` **with content** and names the indexing, rather than
simply substituting the number, so a reader comparing the docstring against the `Fin (sqRank h)`
binder does not find a second discrepancy.

### 2.3  Sites, after a tree-wide grep

The grep for `3 + 2h` (four spellings, `.lean` and `.md`, `.lake` excluded) returns **80 lines** at
`e6bbd2b9`.  Counted as this campaign has learned to count them: **13 lines in 4 files** concern
the residual family, and the other **67 are `sqRank h = 3 + 2h`, the core rank**, which is correct
and unrelated, including `GradedJoinBase.lean:127` and `w76-base-note.md:99`, `:196`, which count
*letters*.  The 13, by disposition:

| line(s) | disposition |
| --- | --- |
| `GradedJoinBase.lean:72` | **APPLIED** (plus a ⚠ paragraph naming `gDecide_triple_self`) |
| `GradedJoinBase.lean:627` | **APPLIED** |
| `GradedBaseDecide.lean:11` | **APPLIED** |
| `w76-base-note.md:18` (headline) | **ANNOTATED** (dated record; also that §4's argument is now a theorem) |
| `w76-base-note.md:48`, `:54` | **RECONCILED**: the flag, now discharged, with the landing hash |
| `w77-house-note.md:324`, `:325`, `:332` | **RECONCILED**: the same flag |
| `w77-house-note.md:502` | **STRUCK**: the owner item, now done |
| `w77-house-note.md:345`, `:347` | **LEFT, deliberately**: verbatim quotes of the pre-correction text, which would stop being quotes |
| `GradedBaseDecide.lean:62` | **DECLINED**, with reasons: "the `3 + 2h = 3` classes ... the third being trivial" states the same fact and is not an overcount |

---

## Ticket 3: watch round 15

### 3.1  Staleness, run first

**(a) ⚠⚠ HIGH.  `w77-house-note.md` §3.2(b) was false when it was committed, and §4.2 repeats
it.**  Verbatim, `:334-337`:

> **(b) Recorded.**  The field lane's `Instances/FieldBranchIdentification.lean` is at §0 only,
> the two already-closed rows restated; §§1-4 are planned in its docstring but not written.
> Flagship item 1 is therefore **in flight, not closed** ...

The timeline, all `2026-08-15`:

| time | commit | the field module |
| --- | --- | --- |
| 06:06 | `62a8c05b` | opened, 126 lines, §0 only.  **The state described above.** |
| 06:14 | `dddd3734` | 398 lines |
| 06:16 | `4e4a6541` | 544 lines, all three remaining rows closed |
| 06:22 | `c9881c4c` | 746 lines, the five rows composed |
| 06:25 | `234ff5f1` | **merged into `dyadic`** |
| 06:28 | `9443a52b` | the house note is committed |

§4.2 compounds it: "the module is at §0 at `1d3d5a84`" is wrong twice over, because the module
**does not exist at `1d3d5a84`** (`git cat-file -e` fails there); it is created by the lane.

What makes this worth a HIGH rather than a shrug: the note's own §4.5 rule is *"Run the staleness
check before the application pass"*, and the round did run it, over the w76 queue and over its own
edits.  It did not run it over its **sibling readings**, which is the one section that cannot be
checked from the note's own base.  The rule needs a second clause: **re-read every sibling module
at merge time, not at lane start**, because sibling branches move during the wave and the base
hash is not a proxy for them.

**(b) LOW.  Two of three registration line numbers have drifted.**  `w77-house-note.md` §3.1(a)
gives `GQ2.lean:857`, `:858` for `GeneralAssembly` / `GeneralCertificates`.  At `e6bbd2b9` they
are `:858`, `:859`, because `7be6d122` inserted the decide module at `:778`;
`FieldBranchIdentification` is `:860`.  `GradedJoinBase` at `:777` still resolves.  The item's own
recommendation, grep rather than cite a line, is the right one.

**(c) LOW.  The decide lane's commit list is one short, and this is the third instance of the
pattern.**  `w77-decide-note.md:8-10` lists six commits; `git rev-list --count 1d3d5a84..294a197a^2`
is **seven**.  The missing one is `daf6f49a`, whose own subject is *"note bookkeeping: declaration
count and commit list"*, i.e. the commit that wrote the list could not include itself.  The
sibling house lane solved exactly this in the same wave (`8b9df64d`, "set the lane's own commit
count, which this commit makes exact"), and the wave-76 lane before it.  Worth promoting from a
recurring finding to a convention: **the last commit of a lane sets the lane's own counts**.

### 3.2  ⚠⚠ HIGH, and it is this round's real finding: the tree does not say the route is dead

`gDecide_not_baseResidual` and `gDecide_not_joinBase` refute `GBaseResidual h` and `GJoinBase h`
at every `h`.  The decide lane landed them in a new leaf module and, per protocol, edited
nothing.  The consequence at `e6bbd2b9`, before this lane:

* `GradedUniformJoin.lean` §8 introduced `GJoinBase h` as "the ENGINE lane's stated W75 item",
  **not** discharged here, alongside a live-looking second and third input;
* `GradedJoinBase.lean`'s module docstring said **"Whether they hold is open, and the lane note
  argues they do not"**;
* and **five ⭐⭐⭐ theorems became vacuous with no marker**:
  `gJoin_defectVanishing_of_base`, `gJoin_supply_of_base`, `gJoin_markTransitivity_of_base`
  (`GradedUniformJoin.lean:1023`, `:1037`, `:1044`), `gBase_markTransitivity_of_residual` and
  `gBase_supply_of_residual` (`GradedJoinBase.lean:655`, `:660`).

A reader of either module, at the tree, would take the campaign's most starred graded route for
live.  **Applied**, comment-only, at four sites: the two `Prop` definitions get a ⚠⚠ "FALSE at
every `h`, as of `e6bbd2b9`" line naming the refuting theorem, and the two module headers get the
scoping.  Each annotation also says what the refutation does **not** settle, because the failure
mode in the other direction is just as bad: `SqClassClearingSupply h k` and
`SqLamMarkTransitivity h` stand exactly where wave 67 left them.

This is a **protocol consequence, not a lane's mistake**.  New-files-only is the right rule for a
lane that might not land; it guarantees that a refutation's effect on committed modules is
invisible until a house lane walks it.  The check belongs on the standing checklist under its own
name: *after any refutation lands, grep every consumer of the refuted `Prop` and mark it*.

### 3.3  The named check (a): the decide note against the Lean

Everything structural verifies.  Confirmed at `e6bbd2b9`:

* **"No edits to existing files"**: `git diff --stat 958e8a59 294a197a` is two files, both new,
  887 insertions, **zero deletions**.  Same for the field lane: two new files, 930 insertions,
  zero deletions.  So the supply, the functionals and `limFinal_markTransitivity_iff` are
  untouched in the strongest sense, not merely unmentioned.
* **The supply.**  `SqClassClearingSupply` is at `GradedLimit.lean:236` as cited, and
  `limFinal_markTransitivity_iff` at `:328`.  `GradedBaseDecide.lean` names either exactly once,
  in the scope docstring, and in no statement.
* **The quantifier claim.**  `gDecide_reach_le_ker` (`:418`) really does range over the closure
  generators with only `ht.1` consumed on the knob and bundle branches, so admissibility is
  genuinely unused, as §"the refutation is stronger" says.
* **Not a quantifier artefact.**  `gDecide_triple_mem_three` (`:514`) and `gBase_adm_commP`
  (`GradedJoinBase.lean:352`) are both where the note puts them and are used as described.
* **The engine claims.**  `gTower_layerReach_step` (`GradedUniformTower.lean:1580`) carries
  `hk : 2 ≤ k`; `gTower_layerReach_of_base` (`:1591`) is stated at `k₀ = 2`;
  `gTower_defect_reach_of_base` (`:1667`) needs the base at `2`.  `gJoin_chiSupply_three`,
  `gJoin_clear_step`, `gJoin_supply_of_vanishing` are at `GradedUniformJoin.lean:226`, `:233`,
  `:260`, and the seeding argument reads exactly as the note has it.
* **The functionals.**  `gDelta_chiSq_of_gammaTwo` occurs **nowhere** in the tree, so correction
  1 is right.

**⚠ MEDIUM-LOW, and it is inside a correction about which lemma exists.**  The note gives
`gDelta_chiSq_of_nuLam` as `GradedUniformJoin.lean:113` and `gDelta_chi_gammaTwo_dvd` as
`GradedUniformJoin.lean:137`.  Both are **declared in `GradedDeltaFunctionals.lean`**, at `:1198`
(with `gDelta_chiSq_sq_of_nuLam` at `:1188`) and `:1456`.  `GradedUniformJoin.lean:113` is the
*proof term* of `gJoin_slot_dichotomy`; `:137` is a line of §2's module docstring and not a
declaration at all.  A correction whose point is "the real lemma is this one" should cite where it
is stated.  Annotated.

**⚠ LOW, and a new counting trap.**  "63 declarations, all pinned" is right about the named
declarations: **63 named, 63 pins, an exact bijection**, none unpinned, no duplicate, no pin
naming anything outside the file.  But the file declares **15 more things**: the `GDecideQ` group
and topology instances at `:104-137` are **anonymous** (`instance : Mul GDecideQ` and fourteen
others), so they carry machine-generated names and no pin.  78 declarations, 63 pinnable.  In any
module with anonymous instances `grep -c` on declarations will never equal `grep -c '#print
axioms'`, and the disagreement is not a broken bijection.  First collision of the two conventions
in the campaign, because the sibling landings declare no instances.

### 3.4  The named check (b): "Group A is now empty", adjudicated

`w77-field-note.md` §7 verbatim: *"Group **A** of the memo's closing set is now empty of open
mathematics"*, with A1 closed at all five rows and **"A2 ... was already a restatement; §6/§7
perform it"**.

**A1: DISCHARGED, confirmed.**  `fieldId_hrange_sqrt{Five,Ten,NegTen}` are equalities
`range chiCycKTwo = imChiM 2` over the field's own `MarkedRecip` bundle and the standing binders,
and the two older rows are re-exported.  The range identities print std-3, so the pin costs no
arithmetic axiom.  The lane's own two findings inside the argument (the uniformizer clause is
load-bearing; `ℚ₂(√5)` costs one extra element, not one extra binder) are consistent with the
Lean: `fieldId_hrange_sqrtFive` goes through `_of_negOne` and takes no ramification input, exactly
as claimed.

**A2: BYPASSED, not discharged, and §6/§7 do not perform it.**  The memo's A2 is *"the
`KTwoN`/`KTwoM` adapter into the two record spellings (§1.5)"*, and §1.5's test is "until it is
done the even route's output does not typecheck into either record".  The records in question are
`Main.lean`'s.  What the field lane produces is `∃ G : GenAsmBranch K B`, and:

* `GenAsmBranch` is `GeneralAssembly.lean`'s record, introduced in **wave 76**.  A tree-wide grep
  finds it in exactly **two** files, `GeneralAssembly.lean` and `FieldBranchIdentification.lean`.
* `Main.lean:352`'s `ResidualSqrtNegTwo` is **untouched** and still carries `fLab`, `piAb`,
  `hpiAb`, `hpiNu` and `horient : ∀ x, chiCycKAb K (piAb (fLab x)) = chiN 2 0 x`, i.e. the
  abelianization spelling §1.5 says the even route does not produce.  The four `ResidualSqrt*`
  records are likewise untouched.
* What actually performs the adapter is `KSupply.ofMarkedCoreRealization` inside
  `genAsm_candidate_equiv_galK` (`GeneralAssembly.lean:345-351`) together with §4.2's field-by-field
  record map, which explicitly **retires** `piAb`/`hpiAb`/`hpiNu` by moving to a new record rather
  than restating the old one.  Both are wave 76's, not the field lane's.

So the field lane *inhabits* the record; it does not build the adapter.  **The accurate sentence
is: Group A is empty of open mathematics on the general-record path, and on `Main.lean`'s
committed path A2 is untouched and the memo's own typecheck test still fails there.**  Neither
reading makes A2 open *mathematics* (it was always priced as a restatement), so what is at stake
is which records the campaign intends to ship.  **That is an owner call and is flagged as one.**

⚠ **The same sentence is in the owner memo.**  `docs/dyadic/owner-items-2026-08-05.md`'s wave-77
status block repeats "Group A of the flagship's closing set is now empty of open mathematics".
**Not edited here**: it is the owner's own dated status block, and the correction is a
qualification rather than a refutation.  Raised here so the owner can qualify it.

### 3.5  The named check (c): `GeneralAssembly.lean`'s `alpha` pin sentence

**APPLIED**, comment-only, with the as-of-hash convention.  The sentence (`:539-541`, over
`theorem genAsm_evenRoute_output` at `:542`, both at `1d3d5a84` and at `e6bbd2b9`) is **kept**,
because it states correctly what `parityFinal_evenClassification` itself supplies; the false
closing clause "and it stays open" is superseded in place, naming all five suppliers and noting
that the pin was already closed at two rows since wave 68.  One citation correction against the
field note: the sentence is at `:539-541`; `:542` is the declaration it sits on.  Off-by-one, not
drift.

### 3.6  The named check (d): identity headlines on the two new modules

**Both modules come up clean on the identity-versus-containment pattern.**  Said in detail,
because a check that reports only hits is not a check.

* `GradedBaseDecide.lean`: 18 starred docstrings, each read against its statement.  Every
  identity-flavoured one is an identity: `gDecide_residual_zero_iff` is a genuine `↔`, the three
  `gDecide_mem_*` are `Iff.rfl`, `gDecide_lambdaFour` is an equality proved by `le_antisymm`.  The
  negative headlines sit over negations.  **No containment is presented as an identity.**
* `FieldBranchIdentification.lean`: no stars at all, 27 bold-headline docstrings.  Every `hrange`
  headline claims an equality and the statement is an equality; the "CLASSIFICATION DATUM"
  headlines say "oriented-isomorphic" over `Nonempty (OrientedContinuousMulEquiv ...)`; the two
  criteria headlines state their hypotheses.  `fieldId_hrange_sqrtFive`'s "**no ramification
  input**" is confirmed by its proof term.

**Two precise citation defects found instead, both fixed comment-only.**

1. **MEDIUM-LOW.**  `gDecide_x0_not_mem` and `gDecide_sigma_not_mem` are proved at the **selected
   marking** `gDecideNu h`, and their docstrings wrote `∉ gTowerReach h ν' 2` with a free `ν'`,
   which reads as a claim at every marking.  Corrected to name the marking, with the reason one
   marking suffices (the residual quantifies over markings) and a pointer to the genuinely
   every-marking result at `h = 0`.
2. **LOW.**  `FieldBranchIdentification.lean:499` and `:512` cite
   `CertificateSupplyRN.nNuZtwo`.  `CertificateSupplyRN` is the **file**; the declaration is
   `SelectedCoreLeavesRN.nNuZtwo` at `CertificateSupplyRN.lean:223`, which is what the Lean
   beside the docstring actually writes, and what `w77-field-note.md` §5 writes.  Corrected.

### 3.7  Round 14's own work, re-verified

* The LamFrames repair resolves exactly at both shipped sites: `GradedClassFourCompose.lean:420-421`
  and `w73-knob-note.md:91` now cite `sqEichU`/`sqEichV` at `LamFrames.lean:303`/`:295`, and
  `:303`, `:295` are those two `noncomputable def` lines.  The whole `:293`/`:295`/`:300`/`:301`/`:303`
  table of §2(b) reproduces line for line.
* The as-of datings of §2(c) item 4 all reproduce: `GradedDeltaFunctionals.lean` **1757** lines and
  **103** pins (the column-zero anchor holds, and the docstring bullet at `:111` is still the only
  false `grep` hit); `EvenStratumRowFrame.lean` **1088** lines.
* `GeneralAssembly.lean`'s pins block: **42**, `mirror.sh check` OK, and the honest-split docstring
  is accurate.
* `GradedJoinBase.lean`: **48** declarations, **48** pins, every one exactly std-3.
* `GeneralCertificates.lean:705-711`'s F2 quote reproduces verbatim.
* The house lane's own "Seven commits" is exact (`git rev-list --count 1d3d5a84..958e8a59^2` = 7).

**One miss found outside the round's own edits, and swept.**  `gDelta_cfourCmp_span_hyp_false` was
at `GradedDeltaFunctionals.lean:1575` at `f0a71688` and is at **`:1583`** since the wave-76
landings; `:1575` is now a prose line of a docstring.  Three committed modules still sent readers
there: `GradedClassFourCompose.lean:75`, `:783`, `GradedClassFiveJoin.lean:90`.  **All three
corrected**, with the drift recorded once at the first so the change is traceable.  The five lane
notes that cite `:1575` (`w70-cfour`, `w71-cfour`, `w72-five`, `w73-five`, `w73-knob`) are
**deliberately left**: the number was right at each note's own tree, and a note is a dated record.
That is the same disposition rule this lane used for the `3 + 2h` sites.

⚠ **One citation this lane could not resolve and did not guess at**:
`GradedClassFourCompose.lean:745` says "See `GradedDeltaFunctionals.lean:1557`", and `:1557` is a
`have hcancel :` inside a proof.  Its intent is not recoverable from the sentence, so it is
reported rather than repaired.

---

## Ticket 4 (report only): the W79 queue

### 4.1  What the two sibling lanes leave

Neither `SqCore/GradedAbsorption.lean` nor `Instances/FieldUnimodularity.lean` exists at this
lane's base, so this section is written from the interfaces they are aimed at, and **wave 79
should re-read both modules at merge time rather than trusting this paragraph** (§3.1(a) is what
happens otherwise).

**The absorption lane.**  The owner memo names it the wave-78 lead and prices it from Labute's
Theorem-5 endgame: unreachable classes are absorbed into `2`-adic generator exponents, and the
campaign's markings already carry that freedom.  Read against the tree, the landing has to clear
one specific bar, and it is not the base:

* the target is `SqClassClearingSupply h k`, `GradedLimit.lean:236`, reached through
  `limFinal_markTransitivity_iff` at `:328`.  Nothing in wave 77 moved either;
* the committed route into it is `gJoin_supply_of_vanishing` (`GradedUniformJoin.lean:260`), and
  the decide note's §T2 proves the load-bearing negative: that recursion **seeds at class three**
  and its first step consumes the vanishing at `k = 2`.  So an absorption result stated one level
  up does not seed it either.  A partial landing that produces the vanishing only for `k ≥ 3` is a
  restatement of the depth-`3` problem, not progress past it;
* the cheapest genuinely new thing the lane could leave, if the full absorption does not close, is
  **a class-four supply witness** (`GJoinChiSupply h 4`, or `SqClassClearingSupply h 4` with the
  `χ`-clause restored).  That single object converts the depth-`3` re-cut from "needs two things"
  to "needs one", and it is the wave-69-to-73 question in its sharpest form.

**The unimodularity lane, selector side.**  The five `fieldId_genAsmBranch_*` producers each stand
over **exactly one** clause: `hpivot` (`IsUnit (toAdd (nuUrKTwo B (e.1 (dmC α 0))))`) on the four
`M` rows, `hpair` (the `σ`-or-`x₂` disjunction) on the pilot.  Two things wave 79 should check
about whatever lands:

1. the clause is stated **at a chosen equivalence** (`fieldId_chosenEquivM_*`, a `Nonempty.some`).
   A discharge at some other equivalence does not compose with these producers;
2. the field note scopes a **stronger route that removes the clause entirely**:
   `marked_matching_certificate_KTwo{M,N}_of_level_zero` (`LabuteInterface.lean:81`, `:123`)
   replace both `hpivot` and `hMix` by `B.r = 0` plus a decomposition.  Its own caveat is that
   `genAsm_branch_of_even{M,N}` route through the *non*-level-zero producers, so taking it needs a
   **new `GenAsmBranch` producer**.  If the lane took that route, the five row theorems above are
   not the ones that get discharged, and the queue should say which set survives.

### 4.2  The flagship surface that remains

`w74-critical-path.md`'s eight items, updated:

* **Group A**: A1 discharged at the five frozen rows (§3.4).  A2 discharged on the general-record
  path, untouched on `Main.lean`'s.  ⚠ **Neither closes the `α` pin at a general ramified-`i`
  `K`**, which is what the general-degree statement asks for; the criterion is per field and its
  witnesses are explicit elements.
* **Group B, the ASK bundles at `G_K`**: items 3, 4, 5 unchanged and unowned.  Item 5, the
  **LG5 ⇒ `GaussZResidueK` bridge**, still has no `K` clone and no supplier lane.
* **Group C, the CAND clauses**: item 6 (the four certificate-to-count bridges at
  `GammaR n q word`) is a **uniform residual on four even rows**, not a per-row obligation, since
  `GeneralCertificates.lean`'s four producers all take the same four analytic clauses; item 7's
  `hsimp`/`hsplit`/`hZcount`; item 8's `nuP` build.
* **`hdet` is still unowned and still the sharpest item on the list**, for the reason the memo
  gives: it is the only place both sides of the two-sided architecture are carried and neither has
  a supplier lane.  Nothing in waves 76-78 touched it.  ⚠⚠

### 4.3  ⚠⚠ Separation and realizability: the wave-77 queue's advice is inverted

`w77-house-note.md` §4.3 recommends `GJoinSeparationAll h` and `GTowerKnobRealizable h` as the two
lanes "whose value does not turn on the decide fork", calling separation "the cheapest of the
three graded items and the one most likely to close in a single lane".  The fork returned outcome
2 (the base is refuted), and under that outcome the two behave **oppositely**:

* **`GJoinSeparationAll h` has no live consumer at all.**  Its four consumers are
  `gJoin_defectVanishing_of_base`, `gJoin_supply_of_base`, `gJoin_markTransitivity_of_base` and
  the two `gBase_*_of_residual`, and **every one of them also takes a hypothesis now proved
  false**.  A lane that discharged separation today would produce a theorem with no consumer.  It
  becomes valuable again only if a base at *some* depth is re-established, and then it needs
  restating at that depth.
* **`GTowerKnobRealizable h` is fully live.**  It is consumed by `gJoin_clear_step` (`:233`),
  `gJoin_supply_of_vanishing` (`:260`), `gJoin_markTransitivity_of_vanishing` (`:283`) and by
  `gTower_clear_step` / the tower-side assembly (`GradedUniformTower.lean:1732`, `:1758`, `:1785`),
  **none of which mention `GJoinBase`**.  Any future producer of the vanishing, from a depth-`3`
  base or from the absorption route, still has to pay for it.

So the recommendation should read: **realizability, yes; separation, not until a base exists.**
This is the concrete cost of §3.2's blindness, and it is why that check is worth standing.

### 4.4  The owner items

* **The plan-A6 freeze on `GQ2/Roe/*`** is still open, carried from round 11 through W75 §8 item
  6, W76 §4.4, W77 §4.5 and this round.  Untouched here: `git diff --name-only e6bbd2b9..HEAD`
  returns **zero** paths under `GQ2/Roe/`.  **The oldest live owner item in the campaign.**
* **The 100-character question.**  Still no policy, and the drift is now visible in the tree: the
  wave-77 field lane shipped **two** lines over 100 characters
  (`Instances/FieldBranchIdentification.lean:363` at 104 and `:396` at 101), the first over-long
  lines in a landing for several waves.  This lane held to 100 and added none.  A lane that
  believes there is a rule and a lane that does not are now both producing evidence; the state is
  worse than it was when the item was minor.
* **New, and one of them is a rule rather than a fix**: the standing checklist should carry *"after
  a refutation lands, mark every consumer of the refuted `Prop`"* (§3.2), and *"re-read sibling
  modules at merge time, not at lane start"* (§3.1(a)).
* Carried and untouched: `chifree-clearing-note.md`'s rewrite, `mc-design.md`'s third `q`,
  `w75-house-note.md` §5.2's class-five mod-16 kit, and W77's suggestion that the reachability walk
  be committed under `scripts/` (still not created; a comment-only lane should not add a script).
* **New, small, and for the owner**: the "Group A is now empty of open mathematics" sentence in the
  wave-77 status block of `owner-items-2026-08-05.md` wants the §3.4 qualification.

---

## Verification record

* Lane `claude/w78-house`, base `e6bbd2b9`.  **Seven commits**, all path-limited, the last of them
  the one that sets this figure.  **Not pushed.**
* **No `lake` command was run**; `scripts/check_dyadic.sh`, `scripts/check_axioms.sh` and
  `scripts/check_ledger.sh` were not run.
* `scripts/mirror.sh sweep` once at lane start (**5893 artifacts**), then `gen` on every edited
  module with dependents and `check` on every edited file after every edit.  **All eight modules
  green**, no error, no warning:

  ```
  GQ2/Dyadic/GeneralCertificates.lean               gen  (44 pins printed)
  GQ2/Dyadic/GeneralAssembly.lean                   OK   (42 pins printed)
  GQ2/Dyadic/SqCore/GradedJoinBase.lean             gen  (48 pins printed)
  GQ2/Dyadic/SqCore/GradedUniformJoin.lean          gen
  GQ2/Dyadic/SqCore/GradedBaseDecide.lean           OK   (63 pins printed)
  GQ2/Dyadic/Instances/FieldBranchIdentification.lean OK
  GQ2/Dyadic/SqCore/GradedClassFourCompose.lean     OK
  GQ2/Dyadic/SqCore/GradedClassFiveJoin.lean        OK
  ```

  Order of record observed: `sweep` first, then `gen` for `GradedUniformJoin` before
  `GradedJoinBase`, and `check` on the dependents after, so nothing typechecked against a pre-edit
  olean.  `GeneralCertificates` was `gen`'d and its importer `FieldBranchIdentification` re-checked
  at the end for the same reason; the risk there is nil, since a `#print axioms` command adds no
  declaration, but "obviously nil" is what the rule exists to override.
* **Comment-only discipline, verified mechanically.**  Each edited `.lean` file was
  comment-stripped (nested block comments, docstrings and line comments removed, string literals
  respected, whitespace collapsed) and compared against its content at the lane base `e6bbd2b9`:

  ```
  GQ2/Dyadic/SqCore/GradedJoinBase.lean               IDENTICAL
  GQ2/Dyadic/SqCore/GradedUniformJoin.lean            IDENTICAL
  GQ2/Dyadic/SqCore/GradedBaseDecide.lean             IDENTICAL
  GQ2/Dyadic/GeneralAssembly.lean                     IDENTICAL
  GQ2/Dyadic/Instances/FieldBranchIdentification.lean IDENTICAL
  GQ2/Dyadic/SqCore/GradedClassFourCompose.lean       IDENTICAL
  GQ2/Dyadic/SqCore/GradedClassFiveJoin.lean          IDENTICAL
  GQ2/Dyadic/GeneralCertificates.lean                 one pure addition, 0 deletions
  ```

  For `GeneralCertificates.lean`, the lane's one non-comment edit and its stated exception, the
  stripped diff has **zero deletions** and adds exactly **136 tokens**: `44 × (#print, axioms,
  name)` plus `section`, `AxiomPins`, `AxiomPins`, `end`.  Nothing else.  So no statement, term,
  binder, name or proof changed anywhere in this lane.
* `GQ2.lean` was not touched.  Nothing under `GQ2/Roe/` was touched (plan A6).  Neither
  `SqCore/GradedAbsorption.lean` nor `Instances/FieldUnimodularity.lean` was created or touched;
  neither exists at this base.
* No line over 100 **characters** was added to any Lean file (measured in codepoints, not bytes:
  `awk 'length'` counts bytes in this environment and reports false positives on every line with
  `⁅` or `ℚ`).  No em-dash was added to any prose.

## Files edited

**Lean (8):** `Dyadic/GeneralCertificates.lean` (pins block added), `Dyadic/GeneralAssembly.lean`,
`Dyadic/SqCore/GradedJoinBase.lean`, `Dyadic/SqCore/GradedUniformJoin.lean`,
`Dyadic/SqCore/GradedBaseDecide.lean`, `Dyadic/Instances/FieldBranchIdentification.lean`,
`Dyadic/SqCore/GradedClassFourCompose.lean`, `Dyadic/SqCore/GradedClassFiveJoin.lean`
(all comment-only but the first).

**Docs (6):** `w78-house-note.md` (new); `w76-base-note.md`, `w76-cert-note.md`,
`w77-decide-note.md`, `w77-field-note.md`, `w77-house-note.md`.
