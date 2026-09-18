# W366-HOUSE lane note

Wave 366, housekeeping lane. Branch `claude/w366-house`, base `9dd8a307`.
Date: 2026-09-18.

Remit: watch 27 (T1), the decision's consequences in the docs corpus (T2), the
handoff's post-decision repairs (T3), the scoreboard baseline (T4).

Out of remit this lane: `GQ2.lean` and every Lean module; `docs/dyadic/refs/*`,
`w361-completion-audit.md`, `w364-proof-packet-amendment-mc.md`,
`w364-acceptance-readiness-mc.md` (APPLY lane); `generated/` and
`scripts/w366_*` (GAUSSEXPORT lane).

## T4, baseline

Run at the lane's own HEAD `2c2107da` (branch `claude/w366-house`), generated
2026-09-18 00:28, through the shared cache
(`GQ2_MIR=/Users/roed/claude/cla/work/main-build-cache/lib/lean`).

**The `--raw` flag does not produce these two sections.** `scripts/scoreboard.sh:1515`
returns immediately after `cat`-ing the probe records, so FROZEN ROWS and OWNER ITEMS
exist only in the formatted report. The board below is the formatted run of the same
script, same environment; no `lake`, no `check_dyadic.sh`.

**The shared-cache caveat still applies**, and W362-HOUSE and W364-HOUSE both recorded
it. The cache describes whatever the main clone last built, not this lane's base. This
lane changes no `.lean` file at all, so no row's binder count, axiom footprint or import
closure can differ between the cache's tree and this one.

### FROZEN ROWS

```
  Q2(v-2)  .N0 2 0               EXISTS   GQ2.Dyadic.FieldUnimod.fieldUni_genAsmBranch_sqrtNegTwo
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v2)   .M0 3 0               EXISTS   GQ2.Dyadic.FieldUnimod.fieldUni_genAsmBranch_sqrtTwo
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v5)   .M0 2 0               EXISTS   GQ2.Dyadic.FieldSqrtFive.fieldFive_genAsmBranch_sqrtFive
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v10)  .Mpc F                EXISTS   GQ2.Dyadic.Instances.MpcNorm.mpcNorm_genAsmBranch_sqrtTen
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v-10) .Mpc T                EXISTS   GQ2.Dyadic.Instances.MpcNorm.mpcNorm_genAsmBranch_sqrtNegTen_of_pivot
      carries 2  : MarkedRecip, Exists
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v-10) via shift             EXISTS   GQ2.Dyadic.Instances.MpcPiv.mpcPiv_genAsmBranch_sqrtNegTen_of_shift
      carries 2  : MpcPivShift, MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v-10) untied                EXISTS   GQ2.Dyadic.Instances.MpcPiv.mpcPiv_genAsmBranch_sqrtNegTen
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  v-10 residue = word prob       EXISTS   GQ2.Dyadic.Instances.MpcOrb.mpcOrb_shift_iff_marking
      carries NOTHING (no explicit binder)
      axioms     : std-3
  v-10 finite-class route        EXISTS   GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class_four
      carries 1  : (function)
      axioms     : std-3
  v-10 residual move             producers: 15   [MpcPivShift]
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_bracket_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_forall_class
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_forall_class_five
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_full_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_word
        carries 14 : carrier, carrier, carrier, carrier, mem, mem, mem, mem, Eq, Eq, Eq, Eq, (function), Eq
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_wide_shift_of_forall_class_five
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcLad.mpcLad_shift_of_exists_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcMk.mpcMk_pivShift
        carries NOTHING            axioms: std-3
      GQ2.Dyadic.Instances.MpcMk.mpcMk_shift_of_fullSupply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcMk.mpcMk_shift_of_good_four
        carries 2  : MpcMkGood, (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcOrb.mpcOrb_shift_of_marking
        carries 7  : Eq, Eq, Eq, Eq, Eq, Eq, (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcSx.mpcSx_shift_of_marked_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class_four
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_word
        carries 14 : carrier, carrier, carrier, carrier, mem, mem, mem, mem, Eq, Eq, Eq, Eq, (function), Eq
        axioms     : std-3
  v-10 initial-relator absorption EXISTS   GQ2.Dyadic.Instances.MpcMk.mpcMk_initialRelatorAbsorption
      carries 2  : Nat, le
      axioms     : std-3
  v-10 pivot shift theorem       EXISTS   GQ2.Dyadic.Instances.MpcMk.mpcMk_pivShift
      carries NOTHING (no explicit binder)
      axioms     : std-3
```

All twelve frozen rows EXIST; the residual-move row has 15 producers. No row changed
against the W364-HOUSE baseline.

### The board's owner-items row

```
  owner memo (AUTHORITY)   docs/dyadic/owner-items-2026-08-05.md
    latest status block    ## Status at wave 362 (2026-09-17)
    count it asserts       7   (PROSE, off "N items await you")
  latest house note        docs/dyadic/w366-house-note.md
    owner-items heading    NOT FOUND in it (so no count; this is the
                           signal, not a zero)
  memo vs note             NOT COMPARED (one side is missing above)
  status of each item      UNVERIFIED (prose; not machine-checkable)
```

**The memo's count was stale and is finding H1 below.** The board read **7** because the
wave-362 status block still said "Seven items await you" after the owner decided item 4
and did item 5 on 2026-09-18. Expected after the decisions: **5**. Fixed in this lane;
the board re-reads 5 once the memo's headline is corrected.

The "NOT FOUND" line against this note is the board's own signal, not a defect in
it: this note had no owner-items heading when the baseline ran. One is supplied
below, and both sides now read **five**.

**A trap in supplying it, worth recording.** The board takes the *first* heading
in the note matching its owner-items pattern, and that pattern also matches the
heading of this very subsection. Reproducing the board's `## OWNER ITEMS` block
verbatim under a heading of the same name makes the board parse its own echo --
a subsection with no numbered lines -- and print `0`, which its own header warns
is indistinguishable from "not found". The subsection above is therefore headed
"the board's owner-items row", with a hyphen, which the pattern cannot match.
The second half of the trap is the count: the memo's five is prose
("N items await you"), while the note's is a count of lines beginning
`<digit>.`, so a note that numbers all seven items and strikes two would make the
board print a DISAGREE that is an artifact of two different counting rules. The
owner-items section below numbers the five that are open and puts the two
decided ones in prose under their own heading. Both rules then give five.

## T1, watch 27

Window: `d2056503..9dd8a307`, 145 files. One new Lean module
(`GQ2/Dyadic/Instances/GaussPhaseValues.lean`), two Lean modules edited
comment-only (`MNielsenGenerators.lean`, `NNielsenGenerators.lean`), one import
line added to `GQ2.lean`, ten documents, three durable JSON reports, and 128
files under `generated/`.

Findings are ranked. **FIXED** means this lane changed the tree. **FLAGGED**
means it did not, because the site is a Lean module (not this lane's remit), a
file outside the repo, or another lane's.

### HIGH

**H1. The owner memo's headline count was stale, and the scoreboard was
reporting it. FIXED.** `9dd8a307` recorded the owner's two decisions inside items
4 and 5 but left the block's first line reading "**Seven items await you.**". The
board reads exactly that phrase as its AUTHORITY count, so the T4 baseline below
was taken against a **7** that no longer described the docket. Corrected to
**five**, with the reason and the date in the same sentence. Both items keep
their original text, as `9dd8a307` left them; only the count moved, and only to
match decisions the owner had already recorded.

**H2. The handoff's section 5 draft claimed to be accurate at the very commit
that repaired it. FIXED.** The draft said "accurate at `e34315af`". `e34315af`
is "apply watch 26's comment-level findings", and it repaired **three of the four
documentation items in that draft**: item 9 (the `NNielsenGenerators` docstring
now carries its overtaken banner), item 11 (zero occurrences of the retained
alias remain in `MNielsenGenerators`, and the stabilizer claim now states its
scope), and the disclosure half of item 12 (`eb3089cd` gave the W363 M audit a
dated annotation naming base `69b9851c`). A next session working the list would
have re-done work that had already landed. Corrected to `2c4d0197`, the draft's
own base, with each item marked with its outcome rather than deleted, because
section 7 cites the list.

**H3. Section 5's ordering was still gated on two settled decisions. FIXED.** It
put "Owner decisions first ... the proof-method acceptance (Option A is
recommended ...), the four Codex adoption items, the push" at position (1). Option
A is taken and the push is done. Rewritten to start after Option A: applying it is
the writing task that replaces it, three Codex adoption items remain, and Option
B's generator-level bill (M4/M5/M6/M7 at M, N4 at N) is explicitly **not owed**,
which the old ordering left open at position (3).

### MEDIUM

**M4. `NNielsenFactorization.lean:38-39` still says "every parameter" where both
its named witnesses need a supplied inverse. FLAGGED (Lean module).** The
docstring reads "every parameter fixes the integral `x1` coordinate, hence
preserves `nFrameOrientation` (`nNielsenFac_orientation`); every admissible
parameter is an `NFrameCupIsometry`". Both theorems (`:504`, `:565`) take
`(P Q : NStabParam)` with two mutual-inverse hypotheses, because they are stated
about `nNielsenFacEquiv` (`:480`), not about `nNielsenFacMap`. This is the **N
half** of the handoff's section 5 item 10; `e34315af` fixed the M half and did
not touch this module, so the item is half open, not closed. Recorded in the
handoff and as index flag 7. The headline theorems are unaffected.

**M5. The campaign log's "Live frontier" still gates the mathematics on Option
A/B and the push. FLAGGED (orchestrator's file, outside the repo).** Section 199
of `~/claude/cla/outputs/dyadic-general-K-proof-campaign-plan-2026-08-02.md`
reads "Nothing mathematical remains that does not first require an owner
decision: Option A/B on the proof method; the four Codex adoption items; the
push." The 2026-09-18 addendum does correct both, but it sits *below* the
frontier paragraph, so a reader who stops at the frontier -- which is what a
paragraph called the live frontier invites -- gets the superseded list. Same
treatment as W364-HOUSE's L7: the log is the orchestrator's file.

### LOW

**L1. The new Gauss module credits the wrong assistant. FLAGGED (Lean module).**
`GQ2/Dyadic/Instances/GaussPhaseValues.lean:4` reads "Authors: David Roe,
roed@mit.edu, and OpenAI Codex". The module is a Claude lane's: `db4fbede` and
`d58e477b`, both carrying the `Claude Opus 5` trailer. The line is almost
certainly copied from `LHessianCertificates.lean`, which the module imports and
whose line 4 is byte-identical. 229 files in the tree legitimately carry that
line, so this is not a house style question, it is one file's provenance.

**L2. One Gauss docstring headline outruns its statement. FLAGGED (Lean
module).** `gaussValCompactDisplayUnram`'s docstring opens "The compact display
cell serves both compact branches: at even degree the unramified and the
ramified target are the same integer, so the compact-`N` and compact-`M` sectors
print the same sign and the same exponent." The statement is one equation,
`gaussSum (wPhCompactWallHandlePhase q h) = (standardNumerics (2*h+2)).gaussUnram m`,
and mentions neither the cell nor two branches. The headline follows from this
theorem *together with* `gaussValCompactDisplay`; it is not what this one says.
The module's other ten docstrings are exact, including the three that
deliberately say "recorded here rather than re-derived".

**L3. The campaign log's 2026-09-18 addendum names three of wave 366's four
lanes. FLAGGED.** "W366 applies the amendment wording to the packet and ledger,
wires the Gauss theorems into the item-8 exporter (staged), and runs watch 27."
W366-HANDLES (`MNielsenHandles`, the handle extension of the finite lists) is
missing.

**L4. `w365-gauss-note.md` has nine lines over 100 columns. FLAGGED (another
lane's frozen note).** All nine are Markdown table rows, the standing exception,
and ruling 4 is prospective. Recorded so the next scan does not re-raise it.

**L5. The memo's own item-5 annotation ran to 107 columns. FIXED**, reflowed in
the same commit as H1, and its tense made consistent (the paragraph had already
been moved to the past tense, so "Original item text follows" was no longer
literally true; it now says so).

**L6. The index's "Landed after this index's base" section was stale. FIXED.**
All four documents it listed as in flight at `d2056503` are tracked at
`9dd8a307` and are now classified.

### Verified clean, with the measurement

These were checked and are **not** defects. They are recorded because three of
them look like errors until measured.

1. **The three durable W365 reports hash exactly as handoff section 4 claims.**
   Recomputed here with `shasum -a 256`:

   ```
   8c47b4aa93b17009db0715c1944f31194f357cb202380b5fe9f718ac64804920  w365-fresh-build-result.json
   925e22635b17a44b2bbdcc2f064cce07bac611f5eb1ac5657a0fcd56c1b3d941  w365-fresh-build-provenance.json
   05e3e2c17bbcd3f7260cdf9f068783a5b097f37cf73d3aba71538a4753ea42cb  w365-fresh-verification-report.json
   ```

   Three of three match.
2. **Their contents match section 4 too**, field by field: `total` 1565,
   `completed` 1565, `failed: []`, `unbuilt: []`, `seconds` 2080.185,
   `live_source_drift: []`, `live_manifest_drift: false`, 3,727 entries in
   `output_file_sha256`; provenance `jobs` 6, snapshot started
   `2026-09-18T03:28:06` UTC, `lean_sha256` `1b370cfc...`, `manifest_sha256`
   `3c3d5e1a...`, `driver_sha256` `21b8f1d7...`; report `status: PASS`,
   `modules` 1565, `replayed: true`, `current_live_source_match: true`,
   `local_output_files` 3727. The report's own `provenance_sha256` field equals
   the recomputed hash of the provenance file, so the two are cross-bound from
   the inside as well.
3. **`GaussPhaseValues.lean` re-elaborated in this lane** through
   `scripts/w361_lean_runner.sh` against the shared cache: **exit 0, no errors,
   no warnings, 25 pins**. The merge message's axiom claims are exact --
   the structure and its three projections axiom-free, `GaussValCell.value` on
   `[propext]` alone, the three cell constants and six `rfl` simp lemmas
   axiom-free, and the **eleven substantive theorems exactly
   `[propext, Classical.choice, Quot.sound]`**. No standing input, as claimed.
4. **The 180-pin collision between two merge messages is a coincidence, not a
   relay error.** W364-AUDIT2's merge says "all 180 pins of the **three** modules
   ... 70/70, 16/16, 94/94"; W364-PACKET's says "**Four** modules re-elaborated
   by the lane: 180 pins". Both are right and the note behind each agrees with
   it: AUDIT2's three are 70 + 16 + 94 = 180, and PACKET's four are
   `MFullStabilizerLift` 10 + `NFullStabilizerLift` 6 + `MNielsenGenerators` 70
   + `NNielsenFactorization` 94 = 180. Different module sets, same total.
5. **217 and 397 both verify exactly.** The nine wave-362 M modules pin
   11 + 16 + 111 + 25 + 12 + 10 + 5 + 9 + 18 = **217**, and with the three
   Nielsen modules' 180 that is **397**, which is what W364-AUDIT2's merge
   message and campaign-log section 199 both assert.
6. **Section 198's declaration count was already corrected.** W364-HOUSE's L7
   flagged "~190 declarations"; the log now reads "216 declarations at merge
   (217 after the W363 consolidation)". Verified at 217. L7 is discharged.
7. **Line counts in the merge messages are exact.** W364-AUDIT2's "1102 lines"
   = 898 (`w364-nielsen-independent-audit.md`) + 204 (`w364-nielsen-scope.md`).
   W364-PACKET's "542 lines" for `w364-proof-packet-amendment-mc.md` is exact.
8. **Em-dash scrub over the window: clean.** No file the window touched gained
   an em-dash. Two exist in touched files -- `GQ2.lean:246` and the memo's own
   title -- and `git log -S` puts both before `d2056503`.
9. **Registration is complete and binds to the fresh build.** 1,570 `.lean`
   files under `GQ2/`; the board finds the same **six** outside the umbrella
   (`GQ2.AxiomLedger` plus the five `Dyadic/Word/*Export` drivers, all
   intentional); 1,570 - 6 + 1 root = **1,565**, exactly the module count of the
   fresh build in section 4. The one new module is imported at `GQ2.lean:891`.

## T2, the decision's consequences

The sweep was narrower than it looks. Greping `docs/dyadic/` for the three
shapes -- MC-M/MC-N stated as open, the proof method stated as unaccepted, the
push stated as pending -- returns **eight** documents plus the vendored packet,
and no others. `plan.md`, `tickets.md`, `mc-design.md`, `recon/mc-survey.md`,
`literature-axioms-dyadic.md`, the ledger and every W363/W364 lane note mention
MC without ever asserting its status, so none needed an annotation.

### Annotated in this lane

| Site | What it said | Annotation |
| --- | --- | --- |
| `owner-items-2026-08-05.md:5` | "Seven items await you" | Corrected to five; H1 above |
| `w361-proof-packet-amendment.md` head | dated pointer to the W364 successor only | 2026-09-18 paragraph: the MC proof-method question is decided, Option A, both cores |
| `w361-proof-packet-amendment.md` section 4 | "proof-method reconciliation remains" | one-line note that it no longer remains |
| `w361-proof-packet-amendment.md` decision item 4 | "Accepting ... or separately constructing that literal presentation artifact" | DECIDED, Option A, and the artifact was built too |
| `w361-acceptance-readiness.md` head | dated pointer to the W364 successor only | 2026-09-18 paragraph, same content |
| `w361-acceptance-readiness.md` item 4 | "accept the new uniform filtered proof method or construct that additional literal presentation" | DECIDED, Option A, at M as well as N |
| `w361-index.md` class definition | "None of these is approved" | records that one has since been decided, and which |
| `w362-claude-handoff.md` sections 5, 7, 8 | see T3 | rewritten, not annotated |

No body text was rewritten in the two W361 documents. Each annotation is dated
and points at item 4 of the memo, so both stay the record of their date. That
also **answers question (3) of the MC-N decision row** in
`w364-acceptance-readiness-mc.md`, which asked whether those two W361 items are
superseded or retained: superseded on the proof-method point, retained as
dated records.

### The index, extended

`w361-index.md` is retitled to W360-W366 and gains a **part three** for waves
365 and 366, compiled against `9dd8a307`: eleven documents in five classes,
including the four part two had left in flight and the three durable W365
reports (with the recomputed hashes in their rows). The three wave-366 lane
notes still on their own branches are named in an "in flight" section, with
`w366-apply-note.md` marked read-first. Flags 5 and 6 are re-judged against
`9dd8a307` (**flag 6 CLOSED**, flag 5 half addressed) and two new flags are
added, 7 and 8, which are findings M4 and L1/L2 above.

## T3, the handoff

Four changes, no verification fact touched. Section 4 was read closely for T1
and every number in it was re-derived, not edited.

1. **Section 5's ordering** now starts after Option A. See H3.
2. **Section 5's draft** carries its correct as-of commit and each documentation
   item carries its outcome. See H2 and M4.
3. **Section 5's carried-forward item 4** said the memo's newest block is wave
   89 reading "Zero items await you" while the board printed seven, and told the
   reader not to resolve the disagreement. Both halves are overtaken: the docket
   was folded into the memo, and after this lane both sides read five. The
   standing instruction is kept in the form that still binds -- only the owner
   decides an item; a lane may correct the memo's *count* to match decisions the
   owner has already recorded, which is exactly what H1 did and no more.
4. **Sections 7 and 8.** The reading list gains `w365-gauss-note.md` and all
   four wave-366 lanes, in an entry that tells the reader to read the memo's
   item 4 first because every one of them is downstream of Option A. Items 7 and
   9.7 carry the decision. The first prompt drops "Option A/B on the proof
   method and the push" and "the push is an owner item, not a default", and
   names the five items that actually remain.

## Sites the APPLY lane must handle

These are in files this lane is forbidden to touch. As of this lane's read, the
`claude/w366-apply` branch already covers the first five thoroughly; the list is
a cross-check, and the last two are the residue.

| # | Site | What is stale | Covered on `claude/w366-apply`? |
| --- | --- | --- | --- |
| 1 | `refs/dyadic-presentations-formalization-proof.tex:1077-1082` | the MC-M and MC-N rows still state the finite-Nielsen-list criterion as the obligation | yes |
| 2 | `refs/dyadic-presentations-formalization-proof.tex:730-735` | `prop:marked-reduction`'s lifting assertion | yes |
| 3 | `refs/dyadic-presentations-formalization-ledger.md` | had no MC rows at all | yes, rows added |
| 4 | `w361-completion-audit.md:43` and `:187-188` | "either that presentation artifact or acceptance of the alternative proof method remains" | yes, both rows marked discharged |
| 5 | `w364-proof-packet-amendment-mc.md` and `w364-acceptance-readiness-mc.md` | headed "PROPOSAL ... Not approved"; the "Decision needed" rows | yes, marked adopted for the applied parts |
| 6 | **`w361-completion-audit.md:278-280`** | the recommendation "MC-N's full mathematical assertion is now proved; **reconcile only its prescribed finite Nielsen-list proof method with the new uniform proof**" is a live instruction to do something Option A settled | **no** -- the lane's diff has two hunks, at `:41` and `:184`, and does not reach this one |
| 7 | `w364-acceptance-readiness-mc.md:52`, MC-N decision (3) | asks whether the two W361 MC records are superseded or retained | partly -- this lane answered it by annotating both W361 records; the row should record the answer |

Two further sites are **not** the APPLY lane's and are listed so nobody assumes
they are: the campaign log's section 199 frontier and its addendum (findings M5
and L3) are the orchestrator's file, outside the repo; and the two Lean
docstring findings (M4, L1, L2) belong to whoever next holds an edit grant on
`NNielsenFactorization.lean` and `GaussPhaseValues.lean`.

## Owner items

Read off `docs/dyadic/owner-items-2026-08-05.md` after this lane's H1
correction. **Five await the owner**, and they are the memo's items 1, 2, 3, 6
and 7, renumbered here only so that this section and the memo present the board
with the same number:

1. Adoption of the changed M pair/mobile words (memo item 1).
2. The corrected RN source interface and the existential realization and
   calibration quantifiers in the general endpoint statement (memo item 2).
3. The symbolic display contract and the treatment of the legacy L/N artifacts,
   now carrying publication decisions 13 to 17 of `w363-pub2-note.md` (memo
   item 3).
4. The untracked working copy of the QA-pinned 29-page PDF under `/output/`
   (memo item 6).
5. G3 / release, the owner's gate as before (memo item 7).

**Decided on 2026-09-18 and therefore not counted above.** Memo item 4:
acceptance of the uniform filtered-correction and compactness proof method for
both cores -- **Option A**, with the finite Nielsen-family lists satisfying the
packet's section-14 sentence in the families reading. Memo item 5: the push --
**done**, `488e7cf2..b9ad374f`, 370 commits, GitHub level with local.

The board's two sides now read five and five. They read 7 against a missing
heading when the T4 baseline ran, for the two separate reasons recorded there.

Nothing in this lane is an owner call of its own. The one number it changed, the
memo's headline count, was changed only to match decisions the owner had already
recorded in the same file.

## Status

CLOSED. T1 to T4 done. Six documents changed, no Lean module touched, no script
touched, `generated/` untouched, nothing pushed.
