# W364-HOUSE lane note

Lane: housekeeping over waves 362, 363 and 364, plus the mechanical sections of the
next-session handoff.

Base: `d2056503` (branch `claude/w364-house`, worktree
`/Users/roed/claude/cla/worktrees/w364-house`, Lean 4.31.0-rc2).
Round window: `6770a87e..d2056503`, 138 commits.

Status: CLOSED. T1 to T4 done; four documents changed, no Lean touched.

## Tickets

- T1 the round (watch 26): docstrings vs statements, counts, citations, honesty
  splits, headline-vs-binder gaps, em-dash scrub, long lines, registration scan,
  merge-message relay check.
- T2 the handoff's mechanical sections (3, 4, 7; draft 5; leave 1, 5, 8 marked).
- T3 the index extension.
- T4 the scoreboard baseline.

## Staleness check, done first

**The shared cache does not describe this lane's base.** At the moment this lane
ran, the main clone
(`/Users/roed/claude/cla/work/gq2-dyadic-campaign`) was at `06daa54a`
("merge W363-PUB2: all six missing L/N exporters, staged, with a five-kind
binding taxonomy"), eleven commits past this lane's base `d2056503`. Everything the
shared cache at `/Users/roed/claude/cla/work/main-build-cache` yields, including
every scoreboard row, therefore describes `06daa54a`, not `d2056503`. That is the
same trap the W362-HOUSE lane recorded, and it has not gone away.

The correction is benign here and checkably so: `d2056503..06daa54a` touches no
`.lean` file under `GQ2/` and does not touch `GQ2.lean` (it adds staged exporter
artifacts under `generated/` and `scripts/`), so no declaration's axiom footprint,
pin count or import closure can differ between the two. Declaration *counts* over
the whole tree are unaffected for the same reason.

A second process was in flight during this lane: an orchestrator-owned
`scripts/w361_fresh_build.py --require-live-match` run, building into its own
private snapshot under `/private/tmp/gq2-w361-fresh-*`, not into the shared
cache. It does not race the probes below.

`NNielsenFactorization.olean` was present in the shared cache before any probe in
this lane was run.

## T1, the round (watch 26 in the Claude numbering)

Scope: every module and note landed in `6770a87e..d2056503`, 138 commits. The
window contains **twelve** new registered modules under `GQ2/`, **one** new
unregistered exporter driver under `scripts/` (so thirteen new `.lean` files),
fourteen new documents under `docs/dyadic/`, five new scripts, and 43 new files
under `generated/`. Exactly one pre-existing `.lean` file was modified,
`GQ2.lean`, and it gained twelve import lines and nothing else.

Findings are ranked by severity. **FIXED** means this lane changed the tree;
**FLAGGED** means it did not, either because the fix is in a Lean module (the
audit lane's remit, not this one's) or because it is another lane's frozen
record.

### HIGH

**H1. `NNielsenGenerators.lean`'s module docstring asserts the non-existence of
declarations that now sit in the same directory. FLAGGED (Lean, comment-only).**

`GQ2/Dyadic/MarkedCore/NNielsenGenerators.lean:14-22` says, of the packet's
MC-N finite-list artifact, "**It cannot be produced yet**", and gives as the
reason "there is no `nNielsen_factorization` and there are no `nFamN1` through
`nFamN6` values anywhere in `GQ2/`. The six N families live only in the design
memo."

At `d2056503` all eight named objects exist, in
`GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean`: `nFamN1` at `:138` through
`nFamN6` at `:158`, `nNielsen_factorization` at `:357`, and the artifact itself,
`nNielsenFac_finite_list`, at `:758`. W364-NFACTOR built exactly the thing W363
recorded as impossible, one wave later, and nothing in `NNielsenGenerators`
points forward. The whole section headed "Why this is not the N twin of
`MNielsenGenerators`" is false as written.

The mathematics is untouched: nothing depends on the docstring, and
`NNielsenFactorization` imports `NNielsenGenerators` and consumes its bridge
exactly as intended. This is the highest-severity comment defect of the session,
and it is the one a next reader is most likely to act on, because it reads as a
research finding rather than as prose.

The same sentence is in `docs/dyadic/w363-nielsen-note.md`, section "The N
side". A lane note is a frozen record of its own wave, so the sentence was true
when written; but the note is also the document the reading list sends people to,
so this lane added an overtaken-by banner in the shape W363-MCONSOL used on the
six `w362-*-note.md` files. **FIXED (docs).**

### MEDIUM

**M1. The W363-MAUDIT documents pin nine source hashes and twenty-one source
line numbers, with no as-of commit, and all of them have drifted. FLAGGED.**

`docs/dyadic/w363-m-full-stabilizer-independent-audit.md` carries a
"Verification performed" table giving a SHA-256 for each of the nine wave-362
M modules. **All nine are now wrong**, every one. Fifteen of its twenty-one
`file:line` citations are also wrong, by a fixed per-file offset
(`MFullFrameCompactness` +6, `MBasisRowRefinement` +4, `MPlaneAmbientStage` +4,
`MFrameCupCoordinates` +6, `MFrameMatrixLift` +5 and then +9 past line 1100,
`MFullStabilizerLift` +33). Four examples, checked by hand in this lane:

| Audit says | Truth at `d2056503` |
| --- | --- |
| `mFullStabilizer_lift_of_frame` at `MFullStabilizerLift.lean:126` | `:159`; `:126` is mid-type |
| `mStageOneLe` at `MFullFrameCompactness.lean:31` | `:37`; `:31` is `noncomputable section` |
| `mBasis_mFiltered_mRelWord` at `MBasisRowRefinement.lean:49` | `:53`; `:49` is blank |
| `MCupFrameCupIsometry` at `MFrameCupCoordinates.lean:74` | `:80` |

**Every named declaration still exists, with the quoted text intact.** This is
pure drift, not a content error, and the verdict `PROVED AS STATED` is
unaffected. The cause is that four commits edited all nine modules *after* the
audit was written: `acffa057`, `492fe22e`, `20174284` and `6359d12a`, that is,
the W363-MCONSOL rename and docstring pass plus the copyright-header fix.

The audit's true base is **`69b9851c`**, established in this lane by recomputing
`MFullStabilizerLift.lean`'s SHA-256 at candidate commits:
`69b9851c` gives `bac55a1a4268bdc1bac2e647a9c2c6b3c70d1dba8c3483421ea57e9ee36da783`,
exactly the audit's figure, and `d2056503` gives
`cf6c7bbd928d8f31f23fa6b9dfe140e2b0d9325ac06ca8b5498779d0a45aebf3`.

This lane did **not** renumber the audit. Rewriting another lane's verdict
document is not housekeeping, and an audit whose citations are re-pointed by a
third party is worth less than one that says which tree it measured. The
repair is one line at the head of the document naming `69b9851c`, plus, if
anyone wants it, a mechanical renumber; that is the orchestrator's call. The
`w361-index.md` entry this lane wrote carries the flag so a reader meets it
before the table.

`docs/dyadic/w363-m-full-stabilizer-scope.md` has the same missing as-of hash
but no `.lean` line citations at all, so nothing in it has drifted.

**M2. "For every parameter" in the Nielsen modules, where the statement
quantifies over a parameter *plus a supplied inverse*. FLAGGED (Lean,
comment-only).**

`MNielsenGenerators.lean:27` says `mNielsenGen_orientation` and
`mNielsenGen_cupIsometry` "discharge both hypotheses **for every parameter**",
and the per-declaration docstrings at `:299-302`, `:435-437` and `:621` say
"every rank-four stabilizer parameter". The statements
(`:303`, `:438`) read

```lean
theorem mNielsenGen_orientation {alpha : ℕ} (ha : 2 ≤ alpha) (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) ...
```

that is, over a parameter **together with** an inverse parameter and two
pointwise inverse proofs, which is what `mNielsenGenEquiv` needs to be a
`ContinuousMulEquiv`. A grep over the whole of `GQ2/` finds **no** inverse,
group or `act_comp` structure on `MStabParam` or on `NStabParam`, so "every
parameter" is not a corollary anyone can currently take. The same pattern is in
`NNielsenFactorization.lean` at `:39-42`, `:502-503`, `:562-564`, `:686-687`
and `:949-951`, and there it is sharper, because the underlying
`nStabParam_fullFrame_lift_general` needs only `2 <= alpha` and `P.Admissible`:
the `Q` binder is this file's packaging, not the mathematics.

**The landed headline theorems are unaffected**, and that is why this is medium
and not high: `mNielsenGen_finite_list` and `nNielsenFac_finite_list` route
through the seven and eight explicit families, each of which supplies its own
inverse by construction (`mNielsenGen_M1_inv` and its siblings). The gap is
between the intermediate lemmas' prose and their binders.

**M3. M's quantifier-closure headline omits its own normalization binders.
FLAGGED (Lean, comment-only).**

`MNielsenGenerators.lean:837-844` claims in bold "**Every element of the
Smith-Witt stabilizer of the rank-four M abelianization is induced by an actual
`chiM`-preserving continuous automorphism of `D_M`**". The statement at
`:845-851` additionally takes an orientation character `chi` with four pinned
generator values and fixes the decomposition to
`(mNielsenGenFrame ha).toMDecomposition`. The lane note is honest about this
(its caveat 2 names it as `M.lean`'s inherited finding 6); the docstring is
not. The N twin at `NNielsenFactorization.lean:903-910` does spell its clause
out, so the two sides of the same wave disagree on how much to say.

### LOW

**L1. `MNielsenGenerators` cites the retained alias, never the public name.
FLAGGED (Lean).** Seven references to `mFullStabilizer_lift_of_frame` and zero
to `mFullStabilizer_lift`, in a module written after W363-MCONSOL freed the
plain name for exactly this theorem. Not a broken reference; both names exist
and `_of_frame` carries the identical statement. It is the rename drifting the
wrong way in a brand-new file.

**L2. Two added Lean lines exceed 100 codepoints. FLAGGED (Lean).**
`MFrameMatrixLift.lean:854` at 101 (a proof-term line) and
`MNielsenGenerators.lean:65` at 117 (a module-docstring prose line). Both are
comment- or formatting-level. The owner memo's ruling 4 makes the 100-column
target prospective and readability-qualified, so neither is a violation of a
freeze; they are simply the two lines the session added over the line.

**L3. Per-declaration docstrings in `NNielsenGenerators` omit the rank-four
restriction that the module header states. FLAGGED (Lean).** `:173-175`
(`nNielsenGenMat`) and `:206-209` (`nNielsenGen_cup_of_mat`) speak of "the
actual N frame"; both statements are at `NFrameModel 0`. The sibling
`nNielsenGen_lift_of_mat` at `:225-226` does say "rank-four", so this is an
inconsistency inside one file rather than a general omission.

**L4. Three docstrings describe the proof rather than the statement. FLAGGED
(Lean).** `MNielsenGenerators.lean:702-703` and
`NNielsenFactorization.lean:774-775` say the realization is "the composite of
the seven/eight Nielsen generators' lifts"; both conclusions are bare
existentials. `NNielsenFactorization.lean:350-351` says the Boolean slot "is the
identity when the `(1,0)` block entry is a unit"; the statement records only
`w = 0 \/ w = 1`.

**L5. One side claim in `MNielsenGenerators` is asserted, not proved. FLAGGED
(Lean).** `:75-77`, "The matrix that comes out is the transpose of
`mFrameMatrix_of_realizes`'s, as that dictionary predicts." No declaration in
the file states it; the file deliberately avoids making that comparison (which
is the point of not needing `Variance.lean`).

**L6. `MASSEMBLE`'s deliverables table has nine rows for ten declarations.
FLAGGED (docs).** `docs/dyadic/w362-massemble-note.md` row
"`mFullStabilizer_lift` (W363 rename; alias kept)" covers what are now two
declarations. The module has ten and is pinned ten times.

**L7. The campaign log's "~190 declarations" for the nine wave-362 modules
understates by about twelve percent. FLAGGED (docs, outside the repo).**
Section 198 of `~/claude/cla/outputs/dyadic-general-K-proof-campaign-plan-2026-08-02.md`
says "Nine new modules, ~190 declarations". The audited figure at the wave's
close was **216**, and it is **217** now. The log is the orchestrator's file.

**L8. `NNielsenFactorization.lean:4`'s author line differs from its siblings**
("using Claude Fable 5.1" against "using Claude Opus 5"). That is accurate, not
a defect; recorded so nobody 'fixes' it.

**L9. The brief this lane was given says thirteen new modules and seven
`[ORCHESTRATOR]` placeholders.** There are twelve new registered modules (a
thirteenth new `.lean` file exists, `scripts/w362_ln_fox_export.lean`, an
exporter driver that intentionally stays outside `GQ2.lean`), and there are
eight placeholders, not seven: section 1 carries two. Section 3 of the handoff
is written to cover all thirteen files, with the distinction stated.

### Verified clean, and worth recording because each was a plausible failure

1. **The em-dash scrub is clean, absolutely.** Over every line added in
   `6770a87e..d2056503`, `generated/` excluded: **zero** em-dashes and **zero**
   en-dashes. The pre-existing hits (25 em-dashes in the owner memo, four in the
   W361 handoff, and a handful elsewhere) are all in Codex-era text that no lane
   of this session added.
2. **Registration is complete, checked twice by independent routes.** An
   import-graph walk over the sources and the scoreboard's own elaborated scan
   both give 1,569 modules under `GQ2/`, 1,564 in the `GQ2` closure, and the same
   six outside it. All twelve new modules are imported directly by `GQ2.lean`.
   The `public import` trap the predecessor recorded is still live: 588 of the
   tree's 5,065 import lines are spelled `public import`, and a scan matching only
   `^import ` misreads the closure. `GQ2.lean` itself uses none.
3. **Pin coverage is exact and total.** 397 declarations across the twelve
   modules, 397 `#print axioms` lines, no declaration unpinned and no pin naming
   a declaration that is not there. The honesty split is stronger than the N
   modules': there the pin set matched the **public** declarations, here the 17
   `private` ones are pinned too (380 public + 17 private = 397).
4. **Per-module pin counts match the notes, and the two that do not are
   explained.** 5/25/12/111/9/16/11/18/10/70/16/94. The two exceptions,
   `MHeadCleanup` (note 7, tree 5) and `MBasisRowRefinement` (note 9, tree 11),
   are the two-declaration move W363-MCONSOL made and documented; the arithmetic
   `-2 +2 +1` that note performs on the audit's 216 reproduces the tree's 217
   exactly.
5. **The merge messages are accurate.** All eleven were read against their lane
   notes. Every declaration count, pin count and headline claim in them is either
   correct at merge time or correct now. **No relay error was found beyond the
   one already caught.** W362-MHEAD's ticket figure "73 to 558" for the head
   module's import cost was corrected by W363-MCONSOL to the measured 459 -> 10
   (with 467 -> 19 and 469 -> 21 downstream), the correction is carried in the
   MCONSOL merge message itself, and the MHEAD note still carries the original
   figure as the ticket's, which is the right way round.
6. **`w362-pub-note.md`'s citations are exact: all 85 of them.** That includes
   every bare `:NNN` continuation, the four non-declaration "inline at"
   pointers, and its negative claim that no `mpcJacobianCertUnram`,
   `_Ram` or `foxD_mpc_unram` exists anywhere under `GQ2/`. It is the
   best-cited document of the session and the only long one whose line numbers
   did not drift, because it cites pre-existing files that nobody edited.
7. **`w364-nfactor-note.md` is clean**: no `file:line` citations to drift, and
   all 37 declaration names it discusses are present. Its one external reference,
   `docs/dyadic/mc-design.md` section 3.4, is real (line 349) and contains the
   N1-N6 table and the completeness recipe the note says it found there.
8. **The packet citation resolves**, with one nitpick.
   `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex:732-735` is
   the lifting proposition's emphasised block, as claimed. The finite-list
   range cited as "lines 1077-1082" is really 1077-1080 for MC-M and 1081-1082
   for MC-N; documents that quote the range for one row alone are two lines wide.
9. **The three Nielsen modules are hygienic.** No `sorry`, `admit`,
   `native_decide`, `set_option`, bare `axiom` or em-dash in any of them. The
   `-` characters in `NNielsenFactorization.lean` at `:32` and `:252-253` are
   U+2212 minus signs inside mathematics, not dashes. All three carry copyright
   headers, which is more than the N siblings `NFullStabilizerLift.lean` and
   `NStabilizerFullLift.lean` do.
10. **The compactness-versus-generator honesty split is present and explicit in
    both Nielsen modules**, in bold, in the module docstring and again at the
    headline theorem: `MNielsenGenerators.lean:41-48` and `:682-684`,
    `NNielsenFactorization.lean:65-75`, `:755-757` and `:955-958`. Both also
    disclaim "finite generating set" in favour of "finitely many families", and N
    additionally flags that its independent per-family route's N4 ingredient is
    itself a compactness limit. Codex's standing warning "do not call the
    finite-list artifact done" is respected at both cores.
11. **`MFullFrameStages.lean`'s missing copyright header, which W363-MCONSOL
    explicitly left open, was closed** by `6359d12a`.
12. **No `[ORCHESTRATOR]` placeholder was filled by guesswork**, and the three
    reserved for the orchestrator are still marked.

### Proposals, kept separate from the findings above

- **P1.** Add one line to the head of
  `docs/dyadic/w363-m-full-stabilizer-independent-audit.md` naming `69b9851c`
  as the tree it measured. That converts fifteen stale citations and nine stale
  hashes from errors into a dated record. A mechanical renumber is optional and
  strictly less valuable.
- **P2.** The `mHead_` prefix on the two declarations now living in
  `MBasisRowRefinement.lean` records where they were first stated, not where
  they live. W363-MCONSOL left this deliberately, with zero consumers. It stays
  a free change for as long as nothing outside the tree references them.
- **P3.** `docs/dyadic/w361-index.md` is now an index of a corpus it no longer
  names. This lane extended it and retitled it rather than starting a second
  index, on the grounds that two indexes are worse than one long one; if a later
  wave disagrees, the W362-W364 section is a clean cut point.

## T2, T3 and what this lane changed

**T2, the handoff.** `docs/dyadic/w362-claude-handoff.md` keeps its filename and
is retitled "W362-W364 handoff to the next session". Filled by this lane:
section 3 in full (twelve registered modules plus the exporter driver, one table
per mathematics lane in the W361 module / reusable content / public pins shape,
two plain-text chain diagrams, and fourteen pitfalls collected from the notes);
section 4's verification record (the per-module pin census, the registration
check by two routes, the scoreboard invocation and result, the gate invocation
with its last recorded output, and an explicit statement that no clean-build or
replay record exists for the session's end state); and section 7's reading list
(fifteen documents in dependency order, with the two audits placed before the
notes they judge and `w363-mconsol-note.md` before any `w362-*-note.md`).

Section 5 carries a **draft** remaining-work list assembled from the notes, in
three groups (mathematics, publication, documentation repairs), under an
unchanged `[ORCHESTRATOR]` marker. Sections 1 and 8 are untouched and still
marked, as is the one placeholder in section 2 about the shared-cache
convention, which was assigned to no lane and which this note records so it is
not lost.

Section 3's tables were reflowed: the "reusable content" cell is `see below` and
the content sits in a wrapped bullet under each table, because the W361 cell
shape does not fit inside 100 columns. Every line the handoff now carries is
inside 100 codepoints and there are no dashes.

**T3, the index.** `docs/dyadic/w361-index.md` keeps its filename, is retitled
"Index of the W360-W364 document corpus", and gains a second part covering the
session's fifteen documents in the same six classes, with each part's base hash
stated at the head. It also gains the "where the Claude session's records live"
paragraph (the tree, the owner memo, campaign-log section 198 onward, session
memory) and two new flags, 5 and 6, for the audit drift and the live
non-existence docstring.

*One stated exception.* Fifteen of the lines this lane added to the index exceed
100 codepoints. All fifteen are rows of the index's own one-line-per-document
table, whose 73 existing rows are the same shape; wrapping them would break the
format the file is named after. This is a deliberate choice under the memo's
ruling 4 ("at most 100 Unicode codepoints **where readable**"), recorded here so
that it reads as a decision rather than as an oversight. Every other line this
lane added anywhere, in any file, is inside 100.

**What this lane changed in the tree**

| File | Change |
| --- | --- |
| `docs/dyadic/w364-house-note.md` | new, this note |
| `docs/dyadic/w362-claude-handoff.md` | retitled; sections 3, 4, 7 filled; section 5 drafted |
| `docs/dyadic/w361-index.md` | retitled; part two added; flags 5 and 6 added |
| `docs/dyadic/w363-nielsen-note.md` | one overtaken-by banner, in the shape W363-MCONSOL used |

No `.lean` file was touched. No script was touched. `generated/` was not touched.
Nothing was pushed.

## Verified counts

All re-derived at `d2056503` by this lane, not carried from a note.

| Quantity | Value |
| --- | ---: |
| Commits in the round (`6770a87e..d2056503`) | 138 |
| New registered modules under `GQ2/` | 12 |
| New `.lean` files in total (with the exporter driver) | 13 |
| Pre-existing `.lean` files modified | 1 (`GQ2.lean`) |
| Declarations in the twelve modules (380 public + 17 private) | 397 |
| `#print axioms` pins in the twelve modules | 397 |
| Declarations unpinned, and pins naming no declaration | 0 and 0 |
| Pins that are not std-3, across the twelve | 0 |
| `.lean` files under `GQ2/` | 1,569 |
| Those in the `GQ2` import closure | 1,564 |
| Outside it (unchanged exception set) | 6 |
| `public import` lines tree-wide, of 5,065 import lines | 588 |
| Em-dashes and en-dashes added in the round | 0 and 0 |
| Added lines over 100 codepoints, `generated/` excluded | 144 |
| Of those, in `.lean` sources | 2 |
| New documents under `docs/dyadic/` | 14 |

Per-module pins: `MHeadCleanup` 5, `MFullFrameCompactness` 25,
`MFullFrameStages` 12, `MFrameMatrixLift` 111, `MInitialCupDepth` 9,
`MFrameCupCoordinates` 16, `MBasisRowRefinement` 11, `MPlaneAmbientStage` 18,
`MFullStabilizerLift` 10 (subtotal 217, matching W363-MCONSOL's own re-elaborated
figure), `MNielsenGenerators` 70, `NNielsenGenerators` 16,
`NNielsenFactorization` 94.

## Owner items

Seven, the same seven the owner's own memo now carries. `6b302efd` folded the
Codex-era docket into `docs/dyadic/owner-items-2026-08-05.md` as a
"Status at wave 362 (2026-09-17)" block reading **Seven items await you**, so the
memo is no longer a month stale and the W362-HOUSE note's prediction that the
board would print seven against zero is itself now out of date. This lane's list
is the memo's list, item for item, so that the board's two sides agree; where the
waves since W362 have moved an item's *substance* without changing the count, that
is said inside the item and not by renumbering.

1. **Adoption of the changed M pair/mobile words.** Unchanged since W362.
2. **The corrected RN source interface**, and the existential realization and
   calibration quantifiers in the general endpoint statement. Unchanged.
3. **The symbolic display contract and the treatment of the legacy L/N
   artifacts.** Moved, without changing the count: W362-PUB staged
   `generated/general-ln-certificate-staged/` (seven sectors, items 4 and 5
   serialized behind 21 `rfl` signature theorems) and re-measured the gap as
   **one exporter layer, not eight missing proofs**. The staged directory is a
   proposal, not an adoption; the five `generated/appendix/` skeletons still
   carry their 40 `\dyadicAppendixTODO` slots.
4. **Acceptance of the uniform filtered-correction and compactness proof method**
   for both stabilizer-lifting obligations. **This is the item the waves since
   W362 moved most, and it is now sharper rather than closed.** The memo's
   sentence "the packet's section 14 finite Nielsen-generator list is a separate
   artifact; W363-NIELSEN is attempting it" has been overtaken twice: W363-NIELSEN
   landed the MC-M list (`mNielsenGen_finite_list`, seven slots, rank four) and
   W364-NFACTOR landed the MC-N list (`nNielsenFac_finite_list`, eight slots, rank
   four) together with the previously absent `nNielsen_factorization`. Both lists
   exist; both lane notes state in terms that their members' lifts still come from
   the compactness theorem, not from generator-level constructions. So the owner
   call is no longer "accept the method or commission the artifact": the artifact
   exists, and the call is whether the packet's wording is satisfied by a finite
   list whose members lift *by* the compactness theorem. W364-NFACTOR narrows it
   further at N, where a second, independent per-family route exists
   (`nNielsenFacLifts_of_param_families`) but its N4 ingredient is itself an
   N-plane compactness limit. The residue of the original call is therefore
   exactly: M4, M5, M6, M7 at M (no group-level construction anywhere in the
   repo), and N4 at N.
5. **The push.** Unchanged; nothing was pushed by this lane.
6. **The untracked working copy of the QA-pinned 29-page PDF** under `/output/`.
   Unchanged.
7. **G3 / release.** Unchanged; the owner's gate.

Nothing in this lane is an owner call of its own. Everything else it found is
either a verified fact or a proposal, and the two are kept apart below.

## T4, the scoreboard baseline for the next session

Run from this worktree, both modes, exit 0 each:

```sh
GQ2_MIR=/Users/roed/claude/cla/work/main-build-cache/lib/lean \
GQ2_PKG=/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages \
bash scripts/scoreboard.sh [--raw]
```

Header of record: `tree 67c7edd7 2026-09-17   branch claude/w364-house`. That is
the hash of the commit this lane was on when the board ran, not the lane's base;
`--raw` at the base `d2056503` and the formatted run at `67c7edd7` give identical
structural rows, the intervening commits being documents only.

| Row | Baseline |
| --- | --- |
| `EXISTS` | 1,084 |
| `MISSING` | 0 |
| `STALE_UMBRELLA` | 0 |
| `UNVERIFIED` | 2 |
| Modules on disk under `GQ2/` | 1,569 |
| `OUTSIDE` the umbrella | 6 |
| Raw records emitted (`SB\|`) | 1,172 |
| Rows printing `std-3` alone | 984 |
| Rows carrying at least one standing input | 100 |
| Owner items, memo | 7 |
| Owner items, newest house note | 7 |
| Verdict | `memo and note AGREE  7` |

The two `UNVERIFIED` are both prose-level and both expected: the A6 review-round
count, which is a function of the adoption wave and is not in git, and the
per-item status of the owner docket, which the board's own contract refuses to
certify. **Neither is a regression, and neither should be "fixed".**

The six `OUTSIDE` modules are `GQ2.AxiomLedger` (it imports `GQ2`, so registering
it would cycle) and the five exporter drivers
`GQ2.Dyadic.Word.General{Fox,PhaseCover,Phase,,LN}...Export`. Unchanged since
W361. This is the board's only blind spot and the registration section is the
check for it.

**The OWNER ITEMS row, against the memo's seven.** The memo's newest block is
"Status at wave 362 (2026-09-17)" reading **Seven items await you**; the board's
artifact side is now `docs/dyadic/w364-house-note.md`, whose "Owner items"
heading the board found, with seven numbered items under it. They agree. (The
board reported that heading at line 54; this note has grown since that run, so
the line has moved and the heading has not.)

Two mechanical facts about that agreement, for whoever reads the board next:

1. **The artifact side moves to the newest house note automatically**, by a
   numeric sort over `docs/dyadic/w*-house-note.md`. Creating this note displaced
   `w362-house-note.md`. A house note with no "Owner items" heading makes the
   board print `NOT FOUND` where it used to print a count, which looks like a
   regression and is not; this note carries the heading for that reason, and the
   heading shape the board accepts is documented in the script's own header.
2. **Agreement at seven is new.** W362-HOUSE predicted a standing disagreement
   between the memo's zero and its own seven, because the memo had not been
   touched since wave 89. `6b302efd` folded the docket in. The prediction in
   `w362-house-note.md` and in section 5 of the W361 handoff is therefore itself
   now out of date, and the count agreeing does **not** mean the docket stopped
   moving: item 4's substance changed twice during this session (see "Owner
   items" above) without changing the count. Read the item text, not the number.

## Method note, for the next housekeeping lane

Three things cost time here and are cheap to avoid.

1. **Diff against your own base before believing any cache-derived number.** The
   main clone moved to `06daa54a` while this lane ran. The check that made the
   numbers usable was `git diff --name-status d2056503..06daa54a`, which showed
   nothing under `GQ2/` and no `GQ2.lean`; that is what licences the transfer,
   not the smallness of the diff.
2. **Measure added lines, not files.** A first pass over whole files reported
   em-dashes in six documents and long lines in fifteen. Restricted to the lines
   the round actually added, the em-dash count is zero and the long-line count is
   144, almost all in Markdown tables. Whole-file greps measure the corpus, not
   the wave.
3. **When a lane note and the tree disagree on a count, look for a later move
   before calling it an error.** Every one of the four count mismatches this lane
   found (`MHeadCleanup` 7 to 5, `MBasisRowRefinement` 9 to 11,
   `MFullStabilizerLift` 9 to 10, and the audit's 216 to 217) is a W363-MCONSOL
   edit, and MCONSOL's own note does the arithmetic explicitly. None is a
   reporting error.
