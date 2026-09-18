# Index of the W360-W364 document corpus

Two parts. The first, the W360/W361 corpus, was compiled by the **W362-HOUSE**
lane against the tree at `6770a87e`, the commit that first tracked all 71 of
those files; every entry in it was read at that hash. The second, the W362-W364
session, was added by the **W364-HOUSE** lane against `d2056503`, and every
entry in it was read at that hash. Neither part is carried over from an earlier
note.

The W360/W361 corpus is 69 Markdown documents and 2 JSON verification reports,
all matching `docs/dyadic/w36[01]*`. The W362-W364 session adds 15 more
Markdown documents, plus this file. Six classes are used, the same six in both
parts:

- **verified record** -- states what a checked artifact proves or what a run
  observed. Cite these.
- **audit** -- an independent read-only review reaching a verdict.
- **scope note** -- delimits what a result does and does not say, or maps the
  next task. Carries no new theorem.
- **proposal (not adopted)** -- proposes a statement, format or migration that
  needs an owner decision. None of these is approved.
- **handoff** -- wave-boundary state transfer.
- **template** -- describes a staged export format and its Lean bindings.

A document's class is what it *is*, not what it covers: an audit of a template
is an audit.

## Start here

`w362-claude-handoff.md` is the current entry point. It defers to
`w361-claude-code-handoff.md` for anything the Codex pass settled, and
`w361-claude-code-verification-report.json` is still the evidence binding the
last whole-tree replay. Everything else is reachable from those three.

## Where the Claude session's records live

Four places, and only the first two are authoritative.

1. **The tree.** `docs/dyadic/`, indexed below, and the Lean itself. A module's
   docstring is the record of what that module proves; a lane note is the record
   of how it got there and what it deliberately did not do.
2. **The owner's memo,** `docs/dyadic/owner-items-2026-08-05.md`. Its newest
   block is "Status at wave 362 (2026-09-17)", reading **Seven items await
   you**, which folded in the whole Codex-era docket that had accumulated since
   the wave-89 block. Only the owner amends it. `scripts/scoreboard.sh` prints
   that count against the newest house note's and says whether they agree; a
   disagreement is the board's product, not a failure, and is never to be fixed
   by editing a number into the script.
3. **The campaign log,** `~/claude/cla/outputs/dyadic-general-K-proof-campaign-plan-2026-08-02.md`,
   **section 198 onward**. Section 198, "Wave 362: the M full-stabilizer lifting
   theorem, in one wave, after the Codex handoff", is the narrative record of
   this session: the interregnum (Codex's waves 89 to 361, of which only 89 to
   187 have sections of their own, the rest living under `docs/dyadic/`), the
   seven lanes plus the assembly lane, the verification figures, and the live
   frontier. At `d2056503` section 198 is the last section; waves 363 and 364
   are recorded only here and in their lane notes, and the orchestrator writes
   their sections at the session's close. The log is outside the repository and
   is not versioned with it.
4. **Session memory,** `~/.claude/projects/.../memory/`, which carries the wave
   states and the `codex-era-infra` facts. It is an index to the other three,
   not a substitute for any of them.

---

## Handoffs (3)

| Document | One line |
| --- | --- |
| `w360-restart-handoff.md` | W360 resumption state: the general even-M source and odd-L arithmetic, at local tip `2bf856c9`. Superseded. |
| `w361-restart-handoff.md` | The 17:30 UTC overnight checkpoint, 1,541 modules / 573 pins. Its own header sends readers to the Claude handoff instead. Superseded. |
| `w361-claude-code-handoff.md` | **Current.** The Codex-to-Claude transfer: full N stabilizer lifting proved, 1,552 modules, 691 pins, census eleven, remaining work and runtime commands. |

## Verified records (24)

| Document | One line |
| --- | --- |
| `w361-claude-code-verification-report.json` | The durable replay report binding the 1,552-module state; SHA-256 `aad5d041...`, verified in place. |
| `w361-final-verification-report.json` | The historical 1,541-module report; SHA-256 `bb20e991...`, verified in place. Does not cover the eleven N modules. |
| `w361-final-verification.md` | The 17:30 UTC source-bound verification contract and record, for the superseded 1,541-module state. **See flag 0: it says it is current and is not, and thirteen documents point at it.** |
| `w361-overnight-progress.md` | The 978-line running log of the 09:10-17:34 UTC pass. See flag 1: a forward-written log, not a current-state record. |
| `w361-compact-n-boundary-hessian-record.md` | Branch-free original compact-N Hessian record at every actual boundary lift. |
| `w361-npc-boundary-hessian-record.md` | Branch-free original Npc Hessian record at every actual boundary lift of the displayed source. |
| `w361-l-boundary-hessian-records.md` | Original L Hessian records at the actual boundary lifts, uniformly in the handle count. |
| `w361-l-hessian-records.md` | Original L phase-cover and Hessian records for `GammaL`, uniformly in `h`; records that the odd head is not the even compact head. |
| `w361-pair-mobile-boundary-hessian-records.md` | `pairBoundaryHessian` and `mobileBoundaryHessian` at the original radical-cover boundary lift. The shortest document in the corpus (23 lines). |
| `w361-hessian-phase-records.md` | Original Hessian and phase-cover records at arbitrary handle rank for the corrected/spliced M words. |
| `w361-polar-normal-certificate.md` | Basis-independent polar normal certificate for the common even phase. |
| `w361-wall-polar-inverse.md` | Arbitrary-diagonal wall polar inverse, uniform in the handle count. |
| `w361-l-polar-polynomial-inverse.md` | Finite polynomial inverse for the odd L head, uniform in action period and handle rank; closes a limitation recorded in `w361-l-hessian-records.md`. |
| `w361-fox-polynomial-inverse.md` | Closed finite-sum inverse of the unramified Fox pivot under a fixed-point-free odd-period action. |
| `w361-ramified-fox-polynomial-inverse.md` | The ramified Fox inverse as a finite polynomial in the sigma and tau actions. |
| `w361-ramified-fox-normal-certificate.md` | The actual ramified differential of the compact-template splice and its explicit invertible row operations. |
| `w361-scalar-fox-normal.md` | The literal scalar Fox matrix for the actual changed pair and mobile sources. |
| `w361-polynomial-fox-certificates.md` | Literal polynomial inverses inside the original `FoxCertificate` records. |
| `w361-original-certificate-record-bridge.md` | Which original certificate records the actual changed words now instantiate, sector by sector. |
| `w361-fox-input-template-binding.md` | Six full input-matrix identities binding the exported Fox templates to the actual inputs. |
| `w361-general-ln-denotation.md` | Exact denotation of the existing raw L/N factories at arbitrary rank and parameters. |
| `w361-n-plane-actual-mixed-congruence.md` | Checked arithmetic-free mixed-power and relative correction congruences in an arbitrary topological group. |
| `w361-n-plane-compactness.md` | The general-rank exact-row compactness reduction as an iff. See flag 2. |
| `w361-word-display-layout.md` | The four overfull word-display lines and the display-plan-only fix; no word, AST, schema or hash changed. |

## Audits (29)

| Document | One line |
| --- | --- |
| `w361-completion-audit.md` | The campaign-level audit: mathematical endpoint versus acceptance, with an in-place 15:44 UTC status refresh. See flag 4. |
| `w361-final-endpoint-scope-audit.md` | Fresh re-elaboration of the public capstone; confirms the standard three plus nine for the original-marked endpoint. |
| `w361-independent-audit.md` | Interface and claim audit of the pair-splice and mobile-Mpc `FlexibleCertificateLeavesRN` closure. |
| `w361-marked-endpoint-independent-audit.md` | No loophole or circular marking in the five marked-endpoint modules; conclusion is existence with an existentially calibrated realization. |
| `w361-aligned-marking-audit.md` | No circularity or dropped source data in the aligned endpoint; calibration replaces only an existentially carried core realization. |
| `w361-arithmetic-assembly-audit.md` | No defect in the inertia / odd-cyclotomic / relative-norm chain or the canonical field data. |
| `w361-axiom-source-verification.md` | Clause-level primary-source verification for the AX3 and AX4 citation targets. Not an axiom change. |
| `w361-selected-word-audit.md` | Finds that the earlier existential theorem dropped the source constructor, and records the checked strengthening. |
| `w361-full-core-marking-audit.md` | What full marked reconstruction still requires; the fixed-frame exact-image theorem does not by itself give it. |
| `w361-n-full-stabilizer-independent-audit.md` | PASS on `nFullStabilizer_lift_iff`, with the exact equivalence spelled out. |
| `w361-n-arbitrary-basis-refinement-audit.md` | PASS on the three `NBasis*` modules plus `FreeProTwoMatrixBasis` and `NFrameMatrixLift`; all 58 pins read. |
| `w361-n-full-row-independent-audit.md` | Torsion-sensitive N core-row lifting verified, with a 17:30 UTC final-status addendum. |
| `w361-n-general-scaling-audit.md` | Uniform strong N-plane scaling; the reviewed scratch modules are now integrated under production names. |
| `w361-n-plane-scaling-audit.md` | What B8 scaling does and does not prove for N; the stronger statement is not needed by the completed endpoint. |
| `w361-n-plane-primary-source-audit.md` | None of the primary results examined supplies the exact simultaneous integral character action `NPlaneScalingHypothesis` wants. |
| `w361-n-plane-filtered-bridge-audit.md` | The filtered-group results do not by themselves discharge `NPlaneScalingHypothesis`; a header records that later work did. |
| `w361-n-plane-completed-ring-independent-audit.md` | Read-only audit and recompilation of the completed-ring and relative-boundary modules. |
| `w361-n-unrestricted-supply-sanity.md` | Sanity check of the uniform N-stage supply; sections 1-6 are the earlier snapshot, 7 and 8 the later results. |
| `w361-n-boundary-record-independent-audit.md` | PASS on the N-family boundary Hessian records; all five pins print exactly the standard three. |
| `w361-npc-hessian-independent-audit.md` | PASS on the full-offset Npc Hessian records; no source, resolver, coordinate or interface defect. |
| `w361-explicit-matrix-independent-audit.md` | The all-cochain unramified Fox and common-phase polar matrix identities are genuine and do not infer differentials from kernels. |
| `w361-ramified-inverse-independent-audit.md` | No defect in the polynomial inverse and Fox-matrix modules; conclusions are conditional matrix identities, not field-hypothesis discharge. |
| `w361-word-template-audit.md` | The staged templates denote the actual splice constructors, with literal `PWord` equality rather than evaluation equality. |
| `w361-certificate-packet-independent-audit.md` | Audit of the ten-item packet pipeline and the compact-N boundary adapter. Approves no fixture-gate replacement. |
| `w361-phase-renderer-boundary-independent-audit.md` | STAGED audit of the phase renderer; passed after two renderer-side parser fixes, no schema or hash change. |
| `w361-fresh-build-independent-audit.md` | Audit of fresh-build isolation and tau-column semantics. Its findings describe the pre-hardening scripts and are explicitly historical. |
| `w361-fresh-verifier-independent-audit.md` | Audit of the opt-in fresh-content verifier; three in-contract issues found, fixed and retested. Not a release gate. |
| `w361-staged-pdf-qa.md` | Review of the 29-page staged certificate PDF, with wrapper and output hashes. |
| `w361-l-n-certificate-readiness.md` | Family-level readiness audit of the L/N certificate producers against the ledger's ten-item standard. |

## Scope notes (7)

| Document | One line |
| --- | --- |
| `w361-n-full-stabilizer-scope.md` | What the full N stabilizer theorem does and does not settle against the original specification. |
| `w361-m-next-general-scaffold.md` | The next general M lifting task: coupled M-head divisibility and cleanup first, not a new class sweep. Research tasks, not hypotheses. |
| `w361-acceptance-readiness.md` | Readiness review separating proofs, artifacts and owner decisions. Explicitly not acceptance. See flag 4. |
| `w361-n-plane-unrestricted-stage-gap.md` | The N-stage gap and the ambient-stage route that closed it. See flag 3. |
| `w361-n-plane-strong-scaling-research.md` | Historical research checkpoint: six rank-uniform intermediate modules from when strong N-plane scaling was open. |
| `w361-tame-splice-mechanism.md` | Why a new source word was necessary and what the rank-uniform construction is. |
| `w361-compositional-certificate-map.md` | Connects the actual word constructors and checked transformations to the ledger's publication requirements. |

## Proposals, not adopted (5)

| Document | One line |
| --- | --- |
| `w361-proof-packet-amendment.md` | Proposed replacement statements for the packet's main theorem, marked-matching requirement, source interface and reconstruction proof. |
| `w361-pair-mobile-certificate-appendix.md` | STAGED parametric appendix giving all ten ledger items for the pair and mobile constructors. Not generated TeX, not an approved format. |
| `w361-word-template-proposal.md` | STAGED symbolic word templates: why no finite rational display represents the new two-adic coefficients. |
| `w361-n-plane-relative-graded-correction.md` | A proposed uniform relative mixed-Lie correction identity. Explicitly not a Lean theorem and not an assumed premise. |
| `w361-general-phase-cover-template.md` | STAGED typed phase-cover export format, with no owner approval or migration status. |

## Templates (3, plus 2 cross-references)

| Document | One line |
| --- | --- |
| `w361-general-phase-template.md` | The staged typed quadratic-phase export: syntax, bindings and hashes. |
| `w361-symbolic-fox-template.md` | The staged symbolic Fox-operation template: typed rows, carried inverse coefficients, finite-sum templates. |
| `w361-general-ln-export.md` | The staged all-parameter L/N export and replay, and the explicit statement that it does not finish the ten-item appendix. |
| `w361-word-template-audit.md` | (listed under Audits; the template it audits is described in `w361-word-template-proposal.md`.) |
| `w361-fox-input-template-binding.md` | (listed under Verified records; the binding it records belongs to the Fox template.) |

Counting each document once by its own class: 3 handoffs, 24 verified records,
29 audits, 7 scope notes, 5 proposals and 3 templates. That is 71. The two
parenthesised rows in the Templates section are cross-references to documents
already counted under Audits and Verified records, and are not recounted.

---

---

# Part two: the W362-W364 session

Added by the W364-HOUSE lane against `d2056503`. Fifteen documents, in the same
six classes. One further document, `w363-pub2-note.md`, had landed on the wave
branch but not in this index's base at the time of writing; see the note at the
end of this part.

## Handoffs (1)

| Document | One line |
| --- | --- |
| `w362-claude-handoff.md` | **Current entry point.** "W362-W364 handoff to the next session": skeleton drafted by W362-HOUSE at the open of wave 362, mechanical sections filled by W364-HOUSE at the close of wave 364. Sections 1, 5 and 8 remain the orchestrator's. |

## Verified records (10)

| Document | One line |
| --- | --- |
| `w362-mhead-note.md` | Step 1 of the M plan: the coupled ordinary-head cleanup `2 f(A) + 2^alpha f(C)`, the scalar divisibility step, and the same-class all-character-zero head representative. Its "all seven declarations" is now five, after the W363 move. |
| `w362-mkernel-note.md` | Step 2: the M defect characterized by the **N** plane-correction kernel through `evenRawStageShift_m`, the arbitrary-basis interpolation, and `mStageStep_holds`, which discharged the interface the other four steps were stated against. Its 9-pin figure is now 11. |
| `w362-minit-note.md` | Step 3: `mFrameLiftEquiv`, the initial free lift with literal fixed head `T = A C^(2^(alpha-1))`, 111 declarations, and the precise negative that independent torsion sections fail on the explicit shear `mFrameTorsionShear`. |
| `w362-mcup-note.md` | Step 4: `MCupFrameCupIsometry`, the semantic predicate over every continuous mod-two frame character, and the depth-three error; the MINIT hypothesis discharged rather than assumed. |
| `w362-mstages-note.md` | Step 5: torsion-retaining full-frame compactness, stage transfer, the all-depth induction, and the conditional composition. Torsion retention is checked in file, not asserted. |
| `w362-massemble-note.md` | The assembly: `mFullStabilizer_lift` and `mFullStabilizer_lift_iff`, unconditional, std-3, the exact twins of the N pair. Explicitly not one of the scaffold's five items. Its deliverables table has nine rows for what are now ten declarations. |
| `w363-mconsol-note.md` | The consolidation under an explicit nine-module edit grant: the rename map that freed the public name, the import-cost measurement (459 to 10 at the head module), nine docstring corrections, and the two audit flags folded in. The one document that reconciles the six W362 notes with the tree. |
| `w363-nielsen-note.md` | The MC-M finite list at rank four (seven families), the cup producer that reduced the semantic predicate to a finite `F_2` check, and the N-side bridge. **See flag 6: its "The N side" section is overtaken by W364-NFACTOR.** |
| `w364-nfactor-note.md` | The N factorization into six families, the *bounded* `GL_2(Z_2)` factorization in five slots, the eight-slot `nNielsen_factorization`, and the MC-N finite list. The best-behaved citation record of the session: nothing in it has drifted. |
| `w362-house-note.md` | Every Codex headline claim checked against the tree at `6770a87e`: 118 N pins std-3, registration complete, census eleven at source and environment level, the four publication counts exact. Also the shared-cache staleness lesson, which every later lane has had to apply. |

## Audits (1)

| Document | One line |
| --- | --- |
| `w363-m-full-stabilizer-independent-audit.md` | The proof-level independent audit of the nine wave-362 M modules. **VERDICT: PROVED AS STATED**, no mathematical caveat, no hidden premise, 216 pins inside the standard three. Three flagged items; FLAG-3 is still open. **See flag 5: all nine of its source hashes and fifteen of its line citations have drifted, and it names no base commit.** |

## Scope notes (2)

| Document | One line |
| --- | --- |
| `w363-m-full-stabilizer-scope.md` | The M twin of `w361-n-full-stabilizer-scope.md`: what the M theorem settles in the governing packet, and six remaining campaign requirements. Cites the endpoint by its pre-rename spelling `mFullStabilizer_lift_of_frame`; no `.lean` line citations, so nothing in it has drifted. |
| `w364-house-note.md` | This session's round (watch 26): the staleness check, the severity-ranked findings, the verified counts, the owner items matched to the memo's seven, and the scoreboard baseline for the next session. |

## Proposals, not adopted (1)

| Document | One line |
| --- | --- |
| `w362-pub-note.md` | The ten-item L/N inventory verified against the tree, the staged `general-ln-certificate-staged/` packets, and twelve owner decisions. Everything staged carries `status: "STAGED"`; nothing is adoption, appendix migration or census amendment. Its T1 inventory is a verified record and its 85 citations are all exact; its T2.d list of six missing exporters was supplied by W363-PUB2. |

## Templates (0)

None this session. The W362-PUB and W363-PUB2 exporter drivers under `scripts/`
are executables, not documents.

## Landed after this index's base

`docs/dyadic/w363-pub2-note.md` exists on the wave branch (present in the main
clone at `06daa54a`, "merge W363-PUB2: all six missing L/N exporters, staged,
with a five-kind binding taxonomy") but not at `d2056503`, this index's base, so
it is not classified above. It is the record of the six exporter drivers
`scripts/w363_ln_*_export.lean` and the artifacts they emit, and on its
description it is a **proposal, not adopted**, like its predecessor. The
W364 audit lane's documents, matching `docs/dyadic/w364-nielsen-*.md`, were in
flight at the same moment and are likewise absent here. Whoever extends this
index next should start from those two.

---

## Flags: where a headline outruns its body

The docstring-outruns-statement rule applied to prose. The corpus is unusually
disciplined -- almost every document states its own limits in its first
paragraph, and every `GQ2/*.lean` and `scripts/*` path cited anywhere in the
corpus resolves in the tree at `6770a87e`. (The single exception is
`GQ2/Dyadic/MarkedCore/NAME.lean` in
`w361-n-arbitrary-basis-refinement-audit.md:138`, which is the placeholder in
a command template, not a reference.) Five items still deserve a marker, and
the first of them is the one to act on.

**Flag 0 (the highest severity here) -- `w361-final-verification.md` asserts
a currency it no longer has, and thirteen documents point at it.**
Its opening words are "Final verified checkpoint, 2026-09-17 17:30 UTC", and
line 141 says in as many words "This is the current final snapshot". That
snapshot is the 1,541-module / 573-pin one. It was superseded five hours later
by the 1,552-module / 691-pin replay that finished at 22:53:05 UTC, which is
the state this tree is in. The document carries no marker saying so, although
the corpus plainly knows how to add one: `w361-restart-handoff.md` opens with
a bold "Historical checkpoint." and sends the reader on.

This matters because it is the most-linked verification record here. Thirteen
other documents reference it, and four of them
(`w361-n-plane-compactness.md`, `w361-n-plane-filtered-bridge-audit.md`,
`w361-n-plane-strong-scaling-research.md`, `w361-n-general-scaling-audit.md`)
send the reader there in the exact words "current verification status" or
"current final clean-build and replay status". Following any of those four
lands on a record that says it is current and is not. Only
`w361-claude-code-handoff.md` frames it correctly, in its section 5: "The
prior 1,541-module / 573-pin checkpoint remains historical".

The corpus leans the same way in bulk: 13 documents cite 1,541 and 9 cite the
573-pin figure, against 5 and 5 for the current 1,552 and 691. Five of the
thirteen carry no forward pointer at all (`w361-final-verification.md`,
`w361-final-endpoint-scope-audit.md`, `w361-compositional-certificate-map.md`,
`w361-n-full-row-independent-audit.md`,
`w361-pair-mobile-certificate-appendix.md`). A reader who greps this corpus
for the module count is more likely to find the superseded number than the
current one.

The fix is one paragraph at the head of `w361-final-verification.md`, in the
shape `w361-restart-handoff.md` already uses, and a matching correction to the
four "current verification status" pointers. This lane is the housekeeping
lane and has not edited another wave's verification record; that is the
orchestrator's call.

**Flag 1 (medium) -- `w361-overnight-progress.md` is a log, not a record.**
978 lines, the longest document here, with a title that reads like a campaign
record. It was written forward in time during the 09:10-17:34 UTC pass, so
earlier sections assert states that later sections and the handoff overturn:
the body contains ten "corrected", nine "historical", four "superseded", one
"stale" and four "conditional". It also names about nineteen `.lean` modules
by their then-current scratch names. Do not cite it as evidence for a current
fact; cite `w361-claude-code-handoff.md` section 5 and the JSON report.

**Flag 2 (low-medium) -- `w361-n-plane-compactness.md` has a completion title
over a conditional body.** The title is the bare assertion "the exact-row N
limit is checked". The body says three separate times what is not proved:
"not by itself a construction of its stage inputs"; "The hard remaining input
is **uniform nonemptiness** of these exact-row upstairs sets"; and "It does
not prove ... `NPlaneScalingHypothesis` itself." A later-added preamble
rescues the title by naming the modules that since supplied the inputs, so
the title is true today, but it was not a description of this module's own
content when written. A retitle would fix it; the body needs no change.

**Flag 3 (low) -- `w361-n-plane-unrestricted-stage-gap.md` has the opposite
problem.** 568 lines under a title that names a gap, whose own first line says
the gap is closed and points at `nFullStabilizer_lift_iff`. A reader scanning
titles for open problems lands on the longest resolved-obstacle document in
the corpus. The fix is a title marker, not an edit to the analysis.

**Flag 4 (low) -- two documents carry two vintages in one body.**
`w361-acceptance-readiness.md` and `w361-completion-audit.md` were both edited
in place with timestamped successor paragraphs at the head ("18:55 UTC
successor update", "15:44 UTC additive status refresh"). Their heads are
current and their lower sections are not, and both say so. The hazard is
partial reading, not a false claim.

**Not a flag, recorded to save the next reader the check.** The handoff's
"five old appendix skeletons still contain 40 recorded TODO invocations" is
exact. A grep for `dyadicAppendixTODO` under `generated/appendix/` returns 45,
because each of the five files also carries the macro's definition on a
commented-out line. Eight real invocations per file, five files, 40.

**Flag 5 (medium) -- `w363-m-full-stabilizer-independent-audit.md` pins nine
source hashes and twenty-one line numbers, names no base commit, and every one
of the hashes is now wrong.** The audit's "Verification performed" table gives a
SHA-256 for each of the nine wave-362 M modules; all nine differ from the files
at `d2056503`. Fifteen of its twenty-one `file:line` citations are also off, by a
fixed per-file offset (`MFullFrameCompactness` +6, `MBasisRowRefinement` +4,
`MPlaneAmbientStage` +4, `MFrameCupCoordinates` +6, `MFrameMatrixLift` +5 then +9
past line 1100, `MFullStabilizerLift` +33). Every named declaration still exists
with the quoted text intact, so this is drift, not a content error, and the
verdict `PROVED AS STATED` is unaffected. The cause is that four commits edited
all nine modules after the audit was written: `acffa057`, `492fe22e`, `20174284`
and `6359d12a`. **The audit's true base is `69b9851c`**, established by
recomputing `MFullStabilizerLift.lean`'s SHA-256 at candidate commits. The fix is
one line at the head of the document naming that commit; a renumber is optional
and worth less. W364-HOUSE did not rewrite another lane's verdict document.

**Flag 6 (high, and the one most likely to be acted on) -- a live Lean docstring
asserts the non-existence of declarations that now sit beside it.**
`GQ2/Dyadic/MarkedCore/NNielsenGenerators.lean:14-22` says the MC-N finite-list
artifact "cannot be produced yet", because "there is no `nNielsen_factorization`
and there are no `nFamN1` through `nFamN6` values anywhere in `GQ2/`". W364-NFACTOR
built all eight, in `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean`:
the families at `:138` to `:158`, `nNielsen_factorization` at `:357`, and the
artifact `nNielsenFac_finite_list` at `:758`. Nothing depends on the docstring,
so the mathematics is untouched; the hazard is that it reads as a research
finding rather than as prose. `docs/dyadic/w363-nielsen-note.md` carries the same
sentence and now opens with an overtaken-by banner; the module docstring does
not, because no lane of this session held an edit grant on it.
