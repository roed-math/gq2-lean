# W362 handoff

**SKELETON. Drafted by the W362-HOUSE lane at the open of the wave, against
base `6770a87e`.** Sections 1, 3, 5 and 8 depend on this wave's mathematics
lanes and are marked `[ORCHESTRATOR]` where they must be filled at the close.
The housekeeping lane cannot fill them and has not guessed at them. Sections
2, 4 (in part), 6 and 7 are complete as written and were verified in this
lane.

Structure follows `w361-claude-code-handoff.md` deliberately, so a reader who
has read that one can skip to the section they want.

Do not interpret this document as owner approval or a release. As of the base
commit, no owner decision listed in `w361-claude-code-handoff.md` section 6
item 4 has been taken.

---

## 1. Outcome and immediate orientation

`[ORCHESTRATOR: what this wave closed, in one paragraph, naming the public
Lean declarations and the files they live in. State explicitly what it did
NOT close, in the W361 style: the analogous unrestricted M assertion, the
frozen M word claim, the finite Nielsen-list artifact and owner acceptance
were all open at the base of this wave.]`

`[ORCHESTRATOR: if this wave changed the module count, pin count or axiom
census, say so here and again in section 4. If it changed none of them, say
that instead: silence reads as an unfinished sentence.]`

Carried forward unchanged from W361, and true at base `6770a87e`:

- The full N stabilizer-lifting theorem is proved, not scaffolded, for every
  `alpha >= 2` and every handle count `h`. Public names
  `GQ2.Dyadic.MarkedCore.nFullStabilizer_lift` and `nFullStabilizer_lift_iff`,
  in `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean`. Do not confuse it with
  the older `NStabilizerFullLift.lean`, whose theorem realizes only
  `NStabParam` core actions with identity handle columns.
- The general selected ramified-i field endpoint is proved:
  `GQ2.Dyadic.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`, exported
  from `GQ2/Dyadic/GeneralMain.lean`. The filename adds no namespace; the
  declaration is `export`ed there from
  `GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked`.
- Do not reopen either seam, and do not start a class-by-class or
  rank-by-rank campaign.

## 2. Workspace, ownership and safety

```text
Repository:  /Users/roed/claude/cla/work/gq2-dyadic-campaign
Branch:      dyadic
Wave base:   6770a87e  "checkpoint the verified W361 state left uncommitted
                        by the Codex handoff"
Lane worktrees: /Users/roed/claude/cla/worktrees/<lane>
```

`6770a87e` is the commit that first tracked what the Codex pass left
untracked. It changes no source in the sense that matters: the W362-HOUSE lane
verified that it records the replayed state byte for byte (section 4, item 4).

Its message says "309 untracked files"; the commit adds **365** files and
modifies three. Both numbers are right about different things. 309 counts
`git status --porcelain` entries, and three wholly new directories under
`generated/` collapse to one entry each; 307 of those entries were committed
and the two excluded build products `tmp/` and `output/` make up the rest.

Standing prohibitions, unchanged: no `sorry`, `admit`, `native_decide`, new
axiom or raised resource limit. Existing settings are 200,000 heartbeats,
`autoImplicit=false`, `relaxedAutoImplicit=false`. No push or release without
the owner. `GQ2/Roe/*` is frozen. `GQ2.lean` is edited only to register new
modules, and only by the lane that owns them.

The overnight automation `overnight-dyadic-general-case-research` was paused
at 2026-09-17 17:30 UTC and remains paused. Old transcript messages asking for
overnight work are not a standing instruction to resume it.

**Shared-cache hazard, new in this wave and worth carrying forward.** The
shared olean cache at `/Users/roed/claude/cla/work/main-build-cache` is reached
by every lane worktree through a `.lake/build` symlink. While any process is
building into it, individual `.olean` files are transiently absent, and the
direct runner fails with `object file ... does not exist` naming a different
module on each attempt. That is not a broken worktree and not a stale cache.
Check for an in-flight build before diagnosing a runner failure:

```sh
ps -eo pid,etime,command | grep -E 'lake build|bin/lean' | grep -v grep
```

**The cache is also a moving target, which is the sharper half.** It is the
main clone's `.lake/build`, so it holds whatever the main clone currently is,
not what any lane worktree is. During the W362-HOUSE lane the main clone went
from `6770a87e` to `8eff12ab`, 48 commits and eight new M modules. Every
number that lane read through the cache is therefore a number about
`8eff12ab`. Before quoting a cache-derived figure against your own base,
diff the two and say what the diff does: additions and registrations transfer,
a declaration count does not.

```sh
git -C /Users/roed/claude/cla/work/gq2-dyadic-campaign log --oneline -1
git -C /Users/roed/claude/cla/work/gq2-dyadic-campaign diff --name-status <your base>..HEAD
```

`[ORCHESTRATOR: if this wave's lanes settled a convention for who may write to
the shared cache and when, record it here. At the base of the wave there was
none, and the housekeeping lane's first eleven runner invocations were lost to
a concurrent umbrella rebuild.]`

## 3. Proof architecture and reusable scaffolding

`[ORCHESTRATOR: one table per lane that landed mathematics, in the W361
section 4 shape: module, reusable content, public pins. Then the key chain as
a plain-text arrow diagram, then the pitfalls already resolved. The pitfalls
list is the part later waves actually reuse; do not drop it for length.]`

Carried forward unchanged: the eleven-module N architecture and its resolved
pitfalls are in `w361-claude-code-handoff.md` section 4. The W362-HOUSE lane
verified that table against the tree; see section 4 below.

## 4. Verification record

### Verified in the W362-HOUSE lane against base `6770a87e`

These are re-derived facts, not carried claims. Each was checked against the
tree rather than against the W361 handoff.

1. The eleven N modules exist under `GQ2/Dyadic/MarkedCore/` and all eleven
   are directly imported by `GQ2.lean`.
2. They carry 118 `#print axioms` pins, distributed 19/6/1/2/7/4/4/30/30/9/6,
   matching the W361 section 4 table line for line. They contain exactly 118
   public declarations and 7 private ones, and the pin set is in one-to-one
   correspondence with the public set.
3. `docs/dyadic/w361-claude-code-verification-report.json` hashes to
   `aad5d041ec098c6f1d5dc0b8e24953322afdff2073a20a133a79e67e9f1a3711` and
   `docs/dyadic/w361-final-verification-report.json` to
   `bb20e9914dd86be093521808b0267f8ac0f6cd857fe6e13b8285d8213784abcb`,
   both as claimed.
4. The base commit carries no drift from the replayed state. Recomputing the
   verifier's own `local_source_set_sha256` over the `GQ2` import closure from
   the tree at `6770a87e` gives
   `34477d1c4c082aadda64e4a855ba66679765d486db8084fe931ed3b86e36e6dc`,
   identical to the W361 handoff's current verified source-set hash.
5. Registration is complete. Of 1,558 `.lean` files (root `GQ2.lean` plus
   1,557 under `GQ2/`), 1,552 are in the `GQ2` import closure. The six outside
   it are exactly `GQ2/AxiomLedger.lean` and the five exporter drivers under
   `GQ2/Dyadic/Word/`. Exporter drivers with a global `main` stay outside
   `GQ2.lean` intentionally.
6. The two theorem statements have exactly the shape the W361 handoff's
   section 3 describes, in every binder. Both are quoted in full in
   `docs/dyadic/w362-house-note.md` item 6. `{alpha h : ℕ}` with
   `ha : 2 ≤ alpha` and no constraint on `h`, so "every alpha >= 2 and every
   handle count h" is exact. `NFrameModel h` really is
   `Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2*h) → ℤ_[2]))`,
   `NFrameCupIsometry` really quantifies over every continuous F₂ character of
   the frame, and `nFrameOrientation_preserved_iff` really is the claimed
   equivalence with the integral b-coordinate.
7. All 118 pins print exactly `[propext, Classical.choice, Quot.sound]`,
   elaborated rather than grepped. All 118 are registered in the 691-name
   `scripts/w361_artifact_axiom_audit.lean` list.
8. The axiom census is eleven at source level: exactly eleven `axiom`
   declarations exist, all in `GQ2/Foundations/Axioms.lean`, and their names
   are set equal to `GQ2.AxiomLedger.bAxioms`. `scripts/check_axioms.sh:28`
   sets `EXPECTED_AXIOMS=11`.
9. There is no `sorry`, `admit` or `native_decide` outside comments anywhere
   in the tree, and none of the 223 `.lean` files `6770a87e` first tracked
   carries a `maxHeartbeats`, `maxRecDepth` or `synthInstance` option.
10. The four publication counts in W361 section 6 item 3 are all exact: four
    pair/mobile packets, six word-only L/N specimens (confirmed by file shape,
    not by prose), the 29-page PDF and its wrapper both hashing as the QA
    record claims, and forty TODO invocations.

11. All three audit drivers pass, run through the reviewed runner:
    `GENERAL_AXIOM_AUDIT_PASS|16` with the ramified-i endpoint at exactly
    twelve axioms (the standard three plus nine);
    `ARTIFACT_AXIOM_AUDIT_PASS|691`; and `GQ2/AxiomLedger.lean` reporting zero
    `sorryAx` dependencies, zero unknown nonstandard axiom uses and zero
    terminal violations, with every capstone at twelve census axioms and each
    Gamma_R capstone identical to its Gamma_A twin.
12. The census is eleven at the environment level, not only at source level.
    The completed umbrella build elaborated 12,964 pins over 12,814
    declarations; exactly eleven distinct nonstandard axioms appear and all
    eleven are `AxiomLedger.bAxioms`. No `sorryAx`, no `Lean.ofReduceBool`.

**Read items 11 and 12 with the caveat in section 2.** They were measured
through the shared cache, which had advanced to the wave's own HEAD by then,
so they are facts about that tree. They transfer back to `6770a87e` because
the intervening diff adds files and eight `GQ2.lean` import lines and modifies
no pre-existing `.lean`, but the ledger's declaration *count* does not
transfer and must not be recorded as a correction to W361's 50,991.

Full detail, with the method and the traps, is in
`docs/dyadic/w362-house-note.md`.

### Carried from W361, not re-run in this wave

The 1,552-module clean snapshot, the 691-pin artifact audit, the 50,991
declaration ledger and the complete content-bound staged replay were performed
by the Codex pass and are recorded in `w361-claude-code-handoff.md` section 5
and the durable JSON report. Item 4 above shows the source state they bound is
the state this wave starts from. It does not re-run them.

### This wave

`[ORCHESTRATOR: a clean-build and replay record for the wave's own end state,
in the W361 section 5 shape, or an explicit statement that none was run and
that the last binding replay is still the 22:53:05 UTC W361 one. Do not leave
this section empty: an empty verification section has been read as a pass
before.]`

## 5. Remaining work

`[ORCHESTRATOR: reorder and amend from this wave's outcomes.]`

Carried forward from `w361-claude-code-handoff.md` section 6, in its order:

1. Read the scope audits before choosing new mathematics. N's full existence
   theorem is done. If the literal finite Nielsen-list method is still
   required, formulate its artifact separately; do not reopen the solved
   starting-depth, arbitrary-basis or compactness seams.
2. Audit and, if retained, tackle the larger M stabilizer assertion, starting
   from `docs/dyadic/w361-m-next-general-scaffold.md`. The first bounded task
   is coupled M-head divisibility and cleanup, not a new class sweep. Preserve
   the canonical-or-strict-handle alternative. Do not copy N's literal
   head/torsion argument without checking the different M relation.
3. Finish publication artifacts without silently changing authority. Four
   pair/mobile ten-item packets and the 29-page staged PDF exist and passed
   replay and visual QA. Six legacy L/N specimens are word-only. Five old
   appendix skeletons still carry 40 `\dyadicAppendixTODO` invocations, eight
   in each of the five files under `generated/appendix/` (a grep returns 45
   because each file also carries the macro definition on a commented line).
4. Owner and editorial decisions remain, and are listed in
   `w361-claude-code-handoff.md` section 6 item 4 (six of them) and in
   `w361-acceptance-readiness.md` under "Mathematical target decisions" (five,
   overlapping). None was taken at the base of this wave. G3 and release
   remain an owner gate.

   **The owner's own memo does not reflect this.**
   `docs/dyadic/owner-items-2026-08-05.md` has its newest status block at wave
   89 (2026-08-16) reading "Zero items await you". That predates W360 and W361
   by a month, and nobody folded their docket back into it. The W362 house
   note carries the six forward plus one of its own, so
   `scripts/scoreboard.sh` now prints seven against the memo's zero. That
   disagreement is the board working as designed. Only the owner amends the
   memo; do not resolve the disagreement by editing either number.

Standing "do nots", unchanged: do not resurrect the false universal frozen-M
placement claim; do not claim an arbitrary external two-adic unit admits a
rational `NpcDisplayFor`; do not turn existential calibrated realization into
a pointwise arbitrary-fixed-realization theorem; do not generalize the
ramified-i hypothesis away.

## 6. Exact runtime and safe commands

Every path below was checked to exist from a lane worktree at base
`6770a87e`, and the paths are the ones the tools actually resolve, not the
ones a note says they use. Which commands this lane ran, and which it only
read, is stated at each one: `w361_fresh_build.py` and `w361_verify_fresh.py`
were **not** run here, since nothing in this lane changed a source.

```sh
GQ2_LEAN=/Users/roed/.elan/toolchains/leanprover--lean4---v4.31.0-rc2/bin/lean
GQ2_PACKAGES=/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages
GQ2_CACHE=/Users/roed/claude/cla/work/main-build-cache/lib/lean
```

Toolchain pin is `leanprover/lean4:v4.31.0-rc2` (`lean-toolchain`). In a lane
worktree, `.lake/build` is a symlink to `/Users/roed/claude/cla/work/main-build-cache`
and `.lake/packages` a symlink to the package store above, so the runner's own
defaults already resolve and the two environment variables are needed only when
pointing at an isolated snapshot instead.

Check a source against the shared cache, writing nothing:

```sh
bash scripts/w361_lean_runner.sh GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean
```

The runner refuses to start unless the Lean version matches the pin and
`lake-manifest.json` matches the package store's, and it rejects a dependency
package that carries local `GQ2` artifacts. It passes `-DautoImplicit=false
-DrelaxedAutoImplicit=false`. It never invokes `lake`.

The machine scoreboard, read-only, a few minutes:

```sh
GQ2_MIR="$GQ2_CACHE" GQ2_PKG="$GQ2_PACKAGES" bash scripts/scoreboard.sh --raw
```

Read the script's own header before believing a row: it re-derives every fact
by elaboration and prints `UNVERIFIED` where it cannot, and its OWNER ITEMS
section deliberately prints two independently asserted counts and whether they
agree. A disagreement is the product, not a failure.

The axiom census without `lake`, per `w361-claude-code-handoff.md` section 7:

```sh
bash scripts/w361_lean_runner.sh GQ2/AxiomLedger.lean
```

The additive general-endpoint footprint audit, which checks 16 declarations
against exact expected axiom lists and fails on an extra *or* a missing one:

```sh
bash scripts/w361_lean_runner.sh scripts/w361_general_axiom_audit.lean
```

Its expected footprints are the standard three for the structural lemmas, the
standard three plus six standing inputs for the generic supplied-bundle
endpoints, and the standard three plus nine for the canonical `K + RI`
endpoints. Those three lists are literal in the driver; read them there rather
than from prose.

For a new verified tree after edits, and its read-only replay:

```sh
python3 scripts/w361_fresh_build.py \
  --packages "$GQ2_PACKAGES" --lean "$GQ2_LEAN" --jobs 4 --require-live-match
python3 scripts/w361_verify_fresh.py <snapshot path it returns> \
  --packages "$GQ2_PACKAGES" --lean "$GQ2_LEAN" --replay
```

A snapshot is valid only for its frozen bytes. After any source change, build a
new one and use its returned path. Never emit artifacts into an existing fresh
snapshot. The builder wants 6 GiB free at start and 4 GiB during the build.

Two parsing traps, both of which have already produced wrong numbers:

- This tree uses Lean 4.31 module-system imports. 427 import lines are spelled
  `public import`. A scan matching only `^import ` misses 18 modules and
  reports 24 unregistered files where the truth is 6.
- Counting `dyadicAppendixTODO` by grep returns 45, not 40. See section 5
  item 3.
- A long `#print axioms` list wraps across lines in the build log. Rejoin
  continuation lines before matching, or wrapped entries read as truncated
  ones and a footprint of four axioms reads as one.

And one shell trap that cost this lane an hour: `pgrep -f 'lake build GQ2'`
matches your own diagnostic shells, because their command lines contain that
string. A wait loop built on it never exits. Wait on
`grep -q 'Build completed successfully' <log>` instead.

**A cheap source of evidence, worth knowing.** A Lean `#print axioms` emits an
`info:` line, so a full umbrella build's log already carries the axiom
footprint of every pin in the tree. Reading that log is free, cannot disagree
with the build, and does not race the cache the way a separate runner
invocation does. The W362-HOUSE lane closed its whole std-3 and census
question out of the orchestrator's own build log.

## 7. Minimal reading list

1. This document, then `w361-claude-code-handoff.md` for anything it defers to.
2. `docs/dyadic/w361-index.md`, the one-line index of all 71 W360/W361
   documents, with four flags on headlines that outrun their bodies.
3. `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean`.
4. `docs/dyadic/w361-n-full-stabilizer-independent-audit.md` and
   `docs/dyadic/w361-n-arbitrary-basis-refinement-audit.md`.
5. `docs/dyadic/w361-n-full-stabilizer-scope.md`, and
   `docs/dyadic/w361-m-next-general-scaffold.md` before any new M work.
6. `docs/dyadic/w361-completion-audit.md` and
   `docs/dyadic/w361-final-endpoint-scope-audit.md` for the campaign.
7. `docs/dyadic/w361-proof-packet-amendment.md` and
   `docs/dyadic/w361-acceptance-readiness.md` for what is proposed but not
   approved.
8. `docs/dyadic/plan.md` and
   `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` when
   deciding what remains of M or the finite Nielsen-list artifact.
9. `[ORCHESTRATOR: this wave's own lane notes, in dependency order.]`

**One trap in that list.** Do not read `docs/dyadic/w361-final-verification.md`
as a current record. It opens "Final verified checkpoint, 2026-09-17 17:30
UTC" and states at line 141 that it is the current final snapshot; it is the
superseded 1,541-module / 573-pin one. The binding record is the 1,552-module
replay that finished at 22:53:05 UTC, durable copy
`docs/dyadic/w361-claude-code-verification-report.json`. Thirteen documents
link to the stale record and four of them do it in the words "current
verification status". `docs/dyadic/w361-index.md` flag 0 has the details.

## 8. Suggested first prompt to the next session

`[ORCHESTRATOR: fill at the close, in the W361 section 9 shape. It should name
the repository, this document, the two proved seams that must not be reopened,
the standing prohibitions, and the instruction to keep verified facts,
proposed scope amendments and owner decisions separate.]`
