# W364-HOUSE lane note

Lane: housekeeping over waves 362, 363 and 364, plus the mechanical sections of the
next-session handoff.

Base: `d2056503` (branch `claude/w364-house`, worktree
`/Users/roed/claude/cla/worktrees/w364-house`, Lean 4.31.0-rc2).
Round window: `6770a87e..d2056503`, 138 commits.

Status: OPEN. Skeleton banked; tickets in progress.

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
binding taxonomy"), two commits past this lane's base `d2056503`. Everything the
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

## Findings

(to be filled)

## Verified counts

(to be filled)

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

## Scoreboard baseline

(to be filled)
