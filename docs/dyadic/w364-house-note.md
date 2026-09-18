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

## Scoreboard baseline

(to be filled)
