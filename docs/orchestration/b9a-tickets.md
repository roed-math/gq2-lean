# B9-A ticket board

Plan: `docs/orchestration/b9a-proof-plan.md`.  Branch `b9a`, worktree `~/claude/gq2-b9a`
(T0 runs read-only against the main checkout).  Model column = subagent model tier
(Fable for design/hard proofs, Opus for mechanical/medium proofs).  One ticket = one agent
dispatch; each ticket commits on green and updates its row here.

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| T0 | mathlib QuadraticForm API recon | opus | none (read-only report) | — | dispatched 2026-07-24 |
| T1 | axiom statement design + skeletons | fable | `GQ2/StiefelWhitney.lean`, `GQ2/TraceForm.lean` (new), design memo | T0 report | done 2026-07-24 (7 sorries: 3×T3, 3×T2, 1×T5 draft axiom; memo `b9a-t1-design.md`) |
| T2 | trace-form diagonalizations (N3) | opus | `GQ2/TraceForm.lean` | T1 | pending |
| T3 | Delzant invariance (N2) | fable | `GQ2/StiefelWhitney.lean` | T1 | pending |
| T4 | truncation/product glue (N4) | opus | `GQ2/StiefelWhitney.lean` (glue section) or fold into T5 | T1 | pending |
| T5 | the flip (N5) — axiom in, theorem out | fable | `GQ2/Foundations/Axioms.lean`, `GQ2/AxiomLedger.lean`, `scripts/check_axioms.sh` | T2–T4 + **owner sign-off on statement** | blocked (gate) |
| T6 | docs sweep after flip | opus | `docs/literature-axioms.md`, `formalization.yaml`, `docs/orchestration/review-packet.md`, `docs/angdinata-review-plan.md` | T5 | pending |
| W2n | `HasEqualNormValueGroups` negative stress test (`ℚ₂(√2)` fails it) | opus | new `example`/lemma near the def's stress tests | — (independent) | pending |
| W2c | ⌣ notation sweep at remaining consumer sites (`SectionSix.lemma_6_16`, `HilbertLedger`, `Shapiro/Deepness`) | opus | those files, display-only rewrites | — (independent) | pending |

## Ticket briefs

**T0 (opus, read-only, main checkout).**  Inventory, against the *pinned* mathlib
(`.lake/packages/mathlib`), everything usable for N1/N3: `QuadraticForm`/`QuadraticMap`
definitions and `Equivalent`, diagonalization theorems (`equivalent_weightedSumSquares` and
friends, char ≠ 2 hypotheses), bilinear-form ↔ quadratic-form passage, `Algebra.trace` /
`Algebra.traceForm` and their `IntermediateField` friction, `IsSquare`/`Units` API for
discriminants, and what `KummerKrullBridge` exposes for index-2 ↔ quadratic-subextension.
Deliverable: a markdown report (paths + exact decl names + signatures + gotchas), saved as
`docs/orchestration/b9a-t0-recon.md`.  No edits.

**T1 (fable, worktree).**  Read the proof plan + T0 report.  Deliverables, all compiling under
`lake env lean` (sorries allowed in proofs, none in statements): (a) `GQ2/StiefelWhitney.lean`
skeleton — binary-form model, `swOne`/`swTwo`, invariance lemma *statements* (N2) with `sorry`
bodies; (b) `GQ2/TraceForm.lean` skeleton — `L`, finrank-2, twisted trace form, diagonalization
*statements* (N3) with `sorry` bodies; (c) the draft `relativeStiefelWhitney_dyadic` statement in
a clearly-marked `section Draft` of `StiefelWhitney.lean` (NOT in the axiom file; as a
`theorem … := sorry` so it elaborates); (d) a design memo `docs/orchestration/b9a-t1-design.md`
recording the N1 design choice (mathlib `QuadraticForm` vs light structure) and why, plus the
exact statement for owner review.  Do not touch existing files.

**T2/T3/T4** — fill the sorried skeletons per plan nodes N3/N2/N4; disjoint files as listed;
commit per green file.

**T5** — gated; do not start without the owner's explicit statement sign-off recorded here.

**T6** — align every doc with the new census entry (label B9 ↦ new declaration name), including
the §C App-D rows for the B11a co-dependence noted in plan node N2.
