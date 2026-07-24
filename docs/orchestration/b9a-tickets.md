# B9-A ticket board

Plan: `docs/orchestration/b9a-proof-plan.md`.  Branch `b9a`, worktree `~/claude/gq2-b9a`
(T0 runs read-only against the main checkout).  Model column = subagent model tier
(Fable for design/hard proofs, Opus for mechanical/medium proofs).  One ticket = one agent
dispatch; each ticket commits on green and updates its row here.

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| T0 | mathlib QuadraticForm API recon | opus | none (read-only report) | — | **done 2026-07-24** → `b9a-t0-recon.md` (committed on `master`) |
| T1 | axiom statement design + skeletons | fable | `GQ2/StiefelWhitney.lean`, `GQ2/TraceForm.lean` (new), design memo | T0 report | done 2026-07-24 (7 sorries: 3×T3, 3×T2, 1×T5 draft axiom; memo `b9a-t1-design.md`) |
| T2 | trace-form diagonalizations (N3) | opus | `GQ2/TraceForm.lean` (+`public import GQ2.KummerKrullBridge`); `KummerSurjectivity.lean` **untouched** — de-`private` not needed | T1 | done 2026-07-24 (3 sorries filled; finrank via public `exists_quadratic_of_open_index_two`, not the private recon lemmas) |
| T3 | Delzant invariance (N2) | fable | `GQ2/StiefelWhitney.lean` | T1 | done 2026-07-24 (3 sorries → 0, std-3 axioms; helpers `private` per Q3; + `CupSymmetry` import) |
| T4 | derive old B9 from the draft (N4/N5 prep) | opus | `GQ2/EvensKahnDerived.lean` (new) | T1 | **done 2026-07-24** — sorry-free; engine `evensKahn_dyadic_of_rsw` (pre-does T5 item 2) + `evensKahn_dyadic_derived` = byte-identical B9 + one trailing `hnorm`(=B11a, Q2 firewall); no unit-arith bridge needed; `#print axioms`={sorryAx,std-3} |
| T5 | the flip (N5) — axiom in, theorem out | fable | `GQ2/Foundations/Axioms.lean`, `GQ2/AxiomLedger.lean`, `scripts/check_axioms.sh`, `GQ2/EvensKahnDerived.lean` (parametrize), `GQ2/TraceForm.lean` (drop draft §) | T2–T4 | **done 2026-07-24** — census 9 with B9 = `relativeStiefelWhitney_dyadic` (17 consumers); ledger gap map 0, ALARM 0; build 3308 jobs green |
| T6 | docs sweep after flip | opus | `docs/literature-axioms.md`, `formalization.yaml`, `docs/orchestration/review-packet.md`, `docs/angdinata-review-plan.md` | T5 | **done 2026-07-24** — literature-axioms §B9 rewritten (relative SW identity; `evensKahn_dyadic` = byte-identical derived theorem, Delzant well-def proved, Q1 `hdeg`/Q2 `hnorm` noted), §C `{B9,B11a}` footprint note + §D B9 row/census-line updated; review-packet §2 amendment appended; angdinata W3→done + §5 postscript; yaml divergence (v) added. Census 9→9 |
| W2n | `HasEqualNormValueGroups` negative stress test (`ℚ₂(√2)` fails it) | opus | `GQ2/Foundations/Axioms.lean` (lemma after the deprecated alias) | — (independent) | **done 2026-07-24** — `not_hasEqualNormValueGroups_sqrt_two`: `⊥`+any `√2` fails; witness `z=δa` gives `‖δa‖²=‖2‖`, a base match forces `1=2·v₂(c)` in `ℤ` (`Padic.norm_eq_zpow_neg_valuation`+`valuation_p`/`valuation_pow`+`zpow_right_inj₀`); census still 9; `#print axioms`=std-3 |
| W2c | ⌣ notation sweep at remaining consumer sites (`SectionSix.lemma_6_16`, `HilbertLedger`, `Shapiro/Deepness`) | opus | those files, display-only rewrites | — (independent) | pending |

## T5 gate — owner sign-off recorded 2026-07-24

Owner approved the draft statement (`GQ2/TraceForm.lean` §Draft) and answered the memo's
questions: **Q1** keep `hdeg` (goal: statement as close as possible to the published theorem);
**Q2** the `hnorm` firewall design is approved; **Q3** keep the T3 helper re-proofs local for
now — upstreaming HilbertLedger tiers can happen after the proof is complete.

T5 execution checklist (single atomic commit on `b9a`, then merge to `master`):

1. Move `relativeStiefelWhitney_dyadic` into `GQ2/Foundations/Axioms.lean` as the B9 `axiom`
   (docstring: Kahn Th. 2 + Evens Th. 1 / Kozlowski Thm 1.1 citations, the `hdeg`-redundancy
   note, retained deviations, and the B11a/`hnorm` instantiation note); delete the draft
   section from `TraceForm.lean`; `Axioms.lean` gains `public import GQ2.TraceForm` (and
   transitively `StiefelWhitney`).
2. Parametrize `GQ2/EvensKahnDerived.lean`: its theorem takes the statement as a hypothesis
   `hrsw : ∀ …` (the file cannot import the axiom file); `Foundations/Axioms.lean` then defines
   `theorem evensKahn_dyadic … := evensKahn_dyadic_of_rsw relativeStiefelWhitney_dyadic …` with
   the statement **byte-identical** to today's axiom.
3. Same commit: `AxiomLedger.bAxioms` B9 ↦ `GQ2.relativeStiefelWhitney_dyadic`;
   `scripts/check_axioms.sh` `EXPECTED_AXIOMS` swap; `formalization.yaml` axiom list + the B9
   `literature_dependencies` line; check whether `Challenge.lean` / `comparator-config.json`
   pin the axiom-name list and update if so.
4. Gates before merge: `lake build` green; `lake env lean GQ2/AxiomLedger.lean` — certificate
   shows B9 = `relativeStiefelWhitney_dyadic`, ALARM empty, gap map empty;
   `scripts/check_axioms.sh` passes; zero sorries anywhere on the branch.
5. Merge `b9a` → `master` (board copies reconcile to this file), then T6 docs sweep.

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
commit per green file.  T2 addendum (from the T0 recon): the finrank-2 route needs
`exists_sqrt_generator` and `fixingSubgroup_subgroupOf_eq_stabilizer`, currently **`private`** in
`GQ2/KummerSurjectivity.lean` — T2's ownership is extended to that file for the sole change of
removing those two `private` keywords (no other edits there); mathlib's
`X_pow_sub_C_irreducible_of_prime_pow` excludes `p = 2`, so do not chase that route.
T4 rescope (2026-07-24 dispatch): T4 = new file `GQ2/EvensKahnDerived.lean` proving the verbatim
old `evensKahn_dyadic` statement from the draft `relativeStiefelWhitney_dyadic` + the T2/T3
lemma statements (no `sorry` of its own); N4 glue folds in only as needed.

**T5** — gate cleared (see the sign-off section above); execute the checklist.

**T6** — align every doc with the new census entry (label B9 ↦ new declaration name), including
the §C App-D rows for the B11a co-dependence noted in plan node N2.
