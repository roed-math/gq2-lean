# W366-APPLY lane note

**Lane**: W366-APPLY of the gq2-lean general-K campaign.
**Branch**: `claude/w366-apply` (worktree `cla/worktrees/w366-apply`), base `9dd8a307`.
**Opened and closed**: 2026-09-18. Not pushed.

## Mandate

Apply the owner's Option A decision, recorded in
[`owner-items-2026-08-05.md`](owner-items-2026-08-05.md) item 4 and defined in
[`w364-proof-packet-amendment-mc.md`](w364-proof-packet-amendment-mc.md)
section 5, to the authoritative packet, the ledger and the completion audit.
The decision: the uniform filtered-correction and compactness proof method is
accepted as satisfying MC-N and MC-M, and the finite Nielsen-family lists
satisfy the packet's section-14 sentence in the families reading.

Authorized edit surface, and only this: the packet TeX per-core assertion and
the two section-14 rows; the ledger's corresponding status; the completion
audit's MC-M / MC-N rows and section-1 verdict sentence; the two W364 proposal
documents marked ADOPTED for the applied parts. Explicitly not authorized, and
not touched: the frozen words, the manifest, `generated/appendix/*.tex`, the
general-endpoint statement, any Lean, any other packet section.

No `lake` was run, and `scripts/check_dyadic.sh` was not run.

## Status

- [x] T1 packet section-8 per-core assertion
- [x] T2 packet section-14 MC-M / MC-N rows
- [x] T3 ledger status, completion audit rows, W364 documents marked ADOPTED

## Diff summary

Six files, 229 insertions, 18 deletions, all of the deletions being lines that
were replaced or extended in place. Nothing outside the authorized surface.

### `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` (+73 -18)

The packet had been untouched since the vendoring commit `da00a908` and
contained no LaTeX comments, so it has no in-file correction convention to
follow. The convention chosen, and used at both sites: replace in place, and
retain the original text verbatim in a `%` comment block directly above the
replacement, headed by the owner decision, its date, and the amendment section
the wording comes from. That preserves the original wording in the source
without changing the compiled document.

| Hunk | Old lines | New lines | What |
| --- | --- | --- | --- |
| 1 | 732-735 (4) | 732-757 (26) | Inside `prop:marked-reduction` (Proposition 8.2): the emphasized per-standard-core statement replaced by amendment section 3's wording, preceded by a 13-line comment carrying the original and the two Lean names. |
| 2 | (insertion) | 1099-1110 (12) | Comment block before the MC rows, carrying the two original rows verbatim. |
| 3 | 1078-1080 (3) | 1112-1129 (18) | The MC-M row's completion-criterion cell. Line 1077, `MC-M & Marked automorphism lifting for the rank-four \(M_\alpha\) core &`, is unchanged. |
| 4 | 1082 (1) | 1131-1139 (9) | The MC-N row's completion-criterion cell. Line 1081 is unchanged. |

**Exact wording applied at hunk 1** (the `\emph{...}` body, amendment section 3
verbatim, transliterated into the packet's own macros; no words changed):

> For each standard core \(P\in\{M,N\}\), every \(\alpha\ge2\) and every handle
> count \(h\): a continuous automorphism of the full topological abelianization
> \(D_P^{\mathrm{ab}}\), torsion coordinate included, is induced by a continuous
> automorphism of \(D_P\) preserving the canonical orientation \(\chi_P\)
> **if and only if** it preserves the transported canonical orientation and the
> full mod-\(2\) cup form. The induced-map equation holds at every element of
> \(D_P\), not only at the marked generators, and handles may mix arbitrarily.
> The torsion relation vector is not a hypothesis: it is fixed automatically by
> every frame automorphism, and the constructed lift fixes the corresponding
> head word literally.

**Exact wording applied at hunk 3** (MC-M completion criterion):

> Discharged, by two theorems with different scopes. (i) The lifting assertion
> of \cref{prop:marked-reduction} holds at every \(\alpha\ge2\) and every handle
> count, as an equivalence, torsion included
> (`MarkedCore.mFullStabilizer_lift_iff`). (ii) At rank four, every element of
> the Smith--Witt stabilizer is the composite of an explicit seven-member list
> drawn from the seven Nielsen families, each member of which preserves the
> orientation and the full mod-\(2\) cup form and therefore lifts, and the
> composite of those lifts induces the given stabilizer element on the nose
> (`MarkedCore.mNielsenGen_finite_list`,
> `MarkedCore.mNielsenGen_stabilizer_induced`). The individual generators are
> lifted by (i), not by seven separate closed-form group constructions.
> Accepted method and scope, per the amendment adopted with this row: the
> uniform filtered-correction and compactness proof of (i) is accepted as
> discharging the generators' lifts, and "a finite list" is read as finitely
> many parameterized families, one member of each slot per stabilizer element;
> no finite generating set exists, and no finite-word decomposition of the
> limiting automorphism is produced. The lists are rank four (\(h=0\)); the
> lifting halves of (i) are general in \(h\).

**Exact wording applied at hunk 4** (MC-N completion criterion):

> Same, with `MarkedCore.nFullStabilizer_lift_iff`, and at rank four an
> eight-slot list drawn from six Nielsen families, complete by
> `MarkedCore.nNielsen_factorization` (`MarkedCore.nNielsenFac_finite_list`,
> `MarkedCore.nNielsenFac_stabilizer_induced`). At \(N\) the list members carry
> a second, independent lift assembled from the families' own constructions
> (`nNielsenFacLifts_of_param_families`), whose \(N_4\) ingredient is itself a
> compactness limit. The same accepted method, families reading and rank-four
> scope apply.

Two deviations from the amendment's section 4 text, both recorded here:

1. **Added**, one sentence per row, the accepted-method and scope statement
   beginning "Accepted method and scope". Option A's own text requires it
   ("the acceptance text must say plainly that no finite-word decomposition of
   the limit automorphism is produced"), the readiness note makes the two scope
   statements non-droppable, and the owner's memo entry names the **families
   reading** explicitly. The MC-N row refers back to it rather than repeating it.
2. **Not carried over**: the amendment renders its proposed rows in italics.
   That is the proposal document's convention for quoting proposed text, not an
   instruction: the packet's other inventory rows are upright, and the original
   MC rows were upright. Rendered upright. (At hunk 1, by contrast, the original
   is `\emph{...}` and the replacement keeps the emphasis.)

Typographic, no wording change: each `\texttt{MarkedCore.…}` name carries
`\allowbreak` after the namespace so the 0.48\textwidth column has a legal break
point. Without it the two `…_stabilizer_induced` names overflowed by 18.7pt.

### `docs/dyadic/refs/dyadic-presentations-formalization-ledger.md` (+55 -0)

The W364-PACKET lane's finding is confirmed: `grep` finds neither `MC-M` nor
`MC-N` anywhere in the ledger. The rows exist only in the packet's section 14.
The ledger's corresponding content is annotated at four places, in the dated
bracketed style the campaign already uses on the other vendored authority
document. Pure insertion: nothing is rewritten, reordered or removed.

| After ledger line | Section | What the annotation says |
| --- | --- | --- |
| 19 | 1, Executive status, missing-work item 1 | The marked rank-four lifting is discharged for both cores; names the decision, the two `_lift_iff` theorems and the five list theorems; says items 2 to 4 of that list are untouched. |
| 164 | 5.1, `MarkedCoreCertificate` | "It is enough to prove that the required abelian marking correction lies in the image of `Aut(P.group)`" is now a theorem; the `correction` field is supplied, not assumed; `correction_nu` is the reduction's own transport step. |
| 291 | 9, implementation order item 6 | Done, and beyond that item's rank-four scope: classification by `mStabilizer_classification` / `nStabilizer_classification`, lifting by the two `_lift_iff` theorems, which are general in `h`; the lists live in two modules beyond the two named in the item. |
| 317 | 11, "What can be claimed now" | The marked-core half of "does not yet provide" no longer holds, with both scope statements. **The word-certificate half is explicitly not adjudicated** by this lane. |

Section 10 (merge gates) was **not** edited: it has no MC-specific gate, so
there is no MC status in it to update.

### `docs/dyadic/w361-completion-audit.md` (+16 -3)

Three annotations in the file's own `[W362: …]` style, dated `[W366 2026-09-18: …]`.

| Line | What |
| --- | --- |
| 44 | Section 1's verdict sentence "It does not exhibit the finite Nielsen-generator list prescribed as a proof method in the old packet" is annotated as superseded twice over: the lists now exist for both cores, and the method was accepted. Says the MC half of the acceptance gap is what closes, and the WC, publication and release items are untouched. |
| 200 | Section 3, MC-M row: discharged, with the seven-member list, the `IsMStabilizer` quantifier, the two scopes and std-3. |
| 201 | Section 3, MC-N row: the row's own "either that presentation artifact or acceptance of the alternative proof method remains" is annotated to say that **both** have now happened. |

### `docs/dyadic/w364-proof-packet-amendment-mc.md` (+29 -1)

Status header: sections 3 and 4 **ADOPTED** (2026-09-18, Option A) and applied;
section 1.3 and section 6 still **PROPOSED** and unapplied. A decision line at
section 5. The closing "No owner decision is recorded by this note" is annotated
rather than rewritten, and says that sub-decisions 1 and 2 are settled while 3
and 4 remain open.

### `docs/dyadic/w364-acceptance-readiness-mc.md` (+33 -5)

Status header: the target decision is taken and the rows it scores are adopted;
the four documentation repairs remain proposed. Three checklist boxes ticked
(the decision, the adoption of the rows with both scope statements, and Option
B as moot), with what was actually done written into each.

## Checks

Every check below is lake-free.

| Check | Before | After |
| --- | --- | --- |
| `python3 scripts/dyadic_word_tex.py check` | `one-tree hash check passed (merge gate 7)`, exit 0 | `one-tree hash check passed (merge gate 7)`, exit 0 |
| `pdflatex` on the packet, 3 passes | exit 0, 0 errors, 0 overfull, 0 LaTeX warnings, 14 pages | exit 0, 0 errors, 0 overfull, 0 LaTeX warnings, 15 pages |
| `\newlabel` numbers in `packet.aux` | baseline | **identical**, every label keeps its number once page numbers are normalised away |
| `\cref{prop:marked-reduction}` renders as | n/a | `Proposition 8.2`, which is the numbering amendment section 1.3 says is correct |

Notes on those checks.

- **The hash gate does not cover the packet.** `scripts/dyadic_word_tex.py`
  contains no reference to `docs/dyadic/refs/` or to the packet file; it gates
  the `generated/` interchange artifacts. It is recorded here because it was
  run before and after, as the brief asked, and because it proves nothing about
  this file either way.
- **No theorem number moved.** This was the risk of the edit: the packet's
  theorem environments share one counter, so adding any numbered environment
  would have renumbered Proposition 8.1 and everything after it. Nothing
  numbered was added; the `.aux` comparison is the evidence.
- The packet gains one page (the MC rows are much longer) and one cosmetic
  `Underfull \vbox` at the new page break on page 14. The original already had
  one such box on page 1.
- Packet SHA-256, for the record: before
  `35c621ef67a566a5a51acef8b8f93726126acb2799e2c7eac61d49bac672168b`, after
  `2b95c73ede820b908fd396d1bff551782b6890dee56b60fbf4b178478f1060ca`.

## Lean cited, and verified present in this tree

Every edit cites the Lean it rests on. All are in namespace
`GQ2.Dyadic.MarkedCore`. Statements were read from the source in this worktree,
not relayed; `mFullStabilizer_lift_iff` and `nFullStabilizer_lift_iff` were
compared character by character against the amendment's section 2.1 quotes and
match.

| Name | File and line |
| --- | --- |
| `mFullStabilizer_lift_iff` | `GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean:238` |
| `mFullStabilizer_lift` | `GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean:144` |
| `nFullStabilizer_lift_iff` | `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean:80` |
| `nFullStabilizer_lift` | `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean:46` |
| `mNielsenGen_finite_list` | `GQ2/Dyadic/MarkedCore/MNielsenGenerators.lean:694` |
| `mNielsenGen_stabilizer_induced` | `GQ2/Dyadic/MarkedCore/MNielsenGenerators.lean:856` |
| `nNielsen_factorization` | `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean:357` |
| `nNielsenFac_finite_list` | `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean:758` |
| `nNielsenFac_stabilizer_induced` | `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean:911` |
| `nNielsenFacLifts_of_param_families` | `GQ2/Dyadic/MarkedCore/NNielsenFactorization.lean:959` |
| `mStabilizer_classification` | `GQ2/Dyadic/MarkedCore/M.lean:887` |
| `nStabilizer_classification` | `GQ2/Dyadic/MarkedCore/N.lean:1008` |

Two line numbers in the W364 amendment have drifted by nine since it was
written: it cites `MNielsenGenerators.lean:685` and `:845`, the current lines
are `694` and `856`. The statements are the ones it quotes. No axiom pin was
re-measured by this lane; the amendment's section 2.3 measurement stands as its
own record.

## Declined, and why

Each of these would have been an improvement to the document's internal
consistency, and each is outside the edit surface Option A authorizes.

1. **The packet's section 14 preamble**, "After the corrections and reductions
   above, the proof is complete modulo the following explicit leaves", now
   introduces a table whose first two rows read "Discharged". The owner may
   want a follow-up wave to reconcile that sentence, and to decide whether
   discharged rows stay in the inventory or move to a separate table. Not
   touched: the authorization names the two rows, not the section.
2. **`docs/dyadic/refs/README.md` line 19**, which calls the marked reduction
   "packet Def. 7.1 + Prop. 7.2". The compiled packet makes it Definition 8.1
   and Proposition 8.2, confirmed by this lane's compile. This is the
   amendment's section 1.3 repair, offered separately there and not part of
   Option A.
3. **The completion audit's section 5 bullet** "reconcile only its prescribed
   finite Nielsen-list proof method with the new uniform proof", which Option A
   also resolves, and its section 8 checklist. The authorization names the
   section-3 rows and the section-1 verdict sentence.
4. **The ledger's section 11 word-certificate clause.** The same sentence this
   lane annotated also says the packet does not provide the reflected universal
   word certificates. The completion audit's section 3 suggests that half is
   stale too. Out of scope, and the annotation says so in terms rather than
   leaving the reader to assume the whole sentence was retired.
5. **The four documentation repairs** of the readiness note (packet citation,
   ledger pointer, the M family inventory docstring at M5 and B8, the stale
   W363 audit hashes). All comment-only, all still open, all flagged in the
   status headers this lane added.
6. **Everything Lean.** No `.lean` file was opened for writing, and no build,
   axiom census or `#print axioms` run was performed.
