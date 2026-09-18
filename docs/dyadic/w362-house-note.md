# W362-HOUSE lane note

Lane: housekeeping and audit, first Claude wave after the Codex handoff.
Worktree: `/Users/roed/claude/cla/worktrees/w362-house`, branch `claude/w362-house`.
Base: `6770a87e` ("checkpoint the verified W361 state left uncommitted by the
Codex handoff").

## Runtime facts (verified at base 6770a87e)

- Toolchain pin: `leanprover/lean4:v4.31.0-rc2` (`lean-toolchain`).
- `.lake/build` is a symlink to `/Users/roed/claude/cla/work/main-build-cache`.
- `.lake/packages` is a symlink to
  `/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages`.
- Lean checks in this lane use `bash scripts/w361_lean_runner.sh <file>` only.
  No `lake` invocation of any form, and no `scripts/check_dyadic.sh`.

## Tickets

- T1 verify the handoff's headline claims against the tree.
- T2 index the 71 `docs/dyadic/w36*` documents.
- T3 hygiene: ignore `tmp/` and `output/`.
- T4 draft the restartable W362 handoff skeleton.

## Log

(Entries appended as the lane runs.)

- Lane opened. First commit banked before any investigation.

## T1 findings (as of base 6770a87e)

### Verified

1. **The eleven N modules exist and are all directly imported by `GQ2.lean`.**
   `FreeProTwoMatrixBasis`, `NBasisRowRefinement`, `NBasisRelativeRefinement`,
   `NBasisExactStages`, `NFullFrameCompactness`, `NFullFrameStageTransfer`,
   `NBasisFullFrameLift`, `NFrameMatrixLift`, `NInitialCupDepth`,
   `NFrameCupCoordinates`, `NFullStabilizerLift`, all under
   `GQ2/Dyadic/MarkedCore/`.

2. **118 pins, and the per-module table in handoff section 4 is exact.**
   `#print axioms` counts per module are 19/6/1/2/7/4/4/30/30/9/6, matching the
   handoff's column line for line; total 118. Independently, the eleven modules
   contain exactly 118 public declarations and 7 private ones, and the pin set
   is in one-to-one correspondence with the public set: no public declaration
   is unpinned and no pin names a non-declaration.

3. **The two durable verification reports hash exactly as claimed.**
   `docs/dyadic/w361-claude-code-verification-report.json` is
   `aad5d041ec098c6f1d5dc0b8e24953322afdff2073a20a133a79e67e9f1a3711` and
   `docs/dyadic/w361-final-verification-report.json` is
   `bb20e9914dd86be093521808b0267f8ac0f6cd857fe6e13b8285d8213784abcb`,
   both as stated in handoff section 5.

4. **The base commit records the verified source state byte for byte.**
   Recomputing the verifier's own `local_source_set_sha256` (the canonical
   JSON digest of the `{module: sha256}` map over the `GQ2` import closure,
   `scripts/w361_verify_fresh.py:67` and `scripts/w361_fresh_build.py:141`)
   from the tree at `6770a87e` gives
   `34477d1c4c082aadda64e4a855ba66679765d486db8084fe931ed3b86e36e6dc`,
   identical to the handoff's "current verified source-set SHA-256". The
   checkpoint therefore carries no drift from the state the Codex replay bound.

5. **Registration is complete (T1e).** Of the 1,558 `.lean` files (root
   `GQ2.lean` plus 1,557 under `GQ2/`), the import closure of `GQ2` contains
   1,552. The six outside it are exactly `GQ2/AxiomLedger.lean` and the five
   exporter drivers `GQ2/Dyadic/Word/General{Fox,PhaseCover,Phase,,LN}...Export.lean`.
   No other file is unregistered. The handoff's arithmetic
   (1,557 = 1,551 + 1 + 5; closure = 1,551 + root = 1,552) is exact.

   Method note for future lanes: this tree uses Lean 4.31 module-system
   imports. 427 import lines are spelled `public import`, and a scan that
   matches only `^import ` misses 18 modules and reports 24 unregistered files
   instead of 6.

6. **The statements have exactly the shape the handoff states (T1b).**
   `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean:46`:

   ```lean
   theorem nFullStabilizer_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
       (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h))
       (hchi : ∀ z, nFrameOrientation ha h (phi z) = nFrameOrientation ha h z)
       (hcup : NFrameCupIsometry ha phi) :
       ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
         (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
         (∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x)))
   ```

   and `:81`, the same two hypotheses as an iff with that existential:

   ```lean
   theorem nFullStabilizer_lift_iff {alpha h : ℕ} (ha : 2 ≤ alpha)
       (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
       (∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
         (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
         (∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x)))) ↔
       (∀ z, nFrameOrientation ha h (phi z) = nFrameOrientation ha h z) ∧
         NFrameCupIsometry ha phi
   ```

   Both quantify `{alpha h : ℕ}` with `ha : 2 ≤ alpha` and no constraint on
   `h`, so "every alpha >= 2 and every handle count h" is exact. The three
   supporting claims also hold:

   - `NFrameModel h` is `Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] ×
     (Fin (2 * h) → ℤ_[2]))` (`GQ2/Dyadic/MarkedCore/N.lean:177`), which is
     the claimed `Z/2 × Z₂³ × Z₂^(2h)`.
   - `NFrameCupIsometry` (`NFrameCupCoordinates.lean:31`) quantifies
     `∀ c d : ContinuousMonoidHom (NFrameModel h) (Multiplicative (ZMod 2))`,
     so it genuinely ranges over every continuous F₂ character including the
     torsion one. It carries no orientation and no identity-handle condition.
   - `nFrameOrientation_preserved_iff` exists (`NFrameMatrixLift.lean:106`)
     and is exactly the claimed equivalence with preservation of the integral
     b-coordinate.

7. **All 118 N pins are registered in the 691-pin artifact audit.**
   `scripts/w361_artifact_axiom_audit.lean` lists 691 names, all distinct, 388
   of them under `MarkedCore`. Resolving each of the eleven modules' 118 pins
   against that list under the module's own namespace leaves zero unmatched.

8. **Census eleven, at source level (T1d).** Exactly eleven `axiom`
   declarations exist in the tree, all in `GQ2/Foundations/Axioms.lean` (lines
   104, 124, 165, 178, 204, 231, 259, 300, 359, 388, 433). Their names are set
   equal to `GQ2.AxiomLedger.bAxioms`, and `scripts/check_axioms.sh:28` sets
   `EXPECTED_AXIOMS=11`. Two further `^axiom ` grep hits, in
   `GQ2/EvensKahnDerived.lean:32` and
   `GQ2/Dyadic/Instances/EvenRouteModel.lean:55`, are docstring prose that
   line-wrapped onto the word.

9. **The general endpoint is exported where the handoff says (T1c).**
   `GQ2/Dyadic/GeneralMain.lean:54` opens `namespace GQ2.Dyadic`, `:67`
   `export`s `Instances.FieldFamilySpliceOriginalMarked`, and `:79` pins
   `hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`. So the short name
   the handoff gives, `GQ2.Dyadic.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`,
   is real; the underlying declaration is
   `GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`,
   which is the spelling `scripts/w361_general_axiom_audit.lean` audits. The
   driver's expected footprints are literal: `standardAxioms` (3),
   `suppliedFieldAxioms` (3 + 6) and `canonicalFieldAxioms` (3 + 6 + 3 = the
   standard three plus nine), over 16 declarations, failing on an extra **or**
   a missing dependency. That matches the handoff's trust-boundary paragraph
   exactly. Elaborating it is queued behind the concurrent umbrella build.

10. **No placeholder and no resource option in the W360/W361 additions.**
    Stripping block comments and line comments, the tree contains zero
    `sorry`, zero `admit` and zero `native_decide` outside comments. (A raw
    grep returns 174 and 166 respectively; every hit is prose.) None of the
    223 `.lean` files that `6770a87e` first tracked contains a
    `set_option maxHeartbeats`, `maxRecDepth` or `synthInstance.*`, and the
    eleven N modules contain no `set_option` of any kind. The handoff's "no
    ... extra resource settings" is therefore exact for this pass.

    **Scope amendment, proposed.** The handoff sentence "Existing default
    settings are 200,000 heartbeats, `autoImplicit=false`, and
    `relaxedAutoImplicit=false`" is true of the *defaults*: `lakefile.toml`
    sets the two implicit options and no heartbeat option, so 200,000 is
    Lean's own default rather than a project setting. The tree is not
    uniformly at 200,000: it carries 224 localised `set_option maxHeartbeats`
    overrides, 34 `maxRecDepth` and 13 `synthInstance.maxHeartbeats`, the
    largest being 8,000,000 in `GQ2/Dyadic/SqCore/GradedFiveSepZero.lean`.
    All of them predate W360. The prohibition a new lane inherits is "do not
    raise a limit", not "the tree runs at 200,000"; the W362 handoff skeleton
    says it that way.

11. **The base commit's own file count reconciles, with a nuance.** The
    message says "309 untracked files and three modified ones". The commit
    adds **365** files and modifies exactly three (`GQ2.lean`,
    `docs/dyadic/literature-axioms-dyadic.md`, `scripts/scoreboard.sh`). The
    309 is a count of `git status --porcelain` *entries*, not files: three
    wholly new directories under `generated/` collapse to one entry each
    (`general-certificate-staged` 29 files, `general-ln-template-staged` 19,
    `general-template-staged` 13), giving 307 committed entries, and the two
    deliberately excluded build products `tmp/` and `output/` make 309. No
    file is missing; the two numbers count different things.

## T3: hygiene

Done: `/tmp/` and `/output/` added to `.gitignore`, root-anchored to match the
existing `/work/` and `/scratch/` style, so a nested `docs/.../tmp/` stays
visible. Checked against the whole index: no tracked path becomes ignored.

`work/` was already ignored (`.gitignore:5`).

**`.DS_Store`, reported and not acted on.** The pattern is already in
`.gitignore` at line 3, unanchored, so it matches at every depth. Nothing
named `.DS_Store` is tracked. Four exist on disk in the main clone
(`/Users/roed/claude/cla/work/gq2-dyadic-campaign`): at the repo root, under
`GQ2/`, under `work/`, and inside `.git/`. All four are ignored and none is at
risk of being committed. No action is required and none was taken.

## T1 findings, publication artifacts (handoff section 6 item 3)

12. **All four counts in the publication paragraph are exact.**

    - Four pair/mobile ten-item packets:
      `generated/general-certificate-staged/` holds exactly four packet stems
      (`pair-alpha2-h1-j0`, `pair-alpha3-h2-j1`, `mobile-alpha2-r1-p0-h0`,
      `mobile-alpha3-r2-p2-h1`), each with the same five files
      (`.appendix.tex`, `.files.json`, `.packet.json`, `.proofs.lean`,
      `.proofs.txt`); 20 files, plus eight cover/phase/fox artifacts and a
      README, is the directory's 29 entries.
    - Six legacy L/N specimens, word-only: `general-ln-template-staged/` holds
      exactly six stems (`L-h0`, `L-h4`, `N0-alpha5-h3`,
      `Npc-alpha2-r1-h0-num1-den1`, `Npc-alpha3-r2-h3-num3-den9`,
      `Npc-alpha3-r2-h3-num-3-den9`). "Word-only" is visible in the file
      shape: each has only `.tex`, `.ln.json` and `.provenance.json`, and none
      has the `.appendix.tex`, `.packet.json` or `.proofs.lean` that the four
      pair/mobile packets carry.
    - The staged PDF is 29 pages and hashes to
      `3cec56dc3adde9ad9982225cbc376904a9284224f23ba0c1a07c72f17a4b71bb`, and
      its wrapper `scripts/w361_staged_certificates.tex` to
      `702e75cbcb6d881ea53c62c0a29d448d04662ad938515fbc668487cadf8c48e5`,
      both exactly as `w361-staged-pdf-qa.md` records.
    - Forty `\dyadicAppendixTODO` invocations: eight in each of the five files
      under `generated/appendix/`. A grep returns 45 because each file also
      carries the macro's definition on a commented-out line.

    **Owner-facing note, not a decision.** The reviewed PDF lives at
    `output/pdf/w361-staged-certificates.pdf` in the main clone. That path was
    untracked at `6770a87e` by the checkpoint's own choice, and T3 has now
    made the choice permanent by ignoring `/output/`. The artifact whose hash
    the QA record pins therefore has exactly one copy, in an ignored
    directory. Its inputs are tracked and it is reproducible from them, so
    this is a hygiene consequence rather than a loss; whether the reviewed
    bytes should also be tracked is an owner call, not this lane's.

## T1a completed: the pins are std-3, machine-derived

13. **All 118 pins print exactly `[propext, Classical.choice, Quot.sound]`.**
    Not a subset and not a superset: 19/6/1/2/7/4/4/30/30/9/6, every one
    exact. This is elaborated output, not a grep.

    **Where the evidence came from, and why it is better than a re-run.**
    A concurrent umbrella build was already elaborating the whole tree into
    the shared cache (see the hazard note in section 2 of the W362 handoff
    skeleton). A Lean `#print axioms` emits an `info:` line, so that build's
    log carries the footprint of every pin in the tree as it is elaborated,
    including all 118 here. Reading it costs nothing and cannot disagree with
    the build, whereas a separate runner invocation would have raced the same
    cache. Parse note: a long axiom list wraps across lines, so continuation
    lines must be rejoined before matching, or wrapped entries read as
    truncated ones.

14. **Environment-level census check, from the same log (partial but
    strong).** Across the 9,051 pins elaborated so far, exactly ten distinct
    nonstandard axioms appear, and all ten are in `AxiomLedger.bAxioms`:
    `tateDualityAt` (636 consumers), `absGalQ2_localEulerCharacteristic`
    (503), `absGalQ2_isTopologicallyFinitelyGenerated` (499),
    `hilbertSymbol_normCriterion_finiteDyadic` (427),
    `peripheralCyclotomicAction` (78), `relativeStiefelWhitney_dyadic` (77),
    `dyadicOrientation` (49), `localReciprocity` (26), `markedRecipAt` (21),
    `tameQuotient` (2). No `sorryAx`. No `Lean.ofReduceBool`, so no
    `native_decide` is reachable. The eleventh census axiom
    `orientedTameQuotientAt` had not yet appeared because the build had not
    reached the canonical K+RI endpoints that consume it.

    That is the ledger's "alarm" and "gap map" reports, derived live from an
    independent run. It is not a substitute for the ledger itself, which
    covers the whole `GQ2` namespace including declarations with no pin; that
    run is queued.

## The four named documents, checked against the tree

15. **The packet citations are exact.** The handoff and
    `w361-n-full-stabilizer-scope.md` both cite
    `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` lines
    732-735 for the lifting proposition and 1077-1082 for the finite Nielsen
    list. Both land. Lines 732-736 are the proposition's emphasised statement,
    "Every automorphism of `D_P^ab` preserving the canonical orientation, the
    torsion relation vector, and the mod-2 cup form ... lifts". Lines 1077-1082
    are the MC-M and MC-N rows, whose criterion is "A finite list of
    orientation-preserving Nielsen generators lifts the Smith-Witt stabilizer
    on the abelianization". Those rows are stated for the **rank-four** cores,
    so the scope note's "the rank-four case is `h = 0`" is the right reading,
    and proving arbitrary `h` is strictly more than the row asks.

16. **Every declaration the M next-task map cites exists.** All 30 names in
    `w361-m-next-general-scaffold.md` resolve to a declaration in the tree,
    including the two whose identity the map's first concrete route depends
    on (`evenRawStageShift_m` and `evenRawStageShift_n`, both in
    `GQ2/Dyadic/Instances/StageAbstractionEvenRawSpan.lean`) and the three N
    kernel results it proposes to reuse
    (`nBasisKernelWitness_mem`, `nBasisKernelWitness_row`,
    `exists_nBasis_allRows_same_kernelCoset`, all in `NBasisRowRefinement`).
    `nFrameModel_map_t`, on which the scope note rests the claim that the N
    torsion clause is automatic, is a real theorem at
    `GQ2/Dyadic/MarkedCore/N.lean:1064`. The next-task map is grounded; it is
    not naming intentions.

17. **The "do not confuse" warning is accurate.** The handoff warns against
    reading `NStabilizerFullLift.lean` as the new result. The two are
    genuinely different theorems, not two spellings of one.
    `nStabParam_fullFrame_lift_general` takes `(P : NStabParam)` with
    `P.Admissible`, a seven-parameter core datum rather than an arbitrary
    frame automorphism, and its frame conclusion is generator-wise:
    `∀ i, nPhiHom ha h (abMk (Psi (dnGen alpha h i))) = fullFrameMark P h i`.
    `fullFrameMark` (`NStabilizerFullRows.lean:252`) builds its handle block
    as `mHandleMark k (ofAdd (1 : ℤ_[2])) i`, the unit coefficient, so the
    handle columns are literally the identity. `nFullStabilizer_lift` by
    contrast takes an arbitrary `phi` and concludes an all-element square. The
    warning is not stylistic.

## T1c and T1d closed by elaboration, with a staleness correction

18. **All three audit drivers PASS.** Run with
    `bash scripts/w361_lean_runner.sh <driver>`, exit 0 each:

    - `scripts/w361_general_axiom_audit.lean` -> `GENERAL_AXIOM_AUDIT_PASS|16`,
      32 s. Every one of the 16 declarations matched its expected footprint
      exactly, with no extra **and** no missing dependency. The endpoint the
      handoff names,
      `...FieldFamilySpliceOriginalMarked.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`,
      reports **12** axioms, that is the standard three plus nine, exactly as
      the handoff's trust-boundary paragraph says. The three structural lemmas
      report 3, the six supplied-bundle endpoints 9, and the seven canonical
      `K + RI` endpoints 12. T1c closed.
    - `scripts/w361_artifact_axiom_audit.lean` -> `ARTIFACT_AXIOM_AUDIT_PASS|691`,
      31 s. All 691 pins, standard three only.
    - `GQ2/AxiomLedger.lean` -> 25 s, and it reports: **gap map 0**
      declarations depending on `sorryAx`; **ALARM 0** unknown nonstandard
      axiom uses; **0 terminal violations**; every capstone at 12 axioms all in
      the census, with each Gamma_R capstone identical to its Gamma_A twin,
      including `main_presentation_literal_roe_unconditional`.

19. **Census eleven at the environment level.** The completed umbrella build
    elaborated 12,964 pins over 12,814 distinct declarations. Exactly eleven
    distinct nonstandard axioms appear and all eleven are
    `AxiomLedger.bAxioms`, `orientedTameQuotientAt` included this time with 13
    consumers. No `sorryAx` and no `Lean.ofReduceBool`, so nothing reachable
    uses a proof placeholder or a native decision. T1d closed.

20. **STALENESS CORRECTION, and the most useful operational fact this lane
    found.** These three runs do **not** measure base `6770a87e`. The shared
    cache is the main clone's `.lake/build`, and the main clone advanced
    during this lane: its HEAD is now `8eff12ab` ("register the kernel
    modules"), 48 commits past this lane's base, carrying the wave's M lanes.
    Anything measured through the shared cache measures whatever the main
    clone currently is, not the lane's own base. A lane that reports a
    cache-derived number against its base is wrong by however much the wave
    has moved.

    Here the correction is benign, and checkably so. `6770a87e..8eff12ab` is
    13 added files and exactly one modified one, `GQ2.lean`, which gains eight
    import lines and nothing else. No pre-existing `.lean` was touched. All
    eleven N modules are byte-identical across the two commits, as are
    `scripts/w361_artifact_axiom_audit.lean`,
    `scripts/w361_general_axiom_audit.lean` and `GQ2/AxiomLedger.lean`.
    Registering a module cannot change an existing declaration's axiom
    footprint, so items 18 and 19 hold at `6770a87e` for every declaration
    they cover.

    **One number does not transfer, and it is not a discrepancy.** The ledger
    reports **51,203** tracked declarations under `GQ2`. The W361 handoff says
    50,991, twice. The difference of 212 is what the wave's eight new M
    modules contribute; the handoff's figure was measured on the W361 tree and
    mine on `8eff12ab`. I cannot re-derive 50,991 now, because the cache that
    matched `6770a87e` has been overwritten. Do not record 51,203 as a
    correction to the handoff, and do not record 50,991 as the current count.

21. **Registration is still complete at the wave's current HEAD.** At
    `8eff12ab` there are 1,565 `.lean` files under `GQ2/`, eight more than at
    this lane's base, and all eight new `MarkedCore/M*.lean` modules appear in
    `GQ2.lean`. The six-file exception set is unchanged.

## Interaction with the machine scoreboard, flagged before it surprises anyone

Creating this file changes what `scripts/scoreboard.sh` reports. Its OWNER
ITEMS section picks the ARTIFACT side with

```sh
ls docs/dyadic/w*-house-note.md | sed 's/.*\/w\([0-9]*\)-house-note.md/\1 &/' |
  sort -n | tail -1
```

a **numeric** sort, so `w362-house-note.md` displaces `w88-house-note.md` the
moment this file exists. Had this note carried no owner-items heading, the
board would have started printing `NOT FOUND` where it used to print a count.
That is the contract's honest outcome, but it would have looked like a
regression and nobody would have known why. The section below therefore
exists, and this paragraph exists so the next reader does not have to
rediscover the mechanism.

The AUTHORITY side is `docs/dyadic/owner-items-2026-08-05.md`, whose newest
block is "Status at wave 89 (2026-08-16)" and reads **Zero items await you**.
That block predates this wave. The board will accordingly print a
disagreement between zero and the count below. Per the script's own header,
"A disagreement is the product, not a failure": the memo is right about the
docket as of wave 89, and the note is right about what has been surfaced
since. Do not respond by editing a number into the script.

## Owner items

The owner memo's newest block is wave 89 (2026-08-16) and reads "Zero items
await you". That block predates W360 and W361 by a month. The W361 corpus
records a docket that has never been folded back into it:
`w361-claude-code-handoff.md` section 6 item 4 names six unapproved adoptions,
and `w361-acceptance-readiness.md` section "Mathematical target decisions: do
not conceal these as formatting" names five, overlapping. Items 1 to 6 below
are the handoff's six, carried forward verbatim and not adopted, changed or
adjudicated by this lane. Item 7 is new and is this lane's own.

1. Adoption of the changed M pair/mobile words.
2. The corrected RN interface.
3. The existential realization and calibration quantifiers.
4. The symbolic display contract for the new words.
5. The treatment of the legacy L/N artifacts.
6. Acceptance of N's alternative proof method. The full unrestricted
   handle-mixing stabilizer assertion is proved by `nFullStabilizer_lift_iff`,
   but by uniform filtered correction and compactness, not by the finite
   Nielsen-generator list that packet lines 1077-1082 prescribe. Either accept
   the method or commission the literal presentation artifact.
7. **New this wave.** Whether the reviewed staged certificate PDF's bytes
   should be tracked. `w361-staged-pdf-qa.md` pins a 29-page artifact by
   SHA-256, and this lane confirmed the bytes at
   `output/pdf/w361-staged-certificates.pdf` in the main clone hash to exactly
   the pinned
   `3cec56dc3adde9ad9982225cbc376904a9284224f23ba0c1a07c72f17a4b71bb`. T3 has
   now ignored `/output/`, making that path permanently untracked, so the
   reviewed bytes exist in exactly one working copy. The artifact is
   reproducible from tracked inputs (`scripts/w361_staged_certificates.tex`,
   hash confirmed, plus the staged appendices under `generated/`), so nothing
   is lost today. The call is whether a QA record that pins bytes by hash
   should be able to point at those bytes in the repository. This lane has no
   authority to track a 308 KB build product into a research tree and has not.

Nothing else this lane found is an owner call. The rest is either verified
fact, recorded above, or a scope amendment proposed to the orchestrator: the
heartbeat-baseline wording in item 10, and the five document flags in
`docs/dyadic/w361-index.md`.

**The board will print a disagreement between the memo's zero and the seven
above. That is the contract working.** The memo is right about the docket as
of wave 89; the note is right about what W360, W361 and this wave have put on
it since. Per the script's own header, do not respond by editing a number
into the script. The memo is the owner's own file and only the owner amends
it.
