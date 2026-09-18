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
