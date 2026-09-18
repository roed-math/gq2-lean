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
