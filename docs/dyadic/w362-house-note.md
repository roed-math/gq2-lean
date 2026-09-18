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
