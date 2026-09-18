# W362-MKERNEL lane note: M derivative-kernel interpolation (arbitrary basis)

Lane of the gq2-lean general-K campaign, M full-stabilizer lifting step 2 of 5.
Branch `claude/w362-mkernel`, base `6770a87e`, Lean 4.31.0-rc2, shared cache.

## Ticket

- T1: the M preservation adapter identifying the N kernel tuples' derivative
  with the shared word via `evenRawStageShift_m`, so the closed
  derivative-kernel subgroup and the arbitrary-basis row witnesses apply at
  the M word.
- T2: the M twin of the closed derivative-kernel interpolation of
  `NBasisRowRefinement` for an arbitrary basis (kill every ordinary row at
  depth `d` from a depth-`(d-1)` correction), with an M ambient-stage
  statement using the actual free-basis target-relative defect.
- T3: the named interface consumed by the stage lane (MSTAGES).

## Status

Opened 2026-09-17. No Lean written yet. Verification of record is
`bash scripts/w361_lean_runner.sh <File.lean>`; no `lake` is ever run here.

## Log

- Commit 1: lane note opened.
