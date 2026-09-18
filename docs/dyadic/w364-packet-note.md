# W364-PACKET lane note

Lane: W364-PACKET (docs only, proposals only).
Branch: `claude/w364-packet`, base `d2056503`.
Scope: the proposed proof-packet amendment for the M full-stabilizer lifting and the two
finite Nielsen lists (MC-M, MC-N), plus the matching acceptance-readiness rows.

Deliverables:

- `docs/dyadic/w364-proof-packet-amendment-mc.md` (T1)
- `docs/dyadic/w364-acceptance-readiness-mc.md` (T2)

Authority: the Codex rule binds. Everything this lane writes is a PROPOSAL for the owner.
No Lean, no `generated/`, no packet TeX, no ledger, no W361 amendment/readiness bodies
(a one-line dated pointer at their tops is the only permitted annotation).

## Status

- [x] Lane note skeleton banked.
- [x] Inputs read (packet obligations, ledger, completion audit section 3, the six
      theorems read verbatim from the Lean, the two W363 audits, the W363/W364 notes,
      the owner memo wave-362 block).
- [x] T1 amendment drafted (`w364-proof-packet-amendment-mc.md`, 542 lines).
- [x] T2 readiness drafted (`w364-acceptance-readiness-mc.md`).
- [x] Contradictions in the inputs recorded (amendment section 6, five of them).
- [x] One dated pointer line added at the top of each W361 MC record.

## Inputs, as actually found

- Packet obligations: the per-core assertion is
  `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex:732-735`, inside
  `prop:marked-reduction`; the MC-M / MC-N rows are `:1077-1082`.
- Theorems read verbatim: `mFullStabilizer_lift`, `mFullStabilizer_lift_iff`
  (`GQ2/Dyadic/MarkedCore/MFullStabilizerLift.lean:144,238`),
  `nFullStabilizer_lift_iff` (`NFullStabilizerLift.lean:80`),
  `mNielsenGen_finite_list`, `mNielsenGen_stabilizer_induced`
  (`MNielsenGenerators.lean:685,853`), `nNielsen_factorization`,
  `nNielsenFac_finite_list`, `nNielsenFac_stabilizer_induced`
  (`NNielsenFactorization.lean:357,758,911`).

## Discrepancies found in the inputs (for the report, not for me to fix)

1. Section number. The assertion at `:732-735` sits in the eighth numbered
   `\section` (`sec:marked`), so in the compiled packet it is Section 8,
   Definition 8.1 / Proposition 8.2. The lane brief and `refs/README.md` line 19
   both call it section 7 / Def. 7.1 / Prop. 7.2. The line ranges are
   authoritative; the section number in those two places is off by one.
2. The ledger has no MC-M / MC-N rows. Those rows exist only in the packet TeX
   section 14. The ledger's corresponding content is section 5.1
   (`MarkedCoreCertificate`), section 9 item 6, section 10 and section 11.
3. Which M families have group-level lifts: three sources disagree. See the
   amendment's verified-facts section.

## Verification this lane performed

`bash scripts/w361_lean_runner.sh` on four modules at
`leanprover/lean4:v4.31.0-rc2` against the shared dependency cache. `lake` was
never invoked, `scripts/check_dyadic.sh` was never run, nothing was written.

| Module | pins | result | exit |
| --- | --- | --- | --- |
| `MarkedCore/MFullStabilizerLift.lean` | 10 | all std-3 | 0 |
| `MarkedCore/NFullStabilizerLift.lean` | 6 | all std-3 | 0 |
| `MarkedCore/MNielsenGenerators.lean` | 70 | all std-3 | 0 |
| `MarkedCore/NNielsenFactorization.lean` | 94 | all std-3 | 0 |

180 pins, no exceptions, no errors, no warnings. Incremental against a shared
cache: not a source-only transitive build, not a whole-tree gate.

## Log

- Commit 1: skeleton, before reading any input.
- Commit 2: inputs read and recorded, with three input discrepancies logged.
- Commit 3: T1, the amendment, with the lane's own pin measurement.
- Commit 4: T2, the readiness rows and the owner-decision list.
- Commit 5: the two W361 pointer lines.
- Commits 6 and 7: precision repairs to T1 (construction files, the Definition
  8.1 clause, the cup/orientation quantifiers).
