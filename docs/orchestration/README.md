# Agent-orchestration archive

This folder holds the **process artifacts** of the 2026-07 formalization swarm: the raw
ticket board, per-ticket plans, scoping notes, design documents, handoff files, session
logs, and status snapshots that coordinated the parallel agents.  The proof is complete,
so none of these are live coordination surfaces any more — they are kept for **proof
analysis** (they record *why* routes were chosen, which approaches were refuted, and the
exact per-ticket acceptance criteria and axiom budgets).

- **`tickets.md`** — the raw step-2 ticket board (132 rows, verbatim, with full per-row
  history in the status cells and per-ticket acceptance criteria).  The human-readable
  summary lives at [`../tickets.md`](../tickets.md).
- **`tickets-step1.md`** — the step-1 board (statement formalization, `T-xx` ticket IDs
  still cited in module docstrings).
- **`p*.md`** — per-ticket/lane plans, scopings, designs, and handoffs (`p13-…` through
  `p25-…`), named by ticket ID.
- **`SESSION-LOG.md`**, **`STATUS.md`** — the swarm's session log and status board.
- **`step2-plan.md`**, **`formalization-plan.md`** — the phase plans; **`review-packet.md`**
  — the external-review brief (v3); **`orbit-data-refactor.md`** — a mid-flight refactor plan.

**Note on stale paths:** code comments across `GQ2/*.lean` (and a few scripts) cite these
files at their original `docs/<name>.md` paths.  Those references date from when the files
lived one level up — read `docs/<name>.md` as `docs/orchestration/<name>.md`.  Comments in
frozen files (e.g. `GQ2/Foundations/Axioms.lean`) were deliberately not rewritten.

**Note on stale statuses:** the raw board's last few rows lag reality — the final sessions
(2026-07-08) closed every remaining lane, and the library is fully `sorry`-free.  The
authoritative final state is in [`../tickets.md`](../tickets.md) and the repo guards
(`scripts/check_axioms.sh`, `atlas-audit.md`).
