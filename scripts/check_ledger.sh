#!/usr/bin/env bash
# The axiom-ledger gate - `GQ2/AxiomLedger.lean`, run as a merge gate.
#
#     bash scripts/check_ledger.sh
#
# ---------------------------------------------------------------------------
# WHY THIS SCRIPT EXISTS
# ---------------------------------------------------------------------------
# `docs/dyadic/ax1-proposal.md` §"Merge gate" prescribes `lake env lean
# GQ2/AxiomLedger.lean` as a gate, but until wave 73 nothing ran it: it was not in
# `scripts/check_dyadic.sh`, so it was a gate on paper only, honoured by whoever
# remembered to type the command.  This script is that command, with its output
# turned into pass/fail.
#
# `GQ2/AxiomLedger.lean` is deliberately NOT imported by `GQ2.lean` (it does
# `import GQ2`, so registering it would make a cycle), which is why it cannot be
# a plain build target and needs a runner of its own.
#
# ---------------------------------------------------------------------------
# WHY IT IS NOT IN THE DEFAULT `check_dyadic.sh` PATH
# ---------------------------------------------------------------------------
# It invokes `lake`.  Campaign LANES must never run `lake` - the orchestrator owns
# all builds, and a lane's verification of record is `scripts/mirror.sh` (see the
# header of that script for why a naive `lake env lean` check comes out
# FALSE-CLEAN against a stale cached olean).  A lane runs `check_dyadic.sh`
# routinely; if this gate were in its default path, every lane would be running
# `lake`.  So `check_dyadic.sh` calls this script only when explicitly asked:
#
#     GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh     # or:  --ledger
#
# and otherwise prints a SKIP line naming this script.  The default path of
# `check_dyadic.sh` runs exactly the checks it ran before this script landed; the
# only difference is that one extra SKIP line is printed, so that the gate is
# discoverable from a default run without being triggered by one.
#
# ---------------------------------------------------------------------------
# WHAT IT CHECKS
# ---------------------------------------------------------------------------
#   L1  the ledger command itself succeeds.  `AxiomLedger.lean`'s terminal
#       certificate `throwError`s on a violation, so a nonzero exit here already
#       means a capstone rests on `sorryAx`, on a non-census axiom, or has
#       stopped printing identically to its Γ_A twin.
#   L2  gap map empty - no declaration depends on `sorryAx`.  The ledger only
#       REPORTS this; its own docstring says it is "expected to stay" empty, and
#       `scripts/check_axioms.sh`'s `SORRY_ALLOWLIST` is the mechanism that lets
#       it be non-empty mid-wave.  A wave closes with the allowlist empty, so a
#       nonzero gap map at merge time is a failure.
#   L3  ALARM empty - no unknown non-standard axiom.  The ledger's docstring:
#       "Must be empty: a stray `axiom`, a `native_decide` (`Lean.ofReduceBool`),
#       or a miscounted census would surface here."
#   L4  terminal violations = 0, read back from the printed count.  Redundant
#       with L1 by construction and kept as a belt-and-braces read of the report,
#       so that a future refactor turning the `throwError` into a warning cannot
#       silently disarm the gate.
#
# The scanned/std-3 counts are reported for the record, never asserted: they move
# with every landing, and a gate that pins them would fail on every wave.
#
# ---------------------------------------------------------------------------
# OVERRIDES
# ---------------------------------------------------------------------------
#   GQ2_LEDGER_FIXTURE   path to a saved ledger transcript.  When set, the script
#                        parses that file INSTEAD of running `lake`, and L1 is
#                        reported as not-run.  This is how the parsing half is
#                        testable without a toolchain (and how a saved ledger from
#                        a CI run can be re-audited).  It is not a way to pass the
#                        gate: L1 is explicitly marked skipped in the output.
set -euo pipefail
cd "$(dirname "$0")/.."

LEDGER_FILE='GQ2/AxiomLedger.lean'
fail=0

if [ ! -f "$LEDGER_FILE" ]; then
  echo "FAIL: ${LEDGER_FILE} not found (run from anywhere inside the repo)"
  exit 1
fi

# -- L1. run the ledger ------------------------------------------------------
if [ -n "${GQ2_LEDGER_FIXTURE:-}" ]; then
  if [ ! -f "$GQ2_LEDGER_FIXTURE" ]; then
    echo "FAIL: GQ2_LEDGER_FIXTURE=${GQ2_LEDGER_FIXTURE} does not exist"
    exit 1
  fi
  ledger_out=$(cat "$GQ2_LEDGER_FIXTURE")
  echo "SKIP: L1 ledger run - parsing the fixture ${GQ2_LEDGER_FIXTURE} instead"
else
  if ! command -v lake >/dev/null 2>&1; then
    echo "FAIL: \`lake\` not found on PATH; this gate needs the toolchain"
    exit 1
  fi
  if ledger_out=$(lake env lean "$LEDGER_FILE" 2>&1); then
    echo "OK:   L1 lake env lean ${LEDGER_FILE} - exit 0"
  else
    echo "FAIL: L1 lake env lean ${LEDGER_FILE} - nonzero exit"
    echo "      Either the library is not built (\`lake build GQ2\` first) or the"
    echo "      terminal certificate fired.  Its report follows."
    fail=1
  fi
fi
printf '%s\n' "$ledger_out" | sed 's/^/      /'

# -- the three report counts -------------------------------------------------
# Each report line is emitted by `AxiomLedger.lean`'s two `run_cmd` blocks in a
# fixed shape; the greps below quote those shapes exactly.  A missing line is a
# FAILURE, not a pass: it means the ledger did not get far enough to print, or
# its output format changed and this gate stopped auditing what it claims to.
count_from() {  # $1 = a sed -n 's/…/\1/p' extractor; empty output means "line absent"
  printf '%s\n' "$ledger_out" | sed -n "$1" | head -1
}

gap=$(count_from 's/^--- gap map: \([0-9][0-9]*\) declaration(s) depend on `sorryAx` ---$/\1/p')
alarm=$(count_from 's/^--- ALARM: \([0-9][0-9]*\) unknown non-standard axiom use(s) (must be 0) ---$/\1/p')
term=$(count_from 's/^\([0-9][0-9]*\) terminal violation(s) (must be 0)$/\1/p')
scanned=$(count_from 's/^scanned \([0-9][0-9]*\) tracked declarations under `GQ2` (theorems + defs)$/\1/p')

# -- L2. gap map -------------------------------------------------------------
if [ -z "$gap" ]; then
  echo "FAIL: L2 gap map - no \`--- gap map: N declaration(s) ... ---\` line in the output"
  fail=1
elif [ "$gap" -ne 0 ]; then
  echo "FAIL: L2 gap map - ${gap} declaration(s) depend on \`sorryAx\` (must be 0 at a merge)"
  echo "      A mid-wave \`sorry\` is allowed only in a file named in check_axioms.sh's"
  echo "      SORRY_ALLOWLIST, and that allowlist is empty at every wave close."
  fail=1
else
  echo "OK:   L2 gap map - 0 declarations depend on \`sorryAx\`"
fi

# -- L3. alarm ---------------------------------------------------------------
if [ -z "$alarm" ]; then
  echo "FAIL: L3 alarm - no \`--- ALARM: N unknown non-standard axiom use(s) ... ---\` line"
  fail=1
elif [ "$alarm" -ne 0 ]; then
  echo "FAIL: L3 alarm - ${alarm} use(s) of an axiom outside the census (must be 0)"
  echo "      A stray \`axiom\`, a \`native_decide\` (\`Lean.ofReduceBool\`), or a census"
  echo "      that moved without \`bAxioms\` moving with it."
  fail=1
else
  echo "OK:   L3 alarm - 0 unknown non-standard axiom uses"
fi

# -- L4. terminal certificate ------------------------------------------------
if [ -z "$term" ]; then
  echo "FAIL: L4 terminal certificate - no \`N terminal violation(s) (must be 0)\` line"
  fail=1
elif [ "$term" -ne 0 ]; then
  echo "FAIL: L4 terminal certificate - ${term} violation(s) (must be 0)"
  fail=1
else
  echo "OK:   L4 terminal certificate - 0 violations"
fi

# -- informational -----------------------------------------------------------
if [ -n "$scanned" ]; then
  echo "INFO: ${scanned} tracked declarations scanned (reported, never asserted)"
else
  echo "FAIL: no \`scanned N tracked declarations\` line - the ledger did not report"
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "check_ledger: FAILED"
  exit 1
fi
echo "check_ledger: all checks passed"
