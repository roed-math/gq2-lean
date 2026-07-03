#!/usr/bin/env bash
# T-19 guard: axiom hygiene for the GQ2 library.
#
# Checks (textual, comment-aware; run from anywhere):
#   1. `axiom` declarations appear ONLY in GQ2/Foundations/Axioms.lean.
#   2. `sorry` appears only in the allowlisted files (the three intentional leaves).
#   3. The axiom census in Axioms.lean matches the expected count (bump EXPECTED_AXIOMS
#      when a new B-leaf lands, in the same commit).
#   4. No `native_decide` anywhere (it would add `Lean.ofReduceBool` beyond the standard
#      three axioms; the project convention is kernel-checked `decide` only).
#
# Comments and docstrings are stripped before matching (a nesting-aware scan of `/- … -/`
# and `--`), so prose mentioning "axiom"/"sorry" does not trip the guard.
#
# Deep verification (axioms of individual theorems) is done per-declaration with
# `#print axioms` / the lean-lsp `lean_verify` tool; the board's acceptance criterion is
# "standard three" for every theorem, plus the B-leaf axioms for their declared consumers.

set -euo pipefail
cd "$(dirname "$0")/.."

AXIOMS_FILE='GQ2/Foundations/Axioms.lean'
EXPECTED_AXIOMS=5   # B1, B2, B5, B7, B7'
SORRY_ALLOWLIST='GQ2/Reconstruction.lean GQ2/Statement.lean GQ2/GammaA.lean'

# Strip Lean comments: nested block comments `/- … -/` (incl. docstrings `/-- … -/`) and
# line comments `-- …`.  Emits one output line per input line (line numbers preserved).
strip_comments() {
  awk '
    BEGIN { depth = 0 }
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth == 0 && two == "--") break
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "-/") { if (depth > 0) depth--; i += 2; continue }
        if (depth == 0) out = out substr(line, i, 1)
        i++
      }
      print out
    }' "$1"
}

# grep_code PATTERN FILE → "FILE:LINE:match" hits in comment-stripped code.
grep_code() {
  local pattern="$1" file="$2"
  strip_comments "$file" | grep -nE "$pattern" | sed "s|^|${file}:|" || true
}

lean_files=$(find GQ2 -name '*.lean' | sort; echo GQ2.lean)

fail=0
stray_axioms=""
stray_sorries=""
native=""

allow_re=" $(echo "$SORRY_ALLOWLIST" | sed 's/ / | /g') "
for f in $lean_files; do
  hits=$(grep_code '^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]' "$f")
  if [ -n "$hits" ] && [ "$f" != "$AXIOMS_FILE" ]; then
    stray_axioms+="$hits"$'\n'
  fi
  case "$allow_re" in
    *" $f "*) ;;  # allowlisted
    *)
      hits=$(grep_code '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' "$f")
      [ -n "$hits" ] && stray_sorries+="$hits"$'\n'
      ;;
  esac
  hits=$(grep_code '(^|[^[:alnum:]_])native_decide([^[:alnum:]_]|$)' "$f")
  [ -n "$hits" ] && native+="$hits"$'\n'
done

# -- 1. axiom placement ------------------------------------------------------
if [ -n "${stray_axioms//$'\n'/}" ]; then
  echo "FAIL: axiom declarations outside ${AXIOMS_FILE}:"
  printf '%s' "$stray_axioms"
  fail=1
else
  echo "OK:   all axiom declarations live in ${AXIOMS_FILE}"
fi

# -- 2. sorry allowlist ------------------------------------------------------
if [ -n "${stray_sorries//$'\n'/}" ]; then
  echo "FAIL: sorry outside the allowlist (${SORRY_ALLOWLIST}):"
  printf '%s' "$stray_sorries"
  fail=1
else
  echo "OK:   sorries only in the allowlist (${SORRY_ALLOWLIST})"
fi

# -- 3. axiom census ---------------------------------------------------------
count=$(strip_comments "$AXIOMS_FILE" | grep -cE '^[[:space:]]*axiom[[:space:]]' || true)
if [ "$count" -ne "$EXPECTED_AXIOMS" ]; then
  echo "FAIL: ${AXIOMS_FILE} declares ${count} axioms, expected ${EXPECTED_AXIOMS}."
  echo "      If a new B-leaf landed intentionally, bump EXPECTED_AXIOMS in this script"
  echo "      (same commit) and record the leaf in docs/literature-axioms.md."
  fail=1
else
  echo "OK:   axiom census: ${count} (= expected)"
fi

# -- 4. no native_decide -----------------------------------------------------
if [ -n "${native//$'\n'/}" ]; then
  echo "FAIL: native_decide found (adds Lean.ofReduceBool to the axiom set):"
  printf '%s' "$native"
  fail=1
else
  echo "OK:   no native_decide"
fi

if [ "$fail" -ne 0 ]; then
  echo "check_axioms: FAILED"
  exit 1
fi
echo "check_axioms: all checks passed"
