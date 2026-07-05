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
EXPECTED_AXIOMS=13  # B1, B2, B3c, B4, B5, B6, B7, B7', B8, B9, B10, B11a, B11b (B10: census decision, P-06 escalation; B9 base-generalized + B11 added: census decision, P-15 escalation, 2026-07-03; B11 split into B11a hilbertSymbol_normCriterion_finiteDyadic + B11b unramifiedQuadratic_units_are_norms, census 12→13: P-23 / adversarial review rec 2, user-approved 2026-07-04 — old dyadicNormCriterion re-derived as a same-name theorem, the spectral-norm bridge isolated as a def not an axiom)
SORRY_ALLOWLIST='GQ2/Statement.lean GQ2/GammaA.lean GQ2/BoundaryFrame.lean GQ2/BoundaryMapsWitness.lean GQ2/FoxHeisenberg.lean GQ2/SectionSix.lean GQ2/SectionSeven.lean GQ2/SectionEight.lean'  # Transgression.lean removed 2026-07-04: P-15i CLOSED (κ⁰_q hypothesis restored per docs/p15i-transgression-gap.md; splitting_of_global_cocycle + lemma_6_21 proved std-3, file sorry-free). HilbertLedger.lean removed 2026-07-04: P-15e O-finish CLOSED (all 6 sub-lemmas proved; whole file sorry-free; evensNorm_deepUnit_vanish = std-3 + B9/B11). Reconstruction.lean removed: exists_contSurj_of_card_le proved (P-02). RepIndependence.lean removed 2026-07-04: P-15d CLOSED (lemma_6_14 proved std-3, no B-axioms, sorry-free — inner-conjugation coboundary on V⋊C; statement moved out of SectionSix.lean, comment-pointer there). SectionThree.lean removed 2026-07-03: P-07 CLOSED (markedHom_bijective proved from B5, std-3; last §3 sorry). SectionThreeMarked.lean removed 2026-07-05: P-25 CLOSED all three §3-marked sorries — prop_3_10_gammaA, prop_3_10_local_marked, prop_3_14 all spliced; file sorry-free. BoundaryFrame: P-11 thm_4_2 (removed by P-17); BoundaryMapsWitness: P-25 prop_3_14 construction — the full 21-field BoundaryMaps bundle is assembled (fiberProductExists/proPKernel_image_ge/ker_nuT_le_proPKernel/compatA all std-3; surjA fully proved), with ONE remaining sorry tame_reciprocity (ι∘ν_t∘tameF = ν_ur — the tame-quotient↔reciprocity orientation bridge; genuine arithmetic, needs a B10-strengthening or tame-reciprocity axiom — census decision, flagged to user); FoxHeisenberg: P-12 §5 statements (removed by P-13); SectionSix+SectionSeven: P-14 §§6–7 statements (removed by P-15a–i); SectionEight: P-16 §8 statements — 8.2×2, 8.3, 8.6×2, prop_8_9 (removed by P-16 O-half)

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

# git-tracked-file membership (P-24: guard hardening).  The guard certifies the *committed*
# library, so violations in a file git does not track are a parallel session's mid-flight scratch
# (uncommitted): they WARN but must not FAIL — else one session's throwaway blocks everyone's
# commits.  Fail-safe: if git membership can't be determined, treat every file as tracked (strict),
# so the certification guarantee is never silently weakened.
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  git_ok=1
  tracked_list=$(git ls-files 2>/dev/null)
else
  git_ok=0
  tracked_list=""
fi
is_tracked() {  # is_tracked FILE → 0 (tracked → FAIL on violation) | 1 (untracked → WARN only)
  [ "$git_ok" -eq 0 ] && return 0
  case $'\n'"$tracked_list"$'\n' in
    *$'\n'"$1"$'\n'*) return 0 ;;
    *) return 1 ;;
  esac
}

fail=0
stray_axioms="";  warn_axioms=""
stray_sorries=""; warn_sorries=""
native="";        warn_native=""

allow_re=" $(echo "$SORRY_ALLOWLIST" | sed 's/ / | /g') "
for f in $lean_files; do
  if is_tracked "$f"; then tracked=1; else tracked=0; fi
  hits=$(grep_code '^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]' "$f")
  if [ -n "$hits" ] && [ "$f" != "$AXIOMS_FILE" ]; then
    if [ "$tracked" -eq 1 ]; then stray_axioms+="$hits"$'\n'; else warn_axioms+="$hits"$'\n'; fi
  fi
  case "$allow_re" in
    *" $f "*) ;;  # allowlisted (always tracked; intentional gap)
    *)
      hits=$(grep_code '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' "$f")
      if [ -n "$hits" ]; then
        if [ "$tracked" -eq 1 ]; then stray_sorries+="$hits"$'\n'; else warn_sorries+="$hits"$'\n'; fi
      fi
      ;;
  esac
  hits=$(grep_code '(^|[^[:alnum:]_])native_decide([^[:alnum:]_]|$)' "$f")
  if [ -n "$hits" ]; then
    if [ "$tracked" -eq 1 ]; then native+="$hits"$'\n'; else warn_native+="$hits"$'\n'; fi
  fi
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

# -- Untracked-scratch WARN (P-24) -------------------------------------------
# Violations in files git does not track are a parallel session's uncommitted scratch, not part of
# the certified library: they WARN but do not fail the gate.  To silence, move throwaway prototypes
# out of GQ2/ (session scratchpad or the gitignored `scratch/`) — see docs/step2-plan.md.
if [ -n "${warn_axioms//$'\n'/}${warn_sorries//$'\n'/}${warn_native//$'\n'/}" ]; then
  echo "WARN: untracked (uncommitted) file(s) contain guard violations — NOT failing the gate:"
  [ -n "${warn_axioms//$'\n'/}" ]  && { echo "      · stray axiom(s):"; printf '%s' "$warn_axioms"  | sed 's/^/          /'; }
  [ -n "${warn_sorries//$'\n'/}" ] && { echo "      · sorry:";          printf '%s' "$warn_sorries" | sed 's/^/          /'; }
  [ -n "${warn_native//$'\n'/}" ]  && { echo "      · native_decide:";  printf '%s' "$warn_native"  | sed 's/^/          /'; }
  echo "      (throwaway prototypes belong outside GQ2/; see docs/step2-plan.md conventions)"
fi

if [ "$fail" -ne 0 ]; then
  echo "check_axioms: FAILED"
  exit 1
fi
echo "check_axioms: all checks passed"
