#!/usr/bin/env bash
# T-19 guard: axiom hygiene for the GQ2 library.
#
# Checks 1-4 are textual and comment-aware; check 5 walks the elaborated environment
# (run from anywhere):
#   1. `axiom` declarations appear ONLY in GQ2/Foundations/Axioms.lean.
#   2. `sorry` appears nowhere (the allowlist is empty — the library is fully proved;
#      re-add a file to SORRY_ALLOWLIST only for a deliberate, ticketed gap).
#   3. The axiom census in Axioms.lean matches the expected count (bump EXPECTED_AXIOMS
#      when a new B-leaf lands, in the same commit).
#   4. No `native_decide` anywhere (it would add `Lean.ofReduceBool` beyond the standard
#      three axioms; the project convention is kernel-checked `decide` only).
#   5. Terminal-theorem axiom audit: the campaign capstones print EXACTLY the standard
#      three plus the frozen literature census, and each Γ_R capstone prints identically
#      to its Γ_A twin.  Needs a built library; skips with a notice otherwise.
#
# For checks 1-4, comments and docstrings are stripped before matching (a nesting-aware
# scan of `/- … -/` and `--`), so prose mentioning "axiom"/"sorry" does not trip the guard.
#
# Per-declaration spot checks beyond the audited capstones are done with `#print axioms` /
# the lean-lsp `lean_verify` tool; the board's acceptance criterion is "standard three" for
# every theorem, plus the B-leaf axioms for their declared consumers.

set -euo pipefail
cd "$(dirname "$0")/.."

AXIOMS_FILE='GQ2/Foundations/Axioms.lean'
EXPECTED_AXIOMS=9  # B1, B3c, B5, B6, B7, B8, B9, B10, B11a — B4 deleted 2026-07-10 (unused; B3c subsumes a marked B4), following B2 (B10: census decision, P-06 escalation; B9 base-generalized + B11 added: census decision, P-15 escalation, 2026-07-03; B11 split into B11a hilbertSymbol_normCriterion_finiteDyadic + B11b unramifiedQuadratic_units_are_norms, census 12→13: P-23 / adversarial review rec 2, user-approved 2026-07-04 — old dyadicNormCriterion re-derived as a same-name theorem, the spectral-norm bridge isolated as a def not an axiom; B12 kummerClassK_surjective + B13 dyadicUnitFiltration added, census 13→15: P-15f1 instantiation, user-approved 2026-07-06, docs/p15f1-axiom-proposal.md; B12 discharged as a same-name theorem over the std-3 proof in GQ2/KummerSurjectivity.lean + GQ2/KummerKrullBridge.lean AND the unused B2 cyclotomicCharacter_two_surjective deleted, census 15→13: B12 board, user-approved 2026-07-09; B7' hilbertSymbol_dyadic discharged as a same-name theorem over the std-3 proof in GQ2/HilbertSymbolDyadicClose.lean, census 13→12: B7' board, user-approved 2026-07-09; B13 dyadicUnitFiltration discharged as a same-name noncomputable def over the std-3 proof in GQ2/UnitFiltrationCounts.lean + GQ2/UnitFiltrationTop.lean, census 12→11: B13 board, user-approved 2026-07-09; B11b unramifiedQuadratic_units_are_norms discharged as a same-name theorem over the std-3 proof in GQ2/UnramifiedQuadraticNorms.lean + GQ2/TeichmullerLift.lean, census 11→10: B11b board, user-approved 2026-07-09 — dyadicNormCriterion now rests on B11a alone; B9 evensKahn_dyadic REPLACED by the relative Stiefel-Whitney identity relativeStiefelWhitney_dyadic with evensKahn_dyadic re-derived as a same-name theorem from it + B11a, census 9→9: B9-A board docs/orchestration/b9a-tickets.md, user-approved 2026-07-24)
# Emptied 2026-07-08 (library fully sorry-free; last leaves GammaA/FoxHeisenberg/SectionSeven
# discharged); held the four GQ2/Roe/Labute/ skeletons while the L-campaign was in flight
# (R40, 2026-07-25) and RE-EMPTIED at L6 (2026-07-26) when the Labute classification instance
# landed as the sorry-free theorem `GQ2.Roe.Labute.bLab` — per-ticket history in
# docs/orchestration/{tickets.md,roe-tickets.md} and the git log of this line.
SORRY_ALLOWLIST=''

# -- check 5 configuration ---------------------------------------------------
# The exact axiom set every audited capstone must print: the standard three plus the frozen
# census of EXPECTED_AXIOMS literature axioms (GQ2/Foundations/Axioms.lean).  Order is
# irrelevant — both sides are sorted before comparison — but membership is exact, so a
# `sorryAx`, a stray axiom, or a dropped B-leaf all show up as a diff.
AUDIT_EXPECTED_AXIOMS='propext Classical.choice Quot.sound
GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated
GQ2.Foundations.absGalQ2_localEulerCharacteristic
GQ2.dyadicOrientation
GQ2.localReciprocity
GQ2.tateDualityAt
GQ2.peripheralCyclotomicAction
GQ2.relativeStiefelWhitney_dyadic
GQ2.tameQuotient
GQ2.hilbertSymbol_normCriterion_finiteDyadic'

# Declarations whose axiom set must equal AUDIT_EXPECTED_AXIOMS exactly, one per line.
# The Γ_R capstones (R32) are hypothesis-parametrized by `BLabHypothesis`; a hypothesis binder
# contributes nothing to an axiom print, so they are audited exactly like the Γ_A capstones.
# `main_presentation_literal_roe_unconditional` (L6) is that binder *discharged* by the theorem
# `GQ2.Roe.Labute.bLab` (std-3, no `sorryAx`): auditing it against the same expected set is what
# certifies that proving the Labute instance — rather than assuming it — widened nothing.
AUDIT_DECLS='GQ2.main_presentation_literal_roe
GQ2.main_presentation_literal_roe_unconditional
GQ2.eq_154_R
GQ2.main_surjection_count_R
GQ2.admissibleCountR_eq_admissibleCount'

# "Γ_A twin" / "Γ_R twin" pairs that must print identically, one pair per line.  The Γ_A side is
# read-only here: this asserts the R-campaign did not widen the trust base, without restating
# (or being able to relax) the Γ_A rows recorded in formalization.yaml and comparator-config.json.
AUDIT_PAIRS="GQ2.main_presentation_literal GQ2.main_presentation_literal_roe
GQ2.SectionTen.eq_154 GQ2.eq_154_R
GQ2.SectionTen.main_surjection_count' GQ2.main_surjection_count_R"

# Strip Lean comments: nested block comments `/- … -/` (incl. docstrings `/-- … -/`) and
# line comments `-- …`.  Emits one output line per input line (line numbers preserved).
# Used by check 3; checks 1/2/4 inline the same scan into their single-pass sweep below.
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

# Checks 1, 2 and 4 in ONE awk pass over the whole library (a pipeline per file per pattern
# cost minutes).  The comment scan is strip_comments' loop verbatim, with the nesting depth
# reset at each file's first line so state cannot leak across files; each stripped line is
# tested against the three patterns and every hit is emitted as "TAG<TAB>FILE:LINE:code" —
# the payload a per-file `strip_comments | grep -nE | sed` produced.  Paths carry no spaces
# (as the loop this replaced also assumed), so they can go straight into argv.
set -- $lean_files
scan=$(awk '
  FNR == 1 { depth = 0 }
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
    hit = FILENAME ":" FNR ":" out
    if (out ~ /^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]/) print "AX\t" hit
    if (out ~ /(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)/) print "SORRY\t" hit
    if (out ~ /(^|[^[:alnum:]_])native_decide([^[:alnum:]_]|$)/) print "ND\t" hit
  }' "$@")

# Partition the tagged hits into the FAIL/WARN buckets (P-24 split on git membership).
while IFS= read -r rec; do
  if [ -z "$rec" ]; then continue; fi  # no hits at all → the here-doc is a single blank line
  tag=${rec%%$'\t'*}; hit=${rec#*$'\t'}; f=${hit%%:*}
  if is_tracked "$f"; then tracked=1; else tracked=0; fi
  case "$tag" in
    AX)
      if [ "$f" = "$AXIOMS_FILE" ]; then continue; fi
      if [ "$tracked" -eq 1 ]; then stray_axioms+="$hit"$'\n'; else warn_axioms+="$hit"$'\n'; fi
      ;;
    SORRY)
      case "$allow_re" in
        *" $f "*) continue ;;  # allowlisted (always tracked; intentional gap)
      esac
      if [ "$tracked" -eq 1 ]; then stray_sorries+="$hit"$'\n'; else warn_sorries+="$hit"$'\n'; fi
      ;;
    ND)
      if [ "$tracked" -eq 1 ]; then native+="$hit"$'\n'; else warn_native+="$hit"$'\n'; fi
      ;;
  esac
done <<EOF
$scan
EOF

# -- 1. axiom placement ------------------------------------------------------
if [ -n "${stray_axioms//$'\n'/}" ]; then
  echo "FAIL: axiom declarations outside ${AXIOMS_FILE}:"
  printf '%s' "$stray_axioms"
  fail=1
else
  echo "OK:   all axiom declarations live in ${AXIOMS_FILE}"
fi

# -- 2. sorry allowlist ------------------------------------------------------
allow_desc=${SORRY_ALLOWLIST:-'empty — the library is fully proved'}
if [ -n "${stray_sorries//$'\n'/}" ]; then
  echo "FAIL: sorry outside the allowlist (${allow_desc}):"
  printf '%s' "$stray_sorries"
  fail=1
else
  echo "OK:   sorries only in the allowlist (${allow_desc})"
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

# -- 5. terminal-theorem axiom audit -----------------------------------------
# Unlike checks 1-4 this one walks the *elaborated* environment, so it needs a built library; when
# the oleans are absent it prints a SKIP rather than failing, keeping the textual guard usable on a
# cold checkout.  CI builds before invoking this script, so there check 5 always runs.
audit_ok=1
if ! command -v lake >/dev/null 2>&1 || [ ! -f .lake/build/lib/lean/GQ2/Roe/Main.olean ]; then
  echo "SKIP: terminal-theorem axiom audit — library not built (run 'lake build GQ2' to enable)"
else
  probe_dir=$(mktemp -d)
  trap 'rm -rf "$probe_dir"' EXIT
  probe_names=$(
    { printf '%s\n' "$AUDIT_DECLS"; printf '%s\n' "$AUDIT_PAIRS" | tr ' ' '\n'; } |
      sed '/^$/d' | LC_ALL=C sort -u | sed 's/^/"/; s/$/"/' | paste -sd, -
  )
  # `collectAxioms` is the same environment walk `#print axioms` performs, emitted in a canonical
  # one-line form so the comparison below is not sensitive to pretty-printer line breaking.
  cat > "$probe_dir/AxiomProbe.lean" <<LEAN
import GQ2.PresentationLiteral
import GQ2.SectionTenSources
import GQ2.Roe.Main

open Lean in
run_cmd do
  let env ← getEnv
  for s in [$probe_names] do
    let n := s.toName
    unless env.contains n do
      throwError "axiom audit: unknown declaration {n} (renamed, removed, or not imported here?)"
    let axs := (← collectAxioms n).qsort (·.toString < ·.toString)
    IO.println s!"AXIOMS {n} :: {String.intercalate " " (axs.toList.map toString)}"
LEAN
  if ! probe_out=$(lake env lean "$probe_dir/AxiomProbe.lean" 2>&1); then
    echo "FAIL: terminal-theorem axiom audit could not run ('lake env lean' failed):"
    printf '%s\n' "$probe_out" | sed 's/^/          /'
    audit_ok=0
    probe_out=''
  fi

  norm_axioms() { tr ' ' '\n' | sed '/^$/d' | LC_ALL=C sort | tr '\n' ' '; }
  axioms_of() { printf '%s\n' "$probe_out" | awk -v d="$1" -F' :: ' '$1 == "AXIOMS " d {print $2}'; }

  expected_norm=$(printf '%s' "$AUDIT_EXPECTED_AXIOMS" | norm_axioms)
  audited=0
  while IFS= read -r d; do
    [ -z "$d" ] && continue
    got=$(axioms_of "$d" | norm_axioms)
    audited=$((audited + 1))
    if [ -z "$got" ]; then
      echo "FAIL: axiom audit: no axiom print for ${d}"
      audit_ok=0
    elif [ "$got" != "$expected_norm" ]; then
      echo "FAIL: axiom audit: ${d} does not print the expected census set:"
      echo "          expected: ${expected_norm}"
      echo "          actual:   ${got}"
      audit_ok=0
    fi
  done <<EOF
$AUDIT_DECLS
EOF

  paired=0
  while IFS=' ' read -r a b; do
    [ -z "$a" ] && continue
    ga=$(axioms_of "$a" | norm_axioms)
    gb=$(axioms_of "$b" | norm_axioms)
    paired=$((paired + 1))
    if [ -z "$ga" ] || [ -z "$gb" ]; then
      echo "FAIL: axiom audit: missing axiom print for the pair ${a} / ${b}"
      audit_ok=0
    elif [ "$ga" != "$gb" ]; then
      echo "FAIL: axiom audit: ${b} does not print identically to its twin ${a}:"
      echo "          ${a}: ${ga}"
      echo "          ${b}: ${gb}"
      audit_ok=0
    fi
  done <<EOF
$AUDIT_PAIRS
EOF

  if [ "$audit_ok" -eq 1 ]; then
    echo "OK:   terminal-theorem axiom audit: ${audited} capstone(s) at the expected census set"
    echo "      (std-3 + ${EXPECTED_AXIOMS} literature axioms, no sorryAx), ${paired} twin pair(s) identical"
  else
    fail=1
  fi
fi

# -- Untracked-scratch WARN (P-24) -------------------------------------------
# Violations in files git does not track are a parallel session's uncommitted scratch, not part of
# the certified library: they WARN but do not fail the gate.  To silence, move throwaway prototypes
# out of GQ2/ (session scratchpad or the gitignored `scratch/`) — see docs/orchestration/step2-plan.md.
if [ -n "${warn_axioms//$'\n'/}${warn_sorries//$'\n'/}${warn_native//$'\n'/}" ]; then
  echo "WARN: untracked (uncommitted) file(s) contain guard violations — NOT failing the gate:"
  [ -n "${warn_axioms//$'\n'/}" ]  && { echo "      · stray axiom(s):"; printf '%s' "$warn_axioms"  | sed 's/^/          /'; }
  [ -n "${warn_sorries//$'\n'/}" ] && { echo "      · sorry:";          printf '%s' "$warn_sorries" | sed 's/^/          /'; }
  [ -n "${warn_native//$'\n'/}" ]  && { echo "      · native_decide:";  printf '%s' "$warn_native"  | sed 's/^/          /'; }
  echo "      (throwaway prototypes belong outside GQ2/; see docs/orchestration/step2-plan.md conventions)"
fi

if [ "$fail" -ne 0 ]; then
  echo "check_axioms: FAILED"
  exit 1
fi
echo "check_axioms: all checks passed"
