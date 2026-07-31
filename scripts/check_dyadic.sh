#!/usr/bin/env bash
# Dyadic-campaign gate — branch `dyadic` (general 2-adic fields, ramified-i case).
#
# `scripts/check_axioms.sh` stays the primary gate: it certifies axiom placement, the census
# count, `sorry`/`native_decide` hygiene, and the per-capstone expected-axiom audit.  This
# script WRAPS it (check D1 below runs it verbatim and propagates its exit code) and adds the
# checks that are specific to the dyadic campaign.  Run from anywhere:
#
#     bash scripts/check_dyadic.sh
#
# Nothing here needs a built library; check_axioms.sh's check 5 self-skips on a cold checkout
# and that behaviour is deliberately untouched.  A full lane → `dyadic` merge still needs the
# build green as well (plan §7 item 1) — this script does not build.
#
# ---------------------------------------------------------------------------
# The per-ticket SORRY_ALLOWLIST workflow
# ---------------------------------------------------------------------------
# The campaign runs many parallel lane worktrees, so a mid-flight `sorry` is allowed to land —
# but only in a file that is named, per ticket, in the `SORRY_ALLOWLIST` of
# `scripts/check_axioms.sh`.  Protocol (docs/dyadic/tickets.md "Board protocol" bullets 5-6;
# docs/dyadic/plan.md §7 items 2-3):
#
#   * The ORCHESTRATOR owns the allowlist.  A worker never edits check_axioms.sh; it gets the
#     entry at dispatch time, together with the ticket id recorded in the comment above the
#     variable.  Same rule for `EXPECTED_AXIOMS`, which moves only in an owner-approved AX
#     census-flip commit.
#   * Entries name the exact in-flight file (a path, never a directory or a glob), so the
#     allowlist doubles as the list of files a reviewer must still read by hand.
#   * The allowlist is EMPTY at every wave close.  That is the wave's exit condition and what
#     makes merge gate 2 ("no `sorry` outside `SORRY_ALLOWLIST`-ticketed in-flight files")
#     mechanical rather than aspirational.
#   * The nine obligations never enter the allowlist mechanism as axioms — see D2.
#
# Consequence for this script: D1 inherits the allowlist exactly as configured, so a green run
# means "green modulo the currently ticketed in-flight files", and check_axioms.sh's
# `SORRY_ALLOWLIST` line is the list of those files.
#
# ---------------------------------------------------------------------------
# What this script checks
# ---------------------------------------------------------------------------
#   D1  Delegate to `scripts/check_axioms.sh` and propagate failure.
#       → merge gates 1 (its half), 2, 3, 8 (its check 5, when the library is built), 10.
#   D2  Obligation guard: none of the nine proof obligations — by campaign id or by the Lean
#       names reserved for their hypothesis binders — may appear in an `axiom` declaration,
#       in `GQ2/Foundations/Axioms.lean` or anywhere else under `GQ2/`.  → merge gate 4.
#   D3  Sign-row guard: no `.lean` file under `GQ2/Dyadic/` may declare a sign-row constructor
#       or definition.  → packet Prop. 8.1 / docs/dyadic/refs/README.md override 1.
#   D4  One-tree hash hook: placeholder until WW5 lands the generated artifacts.
#       → merge gate 7 (its hash half).
#   D5  Python sanity harness (scripts/dyadic_sanity_counts.py, F5 — live since 2026-07-31).
#       → evidence for merge gates 5 and 9 (regressions only, never cited by a proof).
#
# NOT mechanized here, and still reviewed by hand at every merge: gate 5 (no field-specific
# presentation-isomorphism axiom; no theorem proved by finite-target testing), gate 6 (full
# ℤ₂-valued unramified marking in marked statements), gate 9 (the ℚ₂(√-10) instance uses the
# procyclic row (r,ε,η) = (1,1,1)), and the certificate-content half of gate 7.
#
# Text-matching conventions.  Both textual checks strip Lean comments first, with the same
# nesting-aware scan of `/- … -/` and `--` that check_axioms.sh uses (the loop is copied, not
# imported, so this script stays standalone); prose mentioning an obligation or the sign row
# therefore never trips a guard.  D2 matches its tokens as plain substrings — deliberately
# conservative, since no legitimate axiom mentions them at all — while D3 matches on word
# boundaries, case-sensitively, so that an exclusion *theorem* named for the sign row is
# allowed and only a `def`/`structure`/`inductive`-constructor/field carrying the name is not.
#
# One deliberate divergence from check_axioms.sh: its P-24 rule downgrades violations in
# git-untracked files to a WARN, because several sessions once shared one worktree and a
# throwaway prototype must not block everyone's commits.  The dyadic campaign gives every lane
# its OWN worktree (plan §5), so an untracked file under `GQ2/` is this lane's own work in
# progress — D2 and D3 fail on it, which is the point: an obligation-as-axiom or a sign-row
# datum should be caught before the commit, not after.
#
# Both guards are tripwires, not proofs: a declaration that renames its way around the token
# list passes them.  They exist so that the obvious slip fails loudly and early.

set -euo pipefail
cd "$(dirname "$0")/.."

AXIOMS_FILE='GQ2/Foundations/Axioms.lean'
DYADIC_DIR='GQ2/Dyadic'
GENERATED_LATEX='generated/latex'
HASH_MANIFEST='generated/hash-manifest.json'
SANITY_SCRIPT='scripts/dyadic_sanity_counts.py'

# The nine proof obligations (docs/dyadic/plan.md §2, board "Obligation tracker") by campaign
# id, followed by the Lean names reserved for their hypothesis-binder / certificate interim
# states (docs/dyadic/tickets.md MC1, MC5, AS1).  A campaign id cannot occur in an ordinary
# Lean identifier — it can only reach elaborated code through a guillemet identifier such as
# `«MC-M»` or a string literal — so the id rows mostly guard against a copy-paste from the
# board; the Lean-name rows are the ones that catch a real mistake.
OBLIGATION_TOKENS='MC-M
MC-N
WC-L
WC-N0
WC-Npc
WC-M0
WC-Mpc
LG-K
SD-n
MLabHypothesis
NLabHypothesis
BranchCertificate
WordCertificate
MarkedCoreCertificate'

# The sign-Frobenius row does not exist: under the standing ramified-i hypothesis η is odd, so
# the M_α families are exactly compact (r = 0) and procyclic (r ≥ 1, η ∈ ℤ₂ˣ) — packet
# Prop. 8.1, recorded as override 1 in docs/dyadic/refs/README.md, and the reason F1's branch
# datum has five rows.  The draft's superseded `R_{M,sgn}` formulas are archived in the
# ~/claude/general_2adic/ working repo; they are never re-entered here, in any form.
SIGNROW_TOKENS='Msgn
MSign
signRow
SignFrobenius'

# join_alt TOKENS → ERE alternation ("a\nb\nc" → "a|b|c").  The tokens contain no ERE
# metacharacters (letters, digits and `-`, which is literal outside a bracket expression).
join_alt() {
  printf '%s\n' "$1" | sed '/^[[:space:]]*$/d' | tr '\n' '|' | sed 's/|$//'
}

# Comment-stripping prologue for the awk scans below: check_axioms.sh's `strip_comments` loop
# verbatim, with the nesting depth reset at each file's first line so state cannot leak across
# files.  It leaves the main block OPEN — each caller appends its own emit logic and the
# closing brace.  `out` holds the comment-free text of the current line.
STRIP_PROLOGUE='
FNR == 1 { depth = 0; inax = 0 }
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
'

fail=0

# -- D1. the primary gate ----------------------------------------------------
# Run check_axioms.sh unchanged and quote its whole report (indented) so the two scripts'
# outputs stay distinguishable.  Its exit code is authoritative for checks 1-5.
if axioms_out=$(bash scripts/check_axioms.sh 2>&1); then
  echo "OK:   scripts/check_axioms.sh passed — its report follows"
else
  echo "FAIL: scripts/check_axioms.sh failed — its report follows"
  fail=1
fi
printf '%s\n' "$axioms_out" | sed 's/^/      /'

# -- D2. obligation guard (merge gate 4) -------------------------------------
# The nine obligations are PROOF obligations and must never be assumed.  An `axiom` declaration
# is taken to run from its `axiom` line through the indented, non-blank lines that follow it
# (Lean's layout for a multi-line signature — cf. `relativeStiefelWhitney_dyadic` in
# Axioms.lean); a blank line or a line starting in column 1 ends it.  So a token hidden in a
# continuation line of the signature is caught too, not just one in the axiom's name.
#
# Scanning all of GQ2/ rather than only Axioms.lean is defense in depth: check_axioms.sh
# check 1 already confines `axiom` to Axioms.lean, and this second sweep would still catch an
# obligation smuggled in through a hypothetical relaxation of that rule.
lean_files=$(find GQ2 -name '*.lean' | sort; echo GQ2.lean)
obligation_re=$(join_alt "$OBLIGATION_TOKENS")

set -- $lean_files
obligation_hits=$(awk -v re="$obligation_re" "$STRIP_PROLOGUE"'
  if (out ~ /^[[:space:]]*(public[[:space:]]+|private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+)*axiom[[:space:]]/) {
    inax = 1
  } else if (inax && (out ~ /^[[:space:]]*$/ || out ~ /^[^[:space:]]/)) {
    inax = 0
  }
  if (inax && out ~ re) print FILENAME ":" FNR ":" out
}' "$@")

census_hits=''; stray_hits=''
while IFS= read -r hit; do
  if [ -z "$hit" ]; then continue; fi  # no hits at all → the here-doc is a single blank line
  f=${hit%%:*}
  if [ "$f" = "$AXIOMS_FILE" ]; then census_hits+="$hit"$'\n'; else stray_hits+="$hit"$'\n'; fi
done <<EOF
$obligation_hits
EOF

if [ -n "${census_hits//$'\n'/}${stray_hits//$'\n'/}" ]; then
  echo "FAIL: an obligation token appears in an axiom declaration (merge gate 4):"
  if [ -n "${census_hits//$'\n'/}" ]; then
    echo "      · in ${AXIOMS_FILE} (the literature census):"
    printf '%s' "$census_hits" | sed 's/^/          /'
  fi
  if [ -n "${stray_hits//$'\n'/}" ]; then
    echo "      · elsewhere under GQ2/ (stray axiom, or an allowlisted bypass of check 1):"
    printf '%s' "$stray_hits" | sed 's/^/          /'
  fi
  echo "      MC-M, MC-N, WC-L, WC-N0, WC-Npc, WC-M0, WC-Mpc, LG-K and SD-n are proof"
  echo "      obligations, never axioms — not even temporarily.  The permitted interim states"
  echo "      are an explicit hypothesis binder (the BLabHypothesis pattern) or a sorry in a"
  echo "      file the orchestrator has put in check_axioms.sh's SORRY_ALLOWLIST."
  fail=1
else
  echo "OK:   obligation guard — none of the 9 obligations declared as axiom"
fi

# -- D3. sign-row guard ------------------------------------------------------
# packet Prop. 8.1 (docs/dyadic/refs/README.md override 1): the sign-Frobenius row is removed
# from the ramified-i assembly, so no sign-row datum may be declared under GQ2/Dyadic/.  A line
# fails when it contains a sign-row token AND introduces a definition (`def`/`abbrev`/
# `structure`/`inductive`/`class`/`instance`/`opaque`), an inductive constructor alternative
# (`| …`), or a field/binder named for the token.  An exclusion *theorem* mentioning the row —
# which F4 legitimately proves — is not a declaration of it and passes.
signrow_alt=$(join_alt "$SIGNROW_TOKENS")
signrow_re="(^|[^[:alnum:]_])(${signrow_alt})([^[:alnum:]_]|$)"
signrow_field_re="^[[:space:]]*(${signrow_alt})[[:space:]]*:"
signrow_decl_re='(^|[^[:alnum:]_.])(def|abbrev|structure|inductive|class|instance|opaque)[[:space:]]'

dyadic_files=''
if [ -d "$DYADIC_DIR" ]; then
  dyadic_files=$(find "$DYADIC_DIR" -name '*.lean' | sort)
fi

if [ -z "$dyadic_files" ]; then
  echo "SKIP: sign-row guard — no .lean files under ${DYADIC_DIR}/ yet"
else
  set -- $dyadic_files
  signrow_hits=$(awk -v tokre="$signrow_re" -v declre="$signrow_decl_re" \
                     -v fieldre="$signrow_field_re" "$STRIP_PROLOGUE"'
    if (out ~ tokre && (out ~ declre || out ~ /^[[:space:]]*[|]/ || out ~ fieldre))
      print FILENAME ":" FNR ":" out
  }' "$@")

  if [ -n "${signrow_hits//$'\n'/}" ]; then
    echo "FAIL: sign-row declaration under ${DYADIC_DIR}/:"
    # awk's output, unlike the D2 buckets, has its trailing newline eaten by `$( )`.
    printf '%s\n' "$signrow_hits" | sed 's/^/          /'
    echo "      The sign-Frobenius row does not exist (packet Prop. 8.1 /"
    echo "      docs/dyadic/refs/README.md override 1): η even forces r = 1, ε = 1 and K(i)/K"
    echo "      unramified, so under the ramified-i hypothesis η is odd and the M_α families"
    echo "      are exactly compact (r = 0) and procyclic (r ≥ 1).  The draft's superseded"
    echo "      sign-row formulas stay archived in the general_2adic working repo, not here."
    fail=1
  else
    echo "OK:   sign-row guard — no sign-row declaration under ${DYADIC_DIR}/"
  fi
fi

# -- D4. one-tree hash check (merge gate 7, WW5 — live since 2026-07-31) -----
# Merge gate 7: the branch words' TeX and Lean must be generated from ONE expression tree, the
# tree's content hash being emitted into both and compared here.  `scripts/dyadic_word_tex.py
# check` reads ${HASH_MANIFEST}, recomputes each tree's content hash, and diffs it against the
# hash embedded in the generated LaTeX and the Lean-side `<decl>_astHash` constant.  It also
# fails when generated LaTeX exists without a manifest (a wave shipped with the gate off).
if [ -d "$GENERATED_LATEX" ] || [ -f "$HASH_MANIFEST" ]; then
  if hash_out=$(python3 scripts/dyadic_word_tex.py check 2>&1); then echo "OK:   one-tree hash check (merge gate 7)"; else echo "FAIL: one-tree hash check (merge gate 7):"; printf '%s\n' "$hash_out" | sed 's/^/          /'; fail=1; fi
else
  echo "SKIP: one-tree hash check — no generated artifacts yet (arrives with wave 2)"
fi

# -- D5. finite-target sanity harness (F5 placeholder) -----------------------
# Regressions only — the harness's counts are never cited by a proof (merge gate 5).  Once F5
# lands it also carries the mutant-rejection rows (wrong conjugation side, un-reversed E_m,
# sign-row word) and the √-10 procyclic-vs-relative-norm agreement behind merge gate 9.
if [ -f "$SANITY_SCRIPT" ]; then
  if ! command -v python3 >/dev/null 2>&1; then
    echo "FAIL: ${SANITY_SCRIPT} is present but python3 was not found on PATH"
    fail=1
  elif sanity_out=$(python3 "$SANITY_SCRIPT" 2>&1); then
    echo "OK:   dyadic sanity harness (${SANITY_SCRIPT}) passed"
  else
    echo "FAIL: dyadic sanity harness (${SANITY_SCRIPT}) failed:"
    printf '%s\n' "$sanity_out" | sed 's/^/          /'
    fail=1
  fi
else
  echo "SKIP: dyadic sanity harness not yet ported (ticket F5, gated on word freeze)"
fi

if [ "$fail" -ne 0 ]; then
  echo "check_dyadic: FAILED"
  exit 1
fi
echo "check_dyadic: all checks passed"
