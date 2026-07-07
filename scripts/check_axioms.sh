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
EXPECTED_AXIOMS=15  # B1, B2, B3c, B4, B5, B6, B7, B7', B8, B9, B10, B11a, B11b, B12, B13 (B10: census decision, P-06 escalation; B9 base-generalized + B11 added: census decision, P-15 escalation, 2026-07-03; B11 split into B11a hilbertSymbol_normCriterion_finiteDyadic + B11b unramifiedQuadratic_units_are_norms, census 12→13: P-23 / adversarial review rec 2, user-approved 2026-07-04 — old dyadicNormCriterion re-derived as a same-name theorem, the spectral-norm bridge isolated as a def not an axiom); B12 kummerClassK_surjective + B13 dyadicUnitFiltration added, census 13→15: P-15f1 instantiation, user-approved 2026-07-06 (docs/p15f1-axiom-proposal.md)
SORRY_ALLOWLIST='GQ2/Prop89Close.lean GQ2/GammaA.lean GQ2/SectionNine.lean GQ2/FoxHeisenberg.lean GQ2/SectionSix.lean GQ2/SectionSeven.lean GQ2/SectionEight.lean GQ2/RStageGammaA.lean'  # SectionTen.lean + Statement.lean REMOVED 2026-07-07 (P-18e CLOSED): eq_154 (Nat.card ContSurj GammaA = ContSurj AbsGalQ2) + main_surjection_count' PROVED in GQ2/SectionTenSources.lean (A-side needs boundaryMapsWitness, downstream of SectionTen; via card_contSurj_eq ×2 + thm_4_2 per frame + hE2-trivial-on-PUnit; carry sorryAx through the allowlisted §9 thm_4_2 until P-17i) — SectionTen.lean now sorry-free; Statement.lean main_surjection_count MOVED (comment-pointer) + main_presentation gains hypothesis hcount (P-19 supplies from main_surjection_count'), Statement.lean now sorry-free. RStageGammaA.lean ADDED 2026-07-07 (P-16d6e5): the Γ_A (136) residue skeleton — hZcount_gammaA + hsep_hom_gammaA sorried (htriv_gammaA + stageR136_gammaA_of_hcard assembly proved); removed as the two fill. SectionTen.lean ADDED 2026-07-07 (P-18a): the §10 statement skeleton — remaining sorries lemma_10_1/card_contSurj_eq (P-18c), eq_154 (P-18e); twoCore_normal/twoCore_isPGroup/isPGroup_map_of_isProP DONE (P-18b, 2026-07-07, std-3); removed when P-18c/e land. Half139Local.lean removed 2026-07-07 (P-16d6d CLOSED): hMcountM_local (#MLifts=|M_B|²) FULLY PROVED, sorry-free — M-module + card_Z1_eq (Step 3) + hfix (#fixedPts=1 via lemma_7_1_dual, Step 4) + MLifts≃Z¹ torsor equiv + Nonempty(MLifts) via extension-splitting (factor-set 2-cocycle is a coboundary since #H²=1, then f=ψ⁻¹·s lifts ρ'). Gate CONFIRMED 2026-07-07: `lake build GQ2.Half139Local` green (8659 jobs); `#print axioms half139_local` = std-3 + B6(tateDualityAt) + B7(absGalQ2_localEulerCharacteristic), NO sorryAx; check_axioms all-pass. # PhaseMuIndep.lean removed 2026-07-06 (P-16d6b CLOSED): tcocycle_mu_indep + tcocycle_card_indep + mlifts_card_eq_image_mul_tcocycle all proved std-3, file sorry-free — μ-independence reduced via the torsor identity #MLifts = #(red_T image)·#Z¹(T) to the per-source #MLifts / #(red_T image) counts fed at the P-16d6e assembly (mirrors half139_via_radData's hMcountM; prop_5_16_bundle is AbsGalQ2-only, so no generic Route-B proof exists for this file's abstract Γ — see docs/p16d6b-handoff.md §6). RegularSummand.lean removed 2026-07-06: P-17e4 CLOSED (lemma_6_11 PAPER NODE fully proved std-3, no B-axioms — involution_fixedPoints_sq_le discharged by the F2-rational trace-element argument; file sorry-free). BoundaryFrame.lean swapped for SectionNine.lean 2026-07-06 (P-17a): thm_4_2/thm_4_2_stratum relocated there with the reviewed hE2 amendment; BoundaryFrame now sorry-free; SectionNine carries the P-17 skeleton sorries (terminal_count_eq, kappa0_exists, blockFrame, blockEnrichment, mStage_partition, count_eq_of_closedRecursion, thm_4_2), removed by P-17b-i.  # Transgression.lean removed 2026-07-04: P-15i CLOSED (κ⁰_q hypothesis restored per docs/p15i-transgression-gap.md; splitting_of_global_cocycle + lemma_6_21 proved std-3, file sorry-free). HilbertLedger.lean removed 2026-07-04: P-15e O-finish CLOSED (all 6 sub-lemmas proved; whole file sorry-free; evensNorm_deepUnit_vanish = std-3 + B9/B11). Reconstruction.lean removed: exists_contSurj_of_card_le proved (P-02). RepIndependence.lean removed 2026-07-04: P-15d CLOSED (lemma_6_14 proved std-3, no B-axioms, sorry-free — inner-conjugation coboundary on V⋊C; statement moved out of SectionSix.lean, comment-pointer there). SectionThree.lean removed 2026-07-03: P-07 CLOSED (markedHom_bijective proved from B5, std-3; last §3 sorry). SectionThreeMarked.lean removed 2026-07-05: P-25 CLOSED all three §3-marked sorries — prop_3_10_gammaA, prop_3_10_local_marked, prop_3_14 all spliced; file sorry-free. BoundaryFrame: P-11 thm_4_2 (removed by P-17); BoundaryMapsWitness.lean removed 2026-07-06: P-25 CLOSED — the two atoms discharged by the B10′ orientation clauses (B10 strengthened in place, user-approved; census unchanged); file sorry-free, prop_3_14 sorryAx-free (std-3 + B3c/B5/B8/B10′); FoxHeisenberg: P-12 §5 statements (removed by P-13); SectionSix+SectionSeven: P-14 §§6–7 statements (removed by P-15a–i); SectionEight: P-16 §8 statements — 8.2×2, 8.3, 8.6×2, prop_8_9 (removed by P-16 O-half); UnramifiedModel removed 2026-07-05: P-15f3 CLOSED (prop_6_18_unramified proved std-3+B7, no sorryAx; file sorry-free)

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
