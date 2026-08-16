#!/usr/bin/env bash
# ============================================================================
# scripts/scoreboard.sh -- THE MACHINE-CHECKED CAMPAIGN SCOREBOARD
#
# Read-only.  Prints the campaign's load-bearing status facts by ELABORATING
# them, not by reading a table somebody maintained by hand.  Nothing here is
# wired into any gate; lanes and the orchestrator run it to see where the
# campaign stands without trusting a note.
#
# WHY THIS EXISTS
#
#   Hand-written status tables in this campaign have gone stale at their own
#   base six times (W78 through W83 house notes).  The failure is always the
#   same shape: a note asserts "X is open" or "row R carries clause C", the
#   theorem that refutes it predates the note, and no reader re-elaborates.
#   Every fact this script prints is re-derived from the tree on each run, so
#   it cannot go stale; the only thing it can be is INCOMPLETE.
#
# RUNNING
#
#   bash scripts/scoreboard.sh            full board
#   bash scripts/scoreboard.sh --raw      the probe's records, unformatted
#
#   Needs the same shared olean cache `scripts/mirror.sh` needs; run
#   `scripts/mirror.sh sweep` first if the cache has advanced.  It invokes
#   `mirror.sh check` on ONE generated probe file and runs NO `lake` command.
#
# ----------------------------------------------------------------------------
# HOW TO ADD A ROW
#
# Add one line to the ROWS table below.  Four fields, `|`-separated:
#
#     GROUP|LABEL|KIND|DECLARATION-NAME
#
#   GROUP  the section it prints under.  A new group name creates a new
#          section, in first-appearance order.
#   LABEL  free text, printed verbatim in the left column.
#   KIND   `decl` or `prod` (below).
#   DECLARATION-NAME  the SHORT name, exactly as it appears after
#          `theorem`/`def`/`abbrev`/`structure` in the source.  The script
#          finds the file, reconstructs the fully-qualified name from the
#          namespace stack, and derives the module to import.  Do NOT write a
#          module, a namespace, a file path or a line number: those are the
#          things that rot.
#
#   KIND `decl` reports, for that one declaration:
#          * EXISTS / MISSING (elaborated, not grepped);
#          * its EXPLICIT binders' types -- i.e. exactly the clauses a caller
#            must supply.  Instance-implicit and implicit binders are dropped;
#          * its axiom census, as `std-3` plus the non-standard names.
#
#          Read the "carries" column as "what a caller must hand this
#          declaration".  For a `theorem` those are its hypotheses; for a
#          `def _ : Prop` they are the `Prop`'s own parameters, which is why
#          e.g. `askCStageVanishing` reports four.  `--raw` prints the full
#          pretty-printed binder types behind the head symbols.
#
#   KIND `prod` reports EVERY declaration in the `GQ2` root whose conclusion
#          has that name as its head constant -- i.e. every producer of that
#          `Prop`/type in the tree -- each with its explicit binders.  This is
#          the row type that catches "no theorem in this tree produces X":
#          the machine enumerates the producers, so the claim cannot be made
#          against a stale memory of the tree.  The scan runs against the
#          UMBRELLA environment (see "THE PROBE" below), so it does NOT depend
#          on which modules the rows happen to name.
#
# WHAT THIS SCRIPT WILL NOT DO
#
#   It carries NO hand-maintained facts: no clause lists, no axiom tags, no
#   "open/closed" verdicts, no line numbers, no counts.  Where a fact cannot
#   be machine-checked cheaply it prints UNVERIFIED and, next to it, the
#   nearest thing that CAN be checked.  Do not "fix" an UNVERIFIED by writing
#   the answer in here; either make it checkable or leave it.
#
# ----------------------------------------------------------------------------
# THE OWNER-ITEMS CONTRACT  (W87-HOUSE)
#
# The OWNER ITEMS section is the one place this board reads PROSE, because
# owner items are prose and there is nothing in the environment to elaborate.
# It therefore does not certify a count; it reads two files that each assert
# one, prints both, and prints whether they agree.  A disagreement is the
# product, not a failure.
#
#   AUTHORITY  `docs/dyadic/owner-items-*.md`, the owner's own memo (newest by
#              name if the glob ever matches more than one, and it says so).
#              Contract: status blocks newest-first, each headed
#                  `## Status at wave N (YYYY-MM-DD)`
#              and the newest block containing, in bold, the phrase
#                  `**<Word> items await you**`
#              with the count as an English number word (one..twenty).  The
#              word is mapped, never parsed; an unmapped word prints
#              UNVERIFIED rather than a guess.
#
#   ARTIFACT   the highest-numbered `docs/dyadic/wNN-house-note.md`.  Contract:
#              a heading matching, case-insensitively, an optional section
#              number, an optional leading "The", then "Owner items", with any
#              trailing gloss after a colon; the items are the lines under it
#              beginning `N.` up to the next heading.
#
# WHY BOTH.  A house note is FROZEN at its lane's close, so an item discharged
# after that close still counts in the note.  That is not hypothetical: wave
# 86's note listed ten items, the tenth being "register the two wave-86
# modules", which `ed382b2e` then discharged, and the wave-86 memo block
# accordingly says nine.  Reading only the note prints the pre-discharge
# number; reading only the memo hides which item moved.
#
# WHY TOLERANT.  Until W87 this section matched `^#+ +Owner items` against the
# note alone.  Six of the ten house notes w77..w86 do not meet that shape
# ("### 4.5  The owner items", "## OWNER ITEMS", "## 4  Owner items: nine
# standing", and w85 with no such heading at all), and the strict match
# reported the miss as the number 0 -- indistinguishable from a note that
# genuinely lists no items.  The board printed `numbered items in it  0` for
# waves 84 and 85 and no reader queried it.  A missing heading now prints as
# NOT FOUND, with the heading it did match echoed back so the reader can see
# what was counted.
#
# DO NOT respond to a DISAGREE line by editing a number into this script.
# ============================================================================
set -uo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
WT=${GQ2_WT:-$(dirname "$HERE")}
MIRROR=$HERE/mirror.sh
RAW=0
[ "${1:-}" = "--raw" ] && RAW=1

# ----------------------------------------------------------------------------
# THE ROWS.  Declaration names only.  See "HOW TO ADD A ROW" above.
# ----------------------------------------------------------------------------
ROWS=$(cat <<'TABLE'
FROZEN ROWS|Q2(v-2)  .N0 2 0|decl|fieldUni_genAsmBranch_sqrtNegTwo
FROZEN ROWS|Q2(v2)   .M0 3 0|decl|fieldUni_genAsmBranch_sqrtTwo
FROZEN ROWS|Q2(v5)   .M0 2 0|decl|fieldFive_genAsmBranch_sqrtFive
FROZEN ROWS|Q2(v10)  .Mpc F|decl|mpcNorm_genAsmBranch_sqrtTen
FROZEN ROWS|Q2(v-10) .Mpc T|decl|mpcNorm_genAsmBranch_sqrtNegTen_of_pivot
FROZEN ROWS|Q2(v-10) via shift|decl|mpcPiv_genAsmBranch_sqrtNegTen_of_shift
FROZEN ROWS|Q2(v-10) untied|decl|mpcPiv_genAsmBranch_sqrtNegTen
FROZEN ROWS|v-10 residue = word prob|decl|mpcOrb_shift_iff_marking
FROZEN ROWS|v-10 finite-class route|decl|mpcWord_shift_of_forall_class_four
FROZEN ROWS|v-10 residual move|prod|MpcPivShift
LEGACY RECORDS (COMPAT ONLY)|Q2(v-2)  .N0 2 0|decl|canRec_rowResidual_sqrtNegTwo
LEGACY RECORDS (COMPAT ONLY)|Q2(v2)   .M0 3 0|decl|canRec_rowResidual_sqrtTwo
LEGACY RECORDS (COMPAT ONLY)|Q2(v5)   .M0 2 0|decl|canRec_rowResidual_sqrtFive
LEGACY RECORDS (COMPAT ONLY)|Q2(v10)  .Mpc F|decl|canRec_rowResidual_sqrtTen
LEGACY RECORDS (COMPAT ONLY)|the tied transport|decl|canRec_rowResidual_of_tied
LEGACY RECORDS (COMPAT ONLY)|v5 cand clause = coeff|decl|rowCl_mCand_exactLifting_iff
LEGACY RECORDS (COMPAT ONLY)|v-2 cand clause = coeff|decl|rowCl_nCand_exactLifting_iff
CORRECTED RN RECORDS|N0 certificate (all a,h)|decl|wPcNWordCertificateRN
CORRECTED RN RECORDS|M0 certificate (from supply)|decl|wPcMWordCertificateRN_of_supply
CORRECTED RN TIED|N0 residual (all a,h)|decl|wPcN_rowResidualRN_of_tied
CORRECTED RN TIED|N0 endpoint (all a,h)|decl|wPcN_candidate_equiv_galKRN_of_tied
CORRECTED RN TIED|M0 residual (all a,h)|decl|wPcM_rowResidualRN_of_tied
CORRECTED RN TIED|M0 endpoint (all a,h)|decl|wPcM_candidate_equiv_galKRN_of_tied
CORRECTED RN CLOSED ROWS|Q2(v-2) residual|decl|wPcN_rowResidualRN_sqrtNegTwo
CORRECTED RN CLOSED ROWS|Q2(v-2) endpoint|decl|wPcN_candidate_equiv_galKRN_sqrtNegTwo
CORRECTED RN CLOSED ROWS|Q2(v2) residual|decl|wPcM_rowResidualRN_sqrtTwo
CORRECTED RN CLOSED ROWS|Q2(v2) endpoint|decl|wPcM_candidate_equiv_galKRN_sqrtTwo
CORRECTED RN CLOSED ROWS|Q2(v5) residual|decl|wPcM_rowResidualRN_sqrtFive
CORRECTED RN CLOSED ROWS|Q2(v5) endpoint|decl|wPcM_candidate_equiv_galKRN_sqrtFive
ODD SEAM|the seam Prop|decl|SqMarkedForwardSupply
ODD SEAM|every seam producer|prod|SqMarkedForwardSupply
ODD SEAM|seam = marked-core cert|decl|oddId_supply_iff_certificate
ODD SEAM|seam = one cup-adapted frame|decl|oddSeam_supply_iff_cupAdaptedFrame
ODD SEAM|seam = the full marking|decl|oddSeam_supply_iff_fullMarking
ODD SEAM|halved relator clause|prod|SqCupAdaptedFrameRelator
ODD SEAM|frame presentation clause|prod|SqCupAdaptedFramePresentation
ODD SEAM|clearing = row-plane family|decl|gClear_clearing_of_model
ODD SEAM|model clearing clause|prod|SqNuOrientedClearAtUnitPivot
ODD SEAM|row-plane move clause|prod|GClearModelMove
ODD SEAM|seam = clearing instance|decl|oddFrame_supply_iff_clearInstance
ODD SEAM|q-invariant of D_sq h|decl|oddSeam_demushkinQ_DSq
ODD SEAM|odd oriented equivalence|decl|nonempty_orientedEquiv_oddDegree
ASK BLOCK|frozen: surviving Prop|decl|askCStageVanishing
ASK BLOCK|frozen <-> stageVanishing|decl|askC_exactLifting_iff_stageVanishing
ASK BLOCK|corrected RN at G_K|decl|exactLiftingSemanticsRN_galK
ASK BLOCK|stokes at G_K|decl|stokesDualityCertificate_galK
ASK BLOCK|determinant at G_K|decl|affineDeterminant_galK
ASK BLOCK|scalar at G_K|decl|scalarHilbert_galK
CAND BLOCK|M0 a h|decl|mWordCertificate
CAND BLOCK|Mpc a r p q|decl|mpcWordCertificate
CAND BLOCK|N0 a h|decl|sqrtNegTwoWordCertificate
CAND BLOCK|Npc a r h q|decl|genCertNpcWordCertificate
CAND BLOCK|L h|decl|lCand_wordCertificateCanonical
TABLE
)

# ----------------------------------------------------------------------------
# Resolution: short name -> file, module, fully-qualified name.
# The namespace stack is reconstructed by tracking namespace/section open and
# close, so nested namespaces resolve correctly and no namespace is written
# down anywhere in this file.
# ----------------------------------------------------------------------------
NSAWK=$(cat <<'AWKEOF'
BEGIN { top = 0 }
{
  if (NR == TARGETLINE) {
    pfx = ""
    for (i = 1; i <= top; i++) if (kind[i] == "ns") pfx = pfx stack[i] "."
    print pfx NAME
    exit
  }
}
/^namespace[ \t]+[A-Za-z_]/ { top++; stack[top] = $2; kind[top] = "ns"; next }
/^(noncomputable[ \t]+)?section([ \t]+[A-Za-z_][A-Za-z0-9_.]*)?[ \t]*$/ {
  n = ($1 == "noncomputable") ? $3 : $2
  top++; stack[top] = (n == "" ? "<anon>" : n); kind[top] = "sec"; next
}
/^end([ \t]+[A-Za-z_][A-Za-z0-9_.]*)?[ \t]*$/ {
  n = $2
  if (n == "") { if (top > 0) top-- }
  else { while (top > 0 && stack[top] != n) top--; if (top > 0) top-- }
  next
}
AWKEOF
)

resolve() {  # $1 = short name; echoes "module<TAB>fullname" or nothing
  local short=$1 hit file line full mod
  hit=$(grep -rn -m1 \
    "^\(theorem\|lemma\|def\|abbrev\|structure\|noncomputable def\|opaque\)[ ]$short\b" \
    "$WT/GQ2" --include='*.lean' 2>/dev/null | head -1)
  [ -z "$hit" ] && return 0
  file=${hit%%:*}
  line=${hit#*:}; line=${line%%:*}
  full=$(awk -v TARGETLINE="$line" -v NAME="$short" "$NSAWK" "$file")
  mod=${file#"$WT"/}
  mod=${mod%.lean}
  mod=${mod//\//.}
  printf '%s\t%s\n' "$mod" "$full"
}

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# Resolve every row once into the probe's request list.
declare -a REQ=()
while IFS='|' read -r grp lab kind short; do
  [ -z "${grp:-}" ] && continue
  r=$(resolve "$short")
  if [ -z "$r" ]; then
    REQ+=("$grp|$lab|$kind|$short|-|-")
  else
    REQ+=("$grp|$lab|$kind|$short|${r%%$'\t'*}|${r#*$'\t'}")
  fi
done <<< "$ROWS"

# EVERY module under GQ2/, from the filesystem, for the registration scan.  Not
# the rows' modules: the point of the scan is to catch a module NO row reaches,
# so deriving its input from the rows would defeat it.
find "$WT/GQ2" -name '*.lean' |
  sed -e "s|^$WT/||" -e 's|\.lean$||' | tr '/' '.' | sort > "$TMP/allmods"

# ----------------------------------------------------------------------------
# THE PROBE.  Types, explicit binders, axiom censuses, producer scans and the
# registration check, all in ONE file, all against the UMBRELLA environment.
#
# `import GQ2` and nothing else.  This is structural, not cosmetic.  A `prod`
# scan reads the ENVIRONMENT; while the probe imported the rows' own modules,
# every producer count was a function of which modules the rows happened to
# reach, so a module reached by no row was invisible and the count printed
# silently low.  That fired on wave 84 (MpcPivShift) and again on wave 85
# (three counts at once).  Importing the umbrella makes the environment
# exactly what an `import GQ2` consumer sees, so the only producer this board
# can now miss is one in a module the umbrella does not import -- which is
# precisely what the REGISTRATION section flags, in the same environment.
#
# Consequence to read correctly: a row whose declaration lives OUTSIDE the
# umbrella now reports MISSING rather than EXISTS.  That is the intended
# reading (no `import GQ2` consumer can use it either), and the row prints the
# registration verdict for its module alongside so the two are never confused.
# ----------------------------------------------------------------------------
{
  echo 'import GQ2'
  cat <<'LEAN'
open Lean Elab Command Meta

partial def sbStrip : Expr → Expr
  | .forallE _ _ b _ => sbStrip b
  | e => e

def sbFlat (s : String) : String :=
  " ".intercalate ((s.replace "\n" " ").splitOn " " |>.filter (· ≠ ""))

/-- The head symbol of a binder type: what KIND of thing the caller must supply.
Never unfolds, so a clause abbreviation reports under its own name. -/
def sbHead (e : Expr) : String :=
  match e with
  | .forallE .. => "(function)"
  | _ => match e.getAppFn with
         | .const c _ => c.getString!
         | .sort _ => "Sort"
         | _ => "?"

/-- The EXPLICIT binders of `n`, i.e. what a caller must supply: head symbols
(the readable column) paired with the full pretty-printed types (`--raw`). -/
def sbExplicit (n : Name) : MetaM (Array String × Array String) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut heads : Array String := #[]
    let mut full : Array String := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo == .default then
        heads := heads.push (sbHead d.type)
        full := full.push (sbFlat (toString (← ppExpr d.type)))
    return (heads, full)

def sbStd : List Name := [`propext, `Classical.choice, `Quot.sound]

def sbAxioms (n : Name) : CoreM String := do
  let ax ← Lean.collectAxioms n
  let extra := ax.toList.filter (fun a => !(sbStd.contains a))
  let base := if ax.toList.any (fun a => sbStd.contains a) then "std-3" else "none"
  if extra.isEmpty then return base
  return base ++ " + " ++ ", ".intercalate (extra.map (fun a => a.getString!))

def sbRender (tag : String) (n : Name) : CommandElabM Unit := do
  if !(← getEnv).contains n then
    IO.println s!"SB|{tag}|MISSING||||"
    return
  let (heads, full) ← liftTermElabM <| sbExplicit n
  let ax ← liftCoreM <| sbAxioms n
  IO.println s!"SB|{tag}|EXISTS|{heads.size}|{", ".intercalate heads.toList}\
|{ax}|{" ;; ".intercalate full.toList}"

def sbProducers (env : Environment) (target : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n ci =>
    if n.getRoot != `GQ2 || n.isInternalDetail then acc else
    match (sbStrip ci.type).getAppFn with
    | .const t _ => if t == target then acc.push n else acc
    | _ => acc
LEAN
  echo 'run_cmd do'
  echo '  let env ← getEnv'
  i=0
  for rec in "${REQ[@]}"; do
    i=$((i + 1))
    kind=$(echo "$rec" | cut -d'|' -f3)
    full=$(echo "$rec" | cut -d'|' -f6)
    if [ "$full" = "-" ]; then
      echo "  IO.println \"SB|$i|UNRESOLVED|||||\""
    elif [ "$kind" = "prod" ]; then
      cat <<PROD
  if !env.contains \`$full then
    IO.println "SB|$i|MISSING|||||"
  else
    let ps := sbProducers env \`$full
    IO.println s!"SB|$i|EXISTS|{ps.size}|producers|||"
    for p in ps.qsort (fun a b => a.toString < b.toString) do
      sbRender s!"$i.{p}" p
PROD
    else
      echo "  sbRender \"$i\" \`$full"
    fi
  done
  # Registration, in the same environment: a module NOT in `import GQ2`'s
  # transitive closure is a module no consumer can see.  Every module under
  # GQ2/ is checked, as one string membership pass -- emitting a Lean
  # statement per module instead blows the elaborator's heartbeat limit at
  # this repository's size, which is how this was first written and why it
  # is not written that way.
  echo '  let sbPresent := env.header.moduleNames.map (·.toString)'
  printf '  let sbAll := "'
  tr '\n' ' ' < "$TMP/allmods"
  printf '"\n'
  cat <<'REG'
  let sbMods := (sbAll.splitOn " ").filter (· ≠ "")
  for m in sbMods do
    if !sbPresent.contains m then IO.println s!"OUTSIDE|{m}"
  IO.println s!"SCANNED|{sbMods.length}"
REG
} > "$TMP/probe.lean"

bash "$MIRROR" check "$TMP/probe.lean" > "$TMP/out" 2> "$TMP/err"
RC=$?

if [ "$RAW" = "1" ]; then
  cat "$TMP/out"
  exit 0
fi

# ----------------------------------------------------------------------------
# Report.
# ----------------------------------------------------------------------------
HEAD=$(cd "$WT" && git log -1 --format='%h %ad' --date=short 2>/dev/null)
BR=$(cd "$WT" && git branch --show-current 2>/dev/null)

echo "======================================================================="
echo " GQ2 DYADIC CAMPAIGN SCOREBOARD"
echo " tree $HEAD   branch $BR   generated $(date '+%Y-%m-%d %H:%M')"
echo " every EXISTS / binder / axiom line below was elaborated by this run"
echo "======================================================================="

if [ "$RC" != "0" ]; then
  echo
  echo "!! the probe did not elaborate; every row below is UNVERIFIED"
  sed -n '1,20p' "$TMP/err"
fi

lastgrp=""
i=0
for rec in "${REQ[@]}"; do
  i=$((i + 1))
  grp=$(echo "$rec" | cut -d'|' -f1)
  lab=$(echo "$rec" | cut -d'|' -f2)
  kind=$(echo "$rec" | cut -d'|' -f3)
  short=$(echo "$rec" | cut -d'|' -f4)
  mod=$(echo "$rec" | cut -d'|' -f5)
  full=$(echo "$rec" | cut -d'|' -f6)
  if [ "$grp" != "$lastgrp" ]; then
    echo
    echo "## $grp"
    lastgrp=$grp
  fi
  line=$(grep -m1 "^SB|$i|" "$TMP/out" 2>/dev/null)
  if [ -z "$line" ]; then
    printf '  %-30s UNVERIFIED (probe produced no record)\n' "$lab"
    continue
  fi
  st=$(echo "$line" | cut -d'|' -f3)
  cnt=$(echo "$line" | cut -d'|' -f4)
  heads=$(echo "$line" | cut -d'|' -f5)
  ax=$(echo "$line" | cut -d'|' -f6)
  if [ "$st" != "EXISTS" ]; then
    # The probe sees only the umbrella, so a MISSING row is either a name that
    # is not in the tree or a name in a module the umbrella does not reach.
    # Print which, rather than leaving the reader to guess.
    if grep -qx "OUTSIDE|$mod" "$TMP/out" 2>/dev/null; then
      printf '  %-30s %s   [%s; its module %s is OUTSIDE the umbrella]\n' \
        "$lab" "$st" "$short" "$mod"
    else
      printf '  %-30s %s   [%s]\n' "$lab" "$st" "$short"
    fi
    continue
  fi
  if [ "$kind" = "prod" ]; then
    printf '  %-30s producers: %s   [%s]\n' "$lab" "$cnt" "$short"
    grep "^SB|$i\." "$TMP/out" 2>/dev/null |
      while IFS='|' read -r _ tag _ c h a _; do
        printf '      %s\n' "${tag#*.}"
        if [ "$c" = "0" ]; then
          printf '        carries NOTHING            axioms: %s\n' "$a"
        else
          printf '        carries %-2s : %s\n' "$c" "$h"
          printf '        axioms     : %s\n' "$a"
        fi
      done
  else
    printf '  %-30s EXISTS   %s\n' "$lab" "$full"
    if [ "$cnt" = "0" ]; then
      printf '      carries NOTHING (no explicit binder)\n'
    else
      printf '      carries %-2s : %s\n' "$cnt" "$heads"
    fi
    printf '      axioms     : %s\n' "$ax"
  fi
done

echo
echo "## REGISTRATION (EVERY module under GQ2/, against \`import GQ2\`)"
if [ "$RC" != "0" ]; then
  echo "  UNVERIFIED (the probe did not elaborate)"
  sed -n '1,10p' "$TMP/err"
else
  SCANNED=$(grep -m1 '^SCANNED|' "$TMP/out" | cut -d'|' -f2)
  printf '  modules on disk under GQ2/   %s\n' "${SCANNED:-UNVERIFIED}"
  n=0
  while IFS='|' read -r _ m; do
    [ -z "${m:-}" ] && continue
    n=$((n + 1))
    # A module that itself does `import GQ2` CANNOT be registered: that is a
    # cycle, not an oversight.  Derived by reading the file, not asserted here.
    f=$WT/$(echo "$m" | tr '.' '/').lean
    if [ -f "$f" ] && grep -qx 'import GQ2' "$f"; then
      printf '  OUTSIDE the umbrella         %s   (it imports GQ2 itself:\n' "$m"
      printf '%s\n' "                               registering it would cycle)"
    else
      printf '  OUTSIDE the umbrella         %s\n' "$m"
    fi
  done < <(grep '^OUTSIDE|' "$TMP/out")
  [ "$n" = "0" ] && echo "  OUTSIDE the umbrella         none"
  echo "  (outside = not in \`import GQ2\`'s transitive closure, so invisible"
  echo "   to every consumer AND to the producer scans above.  This is now the"
  echo "   board's only blind spot, and this line is the check for it.)"
fi

echo
echo "## OWNER ITEMS"
# See "THE OWNER-ITEMS CONTRACT" in the header for what this section reads and
# why it reads two files instead of one.  Neither number below is verified; both
# are counted off prose, and the row exists to make them face each other.

# ---- the authority: the owner memo, newest status block first ----
MEMO=$(cd "$WT" && ls docs/dyadic/owner-items-*.md 2>/dev/null | sort | tail -1)
MEMON=$(cd "$WT" && ls docs/dyadic/owner-items-*.md 2>/dev/null | wc -l | tr -d ' ')
MCOUNT=""
MBLOCK=""
if [ -n "$MEMO" ] && [ -f "$WT/$MEMO" ]; then
  MBLOCK=$(grep -m1 '^## Status at wave ' "$WT/$MEMO" 2>/dev/null)
  if [ -n "$MBLOCK" ]; then
    # The first "N items await you" phrase at or after that heading.  The memo
    # writes the count as an English word, so it is mapped, not parsed as a
    # number; an unmapped word prints as UNVERIFIED rather than as a guess.
    MWORD=$(awk '/^## Status at wave /{f++} f==1 && /items await you/ {
        for (i = 1; i <= NF; i++)
          if ($i ~ /^\*\*[A-Za-z]+$/) { print tolower(substr($i, 3)); exit }
        exit
      }' "$WT/$MEMO")
    MCOUNT=$(awk -v w="$MWORD" 'BEGIN {
        n = split("zero one two three four five six seven eight nine ten eleven twelve \
thirteen fourteen fifteen sixteen seventeen eighteen nineteen twenty", a, /[ \t\n]+/)
        for (i = 1; i <= n; i++) if (a[i] == w) { print i - 1; exit }
      }')
  fi
fi
if [ -z "$MEMO" ]; then
  echo "  owner memo (AUTHORITY)   NOT FOUND (docs/dyadic/owner-items-*.md)"
else
  printf '  owner memo (AUTHORITY)   %s\n' "$MEMO"
  [ "$MEMON" != "1" ] &&
    printf '    !! %s memos match the glob; the newest by name was read\n' "$MEMON"
  if [ -z "$MBLOCK" ]; then
    echo "    latest status block    NOT FOUND (no '## Status at wave N' heading)"
  else
    printf '    latest status block    %s\n' "$MBLOCK"
    if [ -n "$MCOUNT" ]; then
      printf '    count it asserts       %s   (PROSE, off "N items await you")\n' "$MCOUNT"
    else
      echo "    count it asserts       UNVERIFIED (no 'N items await you' phrase"
      echo "                           in that block, or its number word is unmapped)"
    fi
  fi
fi

# ---- the lane artifact: the latest house note ----
NOTE=$(cd "$WT" && ls docs/dyadic/w*-house-note.md 2>/dev/null |
  sed 's/.*\/w\([0-9]*\)-house-note.md/\1 &/' | sort -n | tail -1 | cut -d' ' -f2)
NCOUNT=""
NHEAD=""
if [ -n "$NOTE" ] && [ -f "$WT/$NOTE" ]; then
  # Deliberately TOLERANT: case-insensitive, an optional section number, an
  # optional leading "The", an optional trailing ": ..." gloss.  The strict
  # match this replaces scored zero on six of the last ten house notes and said
  # so as "0" rather than as "not found"; see the header.
  NHEAD=$(grep -n -m1 -E '^#+[ \t]+([0-9]+(\.[0-9]+)*[ \t]+)?(The[ \t]+)?[Oo][Ww][Nn][Ee][Rr][ \t]+[Ii][Tt][Ee][Mm][Ss]' \
    "$WT/$NOTE" 2>/dev/null)
  if [ -n "$NHEAD" ]; then
    NCOUNT=$(awk -v start="${NHEAD%%:*}" 'NR > start && /^#/ {exit}
      NR > start && /^[0-9]+\./ {c++} END {print c + 0}' "$WT/$NOTE")
  fi
fi
if [ -z "$NOTE" ]; then
  echo "  latest house note        NOT FOUND (docs/dyadic/w*-house-note.md)"
else
  printf '  latest house note        %s\n' "$NOTE"
  if [ -z "$NHEAD" ]; then
    echo "    owner-items heading    NOT FOUND in it (so no count; this is the"
    echo "                           signal, not a zero)"
  else
    printf '    owner-items heading    line %s: %s\n' "${NHEAD%%:*}" "${NHEAD#*:}"
    printf '    numbered items under   %s\n' "$NCOUNT"
  fi
fi

# ---- the comparison, which is the whole point of printing both ----
if [ -n "$MCOUNT" ] && [ -n "$NCOUNT" ]; then
  if [ "$MCOUNT" = "$NCOUNT" ]; then
    printf '  memo and note AGREE      %s\n' "$MCOUNT"
  else
    printf '  !! memo and note DISAGREE  memo %s, note %s.  The memo is the\n' \
      "$MCOUNT" "$NCOUNT"
    echo "                             owner's record and the note is frozen at"
    echo "                             its own close, so a note item discharged"
    echo "                             after that close still counts in the note."
    echo "                             Read both; this board decides neither."
  fi
else
  echo "  memo vs note             NOT COMPARED (one side is missing above)"
fi
echo "  status of each item      UNVERIFIED (prose; not machine-checkable)"

echo
echo "## THE A6 FREEZE (GQ2/Roe/)"
ROECOMMIT=$(cd "$WT" && git log -1 --format='%h %ad  %s' --date=short -- GQ2/Roe/ 2>/dev/null)
ROESINCE=$(cd "$WT" && git log --format='%H' -- GQ2/Roe/ 2>/dev/null | head -1)
NOTESINCE=$(cd "$WT" && git log --diff-filter=A --format='%H' \
  "$ROESINCE"..HEAD -- 'docs/dyadic/w*-house-note.md' 2>/dev/null | wc -l | tr -d ' ')
printf '  last commit touching it  %s\n' "${ROECOMMIT:-none}"
printf '  house notes added since  %s\n' "$NOTESINCE"
echo "  review rounds frozen     UNVERIFIED (the campaign counts from the A6"
echo "                           adoption wave, which is not recorded in git)"

echo
echo "## WHAT THIS BOARD CANNOT SEE"
echo "  * whether a clause a row CARRIES is discharged somewhere else in the"
echo "    tree at the same instantiation: only the binder is machine-checked."
echo "  * whether a producer's conclusion is at the row's CANONICAL marking;"
echo "    \`GenAsmBranch\` does not pin \`nuP\` (GeneralAssembly.lean, W82-PIVOT)."
echo "  * STRENGTH.  The carries column counts binders, and fewer binders is"
echo "    not a weaker hypothesis: sqNuOrientedClearAtUnitPivot_of_pivotMoves"
echo "    carries 2 against _of_families' 3, and is the STRONGER ask (the whole"
echo "    unit-determinant pivot family, against two one-parameter ones)."
echo "  * producers in modules OUTSIDE THE UMBRELLA, and only those.  The probe"
echo "    imports \`GQ2\` and nothing else, so a \`prod\` scan sees every module"
echo "    in that import's transitive closure, whether or not any row names a"
echo "    declaration in it.  A module OUTSIDE the closure is still invisible"
echo "    to the scan -- but it is invisible to every consumer too, and the"
echo "    REGISTRATION section above enumerates the whole of GQ2/ from disk,"
echo "    so it names any such module rather than leaving it unremarked."
echo "    HISTORY, because this was the board's one standing defect and the"
echo "    fix is structural (W86-HOUSE), not another row: while the probe"
echo "    imported the ROWS' modules, the counts were a function of which"
echo "    modules the rows happened to reach.  (1) W84-HOUSE found the board"
echo "    printing \`producers: 0\` for MpcPivShift while wave 83's"
echo "    MpcOrb.mpcOrb_shift_of_marking produced it.  (2) W85-HOUSE found it"
echo "    printing 1 for MpcPivShift against a true 4, 3 for"
echo "    SqNuOrientedClearAtUnitPivot against a true 6, and 14 for"
echo "    SqMarkedForwardSupply against a true 16, because wave 84's own three"
echo "    modules were reached by no row.  Both were patched by adding rows;"
echo "    the patch does not generalise and wave 85 landed three more modules,"
echo "    so the import set is now the umbrella.  A row is still the way to"
echo "    put a NAMED declaration on the board; it is no longer what makes a"
echo "    module's producers countable."
echo "  * producers stated in a shape other than the head.  \`prod\` matches the"
echo "    conclusion's HEAD constant, so a theorem concluding \`A <-> P ...\`,"
echo "    \`Nonempty (P ...)\` or a structure field of type \`P ...\` is NOT"
echo "    counted.  mpcOrb_shift_iff_marking is such a statement.  Read"
echo "    \`producers: 0\` as \"nothing concludes it directly\", never as"
echo "    \"nothing in the tree bears on it\"."
echo "  * prose.  Every headline, table and inventory in the tree and in"
echo "    docs/dyadic/ is outside this tool and stales on its own."
