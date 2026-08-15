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
#   `mirror.sh check` on generated probe files and runs NO `lake` command.
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
#          against a stale memory of the tree.
#
# WHAT THIS SCRIPT WILL NOT DO
#
#   It carries NO hand-maintained facts: no clause lists, no axiom tags, no
#   "open/closed" verdicts, no line numbers, no counts.  Where a fact cannot
#   be machine-checked cheaply it prints UNVERIFIED and, next to it, the
#   nearest thing that CAN be checked.  Do not "fix" an UNVERIFIED by writing
#   the answer in here; either make it checkable or leave it.
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
FROZEN ROWS|v-10 residual move|prod|MpcPivShift
ODD SEAM|the seam Prop|decl|SqMarkedForwardSupply
ODD SEAM|every seam producer|prod|SqMarkedForwardSupply
ODD SEAM|seam = marked-core cert|decl|oddId_supply_iff_certificate
ODD SEAM|seam = one cup-adapted frame|decl|oddSeam_supply_iff_cupAdaptedFrame
ODD SEAM|seam = the full marking|decl|oddSeam_supply_iff_fullMarking
ODD SEAM|halved relator clause|prod|SqCupAdaptedFrameRelator
ODD SEAM|frame presentation clause|prod|SqCupAdaptedFramePresentation
ODD SEAM|model clearing clause|prod|SqNuOrientedClearAtUnitPivot
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

# Resolve every row once; build the import set and the probe's request list.
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

{
  for rec in "${REQ[@]}"; do
    m=$(echo "$rec" | cut -d'|' -f5)
    [ "$m" != "-" ] && echo "$m"
  done
} | sort -u > "$TMP/imports"

# ----------------------------------------------------------------------------
# Probe A: types, explicit binders, axiom censuses, producer scans.
# ----------------------------------------------------------------------------
{
  while read -r m; do echo "import $m"; done < "$TMP/imports"
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
} > "$TMP/probeA.lean"

# ----------------------------------------------------------------------------
# Probe B: registration.  Imports ONLY the umbrella, so a name it cannot see
# is a name no `import GQ2` consumer can see -- i.e. an unregistered module.
# ----------------------------------------------------------------------------
{
  echo 'import GQ2'
  echo 'open Lean Elab Command'
  echo 'run_cmd do'
  echo '  let env ← getEnv'
  while read -r m; do
    echo "  IO.println s!\"REGMOD|$m|{env.header.moduleNames.contains \`$m}\""
  done < "$TMP/imports"
} > "$TMP/probeB.lean"

bash "$MIRROR" check "$TMP/probeA.lean" > "$TMP/outA" 2> "$TMP/errA"
RCA=$?
bash "$MIRROR" check "$TMP/probeB.lean" > "$TMP/outB" 2> "$TMP/errB"
RCB=$?

if [ "$RAW" = "1" ]; then
  cat "$TMP/outA" "$TMP/outB"
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

if [ "$RCA" != "0" ]; then
  echo
  echo "!! probe A did not elaborate; every row below is UNVERIFIED"
  sed -n '1,20p' "$TMP/errA"
fi

lastgrp=""
i=0
for rec in "${REQ[@]}"; do
  i=$((i + 1))
  grp=$(echo "$rec" | cut -d'|' -f1)
  lab=$(echo "$rec" | cut -d'|' -f2)
  kind=$(echo "$rec" | cut -d'|' -f3)
  short=$(echo "$rec" | cut -d'|' -f4)
  full=$(echo "$rec" | cut -d'|' -f6)
  if [ "$grp" != "$lastgrp" ]; then
    echo
    echo "## $grp"
    lastgrp=$grp
  fi
  line=$(grep -m1 "^SB|$i|" "$TMP/outA" 2>/dev/null)
  if [ -z "$line" ]; then
    printf '  %-30s UNVERIFIED (probe produced no record)\n' "$lab"
    continue
  fi
  st=$(echo "$line" | cut -d'|' -f3)
  cnt=$(echo "$line" | cut -d'|' -f4)
  heads=$(echo "$line" | cut -d'|' -f5)
  ax=$(echo "$line" | cut -d'|' -f6)
  if [ "$st" != "EXISTS" ]; then
    printf '  %-30s %s   [%s]\n' "$lab" "$st" "$short"
    continue
  fi
  if [ "$kind" = "prod" ]; then
    printf '  %-30s producers: %s   [%s]\n' "$lab" "$cnt" "$short"
    grep "^SB|$i\." "$TMP/outA" 2>/dev/null |
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
echo "## REGISTRATION (visible to an \`import GQ2\` consumer)"
if [ "$RCB" != "0" ]; then
  echo "  UNVERIFIED (probe B did not elaborate)"
  sed -n '1,10p' "$TMP/errB"
else
  while IFS='|' read -r _ m v; do
    [ -z "${m:-}" ] && continue
    if [ "$v" = "true" ]; then
      printf '  %-58s registered\n' "$m"
    else
      printf '  %-58s NOT REGISTERED\n' "$m"
    fi
  done < <(grep '^REGMOD|' "$TMP/outB")
fi

echo
echo "## OWNER ITEMS"
NOTE=$(cd "$WT" && ls docs/dyadic/w*-house-note.md 2>/dev/null |
  sed 's/.*\/w\([0-9]*\)-house-note.md/\1 &/' | sort -n | tail -1 | cut -d' ' -f2)
if [ -n "$NOTE" ] && [ -f "$WT/$NOTE" ]; then
  N=$(awk '/^#+ +Owner items/{f=1;next} f&&/^#/{exit} f&&/^[0-9]+\./{c++} END{print c+0}' \
    "$WT/$NOTE")
  printf '  latest house note        %s\n' "$NOTE"
  printf '  numbered items in it     %s\n' "$N"
  echo "  status of each           UNVERIFIED (prose; not machine-checkable)"
else
  echo "  UNVERIFIED (no house note found)"
fi

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
echo "  * producers in modules no row imports.  A \`prod\` scan reads the"
echo "    ENVIRONMENT, so it sees exactly the modules the rows above pull in."
echo "    A new module with a new producer is invisible until some row names a"
echo "    declaration in it.  This is the one way the board can be stale."
echo "  * prose.  Every headline, table and inventory in the tree and in"
echo "    docs/dyadic/ is outside this tool and stales on its own."
