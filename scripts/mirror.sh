#!/bin/bash
# ============================================================================
# THE FULL-MIRROR HARNESS -- standing verification protocol for campaign lanes.
#
# Adopted (W66-CONSOLEGAL) from scripts/w65_six/mirror.sh, which is left in
# place as the wave-65 lane's record.  This copy is the one to use going
# forward: it derives its worktree, toolchain and mirror location instead of
# hardcoding one lane's, so it works unchanged from any worktree.
#
# ----------------------------------------------------------------------------
# WHY THIS EXISTS
#
# `lake env lean` appends its injected LEAN_PATH AFTER its own entries, so
# shadowing the shared olean cache that way silently fails and checks come out
# FALSE-CLEAN -- the check passes while reading the STALE cached olean of the
# very module you just edited.  Lean does not fall through LEAN_PATH roots
# either, so the shadow dir must be a COMPLETE symlink mirror of the cache --
# every artifact, not only `.olean` -- with the raw `lean` binary invoked
# directly.  That is what `sweep` builds and what `gen`/`check` run against.
#
# ----------------------------------------------------------------------------
# USAGE
#
#   scripts/mirror.sh sweep             rebuild the symlink mirror from the
#                                       shared olean cache.  Run once at lane
#                                       start, and again on every cache advance.
#
#   scripts/mirror.sh gen <Module.Name> compile <Module.Name> INTO the mirror
#                                       (DOTTED module name, e.g.
#                                       GQ2.Dyadic.SqCore.GradedFiveFrame).
#                                       Removes the stale mirror symlink first,
#                                       so the lane's own olean wins.  Also
#                                       typechecks, and prints any `#print
#                                       axioms` output.
#
#   scripts/mirror.sh check <file.lean> typecheck <file.lean> against the
#                                       mirror (PATH, not module name).
#                                       Read-only: writes no olean.
#
# ----------------------------------------------------------------------------
# ORDER MATTERS: RESWEEP FIRST, THEN REGENERATE
#
# `sweep` relinks every artifact from the shared cache, so a sweep run AFTER a
# lane's module has landed in that cache will CLOBBER the lane's fresh olean
# with the cache's older one.  The order on any cache advance is therefore:
#
#   1. sweep                    (relink everything from the advanced cache)
#   2. gen <each edited module> (regenerate this lane's oleans on top)
#   3. check <each dependent>   (re-elaborate what imports them)
#
# never gen-then-sweep.  For an EDITED module the same rule applies within a
# single lane: `gen` it again after any sweep, or importers will typecheck
# against the pre-edit olean and pass for the wrong reason.
#
# ----------------------------------------------------------------------------
# OVERRIDES (all optional; defaults are derived)
#
#   GQ2_WT    worktree root         default: the parent of this script's dir
#   GQ2_MIR   mirror directory      default: $TMPDIR-ish path keyed by worktree
#   GQ2_TC    toolchain root        default: read from $GQ2_WT/lean-toolchain
#   GQ2_PKG   lake packages dir     default: $GQ2_WT/.lake/packages
# ============================================================================
set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
WT=${GQ2_WT:-$(dirname "$HERE")}
SRC=$WT/.lake/build/lib/lean
PKG=${GQ2_PKG:-$WT/.lake/packages}

# Toolchain: `leanprover/lean4:v4.31.0-rc2` -> `leanprover--lean4---v4.31.0-rc2`.
# Derived rather than pinned so a toolchain bump does not silently check against
# the wrong `lean` binary (several toolchains are installed side by side).
if [ -n "${GQ2_TC:-}" ]; then
  TC=$GQ2_TC
else
  if [ ! -f "$WT/lean-toolchain" ]; then
    echo "mirror.sh: no $WT/lean-toolchain; set GQ2_TC" >&2
    exit 2
  fi
  tcname=$(tr -d '[:space:]' < "$WT/lean-toolchain")
  tcname=${tcname//\//--}
  tcname=${tcname//:/---}
  TC=$HOME/.elan/toolchains/$tcname
fi

MIR=${GQ2_MIR:-/private/tmp/claude-501/gq2-mirror-$(basename "$WT")}

for d in "$SRC" "$PKG" "$TC"; do
  if [ ! -d "$d" ]; then
    echo "mirror.sh: missing $d" >&2
    exit 2
  fi
done

LP="$PKG/Cli/.lake/build/lib/lean:$PKG/batteries/.lake/build/lib/lean"
LP="$LP:$PKG/Qq/.lake/build/lib/lean:$PKG/aesop/.lake/build/lib/lean"
LP="$LP:$PKG/proofwidgets/.lake/build/lib/lean:$PKG/importGraph/.lake/build/lib/lean"
LP="$LP:$PKG/LeanSearchClient/.lake/build/lib/lean:$PKG/plausible/.lake/build/lib/lean"
LP="$LP:$PKG/lean-atlas/.lake/build/lib/lean:$PKG/mathlib/.lake/build/lib/lean"
LP="$LP:$MIR:$TC/lib/lean"

# The verification flags of record.  Do not drop these: `autoImplicit` in
# particular turns a typo'd binder into a silently-generalised variable.
FLAGS="-DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true"

case "${1:-}" in
  sweep)
    rm -rf "$MIR"
    mkdir -p "$MIR"
    (cd "$SRC" && find . -type d) | sed "s|^\./*|$MIR/|" | tr '\n' '\0' | xargs -0 mkdir -p
    n=0
    while IFS= read -r f; do
      rel=${f#./}
      ln -sf "$SRC/$rel" "$MIR/$rel"
      n=$((n + 1))
    done < <(cd "$SRC" && find . -type f)
    echo "swept $n artifacts into $MIR"
    ;;
  gen)
    mod=${2:?usage: mirror.sh gen <Module.Name>}
    path=${mod//.//}
    if [ ! -f "$WT/$path.lean" ]; then
      echo "mirror.sh: no $WT/$path.lean (dotted MODULE name expected, not a path)" >&2
      exit 2
    fi
    mkdir -p "$MIR/$(dirname "$path")"
    rm -f "$MIR/$path.olean" "$MIR/$path.ilean"
    cd "$WT"
    LEAN_PATH="$LP" "$TC/bin/lean" $FLAGS \
      -o "$MIR/$path.olean" -i "$MIR/$path.ilean" "$WT/$path.lean"
    echo "generated $MIR/$path.olean"
    ;;
  check)
    file=${2:?usage: mirror.sh check <file.lean>}
    cd "$WT"
    LEAN_PATH="$LP" "$TC/bin/lean" $FLAGS "$file"
    echo "OK: $file"
    ;;
  *)
    echo "usage: mirror.sh {sweep|gen <Module.Name>|check <file.lean>}" >&2
    exit 2
    ;;
esac
