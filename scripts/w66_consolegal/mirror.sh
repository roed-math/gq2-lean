#!/bin/bash
# W66-CONSOLEGAL lane mirror harness (copy of scripts/w65_six/mirror.sh, WT retargeted).
set -euo pipefail

WT=/Users/roed/claude/cla/worktrees/w66-consolegal
SRC=$WT/.lake/build/lib/lean
MIR=/private/tmp/claude-501/-Users-roed-claude-cla-work-gq2-dyadic-campaign/9d1ec2b5-716b-4181-831b-d42c1cca6fe1/scratchpad/w66consolegal-mirror
TC=/Users/roed/.elan/toolchains/leanprover--lean4---v4.31.0-rc2
PKG=/Users/roed/claude/gq2-dyadic/.lake/packages

LP="$PKG/Cli/.lake/build/lib/lean:$PKG/batteries/.lake/build/lib/lean"
LP="$LP:$PKG/Qq/.lake/build/lib/lean:$PKG/aesop/.lake/build/lib/lean"
LP="$LP:$PKG/proofwidgets/.lake/build/lib/lean:$PKG/importGraph/.lake/build/lib/lean"
LP="$LP:$PKG/LeanSearchClient/.lake/build/lib/lean:$PKG/plausible/.lake/build/lib/lean"
LP="$LP:$PKG/lean-atlas/.lake/build/lib/lean:$PKG/mathlib/.lake/build/lib/lean"
LP="$LP:$MIR:$TC/lib/lean"

FLAGS="-DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true"

case "${1:-}" in
  sweep)
    rm -rf "$MIR"; mkdir -p "$MIR"
    (cd "$SRC" && find . -type d) | sed "s|^\./*|$MIR/|" | tr '\n' '\0' | xargs -0 mkdir -p
    n=0
    while IFS= read -r f; do
      rel=${f#./}; ln -sf "$SRC/$rel" "$MIR/$rel"; n=$((n + 1))
    done < <(cd "$SRC" && find . -type f)
    echo "swept $n artifacts into $MIR"
    ;;
  gen)
    mod=$2; path=${mod//.//}
    mkdir -p "$MIR/$(dirname "$path")"
    rm -f "$MIR/$path.olean" "$MIR/$path.ilean"
    cd "$WT"
    LEAN_PATH="$LP" "$TC/bin/lean" $FLAGS -o "$MIR/$path.olean" -i "$MIR/$path.ilean" "$WT/$path.lean"
    echo "generated $MIR/$path.olean"
    ;;
  check)
    cd "$WT"
    LEAN_PATH="$LP" "$TC/bin/lean" $FLAGS "$2"
    echo "OK: $2"
    ;;
  *) echo "usage: mirror.sh {sweep|gen <Module.Name>|check <file.lean>}" >&2; exit 2 ;;
esac
