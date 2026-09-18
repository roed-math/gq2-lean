#!/usr/bin/env bash
# Direct Lean runner for the additive general-case checks. It neither invokes lake
# nor mutates a cache. Supply a source-only snapshot's lib/lean as ARTIFACTS when
# checking against an isolated fresh build rather than the shared campaign cache.
#
# GQ2_W361_PACKAGES   exact matching dependency packages directory (required when
#                    the worktree does not have its own .lake/packages)
# GQ2_W361_ARTIFACTS  complete local artifact root; defaults to .lake/build/lib/lean
# GQ2_W361_TOOLCHAIN toolchain root; defaults to the pinned lean-toolchain under elan
#
# Usage: bash scripts/w361_lean_runner.sh scripts/w361_general_axiom_audit.lean
#        python3 scripts/w361_general_word_tex.py check generated/general-template-staged \
#          --lean-runner scripts/w361_lean_runner.sh
set -euo pipefail

GQ2_W361_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
GQ2_W361_PACKAGES=${GQ2_W361_PACKAGES:-$GQ2_W361_ROOT/.lake/packages}
GQ2_W361_ARTIFACTS=${GQ2_W361_ARTIFACTS:-$GQ2_W361_ROOT/.lake/build/lib/lean}
GQ2_W361_TOOLCHAIN_PIN=$(tr -d '[:space:]' < "$GQ2_W361_ROOT/lean-toolchain")
GQ2_W361_EXPECTED_VERSION=${GQ2_W361_TOOLCHAIN_PIN#leanprover/lean4:v}
GQ2_W361_PIN=$GQ2_W361_TOOLCHAIN_PIN
GQ2_W361_PIN=${GQ2_W361_PIN//\//--}
GQ2_W361_PIN=${GQ2_W361_PIN//:/---}
GQ2_W361_TOOLCHAIN=${GQ2_W361_TOOLCHAIN:-$HOME/.elan/toolchains/$GQ2_W361_PIN}

for GQ2_W361_DIRECTORY in "$GQ2_W361_PACKAGES" "$GQ2_W361_ARTIFACTS" \
    "$GQ2_W361_TOOLCHAIN/lib/lean"; do
  if [ ! -d "$GQ2_W361_DIRECTORY" ]; then
    echo "w361 runner: missing directory $GQ2_W361_DIRECTORY" >&2
    exit 2
  fi
done
if [ ! -x "$GQ2_W361_TOOLCHAIN/bin/lean" ]; then
  echo "w361 runner: missing Lean executable" >&2
  exit 2
fi
GQ2_W361_VERSION=$("$GQ2_W361_TOOLCHAIN/bin/lean" --version)
case "$GQ2_W361_VERSION" in
  "Lean (version $GQ2_W361_EXPECTED_VERSION,"*) ;;
  *)
    echo "w361 runner: Lean version does not match $GQ2_W361_TOOLCHAIN_PIN" >&2
    exit 2
    ;;
esac
if ! cmp -s "$GQ2_W361_ROOT/lake-manifest.json" \
    "$GQ2_W361_PACKAGES/../../lake-manifest.json"; then
  echo "w361 runner: dependency manifest does not match this worktree" >&2
  exit 2
fi

GQ2_W361_PATH=$GQ2_W361_ARTIFACTS
GQ2_W361_DECLARED_PATHS=$(python3 - "$GQ2_W361_ROOT/lake-manifest.json" "$GQ2_W361_PACKAGES" <<'PY'
import json
from pathlib import Path
import re
import sys
manifest = json.loads(Path(sys.argv[1]).read_text())
for entry in manifest['packages']:
    name = entry['name'].removeprefix('«').removesuffix('»')
    if not re.fullmatch(r'[A-Za-z0-9_-]+', name):
        raise ValueError('Unexpected dependency package name')
    path = Path(sys.argv[2]) / name / '.lake/build/lib/lean'
    if path.is_dir():
        if (path / 'GQ2').exists() or (path / 'GQ2.olean').exists():
            raise ValueError('Dependency package contains local GQ2 artifacts')
        print(path)
PY
)
while IFS= read -r GQ2_W361_DEPENDENCY; do
  [ -n "$GQ2_W361_DEPENDENCY" ] || continue
  GQ2_W361_PATH="$GQ2_W361_PATH:$GQ2_W361_DEPENDENCY"
done <<< "$GQ2_W361_DECLARED_PATHS"
export LEAN_PATH="$GQ2_W361_PATH:$GQ2_W361_TOOLCHAIN/lib/lean"
cd "$GQ2_W361_ROOT"
exec "$GQ2_W361_TOOLCHAIN/bin/lean" -DautoImplicit=false \
  -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true "$@"
