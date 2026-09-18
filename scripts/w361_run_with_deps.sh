#!/usr/bin/env bash
set -euo pipefail
GQ2_COMMAND_PACKAGE=/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages
GQ2_COMMAND_TC=/Users/roed/.elan/toolchains/leanprover--lean4---v4.31.0-rc2
GQ2_COMMAND_PATH=/Users/roed/claude/cla/work/main-build-cache/lib/lean
for GQ2_COMMAND_DEP in "$GQ2_COMMAND_PACKAGE"/*/.lake/build/lib/lean; do
  GQ2_COMMAND_PATH="$GQ2_COMMAND_PATH:$GQ2_COMMAND_DEP"
done
export LEAN_PATH="$GQ2_COMMAND_PATH:$GQ2_COMMAND_TC/lib/lean"
cd /Users/roed/claude/cla/work/gq2-dyadic-campaign
exec "$@"
