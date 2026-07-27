#!/usr/bin/env bash
# Regenerate docs/axiom-closure.md — the per-axiom statement-closure report.
#
# Needs a built GQ2.Foundations.Axioms (run `lake build GQ2.Foundations.Axioms` first if the
# probe fails to elaborate).  See scripts/AxiomClosureProbe.lean for the dependency model.
set -euo pipefail
cd "$(dirname "$0")/.."

tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT
lake env lean scripts/AxiomClosureProbe.lean > "$tmp"
python3 scripts/axiom_closure.py "$tmp" > docs/axiom-closure.md
echo "wrote docs/axiom-closure.md"
