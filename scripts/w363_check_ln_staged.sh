#!/usr/bin/env bash
# Explicit opt-in checks for the STAGED W363 L/N certificate exporters.
# It does not replace check_dyadic.sh, does not activate a release gate, and does not
# modify w361_check_staged.sh or w362_check_ln_staged.sh: it runs the W362 script
# unchanged (which itself runs the W361 script unchanged) and then adds the new L/N
# exporter checks. Folding these steps into one script is an owner decision.
# It checks existing files; it never regenerates them or edits frozen artifacts.
# See w361_lean_runner.sh for the package/toolchain/artifact-root contract.
set -euo pipefail
GQ2_W363_CHECK_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$GQ2_W363_CHECK_ROOT"

bash scripts/w362_check_ln_staged.sh

python3 scripts/w363_ln_input_tex.py self-test
python3 scripts/w363_ln_stokes_tex.py self-test
python3 scripts/w363_ln_hessian_tex.py self-test

python3 scripts/w363_ln_input_tex.py check generated/general-ln-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w363_ln_stokes_tex.py check generated/general-ln-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w363_ln_hessian_tex.py check generated/general-ln-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh

printf '%s\n' 'W363_LN_STAGED_CHECK_PASS (staged proposals only: not owner approval, not a manifest entry, not a gate)'
