#!/usr/bin/env bash
# Explicit opt-in checks for the STAGED W362 L/N certificate packets.
# It does not replace check_dyadic.sh, does not activate a release gate, and does
# not modify w361_check_staged.sh: it runs that script unchanged and then adds the
# new L/N checks. Folding these two steps into the W361 script is an owner decision.
# It checks existing files; it never regenerates them or edits frozen artifacts.
# See w361_lean_runner.sh for the package/toolchain/artifact-root contract.
set -euo pipefail
GQ2_W362_CHECK_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$GQ2_W362_CHECK_ROOT"

bash scripts/w361_check_staged.sh

python3 scripts/w362_ln_fox_tex.py self-test
python3 scripts/w362_ln_certificate_packet.py self-test

python3 scripts/w362_ln_fox_tex.py check generated/general-ln-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w362_ln_certificate_packet.py check generated/general-ln-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh

printf '%s\n' 'W362_LN_STAGED_CHECK_PASS (staged proposals only: not owner approval, not a manifest entry, not a gate)'
