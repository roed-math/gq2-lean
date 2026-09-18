#!/usr/bin/env bash
# Explicit opt-in checks for the STAGED W366 item-8 exporter: ledger item 8's normal-form
# half, which W363-PUB2 left named_but_unbound, plus the item-8 OVERLAYS that carry both
# halves beside the six W362 packets.
# It does not replace check_dyadic.sh, does not activate a release gate, and does not modify
# w361_check_staged.sh, w362_check_ln_staged.sh or w363_check_ln_staged.sh: it runs the W363
# script unchanged (which runs the W362 script unchanged, which runs the W361 script
# unchanged) and then adds the new checks, exactly as W363 extended W362. Folding these steps
# into one script is an owner decision.
# It checks existing files; it never regenerates them or edits frozen artifacts, and it never
# writes to a W362 packet: the overlay check PINS each packet hash and fails if one stops
# reproducing. See w361_lean_runner.sh for the package/toolchain/artifact-root contract.
set -euo pipefail
GQ2_W366_CHECK_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$GQ2_W366_CHECK_ROOT"

bash scripts/w363_check_ln_staged.sh

python3 scripts/w366_ln_gauss_tex.py self-test
python3 scripts/w366_ln_item8_overlay.py self-test

python3 scripts/w366_ln_gauss_tex.py check generated/general-ln-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w366_ln_item8_overlay.py check generated/general-ln-certificate-staged

printf '%s\n' 'W366_LN_STAGED_CHECK_PASS (staged proposals only: not owner approval, not a manifest entry, not a gate)'
