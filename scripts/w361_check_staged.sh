#!/usr/bin/env bash
# Explicit opt-in checks for the additive W361 research artifacts.
# This does not replace check_dyadic.sh or activate a new release gate.
# It checks existing files; it never regenerates them or edits frozen artifacts.
# See w361_lean_runner.sh for the package/toolchain/artifact-root contract.
set -euo pipefail
GQ2_W361_CHECK_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$GQ2_W361_CHECK_ROOT"

python3 scripts/w361_general_word_tex.py self-test
python3 scripts/w361_general_fox_tex.py self-test
python3 scripts/w361_general_phase_tex.py self-test
python3 scripts/w361_general_cover_tex.py self-test
python3 scripts/w361_certificate_packet_test.py
python3 scripts/w361_verify_fresh_test.py
python3 scripts/w361_general_ln_word_tex.py self-test

bash scripts/w361_lean_runner.sh scripts/w361_general_axiom_audit.lean
bash scripts/w361_lean_runner.sh scripts/w361_artifact_axiom_audit.lean

python3 scripts/w361_general_word_tex.py check generated/general-template-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w361_general_ln_word_tex.py check generated/general-ln-template-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w361_general_fox_tex.py check generated/general-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w361_general_phase_tex.py check generated/general-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w361_general_cover_tex.py check generated/general-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w361_certificate_packet.py check generated/general-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh

printf '%s\n' 'W361_STAGED_CHECK_PASS (not owner approval or a transitive fresh-build certificate)'
