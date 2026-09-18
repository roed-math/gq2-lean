# STAGED symbolic templates — not a frozen-manifest migration

These examples instantiate only the discrete tree-factory arguments. Their
two-adic coefficients, mobile eta, and profinite correction remain exact named
parameters. The hash identifies a **symbolic template**, not an instantiated
word: it does not contain `q`, `nuP`, or the actual parameter values.

The actual-word links are the uniform kernel-checked equalities
`GeneralTemplate.denote_pairSplice` and `GeneralTemplate.denote_mobileSplice`,
using the exact environments named in each artifact. An arbitrary assignment
to the named parameters need not satisfy the source certificate.

Each `.template.json` comes directly from the Lean expression tree. Its `.tex`
is rendered from that tree; displayed `W_i` are literal shared subtrees, with
no algebraic simplification. The adjacent `.provenance.json` snapshots direct
staged source bytes separately from the template hash. It does not record the
entire transitive Lean build or replace a fresh rebuild.

Generate and strongly check using the current configured Lean runner:

```
export GQ2_W361_PACKAGES=/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages
python3 scripts/w361_general_word_tex.py generate \
  --lean-runner scripts/w361_lean_runner.sh pair 2 1 0
python3 scripts/w361_general_word_tex.py generate \
  --lean-runner scripts/w361_lean_runner.sh mobile 2 1 0 0
python3 scripts/w361_general_word_tex.py check generated/general-template-staged \
  --lean-runner scripts/w361_lean_runner.sh
```

The package path is this workstation's matching dependency cache. On another host use an
equivalent manifest-matched directory. `GQ2_W361_ARTIFACTS` may select a completed isolated
fresh build; the default is the local campaign build cache. The runner verifies the toolchain
version and dependency manifest and does not invoke Lake or rebuild missing imports.

Without the runner, `check` is artifact-only and does not verify correspondence
to the actual Lean factory. None of these files modify or supplement the old
S1.1 hash manifest automatically, and none constitutes the ledger's full
ten-item acceptance appendix. See
`docs/dyadic/w361-word-template-proposal.md` for scope and remaining approval.
