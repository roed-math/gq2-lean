# W361 staged certificate displays

These files are additive research artifacts for the **changed pair/mobile source
words**. They are not accepted replacements for `generated/appendix/`, not a
certificate for the frozen M word, and not a new enabled release gate.

The four `.packet.json` objects combine the exact Lean-exported word, Fox,
quadratic-phase and phase-cover trees. Continuous word parameters, residue size,
action half-period, coefficient dimension and quadratic space remain symbolic.
The accompanying `.appendix.tex` has ten sections. Mathematical formulas in the
Fox, phase and cover sections traverse the typed trees. Other explanatory text
and theorem references are editorial and remain subject to review.

For each structural specimen:

- `.packet.json` binds four template envelopes, rank/phase linkage, section text
  and direct source hashes under a domain-separated SHA-256 hash;
- `.appendix.tex` is deterministic generated presentation, including exact
  subtree abbreviations for the large word; expanding them reproduces its AST;
- `.proofs.lean` checks cited declaration existence, standard-three axiom bounds
  and prints types;
- `.proofs.txt` records that transcript; strong replay must match it exactly;
- `.files.json` hashes these four files (without a circular self-hash).

Standalone `.fox`, `.phase` and `.cover` JSON/TeX pairs exercise the component
renderers too. They are symbolic templates, not new instances of field theorems.

## Reproduce and check

From the repository root, configure a manifest-matching dependency tree and the
intended local artifact root. The latter should be a completed isolated build
when reporting final-source evidence, not an unverified shared cache.

```sh
export GQ2_W361_PACKAGES=/absolute/path/to/matching/.lake/packages
export GQ2_W361_ARTIFACTS=/absolute/path/to/local/lib/lean
python3 scripts/w361_certificate_packet.py build \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w361_certificate_packet.py check \
  generated/general-certificate-staged --lean-runner scripts/w361_lean_runner.sh
```

`build` regenerates only the separate staged directory, from existing checked
word-template inputs. The optional `--templates` and `--out` arguments allow
isolated runs; the output path must contain `general-certificate-staged`.

The read-only opt-in suite `bash scripts/w361_check_staged.sh` additionally runs
component/packet mutation tests, exact endpoint and artifact axiom audits, and
all component strong replays. This script does not change the frozen gate.
Without `--lean-runner`, a component or packet `check` explicitly reports
**artifact-only; NOT Lean-synchronized**. Rehashing a coherent fake formula can
pass that weaker mode; actual Lean replay is essential.

## Trust boundary

The original symbolic word hash does not bind concrete q, nuP, eta, shear or
correction values. Fox hashes do not select the coefficient action or its
half-period. Phase/cover hashes do not select a concrete quadratic space. Exact
uniform Lean bridges bind their mathematical uses under the displayed hypotheses.

The combined source provenance covers selected direct files only. It is neither
a transitive build hash nor an atomic filesystem snapshot. The proof probe imports
the artifact root selected by the runner; source hashes alone do not prove those
artifacts were compiled from those source bytes. The type transcript is checked
for replay equality, not against an independently authored type specification.
External dependency artifacts are reused, with a matching manifest, not rebuilt.
Separate source-only build evidence and owner acceptance remain necessary.

In particular, the generated section on normal coordinates links the exact
original coordinate theorem and prints its polar matrix; it does not serialize
an independent executable description of the entire source quotient map. The
same-tree checks also do not turn the editorial specialization/Stokes paragraphs
into kernel-checked prose. None of these caveats is a missing premise in the
already-proved general changed-word presentation.
