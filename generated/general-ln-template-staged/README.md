# STAGED L/N word examples

These six examples exercise the **uniform** factory/export/denotation bridges
in `GQ2/Dyadic/Word/GeneralTemplateLNCanonical.lean`. They are executable
synchronization regressions, not six separate mathematical proofs, an approved
appendix format, or a complete ten-item L/N certificate packet.

| Request | Purpose |
|---|---|
| `L 0` | Empty handles and preservation of the frozen L word hash. |
| `L 4` | Ordered handle expansion beyond the frozen rank. |
| `N0 5 3` | Non-fixture exponent and handle rank. |
| `Npc 2 1 0 1 1` | Empty handles and preservation of the frozen Npc word hash. |
| `Npc 3 2 3 3 9` | Exact nonreduced odd rational display. |
| `Npc 3 2 3 -3 9` | An actual negative odd ratio, also nonreduced. |

Each request has an `.ln.json` envelope, TeX rendered from that exact canonical
AST, and a direct-source `.provenance.json` sidecar. The old S1.1 `word_hash`
binds the canonical word, while the new `template_hash` also binds the original
requested parameters and semantic-bridge metadata. The final requests reduce
to `1/3` and `-1/3`, respectively. Lean proves canonicalization preserves
the actual word, including sign/gcd normalization of the odd rational exponent.

From the repository root, with a matching Lean package/artifact tree:

```sh
export GQ2_W361_PACKAGES=/path/to/matching/.lake/packages
export GQ2_W361_ARTIFACTS=/path/to/matching/lib/lean
python3 scripts/w361_general_ln_word_tex.py self-test
python3 scripts/w361_general_ln_word_tex.py check generated/general-ln-template-staged --lean-runner scripts/w361_lean_runner.sh
```

All six were checked by **fresh Lean factory replay**, not merely by internal
hash consistency. Reproduce a request with `generate`, for example:

```sh
python3 scripts/w361_general_ln_word_tex.py generate Npc 3 2 3 -3 9 --lean-runner scripts/w361_lean_runner.sh --out generated/general-ln-template-staged
```

Scope limits: L's complete certificate still uses its odd residue-degree
hypothesis; N0/Npc certificate hypotheses are distinct from syntax validation.
Npc's semantic-unit bridge requires an **exact** `NpcDisplayFor eta`, not a
finite-precision congruence or an assumed rational display for every unit.
The all-rank proofs establish generality; these examples only test the tooling.
Full L/N Fox/Hessian/phase publication synchronization and owner approval remain
separate. Frozen factories, renderer, manifests and generated skeletons were
not changed. See `docs/dyadic/w361-general-ln-export.md` for the schema and exact
trust boundary.
