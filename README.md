# gq2-lean — A presentation of $G_{\mathbf{Q}_2}$ in Lean

This repository contains a Lean 4 +
[Mathlib](https://github.com/leanprover-community/mathlib4) formalization of an explicit
presentation of the absolute Galois group of the 2-adic numbers.

- [Current writeup and project site](https://roed314.github.io/gq2/)
- [Original paper submitted to the formalization](paper/A_Profinite_Presentation_for_G__Q_2.pdf)

The PDF is retained as an immutable record of the original source. The web writeup is the
maintained version and may change its exposition or theorem numbering. Cross-references between
the paper and Lean therefore use semantic result identifiers and declaration names rather than
treating displayed theorem numbers as stable; see [`docs/paper-api.md`](docs/paper-api.md).

## Result

The formalization is complete and contains no `sorry`. Its literal form of the presentation
theorem is

```lean
GQ2.main_presentation_literal :
  Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)
```

in [`GQ2/PresentationLiteral.lean`](GQ2/PresentationLiteral.lean). The equivalent finite-counting
form is

```lean
GQ2.SectionTen.main_surjection_count'
```

in [`GQ2/SectionTenSources.lean`](GQ2/SectionTenSources.lean): for every finite group $G$, the
cardinality of the continuous surjections $G_{\mathbf{Q}_2} \twoheadrightarrow G$ equals the
cardinality of the admissible marked generating quadruples in $G^4$.

With $x^g=g^{-1}xg$ and $[x,y]=x^{-1}y^{-1}xy$, the presented group has generators
$\sigma,\tau,x_0,x_1$, a pro-2 normal closure of $x_0,x_1$, and relations

$$
\tau^\sigma=\tau^2,
\qquad
h_0u_1^{-1}x_1^\sigma c_0=1.
$$

The definitions of $u_1$, $c_0$, and $h_0$ are in [`GQ2/Words.lean`](GQ2/Words.lean); the current
writeup gives the mathematical construction and proof in full.

## Trust and validation

The repository uses several complementary checks. They answer different questions and should not
be conflated.

### Kernel and axiom hygiene

The proof uses Lean's standard `propext`, `Classical.choice`, and `Quot.sound`, together with nine
explicit literature axioms in
[`GQ2/Foundations/Axioms.lean`](GQ2/Foundations/Axioms.lean). The axioms cover external
local-arithmetic, cohomological, and peripheral-action inputs not currently supplied by Mathlib;
their precise statements, citations, and deviations from the cited formulations are documented in
[`docs/literature-axioms.md`](docs/literature-axioms.md).

[`scripts/check_axioms.sh`](scripts/check_axioms.sh) enforces the axiom census, rejects `sorry` and
`native_decide`, and ensures that no other file declares axioms. Building
[`GQ2/AxiomLedger.lean`](GQ2/AxiomLedger.lean) reports the transitive consumers of every literature
axiom and detects unknown non-standard axioms.

### `formalization.yaml` and Comparator

[`formalization.yaml`](formalization.yaml) is the repository's structured self-report. It records
the source, scope, provenance, automation, fidelity decisions, review status, principal Lean
declarations, and permitted axiom set using the
[`formalization.yaml` standard](https://github.com/mathlib-initiative/formalization.yaml).

The main theorem is also packaged for
[`leanprover/comparator`](https://github.com/leanprover/comparator):

- [`Challenge.lean`](Challenge.lean) states the theorem using only the imports needed for its
  statement;
- [`Solution.lean`](Solution.lean) supplies `GQ2.main_presentation_literal` as its proof;
- [`comparator-config.json`](comparator-config.json) names the theorem and permits exactly the
  standard three axioms plus the nine documented literature axioms.

Comparator checks that the challenge and solution statements agree, that the solution uses only
the permitted axioms, and that the exported solution is accepted by Lean's kernel. Its security
model requires a fresh checking environment and external `landrun` and `lean4export` binaries; the
upstream Comparator README gives the authoritative invocation and trust assumptions. The local
pair can be compiled with `lake build Challenge Solution` before running that independent check.

### Lean Atlas and Lean Compass

[Lean Atlas](https://github.com/NyxFoundation/lean-atlas) exports the project dependency graph.
Lean Compass removes theorem-proof value dependencies—already checked by Lean's type checker—to
isolate declarations whose *semantic statements or definitions* can affect a selected result.

The post-refactor report is [`atlas-audit.md`](atlas-audit.md). For
`GQ2.SectionTen.main_surjection_count'`, the current graph has 4,225 project nodes and 35,335 edges.
Its 638-node Atlas closure reduces to a **30-declaration Lean Compass review cone**: according to
the Lean Compass review model, these are the project declarations that should be checked by a
human for semantic alignment. The report lists all 30 with source links. It separately obtains the
complete nine-axiom trust base from Lean's `#print axioms`; this avoids undercounting axioms reached
through private proof helpers, which Atlas intentionally omits from its user-visible graph.

Regeneration instructions and the distinction between the Compass cone and the kernel trust base
are in [`docs/atlas.md`](docs/atlas.md).

## Reproducing the local checks

The project uses `leanprover/lean4:v4.31.0-rc2`; Mathlib and Lean Atlas are pinned in
[`lakefile.toml`](lakefile.toml).

```sh
lake exe cache get
lake build

bash scripts/check_axioms.sh
lake env lean GQ2/AxiomLedger.lean
lake build Challenge Solution

lake exe atlas graph-data -o atlas-graph.json
python3 scripts/atlas_audit.py atlas-graph.json
```

`atlas-graph.json` is generated and ignored by Git. The human-readable
[`atlas-audit.md`](atlas-audit.md) is committed so reviewers can inspect the exact post-refactor
review cone without installing the Atlas viewer.

## Repository guide

| Path | Purpose |
|---|---|
| `paper/` | Original source PDF retained for reproducibility |
| `GQ2/Words.lean` | Finite-group marking, auxiliary words, and admissibility predicate |
| `GQ2/GammaA.lean` | Construction of the candidate profinite group $\Gamma_A$ |
| `GQ2/Foundations/Axioms.lean` | The nine cited literature inputs |
| `GQ2/SectionTenSources.lean` | Counting capstone and paper equation (154) |
| `GQ2/PresentationLiteral.lean` | Literal profinite-group isomorphism theorem |
| `GQ2/AxiomLedger.lean` | Generated-style transitive axiom-consumer certificate |
| `Challenge.lean`, `Solution.lean`, `comparator-config.json` | Comparator validation pair |
| `formalization.yaml` | Structured provenance, fidelity, and review metadata |
| `atlas-audit.md` | Regenerated Lean Compass review cone and kernel axiom report |
| `docs/` | Maintained mathematical audits, paper crosswalks, errata, and historical proof-design archive; see [`docs/README.md`](docs/README.md) |
| `scripts/` | Axiom hygiene, Atlas report generation, and paper-API audit tools |

Large proof developments are split into focused submodules while their original import paths remain
thin public umbrellas. Public declarations stay under the `GQ2` namespace, so the file split does
not change the paper-facing API.

## Documentation

[`docs/README.md`](docs/README.md) describes every maintained document and explains the status of
the historical material in [`docs/orchestration/`](docs/orchestration/). The most useful entry
points for mathematical review are:

- [`docs/paper-api.md`](docs/paper-api.md) — stable paper-to-Lean cross-reference policy;
- [`docs/paper-errata.md`](docs/paper-errata.md) — corrections, load-bearing hypotheses, and fragile
  passages discovered during formalization;
- [`docs/literature-axioms.md`](docs/literature-axioms.md) — exact literature inputs and citations;
- [`docs/adversarial-axioms-review.md`](docs/adversarial-axioms-review.md) — independent critical
  review of those inputs;
- [`docs/atlas.md`](docs/atlas.md) — Lean Atlas and Lean Compass methodology and regeneration.

## License

The Lean code and repository documentation are released under Apache License 2.0; see
[`LICENSE`](LICENSE). The retained paper PDF is included as source material and is not relicensed by
the code license.
