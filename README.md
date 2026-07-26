# gq2-lean — A presentation of $G_{\mathbf{Q}_2}$ in Lean

[![CI](https://github.com/roed-math/gq2-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/roed-math/gq2-lean/actions/workflows/ci.yml)

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

The paper's result is complete and its proof contains no `sorry`. The separate Comparator input
[`Challenge.lean`](Challenge.lean) intentionally contains one `sorry` per challenge theorem: those
are the untrusted challenge statements whose proofs are supplied by
[`Solution.lean`](Solution.lean). A follow-on campaign under
[`GQ2/Roe/`](GQ2/Roe/) — described in [Roe-candidate verification](#roe-candidate-verification)
below, and not part of the paper — is still in progress and does contain `sorry`; those are
confined to `GQ2/Roe/Labute/`, and nothing outside that directory depends on them. The literal
form of the proved presentation theorem is

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

## Roe-candidate verification

A candidate presentation found independently, before the paper's, asks whether a *different*
4-generator 2-relator group also presents $G_{\mathbf{Q}_2}$. Call it $\Gamma_R$: same generators
$\sigma,\tau,x_0,x_1$, same pro-2 normal closure of $x_0,x_1$, same tame relation
$\tau^\sigma=\tau^2$, but a different wild relator,

$$
(x_0^\sigma)^{-1}\,a\,x_1^2\,c = 1,
\qquad
a=(x_0^{-3}\tau)^{\omega_2},
\qquad
c=[x_1,\,x_1^{\sigma_2}],
\qquad
\sigma_2=\sigma^{\omega_2}.
$$

Answering it is a *replacement theorem*: the paper's finite-target induction is reused unchanged,
while the four candidate-specific inputs (tame and marked pro-2 boundary, Fox row, Stokes/duality,
quadratic Gauss signs) are re-verified for $\Gamma_R$. The terminal theorem is

```lean
GQ2.main_presentation_literal_roe (hBLab : BLabHypothesis) :
  Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)
```

in [`GQ2/Roe/Main.lean`](GQ2/Roe/Main.lean), with the counting form
`GQ2.main_surjection_count_R` and the bridge `GQ2.admissibleCountR_eq_admissibleCount` proving
that the two candidates' admissible-marking counts agree on every finite group.

**This result is conditional, and the paper's result is not.** `BLabHypothesis`
([`GQ2/Roe/MarkedPro2.lean`](GQ2/Roe/MarkedPro2.lean)) is a Labute-classification instance carried
as an explicit hypothesis — deliberately a theorem binder rather than a tenth axiom, so that the
conditionality is visible in the statement itself. It is neither proved in-repo nor admitted as an
axiom; the proof attempt lives in [`GQ2/Roe/Labute/`](GQ2/Roe/Labute/) and is unfinished, which is
the sole source of `sorry` in the `GQ2` library. Everything else in `GQ2/Roe/` is unconditional,
including `GQ2.prop_2_3_R`, which needs no literature axiom at all.

Granting that one hypothesis, $\Gamma_R$ costs nothing further: `main_presentation_literal_roe`
depends on exactly the same twelve axioms as `main_presentation_literal`, which
[`scripts/check_axioms.sh`](scripts/check_axioms.sh) and
[`GQ2/AxiomLedger.lean`](GQ2/AxiomLedger.lean) both check mechanically rather than assert.

The two-page mathematical account is
[`docs/roe-campaign-summary.md`](docs/roe-campaign-summary.md); the campaign plan, with a status
block recording the outcome against it, is
[`docs/orchestration/roe-verification-plan.md`](docs/orchestration/roe-verification-plan.md).

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
`native_decide` from the `GQ2` library, and ensures that no other library file declares axioms. It
deliberately does not treat the Comparator placeholders in `Challenge.lean` as library proof gaps.
Its `sorry` allowlist currently holds the four unfinished `GQ2/Roe/Labute/` files and nothing else,
so a `sorry` anywhere outside that directory still fails the check. A final check reads the axioms
each capstone actually depends on and requires them to be exactly the standard three plus the nine
literature axioms — which is also how the repository certifies that the conditional $\Gamma_R$
result introduces no new axiom and rests on no unfinished proof.

Building [`GQ2/AxiomLedger.lean`](GQ2/AxiomLedger.lean) reports the transitive consumers of every
literature axiom, lists everything still resting on a `sorry`, detects unknown non-standard axioms,
and fails outright if any capstone acquires a `sorry` or an off-census axiom, or if a $\Gamma_R$
capstone stops matching its paper counterpart axiom for axiom.

### `formalization.yaml` and Comparator

[`formalization.yaml`](formalization.yaml) is the repository's structured self-report. It records
the source, scope, provenance, automation, fidelity decisions, review status, principal Lean
declarations, and permitted axiom set using the
[`formalization.yaml` standard](https://github.com/mathlib-initiative/formalization.yaml).

The main theorem, and the conditional $\Gamma_R$ theorem alongside it, are also packaged for
[`leanprover/comparator`](https://github.com/leanprover/comparator):

- [`Challenge.lean`](Challenge.lean) states both theorems, one intentional `sorry` each, using only
  the imports needed for their statements — neither reaches `GQ2/Roe/Labute/`;
- [`Solution.lean`](Solution.lean) supplies `GQ2.main_presentation_literal` and
  `GQ2.main_presentation_literal_roe` as their proofs;
- [`comparator-config.json`](comparator-config.json) names both theorems and permits exactly the
  standard three axioms plus the nine documented literature axioms — one list, shared, because the
  two theorems have the same axiom dependencies.

For the $\Gamma_R$ theorem, note what a passing Comparator run does and does not establish: it
checks the *conditional* statement, so it is silent on whether `BLabHypothesis` is true.

Comparator checks that the challenge and solution statements agree, that the solution uses only
the permitted axioms, and that the exported solution is accepted by Lean's kernel. Its security
model requires a fresh checking environment and external `landrun` and `lean4export` binaries; the
upstream Comparator README gives the authoritative invocation and trust assumptions. The local
pair can be compiled with `lake build Challenge Solution` before running that independent check.

### Lean Atlas and Lean Compass

[Lean Atlas](https://github.com/NyxFoundation/lean-atlas) exports the project dependency graph.
Lean Compass removes theorem-proof value dependencies—already checked by Lean's type checker—to
isolate declarations whose *semantic statements or definitions* can affect a selected result.

The report is [`atlas-audit.md`](atlas-audit.md), a committed snapshot regenerated on 2026-07-26
after the R-campaign, from a graph of 5,351 project nodes and 47,492 edges. For
`GQ2.SectionTen.main_surjection_count'` — whose closure `GQ2/Roe/` does not touch — the 1,789-node
Atlas closure reduces to a **30-declaration Lean Compass review cone**: according to the Lean
Compass review model, these are the project declarations that should be checked by a human for
semantic alignment. The report lists all 30 with source links. It separately obtains the complete
nine-axiom trust base from Lean's `#print axioms`; this avoids undercounting axioms reached through
private proof helpers, which Atlas intentionally omits from its user-visible graph.

The whole-graph `sorry` count is 11, all in the allowlisted in-flight `GQ2/Roe/Labute/` files; the
capstone's own closure is sorry-free.

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
[`atlas-audit.md`](atlas-audit.md) is committed so reviewers can inspect the exact current
review cone without installing the Atlas viewer.

The [GitHub Actions workflow](.github/workflows/ci.yml) performs the full Lean build, including the
Comparator challenge and solution, then runs the axiom-hygiene script and transitive axiom ledger
on every push to and pull request against `master`.

## Repository guide

| Path | Purpose |
|---|---|
| `paper/` | Original source PDF retained for reproducibility, plus the $\Gamma_R$ verification note (`roe-presentation-*`) that the Roe campaign formalizes |
| `GQ2/Words.lean` | Finite-group marking, auxiliary words, and admissibility predicate |
| `GQ2/GammaA.lean` | Construction of the candidate profinite group $\Gamma_A$ |
| `GQ2/Foundations/Axioms.lean` | The nine cited literature inputs |
| `GQ2/SectionTenSources.lean` | Counting capstone and paper equation (154) |
| `GQ2/PresentationLiteral.lean` | Literal profinite-group isomorphism theorem |
| `GQ2/Roe/` | Roe-candidate verification: $\Gamma_R$, its capstones (`Roe/Main.lean`), and the unfinished `BLabHypothesis` proof (`Roe/Labute/`) |
| `GQ2/AxiomLedger.lean` | Generated-style transitive axiom-consumer certificate |
| `Challenge.lean`, `Solution.lean`, `comparator-config.json` | Comparator validation pair |
| `formalization.yaml` | Structured provenance, fidelity, and review metadata |
| `atlas-audit.md` | Regenerated Lean Compass review cone and kernel axiom report |
| `docs/` | Maintained mathematical audits, paper crosswalks, errata, and historical proof-design archive; see [`docs/README.md`](docs/README.md) |
| `scripts/` | Axiom hygiene, Atlas report generation, and paper-API audit tools |
| `.github/workflows/ci.yml` | Automated build, axiom-hygiene, and ledger checks |

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
- [`docs/atlas.md`](docs/atlas.md) — Lean Atlas and Lean Compass methodology and regeneration;
- [`docs/roe-campaign-summary.md`](docs/roe-campaign-summary.md) — the $\Gamma_R$ campaign's
  mathematics, and exactly what its conditional theorem rests on.

## License

The Lean code and repository documentation are released under Apache License 2.0; see
[`LICENSE`](LICENSE). The retained paper PDF is included as source material and is not relicensed by
the code license.
