# gq2-lean — A presentation of $G_{\mathbf{Q}_2}$ in Lean

[![CI](https://github.com/roed-math/gq2-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/roed-math/gq2-lean/actions/workflows/ci.yml)

This repository contains a Lean 4 +
[Mathlib](https://github.com/leanprover-community/mathlib4) formalization of an explicit
presentation of the absolute Galois group of the 2-adic numbers. It assumes no axiom beyond Lean's
standard three: the nine classical local-arithmetic results the paper cites are proved from the
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) library.

- [Current writeup and project site](https://roed314.github.io/gq2/)
- [Original paper submitted to the formalization](paper/A_Profinite_Presentation_for_G__Q_2.pdf)

The PDF is retained as an immutable record of the original source. The web writeup is the
maintained version and may change its exposition or theorem numbering. Cross-references between
the paper and Lean therefore use semantic result identifiers and declaration names rather than
treating displayed theorem numbers as stable; see [`docs/paper-api.md`](docs/paper-api.md).


> **Branch note (`dyadic`, 2026-10-17).** This branch carries the general-2-adic campaign
> (`docs/dyadic/`). The statements below about the ℚ₂ theorem and its trust base hold here too. The
> campaign's two `K`-level inputs, B5-K `markedRecipAt` and B10-K `orientedTameQuotientAt`, were the
> last `axiom` declarations on this branch (census 2 after the merge of the ℚ₂ discharge); they are
> proved from Tau Ceti as well since ticket C1' of
> [`docs/dyadic/tauceti-discharge-plan.md`](docs/dyadic/tauceti-discharge-plan.md)
> (`GQ2/TauCeti/{GaloisDictK,B5K,B10K}.lean`), so the library on this branch also contains no axiom.

## Result

The paper's result is complete and its proof contains no `sorry`; since 2026-07-26 neither does
anything else in the `GQ2` library, including the follow-on campaign under
[`GQ2/Roe/`](GQ2/Roe/) described in [Roe-candidate verification](#roe-candidate-verification) below
(not part of the paper). The separate Comparator input
[`Challenge.lean`](Challenge.lean) intentionally contains one `sorry` per challenge theorem: those
are the untrusted challenge statements whose proofs are supplied by
[`Solution.lean`](Solution.lean). The literal
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

Both theorems take no hypothesis and depend only on Lean's standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. The library declares no axiom, and every declaration under
`GQ2` depends on those three alone. The paper cites nine classical local-arithmetic results that
Mathlib does not provide (Appendix B: leaves B1, B3c, B5–B10, B11a). Until 2026-10-17 this
repository stated them as nine Lean axioms; they are now proved from the
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) library, pinned at revision `706344c35`, by
adapters in [`GQ2/TauCeti/`](GQ2/TauCeti/) (see [The nine literature inputs](#the-nine-literature-inputs)
below). The trust base is therefore Lean's kernel and standard axioms, Mathlib, and Tau Ceti's
proofs at that revision.

The same proof graph is also available with the nine inputs as an explicit hypothesis.
[`GQ2/Foundations/LiteratureInputs.lean`](GQ2/Foundations/LiteratureInputs.lean) bundles
their interfaces into an ordinary `LiteratureInputs` typeclass hypothesis, and the generic
capstones are

```lean
GQ2.main_presentation_literal_of_inputs [LiteratureInputs] :
  Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)

GQ2.main_presentation_literal_roe_unconditional_of_inputs [LiteratureInputs] :
  Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)
```

[`GQ2/TauCeti/Instance.lean`](GQ2/TauCeti/Instance.lean) builds
`GQ2.TauCetiBridge.tauCetiInputs : LiteratureInputs` from the nine adapters, and
[`GQ2/TauCeti/Main.lean`](GQ2/TauCeti/Main.lean) instantiates the generic capstones at it:
`GQ2.main_presentation_literal_tauceti`, `GQ2.main_presentation_literal_roe_tauceti`,
`GQ2.main_surjection_count_tauceti`, and `GQ2.main_surjection_count_R_tauceti` carry the statements
of the corresponding legacy capstones, independently of instance selection.
[`GQ2/Foundations/TauCetiInstance.lean`](GQ2/Foundations/TauCetiInstance.lean) registers the same
term as the instance `GQ2.tauCetiLiteratureInputs`, which the legacy capstones select, and keeps
the nine original public names (`GQ2.localReciprocity`, `GQ2.tateDualityAt`, …) as theorems and
definitions whose statements are byte-identical to the former axioms and whose bodies are the
adapters.

Eight fields have the same universe scope as their legacy declarations.  B7 is restricted to
`M : Type` because a Lean structure field cannot quantify over a fresh universe level; this covers
every consumer in this proof. Tau Ceti's Euler-characteristic theorem is also stated for
`M : Type`; the legacy B7 theorem keeps `M : Type*` by transporting it along a `Fin (Nat.card M)`
copy of `M`.

The independent Palomar/Comparator pair
[`ChallengePalomar.lean`](ChallengePalomar.lean) and [`SolutionPalomar.lean`](SolutionPalomar.lean)
uses only the explicit-hypothesis route; its import-closure audit checks that none of the nine
legacy literature declarations is present at all. The pair was locally verified, before the move
to Lean `v4.35.0`, with Comparator commit `68a064109f01c08f47c8edc9f51d6a2bbffaa188` and the
`lean4export` tag matching Lean `v4.31.0-rc2`.

With $x^g=g^{-1}xg$ and $[x,y]=x^{-1}y^{-1}xy$, the presented group has generators
$\sigma,\tau,x_0,x_1$, a pro-2 normal closure of $x_0,x_1$, and relations

$$
\tau^\sigma=\tau^2,
\qquad
h_0u_1^{-1}x_1^\sigma c_0=1.
$$

The definitions of $u_1$, $c_0$, and $h_0$ are in [`GQ2/Words.lean`](GQ2/Words.lean); the current
writeup gives the mathematical construction and proof in full.

### The nine literature inputs

Each input is proved by an adapter in namespace `GQ2.TauCetiBridge`, in the listed file under
[`GQ2/TauCeti/`](GQ2/TauCeti/), from the listed Tau Ceti declarations. The legacy name (in
namespace `GQ2`, declared in `GQ2/Foundations/TauCetiInstance.lean`) keeps the former axiom's
statement and is proved by that adapter (for B7, through the universe transport above). Every
adapter depends only on the standard three axioms.

| Leaf | Input | Legacy name | Adapter file | Main Tau Ceti declarations |
|---|---|---|---|---|
| B1 | $G_{\mathbf{Q}_2}$ topologically finitely generated | `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` | `B1.lean` | `TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup` |
| B3c | dyadic orientation | `dyadicOrientation` | `B3c.lean` | `TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked`, `TauCeti.standardD0Orientation_d0A` (`_d0S`, `_d0Y`) |
| B5 | local reciprocity for $\mathbf{Q}_2$ | `localReciprocity` | `B5.lean` | `TauCeti.ClassFieldTheory.artinMap` and its lemmas (`TauCeti.NumberTheory.ClassFieldTheory.Local.*`) |
| B6 | local Tate duality at finite $k/\mathbf{Q}_2$ | `tateDualityAt` | `B6.lean`, `DualizingGroup.lean` | `TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed`, `TauCeti.ClassFieldTheory.h2MuEquivZMod_mixed` |
| B7 | local Euler characteristic at $p=2$ | `Foundations.absGalQ2_localEulerCharacteristic` | `B7.lean` | `TauCeti.ClassFieldTheory.eulerCharacteristic_mixed`, `TauCeti.ClassFieldTheory.finite_H` |
| B8 | peripheral cyclotomic action | `peripheralCyclotomicAction` | `B8.lean` | `TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two` |
| B9 | relative Stiefel–Whitney identity, dyadic case | `relativeStiefelWhitney_dyadic` | `B9.lean`, `StiefelWhitneyDict.lean` | `TauCeti.sw1_eq_add_galoisCor_of_equivalent_traceTransfer`, `TauCeti.sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer` |
| B10 | oriented tame quotient of $G_{\mathbf{Q}_2}$ | `tameQuotient` | `B10.lean` | `TauCeti.wildInertiaSubgroup`, `TauCeti.tameQuotientGeometricEquiv`, `TauCeti.iwasawaCoordinateGeometric` |
| B11a | Hilbert-symbol norm criterion, finite dyadic $k$ | `hilbertSymbol_normCriterion_finiteDyadic` | `B11a.lean` | `TauCeti.cup_kummerClass_eq_zero_iff` |

Three shared dictionaries translate between the libraries: `GaloisDict.lean` (absolute Galois
groups of finite extensions of $\mathbf{Q}_2$, the cyclotomic character), `CohomologyDict.lean`
(this repository's explicit $H^0$, $H^1$, $H^2$, restriction, cup products, and Kummer classes
against Tau Ceti's continuous cohomology), and `ProPDict.lean` (pro-$p$ and free profinite groups,
presentations, $\hat{\mathbf{Z}}$, the Demushkin group $D_0$). Convention differences are reconciled
inside the proofs, not in the statements: for example, Tau Ceti's arithmetic Frobenius against the
geometric one used here (B5, B10) is handled by inversion. What each statement asserts, its
citation, and its encoding choices are documented in
[`docs/literature-axioms.md`](docs/literature-axioms.md); the statements did not change when the
axioms were replaced.

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
GQ2.main_presentation_literal_roe_unconditional :
  Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)
```

in [`GQ2/Roe/Main.lean`](GQ2/Roe/Main.lean), with the counting form
`GQ2.main_surjection_count_R` and the bridge `GQ2.admissibleCountR_eq_admissibleCount` proving
that the two candidates' admissible-marking counts agree on every finite group.

**This result is unconditional, and costs nothing beyond the paper's own inputs.**
`main_presentation_literal_roe_unconditional` depends on exactly the same axioms as
`main_presentation_literal` — the standard three since 2026-10-17, and before that the standard
three plus the same nine literature axioms — which
[`scripts/check_axioms.sh`](scripts/check_axioms.sh) and
[`GQ2/AxiomLedger.lean`](GQ2/AxiomLedger.lean) both check mechanically rather than assert.

It was briefly conditional, and how that was resolved is the campaign's main methodological point.
The $\Gamma_R$ route needs one input the paper's does not: a Labute-classification instance
identifying the pro-2 quotient $D_R$ with the dyadic normal form $D_0$. Rather than admit it as a
tenth axiom, it was carried as an explicit hypothesis `BLabHypothesis`
([`GQ2/Roe/MarkedPro2.lean`](GQ2/Roe/MarkedPro2.lean)) — a theorem binder, so that the
conditionality was visible in the statement itself — and then **proved** (2026-07-26):

```lean
GQ2.Roe.Labute.bLab : BLabHypothesis
```

in [`GQ2/Roe/Labute/`](GQ2/Roe/Labute/), at the standard three axioms and with no `sorry`, by
building continuous surjections both ways along the two-central tower of $D_R$ and closing with the
profinite Hopfian property. So $D_R \cong D_0$ is now itself a theorem of this repository over
Mathlib, the axiom census stayed at nine (it is zero since the nine were proved from Tau Ceti), and
the hypothesis-parametrized `main_presentation_literal_roe` is kept alongside the corollary as the
frozen statement the gates audit. The exact statement, the proof chain, and the decision record are in the "B3 addendum" of
[`docs/literature-axioms.md`](docs/literature-axioms.md).

The two-page mathematical account is
[`docs/roe-campaign-summary.md`](docs/roe-campaign-summary.md); the campaign plan, with a status
block recording the outcome against it, is
[`docs/orchestration/roe-verification-plan.md`](docs/orchestration/roe-verification-plan.md).

## Trust and validation

The repository uses several complementary checks. They answer different questions and should not
be conflated.

### Kernel and axiom hygiene

Every declaration under `GQ2` depends only on Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`, and the library declares no axiom. Until 2026-10-17 the legacy API also used nine
explicit literature axioms in `GQ2/Foundations/Axioms.lean`, assembled into a `LiteratureInputs`
instance by `GQ2/Foundations/AxiomInstance.lean`; both files were deleted once all nine inputs were
proved from Tau Ceti (ticket C2 of the campaign recorded in
[`docs/orchestration/tauceti-tickets.md`](docs/orchestration/tauceti-tickets.md)). The legacy names
now live in [`GQ2/Foundations/TauCetiInstance.lean`](GQ2/Foundations/TauCetiInstance.lean), and the
derived same-name interfaces over them in
[`GQ2/Foundations/Interfaces.lean`](GQ2/Foundations/Interfaces.lean). What changed is why the nine
statements hold, not what they say: their precise statements, citations, and deviations from the
cited formulations are documented in [`docs/literature-axioms.md`](docs/literature-axioms.md).
[`docs/axiom-closure.md`](docs/axiom-closure.md) lists, per input, every project definition a
reader must consult to know what the input asserts (115 definitions across the nine); it was
generated on 2026-07-27, when the nine were axioms, and its generator `scripts/axiom_closure.sh`
still imports the deleted axiom file.

Tau Ceti's proofs are part of the trust base. Tau Ceti is machine-written; it enforces zero
sorries and an axiom allowlist in its own CI. Here its contribution is re-checked through the
axiom prints below: a `sorry` or a non-standard axiom in Tau Ceti's proofs of the nine inputs
would appear in the capstones' `#print axioms`.

[`scripts/check_axioms.sh`](scripts/check_axioms.sh) enforces the axiom census (zero), rejects
`sorry` and `native_decide` from the `GQ2` library, and ensures that no library file declares an
axiom. It deliberately does not treat the Comparator placeholders in `Challenge.lean` as library
proof gaps. Its `sorry` allowlist is empty, so a `sorry` anywhere in the library fails the check.
It then reads the axioms each capstone actually depends on and requires them to be exactly the
standard three, with each $\Gamma_R$ capstone printing identically to its $\Gamma_A$ twin — which
is also how the repository certifies that the $\Gamma_R$ result introduces no new axiom and rests
on no unfinished proof — and finally runs the two import-closure audits below.

Building [`GQ2/AxiomLedger.lean`](GQ2/AxiomLedger.lean) walks every declaration under `GQ2`
(7,486 at the census flip, all at the standard three), summarizes by module which elaborated
declaration types carry `LiteratureInputs`, lists everything still resting on a `sorry`, detects
unknown non-standard axioms, and fails outright if any capstone acquires a `sorry` or a
non-standard axiom, or if a $\Gamma_R$ capstone stops matching its paper counterpart axiom for
axiom.

[`GQ2/TauCetiAxiomAudit.lean`](GQ2/TauCetiAxiomAudit.lean) imports only `GQ2.TauCeti.Main` and
checks that none of the nine legacy declarations is in that import closure and that the four Tau
Ceti capstones use exactly the standard three axioms.
[`GQ2/PalomarAxiomAudit.lean`](GQ2/PalomarAxiomAudit.lean) imports only `SolutionPalomar` and
checks the same absence and that both explicit-hypothesis solutions use only the standard three.

### `formalization.yaml` and Comparator

[`formalization.yaml`](formalization.yaml) is the repository's structured self-report. It records
the source, scope, provenance, automation, fidelity decisions, review status, principal Lean
declarations, and permitted axiom set using the
[`formalization.yaml` standard](https://github.com/mathlib-initiative/formalization.yaml).

The main theorem, and the $\Gamma_R$ theorem alongside it, are also packaged for
[`leanprover/comparator`](https://github.com/leanprover/comparator):

- [`Challenge.lean`](Challenge.lean) states both theorems, one intentional `sorry` each, using only
  the imports needed for their statements — neither reaches `GQ2/Roe/Labute/`;
- [`Solution.lean`](Solution.lean) supplies `GQ2.main_presentation_literal` and
  `GQ2.main_presentation_literal_roe_unconditional` as their proofs;
- [`comparator-config.json`](comparator-config.json) names both theorems and permits exactly the
  standard three axioms (until 2026-10-17, also the nine literature axioms) — one list, shared,
  because the two theorems have the same axiom dependencies.

For the $\Gamma_R$ theorem, the challenge is `challenge_main_presentation_literal_roe_unconditional`
— `Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)` with no hypothesis and no instance binder — so a
passing Comparator run certifies the **unconditional** statement. Between 2026-07-25 and 2026-07-26
the challenge carried an `hBLab : BLabHypothesis` binder and Comparator therefore certified only the
*conditional* statement; the L-campaign discharged that hypothesis as the in-repo theorem
`GQ2.Roe.Labute.bLab`, and the pair was restated against
`GQ2.main_presentation_literal_roe_unconditional`. The solution's import closure consequently now
reaches `GQ2/Roe/Labute/` — sorry-free, like the rest of the library — while neither challenge
statement's closure does.

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
after the L-campaign, from a graph of 5,571 project nodes and 49,304 edges. For
`GQ2.SectionTen.main_surjection_count'` — whose closure `GQ2/Roe/` does not touch — the 1,789-node
Atlas closure reduces to a **30-declaration Lean Compass review cone**: according to the Lean
Compass review model, these are the project declarations that should be checked by a human for
semantic alignment. The report lists all 30 with source links. It separately obtains the kernel
trust base from Lean's `#print axioms`; this avoids undercounting axioms reached through private
proof helpers, which Atlas intentionally omits from its user-visible graph. The snapshot predates
the Tau Ceti discharge, so it still reports the nine literature axioms of that date; it has not
been regenerated since.

The snapshot's header records a whole-graph `sorry` count of **0**: the last 11 were in the
`GQ2/Roe/Labute/` files, which closed on 2026-07-26 before this snapshot was taken, and
`scripts/check_axioms.sh` enforces the count on every build. The capstone's own closure was
sorry-free throughout.

Regeneration instructions and the distinction between the Compass cone and the kernel trust base
are in [`docs/atlas.md`](docs/atlas.md).

## Reproducing the local checks

The project uses `leanprover/lean4:v4.35.0`; Tau Ceti (`706344c35`), Mathlib (`cfc55fc`, the
revision Tau Ceti's manifest pins, so the two pins move together), and Lean Atlas are pinned in
[`lakefile.toml`](lakefile.toml).

Mathlib's build outputs come from its own cache. Tau Ceti's come from Tau Ceti's public Lake
cache, set up as in the "Fetch Tau Ceti cache map" step of the
[CI workflow](.github/workflows/ci.yml): declare the service in a Lake configuration file, then
keep `LAKE_CONFIG` (that file) and `LAKE_CACHE_DIR` (the local cache directory) set for the fetch,
the build, and the checks.

```sh
lake exe cache get

cat > .lake/tauceti-lake-cache.toml <<'TOML'
cache.defaultService = "tauceti-public"
[[cache.service]]
name = "tauceti-public"
kind = "s3"
artifactEndpoint = "https://cache.taucetiproject.org/artifacts"
revisionEndpoint = "https://cache.taucetiproject.org/revisions"
TOML
export LAKE_CONFIG=$PWD/.lake/tauceti-lake-cache.toml LAKE_CACHE_DIR=$PWD/.lake/cache
lake cache get --package=TauCeti --service=tauceti-public \
  --repo=TauCetiProject/TauCeti --mappings-only --max-revs=20
lake build

bash scripts/check_axioms.sh
lake env lean GQ2/AxiomLedger.lean
lake build Challenge Solution
lake build ChallengePalomar SolutionPalomar
lake env lean GQ2/PalomarAxiomAudit.lean
lake env lean GQ2/TauCetiAxiomAudit.lean

lake exe atlas graph-data -o atlas-graph.json
python3 scripts/atlas_audit.py atlas-graph.json
```

Without the Tau Ceti cache (the two variables unset, or a cache miss), `lake build` compiles Tau
Ceti's import closure, several thousand modules, from source instead.

`atlas-graph.json` is generated and ignored by Git. The human-readable
[`atlas-audit.md`](atlas-audit.md) is committed so reviewers can inspect the exact current
review cone without installing the Atlas viewer.

The [GitHub Actions workflow](.github/workflows/ci.yml) restores the Mathlib cache and the Tau
Ceti cache map, performs the full Lean build, including both Comparator pairs, then runs the
axiom-hygiene script, the transitive axiom ledger, and the explicit-hypothesis and Tau Ceti audits
on every push to and pull request against `master`.

## Repository guide

| Path | Purpose |
|---|---|
| `paper/` | Original source PDF retained for reproducibility, plus the $\Gamma_R$ verification note (`roe-presentation-*`) that the Roe campaign formalizes |
| `GQ2/Words.lean` | Finite-group marking, auxiliary words, and admissibility predicate |
| `GQ2/GammaA.lean` | Construction of the candidate profinite group $\Gamma_A$ |
| `GQ2/Foundations/LiteratureInputs.lean` | The `LiteratureInputs` bundle: interfaces of the nine cited literature inputs |
| `GQ2/TauCeti/` | Proofs of the nine inputs from Tau Ceti: one adapter per input, shared dictionaries, the bundle `tauCetiInputs` (`Instance.lean`), and the four Tau Ceti capstones (`Main.lean`) |
| `GQ2/Foundations/TauCetiInstance.lean` | The nine legacy names, now theorems and definitions backed by the adapters, and the `LiteratureInputs` instance |
| `GQ2/Foundations/Interfaces.lean` | Derived same-name interfaces over the literature inputs (discharged B7′/B11b/B12/B13, derived B9 form, …) |
| `GQ2/SectionTenSources.lean` | Counting capstone and paper equation (154) |
| `GQ2/PresentationLiteral.lean` | Literal profinite-group isomorphism theorem |
| `GQ2/Roe/` | Roe-candidate verification: $\Gamma_R$, its capstones (`Roe/Main.lean`), and the proof of `BLabHypothesis` (`Roe/Labute/`) |
| `GQ2/AxiomLedger.lean` | Generated-style transitive axiom-consumer certificate |
| `GQ2/TauCetiAxiomAudit.lean`, `GQ2/PalomarAxiomAudit.lean` | Import-closure and capstone axiom audits of the Tau Ceti and explicit-hypothesis routes |
| `Challenge.lean`, `Solution.lean`, `comparator-config.json` | Comparator validation pair |
| `formalization.yaml` | Structured provenance, fidelity, and review metadata |
| `atlas-audit.md` | Regenerated Lean Compass review cone and kernel axiom report |
| `docs/` | Maintained mathematical audits, paper crosswalks, errata, and historical proof-design archive; see [`docs/README.md`](docs/README.md) |
| `scripts/` | Axiom hygiene, Atlas report generation, and paper-API audit tools |
| `.github/workflows/ci.yml` | Automated build, axiom-hygiene, ledger, and audit checks |

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
  mathematics, and exactly what its theorem rests on.

## License

The Lean code and repository documentation are released under Apache License 2.0; see
[`LICENSE`](LICENSE). The retained paper PDF is included as source material and is not relicensed by
the code license.
