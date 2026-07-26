# Documentation guide

The documentation is organized by review task. Files at the top level of `docs/` are maintained
mathematical or technical references. `docs/orchestration/` is a historical archive of the agent
workflow that produced the proof; it is useful for provenance and design rationale, but its ticket
states are not current project status. Two files in that directory are the exception and are
live: [`orchestration/roe-tickets.md`](orchestration/roe-tickets.md) and
[`orchestration/roe-verification-plan.md`](orchestration/roe-verification-plan.md), the board and
plan for the in-flight Γ_R campaign.

The original submitted paper is retained at
[`paper/A_Profinite_Presentation_for_G__Q_2.pdf`](../paper/A_Profinite_Presentation_for_G__Q_2.pdf).
The maintained writeup is published at <https://roed314.github.io/gq2/>. Because that writeup may
be reorganized, documentation should prefer semantic paper identifiers and Lean declaration names
over displayed theorem numbers.

## Review and validation

| File | Purpose |
|---|---|
| [`atlas.md`](atlas.md) | Explains Lean Atlas, the Lean Compass semantic-review cone, the separate kernel axiom check, and how to regenerate `atlas-audit.md`. |
| [`paper-api.md`](paper-api.md) | Defines the stable paper-to-Lean API policy using semantic HTML ids and `data-lean-ref` declarations. |
| [`literature-axioms-onepage.md`](literature-axioms-onepage.md) | One-page expert checklist for the nine external mathematical inputs. |
| [`literature-axioms.md`](literature-axioms.md) | Full statements, citations, encoding choices, and verification discussion for the literature inputs. |
| [`adversarial-axioms-review.md`](adversarial-axioms-review.md) | Dated adversarial review of whether the Lean axiom interfaces are supported by the cited sources. Later census decisions are called out explicitly rather than silently rewriting the historical findings. |
| [`angdinata-review-plan.md`](angdinata-review-plan.md) | Response plan for an external four-point review of the axiom interfaces: the verdict on each point, the state of cup products in Mathlib and FLT, and the resulting work items. |
| [`foundations-audit.md`](foundations-audit.md) | Dated survey of which required foundations existed in the pinned Mathlib revision and which gaps had to be filled locally. |
| [`mathlib-cft-survey.md`](mathlib-cft-survey.md) | Dated inventory of relevant Mathlib and ClassFieldTheory APIs. It is a dependency-snapshot document, not a claim about newer upstream versions. |
| [`cts-cohomology-gap.md`](cts-cohomology-gap.md) | Describes the homogeneous/inhomogeneous continuous-cohomology interface gap and the explicit low-degree model used by this project. |

## Paper fidelity and mathematical design

| File | Purpose |
|---|---|
| [`paper-errata.md`](paper-errata.md) | Consolidated corrections, implicit hypotheses, fragile passages, and positive confirmations discovered by formalization. This is the main input for revising the paper. |
| [`erratum-h0-transcription.md`](erratum-h0-transcription.md) | Detailed forensic record of the dropped `d₀` factor in the first Lean transcription and its completed repair. |
| [`off-path-statements.md`](off-path-statements.md) | Paper results proved in Lean but not used by the final capstone dependency route. |
| [`section3-extraction.md`](section3-extraction.md) | Paper §3 statement crosswalk, absorptions, and resolved encoding deviations. |
| [`section67-extraction.md`](section67-extraction.md) | Paper §§6–7 statement/display crosswalk and the mathematical amendments exposed by proof. |
| [`section8-extraction.md`](section8-extraction.md) | Paper §8 crosswalk and the corrections needed for the affine-lifting and recursion argument. |
| [`section9-extraction.md`](section9-extraction.md) | Paper §9 crosswalk and architecture of the terminal, block, and induction lanes. |
| [`section10-extraction.md`](section10-extraction.md) | Paper §10 crosswalk for tame-frame exhaustion, equation (154), and the count-form capstone. |
| [`tickets.md`](tickets.md) | Concise proof-development history retained at its established path; it summarizes the mathematical route without acting as a live ticket board. |

## The Γ_R (Roe-candidate) campaign

A follow-on campaign, not part of the paper, verifies a *second* 4-generator 2-relator
candidate presentation `Γ_R` against the same finite-target machinery. Its terminal theorem
`GQ2.main_presentation_literal_roe_unconditional` is sorry-free, adds no axiom, and (since
2026-07-26) carries no hypothesis: the one explicit binder it used to have, `BLabHypothesis`, is
now the in-repo theorem `GQ2.Roe.Labute.bLab`, proved at the standard three axioms — see the "B3
addendum" of [`literature-axioms.md`](literature-axioms.md) for the statement, the proof chain,
and the decision record.

| File | Purpose |
|---|---|
| [`roe-campaign-summary.md`](roe-campaign-summary.md) | **Start here.** The mathematical story in two pages: what `Γ_R` is, why the explicit-identification route is impossible, the route actually taken, the `SourceData` interface refactor, and exactly what the capstone rests on. |
| [`orchestration/roe-verification-plan.md`](orchestration/roe-verification-plan.md) | Live. The campaign plan, preceded by a dated status block recording the outcome against it — routes taken, actuals against the estimate, and the state of the follow-on Labute campaign. |
| [`orchestration/roe-tickets.md`](orchestration/roe-tickets.md) | Live. The ticket board: every ticket with its owned files, dependencies, landing commit, and the discoveries that changed later tickets. The provenance record for the whole campaign. |
| [`roe-verso-chunk.md`](roe-verso-chunk.md) | Prepared-not-applied blueprint chunk for the project site: the Verso markup for the `Γ_R` theorems in the site's own conventions, plus integration and build instructions. Nothing in it has been deployed. |
| [`orchestration/roe-r2-spike.md`](orchestration/roe-r2-spike.md) | Why no explicit word identification of the two pro-2 quotients exists — an impossibility theorem, with the independent re-derivation of the note's orientation numerics. |
| [`orchestration/roe-r7-design.md`](orchestration/roe-r7-design.md) | The frozen statements of the pro-2 identification lane, and the first draft of the classification interface later declined as an axiom. |
| [`orchestration/roe-r13b-plan.md`](orchestration/roe-r13b-plan.md) | Route for the degree-2 word-cohomology bridge that makes `D_R` Demushkin, including the machine-checked cup–Bockstein matrix. |
| [`orchestration/roe-r20-recon.md`](orchestration/roe-r20-recon.md) | Where the §5 duality scaffolding is generic in the relator and where it is not; the evidence behind the decision to clone the dévissage tree rather than generalize frozen code. |
| [`orchestration/roe-r30-recon.md`](orchestration/roe-r30-recon.md) | How the `SourceData` field list was read off the proof-time uses of Theorem 4.2, with the refactor's regression gates. |
| [`orchestration/roe-r31-survey-ii34.md`](orchestration/roe-r31-survey-ii34.md) | Supply survey: lift multiplicity, the half-torsor, and the shared obstruction layer. |
| [`orchestration/roe-r31-survey-stage-ii5.md`](orchestration/roe-r31-survey-stage-ii5.md) | Supply survey: the display-(136) stage obligation and its cover-lift kernel. |
| [`orchestration/roe-r31-survey-ii6.md`](orchestration/roe-r31-survey-ii6.md) | Supply survey: the display-(140) residues, and the private helpers a second source has to restate. |
| [`orchestration/roe-r31-survey-gaussz.md`](orchestration/roe-r31-survey-gaussz.md) | Supply survey: the Gauss-`Z` layer, plus the specification of the shared word substrate that unblocked the rest. |
| [`orchestration/labute-plan.md`](orchestration/labute-plan.md) | Comparison of the available proof routes for the classification instance, with a page-verified literature survey and the recommended levelwise route. |
| [`orchestration/labute-spike.md`](orchestration/labute-spike.md) | The computational de-risking evidence: what the naive argument gets wrong, the congruence invariant that repairs it, and the control experiment showing the invariant is necessary. |
| [`orchestration/labute-l1-design.md`](orchestration/labute-l1-design.md) | Statement freeze for the Lean skeleton, with per-ticket proof sketches and the deviations taken against the spike. |

## Generated and structured metadata

Several important review artifacts live at repository root because external tools expect them
there:

- [`../formalization.yaml`](../formalization.yaml) — structured provenance, fidelity, automation,
  alignment, and review metadata;
- [`../comparator-config.json`](../comparator-config.json) with [`../Challenge.lean`](../Challenge.lean)
  and [`../Solution.lean`](../Solution.lean) — the Comparator validation pair;
- [`../atlas-audit.md`](../atlas-audit.md) — committed, regenerated Lean Compass and kernel-axiom
  report;
- [`../scripts/check_axioms.sh`](../scripts/check_axioms.sh) — the primary gate: axiom census,
  `sorry`/`native_decide` hygiene, and the per-capstone expected-axiom audit;
- [`../scripts/atlas_audit.py`](../scripts/atlas_audit.py) and
  [`../scripts/paper_api_audit.py`](../scripts/paper_api_audit.py) — report generators;
- [`../scripts/roe_sanity_counts.py`](../scripts/roe_sanity_counts.py) — independent
  finite-quotient count check for the `Γ_R` admissible-marking semantics.

## Historical orchestration archive

[`orchestration/`](orchestration/) preserves the plans, handoffs, counterexamples, and design
records produced during the July 2026 agent-assisted formalization. These files often contain
valuable mathematical reasoning, but words such as “open”, “blocked”, “remaining”, and “sorried”
describe the moment when the note was written. They must not be used as a current ledger — with
the two exceptions named above, `roe-tickets.md` and `roe-verification-plan.md`, which are the
live board and plan of the Γ_R campaign.

The archive's [`README.md`](orchestration/README.md) lists every retained file and explains its
historical role. Current truth comes from the Lean sources and mechanical gates:

```sh
lake build
bash scripts/check_axioms.sh
lake env lean GQ2/AxiomLedger.lean
python3 scripts/atlas_audit.py atlas-graph.json
```
