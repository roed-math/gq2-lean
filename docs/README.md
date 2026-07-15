# Documentation guide

The documentation is organized by review task. Files at the top level of `docs/` are maintained
mathematical or technical references. `docs/orchestration/` is a historical archive of the agent
workflow that produced the proof; it is useful for provenance and design rationale, but its ticket
states are not current project status.

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

## Generated and structured metadata

Several important review artifacts live at repository root because external tools expect them
there:

- [`../formalization.yaml`](../formalization.yaml) — structured provenance, fidelity, automation,
  alignment, and review metadata;
- [`../comparator-config.json`](../comparator-config.json) with [`../Challenge.lean`](../Challenge.lean)
  and [`../Solution.lean`](../Solution.lean) — the Comparator validation pair;
- [`../atlas-audit.md`](../atlas-audit.md) — committed, regenerated Lean Compass and kernel-axiom
  report;
- [`../scripts/atlas_audit.py`](../scripts/atlas_audit.py) and
  [`../scripts/paper_api_audit.py`](../scripts/paper_api_audit.py) — report generators.

## Historical orchestration archive

[`orchestration/`](orchestration/) preserves the plans, handoffs, counterexamples, and design
records produced during the July 2026 agent-assisted formalization. These files often contain
valuable mathematical reasoning, but words such as “open”, “blocked”, “remaining”, and “sorried”
describe the moment when the note was written. They must not be used as a current ledger.

The archive's [`README.md`](orchestration/README.md) lists every retained file and explains its
historical role. Current truth comes from the Lean sources and mechanical gates:

```sh
lake build
bash scripts/check_axioms.sh
lake env lean GQ2/AxiomLedger.lean
python3 scripts/atlas_audit.py atlas-graph.json
```
