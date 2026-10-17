# Documentation guide

The documentation is organized by review task. Files at the top level of `docs/` are maintained
mathematical or technical references. `docs/orchestration/` is a historical archive of the agent
workflow that produced the proof; it is useful for provenance and design rationale, but its ticket
states are not current project status. Two files in that directory are the exception and are
live until the campaign's owner gate G2 is recorded:
[`orchestration/tauceti-tickets.md`](orchestration/tauceti-tickets.md) and
[`orchestration/tauceti-proof-plan.md`](orchestration/tauceti-proof-plan.md), the board and plan
of the campaign that proved the nine literature inputs from the Tau Ceti library (the earlier
Γ_R board and plan were archived on 2026-07-26).

**Current state (2026-10-17):** the library contains no `axiom` declaration (census 0). The nine
literature inputs that were axioms until then are proved from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) (revision `706344c35`) by the adapters in
`GQ2/TauCeti/`; their legacy names and statements are kept in
`GQ2/Foundations/TauCetiInstance.lean`, and every declaration under `GQ2` is at the standard three
axioms. See the Tau Ceti section below.

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
| [`literature-axioms-onepage.md`](literature-axioms-onepage.md) | One-page expert checklist for the nine external mathematical inputs, each with the Tau Ceti source and gq2 adapter that proves it. |
| [`literature-axioms.md`](literature-axioms.md) | Full statements, citations, encoding choices, and verification discussion for the literature inputs, and (since 2026-10-17) how each is proved from Tau Ceti. |
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

## The Tau Ceti discharge campaign

The nine literature inputs (B1, B3c, B5, B6, B7, B8, B9, B10, B11a) were the project's only axioms.
In October 2026 each was proved from the Tau Ceti library, and the axiom file was deleted
(census 9 → 0, owner gate G1, 2026-10-17). The trust base is now Lean's standard three axioms plus
Tau Ceti's proofs at the pinned revision (owner gate G0).

| File | Purpose |
|---|---|
| [`orchestration/tauceti-proof-plan.md`](orchestration/tauceti-proof-plan.md) | Live until G2. The plan: platform decisions, the axiom-by-axiom map to Tau Ceti, assembly and census flip. |
| [`orchestration/tauceti-tickets.md`](orchestration/tauceti-tickets.md) | Live until G2. The ticket board with each ticket's landing commit. |
| [`orchestration/tauceti-t2-recon.md`](orchestration/tauceti-t2-recon.md) | The recon memo: exact Tau Ceti signatures, instance needs, the cross-cutting hazards (unexposed Tau Ceti definitions, instance-search timeouts, separable vs algebraic closure) and the corrections to the plan. |
| [`orchestration/tauceti-t2-evidence/`](orchestration/tauceti-t2-evidence/README.md) | The recon's scratch prototypes and probes (outside every `lean_lib`). |
| `../GQ2/TauCeti/` | The adapters (one file per input, plus the dictionaries `GaloisDict`, `CohomologyDict`, `ProPDict`, `StiefelWhitneyDict`, `DualizingGroup`), `Instance.lean` (the bundle) and `Main.lean` (the four `*_tauceti` capstones). |

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
- [`../scripts/check_axioms.sh`](../scripts/check_axioms.sh) — the primary gate: axiom census
  (now 0), `sorry`/`native_decide` hygiene, the per-capstone expected-axiom audit (every capstone at
  exactly the standard three), and the Palomar and Tau Ceti import-closure audits
  ([`../GQ2/PalomarAxiomAudit.lean`](../GQ2/PalomarAxiomAudit.lean),
  [`../GQ2/TauCetiAxiomAudit.lean`](../GQ2/TauCetiAxiomAudit.lean));
- [`../scripts/atlas_audit.py`](../scripts/atlas_audit.py) and
  [`../scripts/paper_api_audit.py`](../scripts/paper_api_audit.py) — report generators;
- [`../scripts/roe_sanity_counts.py`](../scripts/roe_sanity_counts.py) — independent
  finite-quotient count check for the `Γ_R` admissible-marking semantics.

## Historical orchestration archive

[`orchestration/`](orchestration/) preserves the plans, handoffs, counterexamples, and design
records produced during the July 2026 agent-assisted formalization. These files often contain
valuable mathematical reasoning, but words such as “open”, “blocked”, “remaining”, and “sorried”
describe the moment when the note was written. They must not be used as a current ledger — with
the two exceptions named above, `tauceti-tickets.md` and `tauceti-proof-plan.md`, which stay live
until the Tau Ceti campaign's G2 is recorded (the Γ_R campaign's `roe-tickets.md` and
`roe-verification-plan.md` were archived on 2026-07-26).

The archive's [`README.md`](orchestration/README.md) lists every retained file and explains its
historical role. Current truth comes from the Lean sources and mechanical gates:

```sh
lake build        # with the Tau Ceti cache variables set (see README.md); otherwise Tau Ceti's
                  # import closure is compiled from source
bash scripts/check_axioms.sh
lake env lean GQ2/AxiomLedger.lean
lake env lean GQ2/TauCetiAxiomAudit.lean
python3 scripts/atlas_audit.py atlas-graph.json
```
