# Historical agent-orchestration archive

This directory preserves the process artifacts of the July 2026 formalization: ticket boards,
plans, scoping notes, rejected routes, counterexamples, design documents, and handoffs. It is an
archive, not a current coordination surface. Status words in these files describe the state when a
note was written and may be contradicted by later notes in the same file.

The archive remains useful because it records why statement hypotheses changed, which tempting
generalizations are false, where the paper supplied implicit data, and how difficult proof seams
were decomposed. Mathematical explanations and source references have therefore been retained even
when their surrounding project-management prose is historical.

For current truth use the Lean sources, [`../../formalization.yaml`](../../formalization.yaml),
[`../../atlas-audit.md`](../../atlas-audit.md), and the repository gates. The maintained
documentation index is [`../README.md`](../README.md).

## Global plans, boards, and review packets

| File | Historical role |
|---|---|
| [`SESSION-LOG.md`](SESSION-LOG.md) | Chronological autonomous-session log, including early foundation work and discovered soundness issues. |
| [`STATUS.md`](STATUS.md) | Early status ledger; superseded as a source of current state. |
| [`formalization-plan.md`](formalization-plan.md) | Initial plan for replacing or isolating the literature inputs. |
| [`step2-plan.md`](step2-plan.md) | Plan for proving the paper's theorem from the statement layer and approved axioms. |
| [`tickets-step1.md`](tickets-step1.md) | Archived board for formalizing the paper and literature statements. |
| [`tickets.md`](tickets.md) | Raw proof-stage board with its complete row history and axiom budgets. |
| [`proof-architecture.md`](proof-architecture.md) | Proof DAG and the intended mathematical role of each major layer. |
| [`review-packet.md`](review-packet.md) | External-review packet for the then-current axiom and deviation inventory. |
| [`orbit-data-refactor.md`](orbit-data-refactor.md) | Design for the orbit-data refactor that unblocked later §6 splices. |

## Post-completion axiom-discharge campaigns

| File | Historical role |
|---|---|
| [`b7prime-proof-plan.md`](b7prime-proof-plan.md) | Plan for proving the explicit dyadic Hilbert-symbol formula in Lean. |
| [`b7prime-tickets.md`](b7prime-tickets.md) | Board for the B7′ discharge. |
| [`b7prime-b34-coordination.md`](b7prime-b34-coordination.md) | Coordination note for the parallel B7′ proof lanes. |
| [`b11b-proof-plan.md`](b11b-proof-plan.md) | Plan for proving that units are norms in an unramified quadratic dyadic extension. |
| [`b11b-tickets.md`](b11b-tickets.md) | Board for the B11b discharge. |
| [`b12-proof-plan.md`](b12-proof-plan.md) | Plan for proving Kummer-class surjectivity. |
| [`b12-tickets.md`](b12-tickets.md) | Board for the B12 discharge. |
| [`b13-proof-plan.md`](b13-proof-plan.md) | Plan for constructing the dyadic unit filtration. |
| [`b13-tickets.md`](b13-tickets.md) | Board for the B13 discharge. |

## §5 and §6 local-arithmetic design

| File | Historical role |
|---|---|
| [`p13-normal-form-hypothesis-gap.md`](p13-normal-form-hypothesis-gap.md) | Diagnosis of the missing pro-2 wild-core hypothesis in the §5 normal-form and duality statements. |
| [`p13-ticket-split.md`](p13-ticket-split.md) | Parallel decomposition of the §5 proof work. |
| [`p15b-field-core-scoping.md`](p15b-field-core-scoping.md) | Scope of the remaining finite-field and field-core work. |
| [`p15f-handoff.md`](p15f-handoff.md) | Handoff for the two halves of Lemma 6.17 and their final count. |
| [`p15f1-axiom-proposal.md`](p15f1-axiom-proposal.md) | Candidate external interfaces considered for the Lemma 6.17 dimension half. |
| [`p15f1-dimcount-scoping.md`](p15f1-dimcount-scoping.md) | Focused analysis of the deep-half cardinality. |
| [`p15f1-leaf-candidates.md`](p15f1-leaf-candidates.md) | Precise possible leaf statements and citations considered during that analysis. |
| [`p15f1-scoping.md`](p15f1-scoping.md) | Initial scope for the dimension half of Lemma 6.17. |
| [`p15f2-handoff.md`](p15f2-handoff.md) | Handoff for the vanishing half of Lemma 6.17. |
| [`p15f2-option1-scoping.md`](p15f2-option1-scoping.md) | Analysis of the orbit-decomposition route to vanishing. |
| [`p15f2-scoping.md`](p15f2-scoping.md) | Initial vanishing-theorem scope. |
| [`p15f2-subtickets.md`](p15f2-subtickets.md) | Parallel decomposition of the vanishing proof. |
| [`p15f2b-foundation-notes.md`](p15f2b-foundation-notes.md) | Landed orbit-route foundation and its reusable lemmas. |
| [`p15f2c-design.md`](p15f2c-design.md) | Shapiro-coordinate and scalar-deepness design record. |
| [`p15f2c2c-scoping.md`](p15f2c2c-scoping.md) | Scope for the unramified equal-value-group lemma. |
| [`p15f2c2c-handoff.md`](p15f2c2c-handoff.md) | Handoff for that analytic lemma. |
| [`p15f2d-handoff.md`](p15f2d-handoff.md) | Final assembly handoff for `lemma_6_17_vanish`. |
| [`p15f4-plan.md`](p15f4-plan.md) | Plan for the faithful-image projectivity theorem behind Lemma 6.11. |
| [`p15f7-axiom-proposal.md`](p15f7-axiom-proposal.md) | Considered K-level duality inputs and the decision about what to prove locally. |
| [`p15i-transgression-gap.md`](p15i-transgression-gap.md) | Diagnosis and repair of the dropped fixed-`κ⁰_q` hypothesis in Lemma 6.21. |

## §8 recursion and Gauss-sum design

| File | Historical role |
|---|---|
| [`p16-ticket-split.md`](p16-ticket-split.md) | Decomposition of the §8 proof into independently executable lanes. |
| [`p16c3-recon.md`](p16c3-recon.md) | Reconnaissance and blueprint for the §8 obstruction construction. |
| [`p16d2-plan.md`](p16d2-plan.md) | Reduction and construction plan for the `R`-stage obstruction module. |
| [`p16d4-plan.md`](p16d4-plan.md) | Plan for affine `T`-lifting, Lemma 8.7, and Proposition 8.8. |
| [`p16d6-concrete-spec.md`](p16d6-concrete-spec.md) | Exact source-specific obligations needed to instantiate Proposition 8.9. |
| [`p16d6-plan.md`](p16d6-plan.md) | Overall two-source splice plan for Proposition 8.9. |
| [`p16d6a-handoff.md`](p16d6a-handoff.md) | Handoff for the concrete `R`-stage obstruction datum. |
| [`p16d6b-handoff.md`](p16d6b-handoff.md) | Handoff for source-independence of the `T`-cocycle multiplicity. |
| [`p16d6c-handoff.md`](p16d6c-handoff.md) | Handoff for the display-(140) core. |
| [`p16d6c-keystone-design.md`](p16d6c-keystone-design.md) | Complete design record for the keystone (140) calculation. |
| [`p16d6d-handoff.md`](p16d6d-handoff.md) | Local-source handoff for display (139). |
| [`p16d6d-hMcount-handoff.md`](p16d6d-hMcount-handoff.md) | Focused handoff for the unrestricted `M`-lift cardinality. |
| [`p16d6e-assembly-plan.md`](p16d6e-assembly-plan.md) | Assembly plan and record of statement corrections to Proposition 8.9. |
| [`p16d6e-handoff.md`](p16d6e-handoff.md) | Handoff for the `Γ_A` display-(136) residues. |
| [`p16d6e4-gauss-design.md`](p16d6e4-gauss-design.md) | Design for transporting the source Gauss sum from cocycles to cohomology. |
| [`p16d6e4a-evaluation-design.md`](p16d6e4a-evaluation-design.md) | Design for the paper's display-(83) evaluation seam. |
| [`p16d6e4aA-a4-prep.md`](p16d6e4aA-a4-prep.md) | Paper reread and resolution of the A-4 watch item. |
| [`p16d6e4aA-gammaA-gauss-design.md`](p16d6e4aA-gammaA-gauss-design.md) | Candidate-source Gauss evaluation route. |
| [`p16d6e4aA-p4-tame-package.md`](p16d6e4aA-p4-tame-package.md) | Refuted tame-package derivation and the resulting head-inflation redesign. |
| [`p16d6e4aA-p4d-handoff.md`](p16d6e4aA-p4d-handoff.md) | Handoff for the two `blockEnrichmentD` source constructions. |
| [`p16d6e4aA-pack-design.md`](p16d6e4aA-pack-design.md) | Design of the ramified isotypic package. |
| [`p16d6e4aAP-handoff.md`](p16d6e4aAP-handoff.md) | Endgame handoff for the `Γ_A` Gauss-`Z` family. |
| [`p16d6e5-plan.md`](p16d6e5-plan.md) | Design for the remaining `Γ_A` display-(136) residues. |

## §9 induction and §10 exhaustion

| File | Historical role |
|---|---|
| [`p17b3-plan.md`](p17b3-plan.md) | Terminal-case correspondence design. |
| [`p17d2-handoff.md`](p17d2-handoff.md) | Handoff for constructing the concrete block enrichment. |
| [`p17e-kappa0-scoping.md`](p17e-kappa0-scoping.md) | Counterexample-driven correction of `kappa0_exists` to the paper's simple tame setting. |
| [`p17e4-handoff.md`](p17e4-handoff.md) | Reduction of the ramified Lemma 6.11 case to an involution fixed-point bound. |
| [`p17e5-plan.md`](p17e5-plan.md) | Normal-form and final assembly plan for `kappa0_exists`. |
| [`p17i-handoff.md`](p17i-handoff.md) | Handoff for the strong-induction proof of Theorem 4.2. |
| [`p18-plan.md`](p18-plan.md) | Plan for tame-frame exhaustion, equation (154), and the count capstone. |
| [`p25-tame-reciprocity-plan.md`](p25-tame-reciprocity-plan.md) | Plan for deriving the tame reciprocity interface from the local reciprocity bundle. |

Every Markdown file retained in this directory appears in the tables above. Code comments may link
directly to an archived design record when it gives the clearest explanation of a statement
correction or counterexample; such a link is documentary provenance, not a claim that the file's
task state remains live.
