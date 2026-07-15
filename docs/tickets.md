# Proof development history

This file is retained at its established path because Lean docstrings and historical notes refer to
it. It is no longer a ticket board. The formalization is complete; current status is determined by
the Lean sources and the repository's mechanical checks, not by archived task labels.

The raw agent-orchestration boards, plans, and handoffs are preserved under
[`orchestration/`](orchestration/). They record useful design decisions and failed approaches, but
their words “open”, “remaining”, and “sorried” describe intermediate states in July 2026.

## Final proof route

| Mathematical stage | Principal Lean declarations | Current modules |
|---|---|---|
| Candidate profinite group and finite markings | `GammaA`, `Marking.Admissible`, `prop_2_3` | `GQ2/GammaA.lean`, `GQ2/Words.lean`, `GQ2/Prop23.lean` |
| §3 boundary comparison | `boundaryMapsWitness`, `prop_3_2_gammaA`, `prop_3_2_local` | `GQ2/BoundaryMapsWitness.lean`, `GQ2/Prop32.lean` |
| §§4–5 framed lifting and Fox–Heisenberg calculations | `BoundaryFrame`, `prop_5_8_left`, `prop_5_8_right`, `prop_5_16_bundle` | `GQ2/BoundaryFrame.lean`, `GQ2/FoxHeisenberg/`, `GQ2/LocalLiftingDuality.lean` |
| §§6–7 quadratic and block theory | `lemma_6_17_vanish_final`, `prop_6_18_ramified`, `exists_minimalBlock` | `GQ2/VanishClose.lean`, `GQ2/DetRamified.lean`, `GQ2/SectionSeven/` |
| §8 closed recursion | `prop_8_9` | `GQ2/Prop89Close.lean` and the `GQ2/SectionEight/` support modules |
| §9 induction | `terminal_count_eq`, `thm_4_2`, `thm_4_2_stratum` | `GQ2/SectionNine/`, `GQ2/ThmFourTwo.lean` |
| §10 exhaustion and equation (154) | `lemma_10_1`, `eq_154`, `main_surjection_count'` | `GQ2/SectionTen.lean`, `GQ2/SectionTenSources.lean` |
| Profinite reconstruction | `main_presentation_literal` | `GQ2/Reconstruction.lean`, `GQ2/PresentationLiteral.lean` |

The final deliverables are:

- `GQ2.main_presentation_literal`, the literal profinite-group isomorphism;
- `GQ2.SectionTen.main_surjection_count'`, the finite surjection-count identity;
- `GQ2.thm_4_2`, the per-boundary-frame equality driving the §9 induction;
- `GQ2.SectionEight.prop_8_9`, the closed-recursion theorem.

## The main engineering bottlenecks

The proof did not close by translating the paper line by line. Several parts required new Lean
infrastructure or a more explicit formulation.

1. **Continuous cohomology.** The project uses explicit inhomogeneous low-degree cochains because
   the pinned Mathlib continuous-cohomology API does not expose the required concrete degree-one
   and degree-two model. The precise interface gap is documented in
   [`cts-cohomology-gap.md`](cts-cohomology-gap.md).
2. **The deep-unit vanishing theorem.** `lemma_6_17_vanish_final` was assembled from Shapiro
   coordinates, Kummer theory, unit-filtration duality, and the involution calculation. The
   formal proof made the unramified equal-value-group input and the fixed equivariant class
   explicit.
3. **The §8 recursion.** The first direct translation obscured multiplicity factors in displays
   (132), (137), and (140). The final design separates the recursion interface from the two source
   constructions and records the corrected factors in [`section8-extraction.md`](section8-extraction.md)
   and [`paper-errata.md`](paper-errata.md).
4. **The ramified Gauss count.** The last difficult local result was
   `zeroCount_qDouble_ramified_of_faithful`. Its proof uses a single-isotype package, characteristic-2
   Frobenius, semilinear descent, and a count of the 2-primary projection. The implementation is now
   split between `GQ2/RamifiedPack/` and `GQ2/GaussZ/FinalGammaA/`.
5. **Reconstruction.** Equality of finite surjection counts must be interpreted as equality of
   cardinalities, followed by the finitely generated profinite Hopfian argument. The formalization
   found and repaired the ambiguous stronger reading; see [`paper-errata.md`](paper-errata.md).

## How the final gaps closed

The §8 recursion first closed in `GQ2/Prop89Close.lean` with its source-Gauss values isolated as
explicit ledger hypotheses. Those hypotheses were then discharged on the `GammaA` side through the
block-`D` route in `GQ2/GaussZ/GammaAD.lean`. The remaining ramified zero-count theorem closed via
the ramified isotypic pack described above. In parallel, the §6 Shapiro/Kummer lane completed
`lemma_6_17_vanish_final` without introducing another axiom.

This left a proof with no `sorryAx`; `GQ2/AxiomLedger.lean` now reports only the standard three Lean
axioms and the nine declared literature inputs.

## Trust-base reduction after proof completion

The initial complete proof used fifteen literature axioms. Six were subsequently removed from the
trust base without changing the public theorem statements:

- unused B2 (cyclotomic surjectivity) and B4 (a standalone Demushkin presentation) were deleted;
- B7′ (`hilbertSymbol_dyadic`) was proved from 2-adic square calculations and the explicit Hilbert
  symbol formula;
- B11b (`unramifiedQuadratic_units_are_norms`) was proved by a unit-filtration approximation;
- B12 (`kummerClassK_surjective`) was proved using the in-repository Kummer/Krull bridge;
- B13 (`dyadicUnitFiltration`) was constructed from the local-field filtration and residue-field
  counts.

The resulting census is nine. Every remaining literature axiom is consumed by the capstone. Exact
statements and citations are in [`literature-axioms.md`](literature-axioms.md), and the live consumer
graph is produced by `GQ2/AxiomLedger.lean`.

## Post-completion maintenance

The cleanup pass removed superseded scaffolding, narrowed imports, privatized implementation
helpers, added documentation and licensing headers, and split the largest modules behind stable
public import umbrellas. The paper-facing public declaration set was checked before and after the
split and remained unchanged.

The maintained review surfaces are [`../formalization.yaml`](../formalization.yaml),
[`../atlas-audit.md`](../atlas-audit.md), [`paper-api.md`](paper-api.md), and the axiom gates. For the
full historical process record, use the indexed archive in
[`orchestration/README.md`](orchestration/README.md).
