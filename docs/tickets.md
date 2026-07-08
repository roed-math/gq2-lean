# GQ2 formalization — ticket summary (human-readable board)

**The proof is complete.**  Theorem 1.2 of *A profinite presentation for `G_{ℚ₂}`* is
formalized end-to-end: the literal statement

> `GQ2.main_presentation_literal : Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)`

is proved in [`GQ2/PresentationLiteral.lean`](../GQ2/PresentationLiteral.lean), together with
the counting capstone `main_surjection_count'` (`#(continuous surjections G_{ℚ₂} ↠ G) =
admissibleCount G`, [`GQ2/SectionTenSources.lean`](../GQ2/SectionTenSources.lean)).  The
library is **fully `sorry`-free** (guard: [`scripts/check_axioms.sh`](../../scripts/check_axioms.sh),
allowlist emptied 2026-07-08) and rests on the **frozen 15-axiom census** of
[`GQ2/Foundations/Axioms.lean`](../GQ2/Foundations/Axioms.lean) — every theorem is
`#print axioms` ⊆ std-3 ∪ its declared B-leaves.  The capstone's trust base (12 of the 15
axioms) and its 30-node semantic review cone are machine-generated in
[`atlas-audit.md`](../atlas-audit.md).

This file is the **human-readable summary** of the ticket system that produced the proof
(2026-07-02 → 2026-07-08, a swarm of parallel Fable/Opus agents).  The raw orchestration
board — 132 rows with full per-row history, acceptance criteria, and axiom budgets — is
archived verbatim at [`orchestration/tickets.md`](orchestration/tickets.md); per-lane plans,
scopings, designs, and handoffs are the `orchestration/p*.md` files (see
[`orchestration/README.md`](orchestration/README.md), including the note that code comments
still cite the old `docs/<name>.md` paths).

## Where things stand (final audit, 2026-07-08)

| Deliverable | Lean name | File | Axioms beyond std-3 |
|---|---|---|---|
| **Theorem 1.2 (literal)** | `main_presentation_literal` | `GQ2/PresentationLiteral.lean` | B1 + Track B (12 leaves total) |
| Theorem 1.2 (count form) | `main_surjection_count'` | `GQ2/SectionTenSources.lean` | 12 leaves (see `atlas-audit.md` §2) |
| eq. (154) | `eq_154` | `GQ2/SectionTenSources.lean` | via `thm_4_2` |
| Theorem 4.2 (per frame) | `thm_4_2`, `thm_4_2_stratum` | `GQ2/ThmFourTwo.lean` | B1, B3c, B6, B7, B7′, B8, B9, … |
| Prop 8.9 (closed recursion) | `prop_8_9` | `GQ2/Prop89Close.lean` | B6, B7 |
| Lemma 6.17 (vanish) | `lemma_6_17_vanish_final` | `GQ2/VanishClose.lean` | (see file) |

Notes:
- **Axiom census 15** (B1, B2, B3c, B4, B5, B6, B7, B7′, B8, B9, B10′, B11a, B11b, B12, B13);
  literature justification in [`literature-axioms.md`](literature-axioms.md) (+ one-page form),
  adversarial review in [`adversarial-axioms-review.md`](adversarial-axioms-review.md).
  Two axioms (`absGalQ2_maxProTwo_presentation`, `cyclotomicCharacter_two_surjective`) are
  consumed by **no** deliverable — kept because the census is frozen.
- **Zero `sorry`s anywhere**; no `native_decide`; `axiom` only in `Foundations/Axioms.lean`.
- Paper statements proved but **off** the main path are catalogued in
  [`off-path-statements.md`](off-path-statements.md) (kept for the paper rewrite).
- 2026-07-08 **post-completion prune**: ~5,000 lines of superseded agent scaffolding deleted
  (7 whole files + parts of 81), the unused `ClassFieldTheory` Lake dependency dropped.
  Statement-level content and the off-path paper statements were preserved.

## Reading the tables

**Status** ☑ = closed (all proofs `#print axioms`-verified at close) · ✂ = superseded /
not needed (route refuted or absorbed elsewhere).  **Model**: F = Fable (design-heavy),
O = Opus (well-specified).  Dates are 2026-07.  Sub-tickets that lived only in handoff/plan
files are included — the "Ref" column names the `orchestration/` file with the full story
where one exists.

## Phase 0 — meta, guards, foundations

| ID | Delivered | Where | Status |
|---|---|---|---|
| P-00 | step-2 plan + board + tooling | `orchestration/step2-plan.md` | ☑ 07-03 |
| P-01 | STATUS refresh + repo-wide axiom ledger (batch `#print axioms`) | `GQ2/AxiomLedger.lean` | ☑ 07-03 |
| P-20 | review packet v3 (interior-node statements, App. D certificate diff, citation table) | `orchestration/review-packet.md` | ☑ 07-05 |
| P-21 | ℤ₂-powering on pro-2 groups (`maxPro2(ℤ̂) ≅ ℤ₂`, unit/odd-power bijectivity) | `GQ2/ZtwoPowering.lean`, `GQ2/FrattiniCriterion.lean` | ☑ 07-03 |
| P-22 | axiom documentation pass (adversarial-review recs 1/3/4/6) | `GQ2/Foundations/Axioms.lean` docstrings | ☑ 07-05 |
| P-23 | B11 split into B11a/B11b (census 12→13, user-approved) | `GQ2/Foundations/Axioms.lean` | ☑ 07-04 |
| P-24 | guard hardening: untracked-file WARN + scratch conventions | `scripts/check_axioms.sh` | ☑ 07-05 |

## Track A — the `Γ_A` side (§2)

| ID | Delivered | Where | Status |
|---|---|---|---|
| P-02 | `exists_contSurj_of_card_le` (cofiltered system + compactness) | `GQ2/Reconstruction.lean` | ☑ 07-03 |
| P-03 | topological finite generation: `FreeProfiniteGroup`, quotients, `Γ_A` t.f.g. | `GQ2/FinitelyGenerated.lean` | ☑ 07-03 |
| P-04 | universal marking admissible-in-the-limit | — | ☑ 07-03 |
| P-05 | **Prop 2.3**: `#ContSurj(Γ_A, G) = admissibleCount G` | `GQ2/Prop23.lean` | ☑ 07-03 |

## §3 — boundary construction

| ID | Delivered | Where | Status |
|---|---|---|---|
| P-06 | §3 statement extraction (Lemmas 3.4–3.8, Prop 3.2, Prop 1.1) | `docs/section3-extraction.md` | ☑ 07-03 |
| P-07 | Lemmas 3.4/3.5 (eq. (13) ledger; square-class basis, cup form) | `GQ2/SectionThree.lean` | ☑ 07-03 |
| P-08 | Lemmas 3.6–3.8 (cyclotomic conjugation of peripherals; wild-relation shape) | — | ☑ 07-03 |
| P-09 | **Prop 3.2**: common tame quotient (both sides) | `GQ2/Prop32.lean`, `GQ2/TameQuotient.lean` | ☑ 07-03 |
| P-10 | **Prop 1.1**: marked dyadic Demushkin normalization, `ν_ur = (−2,1,0)` | `GQ2/Demushkin.lean` area | ☑ 07-03 |
| P-25 | §3-marked closes: `prop_3_10_gammaA` + `prop_3_10_local_marked` + `prop_3_14` (21-field `BoundaryMaps` witness; B10→B10′ strengthening, user-approved) | `GQ2/SectionThreeMarked.lean`, `GQ2/BoundaryMapsWitness.lean` | ☑ 07-06 |

## §§4–5 — boundary frames and the Fox–Heisenberg complex

| ID | Delivered | Where | Status |
|---|---|---|---|
| P-11 | §4 design: boundary-framed marked targets + **Thm 4.2 statement** | `GQ2/BoundaryFrame.lean` | ☑ 07-03 |
| P-12 | §5 design: Fox–Heisenberg word complex; 5.7–5.15 statements | `GQ2/FoxHeisenberg.lean` | ☑ 07-03 |
| P-13 | §5 proofs umbrella (decomposed a–g; `orchestration/p13-ticket-split.md`) | — | ☑ 07-05 |
| P-13a | wild-Fox + mixed-Hessian engines, §5.13 splits | `GQ2/FoxHeisenberg.lean` | ☑ 07-04 |
| P-13b | §5.13 ramified normal form | — | ☑ 07-04 |
| P-13c | §5.14 ramified mixed Hessian | — | ☑ 07-04 |
| P-13d | §5 tameness rep-theory (`σ₂=1`, `V^S=0`) | — | ☑ 07-04 |
| P-13e | §5.11 dévissage (2-of-3 for `IsSelfDual`) | `GQ2/Devissage.lean` | ☑ 07-04 |
| P-13f | **Prop 5.15** duality assembly | `GQ2/DualityAssembly.lean`, `GQ2/DevissageInduction.lean` | ☑ 07-05 |
| P-13g | **Prop 5.16** local lifting duality | `GQ2/LocalLiftingDuality.lean` | ☑ 07-04 |

## §§6–7 — quadratic engine, Shapiro/Kummer, Gauss signs

| ID | Delivered | Where | Status |
|---|---|---|---|
| P-14 | §§6–7 statement design | `GQ2/SectionSix.lean`, `GQ2/SectionSeven.lean`, `docs/section67-extraction.md` | ☑ 07-03 |
| P-15 | §§6–7 proofs umbrella | — | ☑ (last leaf 07-08) |
| P-15a | nonsingular `𝔽₂` zero-count + **Lemma 6.6** (Wall) | `GQ2/QuadraticFp2.lean` | ☑ 07-04 |
| P-15b | Gauss signs: **Lemma 6.8** (87)/(88) + **Prop 6.9** (91) ×2 | `GQ2/GaussSigns.lean`, `GQ2/GaussCount.lean` | ☑ 07-04 |
| P-15c | Shapiro ledger: 6.15 free (104) + involution (105) | `GQ2/ShapiroLedger.lean` | ☑ 07-04 |
| P-15d | **Lemma 6.4/6.14**: datum independence of `Q⁰_loc` | `GQ2/RepIndependence.lean` | ☑ 07-04 |
| P-15e | Hilbert ledger: **Lemma 6.16** (110)–(114), deep-unit Evens norm | `GQ2/HilbertLedger.lean` | ☑ 07-04 |
| P-15f | deep part + §6 headline umbrella (`orchestration/p15f-handoff.md`) | `GQ2/DeepPart.lean` + lane files | ☑ (via f1–f8) |
| P-15f1 | **`lemma_6_17_dim`** — deep-half self-perpendicularity (via f4–f8) | `GQ2/DimAssembly.lean` + kits | ☑ 07-07 |
| P-15f2 | **`lemma_6_17_vanish`** — orbit decomposition umbrella (`orchestration/p15f2-handoff.md`) | `GQ2/OrbitVanish.lean` + lane | ☑ 07-08 |
| P-15f2a | DI-core: graph pullback of a zero-form factor set is a 2-coboundary | `GQ2/OrbitVanish.lean` | ☑ 07-07 |
| P-15f2b | isometric regular embedding `ι : V →+ W` with orbit-sum form | `GQ2/OrbitDecomp.lean`, `GQ2/RegularIsometry.lean` | ☑ 07-07 |
| P-15f2c | Shapiro coordinates + scalar deepness (split → c1/c2) | `GQ2/ShapiroDeepness.lean` | ☑ 07-08 |
| P-15f2c1 | Shapiro H¹ coordinate read (`hcoh` ×3 orbit types) | `GQ2/ShapiroRead.lean` | ☑ 07-07 |
| P-15f2c2 | involution deep-unit Kummer presentation (split → c2a/b/c) | — | ☑ 07-08 |
| P-15f2c2a | abstract Kummer presentation package (`exists_kummer_presentation`) | `GQ2/QuadraticAdjoin.lean` | ☑ 07-07 |
| P-15f2c2b | involution spine: tower dictionary + `lemma_6_16` assembly (`hvanish_involution`) | `GQ2/ShapiroDeepness.lean`, `GQ2/InvolutionSplice.lean` | ☑ 07-08 |
| P-15f2c2c | the analytic `hunram` umbrella (`orchestration/p15f2c2c-handoff.md`; no new axiom) | `GQ2/UnramifiedBridge.lean` | ☑ 07-08 |
| P-15f2c2c1 | Galois coset-norm kit (`cosetNorm`, `relE`) | `GQ2/GaloisCosetNorm.lean` | ☑ 07-08 |
| P-15f2c2c2 | CFT unit-index = ramification index (`card_unitImage_eq_e`) | `GQ2/UnitNormIndex.lean` | ☑ 07-08 |
| P-15f2c2c3 | tame 2-quotient factoring + B10′ orientation package | `GQ2/TameTwoQuotient.lean` | ☑ 07-08 |
| P-15f2c2c4 | `hunram` assembly for the involution tower | `GQ2/UnramifiedBridge.lean` | ☑ 07-08 |
| P-15f2d | final assembly + SectionSix splice → **`lemma_6_17_vanish_final`** | `GQ2/VanishClose.lean` | ☑ 07-08 |
| P-15f3 | **Prop 6.18 unramified** (cohomological model identification) | `GQ2/UnramifiedModel.lean` | ☑ 07-05 |
| P-15f4 | **Lemma 6.11** regular-summand projectivity (= P-17e4) | `GQ2/RegularSummand.lean` | ☑ 07-06 |
| P-15f5 | Hom-exactness counting engine | `GQ2/HomCounting.lean` | ☑ 07-06 |
| P-15f6 | Kummer transport + graded counts (`card_fam`/`card_deepFam`) | `GQ2/KummerFiltration.lean` area | ☑ 07-07 |
| P-15f7 | the two symmetry inputs (`hmid`, duality) | `GQ2/DeepDuality.lean`, `GQ2/DeepDualityK.lean` | ☑ 07-06/07 |
| P-15f8 | `DeepKummerData` assembly → `lemma_6_17_dim` close | `GQ2/DimAssembly.lean` | ☑ 07-07 |
| P-15g | §7 **Lemma 7.2** (tame-free route) | `GQ2/SectionSeven.lean` | ☑ 07-04 |
| P-15h | §7 **Prop 7.4** fully std-3 | `GQ2/SectionSeven.lean` | ☑ 07-04 |
| P-15i | **Lemma 6.21** transgression splitting (statement-extraction gap found & fixed) | `GQ2/Transgression.lean` | ☑ 07-04 |

## §8 — half-torsor count and the closed recursion

| ID | Delivered | Where | Status |
|---|---|---|---|
| P-16 | §8 umbrella: 8.6 both sources + **`prop_8_9`** | — | ☑ 07-08 |
| P-16a | central-obstruction engine (`RadicalEdgeData`, `MLifts`, `H²` obstruction) | `GQ2/RadicalEdgeData.lean`, `GQ2/CentralObstruction.lean` | ☑ 07-05 |
| P-16b | **`lemma_8_6_local`** close | `GQ2/RadicalEdgeLocal.lean` | ☑ 07-05 |
| P-16c | **`lemma_8_6_gammaA`** umbrella (decomposed c1–c5) | — | ☑ 07-06 |
| P-16c1 | `Γ_A` degree-≤1 bridge (`z1Equiv`, `h1Equiv`) | `GQ2/WordCohBridge.lean` | ☑ 07-05 |
| P-16c2 | `Γ_A` degree-2 comparison + `card_H2_gammaA_le_two` | `GQ2/WordCoh2.lean` | ☑ 07-06 |
| P-16c3 | the `Γ_A` twist, duality half | `GQ2/RadicalEdgeGammaA.lean` | ☑ 07-05 |
| P-16c4 | Θ–mixedB comparison (`H²(Γ_A) ↪ 𝔽₂` + ledger) | `GQ2/HalfTorsorGammaA.lean` | ☑ 07-06 |
| P-16c5 | `half_torsor_gammaA` assembly + splice | `GQ2/HalfTorsorGammaA.lean` | ☑ 07-06 |
| P-16d | `prop_8_9` assembly umbrella (decomposed d1–d6) | — | ☑ 07-08 |
| P-16d1 | frame-enrichment layer (per-λ square-form data) | `GQ2/SectionEight.lean` | ☑ 07-05 |
| P-16d2 | R-stage obstruction module (`stageR136_of`) | `GQ2/RStageObstruction.lean`(+`Build`) | ☑ 07-06 |
| P-16d3 | `zBC ↔ MLifts` bridge + `half139_of` | `GQ2/RadicalEdgeBridge.lean` | ☑ 07-05 |
| P-16d4 | **Lemma 8.7** (affine T-lifting) + Prop 8.8/(135) statement layer | `GQ2/AffineTLift.lean` | ☑ 07-05 |
| P-16d5 | shared witness `(μ, G⁰, D_T, phase)`; `centralCoverOfCocycle` | `GQ2/AffineTLift.lean` | ☑ 07-05 |
| P-16d6 | `phase140` + final two-source splice umbrella | — | ☑ 07-08 |
| P-16d6a | (136) R-stage against the concrete frame | `GQ2/BlockRStage.lean` | ☑ 07-06 |
| P-16d6b | (140) μ-independence (`tcocycle_mu_indep`) | (file later pruned — superseded route) | ☑ 07-06 |
| P-16d6c | (140) Prop-8.8 core umbrella (c1s/c1a/c1b/c1c/c2/c3; `orchestration/p16d6c-handoff.md`) | — | ☑ 07-07 |
| P-16d6c1s | engine-spec repair (Bug 1: `hM ↦ #W · N(κρ,ερ)`) | `GQ2/RecursionSplice.lean` | ☑ 07-07 |
| P-16d6c1a | crossed `V`-cocycle layer (`VCocycle`, `vcocycleEquivLifts`) | `GQ2/VCocycle.lean` | ☑ 07-07 |
| P-16d6c1b | connecting map + **Lemma 8.7 (131)** (`iotaB` obstruction calculus) | `GQ2/PhaseObstruction.lean` + leaf | ☑ 07-07 |
| P-16d6c1c | (135)-Γ keystone + `hM` close (`orchestration/p16d6c-keystone-design.md`) | — | ☑ 07-07 |
| P-16d6c2 | (140) phase witness; `hphase` **eliminated** by the c1b architecture; (141) split | — | ☑ 07-07 |
| P-16d6c3 | (140) `G⁰`/`μ` `l`-independence | `GQ2/PhaseLIndep.lean` (+`PhaseGaussLIndep`, later pruned) | ☑ 07-07 |
| P-16d6d | (139) for `G_ℚ₂` (`half139_local`) | `GQ2/Half139Local.lean` | ☑ 07-07 |
| P-16d6e | final assembly umbrella (e1–e7; `orchestration/p16d6e-handoff.md`) | — | ☑ 07-08 |
| P-16d6e1 | `prop_8_9` statement surgery (per-λ phase family, Bug 3) | 4 files | ☑ 07-08 |
| P-16d6e2 | generic (140) assembly chain | `GQ2/Phase140Assembly.lean` | ☑ 07-08 |
| P-16d6e3 | local (140) residues (`phase140_local`) | `GQ2/Phase140Local.lean` | ☑ 07-08 |
| P-16d6e4 | source-Gauss transport `hGaussZ` design + local layer (`orchestration/p16d6e4-gauss-design.md`) | — | ☑ 07-08 |
| P-16d6e4a | the (83)-evaluation seam, local discharge (`gaussZResidue_local_*`) | (`GQ2/GaussZFinal.lean`, later pruned — superseded by the D-route) | ☑ 07-08 |
| P-16d6e4aA | the (83)-for-`Γ_A` seam umbrella (A-1…A-4, P1–P5; `orchestration/p16d6e4aAP-handoff.md`) | — | ☑ 07-08 |
| P-16d6e4aA-P1 | Maschke brick (odd-order complement) | — | ✂ not needed (étale route) |
| P-16d6e4aA-P2 | the pack design doc (paper pp. 26–28 reread) | `orchestration/p16d6e4aA-pack-design.md` | ☑ 07-08 |
| P-16d6e4aA-P3 | **the ramified isotypic pack** (single isotype, `AdjoinRoot` field, char-2 Frobenius, σ-semilinear descent, `#V^{powOmega2 s} = 2^{r·sV}`) → `zeroCount_qDouble_ramified_of_faithful` PROVED — **the last library sorry** | `GQ2/RamifiedPack.lean`, `GQ2/GaussZFinalGammaA.lean` | ☑ 07-08 |
| P-16d6e4aA-P4 | c3-G0 package (frozen `TamePackage` shape **refuted**; reshaped → P4d/P4e block-D twins) | `GQ2/GaussZGammaAD.lean`, `GQ2/GaussZFinalD.lean`, `GQ2/BlockHeadDat.lean` | ☑ 07-08 (as P4d/P4e) |
| P-16d6e4aA-P5 | ThmFourTwo swap: G0-obtain sorry closed by `gaussZ_obtain_blockD` | `GQ2/ThmFourTwo.lean` | ☑ 07-08 |
| P-16d6e5 | `Γ_A` (136) residues (`hsep_hom_gammaA`, marking route) | `GQ2/RStageGammaA.lean` | ☑ 07-07 |
| P-16d6e6 | `Γ_A` (140) residues + M-lift counts (the four residues consumed at e7) | — | ☑ 07-08 |
| P-16d6e7 | witness + `RecursionInputs` + final splice → **`prop_8_9` PROVED** | `GQ2/Prop89Close.lean` | ☑ 07-08 |

## §9 — the induction (Theorem 4.2)

| ID | Delivered | Where | Status |
|---|---|---|---|
| P-17 | §9 umbrella (a–i; `docs/section9-extraction.md`) | — | ☑ 07-08 |
| P-17a | §9 design: skeleton + extraction + DAG | `GQ2/SectionNine.lean` | ☑ 07-06 |
| P-17b | §9.1 terminal case (`terminal_count_eq`; b1–b3) | `GQ2/SectionNine.lean` | ☑ 07-06 |
| P-17b1 | Lemma 9.2 structure (odd normal lift + fibre-product iso) | `GQ2/SectionNine.lean` | ☑ 07-06 |
| P-17b2 | tame 2-nilpotency (`O²(H)` odd) | — | ☑ 07-06 |
| P-17b3 | (144) correspondence + assembly | `GQ2/SectionNine.lean` | ☑ 07-06 |
| P-17c | concrete frame `blockFrameImpl` | `GQ2/BlockFrameImpl.lean` | ☑ 07-06 |
| P-17d | concrete enrichment umbrella (d1/d2/d3; `orchestration/p17d2-handoff.md`) | `GQ2/Block{Descent,Char,FormFields,Enrichment}.lean` | ☑ 07-06 |
| P-17d1 | descent structure (`Vmod` + action instances) | `GQ2/BlockDescent.lean` | ☑ 07-06 |
| P-17d2 | form fields umbrella (d2a/b/c) | `GQ2/BlockChar.lean`, `GQ2/BlockFormFields.lean` | ☑ 07-06 |
| P-17d2a | `blockLam` character | `GQ2/BlockChar.lean` | ☑ 07-06 |
| P-17d2b | `qbar`/`q` field lemmas wiring | `GQ2/BlockFormFields.lean` | ☑ 07-06 |
| P-17d2c | `hquad`/`hns` (the new math) | `GQ2/BlockFormFields.lean` | ☑ 07-06 |
| P-17d3 | κ⁰ discharge + `blockEnrichment` assembly | `GQ2/BlockEnrichment.lean` | ☑ 07-06 |
| P-17e | κ⁰ base-class existence umbrella (**paper Lemma 6.3**; e1–e5) | — | ☑ 07-06 |
| P-17e1 | odd/unramified case (average the form) | `GQ2/SectionNine.lean` | ☑ 07-06 |
| P-17e2 | orbit data square/free (75)/(76) | `GQ2/SectionNine.lean` | ☑ 07-06 |
| P-17e3 | involution datum (Lemma 6.2, explicit `m`) | `GQ2/InvolutionDatum.lean` | ☑ 07-06 |
| P-17e4 | ramified split embedding = **Lemma 6.11** (shared with P-15f4) | `GQ2/RegularSummand.lean` | ☑ 07-06 |
| P-17e5 | normal form + assembly → `kappa0_exists` | `GQ2/KappaNormalForm.lean` | ☑ 07-06 |
| P-17f | §9.2 M-stage partition | `GQ2/SectionNine.lean` | ☑ 07-05 |
| P-17g | Lemma 9.4 bounds ((145)/(148)/(153)) | `GQ2/BlockFrameBounds.lean` | ☑ 07-06 |
| P-17h | §9.3 recursion solver (ℤ-arithmetic) | `GQ2/SectionNine.lean` | ☑ 07-06 |
| P-17i | §9 master induction → **`thm_4_2` proved** (`orchestration/p17i-handoff.md`) | `GQ2/ThmFourTwo.lean` | ☑ 07-08 |

## §10 — exhaustion and the main theorem

| ID | Delivered | Where | Status |
|---|---|---|---|
| P-18 | §10 umbrella (a–e) | — | ☑ 07-07 |
| P-18a | §10 design + statements (`docs/section10-extraction.md`) | `GQ2/SectionTen.lean` | ☑ 07-07 |
| P-18b | the 2-core layer (`twoCore_*`) | `GQ2/SectionTen.lean` | ☑ 07-07 |
| P-18c | Γ-generic **Lemma 10.1** + `card_contSurj_eq` | `GQ2/SectionTen.lean` | ☑ 07-07 |
| P-18d | per-source `htame`/`hwild` hypotheses | `GQ2/SectionTenSources.lean` | ☑ 07-07 |
| P-18e | assembly: **`eq_154`** + **`main_surjection_count'`** | `GQ2/SectionTenSources.lean` | ☑ 07-07 |
| P-19 | **`main_presentation_literal`** — the literal Theorem 1.2 | `GQ2/PresentationLiteral.lean` | ☑ 07-07 |

## How the last sorries fell (the endgame, 2026-07-08)

1. **`prop_8_9`** closed at P-16d6e7 (`Prop89Close.lean`) — the four `Γ_A` residues through
   `phase140_from_residues`, with the source-Gauss values `hGaussZA`/`hGaussZF` carried as
   *ledger hypotheses* (the sanctioned §6.2-style deferral).
2. The ledger was discharged at the consumer: P-16d6e4aA reshaped the `Γ_A` (83)-evaluation
   onto the **block-D route** (P4d/P4e twins), and P5 swapped `thm_4_2`'s G0-obtain to
   `gaussZ_obtain_blockD` — leaving exactly one sorry in the library.
3. That sorry — `zeroCount_qDouble_ramified_of_faithful` (`GaussZFinalGammaA.lean`) — fell to
   the **P3 ramified isotypic pack** (`RamifiedPack.lean`): étale single-isotype structure,
   hand-rolled char-2 Frobenius, σ-semilinear Artin/Dedekind descent, and the 2-primary
   projection count `#V^{powOmega2 s} = 2^{r·sV}`.  Verified std-3 exactly; the capstone
   `#print axioms` shows **no `sorryAx`** and the 12-leaf trust base of `atlas-audit.md`.
4. In parallel, the §6 lane finished `lemma_6_17_vanish_final` (P-15f2d splice at
   `VanishClose.lean`) on top of the c2c analytic-`hunram` tower — **no new axiom**, as decided.
