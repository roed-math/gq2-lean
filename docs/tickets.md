# Ticket board — step 2 (proving Theorem 1.2 from the axioms)

Source of truth for the proof phase.  Rationale, DAG, conventions, and wave schedule:
[`step2-plan.md`](step2-plan.md).  The **step-1 board** (statement formalization, ticket IDs
`T-xx` cited in module docstrings) is archived at [`tickets-step1.md`](tickets-step1.md).
Difficulty: ⭐ easy · ⭐⭐ medium · ⭐⭐⭐ hard/design-sensitive.  Model: **F** = Fable
(design-heavy), **O** = Opus (well-specified).  Status: ☐ open · ◐ in progress · ☑ done.

Rules: **no new `axiom`s** (census frozen at 11 — B10 added post-kickoff by explicit decision, P-06 escalation); statement tickets add their sorried theorems to
`SORRY_ALLOWLIST` in `scripts/check_axioms.sh` (same commit, entry cites the ticket), proof
tickets remove them; every ticket's new theorems satisfy `#print axioms` ⊆ std-3 ∪ the ticket's
**Ax** column; `GQ2/Foundations/Axioms.lean` is frozen; sessions claim a ticket by marking its
row ◐ before starting.  Paper: `paper/A_Profinite_Presentation_for_G__Q_2.pdf`.

| ID | Title | Diff | Model | Deps | Ax | Status |
|---|---|---|---|---|---|---|
| P-00 | Meta: step-2 plan + board + LeanBridge tooling import | ⭐ | **F** | — | — | ☑ 2026-07-03 (`docs/step2-plan.md`, `.claude/`) |
| P-01 | Meta: `docs/STATUS.md` refresh + repo-wide axiom ledger (batch `#print axioms` check vs App. D) | ⭐⭐ | O | — | — | ☑ 2026-07-03 (`GQ2/AxiomLedger.lean`, `docs/STATUS.md`) |
| P-02 | A: fill `exists_contSurj_of_card_le` (recipe at the sorry: cofiltered system + compactness) | ⭐⭐ | O | — | ∅ | ◐ (Opus, 2026-07-03) |
| P-03 | A: t.f.g. — `FreeProfiniteGroup X` (finite `X`), quotients of t.f.g., `GammaA` t.f.g. | ⭐⭐ | O | — | ∅ | ☑ 2026-07-03 (`GQ2/FinitelyGenerated.lean`) |
| P-04 | A: universal marking admissible-in-the-limit (relator words ∈ `N_A`; wild pair's closed normal closure pro-2 in `Γ_A`) | ⭐⭐⭐ | **F** | — | ∅ | ◐ (Fable, 2026-07-03) |
| P-05 | A: Prop 2.3 — `Nat.card (ContSurj GammaA G) = admissibleCount G` | ⭐⭐⭐ | **F** | P-04 | ∅ | ☐ |
| P-06 | B: §3 statement extraction — Lemmas 3.4–3.8, Prop 3.2, Prop 1.1 as sorried statements + design note | ⭐⭐ | **F** | — | (statements) | ☑ 2026-07-03 (`GQ2/SectionThree.lean` + `GQ2/SectionThreeMarked.lean`, `docs/section3-extraction.md`) |
| P-07 | B: Lemmas 3.4/3.5 proofs (eq. (13) ledger: square-class basis, χ/ν rows, cup form `α²+βγ+γβ`) | ⭐⭐ | O | P-06 | B5, B7′ | ☐ |
| P-08 | B: Lemmas 3.6–3.8 proofs (cyclotomic conjugation of peripherals; wild-relation shape) | ⭐⭐ | O | P-06 | B2, B8 | ☐ |
| P-09 | B: Prop 3.2 proof — common tame quotient (`Γ_A` side: Lemma 3.1 ✓ + bridges; local side: B10 + Lemma 3.3 maximality) | ⭐⭐⭐ | O | P-06 | B5, B10 | ☐ |
| P-10 | B: Prop 1.1 proof — marked dyadic Demushkin normalization, `ν_ur = (−2,1,0)` | ⭐⭐ | O | P-06, P-07, P-08 | B3c, B4, B5, B7′ | ☐ |
| P-11 | B: §4 design — boundary-framed marked targets, exact-image counts, **Thm 4.2 statement** | ⭐⭐⭐ | **F** | — | (statements) | ☑ 2026-07-03 (`GQ2/BoundaryFrame.lean`) |
| P-12 | B: §5 design — Fox–Heisenberg word complex; 5.7/5.8/5.10/5.11/5.13/5.15 statements | ⭐⭐⭐ | **F** | P-11 | (statements) | ☐ |
| P-13 | B: §5 proofs (Stokes identities → chain map; dévissage; elementary-module duality 5.15) | ⭐⭐⭐ | O | P-12 | B6, B7 | ☐ |
| P-14 | B: §§6–7 design — 6.13 (D₈ class), 6.15→6.17 (Shapiro/cor), 6.8/6.9 (Gauss sign), 6.16→6.18 (Hilbert ledger), 6.21 (transgression) statements | ⭐⭐⭐ | **F** | P-11 | (statements) | ☐ |
| P-15 | B: §§6–7 proofs | ⭐⭐⭐ | O | P-14 | B5, B6, B7′, B9 | ☐ |
| P-16 | B: §8 — half-torsor count 8.6 + closed recursion Prop 8.9 (eqs. (136)–(142)) | ⭐⭐⭐ | **F** draft, O finish | P-11, P-14 | B6, B7, B9 | ☐ |
| P-17 | B: §9 — induction on `\|L_Y\|`: regime 9.1 (Lemma 9.2 ✓), 9.2 (counts + strict decrease (145)/Lemma 9.4), 9.3 (Frattini/Fourier, central formula (151)) ⇒ **Thm 4.2 proof** | ⭐⭐⭐ | **F** design, O finish | P-11–P-16 | B6, B7, B7′, B8, B9 | ☐ |
| P-18 | B: Lemma 10.1 (tame-frame exhaustion) + eq. (154) ⇒ `main_surjection_count` | ⭐⭐ | O | P-09, P-10, P-17 | (all of Track B) | ☐ |
| P-19 | Assembly: `main_presentation_literal` via `main_presentation` | ⭐ | O | P-02, P-03, P-05, P-18 | B1 + Track B | ☐ |
| P-20 | Meta: review packet v3 — interior-node statements + App. D certificate diff, at statement freeze | ⭐ | O | P-06, P-11, P-12, P-14 | — | ☐ |

## Per-ticket acceptance criteria

Common to all: `lake build GQ2` green; `scripts/check_axioms.sh` green (allowlist edits per the
rules above); `#print axioms` of every new theorem ⊆ std-3 ∪ the **Ax** column; docstrings carry
paper eq./§ cross-references; new files, own board row only.

- **P-01** ☑: `docs/STATUS.md` regenerated to the current tree (it stops at 2026-07-02); a script or
  Lean file (`scripts/axiom_ledger.*` or `GQ2/AxiomLedger.lean`) that reports, for every theorem in
  `GQ2`, its non-std-3 axioms, diffable against the per-ticket **Ax** declarations.  Re-run
  instructions in the file header.
  *Done.* `GQ2/AxiomLedger.lean` — a `run_cmd` metaprogram over the elaborated environment
  (`Lean.collectAxioms` per decl; robust to `namespace`/`private`, which the shell
  `.claude/tools/lean4/check_axioms.sh` cannot see).  Re-run: `lake env lean GQ2/AxiomLedger.lean`
  (header documents it; **not** imported by `GQ2.lean`, so `lake build GQ2` never runs it).  Output:
  per-B-axiom consumer lists (diff vs App. D §C), the `sorryAx` gap map, and an **ALARM** count for
  any other non-standard axiom.  Current run: 613 tracked decls, 601 at std-3, ALARM 0; only B7 has
  consumers (its 6 Euler stress tests), gap map = 6 (the 3 root sorries + 3 transitive).
  `docs/STATUS.md` rewritten as a per-layer ledger (axiom layer, 3-sorry gap map, def-layers
  T-05…T-18, proved infra), with verify-from-scratch commands.
- **P-02**: the sorry replaced following the in-file recipe (level sets nonempty+finite via `h`;
  `nonempty_sections_of_finite_inverse_system`; assemble through
  `ProfiniteGrp.isoLimittoFiniteQuotientFunctor`; image compact-dense ⇒ surjective).  Zero sorries
  in `Reconstruction.lean`; allowlist entry removed; `reconstruction`/`reconstruction_of_equinum`
  at std-3.
- **P-03**: `FreeProfiniteGroup X` is t.f.g. for finite `X` (the generators' images topologically
  generate — density of the free group in its completion); t.f.g. passes to `profiniteQuotient`;
  instantiate: `GammaA` t.f.g. in the exact `∃ s : Finset _, …` form `main_presentation` consumes.
  *Done (`GQ2/FinitelyGenerated.lean`, std-3):* predicate `IsTopologicallyFinGen G` (unfolds to the
  raw `main_presentation` form); `IsTopologicallyFinGen.of_surjective` (transfer along a continuous
  surjection — `DenseRange.topologicalClosure_map_subgroup`); `isTopologicallyFinGen_freeProfiniteGroup`
  (finite `X` — `ProfiniteGrp.ProfiniteCompletion.denseRange` + `FreeGroup.closure_range_of`);
  `gammaA_isTopologicallyFinGen` + `gammaA_topologicallyFinitelyGenerated` (the raw `∃`-form P-19 feeds
  to `main_presentation`).
- **P-04**: (i) `tameRelator`/`wildRelator` of `univMarking` lie in `NA` (each dies in every
  admissible quotient — `map_*Relator_eq_one_iff` + `IsAdmissibleU`); (ii) the closed normal
  closure of `{x₀, x₁}`-images in `Γ_A` is pro-2 (`IsProP 2`, via `MaxProP.lean`'s
  characterization: every open normal subgroup of `Γ_A` pulls back to an admissible-dominated one —
  the Lemma 2.1 subdirect-closure argument).  Design note documenting the limit argument.
- **P-05**: the bijection `ContSurj GammaA G ≃ {t : Marking G // t.Admissible}` for finite discrete
  `G`: forward = push `univMarking` (admissible by P-04 + Lemma 2.2 `map_admissible`); backward =
  `quotientLift` along `NA_le_ker` (T-21); round-trips via `univMarking_map_toHom` and topological
  generation (P-03).  `Nat.card` conclusion in exactly `main_presentation`'s `hΓA` form.
- **P-06**: sorried statements, faithful to the paper's §3 (read the PDF; extract also 3.7/3.8,
  whose precise content the step-1 docs never recorded), phrased against the existing def-layers
  (`Reciprocity` bundle for eq. (13), `HilbertSymbol`/`Kummer` for 3.5, `PeripheralAction` for
  3.6, `Tame.lean` for the tame side, `DyadicPresentation`+`Orientation` for Prop 1.1's target).
  Design note mapping each statement to its paper display.  Allowlist entries added.
  *Done (`GQ2/SectionThree.lean` — 10 sorries — plus `GQ2/SectionThreeMarked.lean` — 5 — both
  allowlisted; design note `docs/section3-extraction.md`).*  Statements: Prop 1.1 (`prop_1_1`,
  lift-read `ν_ur`-rows, `R : LocalReciprocity`-parametrized); Prop 3.2 split
  (`prop_3_2_gammaA` generator-pinned; `prop_3_2_local` = `Nonempty LocalTameQuotient`, wild
  inertia encoded as the maximal closed normal pro-2 subgroup per Lemma 3.3); eq. (11) bundle
  (`BDecomposition`, `b_decomposition`); Lemma 3.5 residue (`lemma_3_5_marked_abelianization`,
  `lemma_3_5_hilbert_ledger`, `lemma_3_5_injective` — the (13) rows are step-1-proved in
  `Reciprocity.lean`); Lemma 3.7 (`lemma_3_7`); Prop 3.8 (`prop_3_8_lift`,
  `prop_3_8_classification`).  **Absorptions**: Lemma 3.4 = B4 + B3c + the B3b no-axiom
  decision; Lemma 3.6 = B8 verbatim.  **P-11 handoff taken**: Prop 3.10/3.14 stated against
  `BoundaryFrame.lean` (`prop_3_10_gammaA`, `prop_3_10_local_marked`, `nuT_surjective`,
  `nuTwo_surjective`, `prop_3_14 : Nonempty BoundaryMaps`) in `SectionThreeMarked.lean`
  (separate file: it imports the P-11 layer, committed `f4f911e`, while the core file rests
  on step-1 modules only).  **Escalation for P-09** (rule 1, pre-authorized in its bullet): `prop_3_2_local`
  needs the classical tame-quotient description of `G_ℚ₂`, which no census axiom covers —
  census discussion before P-09; options in the design note.  P-10 infra flagged:
  `IsProP 2 (Multiplicative ℤ₂)` descent + the `Ztwo ≅ Multiplicative ℤ₂` bridge.
  *Escalation resolved (same day, user decision):* **B10** (`GQ2.tameQuotient`, NSW (7.5.3)
  Iwasawa; defs `GQ2/TameQuotient.lean`) added, census 10 → 11; maximality (Lemma 3.3) kept
  as P-09's theorem (`LocalTameQuotient extends TameQuotientData`); `Ttame` deduped onto the
  P-11 layer (`SectionThree`'s copy removed; `tame_relation` now in `TameQuotient.lean`).
- **P-07/P-08/P-09/P-10**: the P-06 statements proved, allowlist entries removed, axiom sets per
  the **Ax** column (this *is* the App. D certificate check for §3).  P-09's `Γ_A` side should
  consume `Tame.lean`'s Lemma 3.1 as-is; if the local side needs more than the B5 bundle exposes,
  that is a design escalation (rule 1), not a bundle edit.
- **P-11**: the §4 objects as Lean structures (boundary frame, marked target, the two exact-image
  counts) + `theorem thm_4_2 : … := sorry`, with a design note justifying every encoding choice
  against the paper's §4 text; the `Γ_A`-side count must be *definitionally* the finite object §5
  computes with.  This is the step-2 keystone — over-document rather than over-abstract.
  *Done (`GQ2/BoundaryFrame.lean`; design note = module docstring; proved layer at std-3 with
  **zero** B-axioms).*  Shipped: `Ttame` (§3 display), `PiBd` = paper's `Π` (Prop 3.10 eq. (20),
  relator `x₀^{σ²}x₀[x₁,σ]` — conjugation by `σ` **squared**; pro-2 presentation encoded as
  `maxProPQuotient 2 ∘ profinitePresentation`, the Δ/T-12 pattern), `Ztwo := maxProPQuotient 2
  Zhat`, markings `nuT`/`nuTwo` via new `presentationLift` helper + T-05 universal property, with
  **proved** generator-value stress tests (`nuT_tameSigma` etc.); `boundarySubgroup`/`Boundary` =
  eq. (26) as the closed equalizer subgroup; `BoundaryFrame` (28) with `frameMap` β;
  `MarkedTarget` (Def 4.1, `[Finite Y]` carried — implied by paper) + `stratum`;
  `IsBoundaryLift`/`BoundaryLifts`/`exactImageCount` (29) on `ContSurj` (Nat.card convention;
  `finite_boundaryLifts` under t.f.g.).  **Key decision**: the (27) epimorphisms are a hypothesis
  bundle `BoundaryMaps` (B5/B6-style) — `Γ_A`-side pinned rigidly by 8 generator equations
  (Prop 3.10/3.14 proof), `G_ℚ₂`-side intrinsically (Lemma 3.3 2-core kernel for tame;
  `ker = proPKernel 2` for pro-2) + ν-compat + joint surjectivity; `thm_4_2` quantifies over
  witnesses (faithful per 3.14's "may be chosen" + §4's "once and for all"; residual-slack risk
  flagged in-file for P-17/P-20).  `thm_4_2_stratum` (second clause) is *derived*, fixing §8's
  consumption shape.  **Handoffs**: P-06 states Prop 3.10/3.14 against these defs (instantiation
  = P-09/P-10); P-12 consumes `IsBoundaryLift` + may promote `presentationLift`; P-16's
  `X_Γ(C)` = `BoundaryLifts`; P-17 removes the sorry.
- **P-12/P-14**: same statement-first discipline for §5 / §§6–7 (P-14 discovers §7's actual
  content at extraction — the step-1 docs only ever cite 6.x and 8.x).
- **P-13/P-15/P-16**: proofs; each lemma cites its display number; `decide`-style finite
  verifications welcome where the paper's objects are literally finite (e.g. 6.13's two-point
  `D₈` class), `native_decide` still banned.
- **P-17**: the strong induction assembled exactly as §9 states it (Lemma 9.4 strict decrease as
  the termination measure; regimes 9.1/9.2/9.3 as separate lemmas); `thm_4_2`'s sorry removed.
- **P-18**: `main_surjection_count`'s sorry removed; `Statement.lean` untouched except the proof
  body (statement frozen since T-21 review).
- **P-19**: `main_presentation_literal`'s sorry removed by instantiating `main_presentation` at
  `GammaA` with P-03 + P-05 + B1 + P-18; **zero sorries repo-wide**, allowlist empty, census 10.
- **P-20**: `docs/review-packet-v2.md` → v3: every interior-node statement quoted with its paper
  display + the certificate table (per-node `#print axioms` vs App. D row), handed for human
  review before Wave-3 proofs begin.
