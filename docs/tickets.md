# Ticket board — step 2 (proving Theorem 1.2 from the axioms)

Source of truth for the proof phase.  Rationale, DAG, conventions, and wave schedule:
[`step2-plan.md`](step2-plan.md).  The **step-1 board** (statement formalization, ticket IDs
`T-xx` cited in module docstrings) is archived at [`tickets-step1.md`](tickets-step1.md).
Difficulty: ⭐ easy · ⭐⭐ medium · ⭐⭐⭐ hard/design-sensitive.  Model: **F** = Fable
(design-heavy), **O** = Opus (well-specified).  Status: ☐ open · ◐ in progress · ☑ done.

Rules: **no new `axiom`s** (census frozen at 10); statement tickets add their sorried theorems to
`SORRY_ALLOWLIST` in `scripts/check_axioms.sh` (same commit, entry cites the ticket), proof
tickets remove them; every ticket's new theorems satisfy `#print axioms` ⊆ std-3 ∪ the ticket's
**Ax** column; `GQ2/Foundations/Axioms.lean` is frozen; sessions claim a ticket by marking its
row ◐ before starting.  Paper: `paper/A_Profinite_Presentation_for_G__Q_2.pdf`.

| ID | Title | Diff | Model | Deps | Ax | Status |
|---|---|---|---|---|---|---|
| P-00 | Meta: step-2 plan + board + LeanBridge tooling import | ⭐ | **F** | — | — | ☑ 2026-07-03 (`docs/step2-plan.md`, `.claude/`) |
| P-01 | Meta: `docs/STATUS.md` refresh + repo-wide axiom ledger (batch `#print axioms` check vs App. D) | ⭐⭐ | O | — | — | ☐ |
| P-02 | A: fill `exists_contSurj_of_card_le` (recipe at the sorry: cofiltered system + compactness) | ⭐⭐ | O | — | ∅ | ☐ |
| P-03 | A: t.f.g. — `FreeProfiniteGroup X` (finite `X`), quotients of t.f.g., `GammaA` t.f.g. | ⭐⭐ | O | — | ∅ | ☐ |
| P-04 | A: universal marking admissible-in-the-limit (relator words ∈ `N_A`; wild pair's closed normal closure pro-2 in `Γ_A`) | ⭐⭐⭐ | **F** | — | ∅ | ☐ |
| P-05 | A: Prop 2.3 — `Nat.card (ContSurj GammaA G) = admissibleCount G` | ⭐⭐⭐ | **F** | P-04 | ∅ | ☐ |
| P-06 | B: §3 statement extraction — Lemmas 3.4–3.8, Prop 3.2, Prop 1.1 as sorried statements + design note | ⭐⭐ | **F** | — | (statements) | ☐ |
| P-07 | B: Lemmas 3.4/3.5 proofs (eq. (13) ledger: square-class basis, χ/ν rows, cup form `α²+βγ+γβ`) | ⭐⭐ | O | P-06 | B5, B7′ | ☐ |
| P-08 | B: Lemmas 3.6–3.8 proofs (cyclotomic conjugation of peripherals; wild-relation shape) | ⭐⭐ | O | P-06 | B2, B8 | ☐ |
| P-09 | B: Prop 3.2 proof — common tame quotient (`Γ_A` side: Lemma 3.1 ✓ + bridges; local side: B5 `ν_ur`) | ⭐⭐⭐ | O | P-06 | B5 | ☐ |
| P-10 | B: Prop 1.1 proof — marked dyadic Demushkin normalization, `ν_ur = (−2,1,0)` | ⭐⭐ | O | P-06, P-07, P-08 | B3c, B4, B5, B7′ | ☐ |
| P-11 | B: §4 design — boundary-framed marked targets, exact-image counts, **Thm 4.2 statement** | ⭐⭐⭐ | **F** | — | (statements) | ☐ |
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

- **P-01**: `docs/STATUS.md` regenerated to the current tree (it stops at 2026-07-02); a script or
  Lean file (`scripts/axiom_ledger.*` or `GQ2/AxiomLedger.lean`) that reports, for every theorem in
  `GQ2`, its non-std-3 axioms, diffable against the per-ticket **Ax** declarations.  Re-run
  instructions in the file header.
- **P-02**: the sorry replaced following the in-file recipe (level sets nonempty+finite via `h`;
  `nonempty_sections_of_finite_inverse_system`; assemble through
  `ProfiniteGrp.isoLimittoFiniteQuotientFunctor`; image compact-dense ⇒ surjective).  Zero sorries
  in `Reconstruction.lean`; allowlist entry removed; `reconstruction`/`reconstruction_of_equinum`
  at std-3.
- **P-03**: `FreeProfiniteGroup X` is t.f.g. for finite `X` (the generators' images topologically
  generate — density of the free group in its completion); t.f.g. passes to `profiniteQuotient`;
  instantiate: `GammaA` t.f.g. in the exact `∃ s : Finset _, …` form `main_presentation` consumes.
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
- **P-07/P-08/P-09/P-10**: the P-06 statements proved, allowlist entries removed, axiom sets per
  the **Ax** column (this *is* the App. D certificate check for §3).  P-09's `Γ_A` side should
  consume `Tame.lean`'s Lemma 3.1 as-is; if the local side needs more than the B5 bundle exposes,
  that is a design escalation (rule 1), not a bundle edit.
- **P-11**: the §4 objects as Lean structures (boundary frame, marked target, the two exact-image
  counts) + `theorem thm_4_2 : … := sorry`, with a design note justifying every encoding choice
  against the paper's §4 text; the `Γ_A`-side count must be *definitionally* the finite object §5
  computes with.  This is the step-2 keystone — over-document rather than over-abstract.
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
