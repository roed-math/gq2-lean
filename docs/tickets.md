# Ticket board — step 2 (proving Theorem 1.2 from the axioms)

Source of truth for the proof phase.  Rationale, DAG, conventions, and wave schedule:
[`step2-plan.md`](step2-plan.md).  The **step-1 board** (statement formalization, ticket IDs
`T-xx` cited in module docstrings) is archived at [`tickets-step1.md`](tickets-step1.md).
Difficulty: ⭐ easy · ⭐⭐ medium · ⭐⭐⭐ hard/design-sensitive.  Model: **F** = Fable
(design-heavy), **O** = Opus (well-specified).  Status: ☐ open · ◐ in progress · ☑ done.

Rules: **no new `axiom`s** (census frozen at 12 — B10 added by explicit decision, P-06 escalation; B9 base-generalized + B11 added by explicit decision, P-15 escalation, user-approved 2026-07-03); statement tickets add their sorried theorems to
`SORRY_ALLOWLIST` in `scripts/check_axioms.sh` (same commit, entry cites the ticket), proof
tickets remove them; every ticket's new theorems satisfy `#print axioms` ⊆ std-3 ∪ the ticket's
**Ax** column; `GQ2/Foundations/Axioms.lean` is frozen; sessions claim a ticket by marking its
row ◐ before starting.  Paper: `paper/A_Profinite_Presentation_for_G__Q_2.pdf`.

| ID | Title | Diff | Model | Deps | Ax | Status |
|---|---|---|---|---|---|---|
| P-00 | Meta: step-2 plan + board + LeanBridge tooling import | ⭐ | **F** | — | — | ☑ 2026-07-03 (`docs/step2-plan.md`, `.claude/`) |
| P-01 | Meta: `docs/STATUS.md` refresh + repo-wide axiom ledger (batch `#print axioms` check vs App. D) | ⭐⭐ | O | — | — | ☑ 2026-07-03 (`GQ2/AxiomLedger.lean`, `docs/STATUS.md`) |
| P-02 | A: fill `exists_contSurj_of_card_le` (recipe at the sorry: cofiltered system + compactness) | ⭐⭐ | O | — | ∅ | ☑ 2026-07-03 (`GQ2/Reconstruction.lean`) |
| P-03 | A: t.f.g. — `FreeProfiniteGroup X` (finite `X`), quotients of t.f.g., `GammaA` t.f.g. | ⭐⭐ | O | — | ∅ | ☑ 2026-07-03 (`GQ2/FinitelyGenerated.lean`) |
| P-04 | A: universal marking admissible-in-the-limit (relator words ∈ `N_A`; wild pair's closed normal closure pro-2 in `Γ_A`) | ⭐⭐⭐ | **F** | — | ∅ | ☑ 2026-07-03 (`GQ2/AdmissibleLimit.lean`) |
| P-05 | A: Prop 2.3 — `Nat.card (ContSurj GammaA G) = admissibleCount G` | ⭐⭐⭐ | **F** | P-04 | ∅ | ☑ 2026-07-03 (`GQ2/Prop23.lean`) |
| P-06 | B: §3 statement extraction — Lemmas 3.4–3.8, Prop 3.2, Prop 1.1 as sorried statements + design note | ⭐⭐ | **F** | — | (statements) | ☑ 2026-07-03 (`GQ2/SectionThree.lean` + `GQ2/SectionThreeMarked.lean`, `docs/section3-extraction.md`) |
| P-07 | B: Lemmas 3.4/3.5 proofs (eq. (13) ledger: square-class basis, χ/ν rows, cup form `α²+βγ+γβ`) | ⭐⭐ | O | P-06 | B5, B7′ | ◐ (Opus, 2026-07-03): `lemma_3_5_hilbert_ledger` ✓ (B7′) **and `lemma_3_5_injective` ✓ (std-3)** — the latter via a self-contained pro-2-abelianization layer in `SectionThree.lean` (`isProP_two_topAb_D0`, `zpowZtwo` helpers, `D0ab_coord`: `D₀^ab ∋ z = Ā^aS̄^sȲ^y`, topological generation through `F₃↠D0Full↠D₀↠D₀^ab`); coordinate argument uses P-21 `η`-injectivity + a mod-4 unit reduction. `topAbelianization` profinite instances kept **`local`** (a global generic instance perturbs `AnabelianBridge`'s `K⧸M` synthesis; verified both build). **`b_decomposition` ✓ (std-3)** — `D₀^ab ≅ ℤ/2×ℤ₂×ℤ₂` via coordinate homs `τ,σ,γ` (local `d0LiftHom` universal-property replica + `abLift` descent through `abMk`), combined into `φ` shown bijective. **All 4 clauses now have proofs.** `lemma_3_5_marked_abelianization` (B5) is **proved modulo one clean lemma `markedHom_bijective`** (std-3 + sorryAx): the descent `markedPi` (`G_ℚ₂^ab→(G_ℚ₂(2))^ab`, all-lifts-agree), the marked hom `markedHom` (`Ā,S̄,Ȳ↦rec(−4),rec(1/2),rec(−3)`, relation `(−4)²·2⁻⁴=1` verified), and the generator matching are **all std-3**; the sole remaining sorry is `markedHom_bijective` = the **census-gated pro-2 reciprocity iso** (that `{rec(−4),rec(1/2),rec(−3)}` coordinatize `(G_ℚ₂(2))^ab`; B5 gives only coordinate values, not surj/inj — see `section3-extraction.md` Escalation 5; resolution = strengthen B5 or derive from `norm_reciprocity`, same family as P-10). |
| P-08 | B: Lemmas 3.6–3.8 proofs (cyclotomic conjugation of peripherals; wild-relation shape) | ⭐⭐ | O | P-06 | B2, B8 | ☑ 2026-07-03 (Fable): all three theorems proved in `GQ2/AnabelianBridge.lean`, namespace `GQ2.SectionThree` — **`lemma_3_7`** (std-3 + B8), **`prop_3_8_lift`** (std-3 + B8; `α_{u,b} = θ_b ∘ ψ_u`: `ψ_u` from the B8 action pushed through `deltaLift`/`d0Lift` + Frattini surjectivity, `θ_b` the `Y ↦ S^bY` shear with `theta_relator`), **`prop_3_8_classification`** (**std-3 only, axiom-free**: `t`-torsion fixing + `η`-mod-4 kill of the `(−1)`-component + `D0ab_coord` rows; `u ∈ ℤ₂ˣ` forced via the same row for `ξ⁻¹`). B2 turned out unneeded. The three statements are **moved out of** `SectionThree.lean` (comment-pointers there; no sorried duplicates). B8 amended with the `hι_proj` pinning (`GQ2/PeripheralAction.lean` docstring; consistency `zhatProjTwo_omega2` proved). Certificates re-checked via `lake env lean` `#print axioms` |
| P-09 | B: Prop 3.2 proof — common tame quotient (`Γ_A` side: Lemma 3.1 ✓ + bridges; local side: B10 + Lemma 3.3 maximality) | ⭐⭐⭐ | O | P-06 | B5, B10 | ☑ 2026-07-03 (`GQ2/Prop32.lean`; in tree, commit pends SectionThree co-owner P-07) |
| P-10 | B: Prop 1.1 proof — marked dyadic Demushkin normalization, `ν_ur = (−2,1,0)` | ⭐⭐ | O | P-06, P-07, P-08 | B3c, B4, B5, B7′ | ◐ (Opus, 2026-07-03): descent infra landed (`GQ2/PropOneOne.lean`); `prop_1_1` assembly blocked on P-07 + P-08⚠ |
| P-11 | B: §4 design — boundary-framed marked targets, exact-image counts, **Thm 4.2 statement** | ⭐⭐⭐ | **F** | — | (statements) | ☑ 2026-07-03 (`GQ2/BoundaryFrame.lean`) |
| P-12 | B: §5 design — Fox–Heisenberg word complex; 5.7/5.8/5.10/5.11/5.13/5.15 statements | ⭐⭐⭐ | **F** | P-11 | (statements) | ☑ 2026-07-03 (`GQ2/FoxHeisenberg.lean`) |
| P-13 | B: §5 proofs (Stokes identities → chain map; dévissage; elementary-module duality 5.15) | ⭐⭐⭐ | O | P-12 | B6, B7 | ◐ (Opus, 2026-07-03) — **Fox–Heisenberg Stokes core done, all std-3**: `d1Fun_add`, `d1Fun_comp_d0`, 5.6, **5.7 (38)/(39)**, **5.8 (41)/(42)**, 5.12; 5.10 absorbed as 5.8+5.6. Note: found+fixed the repo `h₀` transcription bug (dropped bare `d₀`, paper eq.(3)/App.B) — `docs/erratum-h0-transcription.md`. **Remaining sorries**: 5.11 (mapping-cone dévissage), 5.13 normal forms/pairing ×4 (needs §5.1 Lemmas 5.2–5.5 ledger), 5.15 (assembles 5.11+5.13), 5.16 (B6/B7). |
| P-14 | B: §§6–7 design — 6.13 (D₈ class), 6.15→6.17 (Shapiro/cor), 6.8/6.9 (Gauss sign), 6.16→6.18 (Hilbert ledger), 6.21 (transgression) statements | ⭐⭐⭐ | **F** | P-11 | (statements) | ☑ 2026-07-03 (`GQ2/SectionSix.lean` + `GQ2/SectionSeven.lean` + `GQ2/QuadraticFp2.lean` + `GQ2/Corestriction.lean`, `docs/section67-extraction.md`) |
| P-15 | B: §§6–7 proofs | ⭐⭐⭐ | O | P-14 | B5, B6, B7, B7′, B9, B11 | ◐ (Fable+Opus, 2026-07-03): **9/25 proved, all std-3** (§6: 6.1; 6.13 D₈ + (96); **6.22 shear** via explicit coboundary `w(v,c)=f(v,a c)` — `f_cocycle`×4 + `f_polar` + `m_quad`, char-2 close through `CharTwo.two_eq_zero`.  §7: **all of Lemma 7.1** — head + radical + dual; 7.3; **§7 block existence**; `frattiniLike` infra) **+ Prop 7.4 complete modulo its tame step-2 helper** (`lam_sq_vanish`, sorried; 7.4 verifies std-3+sorryAx through it, no B-axioms) **+ reusable infra `comm_bot_of_scalarChain`** (std-3): coprime odd action on a `Y`-central series is trivial (`⁅Ñ,S⁆=⊥`), the key step for 7.2 — Mathlib lacks coprime-action commutator theory, proved here by central-series induction (bottom layer `c 1 ≤ Z`, displacement hom `Ñ→G` into the central 2-layer, odd-coprime ⟹ trivial image).  Statement amendments: `f_cocycle`; `MinimalBlock.hL/h2L` (7.1-head false without — S₃/A₃ counterexample); **7.4 + framed-target head data** (soundness #3 — step 2 needs `H¹(H_V,V^∨) = 0`, tame-only; step 1 `b_λ(T₀,M)=0` proved abstractly as `lam_comm_vanish`).  **6.16 escalation RESOLVED**: B9 base-generalized + B11 added (census 12, user-approved) — `kummerClassK` layer in `GQ2/EvensKahn.lean`, history in `docs/review-packet.md` §2.  Remaining: **7.2** (now unblocked — `comm_bot_of_scalarChain` ready; **tame-free route found**: no Hall/Schur–Zassenhaus needed — get an odd element acting nontrivially on `V` from "`Ȳ=Y/C_Y(V)` not a 2-group" via Cauchy, then three-subgroup lemma [`commutator_commutator_eq_bot_of_rotate`] + class-2 fourth-power hom + `B.minimal` closures); `lam_sq_vanish` (char-2 odd-averaging, `tame_odd_order`); §6 6.6/6.8/6.9 (Gauss-sum counting), 6.14, 6.15-trio (transversal), 6.16→6.18.  NOTE: `lake build GQ2` fails in `GQ2.SectionEight`/`GQ2.AnabelianBridge` (P-16's in-flight untracked files, `ConcreteCategory.ofHom`/`cmhEquivFun` unknown — NOT P-15 breakage; `lake build GQ2.SectionSix GQ2.SectionSeven` green, gate script green) |
| P-16 | B: §8 — half-torsor count 8.6 + closed recursion Prop 8.9 (eqs. (136)–(142)) | ⭐⭐⭐ | **F** draft, O finish | P-11, P-14 | B6, B7, B9 | ◐ **F-draft ☑ + 8.2-candidate proved 2026-07-03** (`GQ2/SectionEight.lean` + `docs/section8-extraction.md`; **proved, all std-3**: engines 8.4/8.5, scalar twisting, and `lemma_8_2_gammaA` — via `ker_char_NA_le_iff` (kills-`N_A` ⟺ kills-`τ`, P-04 both directions) + the exponent-2 `ω₂`-ledger collapse `Marking.wildRel_of_comm2`; **5 sorries allowlisted**: 8.2-local (needs a `BoundaryMaps`-hypothesis amendment, flagged), 8.3, 8.6×2 (blocked-ish on P-13's 5.15/5.16 for the candidate side), `prop_8_9` — remaining work order + O-half log in the design note) |
| P-17 | B: §9 — induction on `\|L_Y\|`: regime 9.1 (Lemma 9.2 ✓), 9.2 (counts + strict decrease (145)/Lemma 9.4), 9.3 (Frattini/Fourier, central formula (151)) ⇒ **Thm 4.2 proof** | ⭐⭐⭐ | **F** design, O finish | P-11–P-16 | B6, B7, B7′, B8, B9 | ☐ |
| P-18 | B: Lemma 10.1 (tame-frame exhaustion) + eq. (154) ⇒ `main_surjection_count` | ⭐⭐ | O | P-09, P-10, P-17 | (all of Track B) | ☐ |
| P-19 | Assembly: `main_presentation_literal` via `main_presentation` | ⭐ | O | P-02, P-03, P-05, P-18 | B1 + Track B | ☐ |
| P-20 | Meta: review packet v3 — interior-node statements + App. D certificate diff, at statement freeze | ⭐ | O | P-06, P-11, P-12, P-14 | — | ☐ |
| P-21 | Foundations: ℤ₂-powering on pro-2 groups — `maxPro2(ℤ̂) ≅ ℤ₂` (the `ι`-seam), `zpowZtwo` + unit/odd-power bijectivity, `IsProP 2 ℤ₂ˣ` + `η`-injectivity, pro-2 Frattini criterion | ⭐⭐⭐ | **F** | — | ∅ | ☑ 2026-07-03 (`GQ2/ZtwoPowering.lean` (i)–(iii) + `GQ2/FrattiniCriterion.lean` (iv); all std-3, zero sorries). **Unblocks P-07 η-leg, all three P-08 legs' infra, `prop_3_10` `ι`-seam** |

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
- **P-02** ☑: sorry replaced; **zero sorries in `Reconstruction.lean`**, allowlist entry removed,
  `exists_contSurj_of_card_le`/`reconstruction_of_equinum`/`reconstruction` all `#print axioms` =
  std-3 (`lean_verify`'d), `check_axioms.sh` green (census 10).  Level sets nonempty+finite via
  `contSurj_quotient_nonempty_finite`; the compatible family via `konigFunctor : OpenNormalSubgroup
  (ProfiniteGrp.of R) ⥤ Type` + `nonempty_sections_of_finite_cofiltered_system` (König), as the
  recipe said.  **Deviation from the recipe's assembly step**: instead of building a cone over
  `ProfiniteGrp.diagram R` and `isLimitCone.lift`, the section is assembled by an **elementary**
  embedding `e : R ↪ ∏_U R/U` (closed embedding, `R` compact/`Q` Hausdorff) + **two Cantor
  intersections** (`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`): one in `R`
  realizes each compatible family as `e r` (⇒ `ψ := e⁻¹∘Φ` a continuous hom), one in `S` gives `ψ`
  surjective.  **Why**: the `ProfiniteGrp.diagram` objects carry the discrete `⊥` topology, not
  `R/U`'s coinduced (equal but not defeq) topology, and `(diagram R).obj U` won't even synthesize a
  `TopologicalSpace` when used as a bare `ContinuousMonoidHom` codomain — so the categorical
  cone/lift route fights Mathlib's `CompHausLike`/`FiniteGrp` coercions at every step.  The
  product-embedding route stays in natural quotient topologies throughout.  Reusable spinoffs (top
  of the file, `open CategoryTheory`): `projMap`(+`_mk`/`_surjective`/`_id`/`_comp_apply`) and
  `konigFunctor` — for **P-04/P-05** (also over `OpenNormalSubgroup (ProfiniteGrp.of _)`).
- **P-03**: `FreeProfiniteGroup X` is t.f.g. for finite `X` (the generators' images topologically
  generate — density of the free group in its completion); t.f.g. passes to `profiniteQuotient`;
  instantiate: `GammaA` t.f.g. in the exact `∃ s : Finset _, …` form `main_presentation` consumes.
  *Done (`GQ2/FinitelyGenerated.lean`, std-3):* predicate `IsTopologicallyFinGen G` (unfolds to the
  raw `main_presentation` form); `IsTopologicallyFinGen.of_surjective` (transfer along a continuous
  surjection — `DenseRange.topologicalClosure_map_subgroup`); `isTopologicallyFinGen_freeProfiniteGroup`
  (finite `X` — `ProfiniteGrp.ProfiniteCompletion.denseRange` + `FreeGroup.closure_range_of`);
  `gammaA_isTopologicallyFinGen` + `gammaA_topologicallyFinitelyGenerated` (the raw `∃`-form P-19 feeds
  to `main_presentation`).
- **P-04** ☑: (i) `tameRelator`/`wildRelator` of `univMarking` lie in `NA` (each dies in every
  admissible quotient — `map_*Relator_eq_one_iff` + `IsAdmissibleU`); (ii) the closed normal
  closure of `{x₀, x₁}`-images in `Γ_A` is pro-2 (`IsProP 2`, via `MaxProP.lean`'s
  characterization: every open normal subgroup of `Γ_A` pulls back to an admissible-dominated one —
  the Lemma 2.1 subdirect-closure argument).  Design note documenting the limit argument.
  *Done (`GQ2/AdmissibleLimit.lean`; every theorem `#print axioms` = std-3; no allowlist changes —
  pure proof ticket).*  Deliverables: (i) `tameRelator_mem_NA`/`wildRelator_mem_NA` +
  `quotientMk_*Relator_eq_one` (relations (5)/(6) hold in `Γ_A`); (ii) `wildCore` (the closed
  normal closure `⟨⟨x₀,x₁⟩⟩`, on the raw quotient `F₄ ⧸ NA` ≡ᵈᵉᶠ `GammaA`) with
  `isProP_wildCore : IsProP 2 wildCore`.  **P-05 interface**: `isAdmissibleU_iff_NA_le`
  (admissible opens = opens above `N_A`) and `generates_univMarking_map` (generation is automatic
  in every finite quotient — density of `FreeGroup` in its completion).  Engine (design note in
  the module docstring): `isAdmissibleU_top` (trivial quotient admissible — nonvacuity without
  App. B) + `isAdmissibleU_inf` (Lemma 2.1 subdirect closure, elementwise 2-power form
  `isPGroup_normalClosure_image_inf`) ⇒ directedness ⇒ compactness domination
  (`exists_isAdmissibleU_le`, the `proPKernel`-style argument) ⇒ `isAdmissibleU_of_NA_le`
  (Lemma 2.2 pushforward).  Lean gotcha recorded: state `wildCore` on `F₄ ⧸ NA`, not
  `Subgroup GammaA` — mixing the `↥GammaA` and raw-quotient spellings breaks instance search
  (`Membership`-instance mismatch), while everything is defeq on the raw type.
- **P-05** ☑: the bijection `ContSurj GammaA G ≃ {t : Marking G // t.Admissible}` for finite discrete
  `G`: forward = push `univMarking` (admissible by P-04 + Lemma 2.2 `map_admissible`); backward =
  `quotientLift` along `NA_le_ker` (T-21); round-trips via `univMarking_map_toHom` and topological
  generation (P-03).  `Nat.card` conclusion in exactly `main_presentation`'s `hΓA` form.
  *Done (`GQ2/Prop23.lean`; zero sorries; `prop_2_3` and all helpers `#print axioms` = std-3).*
  Headline: `prop_2_3 : Nat.card (ContSurj GammaA G) = admissibleCount G` via
  `contSurjEquivAdmissible` (assembled from named halves `Marking.push`/`Marking.descend` with
  `push_admissible`, `descend_surjective`, `push_descend`, `descend_push`).  Key new lemma:
  `admissible_of_NA_le_ker` — the **converse of `NA_le_ker`** (surjective + `N_A ≤ ker` ⇒ pushed
  marking admissible, via P-04's `isAdmissibleU_of_NA_le` + Lemma 2.2 transfer along
  `quotientKerEquivOfSurjective`); together they characterize admissible markings of `G` as the
  continuous surjections `F₄ ↠ G` killing `N_A`.  **Deviations from this sketch**: (i) t.f.g.
  (P-03) is *not needed* — the round-trip uses the **uniqueness half of the universal property**
  (`Marking.toHom_univMarking_map`: every `f : F₄ ⟶ P` is `toHom` of its own pushed marking;
  CMH-level form `toHom_hom_univMarking_map` via `ConcreteCategory.ofHom`, whose constructor is
  the public route — `ProfiniteGrp.Hom.mk` is private); (ii) the equiv is stated on `F₄ ⧸ NA`
  (defeq `GammaA`, the P-04 spelling convention), `prop_2_3` itself on `GammaA`.  Lean gotchas:
  prove uniqueness by `rw [Marking.toHom, Equiv.symm_apply_eq]` then rewrite
  `homEquiv_apply` **before** `fin_cases i <;> rfl` (otherwise `rfl` unfolds the completion
  adjunction — deterministic timeout), and keep the equiv's fields as *named* lemmas — inline
  `by`-blocks inside the `Equiv` literal retrigger the same timeout via nested-proof abstraction.
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
  *P-09 done (`GQ2/Prop32.lean`, ~1250 lines, zero sorries).*  `prop_3_2_gammaA` **proved at
  std-3 — no axioms at all** (classifier `F₄ → T_tame` kills `N_A` via the ω₂ word-ledger
  collapse at odd-order `τ̄`; mutually inverse maps by generator density); `prop_3_2_local`
  **proved at std-3 + B10 exactly** (the declared Ax was an upper bound; B5 unused): the
  maximality of the B10 wild subgroup via `eq_bot_of_normal_two_images` — the paper's
  Lemma 3.3 argument with concrete Fermat levels `G_m = C_{2^{2^m}−1} ⋊ C_{2^m}`
  (faithful inverse-squaring `SemidirectProduct`, trivial center, `ord(2 mod e_m) = 2^m` by
  the Fermat-number trick), a procyclic level-comparison in `Q = T_tame/⟨⟨τ⟩⟩` (cyclic
  `#K`-torsion lemma `mem_of_orderOf_dvd_card`), and the odd∧2-power kill on inertia.  Also
  proved: `nuT_surjective`, `nuTwo_surjective` (their sorried statements deleted from
  `SectionThreeMarked.lean`), the reusable density pack (`topGen_*`, `monoidHom_eq_of_topGen`),
  and `isPGroup_map_of_isProP`.  The two `prop_3_2` sorries are deleted from
  `SectionThree.lean` (allowlist entry stays for the remaining P-07/P-10 sorries).
  **Commit note**: `Prop32.lean` imports the P-04/P-07 dedup layer (`wildCore`,
  `wildPart_eq_closure`) still uncommitted in `SectionThree.lean`/`AdmissibleLimit.lean` —
  commit together with (or after) those.  Gotcha for the record: `continuous_quot_mk` pins
  the generic quotient topology into instance goals; use `QuotientGroup.continuous_mk` when
  downstream needs `QuotientGroup` instances (`IsTopologicalGroup (G ⧸ N)` etc.).
- **P-07** ◐ (partial): `lemma_3_5_hilbert_ledger` **proved** (six `hilbertSymbol_dyadic`
  evaluations; `#print axioms` = std-3 + B7′, matching the **Ax**), and the missing
  `import GQ2.Foundations.Axioms` added to `SectionThree.lean` (P-08 needs it too).  **⚠ D₀ fixed to
  pro-2 (structural correction, `GQ2/DyadicPresentation.lean`)**: `D0` was `profinitePresentation
  {d0Relator}` — a *full* profinite group (it surjects onto `ℤ/3`: `A,S↦0,Y↦1` kills the relator),
  so `topAbelianization D0 ≅ ℤ/2 × Ẑ × Ẑ`, making `b_decomposition`'s `ℤ/2 × ℤ₂ × ℤ₂` target
  *unprovable* and **axiom B4** (`maxProQuotient 2 AbsGalQ2 ≅ D0`) non-faithful (pro-2 ≅
  non-pro-2 — a latent inconsistency).  Now `D0 := maxProPQuotient 2 D0Full` (pro-2), with
  `d0FullA/S/Y : D0Full` + `d0Full_relation` and `d0A/S/Y := maxProPMk 2 D0Full d0Full…`;
  `d0_relation` and `d0A/S/Y : D0` unchanged, so `Orientation`/`SectionThree`/B4 recompile
  unaffected (validated: `lake build GQ2.Orientation GQ2.Foundations.Axioms` green).  **Consumers
  (P-10) note**: `D0` is now genuinely pro-2.  **Remaining (blocked on new infra)**:
  `b_decomposition`, `lemma_3_5_injective`, `lemma_3_5_marked_abelianization` need a
  **pro-2-abelianization layer** (free pro-2 abelian `≅ ℤ₂^X`, `topAbelianization` congruence along
  a `ContinuousMulEquiv`, the explicit `D₀^ab ≅ ℤ/2×ℤ₂×ℤ₂` basis change) — absent from repo+Mathlib,
  a large foundational build (arguably its own infra ticket).
- **P-10** ◐ (partial — the provable-now part): `GQ2/PropOneOne.lean` (new file, `lake build GQ2`
  green, both key theorems `lean_verify`'d = std-3; **`prop_1_1`'s `SectionThree.lean` sorry is
  untouched**, so no allowlist change yet).  Delivered the design-note §1.1 descent infrastructure:
  `isProP_two_multPadicInt : IsProP 2 (Multiplicative ℤ₂)` (every open subgroup of `ℤ₂` contains
  `span{2ⁿ}` — `PadicInt.norm_le_pow_iff_mem_span_pow` — so `2ⁿ` uniformly annihilates the quotient;
  reusable, also for P-09's `nuTwo`) and the **`ν_ur`-descent** `nuUrBar`/`nuUrBar_maxProPMk`/
  `nu_ur_toAb_eq_of_maxProPMk_eq` (`ν_ur ∘ toAb` factors through `maxProPMk 2 G_{ℚ₂}` via
  `maxProPHomEquiv`) — the well-definedness `prop_1_1`'s `ν_ur`-rows read off `maxProPMk`.
  **`prop_1_1` itself remains blocked**: its assembly composes B4's iso with Lemma 3.5's marked
  abelianization (**P-07**, in progress) and Prop. 3.8's automorphism lift (**P-08**, ⚠ escalated —
  needs the new "ℤ₂-powering on pro-2 groups" foundations ticket, `docs/section3-extraction.md`
  §Escalations 4).  When those land, `prop_1_1` closes by: take `e₀` from B4, correct its marking by
  the Prop. 3.8 lift of the (orientation-preserving, by B3c) automorphism `φ = e₀^{ab}∘e'` matching
  Lemma 3.5's `e'`, then the `ν_ur`-rows follow from `nuUrBar_maxProPMk` + `Reciprocity.lean`'s
  eq. (13) rows.  So P-10 is unblocked-modulo-P-07/P-08, not design-blocked.
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
  *P-12 done (`GQ2/FoxHeisenberg.lean`, namespace `GQ2.FoxH`; proved layer std-3, zero B-axioms).*
  Defs: `Marking.tameValue/wildValue` (relations (5)/(6) as elements, `= 1 ↔ Rel` proved);
  `WordLift A C` (paper's `(u,g)(v,h) = (u+g•v, gh)`, own instances — no `Multiplicative`
  wrappers); the word complex (30)/(31): `d0` proved-additive, `d1Fun` = the literal
  A-coordinates of the evaluated relator values at `liftMarking`, with **Fox linearity
  `d1Fun_add` as a named sorried obligation** (bundled `d1` built on it; `Z1w/H0w/H1w/H2w`
  ContCoh-shaped total defs); `ElemDual` (T-14 recipe, contragredient action); `HeisLift`
  (§5.2 Heisenberg ⋊, group laws proved incl. the char-2 center); `mixedB` = traced `β_t+β_w`;
  `stokesEval`/`expMod2` (general 5.7 form on Mathlib `FreeGroup`); `dualEval` + `fixedPts`;
  `x0Supported`, `IsSimpleModTwo`, `IsSelfDual` (the (56)-package: card numerics +
  ∃-descended nondegenerate pairing).  Sorried statements (15, all tagged P-13):
  `d1Fun_add`, `d1Fun_comp_d0`, 5.6, 5.7 (38)/(39), 5.8 (41)/(42), 5.11 (2-of-3 for
  `IsSelfDual`), 5.12, 5.13 (split/ramified shapes + (54) pairings), 5.15, 5.16 (T-14-style
  cup perfectness + `#H²(𝔽₂)=2` line clause; **B6/B7 enter only in its proof**).  Proved
  stress: `d1Fun_tame` (the (34) tame row in closed form — validates the whole convention
  stack), `expMod2_fgTame` ((0,1,0,0) exponent vector), `cor_5_17_card` (5.17-numerics wiring).
  **Deviations flagged in-module**: 5.10 carried as 5.8+5.6 component identities (no
  `HomologicalComplex`); 5.11 in quasi-iso-consequence form (cone (49) = proof device); 5.1
  absorbed by `powOmega2` encoding; **5.17's adjoint-boundary (58) deferred** (needs
  connecting-map infra in both theories — owner P-13, shape arbitrated by P-17); 5.2/5.3/5.4/
  5.14 + Remark 5.9's GL₂(𝔽₂) regression test = P-13 proof layer.
  *P-14 done (`GQ2/SectionSix.lean` + `GQ2/SectionSeven.lean`; sorry-free def-layers
  `GQ2/QuadraticFp2.lean` + `GQ2/Corestriction.lean`; design note + full display map + deviation
  ledger in `docs/section67-extraction.md`).*  25 sorried statements (18 §6 + 7 §7, all tagged
  P-15; verified std-3 + `sorryAx` only — no B-axiom leakage; proved infra at std-3):
  `graphPullback_mem_Z2` (6.1/(62)), 6.6, 6.8, 6.9×2 (unram/ram via (83)'s branches), 6.13×2
  (`D₈` fibre extension of the `decide`-checked `twoPointExt` + (96) against `evensNormH2`),
  6.15×3 ((103)/(104)/(105) per orbit type on `RegRep`, canonical `Quotient.out` transversals;
  (105) absorbs (100)), 6.16 (deep-unit Evens norm — `IsDeepUnit` via the spectral norm on
  `ℚ̄₂`, `‖b‖ < 1`; unramifiedness = index-2 fixing subgroups + equal norm value groups), 6.17×2
  (`deepPart`; `#X₊² = #H¹`; `Q⁰_loc`-vanishing), **6.18×2 (the headline Gauss counts on
  `Q0loc`)**, 6.14 ((102) via `FactorSet.comap` + `mapCoeff1`), 6.21 (consequence/splitting
  form), 6.22 ((121) cochain-exact mod explicit coboundary); §7: `exists_minimalBlock`,
  7.1×3 (radical/head-as-`R ≤ K⊓S`/dual-as-no-index-2), 7.2 (tame head via `Ttame`-marked
  surjection), 7.3, 7.4 (`∃ q̄_λ` bundled with spec — §8's Gauss-sum form).  Key encodings:
  `ι_F = inv_ℚ₂` = `iotaF D` through the `𝔽₂ ≅ μ₂` bridge (B6's `D.inv`, statements
  parametrized over `D : TateDuality 2` — statement layer axiom-free); ramified/unramified =
  `c tameTau`-action through `ρ = c ∘ B.tameF` (`BoundaryMaps`); `SemiProd` = same
  no-`Multiplicative` carrier convention as P-12's `WordLift` (independent convergence);
  democratic `arf`.  Trimmed with flags: 6.5→P-12 seam, 6.19→P-16 assembly, 6.4+6.7/6.10/6.11
  = P-15 proof-internal.
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
- **P-21** (the foundations ticket requested by P-08's escalation — `docs/section3-extraction.md`
  §Escalations 4; opened by user decision 2026-07-03): `GQ2/ZtwoPowering.lean`, **no axioms, no
  sorries, everything std-3** (pure infra; Ax = ∅).  Scoped phases, partial landing legible:
  **(i) the projection + seam iso** — `zhatProjTwo : ℤ̂ → Multiplicative ℤ₂` (defined as
  `(ofAdd 1) ^ᶻ ·`, so the T-06 anchors come free), surjectivity, `ker = proPKernel 2 ℤ̂`, and
  `ztwoEquivPadic : ContinuousMulEquiv (maxProPQuotient 2 Zhat) (Multiplicative ℤ₂)` pinned by
  `maxProPMk (ofInt 1) ↦ ofAdd 1` — **this is the `ι` of `prop_3_10_local_marked`**
  (`Ztwo := maxProPQuotient 2 Zhat` defeq) and the T-12 nice-to-have `maxPro2(ℤ̂) ≅ ℤ₂`;
  **(ii) `zpowZtwo`** — `x^u` for `u ∈ ℤ₂`, `x` in any pro-2 `P` (`IsProP 2 P` hypothesis), via
  `maxProPHomEquiv` through (i); anchors (`= x^n` on `ℤ`, exponent-additivity, composition
  `(x^u)^v = x^{uv}`, naturality, **uniqueness** of a continuous hom `ℤ₂ → P` by its value at
  `1`) and **bijectivity of `x ↦ x^u` for `u ∈ ℤ₂ˣ`**, specialized to odd integer powers
  (P-08's cube roots);
  **(iii) the `η`-facts** — `IsProP 2 ℤ₂ˣ` (uniform annihilation: `‖u^{2^k}−1‖ ≤ 2^{-(k+1)}` by
  ultrametric factoring, no binomials) and **`η`-injectivity**: `‖η−1‖ = 2⁻² ⇒ u ↦ η^u`
  injective (exact-level squaring + (ii)-bijectivity; no closed-subgroup classification) — the
  shared P-07 (`lemma_3_5_injective`) / P-08 (`prop_3_8_classification`) prerequisite, with the
  `η = (−3)⁻¹` anchor;
  **(iv) pro-2 Frattini/Burnside** ("surjective on `G/Φ(G)` ⇒ surjective") — phase 2 of this
  ticket (route sketched in the module docstring: Mathlib `frattini` + finite `p`-groups
  nilpotent + maximal-⇒-normal-index-`p`); its only consumers (`lemma_3_7`/`prop_3_8_lift`
  surjectivity legs) are still blocked on the escalation's (a) HNN gap, so (i)–(iii) land first.
  *Phases (i)–(iii) done (2026-07-03):* `GQ2/ZtwoPowering.lean`, imported in `GQ2.lean`;
  `lake build GQ2` + `check_axioms.sh` green; key theorems `lean_verify`'d = std-3
  (`ker_zhatProjTwo`, `zpowZtwo_zpowZtwo`, `pow_bijective_of_odd`, `isProP_two_unitsPadicInt`,
  `zpowZtwo_injective_of_exact_level`).  Deviations from the sketch, all documented in-file:
  the density workhorse is `multPadicIntHom_ext` (via Mathlib's
  `DenseRange.addChar_eq_of_eval_one_eq` — continuous homs out of `ℤ₂` are pinned by their
  value at `1`), which makes every algebraic law of `zpowZtwo` a one-liner; the `ker ⊆`
  direction of (i) identifies any finite 2-group quotient map of `ℤ̂` with a mod-`2^k` powering
  (`powZModTwoHom`, the finite-order `ℤ₂`-powering gadget) by `funext_ofInt`; part (iii)'s
  level-tracking is **divisibility-with-unit-witnesses** (`2^{k+1} ∣ u^{2^k} − 1`;
  `η^{2^k} − 1 = 2^{k+2}·unit`), no real-norm induction — norms appear once, at the
  `Units`-topology ball bridge; the `η`-hypothesis is the algebraic `η − 1 = 4a` (`a ∈ ℤ₂ˣ`,
  ⟺ `v₂(η−1) = 2`), with the `(−3)⁻¹` instance `zpowZtwo_injective_neg_three_inv` as the
  direct P-07/P-08 consumable.  Bonus: `zpowHat_eq_zpowZtwo` (T-06 `ẑ`-powers factor through
  `ℤ₂` on pro-2 groups — the `ω₂`-word bridge) and the `TotallyDisconnectedSpace ℤ₂ˣ/ℤ₂ᵐᵒᵖ`
  instances (Mathlib had compactness/T2 for units but not these).
  *Phase (iv) done (same day):* `GQ2/FrattiniCriterion.lean` (imported in `GQ2.lean`;
  `lake build GQ2.FrattiniCriterion` + guard green; `lean_verify` = std-3 on
  `coatom_index_of_pGroup`, `eq_top_of_forall_not_le_index_p`,
  `surjective_of_forall_index_p_quotient_surjective`).  **Index-`p`-detection form** — no
  `Φ(K)` object: finite ingredients `coatom_normal_of_pGroup` (via `IsPGroup.isNilpotent` +
  `Group.normalizerCondition_of_isNilpotent` + `Subgroup.NormalizerCondition.normal_of_coatom`,
  all Mathlib) and `coatom_index_of_pGroup` (the coatom quotient is simple by the subgroup
  correspondence, abelian since its centre is nontrivial-normal, so `ℤ/p` by
  `IsSimpleGroup.prime_card`); profinite side: `eq_top_of_forall_map_eq_top` (closed subgroup
  with full image in every open-normal quotient is dense, via
  `exist_openNormalSubgroup_sub_open_nhds_of_one` — no T2 needed), then pull a coatom above the
  image back (`Finite.to_isCoatomic` + `comap`; index preserved by
  `index_comap_of_surjective`).  Hom forms take `[T2Space K]` only (closed range).  Note at
  landing time the *aggregate* `lake build GQ2` was transiently red in `GQ2/SectionSeven.lean`
  (P-15's in-flight edits, unrelated); `GQ2.FrattiniCriterion`/`GQ2.ZtwoPowering` build green
  in isolation.
