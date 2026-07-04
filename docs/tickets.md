# Ticket board — step 2 (proving Theorem 1.2 from the axioms)

Source of truth for the proof phase.  Rationale, DAG, conventions, and wave schedule:
[`step2-plan.md`](step2-plan.md).  The **step-1 board** (statement formalization, ticket IDs
`T-xx` cited in module docstrings) is archived at [`tickets-step1.md`](tickets-step1.md).
Difficulty: ⭐ easy · ⭐⭐ medium · ⭐⭐⭐ hard/design-sensitive.  Model: **F** = Fable
(design-heavy), **O** = Opus (well-specified).  Status: ☐ open · ◐ in progress · ☑ done.

Rules: **no new `axiom`s without explicit user approval** (census at 13 — B10 added by explicit decision, P-06 escalation; B9 base-generalized + B11 added by explicit decision, P-15 escalation, user-approved 2026-07-03; **B11 split into B11a `hilbertSymbol_normCriterion_finiteDyadic` + B11b `unramifiedQuadratic_units_are_norms` by P-23, census 12→13, user-approved 2026-07-04** — `dyadicNormCriterion` kept as a same-name theorem, spectral-norm bridge isolated as a `def IsUnramifiedQuadraticSpectral`, not an axiom); statement tickets add their sorried theorems to
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
| P-07 | B: Lemmas 3.4/3.5 proofs (eq. (13) ledger: square-class basis, χ/ν rows, cup form `α²+βγ+γβ`) | ⭐⭐ | O | P-06 | B5, B7′ | ☑ **CLOSED 2026-07-03 (Opus)** — all four clauses proved, `SectionThree.lean` sorry-free & off the `SORRY_ALLOWLIST`, census unchanged (12). `lemma_3_5_hilbert_ledger` ✓ (B7′) **and `lemma_3_5_injective` ✓ (std-3)** — the latter via a self-contained pro-2-abelianization layer in `SectionThree.lean` (`isProP_two_topAb_D0`, `zpowZtwo` helpers, `D0ab_coord`: `D₀^ab ∋ z = Ā^aS̄^sȲ^y`, topological generation through `F₃↠D0Full↠D₀↠D₀^ab`); coordinate argument uses P-21 `η`-injectivity + a mod-4 unit reduction. `topAbelianization` profinite instances kept **`local`** (a global generic instance perturbs `AnabelianBridge`'s `K⧸M` synthesis; verified both build). **`b_decomposition` ✓ (std-3)** — `D₀^ab ≅ ℤ/2×ℤ₂×ℤ₂` via coordinate homs `τ,σ,γ` (local `d0LiftHom` universal-property replica + `abLift` descent through `abMk`), combined into `φ` shown bijective. **All 4 clauses now have proofs.** `lemma_3_5_marked_abelianization` (B5) is **proved modulo one clean lemma `markedHom_bijective`** (std-3 + sorryAx): the descent `markedPi` (`G_ℚ₂^ab→(G_ℚ₂(2))^ab`, all-lifts-agree), the marked hom `markedHom` (`Ā,S̄,Ȳ↦rec(−4),rec(1/2),rec(−3)`, relation `(−4)²·2⁻⁴=1` verified), and the generator matching are **all std-3**; the sole remaining sorry is `markedHom_bijective` (the pro-2 reciprocity iso: `{rec(−4),rec(1/2),rec(−3)}` coordinatize `(G_ℚ₂(2))^ab`). **Census-gating claim RETRACTED (Fable re-audit), then derivation EXECUTED (Opus):** B5 carries `denseRange_recip` + `continuous_recip`, so `markedHom_bijective` is provable from B5 as-is. **Now proved** (`#print axioms markedHom_bijective = std-3` since `R` is a param): injectivity via `nuT`/`chiT` descents (`abLiftG`) feeding the already-proved `lemma_3_5_injective`; surjectivity via `DenseRange (markedPi∘rec)` + the arithmetic lemma `units_gen` (`ℚ₂ˣ = ⟨−4,2,−3⟩·(ℚ₂ˣ)²`: valuation split + `hensel_sq` (Mathlib `hensels_lemma`) + `mod8_sq` (`toZModPow 3` casework) + `norm_one_unit`) + finite-2-Frattini `sq_generate` (coatom) + `eq_top_of_forall_map_eq_top`. `lemma_3_5_marked_abelianization` ✓ (B5); **P-10 `prop_1_1` thereby sorryAx-free** (std-3 + B3c + B8). The `norm_reciprocity`/Galois route was dominated and not taken. |
| P-08 | B: Lemmas 3.6–3.8 proofs (cyclotomic conjugation of peripherals; wild-relation shape) | ⭐⭐ | O | P-06 | B2, B8 | ☑ 2026-07-03 (Fable): all three theorems proved in `GQ2/AnabelianBridge.lean`, namespace `GQ2.SectionThree` — **`lemma_3_7`** (std-3 + B8), **`prop_3_8_lift`** (std-3 + B8; `α_{u,b} = θ_b ∘ ψ_u`: `ψ_u` from the B8 action pushed through `deltaLift`/`d0Lift` + Frattini surjectivity, `θ_b` the `Y ↦ S^bY` shear with `theta_relator`), **`prop_3_8_classification`** (**std-3 only, axiom-free**: `t`-torsion fixing + `η`-mod-4 kill of the `(−1)`-component + `D0ab_coord` rows; `u ∈ ℤ₂ˣ` forced via the same row for `ξ⁻¹`). B2 turned out unneeded. The three statements are **moved out of** `SectionThree.lean` (comment-pointers there; no sorried duplicates). B8 amended with the `hι_proj` pinning (`GQ2/PeripheralAction.lean` docstring; consistency `zhatProjTwo_omega2` proved). Certificates re-checked via `lake env lean` `#print axioms` |
| P-09 | B: Prop 3.2 proof — common tame quotient (`Γ_A` side: Lemma 3.1 ✓ + bridges; local side: B10 + Lemma 3.3 maximality) | ⭐⭐⭐ | O | P-06 | B5, B10 | ☑ 2026-07-03 (`GQ2/Prop32.lean`; in tree, commit pends SectionThree co-owner P-07) |
| P-10 | B: Prop 1.1 proof — marked dyadic Demushkin normalization, `ν_ur = (−2,1,0)` | ⭐⭐ | O | P-06, P-07, P-08 | B3c, B8 (B5 via param) | ☑ **CLOSED 2026-07-03** (Fable assembled, closed when P-07 landed): **`prop_1_1`** in `GQ2/PropOneOneAssembly.lean` (`GQ2.SectionThree.prop_1_1`), statement moved out of `SectionThree.lean` (comment-pointer). `#print axioms` = **std-3 + B3c(`dyadicOrientation`) + B8(`peripheralCyclotomicAction`)** — **sorryAx GONE** now that P-07's `markedHom_bijective` is proved; **nothing else**. Actual Lean axioms **B3c + B8** (not B4 — subsumed by B3c; not B5 — `R` is a param; not B7′ — Lemma 3.5's marked clause is B5-only). Assembly = B3c's `orientBundle.equiv` adjusted by the Prop-3.8-lifted (P-08) automorphism realizing the χ-preserving comparison `Θ = eab∘equivAb`, so `abMk(e.symm gen) = markedPi(rec …)`, then `ν_ur` reads off via the descent `nuUrBarAb`. New infra: generic `topAbCongr` (functorial topological abelianization), `abDescend`, `d0ab_hom_ext` (generator extensionality via `D0ab_coord`), χ-descents `chiD0`/`chiG`. `lake build GQ2.PropOneOneAssembly` green (8618); own-scope + check_axioms(census 12) pass |
| P-11 | B: §4 design — boundary-framed marked targets, exact-image counts, **Thm 4.2 statement** | ⭐⭐⭐ | **F** | — | (statements) | ☑ 2026-07-03 (`GQ2/BoundaryFrame.lean`) |
| P-12 | B: §5 design — Fox–Heisenberg word complex; 5.7/5.8/5.10/5.11/5.13/5.15 statements | ⭐⭐⭐ | **F** | P-11 | (statements) | ☑ 2026-07-03 (`GQ2/FoxHeisenberg.lean`) |
| P-13 | B: §5 proofs — **decomposed → P-13a–g** (parallelizable; see [`p13-ticket-split.md`](p13-ticket-split.md)) | ⭐⭐⭐ | O | P-12 | B6, B7 | ◐ (2026-07-04) **only P-13f open** — P-13a/b/c/d/e/g all ☑. `lemma_5_11` (P-13e, `GQ2/Devissage.lean`) and `prop_5_16` (P-13g, `GQ2/LocalLiftingDuality.lean`) PROVED std-3; the whole §5 duality assembly now reduces to `prop_5_15` (P-13f parts ii/iii). |
| P-13a | B: §5 wild-Fox + mixed-Hessian engines & split §5.13 (Stokes 5.6–5.10; wild row 5.4/5.5; Hessian 5.14 toolkit; `lemma_5_13_split` + `lemma_5_13_pairing_split`) | ⭐⭐⭐ | O | P-12 | — | ☑ 2026-07-04 (Opus; `GQ2/FoxHeisenberg.lean`, all std-3) |
| P-13b | B: §5.13 ramified normal form (`lemma_5_13_ramified`; V^T=0 ⇒ wild row S⁻¹d, unique x₀-supported rep) | ⭐⭐⭐ | O | P-13a | — | ☑ **DONE (Opus, 2026-07-04)** — `lemma_5_13_ramified` **sorry-free, std-3** (`{propext, Classical.choice, Quot.sound}`, no B-axioms = "Ax —"); library builds green (8591 jobs). **Statement amended** (both needed, mirror split's `hU`/`hVS`; supplied per-simple-factor by P-13d — `hTodd`+`hU` must both hold on each factor for P-13f): `hTodd : ∀ v, powOmega2 t.τ • v = v` (τ odd-order on V) + `hU : ∀ v, t.sigma2 • v = v` (σ₂ trivial). Nothing consumed it, so safe. **Assembly**: `(T−1)` surjective on finite V (`Finite.injective_iff_surjective` from `V^T=0`); `v=(T−1)⁻¹x₁`; wild row ⟹ `x₃=0`; reduced cocycle `x−d0 v` has zero `x₁`-slot so its tame row (`d1Fun_tame`) `σ⁻¹(T−1)x'₀=0` forces `x'₀=0`; `x−x0Supported(x₂)=d0 v`, `c=x₂` unique via the `x₂`-coord. **Full details below.** — **hyp gap RESOLVED + full ramified engine layer (all std-3)**: (1) **statement amended** — added `hTodd : ∀ v, powOmega2 t.τ • v = v` (τ's 2-part acts trivially = τ odd-order on V; ramified twin of split's `hU`, supplied per-factor by P-13d; nothing consumes the lemma yet so signature change is safe); (2) **4 engine lemmas** in the wild-Fox section — `sum_pow_smul_eq_zero` (general `P=0`: fixed-point-free σ + `σᴷ` fixes u ⟹ `∑_{i<K}σⁱu=0`), `norm_eq_zero_of_fixedPointFree` (orderOf corollary), **`powOmega2_u_of_oddFixedPointFree`** (the ramified twin of `powOmega2_u_of_trivial`: fixed-point-free odd-order base ⟹ `(powOmega2 p).u=0`, via `pow_u`+`powOmega2_pow_eq`+the ledger), `powOmega2_smul_of_trivial_mul` (ω₂-transparency of a trivial left factor, via `powOmega2_map` naturality — lets bases `x₁τ`/`x₀τ` inherit `hTodd` from τ). **FULL RAMIFIED WILD ROW LANDED (all std-3)**: statement further amended with `hU : ∀ v, t.sigma2 • v = v` (also needed — `g0 = sigma2²` in `h0`; mirrors split exactly), and the complete aux-word layer landed — `liftMarking_{u0,u1}_{u,g}_ramified` (offsets `=0`, bases trivial), `liftMarking_d0_{g,u}_ramified` (`d0.u = x₂`, the `P=0` `c`-survives/`b`-dies), `liftMarking_c0_u_ramified` (`=0`; `z0.g` reuses the split lemma), `liftMarking_h0_{g,u}_ramified` (`h0.u=0`, the `x₂+x₂+x₂+x₂` cancellation), and **`liftMarking_wildValue_u_ramified : wildValue.u = t.σ⁻¹ • x₃`** = the display-(53) wild row `S⁻¹·d`.  All mirror the split proofs with `u0.u=u1.u=0` (collapse) substituted. The `∃!`-assembly (see the header above) is now landed too — `lemma_5_13_ramified` is complete. See P-13b in `p13-ticket-split.md` |
| P-13c | B: §5.14 ramified mixed Hessian (`lemma_5_13_pairing_ramified`; λ((1+U+U⁻¹)c), U=σ₂ nontrivial) | ⭐⭐⭐ | O | P-13a | — | ☑ **DONE (Opus, 2026-07-04)** — `lemma_5_13_pairing_ramified` proved std-3, sorry-free (`heisMarking_{h0,c0,wildValue}_z_ramified` + `HeisLift.conjP_*_of_slice` + `elemDual_fixedPointFree_of`); adds `hTodd` per P-13b precedent. Build 8591 jobs; #axioms=12 |
| P-13d | B: §5 tameness rep-theory (central σ₂ 2-pow-order ⇒ σ₂=1; V^σ submodule ⇒ V^S=0; supplies hU/hVS to P-13f) | ⭐⭐⭐ | O | 5.12 (done) | — | ☑ 2026-07-04 (Opus; `GQ2/TameSimple.lean` std-3; `sigma2_smul_trivial`+`fixedPoints_sigma_eq_zero` via `central_pow2_smul_trivial`, the centrality-analogue of 5.12) |
| P-13e | B: §5.11 dévissage (mapping-cone 2-of-3 for `IsSelfDual` along a module SES) | ⭐⭐⭐ | F | — | — | ☑ 2026-07-04 (Opus/Fable) **CLOSED — `lemma_5_11` PROVED std-3, no sorry** (`GQ2/Devissage.lean`, same FQN `GQ2.FoxH.lemma_5_11`, relocated there since the proof needs the dévissage machinery). One hypothesis added vs the P-12 statement: `hgen : t.Generates` (identifies `ker d⁰` with `fixedPts C` via `H0w_eq_fixedPts`; admissible markings supply it). Full stack in `Devissage.lean`: nine-term LES (primal + dualized SES, arrows + all exactness), ElemDual pack (extension/separation/biduality/dual exactness), six χ-maps with free halves, all ladder squares (lemma_5_6 + eval + δ-cores), four-lemma, nine-window assembly ⇒ `selfdualW_two_of_three` (generation-free, word-internal form) ⇒ `lemma_5_11` via `isSelfDual_iff_W`. **Threaded:** `prop_5_15` (P-13f) and `cor_5_17_card` (incl. the P-13g worktree copy) gained `hgen`; `GQ2.lean` imports `GQ2.Devissage`. P-13f can invoke `lemma_5_11` directly. |
| P-13f | B: §5.15 duality assembly (`prop_5_15`; trivial-module Gram + simple via 5.12/5.13 + dévissage) | ⭐⭐⭐ | O | P-13b, P-13c, P-13d, P-13e | — | ◐ (Opus 2026-07-04) **part (i) `trivialSelfDual` COMPLETE — std-3, no sorry** (`GQ2/{TrivialSelfDual,MixedBilinear}.lean`): `IsSelfDual t A` for any trivial `C`-action on a finite elementary-2 module. Cards + full degree-one pairing: `mixedB` bilinearity, general-offset wild `.z` peel (`heisMarking_{h0,x1sig,c0,wildValue}_z_cocycle`, `conjP_z_of_alzero`), closed form `mixedB_cocycle = y₂(x₂)+y₃(x₀)−y₀(x₃)+u₁.z` with ω₂ scalar confined to (3,3) (`heisMarking_u1_z_of_{x3,y3}_zero`) ⇒ Gram det = 1; descent via `Quotient.lift₂` + `elemDual_separates` nondegeneracy. **Remaining:** parts (ii) nontrivial simple factors (P-13d + 5.13) & (iii) dévissage (P-13e). |
| P-13g | B: §5.16 local lifting duality (`prop_5_16`; local Tate duality — invokes existing axioms B6/B7, no axiom-layer change) | ⭐⭐⭐ | O | — | B6, B7 | ◑ MATH COMPLETE (Opus, 2026-07-04) **ALL 6 CLAUSES PROVED & verified std-3+B6+B7**, own files `GQ2/LocalLiftingDuality.lean` + reusable `GQ2/CupSymmetry.lean` (both `lake build` green 8615/8586, sorry-free). Capstone `prop_5_16_bundle` = full 6-tuple with `prop_5_16`'s exact signature; `#print axioms` = std-3 + `GQ2.tateDuality` (B6) + `GQ2.Foundations.absGalQ2_localEulerCharacteristic` (B7), **NO sorryAx / no native_decide**. Clauses i–iii numeric (as before). iv–vi cups via NEW reusable infra: **cup graded-commutativity** `cup11_comm` (char-2 cochain homotopy) / `cup02_eq_cup20_flip` / `cup20_eq_cup02_flip`; **coefficient transport** `H0congr`/`H1congr`/`H2congr` (+`_mk` rfl bridges) — repo had ZERO cohomology functoriality; `dualAddEquiv : MuDual 2 A ≃+ ElemDual A` shown `G`-equivariant FROM `hpair`; and the **opposite-currying count** `bijective_cup` (B7 finiteness + 𝔽₂-functional separation `exists_addHom_ne_zero`) discharging B6's flagged one-sided-perfectness deviation. **`FoxHeisenberg.prop_5_16` STAYS SORRIED**: splicing `:= prop_5_16_bundle …` is an IMPORT CYCLE (`FoxHeisenberg` ← `LocalLiftingDuality`, needed there for `ElemDual`/`dualEval`); the in-place close needs the statement RELOCATED out of co-owned `FoxHeisenberg.lean` (coordinated move, not a 1-line splice — flagged for owner). Gate: my files clean, census 13; only red = parallel agent's `TrivialSelfDual.lean:179`. |
| P-14 | B: §§6–7 design — 6.13 (D₈ class), 6.15→6.17 (Shapiro/cor), 6.8/6.9 (Gauss sign), 6.16→6.18 (Hilbert ledger), 6.21 (transgression) statements | ⭐⭐⭐ | **F** | P-11 | (statements) | ☑ 2026-07-03 (`GQ2/SectionSix.lean` + `GQ2/SectionSeven.lean` + `GQ2/QuadraticFp2.lean` + `GQ2/Corestriction.lean`, `docs/section67-extraction.md`) |
| P-15 | B: §§6–7 proofs | ⭐⭐⭐ | O | P-14 | B5, B6, B7, B7′, B9, B11 | ◐ (Fable+Opus, 2026-07-03): **§§6–7 essentially complete — only P-15f's 4 sorries remain** (`lemma_6_17_dim/vanish`, `prop_6_18_ramified/unramified`; SectionSix 16/20 theorems proved, SectionSeven sorry-free; sub-tickets P-15a–e, g, h, i all CLOSED std-3).  Original snapshot: (§6: 6.1; 6.13 D₈ + (96); **6.22 shear** via explicit coboundary `w(v,c)=f(v,a c)` — `f_cocycle`×4 + `f_polar` + `m_quad`, char-2 close through `CharTwo.two_eq_zero`; **6.15-square** on-the-nose — `graphPullback(squareOrbitDatum)=cor2Fun(α⌣α)` as raw functions via `congr 1`+`funext`+`finsum_congr`, key index identity `(mk' N g)⁻¹·u = g⁻¹•u` on `G/N`, NO cocycle needed [6.15-free/involution are NOT on-the-nose: the `ghat`-shift makes canonical `.out` reps differ, needs β's Z1 condition].  §7: **all of Lemma 7.1** — head + radical + dual; 7.3; **§7 block existence**; `frattiniLike` infra) **+ Prop 7.4 complete modulo its tame step-2 helper** (`lam_sq_vanish`, sorried; 7.4 verifies std-3+sorryAx through it, no B-axioms) **+ reusable infra `comm_bot_of_scalarChain`** (std-3): coprime odd action on a `Y`-central series is trivial (`⁅Ñ,S⁆=⊥`), the key step for 7.2 — Mathlib lacks coprime-action commutator theory, proved here by central-series induction (bottom layer `c 1 ≤ Z`, displacement hom `Ñ→G` into the central 2-layer, odd-coprime ⟹ trivial image).  Statement amendments: `f_cocycle`; `MinimalBlock.hL/h2L` (7.1-head false without — S₃/A₃ counterexample); **7.4 + framed-target head data** (soundness #3 — step 2 needs `H¹(H_V,V^∨) = 0`, tame-only; step 1 `b_λ(T₀,M)=0` proved abstractly as `lam_comm_vanish`).  **6.16 escalation RESOLVED**: B9 base-generalized + B11 added (census 12, user-approved) — `kummerClassK` layer in `GQ2/EvensKahn.lean`, history in `docs/review-packet.md` §2.  **SPLIT 2026-07-03 into sub-tickets P-15a–P-15i** (rows below; this row = umbrella + amendment history, stays ◐ until all sub-tickets land).  **Sub-ticket mechanics**: heavy work goes in each ticket's OWN new file; `SectionSix/Seven.lean` edits are one-line sorry-splices (`:= by exact GQ2.<OwnFile>.<thm> …`) — claim your row ◐ first; never `git checkout` the co-owned §-files (other tickets' closed lemmas live there); the `SORRY_ALLOWLIST` entry for a §-file is removed by the LAST sub-ticket zeroing its sorries; per-ticket gate = `lake build <own file> GQ2.SectionSix GQ2.SectionSeven` + `scripts/check_axioms.sh` (census 12).  (The earlier SectionEight/AnabelianBridge build-note is resolved — whole-library build was green at the first commit.) |
| P-15a | B: §6 quadratic engine — nonsingular `𝔽₂` zero-count + Lemma 6.6 (Wall, (86)) | ⭐⭐⭐ | O | — | ∅ | ☑ **CLOSED 2026-07-04 (Fable)** — **`lemma_6_6` FULLY PROVED + spliced; `#print axioms lemma_6_6` = exactly std-3 (no B-axioms, no sorryAx).**  **Wall's sign relation `g(q_U)=(−1)ᵏg(q)` proved in `GQ2/GaussCount.lean`** via the paper's Wall-form route made precise: (i) **`wall_count`** — the abstract Wall count `∑_{t,u∈W}(−1)^{ω(t,t)+ω(u,u)+ω(t,u)} = (−2)^k` for a biadditive right-nondegenerate `ω` on a finite elem-ab-2 `W` with a **2-power-order monodromy** `M` (`ω t u = ω u (M t)`) — proved by strong induction on `#W`: a nonzero `M`-fixed `a` (norm-trick `a := b + Mb` induction on the order) has row = column functional; if `ω a a = 1` split `W ≃ ZMod 2 × ker(ω a)` along `a` (factor `−2`); if `ω a a = 0` pick `t₀` with `ω t₀ a = 1`, shift-pairing by `a` kills every block with a `t₀`-coordinate (`sum_sign_shift_eq_zero`/`sum_neg_shift_eq_zero`), the surviving `ker(ω a)²`-block is `⟨a⟩`-blind (factor `4`), and the induction continues on `C = ker ψ` with the **corrected monodromy** `c ↦ Mc + ψ(Mc)·a`.  **The monodromy hypothesis is essential** (`ω=[[1,1],[0,1]]` on `𝔽₂²` gives `−8 ≠ 4`) — the paper's induction sketch is silent on it; flag for P-20 review.  (ii) **duality block**: `card_addHom_zmod2` (`#Hom(A,𝔽₂)=#A`, via `AddCommGroup.zmodModule`+`Module.card_eq_pow_finrank`+`Subspace.dual_finrank_eq`) ⟹ **`perp_ker_iff_mem_range`** (`K^⊥ = im N`, annihilator counting, both applications of the duality). (iii) **`gaussSum_qDouble`**: reindex `g(q_U)g(q) = ∑_{x,u}(−1)^{q(Nx)+q(u)+B(x,u)}`, fiber the `x`-sum over `N` (`Fintype.sum_fiberwise` + explicit `ker`-fiber equivs), kernel character sum `= #K·[u ∈ K^⊥]` (`charSum_eq_zero`), Wall form `ω t u := B(xrep t, u)` (choice-independent via `ker ⟂ im`), diagonal `ω t t = q t`, monodromy `U⁻¹|_R` ⟹ `g(q_U)g(q) = #K·(−2)^k = (−1)^k#V = (−1)^k g(q)²`, cancel `g(q) ≠ 0`.  Engine + 6.6 both consumable by P-15b.  ~~◐ (Fable, 2026-07-03) —~~ **`GQ2/GaussCount.lean` built, all std-3, no axioms/sorries; the ZERO-COUNT ENGINE (what P-15b's `prop_6_9` consumes) is COMPLETE.** Better route than hyperbolic-splitting: the integer **Gauss sum** `g(q)=∑_v(−1)^{q v}` has **`gaussSum_sq : g(q)²=#V`** for nonsingular `q` (char-sum identity `g²=∑_u(−1)^{q u}∑_x(−1)^{B(x,u)}=(−1)^{q 0}#V`; inner sum vanishes off `u=0` by nonsingularity — NO splitting induction needed). Bridges: `gaussSum_eq` (`g=2·zeroCount−#V`), `arf_eq_zero_iff_gaussSum_pos`, `gaussSum_eq_pow` (`g=±2^m` when `#V=2^{2m}`), and the two headline lemmas **`zeroCount_of_arf_zero`** (`=2^{2m−1}+2^{m−1}`) / **`zeroCount_of_arf_one`** (`=2^{2m−1}−2^{m−1}`). **Lemma 6.6: 3 of its 4 pieces PROVED (std-3) + spliced.** `qDouble_eq_add` (`q_U(x)=q x+q((1+U)x)`), `polar_qDouble`/`polar_qDouble_eq` (`B_U(x,y)=B(x,(1+U+U⁻¹)y)`); **`qDouble_nonsingular`** (`ker(1+U+U²)=0` for 2-power `U` via `Function.IsPeriodicPt.gcd`: `U³y=y ∧ U^{2ⁿ}y=y ⟹ U^{gcd(3,2ⁿ)=1}y=y`); **`exists_card_range_eq_two_pow`** (rank `2^k`, `IsPGroup.iff_card`); **`gaussSum_ne_zero`** + **`arf_qDouble_of_gaussSum_sign`** (Arf reduction: `g(q_U)=(−1)^k g(q) ⟹ arf(q_U)=arf q+k`). **`lemma_6_6` SPLICED in `SectionSix.lean`** (imports GaussCount): nonsingularity + rank + Arf-reduction wired; **the ONLY remaining `sorry` is Wall's sign relation `g(q_U)=(−1)^k g(q)`** — Gauss sum of the DEGENERATE form `μ(x)=B(x,Ux)` (radical `ker(U+U⁻¹)`) with a linear twist (radical-split + descended nonsingular Gauss sum, ~300 ln; the hard core, own focused session). `#print axioms lemma_6_6` = std-3 + sorryAx (no new axioms; SectionSix stays allowlisted). Added reusable **`sum_sign_shift_eq_zero`** (twisted-sum vanishing, the level-0 building block of the Wall sign). **ASSESSMENT (2026-07-04):** the remaining Wall sign `g(q_U)=(−1)^k g(q)` needs the DESCEND machinery — twisted Gauss sum of the degenerate `q∘W` reduced through `V⧸radical` to a descended NONSINGULAR form + its `gaussSum_sq`, with two-level radical/`dim(K∩I)` bookkeeping (~300–400 ln quotient-quadratic-form theory absent from Mathlib); a focused (not unattended) session. GaussCount 0 sorries, in `GQ2.lean`; census 12. Defs: `GQ2/QuadraticFp2.lean`, `onePlusU` in `SectionSix.lean` |
| P-15b | B: Gauss signs — Lemma 6.8 (87)/(88) + Prop 6.9 (91) ×2 | ⭐⭐⭐ | O | P-15a | ∅ | ☑ **CLOSED 2026-07-04 (Fable)** — the entire §6.2 Gauss-sign pair PROVED, all std-3 (no B-axioms/sorryAx): **`prop_6_9_unramified`, `lemma_6_8`, `prop_6_9_ramified`** spliced in `SectionSix.lean`. Engine in `GaussSigns.lean` (Arf pinches `arf_eq_{one,zero}_of_dvd`, free-action divisibility `free_zeroCount_dvds`/`card_dvd_card_subtype_of_free`, operator crux `irreducible_operator_pow_ne_one` [cyclic `finrank=natDegree(minpoly)` bridge], `arf_eq_of_free`); ramified core in `GaussSignsRamified.lean` (`irreducible_operator_pow_card_sub_one` [`T^{2^{2m}−1}=1` via AdjoinRoot field] + **`arf_eq_s_ramified`** — the **⟨T⟩ route**, NO Hermitian model/involution/norm-one needed). REUSES **P-13d** (`IsSimpleModTwo`, `orderOf_powOmega2_dvd_two_pow` from `TameSimple.lean`). Key method: both Arf values fall out of the SAME free-action machinery (unramified pinch to 1; ramified dual pinch to parity of s), with tame inertia `⟨T⟩` itself as the free group. **Statement amendments (documented, P-20)**: `lemma_6_8`/`prop_6_9_ramified` gained `hWtsimple`(=`IsSimpleModTwo (zpowers cτ) Wt`), `hV2`/`hWt2` (exp-2), `hs1`, and **`hVU`/`hrank`** [(88a) `#V^U=2^{rs}` and (88b) `rank≡s` as isotypic DATA per extraction note 6 — deriving them needs the S-action/ω₂-cycle structure absent from `he` (covers only ⟨cτ⟩); genuine gap in `docs/p15b-field-core-scoping.md`]. `prop_6_9_unramified` fully SELF-CONTAINED (no data hyps). `GQ2.lean` gains `TameSimple`+`GaussSignsRamified`; SectionSix imports `GaussSignsRamified`+`Prop32`. Feeds P-15f (6.18) + P-16 (§8, not yet wired). |
| P-15c | B: Shapiro ledger — 6.15 free (104) + involution (105) | ⭐⭐⭐ | O | — | ∅ | ☑ **CLOSED 2026-07-04 (Fable)** — both clauses proved std-3, `Ax = ∅`, and **spliced into `SectionSix`** (`lemma_6_15_free` + `lemma_6_15_involution` both sorry-free; `ShapiroLedger.lean` sorry-free; `#print axioms lemma_6_15_involution_aux = [propext, Classical.choice, Quot.sound]`). **Free (104)**: `lemma_6_15_free_aux` (prior Opus session). **Involution (105)**: restructured off the banked monolithic-Λ plan onto the **paper-shaped transversal-change route** — (1) generic brick `cor2FunT_sub_cor2Fun_mem_B2` (corestriction along any transversal `T` differs from `cor2Fun` by `δ¹twistLambda`; needs only the raw char-2 cocycle identity + right-normalization; `cocycle_twist` = 5 cocycle instances + char-2 dup-kill via one `linear_combination … * (2=0)`); (2) the **compatible transversal** `invLift v := ((invIndexEquiv v).out).out` — lifts each `U₀`-coset through **`phi`'s own orbit-canonical base point**, killing the `uCorr` AND orientation layers by construction; alignment discriminant = literally `phi_inv_eq`'s ε-condition (`lWordT_invLift_mem_N_iff`); (3) word identities: aligned words **on the nose** (`W1`), flipped = canonical·ĝ·`shiftCorr` (`W2`), duality `sc(m·ḡ) = (ĝ·sc(m)·ĝ)⁻¹` collapsing all corrections to one read `dRead(m) = α(sc m)`; α-reads R1/R2 (evensAux) + R5/R6 (bS via `ghat_conj_lWord`); (4) **the position identity** `invPositionEval`: per position, `evensNormFun(ℓ^T_v γ, ℓ^T_{γ⁻¹v} η)` = `phi`'s Sum1 (on the nose) + Sum2 (ε·reads at the canonical shifted point via `invIndexEquiv_smul_out`) + the three coboundary terms of the **aligned-locus** `invLambda(σ) = Σ_{v aligned-for-σ} α(ℓ_{z_v}σ)·dRead(σ⁻¹•z_v)` — 2×2 aligned/flipped cells, each with char-2 pair-kills; (5) δ-assembly `graphPullback_sub_cor2FunT_mem_B2` (O-sums→v-sums via `finsum_comp_equiv`, η-sum reindex `sum_reindex_smul'`, `abel_nf` + `-1•x = x`); (6) chain `sub_add_sub_cancel` → `H2ofFun_eq_of_sub_mem_B2`. **Reusable**: the Step-1 brick is generic (any open finite-index `U`, any transversal); `IsLocallyConstant` continuity route for non-normal coset spaces (no `QuotientGroup.discreteTopology`). Gotchas: `set`-fvar folding vs rw (use body-form); `mk'`-vs-`↑`-form discipline (`simp only [mk'_apply]` breaks the O-TYPE — convert value-atoms only, `hcoe : ↑ghat = mk' N ghat` per cell); dependent-⟨v,proof⟩ rewrites via ∀-form helpers. |
| P-15d | B: Lemma 6.4 layer — representative/datum independence of `Q⁰_loc` ⟹ 6.14 (102) | ⭐⭐ | O | — | ∅ | ☑ **CLOSED 2026-07-04 (Opus)** — `GQ2.RepIndependence.lemma_6_14` **proved, `#print axioms = std-3` (no B-axioms, no sorryAx)**; `GQ2/RepIndependence.lean` sorry-free & OFF the allowlist; statement moved out of `SectionSix.lean` (comment-pointer, P-08/P-10 pattern — RepIndependence is downstream of §6's `Q0loc`/`graphPullback`).  Key: **inner-conjugation coboundary on `V⋊C`** (not a raw `linear_combination` — the direct route hit a genuinely multi-term coboundary).  `graphPullback(b) = φ_b^*κ⁰` (`φ_b(g)=(b g,ρ g) : SemiProd C W`); the `Quotient.out`-representative change is `φ_{b+δ⁰w₀} = c_s ∘ φ_b` (conj by `s=(−w₀,1)`); inner autos act trivially on `H²` via `innerConj` (`c_s^*κ⁰ − κ⁰ = δ¹η_s`, `η_s(x)=κ⁰(s,x)+κ⁰(sxs⁻¹,s)`, 3 instances of the cocycle identity `kappa0_cocycle`).  New reusable: `kappa0_cocycle` (κ⁰ ∈ Z²(V⋊C) from the factor-set axioms), `etaS`, `innerConj`.  **2-torsion hypothesis DROPPED** (structural proof works over any `AddCommGroup W`); amended hyps now just `hdatW`, `hiC` (C-module map), `hρW`.  ◐-history: reduction (`hStepA` comap on-the-nose via `hiC`; `mapCoeff1`/`Quotient.out` functoriality; `repIndep` = `H1mk`-equal ⟹ `B1`-extraction ⟹ `h2ofFun_eq_of_sub_mem_B2`) landed first, then the core.  `lake build GQ2.SectionSix GQ2.RepIndependence` green (8608).  Feeds P-15f (6.18). ~~◐ H2ofFun invariant under cohomologous change of the `Z1` representative~~ (6.22-style cochain identity + `H2mk` quotient plumbing, `GQ2/Cohomology.lean`/`GQ2/CtsCohBridge.lean`); note `graphPullback (datW.comap i) ρ b = graphPullback datW ρ (i ∘ b)` holds on the nose — ONLY the `Quotient.out` mismatch needs the 6.4 layer.  Own `GQ2/RepIndependence.lean`; splice `lemma_6_14`.  Also feeds P-15f (6.18 needs the same independence).  **STATUS (Opus, 2026-07-03): reduction DONE + verified, one cochain identity remains.**  `GQ2/RepIndependence.lean` builds green (allowlisted); `lemma_6_14` **proved mod one lemma** (`#print axioms = std-3 + sorryAx`, no B-axioms): on-the-nose `comap` step (`hStepA` via C-equivariance `hiC`), `mapCoeff1`/`Quotient.out` functoriality (`H1mk_out` + `QuotientAddGroup.map_mk'`), `repIndep` (`H1mk`-equal ⟹ `B1`-extraction ⟹ `h2ofFun_eq_of_sub_mem_B2`), and coboundary **continuity** all complete.  **Statement amended** (documented): `lemma_6_14` gains `hdatW : IsEquivariantFactorSet q datW`, `hiC : ∀ c v, i(c•v)=c•(i v)` (i a C-module map, eq. (77)), `hρW` (`G_ℚ₂` acts through ρ on W), `htorsW` (W a 𝔽₂-space — all §6 modules are).  **Sole remaining sorry** = `graphPullback_sub_mem_B2`: the conjugation cochain identity `dOne ψ = graphPullback(b+δ⁰w₀) − graphPullback(b)`, `ψ(g)=f(w₀,b g)+f(b g,ρg•w₀)+m(ρg,w₀)` (the `(w₀,1)`-conjugation phase) — a 6.22-style char-2 `linear_combination` over `f_cocycle`/`f_polar`/`m_quad`/`m_mul`, larger than 6.22 (~12 instances + arg-normalization; goal fully set up, subtractions cleared).  NOT yet spliced into `SectionSix` (splice + amend when the core lands). |
| P-15e | B: Hilbert ledger — Lemma 6.16 (110)–(114), deep-unit Evens norm | ⭐⭐⭐ | O | — | B7′, B9, B11 | ✅ **CLOSED 2026-07-04 (Fable) — `lemma_6_16` NOW SPLICED + PROVED.** `SectionSix.lemma_6_16` `#print axioms` = `{propext, Classical.choice, Quot.sound}` ∪ `{evensKahn_dyadic (B9), dyadicNormCriterion (B11)}` — exactly the declared column, no `sorryAx`; whole-scope build green (8629). Splice: `import GQ2.HilbertLedger` in SectionSix (HilbertLedger is import-independent of SectionSix); extract `b` from `IsDeepUnit`, build norm unit `n=Units.mk0(u²−d·v²)` (`≠0`: `A=β²≠0` + conjugate; `δ∉k` from `hindex=2` via `k.fs≤stab δ`⟹`subgroupOf=⊤`), convert `hunram` to the `x+yδ` form (via the NEW `hδL:δ∈L` hyp), transport `evensNormH2` args by `revert…;rw [hLδ];intro…`, `exact evensNorm_deepUnit_vanish`. **Statement amendment (P-20)**: added `hδL : δ ∈ L` (the P-15f consumer has `δ=√d∈L` concretely). `evensNorm_deepUnit_vanish` (HilbertLedger capstone) unchanged. Unblocks P-15f (6.17_vanish/6.18). (prior INFRA-done history:)  `evensNorm_deepUnit_vanish` (HilbertLedger, the capstone, self-contained over `stabilizer δ`) is proved; the SectionSix `lemma_6_16` (stated over `IsDeepUnit`/`L.fixingSubgroup`) is NOT yet wired to it. Splice route (HilbertLedger is import-independent of SectionSix ⟹ SectionSix can `import GQ2.HilbertLedger`, splice in place): extract `b` from `IsDeepUnit`, construct norm unit `n=u²−d·v²` (`≠0` via `A=β²≠0` + conjugate `u−vδ≠0`; `δ∉k` from `hindex=2`), `hβ':β²=u+vδ`, `hA:u+vδ=1+2b`, convert `hunram` (needs `δ∈L` — likely a statement amendment `hδL`, since the P-15f consumer has `δ=√d∈L` concretely), transport `evensNormH2` args along `hLδ`, `exact evensNorm_deepUnit_vanish`. Unblocks P-15f (6.17_vanish/6.18). ~~✅ **CLOSED (Opus, 2026-07-04)** — `GQ2/HilbertLedger.lean` is **fully sorry-free**; whole library builds green (8613 jobs); census 12; **removed from SORRY_ALLOWLIST**. `evensNorm_deepUnit_vanish` `#print axioms` = `{propext, Classical.choice, Quot.sound}` ∪ `{evensKahn_dyadic (B9), dyadicNormCriterion (B11)}` — exactly the declared axiom column, no `sorryAx`. **F-draft ☑ 2026-07-03**: tier structure + full sub-lemma interface fixed; **proved now, exactly std-3+B11**: `cup_of_normForm` (criterion.mpr), `cup_neg_self`, `cup_steinberg`, `cup_two_neg_one` (`−1 = 1²−2·1²`), `cup_unramified_unit` (B11 clause 2); derived `kummerClassK_inv`/`_mul_self`, `cup_self_eq_neg_one` (std-3+sorryAx via the sorried basics).  **O-finish PROGRESS (Opus, 2026-07-04): 5 of 6 O-items PROVED, all exactly std-3, whole library builds green (8613 jobs), census 12** — `h1_add_self`/`h2_add_self` (quotient induction + pointwise char-2), `kummerClassK_mul` (base-general cocycle mul via two new `ℚ̄₂`-level helpers `kcf_root_indep'` + `kcf_mul_of_fixed` off EvensKahn's `two_values_of_fixed`; `+` transported through `H1mk`/`map_add`+`Subtype.ext`), `kummerClassK_one` (`= [1·1]` + `add_left_cancel`), `trivialCupPairing_comm` (graded-comm in char 2: the two cup cocycles differ by `dOne(g↦−(a g·b g))` — identity holds over ℤ — `∈ B2`, then `eq_zero_iff`+`h2_add_self`), `norm_galois` (Mathlib `NormedAlgebra.norm_eq_spectralNorm ℚ_[2]` + `spectralNorm_eq_of_equiv`, 3 lines), **`sq_of_near_one` DONE** (hand-rolled quadratic Newton `w↦w−(w²−z)/(2w)` from 1, ~90 ln; `NormedField ↥k` restricts `ℚ̄₂`'s by `rfl`, `NormedSpace ℚ_[2] ↥k` infers, `CompleteSpace ↥k := FiniteDimensional.complete ℚ_[2] ↥k`; invariants `‖wₙ−1‖≤‖2‖` [ultrametric ⟹ `‖wₙ‖=1`] + `‖wₙ²−z‖≤‖2‖²·qⁿ⁺¹` [`q=‖z−1‖/‖4‖<1`, error identity `eₙ₊₁=eₙ²/(4wₙ²)` by `field_simp;ring`] ⟹ `cauchySeq_of_le_geometric` ⟹ `cauchySeq_tendsto_of_complete` ⟹ `tendsto_nhds_unique`; `‖2‖<1` via `norm_algebraMap' (𝕜':=↥k)`+`Padic.norm_p_lt_one`; API `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`/`norm_add_le_max`; NB `Padic.hensels_lemma` ℤ_p-only, `ℚ̄₂` NOT complete).  **6th / capstone `evensNorm_deepUnit_vanish` DONE** (~135 ln, `set_option maxHeartbeats 2400000` — large context): step 1 `s'•δ=−δ` (`two_values_of_fixed hδ (fixingSubgroup_smul k s.2 d)` + `hs`/`mem_subgroupOf`+`mem_stabilizer_iff`); step 2 apply `s'` to `hA` (smul distributes via `smul_add`/`smul_mul'`; `s'•2=2` by `AlgEquiv.smul_def,map_ofNat`) ⟹ `(u:ℚ̄₂)=1+b+s'•b` (`linear_combination (hA+hArev)/2`), `(n:ℚ̄₂)=(1+2b)(1+2s'•b)` [diff-of-squares off `hnc`+`hδ`, `hnc` by `rw[hn];push_cast;ring`] ⟹ `‖u‖=1` + `‖n/(2u−1)−1‖=‖4‖‖b‖²<‖4‖` [`norm_galois`; numeral coe `((2:↥k):ℚ̄₂)=2` needs `norm_cast` NOT `push_cast`]; step 3 degree-1 B9 ⟹ `cor=[n]` [`kummerClassK_mul`/`_inv`/`h1_add_self`+`add_left_cancel`]; step-5-prep `[n]=[2u−1]` [`p:=Units.mk0(2u−1)`, `sq_of_near_one` on `n·p⁻¹`, `n=p·wU²` by `Units.ext` — beware `Units.val_mk0` unfolds `↑p` too, rewrite only `↑wU`]; step 4 expand degree-2 (`simp[map_add,AddMonoidHom.add_apply]`) kill `(2,u)+(u,2)`[`trivialCupPairing_comm`+`h2_add_self`], `(u,d)`[comm+`cup_unramified_unit`], `(d,n)`[`cup_of_normForm ⟨u,v,hn⟩`], `(u,u)=(u,−1)`[`cup_self_eq_neg_one`]; step 5 `[2]∪[n]+[u]∪[n]=[u]∪[−1]` via `[n]=[2u−1]=[−1]+[1−2u]` (`kummerClassK_mul`, `nth_rewrite 1` to avoid rewriting the `p` in `−p`) + `cup_steinberg(2u,1−2u)` + `cup_two_neg_one`; final collapse by `abel` (pure reorder) + `h2_add_self`×2 + `add_left_cancel`.  **`lemma_6_16` statement amended** (documented, extraction doc): `[FiniteDimensional ℚ_[2] k]` + Kummer presentation `(d, δ, hδ, hLδ)` + coordinates `(u, v, hAuv)` — consumers (P-15f) have these concretely; the splice transports `evensNormH2`-args along `hLδ` |
| P-15f | B: deep part + §6 headline — 6.17 dim/vanish + Prop 6.18 (115) ×2 | ⭐⭐⭐ | O | P-15a, P-15b, P-15d, P-15e | B6, B7 | ◐ (Fable, 2026-07-04) STARTED — deps P-15a/b/d/e all landed (P-15e ✅ CLOSED, 6.16 spliced ⟹ `lemma_6_17_vanish` unblocked). New file `GQ2/DeepPart.lean` (sorry-free, in GQ2.lean): **`card_H1_eq_card_of_H0_H2_trivial`** (Euler-char collapse: B7's `#H¹=#H⁰·#H²·2^{v₂}` + `#H⁰=#H²=1` ⟹ `#H¹=#V` — the Step-1 brick for BOTH 6.17_dim and 6.18) and `card_H0_eq_one_iff` (`#H⁰=1 ⟺ V^{G_ℚ₂}=0`). **PLAN for `lemma_6_17_dim` (`#X₊²=#H¹`)**: (1) `#H¹=#V` [DONE, Euler collapse]; (2) `#H⁰=#H²=1` for ramified simple V [H⁰=V^{im ρ}=0, H²=(V^∨)^{G}=0 via B6 `perfect20`]; (3) `#X₊=2^m` Lagrangian half-count (X₊ self-⊥ under B6 Tate pairing on H¹, deep-unit orthogonality (94), maximal) — the hard cohomological core. **⚠ STATEMENT GAP (P-20)**: frozen `lemma_6_17_dim`/`prop_6_18_*` lack `hc : Surjective c` — `V^{im ρ}` is C-stable (⟹ simplicity kills it) only when `im ρ ◁ C` (e.g. c surjective); parallels the `lemma_6_8` amendments. REMAINING: 6.17_dim (steps 2–3), `lemma_6_17_vanish` (needs P-15e/6.16), `prop_6_18_*` (assembly of 6.9[P-15b ✓]+6.16[P-15e]+6.17+6.4[P-15d ✓]). Own `GQ2/DeepPart.lean`; splice into SectionSix (P-15d pattern — statements move out). **★ KEYSTONE LANDED 2026-07-04 (Fable), std-3, sorry-free** (`DeepPart.lean` now `import GQ2.GaussCount`): **`arf_zero_of_lagrangian`** + **`gaussSum_eq_card_of_lagrangian`** — the combinatorial crux of step-3 / ramified 6.18: a totally-singular self-⊥ subspace `X` (hyp `hperp : X⊥ ⊆ X`) forces `g(q) = #X > 0`, hence `arf q = 0` (positive Gauss sign).  Proof = two-way eval of `∑_v ∑_{x∈X} (−1)^{q(v+x)}`: translation `v↦v+x` ⟹ `#X·g(q)`; polar-expand `q(v+x)=q v+B(v,x)` (`q|X=0`) + `sign_add` + `charSum_eq_zero` (inner char-sum `= #X·[v∈X⊥]`) ⟹ `#X·#X`; cancel.  `#print axioms` = std-3 (no B-axioms, no sorryAx).  **This reduces `prop_6_18_ramified` to**: [Q0loc `IsQuadraticFp2`+`Nonsingular` on H¹ (Tate B6)] + [`#H¹ = 2^{2m}` (Euler collapse + `#H⁰=#H²=1`)] + [`lemma_6_17_dim` `#X₊²=#H¹`] + [`lemma_6_17_vanish` `Q0loc|X₊=0`] → **`arf_zero_of_card_sq`** (the complete algebraic Lagrangian package) → `GaussCount.zeroCount_of_arf_zero`.  **★ `selfperp_of_card_sq` ✅ DONE 2026-07-04 (Fable), std-3** — `#X²=#V` + tot-sing + nonsing ⟹ self-⊥, via the injection `X⊥ ↪ (V/X)^∨` (descended polar functional `QuotientAddGroup.lift`, injective by nonsingularity) ⟹ `#X⊥ ≤ #(V/X)=#V/#X=#X`, sandwiched with `X⊆X⊥` (NO character-extension needed — cleaner than the `LinearMap.exists_extend` route). So the ENTIRE algebraic side of ramified 6.18 is now banked as **`arf_zero_of_card_sq`** (`#X²=#V` ⟹ `arf q=0`, folding in selfperp).  **Remaining for P-15f = purely cohomological**: (i) `Q0loc` is `IsQuadraticFp2`+`Nonsingular` on `H¹` (polar = perfect Tate cup pairing, B6); (ii) `#H⁰=#H²=1` (needs the `hc : Surjective c` statement amendment — analogous to `lemma_6_8` — + B6 `perfect20`); (iii) `lemma_6_17_dim` (`#X₊²=#H¹`, Tate self-duality of the deep half) + `lemma_6_17_vanish` (`Q0loc|X₊=0`, deep-unit orbits + 6.16); (iv) unramified 6.18 = Hermitian-line model (6.4/6.7). ~~☐ `lemma_6_17_dim` (B7 dimension count `#X₊² = #H¹`) is INDEPENDENT — can start any time; `lemma_6_17_vanish` consumes e; `prop_6_18_*` = assembly of 6.9 (b) + 6.16 (e) + 6.17 + the 6.4 layer (d).  Own `GQ2/DeepPart.lean`~~ |
| P-15g | B: §7 Lemma 7.2 — tame-free route + block-module infra | ⭐⭐⭐ | O | — | ∅ | ☑ **CLOSED 2026-07-04 (Opus)** — `lemma_7_2` **proved, `#print axioms GQ2.SectionSeven.lemma_7_2 = [propext, Classical.choice, Quot.sound]` (std-3, no B-axioms, no sorryAx)**; gate green (census 12); tame hyps `π,hπ,hkerπ,cH,hcH` **unused** (tame-free route confirmed). `SectionSeven` stays allowlisted only for `lam_sq_vanish` (P-15h). Prototyped in scratch `GQ2/WF72.lean` then spliced (`set_option maxHeartbeats 1000000 in`); scratch deleted. **Assembly** (~230 ln): `Ñ:=zpowers y` (odd via `exists_odd_moving_general`), `⁅Ñ,S⁆=⊥` (`comm_bot_of_scalarChain` + `B.scalar_below`, coprime `orderOf y` ⊥ `#S` 2-pow via `IsPGroup.iff_card`/`Nat.coprime_two_right`), `⁅Ñ,R⁆=⊥` (`R≤S`), `D=K⊓C_Y(R)` `Y`-normal, three-subgroup `commutator_commutator_eq_bot_of_rotate`, `K₁=normalClosure⁅K,Ñ⁆`, chief dichotomy (`=S`⟹`[y,ks]∈S` contra existence; `=P`⟹`B.minimal K₁=K`⟹(a) `K≤C_Y(R)`); class-2 (b)(c): `[k,l]²=1` (central-comm expand), `(kl)⁴=k⁴l⁴` (via `[l,k]k²l²` + pairwise-central rearrange), `Kf={k∈K\|k⁴=1}` `Y`-normal ⊇`⁅K,Ñ⁆` (`f[k,n]=k⁴·n(k⁴)⁻¹n⁻¹=1`, Ñ fixes `R∋k⁴`) ⟹`K≤Kf`⟹(c); (b) `r²=1` by `closure_induction` (`R` abelian). **Lean gotcha banked: `group` does NOT expand `x^(4:ℕ)` — insert `hp4 : x^4 = x*x*x*x` (`pow_succ×3+pow_one`) before every `^4`-vs-product `group`.** INFRA (banked std-3, wired in): new `GQ2/BlockModule.lean` (sorry-free, in `GQ2.lean` before SectionSix; block-agnostic so no cycle) exports — `comm_bot_of_scalarChain` (relocated public, was private in SectionSeven; that copy REMOVED, `import GQ2.BlockModule` added there, SectionSeven still green), `conjHom`/`conjHom_compat`, `blockAction` (the `Y`-conj MulAction on `↥P⧸S.subgroupOf P`, `@[reducible]`), `blockPerm : Y →* Perm (P/S)` + `@[simp] blockPerm_apply_mk` (**built as a DIRECT perm rep from `QuotientGroup.map`, NOT `MulAction.toPermHom` — the latter's `•` diamonds hopelessly against `blockAction.smul`; `map_mk'` is `rfl`, reduce via defeq `show`, never `rw`/`simp`**), and **`exists_odd_moving_general`** (std-3: odd-order `y` with `∃p∈P,[y,p]∉S`, via `¬goal ⟹ φ.range=blockPerm.range` is `IsPGroup 2` [odd part `y^ordProj[2]` acts trivially] ⟹ `IsPGroup.card_modEq_card_fixedPoints` on `φ.range` ⟹ `|V|` even ⟹ nonzero fixed coset ⟹ the fixed subgroup `W={p∈P|∀y [y,p]∈S}` is `Y`-normal `S<W≤P` ⟹ `B.chief` ⟹ `W=P` ⟹ contradicts `nontrivial_action`).  Key API: `Nat.ordProj_dvd`, `Nat.not_dvd_ordCompl`, `orderOf_pow'`, `orderOf_dvd_natCard q` (arg!), `MulAction.compHom Q φ.range.subtype`, `Finite.one_lt_card_iff_nontrivial`.  **REMAINING = the `lemma_7_2` assembly in SectionSeven** (route below, all tools ready): `Ñ := Subgroup.zpowers y` (odd, coprime to `#S` 2-power); `⁅Ñ,S⁆=⊥` via `comm_bot_of_scalarChain` fed `B.scalar_below`'s chain ⟹ `⁅Ñ,R⁆=⊥` (`R≤S` by `lemma_7_1_head`); `D := K ⊓ centralizer R` proved `Y`-normal inline; three-subgroup `Subgroup.commutator_commutator_eq_bot_of_rotate` (H₁=K,H₂=Ñ,H₃=R: h1 `⁅⁅Ñ,R⁆,K⁆=⊥` from `⁅Ñ,R⁆=⊥`; h2 `⁅⁅R,K⁆,Ñ⁆⊆⁅R,Ñ⁆=⊥` since `⁅R,K⁆≤R`) ⟹ `⁅K,Ñ⁆≤D`; `K₁:=normalClosure ⁅K,Ñ⁆≤D`, and `K₁⊔S` is `Y`-normal in `[S,P]` so `B.chief` ⟹ `=S`(⟹`⁅K,Ñ⁆≤S`⟹ via `mul_normal` factor `p=k·s` and `[y,ks]=⁅y,k⁆·k⁅y,s⁆k⁻¹∈S` ⟹ contra existence) or `=P` ⟹ `B.minimal K₁ = K` ⟹ `K≤centralizer R` = conclusion (a); then class-2: `k²∈R≤Z(K)` ⟹ `[k,l]²=[k²,l]=1`, the 4th-power `Y`-equiv hom `f k=k⁴` kills `⁅K,Ñ⁆` (`f[k,n]=f(k)·(n·f(k⁻¹)·n⁻¹)=1`, Ñ fixes R∋f(k)), normalClosure=K minimality ⟹ `f=1` ⟹ `K⁴=1`=(c), `R` elem ⟹ (b). |
| P-15h | B: §7 `lam_sq_vanish` ⟹ Prop 7.4 fully std-3 | ⭐⭐⭐ | O | P-15g | ∅ | ☑ **CLOSED 2026-07-04 (Opus)** — `#print axioms GQ2.SectionSeven.prop_7_4 = [propext, Classical.choice, Quot.sound]` (**std-3, NO sorryAx, no B-axioms**); SectionSeven compiles clean & is **SORRY-FREE**. The entire §7 Prop 7.4 is proved. Three tiers: (1) **module core** — `avg_dual_zero` (F1 odd averaging, no Maschke), `dual_vanish_concrete` (F1 bridge `V^Ctil=0 ⟹ (V∨)^Ctil=0`), `fixed_zero_of_moves` (A simplicity via `fixSub`+`chief`); (2) **P1** `L` acts trivially on `V=P/S` — `L_le_blockPerm_ker` (`exists_L_fixed_coset` p-group count + chief upgrade); (3) **tame construction** (`by_cases` on tame inertia `⟨cH τ⟩` moving `V`): tame structure via `import GQ2.Prop32` (`SectionThree.gen_ttame_quotient` closure=⊤, `tame_relation` `s⁻¹ts=t²`, `Tame.zpowers_normal_of_tame`+`Tame.tame_odd_order`); **ramified** `Ctil=π⁻¹⟨cH τ⟩` odd via `odd_preimage_quot` (`π⁻¹⟨t⟩/(YV∩·)` quotient of `π⁻¹⟨t⟩/ker π≅⟨t⟩` odd); **unramified** `Ctil=⊤`, `Y/Y_V` odd via `unram_odd` [`cyc_YV` IsCyclic(Y/Y_V) from `cyclic_quot`(H/mapπYV, `cH τ` dies)+iso transport; then by_contra 2∣card, Cauchy order-2 `gbar`, `blockPerm(C̃)` 2-group, `exists_normal_fixed_coset` image-count ⟹ `fixSub⊋S` ⟹ chief ⟹ `C̃≤Y_V` ⟹ `gbar=1` contra] + `top_quot_card` (⊤-quotient card). **New std-3 infra banked in SectionSeven**: avg_dual_zero, dual_vanish_concrete, fixSub/fixed_zero_of_moves, exists_L_fixed_coset, L_le_blockPerm_ker, cyclic_quot, exists_normal_fixed_coset, odd_preimage_quot, unram_odd, cyc_YV, top_quot_card. **Gotchas banked**: `ḡ`(combining macron) invalid Lean id→`gbar`; `IsCyclic.commGroup` mul NOT defeq canonical→derive comm from generator; `exists_prime_orderOf_dvd_card` wants `Fintype.card`; `Subgroup.normal_top`; `QuotientGroup.map_mk`(↑x,rfl) not `map_mk'`; act-based avg (not DistribMulAction, AddAut friction); `ofMul_mul`/`toMul_ofMul` root-ns. SectionSeven now sorry-free (can be dropped from SORRY_ALLOWLIST; left for parallel-run safety). |
| P-15i | B: Lemma 6.21 — transgression splitting (116-consequence) | ⭐⭐⭐ | **F**+Opus | — | ∅ | ☑ **DONE (Fable design + close, 2026-07-04)** — the isolated gap was a *statement-extraction* gap: the paper's “fixed equivariant class κ⁰_q” hypothesis had been dropped in the consequence-form extraction (see `docs/p15i-transgression-gap.md`).  **Amended (reviewed, user-approved)**: `lemma_6_21` gains `(dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)` (Lemma 6.1 vocabulary, same form `lemma_6_22` consumes); `splitting_of_global_cocycle` gains the raw cochain avatar `(t, ht_quad, ht_mul)`.  New std-3 lemmas: `symm_cocycle_is_coboundary` (symmetric zero-diagonal 2-cocycle on elem-ab V is δθ; twisted product 𝔽₂×_S V is an exponent-2 abelian group ⟹ 𝔽₂-linear section — reusable), `mixedA_defect` (D_c formula, 3 cocycle instances), `equivariant_lift_of_factorSet` (m-family transported along θ), and the closed assembly: `Ã c := mixedA c + t c⁻¹` is additive with δÃ = δ(mixedA) = B♭f ⟹ `bflat_bijective` yields the primitive g.  **`lemma_6_21` PROVED & SPLICED, std-3, no B-axioms; `GQ2/Transgression.lean` sorry-free, off SORRY_ALLOWLIST.** |
| P-16 | B: §8 — half-torsor count 8.6 + closed recursion Prop 8.9 (eqs. (136)–(142)) | ⭐⭐⭐ | **F** draft, O finish | P-11, P-14 | B6, B7, B9 | ◐ **F-draft ☑ + Lemma 8.2 fully proved 2026-07-03** (`GQ2/SectionEight.lean` + `docs/section8-extraction.md`; **proved, all std-3**: engines 8.4/8.5, scalar twisting, `lemma_8_2_gammaA` (kills-`N_A` ⟺ kills-`τ` via P-04 + the exponent-2 `ω₂`-ledger collapse `wildRel_of_comm2`), **`lemma_8_2_local`** (amended: `BoundaryMaps` + compactness hypotheses; `pro2F`-transport via `ker_pro2F`/T-05/`continuousMulEquivOfBijective` onto `card_char_piBd : \|Hom(Π,𝔽₂)\| = 8`), plus generalized `charEquiv`/`cmhEquivFun` infra; `𝔽₂`-topology binders removed file-wide — `ZMod.instTopologicalSpace/instDiscreteTopology` are global (two-instance conflict otherwise); plus **`lemma_8_3` FULLY PROVED** (the eight-lift partition (124), std-3): the torsor core (`fiberLiftEquiv` + `scalarTwist_left_injective`/`liftDiff`/`scalarTwist_liftDiff`: lifts through a central cover form a `Hom(Γ,𝔽₂)`-torsor) assembled via **two fibrations of `masterLifts`** — projection (`projB`→`8·u^β`) and image (`imageMap`→RHS) — with the corestriction layer `cmhCodRestrict`/`cmhInclude`/`cmhSubgroupEquiv`, `pCont`, `stratum_surj`, `Equiv.sigmaFiberEquiv`+`Nat.card_sigma`, and `finsum_mem_coe_finset`+`Finset.sum_subtype` for the sum-shape match; `hfg` t.f.g. amendment applied (finitizes via `finite_boundaryLifts`); **3 sorries left**: 8.6×2 (candidate side consumes P-13's 5.15/5.16, in flight), `prop_8_9` — O-half log + remaining order in the design note.  **PROGRESS (Opus, 2026-07-04, dep-analysis for parallel run)**: only `lemma_8_6_local` is un-gated (B6, no P-13); `lemma_8_6_gammaA` needs 5.15/5.16 (P-13), and `prop_8_9`'s `eq139`+`eq140` need both the gammaA-side 8.6 and the 5.15/5.16 `μ`-pinning ⟹ P-13-gated.  **Landed `two_mul_card_fiber`** (std-3, before `section HalfTorsor`): the (127) half-count CORE — a nonzero `𝔽₂`-functional on a finite `𝔽₂`-space has each fibre exactly half; reused by both 8.6 lemmas AND `prop_8_9`'s (139).  `lemma_8_6_local`'s deep remainder (MLifts≅Z¹(Γ,M) torsor → obstruction `o:MLifts→H²(Γ,𝔽₂)≅𝔽₂` wired to `ContCoh` → (127) `ℓ` from the cover's quadratic form → `ℓ≠0 ⟺ NoDescent` via **B6 perfect pairing** → `two_mul_card_fiber`) is a ~500-ln cohomological build needing new group-extension-obstruction infra not yet in repo; decomposition in `section8-extraction.md` O-half work order §3) |
| P-17 | B: §9 — induction on `\|L_Y\|`: regime 9.1 (Lemma 9.2 ✓), 9.2 (counts + strict decrease (145)/Lemma 9.4), 9.3 (Frattini/Fourier, central formula (151)) ⇒ **Thm 4.2 proof** | ⭐⭐⭐ | **F** design, O finish | P-11–P-16 | B6, B7, B7′, B8, B9 | ☐ |
| P-18 | B: Lemma 10.1 (tame-frame exhaustion) + eq. (154) ⇒ `main_surjection_count` | ⭐⭐ | O | P-09, P-10, P-17 | (all of Track B) | ☐ |
| P-19 | Assembly: `main_presentation_literal` via `main_presentation` | ⭐ | O | P-02, P-03, P-05, P-18 | B1 + Track B | ☐ |
| P-20 | Meta: review packet v3 — interior-node statements + App. D certificate diff + **the citation-faithfulness classification table (from P-22, now in `docs/review-packet.md` §2)**, at statement freeze | ⭐ | O | P-06, P-11, P-12, P-14, P-22 | — | ☐ |
| P-21 | Foundations: ℤ₂-powering on pro-2 groups — `maxPro2(ℤ̂) ≅ ℤ₂` (the `ι`-seam), `zpowZtwo` + unit/odd-power bijectivity, `IsProP 2 ℤ₂ˣ` + `η`-injectivity, pro-2 Frattini criterion | ⭐⭐⭐ | **F** | — | ∅ | ☑ 2026-07-03 (`GQ2/ZtwoPowering.lean` (i)–(iii) + `GQ2/FrattiniCriterion.lean` (iv); all std-3, zero sorries). **Unblocks P-07 η-leg, all three P-08 legs' infra, `prop_3_10` `ι`-seam** |
| P-22 | Meta: axiom documentation pass — adversarial axioms review recs 1/3/4/6 (`docs/adversarial-axioms-review.md`): B8 citation → "Stix **plus** cyclotomic surjectivity" (statement KEPT — user decision 2026-07-04), B2 → "available/unused" label, B3c → composite-interface reclassification, 4-way classification table | ⭐ | O | — | — (doc-only; census 12 unchanged) | ☐ |
| P-23 | Foundations: B11 split into named leaves — adversarial review rec 2 (**census change APPROVED**, user 2026-07-04): `hilbertSymbol_normCriterion_finiteDyadic` + `unramifiedQuadratic_units_are_norms` + isolated spectral-norm bridge; old `dyadicNormCriterion` re-derived as a SAME-NAME theorem (zero consumer churn) | ⭐⭐ | O | **P-15e capstone landed** | (census 12→13) | ✅ **CLOSED 2026-07-04 (Fable)** — B11 split landed, census **12→13**, affected scope green.  `axiom dyadicNormCriterion` → two classical leaf axioms `hilbertSymbol_normCriterion_finiteDyadic` (B11a) + `unramifiedQuadratic_units_are_norms` (B11b) in `GQ2/Foundations/Axioms.lean`; the spectral-norm "unramified" proxy isolated as **`def IsUnramifiedQuadraticSpectral`** (a named project convention, **not** an axiom — the review's "riskiest piece": bridge route (c), neither provable-in-repo nor axiomatized, just named + flagged, so it adds zero proof-theoretic strength).  `dyadicNormCriterion` re-derived as a **same-name theorem** `⟨B11a k htriv, fun a δa hδa hunram u hu => B11b k a δa hδa hunram u hu⟩`, statement byte-for-byte unchanged ⟹ **zero consumer churn** (`HilbertLedger`'s `.1`/`.2` projections untouched).  Verified: `lake build GQ2.HilbertLedger GQ2.SectionSix` green (8629); `check_axioms.sh` census **13 (= expected)**, placement OK, no `native_decide`; `#print axioms` — `dyadicNormCriterion` = std-3 + {B11a, B11b} (no `sorryAx`), and both consumers `evensNorm_deepUnit_vanish` = `SectionSix.lemma_6_16` = std-3 + {B9, B11a, B11b} (the declared B9+B11 column, with B11 now expanding to its two leaves).  Updated same commit: `EXPECTED_AXIOMS 12→13` (`scripts/check_axioms.sh`) + `AxiomLedger.bAxioms` (B11a/B11b tags, `dyadicNormCriterion` now a tracked consumer) + Axioms.lean docstrings/B-index/tier + rules line + `review-packet.md` §2 (table split, tier, amendment log).  **(iv) DEFERRED → P-20**: exact Serre display numbers (LF XIV §2 / V §2) stay "pending PDF verification" — the split preserves the pre-split axiom's citations verbatim, so this is citation-audit work independent of the split.  **Unrelated pre-existing guard red** (not P-23): `GQ2/TrivialSelfDual.lean:157` sorry — a paused agent's WIP scratch, not imported by `GQ2.lean`, red before this change. |
| P-24 | Meta: guard hardening — untracked-file WARN (tracked FAIL unchanged) + scratch convention in `step2-plan.md` — adversarial review rec 5 (the `WF72.lean` incident, since self-resolved; that P-15g prototype is now spliced into `SectionSeven` and the scratch DELETED 2026-07-04 — no live scratch remains) | ⭐ | O | — | — | ☐ |
| P-25 | B: §3 boundary construction — Prop 3.10 (`Γ_A` half + local/Cor 3.12 half) + Prop 3.14 `Nonempty BoundaryMaps` (the orphaned `SectionThreeMarked.lean` sorries; see census) | ⭐⭐⭐ | O | P-09, P-10, P-21 | B5, B8, B3c, B10 (inherited via 1.1 / 3.2) | ◐ (Opus 2026-07-04) STARTED — claimed the 3 unowned §3 sorries (`prop_3_10_gammaA`, `prop_3_10_local_marked`, `prop_3_14`).  Heavy work in own file `GQ2/BoundaryConstruction.lean`; splice/relocate into `SectionThreeMarked.lean` (P-15d pattern). |

## Proof-state census — the 14 remaining `sorry`s (audit 2026-07-04)

Authoritative snapshot of every bare `sorry` in the compiled tree (`lake build GQ2` green, 8649 jobs;
`check_axioms.sh` all-pass, census 13, no `native_decide`).  Each is an honest open obligation — no
*proved* theorem depends on `sorryAx` except by explicitly taking the sorried result as a hypothesis
(notably `(B : BoundaryMaps)`, discharged only by `prop_3_14` below).

**Apex — final assembly:**
- `GQ2.main_surjection_count` (`Statement.lean:49`) — Theorem 1.2, surjection-count form → **P-18** ☐
- `GQ2.main_presentation_literal` (`GammaA.lean:286`) — literal `Γ_A ≅ G_ℚ₂` → **P-19** ☐

**§4 keystone:**
- `thm_4_2` (`BoundaryFrame.lean:465`) — Theorem 4.2 → **P-17** ☐ (via the §9 induction)

**Active (agents in flight):**
- `prop_5_15` (`FoxHeisenberg.lean:2971`) → **P-13f** ◐ — part (i) `trivialSelfDual` done; parts (ii) simple
  factors + (iii) dévissage remain (`lemma_5_11` now available to it).
- `lemma_6_17_dim` / `lemma_6_17_vanish` / `prop_6_18_ramified` / `prop_6_18_unramified`
  (`SectionSix.lean:862/883/907/929`) → **P-15f** ◐.
- `lemma_8_6_gammaA` / `lemma_8_6_local` / `prop_8_9` (`SectionEight.lean:1390/1399/1592`) → **P-16a–d** ◐.

**§3 boundary construction — now tracked as ⟶ P-25 ◐** (was UNOWNED; fell through P-09/P-10 closure):
- `prop_3_10_gammaA` (`SectionThreeMarked.lean:47`) — Prop 3.10 `Γ_A` half — design-note-assigned to
  **P-09** (☑ CLOSED, which delivered only Prop 3.2 + the ν-surjectivities).
- `prop_3_10_local_marked` (`SectionThreeMarked.lean:63`) — Prop 3.10 / Cor 3.12 local half — assigned
  **P-10** (☑ CLOSED, which delivered only Prop 1.1).
- `prop_3_14 : Nonempty BoundaryMaps` (`SectionThreeMarked.lean:83`) — assigned **P-09/P-10 jointly**;
  **LOAD-BEARING** — it is the only thing that discharges the `(B : BoundaryMaps)` hypothesis threaded
  through all of §§4–8.  **Now tracked as P-25** (created 2026-07-04, ◐ Opus).  The `SORRY_ALLOWLIST` comment in `scripts/check_axioms.sh`
  ("SectionThreeMarked … removed by P-08/P-09/P-10") over-claims — only the two ν-surjectivities were
  removed; this stale note should be corrected under P-24 (guard hardening).

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
  `SectionThree.lean` (which is now **sorry-free** — P-07 closed the last one and removed the
  `SectionThree.lean` allowlist entry 2026-07-03).
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
  review before Wave-3 proofs begin.  Also carries **P-22's citation-faithfulness classification
  table** (`docs/review-packet.md` §2, four tiers: direct / classical+encoding / composite /
  unused) into the packet, so the human reviewer sees which leaves are composite interfaces
  (B3c, B8, B11) before checking them.
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
- **P-22** (opened from `docs/adversarial-axioms-review.md` recs 1/3/4/6; user decisions
  2026-07-04 — B8: keep the statement, fix the citation; B2: keep, relabel): **docstring/docs
  edits only — no axiom statement may change** (gate: `git diff GQ2/Foundations/Axioms.lean`
  touches comment lines only; census stays 12).  Deliverables: (i) `peripheralCyclotomicAction`
  (B8) docstring reframed as **composite** — Stix (decomposition group acts on cusp inertia
  through the cyclotomic character) **plus** a cyclotomic-surjectivity input (the
  `aut : ℤ_[2]ˣ → …`-for-every-unit form is the strengthening); name the available feeders
  explicitly (B2 globally; the B5-derived local surjectivity via `χ_cyc(rec u) = u⁻¹`, cf.
  P-07's `units_gen`/`markedHom_bijective` machinery) and record that the weakened
  cyclotomic-image form was considered and declined (downstream churn) — review §1 + fixes §1.
  (ii) `cyclotomicCharacter_two_surjective` (B2) docstring gains the honest label — **available
  but currently unused** (grep 2026-07-04: zero consumers; retained as B8's citation companion /
  future B8-elimination route) — review §4.  (iii) `dyadicOrientation` (B3c) reclassified as a
  **composite interface**: Labute orientation values + (Demushkin dualizing character = local
  cyclotomic character) + choice of a normalized B4 iso; note it **subsumes a marked B4**
  (downstream Ax lists citing B3c need not add B4) — review §3.  (iv) The 4-way
  **classification table** (direct: B1, B6, B7, B7′, B10 · classical + encoding choices: B4,
  B5, B9 · composite/project interface: B3c, B8, B11 · available-unused: B2) added to
  `docs/review-packet.md` (new section) and cross-referenced from `Axioms.lean`'s header;
  amend **P-20**'s row so packet v3 carries the table — review §6.  (v)
  `GQ2/AxiomLedger.lean` comment tags + `docs/literature-axioms*.md` updated where they echo
  the old citation stories.  Closed rows' history (e.g. P-08's "B2 turned out unneeded") stays
  untouched.  Gate: `lake build GQ2` green, guard green (census 12).
- **P-23** ✅ **DONE 2026-07-04 (Fable) — see the P-23 row above for the close record; outcome: bridge isolated as a `def IsUnramifiedQuadraticSpectral` (census 12→13), not axiomatized; (iv) citation-number verification deferred to P-20.** (review rec 2; **census change pre-approved** by user 2026-07-04 — the split route,
  not the bridge-doc route): **hard-sequenced — start only when P-15e's Tier-4 capstone
  (`evensNorm_deepUnit_vanish`) is committed and its row shows it landed** (its owner actively
  consumes B11 in uncommitted `HilbertLedger.lean`).  Deliverables: (i) replace
  `axiom dyadicNormCriterion` with named leaves `hilbertSymbol_normCriterion_finiteDyadic`
  (`[a] ∪ [b] = 0 ↔ ∃ x y, b = x² − a·y²` over each finite dyadic base — Serre's norm
  criterion) and `unramifiedQuadratic_units_are_norms` (unramified quadratic ⟹ every base unit
  is a norm); the repo's **spectral-norm proxy** ("unramified = equal spectral-norm value
  groups") is the risky translation layer — first TRY proving the bridge in-repo; if not
  provable, isolate it as a third leaf explicitly flagged *project convention, not a cited
  theorem* (review fixes §2).  (ii) Re-derive the **exact current `dyadicNormCriterion`
  statement as a theorem with the same name**, so `HilbertLedger.lean` and all consumers need
  **zero edits**; re-verify their `#print axioms` = std-3 + exactly the new leaves.  (iii)
  Census 12→13 (bridge proved) or 14 (bridge axiomatic): update the rules line above +
  `EXPECTED_AXIOMS` in `scripts/check_axioms.sh` (precise-staged, hot file) +
  `AxiomLedger.lean` tags + `docs/review-packet.md` §2 history + P-22's classification table,
  same commit (B10/B11-precedent wording).  (iv) Resolve the docstring's "citation display
  numbers pending PDF verification" against the Serre PDF in `references/`.  Gate:
  whole-library build green; guard green at the new census; P-15e's landed theorems re-verified
  unchanged.
- **P-24** (review rec 5): the review-time failure (`GQ2/WF72.lean:239` sorry) **self-resolved**
  (2026-07-04: the sorry is gone and the guard is green) — `WF72.lean` is P-15g's live
  prototype and **must not be touched**; this ticket removes the failure *mode*, not the file.
  Deliverables: (i) `scripts/check_axioms.sh` (precise-staged, hot): the per-file scan
  distinguishes **tracked** files (current behavior — FAIL) from **untracked** ones (`git
  ls-files` membership): untracked violations print a clearly-labeled **WARN** block and do not
  fail the gate (rationale: the gate certifies the committed library; a parallel session's
  mid-flight scratch must not block everyone's commits — review fixes §5).  (ii) Scratch
  convention documented in `step2-plan.md`'s conventions: prototypes importing repo modules go
  in the session scratchpad or a root `scratch/` (gitignored), not `GQ2/`; if under `GQ2/`
  anyway, expect WARN noise.  (iii) Self-test: a planted untracked sorry file WARNs without
  failing; a tracked violation still FAILs (test, then delete the plant).  Gate: guard green on
  the current tree; the script diff reviewed against parallel allowlist edits (reconstruct from
  HEAD).
