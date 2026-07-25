# Roe-candidate verification ticket board

Plan: `docs/orchestration/roe-verification-plan.md`. Branch `roe`, worktree
`~/claude/gq2-roe` (recon/spike tickets run read-only against the main checkout).
Model column = subagent tier (fable = design/hard seams, opus = well-specified fills).
One ticket = one agent dispatch.

**Board protocol (lessons-learned): workers NEVER edit this file.** Each worker commits its
own files on green (`roe Rn: <summary>`) and ends with a report (files, commit hash,
sorry/axiom state, deviations, discoveries affecting later tickets); the orchestrator alone
updates rows here and merges `roe` → `master` at wave boundaries.

## Campaign decisions (orchestrator log)

- 2026-07-24 (owner, pre-sleep): work lives inside `gq2-lean` (single docs tree for the
  website). Placement decided by orchestrator: **`GQ2/Roe/` inside the `GQ2` library**
  (namespace `GQ2.Roe`, `Marking`-dot-notation defs where natural; one `import GQ2.Roe.X`
  line per lane in `GQ2.lean`) — same-library gives verbatim imports and atlas coverage.
- 2026-07-24 (owner, pre-sleep): **G1 route decision delegated to the orchestrator** once
  the R2 spike reports. Safeguard retained: on Route L, all math proceeds
  hypothesis-parametrized; the actual axiom-insertion commit (R14 census flip) still waits
  for owner sign-off in the morning. Owner also flagged 79% weekly fable usage — prefer
  opus where the plan allows; expect possible interruption (commit early, board always
  current).

## Wave 1 (parallel: R1→R3→R4→R5 lane; R6 lane; R2 lane; R20 lane)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| R1 | Roe words + WildRelR + admissibleCountR + wildValueExpR (+stress) | fable | `GQ2/Roe/Words.lean` | — | **done 2026-07-24** (278053c, 261 ln, 0 sorries, std-3 axioms; full build 3309 green). API: `Marking.aR/y1R/cR/wildValueR/WildRelR/AdmissibleR`, `GQ2.admissibleCountR`, `wildValueExpR(+_of_dvd, TWO ω₂-subwords — σ₂ also ω₂; ticket sketch corrected per tex), map naturality, zmod8 stress incl. genuine-ω₂ `wildValueR_zmod8`. Exponent preview for R23: (0,e,e+1,0) |
| R2 | Nielsen search spike: ν-constrained D_R ⇄ D₀ words (off-Lean, q2 archive tooling; timeboxed) | fable | report `roe-r2-spike.md` (no Lean) | — | **done 2026-07-24** (fe4469d) → **ROUTE N NOT VIABLE — impossibility THEOREM** (any word-epi is auto-iso by 5-term exact seq; isos intertwine canonical orientations; norm kill in ℚ(X), disc −59: η has N = −1/27, word-values land in ±4^ℤ). Method validated on d0PiEquiv; §3.2 computation independently re-derived (X≡5, S≡13 mod 16; b≡91367, u≡898793 mod 2^20); Hom-counts agree on all 2668 2-groups ≤128. Extras banked: R13 p=2 cup–Bockstein pitfall, R15 Gram-isometry seed, R5 Hom-count trick |
| R3 | GammaR marked quotient + AdmissibleLimit clone (+`wildRelatorR` profinite word + finite↔profinite bridge; `map_admissibleR` via Subdirect:104 clone) | opus | `GQ2/Roe/GammaR.lean`, `GQ2/Roe/AdmissibleLimit.lean` | R1 | **done 2026-07-24** (486c888, 247+319 ln, 0 sorries, std-3 on all 9 terminals; build 3312). Bridge factored via evaluation lemma `map_wildRelatorR`; shared helpers reused not recloned. R4 chain mapped: clone `admissible_of_NA_le_ker`; FLAG: `markC_admissible` is NOT a prop_2_3 input (it's the §5 supply seam) — R4 colocates it as extra |
| R4 | prop_2_3_R epi-semantics + `markC_admissible_R` (colocated; §5 supply shape per MStageCountGammaA:393) | opus | `GQ2/Roe/Prop23.lean` | R3 ✓ | **dispatched 2026-07-24 night** |
| R5 | small-group numerical cross-check vs June LMFDB-verified counts | opus | `GQ2/Roe/Sanity.lean`, `scripts/roe_sanity_counts.py` | R1 | **done 2026-07-24 — VERDICT: MATCH** (30feeb6; C₂ 7, C₄ 24, V₄ 42, D₄ 144, Q₈ 144; four-way agreement incl. re-run June engine.py). Notes banked: archive convention g^h=hgh⁻¹ vs Lean g⁻¹xg reconciled by σ↦σ⁻¹ bijection (relevant to R32/comparator); `admissibleCountR` NOT decide-able (powOmega2/closure) — counts checked numerically, relator pinned per-group in Lean; anomalous term cR activates only at order ≥16 → `cRExp_d8_ne_one` in DihedralGroup 8 is the first nontrivial machine check of it. (Git note: R5's GQ2.lean commit swept 4 import lines appended by the parallel R7 worker — cosmetic, self-heals when R7 commits) |
| R6 | tame quotient + ν_R + W_R = O₂ (note lem:tame; phiR/nuR in BoundaryMaps-field shapes; builds on R3's wildCoreR) | opus | `GQ2/Roe/Tame.lean` | R3 ✓ | **dispatched 2026-07-24 night** |
| R20 | §5 scaffolding parameter-boundary recon (read-only, citation-dense) | opus | report `roe-r20-recon.md` | — | **done 2026-07-24** → `roe-r20-recon.md` (e78bdb7). Key: word couples via definitional spine (`wildValue→d1Fun/Z1w/H*w/mixedB`); dévissage states over the FIXED spine — no `mixedB_R` drop-in. Orchestrator decision: **clone route** for `Devissage/`-dependent assembly (~3k ln, proofs port verbatim, new files only; spine-generalization noted as post-campaign cleanup option — no frozen-file edits overnight). `prop_5_16` is word-generic, reused verbatim → R26 scope gains thin `cor_5_17_card_R` instead. `markC_admissible_R` assigned to R4. Q6 decl list drives R21–R26 prompts |

## Gate G1 — DECIDED 2026-07-24 night (delegated): **ROUTE L**

R2 proved Route N impossible (see R2 row — a theorem, not a failed search). Route N tickets
R7n–R11n are cancelled. Route L proceeds hypothesis-parametrized: the B-Lab classification
statement (Labute 1967 Thm 8+4 instance) enters only as `BLabHypothesis`/explicit hypothesis;
**the R14 census-flip commit that would make it an axiom waits for owner morning sign-off.**
Bonus de-risk: the exact §3.2 computation was independently re-derived by the spike, with
numerics on file for cross-checks.

## Wave 2 — P2 Route L ∥ P3 word level

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| R7 | D_R presentation (sorry-free) + P2 skeletons (DRDemushkin/CrossedDerivation/MarkedPro2, stmts final) + design memo incl. B-Lab draft | fable | `GQ2/Roe/DRPresentation.lean`, skeletons `DRDemushkin.lean`/`CrossedDerivation.lean`/`MarkedPro2.lean`, memo `roe-r7-design.md` | G1 ✓ | **done 2026-07-24** (4ca6c7a, 1214 ins; DRPresentation 0-sorry incl. `drWord`/`drLiftHom`/D₄ stress; skeletons: CrossedDerivation 6 sorries — `commP_wordLift` already proved, DRDemushkin 14, MarkedPro2 2 — `nuR` proved. **B-Lab draft in `section Draft` (BLabHypothesis, specialized to G := DR; owner decision points in memo) — REVIEW IN MORNING with R14**. Γ_R half of ⟦lem:pro2word⟧ (maxPro2 GammaR ≅ DR) deliberately deferred → assigned to R15) |
| R8 | B_R abelianization bookkeeping (BDecomposition clone; t = ȳ·x̄⁻², topological-generation lemma, demushkinQ feed) | opus | `GQ2/Roe/DRAbelianization.lean` | R7 ✓ | **dispatched 2026-07-24 night** |
| R9 | χ-twisted crossed-derivation fills: master evaluation, the 4 equations, branch exclusion, solution uniqueness (may leave 1 sorry if `_ext` needs in-flight R8) | fable | `GQ2/Roe/CrossedDerivation.lean` (fills) | R7 ✓, R10 ✓ | **dispatched 2026-07-24 night** |
| R10 | cubic Hensel + orientation-value arithmetic (STANDALONE — rescoped off R7's critical path) | opus | `GQ2/Roe/OrientationRoot.lean` | — | **done 2026-07-24** (1f4b265, 290 ln, 0 sorries, std-3; build 3313; mathlib-only imports). API for R9/R11: `rootX(_isRoot/_unique/_isUnit/_toZModPow_four=5/_five=21)`, `Sval(_mul_denom/_toZModPow_four=13)`, `Yval(_eq/_toZModPow_four=7/_ne_sq)`, `denom_isUnit`, `isUnit_sq_sub_self_sub_one_of_odd`, norm facts + exact-level `rootX_sub_one_eq`/`Sval_sub_one_eq` (∃ unit a, ·−1=4a — feeds `zpowZtwo_injective_of_exact_level`). All congruences match spike table |
| R11 | im χ_R = {±1}×(1+4ℤ₂) | opus | `GQ2/Roe/OrientationImage.lean` | R9, R10 | queued |
| R12+13 | **MERGED (single file owner per R7's flag)**: all 14 DRDemushkin sorries — H² card 2 (WordCoh2/CardH2GammaA clone + witness), nine cup-Gram entries + nondegen (p=2 bilinear pitfall), H¹ card 8, demushkinQ (may leave ≤2 sorries if R8 in flight) | opus (fable escalation if H² witness stalls) | `GQ2/Roe/DRDemushkin.lean` (fills) | R7 ✓ (+R8 for demushkinQ only) | **dispatched 2026-07-24 night** |
| R14 | B-Lab axiom flip (b9a-T5-style checklist) — **OWNER-GATED, do not dispatch** | fable | `Foundations/Axioms.lean`, `AxiomLedger.lean`, `check_axioms.sh` | R11–R13 + owner sign-off | blocked (owner) |
| R15 | marked matching assembly (prop_1_1 clone; unique b with S = X^b, k-shear, prop_3_8 reuse; R2's isometry seed + b,u numerics as cross-checks) | fable | `GQ2/Roe/MarkedPro2.lean` (fills) | R7–R13 (hypothesis-parametrized, not R14) | queued |
| R21 | r_R Fox spine (`d1FunR`/`Z1wR`/`H*wR` + `mixedB_R` def) + evaluated wild row split/ramified + trivial-module differential (b,b) | fable | `GQ2/Roe/FoxBasic.lean`, `GQ2/Roe/WildRow.lean` | R1 ✓, R20 ✓ | **dispatched 2026-07-24 night** |
| R22 | simple normal forms (0,0,0,d) | opus | `GQ2/Roe/NormalForms.lean` | R21 | queued |
| R23 | Stokes exponent vector ![0,e,e+1,0] + odd-e (0,1,0,0) endpoint input (RESCOPED: chain-map rows moved to R25) | opus | `GQ2/Roe/Stokes.lean` | R1 ✓ | **done 2026-07-24** (4abf603, +150 ln, std-3, 0 sorries; ns `GQ2.FoxH` beside consumers). R25 endpoint input = `expMod2_wildValueExpR_odd` via `congrFun (… (omega2Exp_exponent_heis_cast))`; sum-zero endpoint `expMod2_tame_add_wildValueExpR_odd`; e=3 `decide` stress |
| R24 | mixed Hessian z-ledger + 1+U+U⁻¹ pairing (note prop:hessian) | opus | `GQ2/Roe/Hessian.lean` | R21 | queued |
| R25 | traced chain-map rows (prop_5_8_*_R) + `mixedB_cocycle_R` + trivial-module Gram a·c′+c·a′+d·d′ + trivialSelfDual_R base | opus | `GQ2/Roe/TrivialSelfDual.lean` | R21, R23 | queued |
| R26 | Devissage clone (per R20 decision) + prop_5_15_R assembly + thin cor_5_17_card_R (prop_5_16 reused verbatim) | fable (+opus clone subtickets if split) | `GQ2/Roe/Devissage*.lean`, `GQ2/Roe/DualityAssembly.lean` | R22, R24, R25 | queued |

## Wave 3 — P4 + P5 + P6

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| R27 | quadratic expansion + Gauss signs by instantiation (note prop:quadratic, cor:gauss) | opus | `GQ2/Roe/Gauss.lean` | R24, R26 | — |
| R30 | SourceData extraction + thm_4_2/prop_8_9 generalization; Γ_A capstones byte-identical (regression-gated, serialized) | fable | `BoundaryFrame.lean`, `Prop89Close.lean`, `RecursionSplice.lean`, `ThmFourTwo.lean`, new `GQ2/SourceData.lean` | R20; ideally after R26 | — |
| R31 | Γ_R supply lemmas: lemma_8_2_R, liftsOver_card_R, lemma_8_6_R, GaussZ package (file list fixed by R30) | opus | `GQ2/Roe/Supply*.lean` | R30, R26, R27, P2 | — |
| R32 | sourceR instance + eq_154_R + main_surjection_count_R + main_presentation_literal_roe | fable | `GQ2/Roe/Main.lean` | R31, R4, P1, P2 | — |
| R40 | gates: check_axioms extension, ledger, formalization.yaml, comparator pair, README | opus | those files | R32 | — |
| R41 | docs sweep + blueprint/verso chunk for the note (site repo; non-blocking) | opus | docs | R40 | — |

## Gate G2 (owner)

Final axiom-census sign-off (unchanged on Route N; +B-Lab on Route L); review-packet
addendum; archive this board per `docs/orchestration/README.md`.
