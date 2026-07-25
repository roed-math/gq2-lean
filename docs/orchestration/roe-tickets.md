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
| R5 | small-group numerical cross-check vs June LMFDB-verified counts | opus | `GQ2/Roe/Sanity.lean` (+optional `scripts/roe_sanity_counts.py`) | R1 | **dispatched 2026-07-24 night** (first dispatch aborted instantly w/ zero tool uses — glitched run, relaunched) |
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
| R7 | D_R presentation (sorry-free) + P2 skeletons (DRDemushkin/CrossedDerivation/MarkedPro2, stmts final) + design memo incl. B-Lab draft | fable | `GQ2/Roe/DRPresentation.lean`, skeletons `DRDemushkin.lean`/`CrossedDerivation.lean`/`MarkedPro2.lean`, memo `roe-r7-design.md` | G1 ✓ | **dispatched 2026-07-24 night** |
| R8 | B_R abelianization bookkeeping (BDecomposition clone, t = ȳ−2x̄) | opus | `GQ2/Roe/DRAbelianization.lean` | R7 | queued |
| R9 | χ-twisted crossed-derivation fills: the 4 equations + branch exclusion | fable | `GQ2/Roe/CrossedDerivation.lean` (fills) | R7, R10 | queued |
| R10 | cubic Hensel + orientation-value arithmetic (STANDALONE — rescoped off R7's critical path) | opus | `GQ2/Roe/OrientationRoot.lean` | — | **dispatched 2026-07-24 night** |
| R11 | im χ_R = {±1}×(1+4ℤ₂) | opus | `GQ2/Roe/OrientationImage.lean` | R9, R10 | queued |
| R12 | Demushkin-ness: dim H¹(D_R) = 3 | fable | `GQ2/Roe/DRDemushkin.lean` (fills, H¹ half) | R7 | queued |
| R13 | dim H²(D_R) = 1 + cup Gram nonsingular (mind R2's p=2 bilinear-Gram pitfall) | opus | `GQ2/Roe/DRH2.lean` | R12 | queued |
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
