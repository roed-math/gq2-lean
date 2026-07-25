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
| R1 | Roe words + WildRelR + admissibleCountR + wildValueExpR (+stress) | fable | `GQ2/Roe/Words.lean` | — | **dispatched 2026-07-24 evening** (worktree warm: build green 3308 jobs) |
| R2 | Nielsen search spike: ν-constrained D_R ⇄ D₀ words (off-Lean, q2 archive tooling; timeboxed) | fable | report `roe-r2-spike.md` (no Lean) | — | **dispatched 2026-07-24 evening** |
| R3 | GammaR marked quotient + AdmissibleLimit clone | opus | `GQ2/Roe/GammaR.lean`, `GQ2/Roe/AdmissibleLimit.lean` | R1 | queued |
| R4 | prop_2_3_R epi-semantics | opus | `GQ2/Roe/Prop23.lean` | R3 | queued |
| R5 | small-group numerical cross-check vs June LMFDB-verified counts | opus | `GQ2/Roe/Sanity.lean` | R1 | queued |
| R6 | tame quotient + ν_R + W_R = O₂ (note lem:tame) | opus | `GQ2/Roe/Tame.lean` | R1 | queued |
| R20 | §5 scaffolding parameter-boundary recon (read-only, citation-dense) | opus | report `roe-r20-recon.md` | — | **done 2026-07-24** → `roe-r20-recon.md` (e78bdb7). Key: word couples via definitional spine (`wildValue→d1Fun/Z1w/H*w/mixedB`); dévissage states over the FIXED spine — no `mixedB_R` drop-in. Orchestrator decision: **clone route** for `Devissage/`-dependent assembly (~3k ln, proofs port verbatim, new files only; spine-generalization noted as post-campaign cleanup option — no frozen-file edits overnight). `prop_5_16` is word-generic, reused verbatim → R26 scope gains thin `cor_5_17_card_R` instead. `markC_admissible_R` assigned to R4. Q6 decl list drives R21–R26 prompts |

## Gate G1 (owner → delegated to orchestrator 2026-07-24, see decisions log)

Route selection for P2 from the R2 spike result; if Route L, the B-Lab axiom statement is
drafted and used ONLY as a hypothesis until owner sign-off (R14 flip stays owner-gated).

## Wave 2 — P2 (route-dependent) ∥ P3 word level

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| R7n/R7 | D_R presentation (+ Route N: NielsenIso skeleton / Route L: design memo) | fable | `GQ2/Roe/DRPresentation.lean` (+`NielsenIso.lean` \| memo) | G1 | blocked (G1) |
| R8n/R8 | N: forward relator ledger \| L: B_R abelianization (BDecomposition clone) | opus | route-fixed | R7 | blocked (G1) |
| R9n/R9 | N: backward ledger + mutual inverse \| L: χ-twisted crossed-derivation calculus + 4 equations | opus \| fable | route-fixed | R7 | blocked (G1) |
| R10n/R10 | N: marked matching (ν direct) \| L: branch exclusion + cubic Hensel + mod-16 | opus | route-fixed | R8,R9 | blocked (G1) |
| R11n/R11 | N: marked assembly to G_ℚ₂(2) \| L: im χ_R = {±1}×(1+4ℤ₂) | fable \| opus | route-fixed | R10 | blocked (G1) |
| R12 | L only: Demushkin-ness — dim H¹ = 3 | fable | `GQ2/Roe/DRDemushkin.lean` | R7 | blocked (G1) |
| R13 | L only: dim H² = 1 + cup Gram (shares R25 machinery) | opus | `GQ2/Roe/DRH2.lean` | R12 | blocked (G1) |
| R14 | L only: B-Lab axiom flip (mirrors b9a T5 checklist) | fable | `Foundations/Axioms.lean`, `AxiomLedger.lean`, `check_axioms.sh` | R11–R13, G1 | blocked (G1) |
| R15 | L only: marked matching assembly (prop_1_1 clone; S = X^b, k-shear, prop_3_8 reuse) | fable | `GQ2/Roe/MarkedPro2.lean` | R14 | blocked (G1) |
| R21 | wild Fox row split+ramified + trivial-module differential (note prop:jacobian, lem:trivial) | fable | `GQ2/Roe/WildRow.lean` | R1, R20 | queued after W1 |
| R22 | simple normal forms (0,0,0,d) | opus | `GQ2/Roe/NormalForms.lean` | R21 | — |
| R23 | Stokes endpoint (0,1,0,0) + chain-map rows | opus | `GQ2/Roe/Stokes.lean` | R1, R20 | — |
| R24 | mixed Hessian + 1+U+U⁻¹ pairing (note prop:hessian) | opus | `GQ2/Roe/Hessian.lean` | R21 | — |
| R25 | trivial-module Gram + mixedB_cocycle analogue | opus | `GQ2/Roe/TrivialSelfDual.lean` | R23 | — |
| R26 | prop_5_15_R / prop_5_16_R duality assembly (note prop:duality) | fable | `GQ2/Roe/DualityAssembly.lean` | R22–R25 | — |

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
