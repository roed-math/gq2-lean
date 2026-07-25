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
- 2026-07-24 night (orchestrator hotfix daecc5a): `GQ2.nuR` name collision — R6's Tame.lean
  (Γ_R-side) vs R7's MarkedPro2.lean skeleton (D_R-side) both defined `nuR`; MarkedPro2's
  renamed `nuDR` (mechanical, file unowned at the time). Aggregate build unblocked. New
  convention: orchestrator + workers use path-limited `git commit -- <files>` (shared-index
  races swept files twice tonight).
- 2026-07-24 night (orchestrator hotfix 2 + stitch, f713db8): nuR_ THEOREM-name renames in
  MarkedPro2 (nuDR_drS/X/Y, nuDR_surjective — first hotfix's \b missed underscore-joined
  names, caught by R8); R9's recorded 3-line `isLabuteOrientation_ext` proof stitched in
  once R8 landed → CrossedDerivation.lean now SORRY-FREE.
- 2026-07-25 morning (orchestrator, new session): **weekly-limit interruption swept all four
  in-flight workers** (R13b-exec, R15, R26a, R31a). Salvage checkpoint `94091f0` commits all
  partial work (build UNVERIFIED — workers verify own lanes): DRWordCoh +260 ln (1 sorry),
  Devissage/ tree ~2.3k ln (0 sorries), Supply.lean 219 ln (0 sorries); R15 had no edits.
  HEAD had been left broken by a mid-flight GQ2.lean sweep (imported never-committed
  `GQ2.Roe.SelfDual` + untracked Devissage files) — fixed in the same checkpoint.
  **GQ2.lean ownership moves to the orchestrator for the rest of the wave**: workers touch it
  only to add an import for a NEW file they create, committed path-limited together with that
  file. All four tickets re-dispatched 2026-07-25.
- 2026-07-25 (owner, morning gates): **B-Lab DECLINED — no new axiom.** R14 CANCELLED.
  `BLabHypothesis` stays the interface; it must be DISCHARGED by an actual Lean proof of the
  Labute classification instance → new **L-campaign** (L0 scoping ticket dispatched, fable;
  deliverable `labute-plan.md` for owner review BEFORE any L-tickets run). R15/R32 capstones
  stay hypothesis-parametrized until L lands; everything else is insulated (plan §3 fat-tail
  provision). **R30 GREEN-LIT** — dispatch after R26b lands ("ideally after R26" honored).
- 2026-07-25 (orchestrator, incident log): a transient API incident stalled R15/R30 mid-run
  and killed L0's literature sub-survey; all resumed. During recovery the orchestrator
  misrouted the "finish the orphaned survey" handoff to the (finished) R26b agent instead of
  L0 — R26b flagged the discrepancy, completed the survey legitimately, and landed
  labute-plan.md (98a1cda); L0 re-woken only to author-verify the graft. Lesson: keep the
  agent-ID ledger per ticket, double-check before SendMessage.
- 2026-07-25 (orchestrator): R26b dispatched on R26a's landing. R26a's report RETRACTS the
  R25 predicate-reconcile flag: `IsSelfDual_R` (fixedPts form) + `IsSelfDualW_R` (H⁰w form)
  mirror Γ_A's pair exactly, bridged by `isSelfDual_iff_W_R`; planned name `IsSelfDualR`
  exists nowhere. ⚠ MODULE-SYSTEM PITFALL (from R31a, cost the predecessor its whole
  verification): `module`-style files CANNOT import non-module files (one-directional);
  anything importing the §2/§8 stack (ScalarCount, Prop89Close, RecursionSplice,
  PresentationLiteral, Prop23) must be plain-import style — R30's `GQ2/SourceData.lean`
  included.

## Wave 1 (parallel: R1→R3→R4→R5 lane; R6 lane; R2 lane; R20 lane)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| R1 | Roe words + WildRelR + admissibleCountR + wildValueExpR (+stress) | fable | `GQ2/Roe/Words.lean` | — | **done 2026-07-24** (278053c, 261 ln, 0 sorries, std-3 axioms; full build 3309 green). API: `Marking.aR/y1R/cR/wildValueR/WildRelR/AdmissibleR`, `GQ2.admissibleCountR`, `wildValueExpR(+_of_dvd, TWO ω₂-subwords — σ₂ also ω₂; ticket sketch corrected per tex), map naturality, zmod8 stress incl. genuine-ω₂ `wildValueR_zmod8`. Exponent preview for R23: (0,e,e+1,0) |
| R2 | Nielsen search spike: ν-constrained D_R ⇄ D₀ words (off-Lean, q2 archive tooling; timeboxed) | fable | report `roe-r2-spike.md` (no Lean) | — | **done 2026-07-24** (fe4469d) → **ROUTE N NOT VIABLE — impossibility THEOREM** (any word-epi is auto-iso by 5-term exact seq; isos intertwine canonical orientations; norm kill in ℚ(X), disc −59: η has N = −1/27, word-values land in ±4^ℤ). Method validated on d0PiEquiv; §3.2 computation independently re-derived (X≡5, S≡13 mod 16; b≡91367, u≡898793 mod 2^20); Hom-counts agree on all 2668 2-groups ≤128. Extras banked: R13 p=2 cup–Bockstein pitfall, R15 Gram-isometry seed, R5 Hom-count trick |
| R3 | GammaR marked quotient + AdmissibleLimit clone (+`wildRelatorR` profinite word + finite↔profinite bridge; `map_admissibleR` via Subdirect:104 clone) | opus | `GQ2/Roe/GammaR.lean`, `GQ2/Roe/AdmissibleLimit.lean` | R1 | **done 2026-07-24** (486c888, 247+319 ln, 0 sorries, std-3 on all 9 terminals; build 3312). Bridge factored via evaluation lemma `map_wildRelatorR`; shared helpers reused not recloned. R4 chain mapped: clone `admissible_of_NA_le_ker`; FLAG: `markC_admissible` is NOT a prop_2_3 input (it's the §5 supply seam) — R4 colocates it as extra |
| R4 | prop_2_3_R epi-semantics + `markC_admissible_R` (colocated; §5 supply shape per MStageCountGammaA:393) | opus | `GQ2/Roe/Prop23.lean` | R3 ✓ | **done 2026-07-24** (6290b18, 0 sorries, std-3 on both capstones). `prop_2_3_R : #ContSurj GammaR G = admissibleCountR G`; `markC_R := Marking.pushR` (markC is Γ_A-hard-typed), consumption shape pinned by `markC_admissible_R_clauses`. Fixes: ticket's `NR_le_ker` suggestion was circular → used `isAdmissibleUR_of_NR_le`. **R32 NOTE: Roe/Prop23 is a NON-module file (imports non-module GQ2.Prop23) → R32 must be non-module too, like PresentationLiteral.lean.** P0 phase COMPLETE (R1/R3/R4/R5 ✓✓✓✓) |
| R5 | small-group numerical cross-check vs June LMFDB-verified counts | opus | `GQ2/Roe/Sanity.lean`, `scripts/roe_sanity_counts.py` | R1 | **done 2026-07-24 — VERDICT: MATCH** (30feeb6; C₂ 7, C₄ 24, V₄ 42, D₄ 144, Q₈ 144; four-way agreement incl. re-run June engine.py). Notes banked: archive convention g^h=hgh⁻¹ vs Lean g⁻¹xg reconciled by σ↦σ⁻¹ bijection (relevant to R32/comparator); `admissibleCountR` NOT decide-able (powOmega2/closure) — counts checked numerically, relator pinned per-group in Lean; anomalous term cR activates only at order ≥16 → `cRExp_d8_ne_one` in DihedralGroup 8 is the first nontrivial machine check of it. (Git note: R5's GQ2.lean commit swept 4 import lines appended by the parallel R7 worker — cosmetic, self-heals when R7 commits) |
| R6 | tame quotient + ν_R + W_R = O₂ (note lem:tame; phiR/nuR in BoundaryMaps-field shapes; builds on R3's wildCoreR) | opus | `GQ2/Roe/Tame.lean` | R3 ✓ | **done 2026-07-24** (fd289c9, 0 sorries, std-3, **B10-free**). R32 package: `phiR(_surjective)`, `ker_phiR = wildCoreR`, `wildCoreR_isMax` (W_R=O₂), `nuR(_surjective)` + generator values. Raw-carrier spelling `F₄ ⧸ NR` matching R3 (bundled-GammaR instance synthesis fails; trivial wrapper if needed). P1 phase COMPLETE |
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
| R8 | B_R abelianization bookkeeping (BDecomposition clone; t = ȳ·x̄⁻², topological-generation lemma, demushkinQ feed) | opus | `GQ2/Roe/DRAbelianization.lean` | R7 ✓ | **done 2026-07-24** (e045a1c, 0 sorries, std-3). `BRDecomposition`/`br_decomposition(+_Y)`, `dr_topGen`, `dr_hom_ext`, `phiEquivR`, torsion ≅ ZMod 2, `demushkinQ_DR_eq_two`. Flagged residual nuR_surjective collision → fixed in hotfix f713db8 |
| R9 | χ-twisted crossed-derivation fills | fable | `GQ2/Roe/CrossedDerivation.lean` (fills) | R7 ✓, R10 ✓ | **done 2026-07-24** (453905e; 6→1 sorries, the 1 = permitted R8-gated `isLabuteOrientation_ext` with finished proof in a comment). ⟦prop:orientation⟧ equations extracted (`isLabuteOrientationDatum_iff`), root satisfies (`_of_root`, via h2S : 2S = X²+1), branch Y=X² killed, uniqueness (`_unique`). Method: sympy-Gröbner cofactor certificates fed to `linear_combination` over the unit ideal — all std-3 |
| R10 | cubic Hensel + orientation-value arithmetic (STANDALONE — rescoped off R7's critical path) | opus | `GQ2/Roe/OrientationRoot.lean` | — | **done 2026-07-24** (1f4b265, 290 ln, 0 sorries, std-3; build 3313; mathlib-only imports). API for R9/R11: `rootX(_isRoot/_unique/_isUnit/_toZModPow_four=5/_five=21)`, `Sval(_mul_denom/_toZModPow_four=13)`, `Yval(_eq/_toZModPow_four=7/_ne_sq)`, `denom_isUnit`, `isUnit_sq_sub_self_sub_one_of_odd`, norm facts + exact-level `rootX_sub_one_eq`/`Sval_sub_one_eq` (∃ unit a, ·−1=4a — feeds `zpowZtwo_injective_of_exact_level`). All congruences match spike table |
| R11 | chiR + IsLabuteOrientation + surjectivity | opus | `GQ2/Roe/ChiR.lean` | R9 ✓, R10 ✓ | **done 2026-07-24** (ec024cd, 243 ln, 0 sorries, std-3). `chiR` via drLiftHom at (SvalUnit,rootXUnit,YvalUnit); `isLabuteOrientation_chiR`; `chiR_torsion` = −1 on drY·drX⁻²; **surjectivity via Burnside/Frattini + mod8_sq** (index-2 subgroups contain squares; 5,7 mod 8 classes force ⊤ — no zpowZtwo closure needed). **B-Lab hypothesis package now fully proven.** Congruence stress ≡5/≡13 mod 16 |
| R12+13 | MERGED: DRDemushkin fills | opus | `GQ2/Roe/DRDemushkin.lean` (fills) | R7 ✓ | **partial 2026-07-24** (140033f): H¹ half DONE (`drH1_bijective`, `card_H1_DR=8`, `demushkinRank_DR=3` — std-3). H² half (12 sorries: card_H2, 9 Gram, nondegen, demushkinQ) BLOCKED on missing 3-gen/1-relator word-coh infra (WordCoh2/WordCohBridge hard-wired to Γ_A) → escalated to R13b |
| R13b | ESCALATION: D_R H² word-coh bridge + discharge DRDemushkin | opus | `GQ2/Roe/DRWordCoh.lean` (+`DRH2.lean`), `GQ2/Roe/DRDemushkin.lean` (fills) | R12+13 partial, R21 ✓, R24 ✓, R8 ✓ | research pass done (no write tools — returned validated plan): **Gram bridge PROVEN GREEN by `decide`** (all 9 entries = [[0,1,0],[1,0,0],[0,0,1]] incl. Bockstein diag); gating CORRECTED (ss/xx NOT R8-gated; only demushkinQ, now dischargeable). Plan committed `roe-r13b-plan.md` (428d413) → exec interrupted 07-24, salvaged 94091f0 → **done 2026-07-25** (90d7cf1 + e8a196d + 7688f68): DRWordCoh 936 ln / 0 sorries, DRDemushkin 522 ln / 0 sorries; capstones isDemushkin_DR, demushkinRank_DR=3, demushkinQ_DR=2, card_H2_DR=2, obsH2_DR_injective, Gram entries — ALL std-3, zero census axioms. **BLabHypothesis antecedents now all theorems.** Salvage twist: hard seam (ker⊆B² injectivity) was already genuinely proven; the sorry was the factoring bridge, done via `obsH2_DR_eq_of_factor` needing NO continuity of ρ. Upgrade: single bilinear `drCup_obs` (64-case decide) subsumes all 9 Gram entries + card + both nondegen clauses. NO DRH2.lean (helpers private in DRDemushkin; +import of DRWordCoh); 69 ln stale private dr_hom_ext clone deleted → rewired to R8's public one. Note: `drE` (D_R ↠ 𝔽₂³) is PRIVATE — promote if a later ticket needs it |
| R14 | ~~B-Lab axiom flip~~ | fable | — | — | **CANCELLED 2026-07-25 — owner DECLINED B-Lab** (no new axiom; census stays frozen). Replaced by the L-campaign below: BLabHypothesis to be discharged by a Lean proof of the Labute instance |
| R15a | maxPro2(GammaR) ≅ DR bridge (⟦lem:pro2word⟧ Γ_R half) | opus | `GQ2/Roe/MaxPro2Bridge.lean` | R3 ✓, R6 ✓, R7 ✓, R8 ✓ | **done 2026-07-24** (823cecf, 504 ln, 0 sorries, std-3, UNCONDITIONAL — no B-Lab). `maxPro2Bridge : ContinuousMulEquiv (maxPro2 (F₄⧸NR)) DR` as direct def; keystone `wildValueR_eq_drWord_of_powOmega2_id` proved first; generator hooks + `maxPro2Bridge_spec` in prop_3_10 shape; raw-carrier spelling throughout. Did NOT import MarkedPro2 (would cycle) — ν-composite left as 1-liners for R15 |
| R15 | marked matching assembly (prop_1_1 clone; unique b with S = X^b, k-shear, prop_3_8 reuse) | fable | `GQ2/Roe/MarkedPro2.lean` (fills) (+opt `MarkedMatching.lean`) | R7–R11 ✓ (cites in-flight R13b's sorried isDemushkin_DR/demushkinQ_DR — axiom print self-heals when R13b lands) | **done 2026-07-25** (2f12a75+66289e3+ff5810c+4eca604; survived a mid-run infra stall). NEW MarkedMatching.lean 1218 ln + MarkedPro2 fills — 0 sorries, statements VERBATIM to R7 skeleton; full build green 3345 jobs. `markedPro2_R` = std-3 + {dyadicOrientation, peripheralCyclotomicAction} (census only, NO sorryAx, BLab still hypothesis); `nuDR_surjective` std-3 unconditional. Route upgrade vs memo: (u,b) solved via coordinate system + mod-2 generation engine + τ₂-parity mod 16; orientation functoriality via 3 master crossed derivations D₀ → ℤ₂(χ₀)⋊ℤ₂ˣ + invertible 3×3 evaluation matrix (`isLabuteOrientation_comp_iso` holds for EVERY continuous iso). ⚠ MarkedPro2 converted to NON-module (forced by prop_1_1/prop_3_8/LocalMarked June chain) → R32 assembly must be non-module. ν-composite quadruple `nuDR_maxPro2Bridge_*` ready for R32. **P2 phase COMPLETE (hypothesis-parametrized)** |
| R21 | r_R Fox spine (`d1FunR`/`Z1wR`/`H*wR` + `mixedB_R` def) + evaluated wild row split/ramified + trivial-module differential (b,b) | fable | `GQ2/Roe/FoxBasic.lean`, `GQ2/Roe/WildRow.lean` | R1 ✓, R20 ✓ | **done 2026-07-24** (633daae, 607 ins, 0 sorries, std-3; ns `GQ2.FoxH`). Rows: split `x1+x2+σ⁻¹•x2` (needs NO hU — weaker than Γ_A!), ramified `σ⁻¹•x2`; swap-vs-Γ_A mechanized (`liftMarking_wildValueR_u_eq_swap`); trivial collapse `d1FunR_of_trivial` (=(x1,x1)); `mixedB_R`+`bridge_wildR` in FoxBasic — later tickets IMPORT bridge_wildR, never re-define. (check_axioms repo-wide currently red on MarkedPro2's in-flight skeleton sorries — expected mid-wave; wave-close gate) |
| R22 | simple normal forms (0,0,0,d) | opus | `GQ2/Roe/NormalForms.lean` | R21 ✓ | **done 2026-07-24** (36cfe95, 206 ln, 0 sorries, std-3). `x1Supported`, `lemma_5_13_split_R` (no hU — one fewer arg), `lemma_5_13_ramified_R` (∃! (0,0,0,d) rep, hypothesis-based for A and A∨), `b1wR_split_shape`. Scope map for R26: H⁰/H²/H¹-cards + `split_shapes_of_wild_R`-style DualityAssembly helpers are R26's (mechanical x2↔x3 swaps); pairing lemmas are R24's |
| R23 | Stokes exponent vector ![0,e,e+1,0] + odd-e (0,1,0,0) endpoint input (RESCOPED: chain-map rows moved to R25) | opus | `GQ2/Roe/Stokes.lean` | R1 ✓ | **done 2026-07-24** (4abf603, +150 ln, std-3, 0 sorries; ns `GQ2.FoxH` beside consumers). R25 endpoint input = `expMod2_wildValueExpR_odd` via `congrFun (… (omega2Exp_exponent_heis_cast))`; sum-zero endpoint `expMod2_tame_add_wildValueExpR_odd`; e=3 `decide` stress |
| R24 | mixed Hessian z-ledger + 1+U+U⁻¹ pairing (note prop:hessian) | opus | `GQ2/Roe/Hessian.lean` | R21 ✓ | **done 2026-07-24** (d3001c0, 395 ln, 0 sorries, std-3). Ledger + assembled `heisMarking_wildValueR_z(_ramified)`, `mixedB_R_pairing_split/_ramified`, `pairingR_operator_injective` (thin alias — Γ_A's operator lemma verbatim, presentation-independent); htau kept as unused binder for R26 signature parity; ramified diagonal needs NO ω₂-collapse (the h₀-free simplification, confirmed) |
| R25 | traced chain-map rows (prop_5_8_*_R) + `mixedB_cocycle_R` + trivial-module Gram + trivialSelfDual_R base | opus | `GQ2/Roe/TrivialSelfDual.lean` | R21 ✓, R23 ✓ | **done 2026-07-24** (3f1aa2a, 582 ln, 0 sorries, std-3). prop_5_8_left/right_R via bridge_wildR + R23 endpoint; Gram [[0,1,0],[1,0,0],[0,0,1]] by decide; ω₂-scalar aR.z lands on (2,2) slot (wild-column swap) w/ killer lemmas; Stokes-bridge helpers built here (R23 shipped exponents only). ⚠ defined `IsSelfDual_R` locally — RECONCILE with R26a's planned `IsSelfDualR` in R26b (single predicate must win) |
| R26a | mechanical dévissage clone onto the r_R spine (`IsSelfDualR`, Devissage/ + DevissageInduction twins, target `prop_5_15_of_simple_R`; ElemDualPack + generic helpers reused not cloned) | opus | `GQ2/Roe/SelfDual.lean`, `GQ2/Roe/Devissage*.lean`, `GQ2/Roe/DevissageInduction.lean` | R21 ✓ (spine only) | **done 2026-07-25** (predecessor had actually FINISHED + built green before the limit hit; verifier commit 810b949, doc-fixes only): 11 files, 2287 ln, 65 decls, 0 sorries; `GQ2.FoxH.prop_5_15_of_simple_R` (DevissageInduction.lean:45) + lemma_5_11_R + card_H1w_eq_R + card_Z1w_eq_sq_mul_card_H2w_R all std-3, ZERO census axioms. 96-vs-207 DevissageInduction gap = legitimate `(A)`-generic reuse (imports Γ_A twin). `H0w`/`fixedPts`/`elemDual_separates` word-free → reused UNSUFFIXED in R statements. Permanent note: no shared spine — future Γ_A dévissage edits must be hand-mirrored into Roe/Devissage/ |
| R26b | duality assembly: `selfDual_of_simple_R` + `prop_5_15_R` + thin `cor_5_17_card_R` (prop_5_16 reused verbatim) | fable | `GQ2/Roe/DualityAssembly.lean` | R22 ✓, R24 ✓, R25 ✓, R26a ✓ | **done 2026-07-25** (2fc6bde + prereq c3a549c, 548 ln, 0 sorries). `selfDual_of_simple_R` + `prop_5_15_R` std-3 ONLY; `cor_5_17_card_R` std-3 + census B6 (tateDualityAt) + B7 (localEulerCharacteristic) — BYTE-IDENTICAL to Γ_A's cor_5_17_card print, inherited solely via verbatim prop_5_16. Statement shapes recorded in worker report for R31/R32 (x₀↔x₁ swap; split_shapes hU-free but split pairing still consumes hU via sigma2_smul_trivial; ramified pairing drops ht/hw). **CRITICAL FIX c3a549c: `GQ2.FoxH.x1Supported` was declared in BOTH NormalForms:68 and Hessian:81 → root GQ2 build was IMPOSSIBLE (env collision); Hessian now imports NormalForms' def — single home is NormalForms, keep it that way.** H0wR_eq_H0w/B1wR_eq_B1w are rfl → shared H0w layer consumable unsuffixed. P3 phase COMPLETE |

## Wave 3 — P4 + P5 + P6

Orchestrator addition (2026-07-24 night): R30a SourceData recon **done** — memo committed
`roe-r30-recon.md` (28bcd0b): 12+1 A-side fields (promote ker_pro2 to field), 7 obligation
families = R31's list, minimal-diff b9a-flip refactor shape (6 files touched, core+producers
untouched), Γ_R readiness table (tame/ν/ker/epi DONE; pro2 gated on R15a; sourceR → R32),
top risks (shared-G0 Gauss seam — recommend external-G0 fields; binder/carrier fragility —
regression-gate capstones). R30 EXECUTION HELD FOR MORNING (pairs with B-Lab sign-off).
| R31a | R30-independent supply: `gammaR_topologicallyFinitelyGenerated` + `lemma_8_2_R` (#Hom=8) | opus | `GQ2/Roe/Supply.lean` | R3 ✓, R6 ✓, recon | **done 2026-07-25** (e4b1b9f, 223 ln, 0 sorries; capstones `gammaR_topologicallyFinitelyGenerated` + `lemma_8_2_R` and 4 extras all std-3, zero census axioms). Predecessor's math sound but NEVER CHECKED — illegal `module` header (imports non-module ScalarCount) had blocked all elaboration; converted to plain imports (Prop23 precedent), proofs compiled unchanged. R30 recon rows ii.1/ii.2 → DONE. Carrier answer for SourceData: bundled `GammaR : ProfiniteGrp` works for both rows, but keep each field's spelling as-is (ii.1 `: Type` ascription, ii.2 bare coercion) — normalizing would edit frozen Γ_A capstones |

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| R27 | quadratic expansion + Gauss signs by instantiation (note prop:quadratic, cor:gauss; word-level layer only — GaussZ package = R31) | opus | `GQ2/Roe/Gauss.lean` | R24 ✓ | **done 2026-07-24** (45095be, 252 ln, 0 sorries, std-3 on 7 capstones). `QZeroR(_apply/_split/_eq_qDouble)`, `polar_QZeroR` + nonsingularity via R24's operator, zero counts + finsum signs ∓2^m by instantiating prop_6_9/lemma_6_6/6_8 verbatim. NON-module file (needs non-module GaussZ.FinalGammaA). κ⁰/honest word evaluation deferred to R31 per scope |
| R30 | SourceData extraction + thm_4_2/prop_8_9 generalization; Γ_A capstones byte-identical (regression-gated, serialized) | fable | `BoundaryFrame.lean`, `Prop89Close.lean`, `RecursionSplice.lean`, `ThmFourTwo.lean`, new `GQ2/SourceData.lean` | R20 ✓; R26b ✓ (owner green-lit 2026-07-25) | **done 2026-07-25** (441f3a4→c10899f→eaabe1a→b8fe006; survived a mid-run infra stall). ALL 4 GATES PASSED: capstone statement diffs EMPTY (prop_8_9, prop_8_9_of, thm_4_2, thm_4_2_stratum); axiom prints identical pre/post incl. eq_154/main_surjection_count'; full build green 3345; check_axioms failure = R15's then-in-flight sorries only (since resolved). NEW GQ2/SourceData.lean 491 ln at ThmFourTwo's import level (NON-module), `BoundaryMaps.sourceA` + `thm_4_2_of_sources` + `prop_8_9_of_sources` + `terminal_count_eq_of_sources` + `gaussZ_obtain_blockD_of_sources`. Deviations (frozen surface SHRUNK): BoundaryFrame.lean + SectionNine/Induction.lean UNTOUCHED (generic lanes replayed in SourceData.lean). Field drift vs recon flagged: +4 generator fields, +3 action-layer fields, ii.7 = two external-G0 dichotomy leaves. R32 path pinned: `thm_4_2_of_sources sourceR boundaryMapsWitness (tameFrame …) localReciprocity …`. Gotcha recorded: named-arg partial application for instance-implicit Pi binders |
| R31 | Γ_R supply: remaining sourceR obligations ii.3–ii.7 (liftsOver_card, lem86, cardH2+stageR136, Phase140 residues, GaussZ dichotomy twins) + trivial-action instance | opus | `GQ2/Roe/Supply2.lean`, `GQ2/RStage/GammaR.lean`, `GQ2/Phase140/GammaR.lean`, GaussZ Γ_R twins (new files, mirror Γ_A layout) | R30 ✓, R26b ✓, R27 ✓, P2 ✓ | **partial 2026-07-25** (9e6154a: RStage/GammaR.lean instance row DONE — trivial action + htriv_gammaR, 103 ln, std-3, smoke-tested, root build green). **ESCALATION FLAGGED**: ii.5 cardH2 NOT thin — WordCoh2 (1457 ln) is Γ_A-hard-wired (116 NA/GA mentions; obsH2 at F₄⧸N_A; no z1EquivR in WordCohBridge); ii.6 stageR136 bottoms out in ~1.2k ln of RStage/GammaA (hsep_hom/hZcount), not a wrapper; total Γ_A-specific surface behind ii.3–ii.7 ≈ 10.7k ln. Mitigation: DRWordCoh's TwoCocycle/central-ext layer is source-GENERIC → gap is Γ_R glue (R12+13→R13b escalation pattern). card_H2_DR confirmed unusable for SourceData.cardH2 (wrong group). Worker paused for its own survey subagents; orchestrator to resume with split decision on survey landing |
| R32 | sourceR instance + eq_154_R + main_surjection_count_R + main_presentation_literal_roe | fable | `GQ2/Roe/Main.lean` | R31, R4, P1, P2 | — |
| R40 | gates: check_axioms extension, ledger, formalization.yaml, comparator pair, README | opus | those files | R32 | — |
| R41 | docs sweep + blueprint/verso chunk for the note (site repo; non-blocking) | opus | docs | R40 | — |

## L-campaign — Labute classification discharge (created 2026-07-25, owner declined B-Lab)

Goal: prove `BLabHypothesis` as a theorem (Labute 1967 Thm 8+4, instance n=3/q=2/f=2 ⇒
≅ D₀), eliminating the would-be axiom. R15/R32 capstones carry the hypothesis until this
lands; no other ticket blocks on it. Ticket board TBD from `labute-plan.md` after owner
review.

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| L0 | scoping recon: proof-route comparison (Labute original vs NSW III§9 vs instance-specific), repo/mathlib asset map, phased decomposition + estimates + first spike | fable | `docs/orchestration/labute-plan.md` (no Lean) | — | **done 2026-07-25** (98a1cda, 495 ln; L0's lit-survey child died on an API error and the §2.6a literature graft was landed by the R26b worker on reassignment — Serre Bourbaki 252 page-verified as primary proof source: λ-series = our filtration, q=2 defect repair, χ-surjective ⟹ f=2, D₀ relator p.148; L0 author-verified the graft: clean except one §6 cross-reference, fixed e68fdbe). **Recommended: Route L2 — levelwise two-sided lifting** (λ-tower + stage lemma + König via Reconstruction.lean machinery + profinite_hopfian endgame; no Aut(F₃), no graded-Lie unless HIGH). Effort LOW ≈2k ln/1.5–2 swarm-days, LIKELY 2.5–5.5k/2.5–4, HIGH 6–10k/8–15 (graded-Lie fat tail; LS detects). Zero census-axiom dependence; B3c must NOT be touched; lean_verify bLab must print std-3 exactly |
| LS | off-Lean de-risking spike (Sage/GAP ANUPQ p-quotient to depth k≈7–9 + paper-level stage lemma vs sources + computational induction test + f=3 control); verdict GREEN/AMBER/RED gates L1 | fable | `docs/orchestration/labute-spike.md` (no Lean) | owner ✓ (**approved 2026-07-25: auto-run L1–L6 if GREEN**; AMBER/RED → owner with §7 options) | **dispatched 2026-07-25** |
| L1 | design memo + compiling sorry-skeletons (statements final): λ-tower API, levelwise sets + defect, stage lemma w/ invariant P per LS, base-case interfaces, assembly stmt | fable | `GQ2/Roe/Labute/{TwoCentralTower,Levelwise,StageLemma,Assembly}.lean` skeletons + `labute-l1-design.md` | LS GREEN | queued |
| L2 | λ-tower fills (generic pro-2 lower 2-central series: openness, nbhd basis, Zₖ, functoriality, G ≅ lim G/λₖ) | opus | `TwoCentralTower.lean` | L1 | queued |
| L3 | base cases: witness triples + relator/generation checks through k₀, both directions (witnesses from LS numerics) | opus | `Levelwise.lean` | L1 | queued |
| L4 | stage lemma: defect calculus + reachability under P for k ≥ k₀ (split L4a calculus / L4b reachability if L1 decides) — THE tail | fable | `StageLemma.lean` | L1, L2 | queued |
| L5 | assembly: `exists_contSurj_of_levelwise_nonempty` refactor (SERIALIZED existing-file edit of Reconstruction.lean, byte-identical-consumers gate), two epis, Hopfian endgame, `theorem bLab : BLabHypothesis`, stress | opus | `Assembly.lean`, `GQ2/Reconstruction.lean` (refactor only) | L2, L3, L4 | queued |
| L6 | gates/docs: literature-axioms B3 addendum (B-Lab DISCHARGED as theorem, census unchanged), std-3 certificate for bLab, board/README, blueprint hook | opus | docs | L5 | queued |

Middle-path owner options if LS comes back AMBER (plan §7): O1 axiomatize only the uniform
stage step; O2 axiomatize levelwise nonemptiness (machine-falsifiable, least
classification-shaped); O3 timebox L4 then drop to O1.

## Gate G2 (owner)

Final axiom-census sign-off (census UNCHANGED — B-Lab declined; unconditional main
statement requires the L-campaign to discharge BLabHypothesis); review-packet addendum;
archive this board per `docs/orchestration/README.md`.
