# Dyadic campaign ticket board — general 2-adic fields, ramified-i case

**LIVE board.** Plan: [`plan.md`](plan.md) (binding constraints in its §0; architecture
decisions A1–A6 in its §3). References: [`refs/`](refs/) (packet overrides drafts — override
list in `refs/README.md`). Recon surveys: [`recon/`](recon/).

Campaign state: branch **`dyadic`** forked from `master` at `d0714a7` (2026-07-28); integration
worktree `~/claude/gq2-dyadic`; refs + surveys vendored. `master` stays ℚ₂-only; `dyadic` merges
to `master` only at owner gate G3.

## Board protocol

- **Workers NEVER edit this file** and never merge branches. The orchestrator alone updates
  rows, owns `GQ2.lean` (workers add only the import line for a new file they create, committed
  path-limited with that file), runs merges lane → `dyadic`, and merges `master` → `dyadic`.
- One ticket = one agent dispatch. Model column: **fable** = design/hard seams, **opus** =
  well-specified fills.
- Lane worktrees: lane `x` works on branch `dyadic-x` in `~/claude/gq2-dyadic-x`
  (`git -C ~/claude/gq2-lean worktree add ~/claude/gq2-dyadic-x -b dyadic-x dyadic`, then
  `lake exe cache get` once). ≤ 4–5 lane worktrees alive at a time; remove when a lane closes.
- **File ownership is exclusive per ticket** ("files owned" column). Never touch another
  ticket's files; cross-lane needs go through the orchestrator.
- Workers commit path-limited (`git commit -- <files>`) on green, message
  `dyadic <ID>: <summary>`, **commit fast after green**, and end with a report: files, commit
  hash, sorry/axiom state, deviations, discoveries affecting later tickets.
- Mid-flight sorries: allowed only in files listed (per ticket) in `SORRY_ALLOWLIST` of
  `scripts/check_axioms.sh`; allowlist empty at wave close. `EXPECTED_AXIOMS` changes only in
  owner-approved AX commits.
- **The nine obligations (MC-M, MC-N, WC-L, WC-N0, WC-Npc, WC-M0, WC-Mpc, LG-K, SD-n) are
  proof obligations — NEVER `axiom`s**, not even temporarily. Interim states: explicit
  hypothesis binders (`BLabHypothesis` pattern) or allowlisted sorries only.
- ⚠ Module-system rule (one-directional, R31a pitfall): `module`-style files cannot import
  plain-import files. Anything importing the §8/§9 stack (`SourceData`, `ThmFourTwo`,
  `Prop89Close`, `SectionNine`, `PresentationLiteral`, `Prop23`, `Roe/Main`) must be
  plain-import. Check imports before choosing the file header; when in doubt, plain-import.
- Kernel `decide` only (no `native_decide`); no unchecked CAS equality; finite-target counts
  are regressions in `scripts/` + stress lemmas, never proofs.
- Merge gates for every lane → `dyadic` merge: plan §7 (ten items).

## Orchestrator log

- 2026-07-28 (owner, session brief): campaign created. Packet is authoritative over both
  drafts; nine obligations never axioms; axiom hygiene preserved (published inputs only, only
  in `GQ2/Foundations/Axioms.lean`); results land on a separate branch so `master` stays ℚ₂.
- 2026-07-28 (orchestrator): **per-lane worktrees** chosen over the roe campaign's single
  shared worktree — the shared-index races documented on the roe board disappear, and lane
  merges are trivial because file ownership is disjoint.
- 2026-07-28 (orchestrator): architecture decisions A1 (reflected `PWord` backbone), A2
  (two-sided SD-n — the recon showed the current induction pins `G_ℚ₂` as the second slot),
  A3 (MC via the presented-group D_R pattern; per-core Demushkin-classification hypotheses as
  `def`s, owner gate G-Lab), A4 (LG-K rebase strategy; try-derive general Euler char via
  Shapiro before proposing an axiom). Details + rationale in plan §3.
- 2026-07-28 (orchestrator): recon surveys for all four wave-1 lanes committed under
  `recon/` — SD1/MC1/LG1 design tickets start from these instead of from scratch.
- **2026-07-29 (owner): CAMPAIGN HELD AT NEW GATE G-1.** A presentation **simplification
  campaign** now runs first, in the repo `~/claude/general_2adic` (its `BOARD.md`; plan =
  `dyadic-presentation-simplification-campaign.md`, setup commit `95f5880`): search, compare,
  and certify simpler `L/M_α/N_α` words (single AST, exact boundary/jet certificate gates,
  Sage + Magma independent evaluators, Pareto selection) before the words are frozen for Lean.
  Consequences here: word-dependent lanes (WW, WN0/WM0/WNP/WMP/WL, AS) blocked until that
  campaign's R5 (= our G-1); SD lane additionally deferred by its §12.1; F2's `PWord` design
  must stay aligned with that campaign's AST (same constructor set — its §5 list extends ours
  with `OrbitNorm`/`Shadow`/`HyperbolicHandles`/`Auxiliary` blocks; F2's dispatch prompt must
  read its `words/ast.py` first). Word-independent lanes (LG, MC, F3, AX memos) remain valid;
  owner may release them to run in parallel — MC caveat: valid only while candidate words
  specialize to the standard cores up to certified Nielsen/Tietze moves (that campaign's
  amendment 6 mirrors this). Its Lean deliverables (orbit-norm/𝓔-block/shadow/Tietze generic
  lemmas) land on this branch under `GQ2/Dyadic/Word/Blocks.lean` etc. via ticket S1.9 there.
- **Open at G0 (owner):** approve plan + board; confirm the AX lane list (plan §4); express a
  G-Lab timing preference (the per-core hypothesis route lets all other lanes proceed
  regardless); flag any model-budget constraints (board defaults fable to the hard seams only).
  **G0 now sits behind G-1** except for any word-independent lanes the owner releases early.
- **2026-07-29 (owner): word-independent lanes RELEASED** (in parallel with the simplification
  campaign): F1, MC1, LG1, AX1/AX3/AX5 dispatched. Wave-1 protocol refinements: (a) `GQ2.lean`
  is orchestrator-only for now — workers do NOT add import lines; the orchestrator adds them at
  merge (avoids cross-branch conflicts); (b) wave-1 Lean tickets typecheck their new leaf files
  via `cd ~/claude/gq2-lean && lake env lean <abs-path-to-file>` against the main checkout's
  built environment — no `lake build` / no `lake exe cache get` in lane worktrees yet; full
  library builds happen at wave boundaries; (c) AX memo tickets share worktree
  `~/claude/gq2-dyadic-ax` (branch `dyadic-ax`), committing strictly path-limited single files
  (retry politely on `index.lock`); MC1/LG1 get their lane worktrees (`dyadic-mc`, `dyadic-lg`);
  F1 in `dyadic-f`; S1.9 (simplification ticket landing here) in `dyadic-ww`.
- 2026-07-29 (orchestrator, F1 merge notes): F1 landed (see row). Two F1 discoveries logged:
  (i) **draft §7.3's ℚ₂(√10) word has B = x₁, i.e. p = 0, i.e. ε = false** — both ε values
  occur on the Mpc row (WMP must handle both; the packet's √-10 is ε = true); (ii) η lives as
  `ℤ_[2]ˣ` with `etaUnit r η : (ZMod (2^r))ˣ` as the λ(u)-comparison hook — F4 needs one
  Units↔Multiplicative adapter against draft §10.2's `Multiplicative (ZMod (2^r))` spelling.
  G1 status: F1 half of the API freeze is in; F2 dispatches after simp-S1.3 lands (its PWord
  mirrors the now-frozen S1.1 grammar + S1.3's specialization semantics). F6 dispatched
  (lane F worktree, sequential). `check_axioms.sh` green on the merged branch (census 9;
  check 5 skipped — library not built here; full build deferred to wave boundary as logged).
- 2026-07-29 (orchestrator, AX5 outcome): **projectivity needs NO axiom** — verdict PROVABLE
  (memo `docs/dyadic/ax5-proposal.md`; 922-ln spike typechecks std-3). Decisions: (i) the
  **in-place hypothesis swap in `RegularSummand/{Trace,Involution}.lean` is APPROVED** per
  plan A6 (memo §4.2 edit list; name-preserving q=2 wrappers; byte-identical capstone prints
  verified at the wave-boundary full build) — fallback duplication rejected (~900 dup lines);
  (ii) ticket **PJ1** dispatched (worktree `gq2-dyadic-pj`) to land it; (iii) leaf ownership:
  the finite-image tame leaves live with PJ1; F3 keeps the profinite `T_q` side; (iv) **LG
  lane note**: `LocalKummer.lean:382/409` (`odd_orderOf_tameInertia`, `tameInertia_normal`)
  hard-code q=2 and need the same two general-q leaves — LG4 should consume PJ1's; (v) packet
  §12 over-attribution recorded: `InflationVanishes` is coprime-averaging, not projectivity —
  LG4 scope trimmed accordingly; (vi) memo's literature citations are attribution-only and
  marked UNVERIFIED (nothing enters the trust boundary).

- 2026-07-29 (orchestrator, LG1 outcomes — `docs/dyadic/lg-design.md`): **AX2 closed, not
  needed** (Euler char derivable from B7; LG2a dispatched). Decisions: 13/13 **clone** into
  `GQ2/Dyadic/LocalGauss/` (in-place is A6-incompatible); retype surface corrected to
  **≈9.2k lines** (6 files the recon survey missed) — **LG4 splits into 4a/4b at dispatch**;
  **LG3 proof-route deviation flagged for owner at G2**: `(−1)^n` via the `arf_eq_of_free`
  engine (`s := n`; field-linearity replaces the ℚ₂ Schur transfer, which is FALSE at n ≥ 2
  since H¹ ≅ Vⁿ is not simple) — packet Prop 6.8's Hermitian diagonalization kept only as the
  n = 1 regression; statement (Thm 6.15) unchanged. **F3 acceptance grows**: export
  `gen_tq_quotient` + packet Lem 3.1 finite-image forms. **AX3 consumers grow**: LG4's
  involution-`hunram` discharge. **SD1/AS1 note**: drop `eulerChar` from `DyadicLocalInput`
  (derived, not an input). AX6 re-confirmed unnecessary.
- 2026-07-29 (orchestrator, AX1 outcomes — `docs/dyadic/ax1-proposal.md`): **AX1 is also not
  an axiom** — provable from B1 (profinite Nielsen–Schreier via
  `Subgroup.exists_finset_card_le_mul`), scratch-verified printing std-3 + B1 only.
  **Route D adopted** (neither replace nor add; census 9→9; B1, comparator-config,
  formalization.yaml all untouched; G-AX no-op) — fallback REPLACE route recorded in the memo
  if the owner prefers a citation over a derivation; revisit at G3. Ticket **FG1** dispatched
  (worktree `gq2-dyadic-fg`). Consumer discoveries: SD-n's two-sided record makes the G_K
  `tfg` a record field (the interim binder is the permanent shape under Route D); the LG lane
  never consumes AX1. Axiom-lane scoreboard: **AX1/AX2/AX5 all eliminated as axioms today**;
  the general-K trust-base growth is so far ZERO, pending AX3/AX4.
- 2026-07-29 (orchestrator, AX3 outcomes — `docs/dyadic/ax3-proposal.md`): the irreducible
  core is **one axiom** (`markedRecipAt`; extend-don't-replace; B5/B3c untouched; B10's
  K-analog delegated to AX4 parametrized by `MarkedRecip`). **Census flip is owner-gated
  (G-AX) and NOT executed** — consumers (F4, MC5, boundary lane) use the memo's interim
  hypothesis binders until sign-off. Owner questions Q1–Q7 pending, incl. the
  `HasEqualNormValueGroups` import-cycle fix and who lands `MarkedRecipBundle.lean`.
  ⚠ Risk adopted as a gate: all five quadratic instances have r ≤ 1 (λ-sign-blind) — the
  synthetic r = 2 mock-bundle regression (memo §7 R2) is REQUIRED before any consumer
  merges. AX4 dispatched (ax worktree, now free).
- 2026-07-29 (orchestrator, AX4 outcomes — `docs/dyadic/ax4-proposal.md`): axiom-lane final
  shape: **exactly two proposed axioms** (AX3 `markedRecipAt`, AX4 `orientedTameQuotientAt`),
  both owner-gated at G-AX, flip order AX3 → AX4. Adopted into specs: (i) **F3 must split**
  (AX4 Q4): `Tq`/`nuTq`/`tame_relation_q` go in a leaf file importable by `Axioms.lean`
  (`GQ2/Dyadic/TameQuotientK.lean`-style; BoundaryFrame-vs-Prop32 precedent), boundary
  theorems separate; F3 exports `gen_tq_quotient`, `o2_Tq_eq_bot`, `tq_two_equiv` — F3's
  dispatch prompt updated accordingly; (ii) the `DyadicUnitFiltration` parametrization is
  the adopted statement shape (supplies canonical `FF.π`, also kills AX3's R8 vacuity mode);
  (iii) `ℚ₂(√5)` q_K = 4 regression mandated wherever T_q enters; (iv) W_K = W∩G_K
  compatibility clause OMITTED (no consumer). PJ1's build makes `gq2-dyadic-pj` the standing
  BUILT worktree — wave-boundary audits (check-5) run there after syncing.

- **2026-07-29 (orchestrator, WAVE INTERRUPTED — HANDOFF WRITTEN):** the Fable 5 monthly spend
  limit killed four in-flight fable-tier agents (MC1, F2 here; S1.4, S1.5 on the simplification
  side). Everything landed is merged and verified: full build 3386 jobs, check_axioms check-5
  RAN clean (5 capstones, 3 twin pairs, census 9), check_dyadic green. **Handoff document:
  `~/claude/handoffs/gq2-dyadic-campaigns-2026-07-29.md`** — re-dispatch prompts for the four
  killed tickets (on **opus**), the full decision record, open gates (G-AX, G-Lab, G2, R1), and
  the trap list. Merged worktrees pruned; lane worktrees retained.
- 2026-07-29 (orchestrator, RESUMED session): **wave A re-dispatched on opus** — MC1
  (`gq2-dyadic-mc`) and F2 (`gq2-dyadic-ww`), lane branches synced to dyadic (0ed4244) first.
  F2 protocol adaptation: because Syntax/Eval chain, the leaf-typecheck rule is replaced for
  this ticket by `lake exe cache get` + `lake build GQ2.Dyadic.Word.{Syntax,Eval}` in the ww
  worktree (builds only the import closure). pj audit worktree synced + build pre-warmed.
  S1.4/S1.5/S1.7 re-dispatched on the simplification board simultaneously.
- 2026-07-29 (orchestrator, MC1 outcomes — `docs/dyadic/mc-design.md`, memo governs MC2–MC5):
  (i) **correction adopted**: the "M and N have different torsion" premise (this board's MC1
  spec + recon/mc-survey) is FALSE — all three cores have q = 2, torsion ℤ/2; the real
  separators are `im χ` (ℤ/2×ℤ₂ vs procyclic) and the torsion generator's position (memo
  §7.1; spec text left as history, memo governs). (ii) **Lifting is three strata** (memo §5):
  S1 elementary Nielsen (constructed+verified), S2 unit scalings — dischargeable from
  existing B8 (`GQ2/PeripheralAction.lean:72-92`, applies on the abstract free pro-2 rank-2
  group via nested three-term peripheral factorizations), S3 "mixing" transvections — in the
  stabilizer, needed for ν-correction, degree-≥3 Labute content unreachable by Nielsen/B8 →
  proposed per-core binders `MMixHypothesis`/`NMixHypothesis` (BLab pattern, NEVER axioms) +
  an MC3a direct-proof spike. **Owner-gated: binder acceptance + spike authorization (memo
  Q1), B8-dependence vs binding the scalings (Q2).** (iii) ⚠ **Gap (memo §7.2, owner Q4)**:
  the compact-M marked change of variables is MISSING from the vendored sources (procyclic
  recipe degenerates at r = 0) — F4/MC5/WM0 consumers blocked on it; possibly a packet-author
  question. (iv) **Packet §14 criterion flag (memo §7.3)**: the stated Smith–Witt completion
  criterion implicitly assumes the S3 stratum — flagged, not silently resolved. (v) G-Lab
  sheet (memo §8) rec: **stay parametrized** (binders; a rank-four levelwise campaign ≈6–8k
  ln/core shouldn't start before G-1) — DECISION STAYS WITH OWNER. (vi) MC2 adopted specs:
  cup Gram is NOT `decide`-able (2^α defeats drRelZ_drCC) — budget an exponent/normal-form
  lemma (reusable by all five branch words); NO Hensel-root work needed (orientations closed
  form); add "free pro-2 rank 2" + generic B8-transport lemmas as MC2 assets. (vii) MC5:
  handles enlarge the stabilizer with new S3-type directions (not a formality). (viii) AX
  lane: any future "rank-four peripheral action" axiom proposal is CLOSED in favor of B8.
  (ix) SD confirmation: rank enters only as demushkinRank = n+2, card_H1 = 2^{n+2}.
- **2026-07-29 (orchestrator): GATE G1 OPEN** — API review of F1 (reviewed at its merge,
  independently re-typechecked) + F2 (report + spot-check of committed decls + full
  wave-boundary audit green: 3388 jobs, census 9, check-5 with 5 capstones/3 twin pairs,
  check_dyadic green). F2 outcomes adopted: (i) **z2pow semantics RATIFIED at G1**:
  `eval (z2pow u z) = eval u ^ᶻ padicOmega2 z` — the ω₂-twisted total extension; on pro-2
  elements it IS the honest ℤ₂-power; consumers must remember the general case is the
  2-primary truncation (a bare ℤ₂-power is undefined on non-pro-2 elements). (ii) Both F2
  files are module-style; module-rule audit done (Parameters/Zhat/Blocks/GammaA all
  module-style). (iii) Notes for WW lanes: `padicOmega2` additivity is true-but-unproved (add
  when x^{η̂₁+η̂₂} algebra is needed); there is NO general `Zhat → ZMod N` residue map —
  `ResolvedAt` takes per-node resolution hypotheses; ω₂-only words (ALL current campaign
  words) need no hypothesis via `evalFin`. (iv) Toolchain traps recorded: `open scoped
  Classical in` does not reach structural-recursion equation lemmas (v4.31.0-rc2) — use
  explicit `@ite _ _ (Classical.propDecidable _)` + expose `_omega2`/`_of_ne` equations;
  top-level pattern-match proofs over `PWord` get inconsistently pre-reduced goals — use
  tactic `induction w with`. (v) GammaA's per-letter bridges are `private` — re-derived, not
  reused (the F2 stress theorems restate them). (vi) `omega2Exp_eight` now exists in two
  places (F2 + Roe/Words) — flagged for mechanical dedup into `GQ2/Omega2.lean` by whichever
  lane first needs both. **G1 consequence: MC2/LG2 (and later SD2/WW1 when their gates clear)
  may start.** F3/F4 dispatched with the AX4-split and mock-bundle mandates (see rows).
- 2026-07-29 (orchestrator, wave-B dispatch): **S1.6** (simp board), **F3** (lane f;
  TameQuotientK leaf + TameBoundary split per AX4 Q4; #Hom(T_q,ℤ/3) √5 regression mandated),
  **F4** (NEW branch `dyadic-f4` in the ww worktree to reuse its built closure; synthetic
  r = 2 mock-bundle regression mandated as an AX3 consumer; compact-M CoV gap warning from
  MC1 §7.2 attached), **LG2** (lane lg per lg-design clone list), **MC2** (lane mc; MC1 memo
  governs incl. corrected frames + not-decide-able cup Gram) — all opus. Lean tickets use the
  F2 build protocol (cache get + `lake build <own modules>` in-worktree).
- 2026-07-29 (orchestrator, F4 outcomes): audit green post-merge (3389 jobs, census 9,
  check-5 + check_dyadic incl. D3 sign-row guard). Adopted findings: (i) **packet Prop. 8.1
  implicitly assumes r ≥ 1** — at r = 0 the target ℤ/2⁰ is trivial ("η even" free, conclusion
  fails); NOT a defect, it IS the compact row: excluded-branch statements carry `1 ≤ d.r`,
  dichotomy `level_zero_or_not_even_eta` states the alternative — wave-2 word lanes cite the
  dichotomy, not raw Prop 8.1. (ii) `MarkedSplitting` deliberately assumes NO algebraic
  generation (⟨u⟩ is a topological closure in the model; `Subgroup.closure = ⊤` would be
  FALSE) — AX3's derived layer supplies the two-coset covering from continuity into the
  finite target, one line; consumers must NOT add a closure hypothesis. (iii) ε is inherently
  sign-blind at every level (λ(−1) is 2-torsion; 2 = −2 in ℤ/4) — the R2 mock regression pins
  η/γ signs only; absence of an ε sign test is NOT a gap. (iv) The MarkedRecip field clause
  landed as the `unramified_of_even` binder with the AX3 §2.2 instantiation recorded in the
  module docstring; simulated MC5/boundary consumer composition type-checked in scratch.
- 2026-07-29 (orchestrator, LG2 outcomes): audit green post-merge (3391 jobs, census 9).
  Adopted: (i) **(H3) isotropy-splice deferral to LG4 APPROVED** — `DeepDualityK.lean:317-578`
  is deep-unit content over `IntermediateField ℚ_[2] ℚ̄₂` whose retype needs the N_K-anchoring
  convention that is `DeepPackage.lean`'s design decision; LG2 supplied `H1anchor`/`H2anchor`
  instead (memo's own mitigation); LG4a/4b dispatch prompts MUST include this splice in
  scope. (ii) ⚠ **NEW LANE-WIDE TRAP** (generalizes the LG2a instance trap): at Γ = G_ℚ₂ the
  𝔽₂/μ₂ actions are trivial DEFINITIONALLY and ℚ₂ proofs silently end in `rfl` on that; at
  general Γ triviality is a THEOREM — cloning any proof ending in `rfl`/`fun _ _ => rfl`
  around a `ZMod 2`/`MuN 2` smul requires inserting `smul_zmodTwo`/`smul_muTwo` (provable for
  ANY group, no binder needed). (iii) `polarBihom_equivariant`/`polar_smul_smul` lose their
  unused `C` binder in the retype — ℚ₂-style `(C := …)` call sites need adjusting. (iv)
  `ker_isLocalDualizingGroup` GENERALIZED (not clone): campaign needs `N_K ≤ G_K ≤ G_ℚ₂`, ℚ₂
  version covered only `ker ρ ≤ G_ℚ₂`; transitivity via `isLocalDualizingGroup_of_openEmbedding`
  (`Subgroup.index_map`, `ker j = ⊥`). (v) LG3 confirmed unaffected in route (arf_eq_of_free
  `s := n` stands); LG3 must additionally clone the `cCoeff`/`cActionH1` block against
  `GQ2.Dyadic.Q0loc` (lives in UnramifiedModel.lean = LG3's file). (vi) Dependency blocks
  cloned INSIDE the two files (RepIndependence trio, LocalKummer conj block) — not separately
  assigned by the memo; RepIndependence.kappa0_cocycle/innerConj/etaS + all of OrbitData
  consumed verbatim (ambient-free already).
- 2026-07-29 (orchestrator, F3 outcomes): audit green (3394 jobs with MC2, census 9). Adopted:
  (i) ⚠ **general-q center correction (load-bearing)**: Fermat levels have
  `Z(C_{q^{2^k}−1} ⋊ C_{2^k}) ≅ C_{q−1}` — NOT trivial as in the q = 2 proof; argument
  survives because q−1 is odd (landed `fermatQ_central_pow_eq_one`); Prop32's
  `Subsingleton (GFermat 0)` shortcut also vanishes (handled by `uq_pow_val_one`) — anyone
  transcribing Prop32 hits both. (ii) ⚠ **AX4 memo §4 arithmetic corrected before G-AX**:
  memo quoted #Hom(T₄,ℤ/3) = 3 vs #Hom(T₂,ℤ/3) = 1 — those are the INERTIA-SLOT counts; true
  continuous-hom counts are 9 and 3 (free Ẑ-coordinate contributes 3 unconditionally). Both
  separate q = 2 from 4; F3 landed BOTH forms by kernel decide + `hom_count_distinguishes_tq_two_four`;
  orchestrator correction note added to `ax4-proposal.md`. (iii) `o2_Tq_eq_bot` needs only
  `2 ≤ q ∧ Even q` (stated at that generality). (iv) Duplication forced by the split
  (TameQ.odd_order/zpowers_normal + TopGen.* restate PJ1/SectionThree — import-height forced;
  distinct names) — DE-DUP CANDIDATE for a later pass: PJ1's two leaves are Mathlib-only and
  could move into TameQuotientK with Projectivity importing the leaf. (v) Prop 3.4(2) landed
  in UNIVERSAL-PROPERTY form (iff: a pro-2 marking extends over Γ_R iff it kills τ and
  pro2 R) — deliberate while words are unfrozen; constructing D_P later is a formality;
  `KillsWild` is the semantic Gate-B admissibility interface (`killsWild_iff_killWild`
  bridges to F2's syntactic operator). (vi) For AX-lane/G-AX: **nothing blocks the flip from
  F3's side**. (vii) For LG3: `gen_tq_quotient` ready; bonus exports
  `zpowHat_omega2_eq_self_of_isProP`, `map_eq_one_of_nuTq_eq_one`. (viii) For SD1: degree-one
  type field is `Tq (qOf K FF)`; refl-bridge means the ℚ₂ record instantiation needs no
  transport.
- 2026-07-29 (orchestrator, MC2 outcomes): adopted: (i) rank via handle count `h`
  (`coreRank h = 4 + 2h`) instead of bare n — `Fin (n+2)` literal wrap at n < 2 is real;
  MC3–MC5 prompts use `h`. (ii) `ν` targets `Multiplicative ℤ_[2]` (memo's Ztwo isomorphic);
  `nuM` needs `1 ≤ α` (genuinely: at α = 0 the abelianized relation has no solution with
  ν(C₀) = 1). (iii) Orientation iffs landed UNCONDITIONALLY (stronger than memo skeleton).
  (iv) Frame-existence `Nonempty` theorems (phiEquiv route, ≈300 ln/core) deferred — MC3/MC4
  consume frames as hypotheses per the BDecomposition precedent; ACCEPTED. (v) ⚠ **infra gap
  (new ticket needed before MC5/branch-word cohomology)**: `DRWordCoh`'s `relZ`/`obsH2` layer
  is hard-wired to `drWord`/`Fin 3` — a relator-generic `obsH2` port (~900 ln) is a separate
  ticket; §6's `IsCupCocycle` layer already supplies the mathematical content it would
  consume. Related: `GQ2/WordCoh2.lean` is non-module (why DRWordCoh re-derived it) —
  hoisting `TwoCocycle`/`CentExt`/`comap`/`projExt` into a module file would let rank-generic
  `relZ` be written once over the `GQ2/Dyadic/Word/` layer. (vi) ⚠ **stale-comment find,
  owner-relevant**: `GQ2/Orientation.lean:48` justifies the `chiTwo` axiom by "avoids an
  `IsProP 2 ℤ₂ˣ` development" — that development NOW EXISTS
  (`GQ2/ZtwoPowering.lean:559`); a census-9 → 8 elimination spike is plausible; OWNER CALL
  (G-AX territory), not executed.
- 2026-07-29 (orchestrator, wave-C dispatch): **LG3** (opus, lg worktree, plain-import per
  memo §5; prompt carries σ-twist + smul + instance traps, F3's `[DiscreteTopology H]` note,
  AX3/AX4 binder rule) and **LG4a** (opus, ww worktree on NEW branch `dyadic-lg4a`).
  **LG4a/LG4b FILE SPLIT FIXED (orchestrator)**: LG4a owns `LocalGauss/DeepPackage.lean` =
  deep-unit package + InflationVanishes/FamiliesExtend twins (coprime-averaging discharge,
  PJ1 general-q leaves for LocalKummer:382/409) + **the (H3) isotropy splice deferred by
  LG2** (LG4a fixes the N_K-anchoring convention, documented in-file) + vanish lane through
  `lemma_6_17_vanish_final_K`, exports staged for the join; LG4b (later) owns
  `Ramified.lean` = dim lane + `card_Q0loc_zero_eq_of_dim_of_vanish_K` + endpoint
  `prop_6_18_ramified_K`, imports LG4a. LG4a instructed to stop-and-report at any resisting
  seam rather than grind (fable-tier ticket run on opus per the night's model policy).
  **MC3/MC4/MC5 NOT dispatched** — entangled with open owner questions (MC1 memo Q1–Q3;
  binder acceptance + B8 usage + quantification) and G-Lab; morning items. S1.10 dispatched
  on the simp board simultaneously.
- 2026-07-29 (orchestrator, LG4a outcomes + lane restructure): audit green 3396, census 9.
  Adopted: (i) **the LG4a anchoring convention is BINDING for LG4b/LG4c/LG5** (element-map
  through `anc : Γ →ₜ* GalQ2`; `GalQ2` local notation in anchor types — `AbsGalQ2`'s
  plain-def instances defeat synthesis; call sites pass AbsGalQ2 data by defeq); the memo's
  nested-subtype risk (§7 risk 2) is DISSOLVED — LG2's `H1anchor`/`H1congrGroup` remain
  available but unused by this lane. (ii) **LG4 split into LG4a/LG4b/LG4c by file** (rows
  above): LG4a's two named seams become LG4b's FamiliesExtendK discharge + dim lane and
  LG4c's §7.1 scope-block retype; both dispatched in parallel (disjoint files; LG4b takes
  the vanish-final as a `Q0locVanishesOnDeep`-shaped binder so it does not wait). (iii)
  σ-twist trap did NOT fire in LG4a's lane (no sigmaFun sections) but the smul trap fired
  twice more — `simp only` where `rw` under-fires on double smul occurrences
  (`cupFun_mem_B2_of_kside` precedent). (iv) `hvanish_cup_ker_K` threads `(k, hker)` — the
  `ResidueLift.splitField` CONSTRUCTION belongs to the dim lane (LG4b decides retype vs
  thread). (v) AX5's attribution correction fully honored downstream (no projectivity in
  InflationVanishesK; q=2-typed LocalKummer lemmas unreferenced). (vi) LG4a's defensive
  `_dp`-suffixed helpers (`h1_add_self_dp` etc.) carry dedup notes — LG4c's retype is the
  permanent home for the `eq_of_H1ofFun_eq` family.
- 2026-07-29 (orchestrator, LG4c outcomes): audit green 3400, census 9. Adopted for LG5:
  (i) ⚠ **NEW smul-trap variant at the reducer interface**: `cup11Fun ∘ mul` is
  definitionally the pointwise product ONLY at G_ℚ₂; the ℚ₂ assembly feeds `innerf` to
  `cup11_mem_Z2`/`hvanish_cup_ker` by bare `exact`, which BREAKS at general Γ — use LG4c's
  `hcupval`/`hsqeq`/`hfreeeq` bridges wherever ℚ₂ code identifies `cup11Fun` with a product.
  (ii) **LG3↔LG4c interface adapter needed** (mechanical, unwritten): LG4c's endpoint takes
  the abstract tame pair `(sg,t,f,hf,hgen,hrel)`, LG3's takes a marking — adapter via
  `sg := c (tqSigma q)` etc. + F3's Tq generation; LG5 owns it (endpoint n=1 pin waits on
  it; deepPartK pins already exist in LG4a §9). (iii) `hancinj` is a genuinely new
  hypothesis vs LG4a's convention (ancSubgroup-hker is strictly weaker than the Γ-side
  membership test the involution carrier needs) — bridge `mem_ker_iff_anc_mem`; both
  campaign instantiations discharge it trivially (`U.subtype`/`id`). (iv) New
  `regular_isometric_embedding_orbit_pow` (general q_K) on PJ1's leaves; ~20 lines
  re-proved because RegularIsometry helpers are `private` — DE-PRIVATIZE upstream candidate.
  (v) `Q0loc_datum_indep_K` docstring pins the tame instantiation to
  `tame_*_pow` — never the q=2-hardcoded LocalKummer pair. (vi) Three-copy
  `eq_of_H1ofFun_eq` dedup map recorded in InvolutionSpliceK docstring; LG5 may collapse
  `_dp` onto `_K` once the import graph allows.
- **2026-07-29 (owner, in session): GATE G-AX ANSWERED — both axioms APPROVED.** AX3 answers:
  Q1 one axiom (§6 shape); Q2 omit the a_K norm-residue clause; Q3 move the
  `HasEqualNormValueGroups` def (alias kept — the one approved edit to frozen Interfaces);
  Q4 field-language spelling (`¬ HasEqualNormValueGroups`) for AS5; Q5 small ticket AX3-b for
  `MarkedRecipBundle.lean`; Q6 "No second axiom sounds good" — read as CONFIRMING §6's
  extend-not-replace (B5 untouched; §6's own "no second axiom is warranted" phrasing; flagged
  to owner for correction if misread); Q7 citation targets approved (Serre LF XI §3, NSW I §5
  + VII §7.1) — **PDF verification NOT performed; UNVERIFIED annotations stay** (house
  "verified against PDFs" line must not be written). AX4 answers: Q1 one separate axiom
  (census → 11); Q2 DyadicUnitFiltration parametrization confirmed (the soundness-critical
  choice); Q3 self-contained W (3 clauses) + omit the W∩G_K compatibility — fine for now;
  Q4 F3 split ratified (already executed); Q5 new ticket AX4-b (the OrientedTameQuotientK
  structure home; F3 already landed the Tq leaf + q-regressions, so AX4-b = structure +
  derived layer only); Q6 NO Ẑ-valued tame character clause for now (owner: "fix it later if
  there is an issue" — recorded as a potential future statement change under G-AX rules);
  Q7 citations accepted without detail-check (same UNVERIFIED discipline); Q8 moot (axiom
  route chosen). **Execution order (memo §6 checklist): AX3-b bundle file (dispatched, ww
  worktree branch dyadic-ax3b) → orchestrator atomic AX3 flip commit (census 9 → 10, B5-K
  row) → AX4-b (structure file) → orchestrator AX4 flip (census 10 → 11, B10-K row); check-5
  byte-identical ℚ₂ capstone prints is a gate at each flip.**
- **2026-08-01 (owner + orchestrator): THIRD INTERRUPTION → MODEL POLICY CHANGED — FABLE IS
  EXHAUSTED FOR THE WEEK; ALL TICKETS RUN ON OPUS.** A session-limit hit killed the three
  in-flight fable tickets (WM0-c, WNP-b, WMP-b); the owner then reported the weekly fable
  quota gone and switched orchestration to opus. **The board's `fable` model column is
  hereby aspirational for the rest of the week — read it as "hard seam", dispatch on
  opus** (this is the same rider the campaign adopted during the 2026-07-29 and 07-30
  credit incidents; it has not cost a ticket yet). Salvage at the kill: **WNP-b's six
  commits AND its 59 uncommitted lines survived and built green** (the continuation
  worker banked them first); WM0-c and WMP-b had written nothing (killed in their reading
  passes) and were restarted clean. Re-dispatched on opus, all four in parallel: **WNP-b**
  (continuation, mc), **WMP-b** (restart, ob), **WM0-c** (restart, wn0), **WL-c** (new,
  lg, branch `dyadic-wlc`, c2-before-c1 per WL-recon Q3). WL-c's brief carries a
  **stale-warning correction**: WL-b told it that the Words-namespace collision blocked
  importing `Certificates/N0Fox.lean`/`N0.lean` — that break is FIXED (see the previous
  entry), the root build is green with every Words/* and Certificates/* file co-imported,
  so WL-c reuses WN0-c's toolkit instead of re-deriving ~350 lines.
- **2026-08-01 (orchestrator, CB-RES — ω₂ HAS NO INTEGER REPRESENTATIVE, AND THAT IS THE
  SEAM):** merged. CB-RES was sent to discharge the last count-lane item and returned a
  proved negative that locates the real problem: **no integer resolves ω₂ in a free
  profinite group**, so the word lane's integer-resolved relators are different elements of
  `F` from the intrinsic ones — refuted at all five frozen families, with the refuting
  characters landing in 2-groups (so CB-MP's restriction does not rescue it) and the
  word-lane relator shown nontrivial **in `Γ_R` itself**. **Orchestrator decision (riding,
  flagged for override): take CB-RES's own third option — the target-resolved
  reformulation**, dispatched as CB-TR. The reasoning is mathematical rather than
  preferential: ω₂ is a profinite exponent that acts as a *different* integer in each finite
  quotient, so pinning one global integer is simply wrong (CB-RES measured that the frozen
  `e = 3` is `omega2Exp 6`, correct only at targets of exponent dividing 6 — adequate for the
  mod-2 Stokes work, not universal), and CB-1's clause (iii) **already quantifies over finite
  targets**, so the resolver can be chosen per target. The two alternatives were rejected on
  the merits: running the count at `Γ_{resolveWord e R}` would make the campaign's theorem
  about a **provably different group** (CB-RES's §7/§8), and forcing the intrinsic relator
  through the word lane would reach the entire certificate stack. CB-RES's refutation stays
  as the permanent record of why the interface has the shape it will have.
- **2026-08-01 (orchestrator, CB-W — THE CAMPAIGN'S LEAN `GammaR` IS NOT THE CAMPAIGN'S
  GROUP):** merged. CB-W was sent to *prove* `hwild`; it **refuted** it for all five branches
  and stopped at exactly the right boundary — no touch to `GammaR`, no axiom (which would
  have made the candidate layer inconsistent rather than merely unproved). Its argument is
  about the definition, not the words: a two-relator presentation leaves one 𝔽₃-linear
  condition on ≥ 2 wild unknowns, so a wild letter always survives into ℤ/3.
  **Orchestrator reclassification — CB-W called this a G-AX/definitional matter; it is a
  BUG**, and the campaign predicted it in writing on 2026-07-29: the simplification campaign
  doc §3 says *"A candidate presentation always means an admissible presentation … A bare
  two-relator profinite quotient is not interchangeable with this definition"*, and
  `plan.md` §1 carries the pro-2 closure clause **inside** the displayed definition of Γ_R.
  `TameBoundary.lean:333` implements the bare quotient. So F3's `GammaR` never was the
  campaign's group, every downstream layer inherited that, and CB-W's refutation is the
  expected consequence rather than a surprise. **GR1 dispatched** to redefine `GammaR` as
  the admissible limit (`GammaA.lean:211`'s `N_A` is the frozen precedent) and discharge
  `hwild` through the bridge CB-W built for exactly this purpose. Two things CB-W got right
  that are worth keeping: its `not_hwild` stays as the record of *why* the definition
  changed (it remains true of the bare presentation), and its §7 criterion is the reusable
  statement of what admissibility buys. Its one stale claim — that `Count/Routine.lean` does
  not compile — was true on its branch and is **not** true at head (the branch predated the
  orchestrator's `open TameSpec` merge fix; re-verified `routine_exit=0`).
- **2026-08-01 (orchestrator, CB-S GREEN — the lane proceeds, and its risk moved):** merged.
  The spike did its job in both directions: it cleared the gate AND corrected the memo that
  sent it. **Five memo-vs-code contradictions adopted, CB-S's landed code winning each**:
  (1) §3.2's "clause 2 survivable only if `SN` is threaded from the start" is FALSE — the
  generic clause is `SN`-free, valued in the presentation deficiency, and §3.3's spike
  instruction would have produced a WORSE statement; (2) the `#A^{|ι|}/#H⁰` shape is wrong —
  the denominator is `#A^{|ρ|}`, the RELATOR count, and `H⁰` does not enter the count at all;
  (3) §1.5 UNDERSTATES its own instruction — in the ℚ₂ dévissage clause 2 carries no
  information (`isSelfDualW_iff_R` literally discards it and re-derives it by rank-nullity),
  so the seam is clause 1 + clause 3 and "one theorem, not eleven" is MORE right than the
  memo claimed; (4) the delta table's "`hZcard` residue: none" is incomplete — it also needs
  `#(A^∨)^C = 1`, supplied by the record's own binders through a generic word-free leaf that
  currently sits in the ℚ₂ assembly file `GQ2/DualityAssembly.lean` (**hoist assigned to
  CB-4**, or to CB-1 if the import height hurts); (5) file-map correction — the memo assigns
  CB-S to `Bridge/Spike.lean`, the lane is using `Count/`. **Ticket sizes move: CB-1 −300,
  CB-4 −400, CB-3 modest, net ~700 lines cheaper; and the lane's largest sizing risk is no
  longer clause 2 — it is CB-1's comparison isomorphism**, now dispatched with the reduced
  scope. CB-P, CB-0 and AS1-b continue in parallel.
- **2026-08-01 (orchestrator, F3b — the Gate-B repair, and the packet's Thm 3.5 gets its
  first word-side instance):** merged; root build green at 3478. The repair is what was
  asked, but the finding underneath is larger than the ticket: **through `KillsWild`, eq.
  (27) joint surjectivity was unreachable at EVERY frozen branch word, so the packet's Thm
  3.5 had no word-side instance in the campaign at all** — F3b rebuilt the whole Prop
  3.4/Thm 3.5 chain over the satisfiable predicate and instantiated it at compact N. Also
  adopted: ⚠ **the WN0-a ruling's remedy was itself wrong** — `killsWild_of_tau` is not a
  usable route either (its hypothesis is refuted by the same ZMod-8 witness); the five
  lanes' copies are dead weight and their docstrings should point at
  `TameSpec.tameSpecializes_of_tau*` (queued for the lanes' next owners, not forced now);
  and `killsWild_of_odd` never existed under that name. **Two Gate-B routes are needed, not
  one** (compact-M and Mpc state death as an implication, since their kill-wild value
  carries an 𝓔-block / orbit norm that collapses only once `τ^{ω₂} = 1`). **AS1-b
  dispatched** to delete AS1's §2b stopgap and take F3b's entry points.
- **2026-08-01 (orchestrator, CB1 — THE FOURTH RESTRUCTURING, AND IT IS AFFORDABLE):**
  memo merged. Riding decisions on its seven owner questions (flagged — owner may override
  any): **Q1 spike first = YES** (CB-S dispatched; its verdict gates CB-1..CB-6 — the
  campaign has never committed 10k lines without a measured spike and will not start now);
  **Q2 generic-first = YES**, contingent on CB-S (the 36k-vs-13k measurement makes this the
  only defensible call); **Q3 `hsimp` = thread as an explicit hypothesis now, discharge
  opportunistically at N0, NEVER an axiom** (it is carried identically by all five closers
  and discharged by none — it is now a visible tenth residual); **Q4 the `NpcJet ↔ WordCoh`
  bridge = open as WW6** (a silent blocker: it has NO ticket anywhere and gates Mpc's
  `determinant` through two dependency levels — queued, not yet dispatched); **Q5 L's
  missing `HessianCertificate` = restate against `qDouble`** (its endpoint is not a
  `plusFormD`, and WL-c said so); **Q6 lane/worktree split = orchestrator's** (Count/ under
  the existing worktrees, one file per ticket, no new lane worktree); **Q7 ASK = adjacent,
  keep separate** — but if CB-S is green, ASK shrinks too. Board corrections CB1 forced:
  **AS2's dependency row was WRONG** (read "AS1, WN0-c"; now includes CB-P + CB-1 + the
  N0-restricted clause tickets), and **WW3b's "NOT degree-generic" warning — which survived
  only in a closed ticket row — is promoted to the obligation tracker** as the spike's
  explicit target. Three tickets dispatched in parallel: **CB-S** (the gate), **CB-P** and
  **CB-0** (both startable today with no spike dependency, and together they close 8 of
  `WordCertificate`'s 17 fields).
- **2026-08-01 (orchestrator, AS1 — THE ASSEMBLY WORKS, AND IT EXPOSED TWO STRUCTURAL
  BLOCKERS):** merged, import registered. The good news is decisive: packet Thm 1.1 is a
  **three-line assembly** over SD3, and AS1's own file is **std-3 with zero B-axioms**. The
  two blockers reshape what remains, and both were found by shaping the record to the
  *recursion's* clauses rather than to the lanes' outputs — which is the honest choice, and
  is why the theorem stayed an assembly:
  1. ⚠ **`KillsWild` is REFUTED, not mis-shaped.** F3's Gate-B predicate quantifies over
     every profinite group with no τ condition, but any word with an `(x_iτ)^{ω₂}` letter
     kills to `τ^{ω₂}` — nontrivial in `Multiplicative (ZMod 8)`. All five `Words/*` files
     carry landed `not_killsWild` theorems (AS1 verified all five by grep, not from the
     survey). AS1 could not call F3's `tameR` and re-did the construction over the
     satisfiable `TameSpecializes` (= the ledger's `specializeTame R = 1`).
     **F3b dispatched** to make the satisfiable predicate primary, keep the refutations,
     and let AS1's §2b duplication be deleted.
  2. ⚠ **THE CERTIFICATE⇒COUNT BRIDGE HAS NO OWNER — a whole missing lane.** The five
     branch lanes closed at Fox rows, Stokes endpoints, scalar Grams and Hessian
     certificates; `SourceDataN` consumes **counts**. At ℚ₂ that bridge is the entire
     `GQ2/Roe/` stack, and the campaign has five words. **AS2 is blocked behind it.**
     Related, AS1's finding 3: word-level `pro2 R = coreRel` (which all five lanes have)
     does NOT give group-level `Γ_R(2) ≅ D_P`, and the generic bridge is unbuilt (the ℚ₂
     ancestor `Roe.exists_pro2R` is Γ_R-specific and consumes `BLabHypothesis`).
     **CB1 dispatched as a DESIGN MEMO** (the SD1/MC1/NC1 pattern — this is the campaign's
     fourth restructuring-on-measured-evidence, and it gets a memo before any
     implementation): its core question is whether the bridge is one generic theorem over
     the WW evaluators plus five thin instantiations, genuinely per-branch, or mixed — the
     answer sizes the rest of the campaign. It also owns the pro-2 gap's disposition
     (including whether it lands on the G-Lab docket) and the shortest path to unblocking
     the √−2 pilot.
  **AS2–AS5 are NOT dispatched**; they wait on CB1's verdict. Standing residuals no lane
  owns, now consolidated in AS1's record docstrings: `hsimp` (per-simple-module Stokes
  duality — carried by all five closers, discharged by none), WW4 items 3 and 5, the
  gate-F witness, P4's central clause per module, `Mpc.hlinrow` at general (α,r,p,η)
  (closed only at √−10), L having no `HessianCertificate` (its endpoint is `qDouble`, not
  `plusFormD`), and the α-threshold mismatch across layers (Fox 1 ≤ α, Stokes/Hessian
  2 ≤ α, compact-M none).
- **2026-08-01 (orchestrator, WAH — the collision's CAUSE is removed):** merged (14 files,
  +409/−564), `Words/Alphabet.lean` registered. **26 shared declarations replacing 94 copies
  — 68 duplicates deleted — with ZERO statement changes and ZERO renames** (the WWH
  standard held); five lanes −501 ln, `Words/` net −156 with a documented shared home; full
  build green under `pipefail`, all 420 lane decls ⊆ std-3. Four upgrades taken where a
  lane's copy had drifted better (`pro2_prodList` at variable rank — the four
  `Generator (2+2h)` copies and LSq's were ONE theorem twice; `invConj_mul_self` at
  `Type*`; the computable `handlesW`; the majority `@[simp]` forms); **two upgrades
  REJECTED by the consumers-unchanged rule** and reported rather than forced (the
  kill-wild trio at `Type*` fires on module-lift goals and breaks four M0Fox proofs;
  `eval_prodList_append` cannot generalize at all — `PWord.eval` is itself `{G : Type}`).
  **Correctly stayed put**: LSq's whole alphabet (a genuinely different alphabet — six
  different statements, not six proofs of one), `killsWild_of_tau`/`not_killsWild` (same
  shape, five statements, different binder lists), and `rawHandleTail` — **the one move
  that turned non-mechanical was STOPPED** (`.int ((h+1:ℕ):ℤ)` vs `.int (h+1)`:
  propositionally equal, syntactically not, and the gate-A hash pins are `rfl`).
  **The three handle shapes are now documented in one place** (count-0 node: N0/Npc; no
  node at h=0: MCompact/Mpc; no node at n=1: LSq — shapes 2/3 are one device on different
  alphabets, shape 1 is a different device; **a wrong choice is invisible to the type
  checker and caught only by the gate-A hash pin**). ⚠ Findings: `Certificates/M0Fox.lean`
  carries three bridge lemmas whose own docstring names this ticket and which now state
  `x = x` — six tactic steps became no-ops (removed); deleting the vacuous lemmas is the
  file owner's follow-up, deliberately left. Remaining duplication ledger (5 items) in the
  report.
- **2026-08-01 (orchestrator, FD2 — and a naming hazard worth the errata pile):** merged,
  import registered. Beyond the row's content, FD2 flagged that the repo carries **two
  incompatible meanings of `q_K`**: the Lean `FieldParameters.qK` is the RESIDUE cardinality
  `2^f`, while the μ-sense (`i ∈ K`) lives only in prose — including in FD1's and L.lean's
  own errata notes. `ℚ₂(√5)` has `q_K = 4` in the Lean sense yet `i ∉ K`. **Anyone reading
  the even-branch hypothesis off `qK` gets it backwards**; FD2 flagged it in its module
  docstring. Internal docs-cleanup item (NOT a packet erratum — the packet's usage is
  consistent); the AS lane should state the ramified-i branch condition through
  `MarkedRecip.ki_unramified` / `kappaK_eq_zero_iff`, never through `qK`.
- **2026-08-01 (orchestrator, INTEGRATION FIX + AUDIT-PROCEDURE CORRECTION — the root build
  was broken for one merge window):** WL-b found that `lake build GQ2` failed at head:
  WL-a's `Words/L.lean` declared its 20-name alphabet toolkit in the bare
  `GQ2.Dyadic.Words` namespace, colliding with `Words/N0.lean` the moment GQ2.lean
  imported both (M0/Npc had chosen sub-namespaces; L had not). **The WL-a integration
  audit's build step was a FALSE GREEN** — the audit chain piped `lake build` through
  `tail`, and the pipeline's exit status is tail's, so the failure was masked and
  check_dyadic (which does not build) then passed; the board's WL-a row claimed "audit
  green" on that basis and the claim was WRONG for the build half (the WNP-a/WM0-a/WWH
  audits were re-verified genuinely green — the break entered exactly at WL-a's merge and
  lasted until this fix). **Fixes**: (i) `Words/L.lean` re-namespaced to
  `GQ2.Dyadic.Words.LSq` (orchestrator integration fix, the M0/Npc pattern; header note
  in-file; WL-b's anticipated one-line adaptation applied to LFox.lean + one qualified
  rfl-pin); root build re-verified green WITH exit-status checking; (ii) **audit
  procedure corrected going forward: `set -o pipefail` + explicit exit echoes in every
  build/audit chain** — a silent-failure class is closed; (iii) the real de-dup remains
  the WAH alphabet hoist (queued; now FIVE files carry variants of the toolkit).
- **2026-07-31 (orchestrator, WWH outcomes — the toolkit is consolidated):** merged (7
  files, +674/−609; no new files, no import changes; integration audit green). 56
  lane-generic decls hoisted into their owning Word/{Fox,Stokes,Hessian,Blocks} layers,
  **zero statement changes, zero renames** (two bound type-variables freshened,
  alpha-equivalent; one verbatim duplicate deleted); certificate files shed 534 ln —
  future `-b` lanes inherit ~162 and `-c` lanes ~305 instead of re-deriving; all 55
  hoisted prints subset-of-std-3 in their new homes, 15 consumer headlines re-audited
  unchanged. **The repo-wide remaining-duplicates ledger is in WWH's report** (7 items):
  the NpcJet slice kit is now the SECOND copy not the third (unmergeable while NpcJet is
  plain and Word/ is module); the `evalFin_congr_of_orderOf_dvd`↔`evalZ_congr_of_parity`
  joint hoist's natural home is Eval.lean (siblings problem — queued for Eval's next
  owner); ⚠ one-line ticket queued for Eval's next owner: its private `map_commR'` is a
  MonoidHomClass near-twin of `Blocks.map_commR` — de-dup requires generalizing the
  Blocks statement (out of WWH's no-statement-change remit). Three items left in place by
  the module rule, documented in-file. `-b` tickets' WWH prerequisite is now met.
- **2026-07-31 (owner, in session): G2 SIGNED — "Go ahead and dispatch."** The four
  branch-word lanes are RELEASED on the pilot's word-certificate review (the AS2
  √−2 instance review folds into the AS lane/G3 as wave 3 lands). Dispatched (all four
  `-a` tickets, parallel, disjoint files): **WM0-a** (opus, wn0 worktree, `dyadic-wm0a`),
  **WNP-a** (opus, mc worktree, `dyadic-wnpa`), **WL-a** (opus, lg worktree,
  `dyadic-wla`), **WMP-a** (fable per the model column — the hardest word, ob worktree,
  `dyadic-wmpa`). `-b` tickets queue behind their `-a` + WWH's hoist landing; `-c`
  tickets behind `-b` (WL-c per WL-recon's c2-first split). Standing rules for all four:
  the WN0-a template + the wave-2 authoring rules (board log), hash pins by candidate_id
  from `general_2adic/generated/MANIFEST.json`, the KillsWild ruling, F5 counts
  docstring-only, and the per-lane re-point/correction blocks in the specs (WL = L_sq;
  WM0's forward-order correction; WNP's corrected L_c; WMP's S4.5 riders + no-.shadow
  statement route).
- **2026-07-31 (orchestrator, WN0-c outcomes — THE PILOT IS END-TO-END; G2 IS NOW THE
  OWNER'S GATE):** merged, import registered, audit green. The ℚ₂(√−2) pilot lane
  (WN0-a word → WN0-b Fox → WN0-c Stokes/scalar/Hessian/phase) is complete at the
  Def 9.1 word-certificate level; WC-N0's tracker row flipped to layer-complete. Adopted:
  (i) the honest-eval finding (this row needs NO ω₂-representative pin under the
  x₂-no-primal convention — S4.5's rider bites in the pleasant direction); (ii) the
  endpoint condition proved GENERALLY (stronger than the per-word decide the WW3 design
  anticipated — future lanes may inherit `nCompact_isStokesEndpoint`'s pattern); (iii) the
  e = 1/e = 3 scalar-Gram twins are the Lean shard of S1.T's mod-4 sensitivity; (iv) ⚠
  **WWH dispatched** (opus, ww worktree, `dyadic-wwh`): the pre-G2 toolkit hoist — WN0-c's
  four re-derived sections (HeisLift trivial-base closed forms; heisEvalZ constructor
  rules; the module-side slice calculus, THIRD copy of the NpcJet kit; commR twins) +
  WN0-b's hoist candidates (trivAct-as-subgroup, `foxD_prodList_of_trivial`,
  `foxD_comm_of_trivial`, sum_generator_* supports) + WW2's fold-into-Fox items, hoisted
  into the owning Word/* files with all existing consumers kept compiling — saves ≈350 ln
  × 4 in the post-G2 lanes and de-triplicates the slice kit. **The four branch lanes
  (WM0/WNP/WMP/WL) are NOT dispatched — G2 is the owner's review**; the G2 packet is in
  the session summary (read-first order: WN0-c inventory item 1, then the WN0-a template
  rules, then the per-lane route notes in WN0-c's report).
- 2026-07-31 (orchestrator): **second session-limit interruption** (reset 9:30pm ET) killed
  SD-R3 (on its FINAL file — seven per-file commits already banked; `Prop89Close.lean`
  untracked on disk) and WN0-c (reading pass, nothing lost). Both RESUMED on their original
  tiers with salvage-first orders; WN0-c's NpcJet question answered in the resume (plain
  can import anything; NpcJet likely not needed on the compact row).
- **2026-07-31 (orchestrator, SQ4 outcomes — THE L_sq CERTIFICATE + THE PIVOT THEOREM):**
  merged, imports registered, audit green. Adopted: (i) **the SqMixPivot datum is now an
  UNCONDITIONAL THEOREM** — `exists_isUnit_zpowZtwo_eq` (surjectivity companion to
  `zpowZtwo_injective_of_exact_level`, digit-induction + compactness; `1 + 4ℤ₂` is
  procyclic) + the `X^c = S` instance; nothing in the campaign carries it as a hypothesis
  any more; the general half is spelled for a pure file-move hoist to `ZtwoPowering.lean`
  (cleanup-pass candidate, recorded). (ii) **finding: MC5's `SqHandleMixHypothesis`
  preserves only the pivot row** — the χ/pivot-preserving moves shear the two core rows
  by one parameter; SQ4 threaded `SqCoreShearHypothesis` (def, non-vacuous, discharged
  outright when ν'(x₀) = 0) AND landed the checked repair: **`SqHandleMixFixesCore`
  (MC-HM's construction "fixes x₀/σ literally") IMPLIES MC5's binder and gives the full
  reduction alone** (`sqMarkedMatching_of_fixesCore` etc.) — whether MC5's binder gets
  RESTATED in fixesCore form is bundled into the errata-item-1 CoV ticket (it owns the
  change-of-variables this rides on; MC5's file untouched meanwhile). (iii) shape ruling:
  MC5's M/N certificate records are source-hardwired — the L core needed its OWN record
  in the same pattern; future core families budget a record each. (iv) **binding
  discipline for AS1/WL**: the satisfiable marked-data clause is `ν'(w) = ofAdd 1`
  EXACTLY, not `IsUnit` (the shear cannot move the pivot value); and the L_sq marked
  data is a PAIR (ν(x₁) = 2ν(x₀) is forced for every marking; σ̄ carries no forced row).
  (v) prints: 39 headlines std-3; exactly 2 isolated B3c+B8 decls = the rank-3-discharge
  consumers (SQ23 precedent honored) — **`marked_square_core_rank3_certificate` is
  UNCONDITIONAL over ℚ₂** with its ν-slot pinned to `R.nu_ur`; census 11 unchanged.
  (vi) SQ2's `dsqEquivDR` cast blows the heartbeat budget at isDefEq — consumers use
  SQ4's `sqEquivDRMarked` (generator-value theorems included; WL-b/c note). (vii)
  **SQ5/AS4 is smaller than feared**: the missing L_sq core stratum is ONE shear family,
  not an MC3/MC4-scale classification. SQ lane remaining: nothing until AS4 (SQ5 folded
  there per WL-recon Q2). mc worktree freed.
- **2026-07-31 (orchestrator, WN0-a outcomes — THE WAVE-2 TEMPLATE EXISTS):** merged,
  import registered, audit green. This file is what the G2 review judges and what the
  other four branch lanes copy. Adopted: (i) ⚠ **`KillsWild` RULING (binding on all
  branch lanes)**: F3's bare `KillsWild` quantifies over every marking with no τ
  condition, and the tame kill of ANY δ-letter branch word is exactly `τ^{ω₂}` — so bare
  `KillsWild` is UNSATISFIABLE for every wave-2 word (WN0-a proved `not_killsWild` in
  `Multiplicative (ZMod 8)`); the admissibility routes are `killsWild_of_tau` /
  `killsWild_of_odd` (τ pro-odd inside Γ_R via `TameQuotientK.odd_order`) — branch lanes
  use those, NEVER the bare form. Micro-row **F3b queued** (docstring warning + a
  τ-pro-odd-conditioned variant on the bare def; cleanup-pass tier, not blocking).
  (ii) **Words/ + Certificates/ are non-module** (forced by the TameBoundary import;
  module rule is one-directional) — lane convention ratified. (iii) the certificate's
  association `(x₂^σ)⁻¹` (`.inv (.conj …)`) is the hashed spelling — NOT F2's `invConj`
  sugar (other association); packet Rem. 2.3 is silent on association and the
  certificate chose. (iv) **template rules distilled for the four remaining lanes**
  (full list in WN0-a's report): every `Multiply` is `prodList` (expect the trailing
  `.one`; five-element instance pins); generator names by literal `match` table (never
  `String.toNat?` — not kernel-reducible); `denote` bridges per-instance never
  h-generic; handles by `Fin h`/`List.finRange` (matches Export AND MC2 orderings);
  the pro-2 comparison needs the ℤ→ℕ zpow realign + `Marking.apply_sigma` and `group`
  cannot close it; reuse WW5's kernel pins by `rfl`-equating to `Export.frozenX`; state
  tame boundaries as VALUES not `= 1`; F5 counts in docstrings only (A₄ is the only
  σ-vs-σ₂-sighted target of the three, and no 2-group can see it); explicit witnesses
  over `∃ … by decide` (kernel recursion budget). **WN0-b queued behind WW2** (its
  FoxCert consumer).
- **2026-07-31 (orchestrator, MC5 outcomes — THE MARKEDCORE LANE'S CERTIFICATE LAYER IS
  COMPLETE):** merged, import registered, audit green. Adopted: (i) the abstract-slot
  certificate shape (SD1 Q4 pattern; the ledger's `DyadicField`/`chiK`/`nuK` names do not
  exist — plain MonoidHoms + continuity in production hypotheses) RATIFIED; (ii)
  `evalMatrix`-invertibility non-duplication RATIFIED (the rank-3 role is carried by the
  MC3/MC4 parameter classifications); (iii) **the final binder inventory is the SQ4/AS1
  supply list of record** — N-core: `NScalingHypothesis` + iso/orientation +
  pair-unimodularity `IsUnit ν'(σ̄) ∨ IsUnit ν'(x̄₂)`; M-core: `MMixHypothesis` + the
  compact-M CoV pivot datum `IsUnit ν'(C̄₀)` (errata item 3 — packet-author input);
  K-layer: the `(G, π, Continuous π)` slot + `MarkedRecip` bundle (satisfied by
  `markedRecipAt` at the flip-free call site); (iv) ⚠ **NEW SQ4 input gap identified**:
  the `SqMixPivot` exponent datum `∃ c ∈ ℤ₂ˣ, X^c = S` is a `zpowZtwo`-surjectivity
  statement about the procyclic `1 + 4ℤ₂` that is **not in the repo** (ZtwoPowering.lean
  is the natural home for the lemma; SQ4's dispatch carries it) — and
  `SqHandleMixHypothesis` needs the errata-item-1 change of variables (the L_sq core has
  no literal `[y,z]` on the ⟨σ̄,x̄₀⟩ plane, so `HandleMixLift` does not transfer; the
  binder may STAY a binder at SQ4); (v) micro-ticket candidate recorded: a module-side
  `IsProP 2 (WordLift ℤ₂ ℤ₂ˣ)` hoist (~90 ln) if a module consumer ever appears —
  NOT opened; (vi) obligation tracker updated: **MC-M and MC-N are now
  theorem-complete-modulo-binders** (classifications = theorems; matching = theorems;
  residual surface = exactly the recorded binders, discharged at G-Lab/AS1 or by the
  packet author's CoV answer). **SQ4 dispatched** (opus, mc worktree freed →
  `dyadic-sq4`): SqCore/Certificate.lean consuming MC5's certificate + the pivot lemma;
  SQ5 stays deferred to AS4 per WL-recon Q2.
- **2026-07-31 (orchestrator, SESSION-LIMIT INTERRUPTION + RESUME — all six in-flight
  agents killed, all seven resumed):** the Fable session usage limit killed WW2/WW4/MC5/
  SD-R1/WN0-a (here) and S4.5 (simp side) mid-flight; reset at 4:20pm ET; every agent
  RESUMED from its transcript with salvage instructions. Salvage state at resume: **SD-R1
  had SIX FILES COMMITTED** (Frame/Numerics/Covers/Partition/Recursion/Block — the
  commit-per-file discipline worked exactly as designed) and **S4.5's verdict chain was
  committed** (through 8a54c9e; only its final suite runs died); WW2 (1069 ln), MC5
  (1045 ln), WW3b (611 ln) had uncommitted files on disk — resume orders lead with
  commit-the-green-subset-first; WW4 and WN0-a lost nothing (died pre-write). **SD-R1's
  stop-and-report fired correctly on two seams** (documented in Recursion/Block.lean),
  and a depth assessment completed during the outage; verdicts ADOPTED: **SEAM A**
  (§7/prop_7_4 is typed at the ℚ₂ boundary) is MECHANICAL and CHEAPER than the memo
  implied — SectionSeven/{Basic,ModuleCore,Prop74Step1} have zero boundary mentions
  (import as-is; do NOT clone); only Decorations' lemma_7_2 (decorative cH binder, zero
  body uses) + Prop74's four decls clone, threading {q ≠ 0, Even q} and swapping exactly
  four lemma names (gen_tq_quotient / tame_rel_map_q / TameQ.zpowers_normal /
  TameQ.odd_order — all already exist general-q); scope-added to SD-R1 with the ~330-ln
  Block-file cH-variable ripple it already owned. **SEAM B** (§6/kappa0_exists through
  `ActsThroughTame`'s literal `t^2` clause) is mechanical-with-one-def-change and
  belongs to **SD-R2** (Induction.lean is its scope; row updated): PJ1 already de-fanged
  the deep half (both consumers are thin wrappers over exponent-free `_of_odd_normal`
  lemmas; the general-q leaves exist in Projectivity.lean), the producer side exists
  (SD-R1's hv_relK), and the ~710-ln Block-file consumer retype rides the def change.
  ⚠ assessment caution recorded for both: `lemma_6_11_of_tame_pair_pow` is stated at
  q = 2^f (1 ≤ f), NOT Even q ∧ q ≠ 0 — route through the leaves + `_of_odd_normal`,
  not that wrapper. (The seam assessment itself was run as a read-only sub-analysis
  during the outage; its full table is in the transcript and the actionable content is
  this entry + the resume orders.)
- **2026-07-31 (orchestrator, WW1+WW3+WW5 outcomes — THE WW SPINE IS IN):** all three merged
  in one train, imports registered, D4 ACTIVATED with WW5's worker-tested line
  (orchestrator-applied; SKIP text now says "arrives with wave 2"). Combined audit at the
  train's head. Adopted per ticket: **WW1** — the evaluator is `evalFin` at the semidirect
  `foxLift` (exact identity, not first-order), Prop 4.1/4.2/Lem 4.3 complete, both n=1
  hand-row regressions proved; the defect interface is hypothesis-style (no frozen
  structure) with descent via `foxD_comp_hom` — RATIFIED (strictly more general than the
  spec's ρ-hardwired shape); Lem 4.3's δ-functor naturality beyond chain-map + coordinatewise
  transfer DEFERRED to WW3's machinery (docstring says so) — accepted; WW2 must state
  resolver-correctness at the lift level (`pow_eq_pow_of_modEq_two_mul`) and route
  ω₂-collapse through the three engine lemmas, never unfold `powOmega2`; new pitfall for all
  lanes: equating two `foxJacobian`s needs `(A := …)` pinned. **WW3** — second-order rule
  DEFINITIONAL via `evalZ` (deviation ratified: strictly stronger reuse than a fresh
  recursion); frozen `lemma_5_7_*` transported via `freeGroupCongr`, not re-proved; Lem 5.1
  landed as mapping cones + `StokesSES` calculus with the six-clause quotient-free
  quasi-iso interface (ratified — consumers get witnesses directly); `stokesDuality_of_simple`
  = the once-only dévissage (wl-recon V6/R5 discharged); the WMP "copies cancel" step is now
  the `heisJetZero` family — **the σ-column coincidence lemma must be stated against it**;
  ⚠ flagged gap → **WW3b row created** (universal-coefficient step, ~150 ln, queued opus;
  fold-into-WL-c1 rejected — it gates the `StokesDualityCertificate` record, whose field
  shapes ride SD1 §6); WW1↔WW3 bridge = one `map_evalZ` line under the HeisLift→WordLift
  projection (recorded for WW2/WW4); 3 mathlib-upstream candidates noted. **WW5** — NO
  second tree encoding (an S1.8 certificate IS an interchange file); hash mirrors ast.py
  byte-for-byte (schema version outside the hashed bytes); 4 frozen-row digest pins python
  + 2 in-kernel Lean byte-pins (own `natToString` — `toString`/`Char.ofNat` don't
  kernel-reduce; `maxRecDepth 8000`); mandate correction accepted (search.json carries no
  word_ast — pin lives in the certificate twin); **six wave-2 gating mismatches RECORDED
  as the wave-2 authoring rules**: (1) ⚠ Shadow parses/hashes but does NOT denote —
  **WMP-a is blocked on a Lean-side `Sh_M` substitution operator** (S4.2's frozen
  substitution is the spec; dated note added to the WMP spec block); (2) OrbitNorm/handles
  denote at concrete lengths only (hash unaffected — it is of the unexpanded tree);
  (3) symbolic exponents denote after assignment; (4) `z2pow` has NO S1.1 counterpart —
  using it in a hashed word needs an S1.1 migration note first; (5) Shadow param sorting
  is a checked precondition Lean-side (`paramsWf`); (6) NEITHER side normalizes before
  hashing — wave-2 Lean trees must be authored in the certificate's spelling (e.g.
  `integerPower`, never `zhatPower … (.int n)`). Export.lean's `<decl>_astHash` +
  `#eval assertAstHash` guard is the wave-2 convention. **Dispatched: WW2 (fable, ww,
  `dyadic-ww2`), WW4 (fable, lg, `dyadic-ww4` — SD1 §6 is its ratified baseline), MC5
  (fable, mc, `dyadic-mc5`), SD-R1 (opus, wl worktree re-pointed, `dyadic-sdr1`)**;
  WW3b + WN0-a queued behind the next freed opus slots.
- **2026-07-31 (orchestrator, SD1 outcomes — THE SD LANE IS RESTRUCTURED):** memo merged
  (`sd-design.md`, docs-only). **The headline is a structural discovery the recon survey
  understated**: every generic count in §§4–9 is typed at the concrete ℚ₂ boundary
  (`b : … ↥boundarySubgroup`, `Ttame`/`PiBd` frames, `tameTau` by name), so a two-sided
  degree-n theorem cannot be stated against the frozen spine at all — SD-n is a
  **boundary-abstracted clone** (≈9.1k ln into `GQ2/Dyadic/Recursion/`), with the
  frozen-file edit list EMPTY (plan A6 holds by construction; LG1's clone ruling is the
  precedent) and the deep mathematics (VLiftCount's `two_mul_card_centralImage`,
  descent/keystone/Fourier, Reconstruction — zero boundary mentions, checked) reused as-is.
  The n = 1 story is STRONGER than wrappers: F3's refl-bridge extends to the subgroup level
  (`boundarySubgroupQ 2 nuTwo = boundarySubgroup := rfl`, probe-verified), so the cloned
  stack's n = 1 instances are stated at literally the old boundary. **Adoption calls
  (flagged blanket — owner may override)**: Q1 = (a) clone-retype, incl. the sub-question's
  clone-side `VLiftCount` wrapper (edit list stays zero); Q2 = DROP the 4 marked-generator
  + 8 pinning fields (consumed nowhere; MC1 §(ix); docs move to instantiations; the
  optional `SourceMarking` companion available if an instance wants it); Q3 = opaque
  `SourceNumerics` constants, formulas confined to `standardNumerics n` (the solver only
  cancels shared coefficients — verified line-by-line; `pow_one` is not `rfl`); Q4 =
  abstract marked pro-2 slot `(P, IsProP 2, nuP)` — SD never waits on MC5; AS1
  instantiates at `D_P` via the certificate (the `sourceR` transport recipe); Q5 =
  SN-valued Gauss leaves (`gaussUnram/gaussRam : ℕ → ℤ` of the half-dimension); Q6 =
  ADOPT the SD-R1–3 wave + one K-supply ticket (rows added; SD2/SD3 rescoped ≈0.5k/≈0.9k;
  SD2 gains `sourceF_N` from the verified `*_local` leaf pack incl. `hsep_local`/
  `hpartial_local`) — **K-supply lane assignment (AS vs LG-revival) is the one item left
  genuinely with the owner**; Q7 = **§6 RATIFIED as WW4's baseline** (maps def:affine-B4
  onto the five REAL record families per the ledger-§3.4 warning; `affinePhase` is a
  certificate INPUT the WMP-c worker constructs — the row-5 satisfiability constraint is
  binding; WW4 deviations go through an SD1-memo amendment, never silent). Degree-analysis
  correction adopted: eq. (140)'s inner `|M|/|T|` factor is #H¹ = |V|ⁿ and MOVES; the
  `GaussZResidue` outer `|V|` is #B¹ and is degree-independent. ⚠ errata cover note
  queued: the campaign's packet citations for §§7–10 are off by one against the vendored
  compile — cite by label (memo does). SD-R1 queued for the first freed opus slot; sd
  worktree pruned.
- **2026-07-31 (orchestrator, MC-OB outcomes — MC5 UNBLOCKED):** merged, import registered;
  integration audit green (build + check_dyadic; census 11; job count grows by the one new
  module). Adopted: (i) **`NatWord` deviation RATIFIED** — the layer is built on an abstract
  word bundle with `NatWord.ofPWord` making F2's reflected syntax an instance, because MC2's
  `mRelWord`/`nRelWord`/`handleWord` and `drWord` are function-shaped; this is the right
  altitude, not a dodge. (ii) **layer-order rule recorded**: `Word/` must never import
  `MarkedCore/` — the MC2 instantiation goes the other way via `relZ_ofDRCoh` (the
  `?RelWord_centLift_fib` fibres ARE this file's `relZ`; one-line anonymous constructor at
  the MarkedCore layer — that line belongs to MC5). (iii) `relZ_zero` needs NO Frattini
  hypothesis (`NatWord.ev_one` unconditional) — cheaper than DRWordCoh's spelling, noted for
  consumers. (iv) the Frattini parity-reduction (`evalZ_congr_of_parity`) is what makes
  kernel `decide` usable where the honest ω₂/η̂ resolvers are noncomputable — WW1/WW2 should
  reuse it rather than re-derive. (v) 1504-vs-900 line overage accepted (multi-relator
  family + parity reduction + Marking wrappers + pins 6–8 — all consumer-facing).
  (vi) dedup map (ofDRCoh/toDRCoh + the WordCoh2 shadow list) recorded in-file; WordCoh2
  itself stays frozen and unimported. **MC5 (fable) dispatched** (mc worktree, branch
  `dyadic-mc5`): the full brief incl. MC3/MC4 frames, HM4's `MLiftSplit`/`NLiftSplit` +
  HM6/6ef/6g binder endstates, MC-VAR's transpose rule, the SQ1-R1 L_sq mixing-frame redo,
  MC-OB's API, the widened odd-L scope, and the compact-M CoV gap (errata item 3) held as an
  explicit datum. ob worktree pruned.
- **2026-07-31 (orchestrator, F5 outcomes — the wave's first landing):** merged (script-only;
  check_dyadic green end-to-end in the integration worktree, D5 now OK; full-build re-run not
  information-bearing — no Lean touched). Adopted: (i) ⚠ **the forward-E_m mutant is
  F5-UNREJECTABLE, structurally** — forward and reversed 𝓔-blocks agree pointwise on every
  marking of S₃/D₈/A₄ AND of S₄/SL(2,3)/GL(2,3) (the last two with nonabelian O₂ = Q₈);
  this is the freeze's own coverage criterion biting (separating orbit needs dim ≥ 2^α;
  these wild layers have 𝔽₂-dim ≤ 2). The WM0 spec's "F5 mutant row must reject it" was
  therefore IMPOSSIBLE as written — dated correction block added to the WM0 spec; the
  rejection of record stays S4.1's §9.4 proof-grade difference formula; F5 pins the row
  NOT-SEPARATED so any future separating target fails loudly. (ii) **counts are too weak
  for 3 of 4 mutants** (sign-row and wrong-conj-side reproduce 6/1568/120 exactly — the
  conj-side mutant's admissible SETS coincide too; only wrong-σ₂ moves a count, 504 ≠ 120
  as predicted) — F5 uses pointwise word values (C1) and a pinned admissible witness (C3)
  instead; any lane adding "python-harness rows" must copy that discipline, not counts.
  (iii) the reference script's d = 10 word was the DRAFT §7.3 field-specific word, not the
  frozen procyclic row — re-pointed count-neutrally (row A4 = frozen spelling; row B2 keeps
  the draft word + pins pointwise 0/0/0 agreement on all three targets). Reconciliation
  note: errata item 8's "S₃ witness separates the two relators as words" refers to the
  S4.3 module-oracle level, NOT marking-values on S₃ the group (F5 measured those at 0
  pointwise) — consistent, but worth one line when the errata bundle is sent. (iv) banked:
  frozen-Npc (α,r,η) = (2,1,1) pin 6/1568/120 for WL-a/WNP-a's harness rows. (v) D5
  placeholder comments in check_dyadic.sh refreshed (orchestrator, comment-only).
  f5 worktree pruned.
- **2026-07-31 (orchestrator, G-1 RELEASED — PHASE 5 OPENS; wave dispatched):** the
  simplification campaign signed R4 (owner-delegated in session: "review the report and
  start the next phase"; verification record on that board) and flipped R5. **The frozen
  selection is `general_2adic/artifacts/reports/selection-freeze.md`** — authoritative for
  every word-dependent lane; suite at freeze 1759 tests both interpreters. **Lane
  re-points** (binding; dated blocks added in the specs where the text disagreed):
  (i) ⚠ **WL is `L_sq`**, the stabilized square-commutator — the lane spec below was
  written against the collector and now carries a re-point block; n = 1 word IS Roe's `Γ_R`
  (SQ1), so WL-a's cross-identification target is `wildRelatorR`/`Γ_R` and the collector
  display survives only as the safety-net regression; χ_sq(σ) = S ≠ 1 (SQ1-R1) — MC5 redoes
  the §6.4 mixing analysis in the L_sq frame; (ii) WNP already re-pointed (corrected `L_c`,
  NC lane governs); the 4 cheaper parked S3.2 survivors are disposed of by WNP-b/c;
  (iii) WMP additions from phase 4: `E₀₁^pc` is justified at SECOND order only (gate D
  cannot justify it; not independently choosable from the shadow substitution — the finding
  is paper-relevant and changes WMP-c's statement); the Lean side needs the **σ-column
  coincidence lemma**, not the geometric-sum identity; the hat copy = ONE frozen
  substitution's image (S4.2 `Sh_M`, four properties in the shadow-theorem memo);
  **the WC-Mpc affine phase data exists in NO ticket yet** — it is WW4/WMP-c work; the
  √−10 relative-norm word is RETIRED to regression-only (F5 keeps its row as a regression
  alternative, per the WMP spec's existing language); `E₂^pc` rides on S1.9's `orbitNorm_eq`;
  (iv) WM0 unchanged in shape; the compact-M marked CoV gap (errata item 3) stays an
  explicit-datum binder until the packet author answers. **Cross-repo artifacts**: simp
  ticket S5.G emits `generated/{lean,latex}` for the five rows (currently EMPTY — WW5's
  one-tree hash gate must consume S1.8's canonical hashes; WW5's prompt reads
  `words/pretty_lean.py` + `certificates/emit.py` first); simp addendum S4.5
  (`swap[E2.E01]` geom comparison) is non-blocking and can only confirm the freeze or
  surface an owner amendment. **Dispatch (this wave)**: **WW1** (fable, ww worktree branch
  `dyadic-ww1`), **WW3** (fable, lg worktree branch `dyadic-ww3`), **SD1** (fable, memo-only,
  fresh worktree `gq2-dyadic-sd` — reads LG1's drop-eulerChar note, F3's Tq-field note,
  AX1/FG1's tfg-as-record-field shape, MC1 §(ix), and coordinates the phase-interface field
  shapes with WW4 per its spec), **WW5** (opus, wl worktree branch `dyadic-ww5`), **F5**
  (opus, fresh worktree `gq2-dyadic-f5` — regression-only python; **includes the retired
  `rel_minus10` row + the mutant rows**), **MC-OB** (opus, NEW ticket, pj-adjacent fresh
  worktree `gq2-dyadic-ob` branch `dyadic-ob`: the relator-generic `obsH2` port MC2 flagged
  (~900 ln — `TwoCocycle`/`CentExt`/`comap`/`projExt` hoist per MC2 log item (v), file
  `GQ2/Dyadic/Word/WordCoh.lean`) — **MC5 and the branch-word cohomology consume it**).
  **Queued**: WW2 (fable) behind WW1; WW4 (fable) behind WW3 + SD1's field-shape
  coordination; **MC5 (fable — upgraded from opus: it is the convergence point of MC3/MC4 +
  HM assets + MC-VAR's transpose rule + the SQ1-R1 L_sq-frame redo)** behind MC-OB; SD2
  behind SD1 review. Fable concurrency held at 3 (the 07-29 spend incident); commit-early
  discipline mandatory in every fable prompt. **Owner queue**: send the errata bundle (8
  items + clarification, appended today); chiTwo census-9→8 spike (G-AX); packet-PDF
  verification; MMixHypothesis family-form restatement (HM6g); G2 at AS2.
- **2026-07-30 (orchestrator, HM6g — the M/N mirror is now EXACT):** merged, import
  registered; audit green **3422 jobs**, census 11; all 12 decls std-3 (no B8, no B3c).
  ⚠ **The prescribed route was wrong and the ticket said so**: HM6ef §6 (which the dispatch
  repeated) is internally inconsistent — it correctly identifies the leftover as
  `D̄ ↦ D̄ + k·Ā` but then prescribes a **B-slot** shear (MC3's `mLambdaEquiv`/τ_a) to remove
  it; in fact `hm6FrameBDc k` leaves `k·Ā` on TWO rows (B̄ and D̄) and τ_a reaches only the
  first, the D-slot analogue is unavailable (the insertion would be a power of `a` inside
  `[c,−]`, where `mCommP_zpow_left` does not apply), and τ_a is **not in `A⁺(P,h)`** anyway,
  so the composite would have left the widened monoid and forced a SECOND widening.
  **The route that works uses the M relation itself**: the M-side analogue of `nChar_dnX0` is
  not `Ā = 0` but `2Ā + 2^αC̄₀ = 0`, which PINS `Ā = −2^{α−1}C̄₀`, so both residues are
  C̄₀-multiples — exactly what HM4's exact τ_c writes. One `.trans` of HM6ef's
  `dmRealizesWide_frameBDc` with `dmRealizesWide_tauD` (both already generators), then
  reparametrize by the unit `1 − 2^{α−1}`. **No second widening, no new generating set.**
  Landed: `mCoreMixHypothesisWide_pureM5` on **literally the N-side stratum set** (so the M/N
  mirror is exact) and `mMixFamily_coreMix`, the true mirror of `nMixPairHypothesis_coreMix`.
  Bonus cross-check: `nuFrame_mLambdaEquiv_eq` shows **MC3's τ_a row IS a pure M5 row** at
  parameter `−k·2^{α−1}` = exactly `mFamM1`'s recorded `B_c` entry — an independent
  confirmation of MC3's Nielsen table, and the reason adding τ_a to the generating set would
  buy nothing (it reaches only the ideal `2^{α−1}ℤ₂` where `dmPureM5` reaches all of ℤ₂).
  HM6ef's `mCoreMixHypothesisWide_m5` is NOT superseded (it holds at general α; HM6g needs
  α ≥ 2). **Remaining on M, unchanged in kind**: `⟨M4,M6,M7⟩` (structural) + the S2
  unit-scaling binder (through the existing B8). **Two owner-visible items**: (i) no part of
  `MMixHypothesis` is discharged and no corollary lands, because MC3's binder is
  **marking-transport shaped**, not family shaped, and the M lane has no
  `mMixHypothesis_of_pair` analogue — **restating `MMixHypothesis` in family form is an owner
  call**; (ii) there is no M-side `dmClearAuts_fixes_core`, so the "narrow FALSE / wide TRUE"
  pin pair exists only in its wide half on M — landing the refutation needs a new rigidity
  lemma (follow-up, not opened).
- **2026-07-30 (orchestrator, MC-VAR — VERDICT (a) DUAL ENCODINGS; the discrepancy is
  CLOSED):** merged, `Variance.lean` import registered; audit green **3421 jobs**, census 11;
  all 15 decls std-3. **Both files were correct all along and their two clauses are literally
  the same equation** — `M.lean` stores the frame endomorphism with images in the **rows**
  (`mFrameMatrix = Aᵀ`), `N.lean` with images in the **columns** (`NRows.mat = A`), so each
  pairs its own layout with the transpose that yields `A·G·Aᵀ = G`. ⚠ **The orchestrator's
  dispatch premise was WRONG and the ticket caught it**: I asserted `nMatOf`'s rows hold the
  images; they do not — column 1 is `NStabParam.rows.x1` reduced. (My dual-encoding
  hypothesis was right in shape, wrong in mechanism: it is rows-vs-columns, not
  group-side-vs-character-side.) The repo's cup semantics decides it: `Cores.lean:1333-1336`
  fixes `κ(a,b) = ⟨v,a⟩⟨w,b⟩` for COVECTORS and the `?RelWord_centLift_fib` evaluations are
  literally `nCupForm`, so preservation is `A·G·Aᵀ = G`. **Both counterexample claims are
  TRUE and are the same counterexample stated twice** (the flipped condition's (0,1) entry
  forces τ = 0, killing M1 resp. N1 — Lean-checked three ways); the distinction is
  nonetheless real (`G⁻¹ ≠ G`; `nMatOf_famN1_variance_differs` exhibits a matrix satisfying
  one variance and refuting the other). Dictionary landed: `mCupIsometry_iff_nCupForm`,
  `nCupForm_iff_mul_transpose`, `nRows_isCupIsometry_iff{,_mStyle}`, and the sharpest
  instance **`mFrameMatrix_transpose_eq_nMatOf`** — at a classified M-parameter, **M's Witt
  coupling IS N's `couple_p` and M's unit γ IS N's `det ḡ = 1`**; as a by-product
  `mFrameMatrix_cupIsometry` gives the converse of MC3's Witt half (which M.lean never
  states) for free via MC4's `nCup_iff_mod2`. **MC5 rule: treat the two `Prop`s as
  interchangeable via `Variance.lean`; NEVER move a matrix between the files without
  transposing; the remaining trap is pairing an H₁ matrix with an H¹ one** (`MStabParam.act`
  vs `NStabParam.nuAction` — the latter's `nCoreMat P.g.transpose` is correct as written).
  **Root cause fixed by the orchestrator** (docs-only, memo §6's exact clauses): both
  variance notes now NAME their layout — that omission, not the mathematics, is what made
  the two reports read as contradictory.
- **2026-07-30 (orchestrator, HM6ef — THE N LANE'S S3 RESIDUE IS GONE):** merged, import
  registered; audit green **3420 jobs**, census 11; all 37 new headlines std-3. **The
  additive route was not a preference but a necessity**: widening `dnClearAuts` IN PLACE
  would have kept `dnClearAuts_fixes_core`'s statement while DESTROYING its truth (HM6's
  `dnCoreMixPEquiv` moves slot 1), and MC4's `nCoreMixHypothesis_not_of_mix`, HM5's
  `chiN_of_mem_dnClearAuts` and HM4's `exists_dnClear_nu` all read that set — the
  in-place edit would have silently broken three landed results. Recorded in both file
  headers. Landed: HM6e's ν-frame rows (ONE frame move serves both M5 and N5 — the interior
  factor is frame-invisible), and HM6f's `ClearWide.lean` (800 ln) with
  `d?ClearAutsWide` + `D?RealizesWide` + the transport lemmas (one line each via
  `Submonoid.closure_mono`), plus `dnClearAutsWide_fixes_x0` — after widening EXACTLY ONE of
  MC4's three rigid slots survives, so `A⁺` is wider by precisely what the core stratum
  needs. **The payoff composed on both halves**: `nCoreMixHypothesisWide_mixX1` is a theorem
  **on the identical stratum set MC4 refuted for the narrow form** (with a kernel-checked
  (2,1) pin placing the negative and the positive side by side), and
  **`nMixPairHypothesis_coreMix` makes MC4's OWN binder a theorem** ⇒ `nMixHypothesis_coreMix`
  and `nStabParam_lift_of_scaling` — **the N lane now has NO S3 residue; its only remaining
  binder is the S2 unit scaling.** Both collapses rest on `nChar_dnX0` (the x̄₀-row kills the
  raw twists' extra components). Deviation documented: `dnClearAutsWide` also absorbs N3
  (MC4's exact `dnTauCEquiv`), which is what cancels N6's σ̄-shear. M side: memo §5.2's
  `⟨M5⟩` factor landed (`mCoreMixHypothesisWide_m5`). **Remaining binder-shaped on M**:
  (i) the last shear for MC1's displayed pure M5 — `τ_a(−k)` is exact and axiom-free but
  lives in MC3's `M.lean`, which HM6ef could not import; `hm6FrameBDc_of_zero` names the
  exact hypothesis (`Ā = 0`, true on `D_N`, false on `D_M` whose relation is
  `2Ā + 2^α C̄₀ = 0`) — **now a ONE-`.trans` follow-up since both files are merged**;
  (ii) `⟨M4,M6,M7⟩`, structurally obstructed — no widening reaches it, MC1 §8 Decision 2(A)'s
  price and risk label stand.
- **2026-07-30 (orchestrator, NC6 — THE NC LANE IS CLOSED):** merged, import registered;
  audit green **3419 jobs**, census 11. `Handles.lean` 504 ln, all 25 decls std-3.
  `npc_cross_operators_handles`: the handled headline gains exactly
  `∑ j, b_q(e_{a j}, e_{b j})`, proved in FOUR rewrites citing NC5 — nothing below the seams
  re-entered; hypothesis surface is NC5's verbatim plus one bookkeeping equation
  (`e 2 = 0`). Generalized beyond the memo: arbitrary handle index functions, with the
  memo's literal `x_{3+2j}/x_{4+2j}` indexing as the corollary
  `npc_cross_operators_handles_std`. **The concrete carrier lands the non-vacuity**:
  `PinC` = C₃ acting on 𝔽₂² by the companion matrix of `x²+x+1`, anisotropic `pinQ`,
  invariant `pinF` — all eight `IsEquivariantFactorSet` fields + `hV2` + `hVu` + the action
  axioms by **kernel `decide`**; because the group is pro-odd, `A = g` for EVERY `η`, so
  **both sides become numerals**: the jet is `1` at `(α,r,η) = (2,1,1)`, and `0` with one
  handle (the tail `b_q((1,0),(0,1)) = 1` OBSERVED, not assumed). Also landed
  `npcHandles_eval_eq_handlesProd` (the block IS `Blocks.lean`'s `handlesProd` at the
  marking — S1.9's Lean identity meeting the NC lane). **Lane inventory: NC1 memo → NC2 Defs
  → NC3 Omega → NC4 Seams → NC5 Main → NC6 Handles; the R3(a) commission is delivered end to
  end, everything std-3.** Residual for WNP-c (unchanged, and correctly scoped): per-module
  invertibility of `L_c` — the identity says the jet IS `Q₀ + b_q(c₁, L_c c₀) + tail`, not
  that the pairing is nondegenerate; that varies with the module (on NC6's carrier
  `L_c = g` is invertible; with `A = B = 1` it is the identity) and belongs to WNP-c's
  Fox/normal-form clauses, where it is a `decide` on a battery module.
- **2026-07-30 (orchestrator, MC3 done + ⚠ AN OPEN DISCREPANCY, ticket MC-VAR):** MC3 merged
  (audit green 3418, census 11, everything ≤ std-3 with zero census-axiom citers). Its
  classification is `∃!` over an explicit 7-parameter stabilizer with a full Nielsen
  factorization. Findings adopted: β is a unit by χ and γ by Witt, so the rank-four
  classification never needs `ξ⁻¹` (unlike `prop_3_8_classification`); the 7-family
  factorization CANNOT avoid parameter adjustments (Y_c reads C̄₀/writes B̄ while X_b reads
  B̄/writes C̄₀ — no ordering works verbatim; all adjustments are even, which is why β₄ stays
  a unit); the S2 unit-scaling lift is NOT built (MC2's scaling lemmas give the scaled TRIPLE
  identity, not a marking whose relator dies — the two conjugators of `w_M = A·A^B` need an
  inner twist to match; left to MC5/G-Lab, `mFamM3` records the frame row it must realize);
  best pin `mPin_mUnit_two` — **the M₂ orientation unit IS the ℚ₂ `η = (−3)⁻¹`**, so the
  rank-four χ-row engine specializes to the rank-three one exactly.
  ⚠ **THE DISCREPANCY (do not let MC5 consume either side until it is settled):** MC3 states
  the cup-isometry as `M̄ᵀ·G·M̄ = G` and reports the other variance "forces τ = 0 and destroys
  family M1"; MC4 states it as `M̄·G·M̄ᵀ = G` and reports the transpose convention "kills
  family N1". Both files are green, both share the SAME Gram
  (`!![1,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]`), and MC4's `nCupForm` is verified to BE that
  Gram's bilinear form (`nCupForm_eq_gram`), so the two matrix equations are genuinely
  different equations — over this G they are `M ∈ O(G)` vs `Mᵀ ∈ O(G)`, and `G⁻¹ ≠ G` here,
  so the two groups need not coincide. **Orchestrator hypothesis (NOT adopted, to be
  machine-checked):** the two are the same statement in DUAL encodings — MC3's matrix is
  ξ's action on the abelianization (group side), MC4's `nMatOf` is the action on ν-frame /
  character vectors (H¹ side), where a substitution acts by transpose (MC4's own note on
  `nCoreMat`), so each is correct in its own encoding. **MC-VAR dispatched** to settle it
  from the repo's cup-form definition, read-only vs both files. No downstream ticket may
  assume an answer meanwhile.
- **2026-07-30 (orchestrator, MC4 done — and it RECONCILES with HM6):** merged, import
  registered, audit green 3417 jobs / census 11. **MC-N's classification is a theorem**
  (iff, unconditional, uniform in α ≥ 2), everything std-3 with NO census axiom anywhere.
  ⚠ **The load-bearing reconciliation**: MC4 proved `dnClearAuts_fixes_core` (no generator of
  `A(P,h)` touches a slot of index < 3) and hence **`nCoreMixHypothesis_not_of_mix`: HM4's
  SCHEMATIC S3 binder is UNSATISFIABLE for any genuinely mixing stratum** (with a stress pin
  at (2,1)). This does NOT contradict HM6 — HM6 proved the core-mixing AUTOMORPHISMS exist;
  MC4 proved they cannot live inside `A(P,h)`, the handle generating set HM4's binder
  quantifies through. **Consequence: HM6f (widen `d?ClearAuts`) is NECESSARY, not cosmetic —
  the N-side discharge cannot be wired until the binder's shape is fixed.** MC4 routed around
  it (its core families use `NPlaneRealizes` — χ-preservation + ν-frame action, no `A(P,h)`
  clause), so nothing is blocked meanwhile. **HM6ef dispatched** with both results as input.
  Other adopted findings: (i) MC4's **deliberate deviation** — the S2 stratum's B8 route is
  CITED but not EXECUTED (the conjugator matching + Frattini surjectivity that assemble two
  scaled triples into one automorphism is the missing step); threaded as
  `NScalingHypothesis`/`NPlaneScalingHypothesis`; discharging them is what will introduce the
  (census-neutral, owner-accepted) B8 print — **a follow-up ticket, sized small**;
  (ii) ⚠ `NLabHypothesis` deviates from `BLabHypothesis` twice — abstract-`G` forced (memo
  R6) and the descent orientation clause DROPPED in favour of `imChiN` (the repo's
  `IsLabuteOrientation` is D_R-specific); **dropping a clause makes the binder STRONGER,
  i.e. asks the owner for more — G-Lab-visible, flagged not resolved**; (iii) `nChar_dnX0` is
  load-bearing: every ℤ₂-character kills x₀, so N1 is ν-invisible and memo §3.6's ν(t) = 0 is
  a check that passes, never an equation; (iv) for MC3: the M-side will NOT transpose cleanly
  (N leans on `nUnit_zpowZtwo_injective` = infinite order ⇒ integral x̄₁ pin; on M, χ(B) = −1
  gives only a mod-2 pin ⇒ the B-scaling the memo warns about), but `nMatOf`+`decide`,
  `nCoreMat`, `nGL_factor` are core-agnostic and **`dmClearAuts` has the same four generator
  families, so MCoreMixHypothesis is unsatisfiable for the same reason — MC3 should expect
  it**; (v) for MC5: `nMarkedCorrection` (+ `_of_liftSplit`, `_nuN`) is the Prop 7.2 input,
  and `nCoreIdx_cases` (the rank-(4+2h) letter case split) is new and needed.
- **2026-07-30 (orchestrator, HM6 — G-LAB MOVES: ONE OBLIGATION DISCHARGED):** merged,
  import registered; audit green **3416 jobs**, census 11. `CoreMix.lean` (732 ln, 0 sorries,
  all 11 headlines std-3) + memo `handlemix-core-spike.md`. **Both cores went green,
  including the M side the MC-HM memo had written off.** Verdicts: **N5 + N6 PROVED ⇒
  `NCoreMixHypothesis` is DISCHARGED** (MC1 §8 Decision 2 moves "(B) binder" → "(A) proved"
  for N, at spike cost instead of the sheet's 2–4k lines); **M5 PROVED ⇒
  `MCoreMixHypothesis` WEAKENED** to `⟨M4,M6,M7⟩`, and that residual is **NOT consumed by
  MC5's ν-correction** (MC1 §5.3 needs only M4 *or* M5's free `B_c`, which HM6 supplies over
  ℤ₂) — so MC5 is unaffected. The M-side reversal: MC-HM's 24 failures were all of the *N6
  shape* (move b,c — genuinely dies on `c^{2^α}`); the family M actually needs is **M5**
  (move b,d), which fixes `a` and `c` AS LETTERS, so `a²`/`c^{2^α}` survive literally
  (MC-HM's own V2 lesson one level down). **One lemma covers everything**: for
  `P(m,K) = a^m[a,b]c^K[c,d]` the move-b,d twist is exact for EVERY (m,K), the move-b,c twist
  for K = 0; `M_α = P(2,2^α)`, `N_α = P(2+2^α,0)`; **no B8, no compactness, no θ_w/SL₂** —
  the 2-adic parameter is `zpowZtwo` alone (strictly cheaper than the handle case).
  **The M residual is a STRUCTURAL obstruction, not a failed search**: M4/M6/M7 are exactly
  the non-symplectic directions (mod-2 Witt only), and any relator-preserving free-group
  automorphism is symplectic on H₁ — so they are outside the reach of ANY word-level
  construction. ⚠ **Scoping finding propagated to MC3/MC4 mid-flight**: `Dm/DnRealizes`
  (`HandleMixClear.lean:854,861`) bundle "acts as F" with membership in the HANDLE generating
  set — too narrow for the core stratum; **HM6e** (ν-frame rows, ~200 ln, in CoreMix.lean)
  + **HM6f** (widen `d?ClearAuts`, ~150 ln, in HandleMixClear.lean) are the mechanical fix,
  queued. Owner questions in memo §7: restate M's `hLift` in consumed form (would remove
  `MCoreMixHypothesis` entirely)? — and **HM Q2 is now THE binding M-side question**: the
  transported `ν'(C̄₀) ∈ ℤ₂ˣ`, which needs the compact-M change of variables still missing
  from the vendored sources (errata item 3). Memo §4.3 also corrects a claim this campaign
  made one ticket ago — rides with the errata bundle.
- **2026-07-30 (orchestrator, NC5 — THE R3(a) COMMISSION IS DELIVERED):** merged, import
  registered; audit green **3415 jobs**, census 11, capstones frozen. **`npc_cross_operators`
  is a committed sorry-free theorem printing exactly std-3** — the corrected
  `L_c = A⁻¹+B+BA⁻¹` universal-second-jet identity, quantified over ALL `r : ℕ` and ALL
  `η : ℤ_[2]` (strictly stronger than commissioned; only `2 ≤ α`, `hV2`, `Odd (orderOf u)`,
  `hVu` are consumed). NC4's recipe closed **verbatim, first try, zero errors**. Also landed:
  `hVu_of_simple` (the companion — needed NOTHING outside the closure; prints
  `[propext, Quot.sound]`), `npc_cross_operators_of_simple`, the (α,r,η) = (2,1,1) stress pin
  at the ℚ₂(√−10) procyclic row (merge gate 9), and **two errata-item-5 pins**:
  `lcOp_eq_draft_add_discrepancy` (L_c = the draft's A⁻¹ PLUS B(1+A⁻¹)) and
  `lcOp_eq_draft_of_eq_one` (the discrepancy dies exactly at A = 1) — the refutation is now
  machine-checked in Lean, not just in the search engine. Per memo Q6, `M_c` stays a
  docstring reading (no adjoint corollary). NOTE: NC5's report flags the WNP board note as
  stale — **it was already corrected inline** at the NC1 merge (the dated CORRECTION block
  is present); NC5 was reading a pre-merge view. **NC6 dispatched** (the handle tail + a
  fully concrete-carrier instantiation of the pin). Residual for WNP-c (unchanged): per-module
  invertibility of L_c.
- 2026-07-30 (orchestrator, NC4 outcomes): merged, import registered; audit green **3414
  jobs**, census 11. 451 ln / 30 decls, ALL std-3. **The memo's route held with NO
  deviation** — every hand-computed block value was correct as written, sign and side
  conventions included. Two confirmations: (a) the D-block's evaluated V-part comes out
  literally `A⁻¹•c₀ + B•(c₀ + A⁻¹•c₀)`, and compressed↔expanded agree operator-by-operator
  via `smul_add`/`mul_smul`/`mul_inv_rev` alone — **the S3.2 correction is visibly the two
  conjugators the draft dropped**; (b) the charge quarantine works as designed (`ζ_D` never
  assembled). `npcEBlock_eval` landed as an EQUATION (not an existential). ⚠ **Upstream
  note**: NC4's §0 `Marking.eval_{conj,comm,zpow,profPow,etaPow,omega2Pow,invConj}` belong in
  `GQ2/Dyadic/Word/Eval.lean` (F2's file, which NC4 could not edit) — they live in
  Seams.lean under their natural names; if a later ticket adds them upstream it is a hard
  duplicate-name error, not silent breakage — **orchestrator call at that merge**.
  **NC4 smoke-tested NC5's assembly in scratch (12-line rw chain, std-3) and recorded the
  recipe in Seams.lean's docstring; NC5 dispatched** with it.
- 2026-07-30 (orchestrator, post-credit re-dispatch on OPUS): the authorized work continues
  on opus (the fable model column is now aspirational — read it as "hard seam"). Running:
  **MC4** (RESUME from the green 747-ln salvage — the classification, the GL₂(ℤ₂) block via
  HM3's SL₂ = E₂, the lifting layer, the NLiftSplit assembly), **MC3** (RESTART — the 489-ln
  salvage is a review-or-rewrite draft; get green early), **NC4** (`NpcJet/Seams.lean` — the
  δ/D/E seams; NC2's typed constructors + NC3's rules compose with no bridge), **HM6** (the
  bounded core↔core mixing spike — N-side completion + M-side ansatz/obstruction
  characterization; would discharge a G-Lab binder). Still running from before: **S4.3**
  (simp side). Queued: NC5 (assembly headline) after NC4, NC6 after NC5, MC5 after MC3+MC4,
  S4.4 after S4.3.
- **2026-07-30 (orchestrator, CREDIT INTERRUPTION + NC2/NC3 landings): the Fable-5 usage
  credits ran out** mid-flight, killing MC3 and MC4 (the two fable obligation tickets); the
  owner switched the session model to opus-5. **The commit-early discipline worked**: MC4
  banked 747 green lines in 3 WIP commits (orchestrator-verified: `lake build
  GQ2.Dyadic.MarkedCore.N` = 3001 jobs green) — resumable; MC3 died mid-write with 489
  uncommitted lines that do NOT build, banked as an explicitly-marked UNVERIFIED salvage
  commit (the S1.5 precedent). **NC2 + NC3 landed and merged** (imports registered; audit
  green 3413 jobs, census 11): NC2 = `NpcJet/Defs.lean` 427 ln, all 47 decls std-3, memo
  names confirmed verbatim, **the NC5 headline elaborates against them** (scratch-verified);
  NC3 = `NpcJet/Omega.lean` 414 ln, 29 decls std-3-or-less, **rules 1+2 committed**, with
  rule 2 proved by REUSE (found `GQ2.FoxH.WordLift.sum_pow_smul_eq_zero` already in closure
  — memo risk 6's search paid off). Deltas recorded: NC2 nests the namespace one deeper
  (`GQ2.Dyadic.NpcJet`) to avoid clashing with NC3's generic lemmas; the `y^k` law landed in
  NC2 (memo's map said Omega) — NC3's scope shrank accordingly; `IsEquivariantFactorSet.m_zero`
  is a THEOREM not a field (spell `IsEquivariantFactorSet.m_zero dat hdat` — NC4/NC5 will
  hit this); NC2 left no sorried skeleton (SORRY_ALLOWLIST is orchestrator-owned) — NC5
  states the headline. **Remaining NC lane: NC4 (δ/D/E seams), NC5 (assembly), NC6
  (handles+companion+pin)** — all unblocked.
- 2026-07-30 (orchestrator, NC1 outcomes — **BETTER THAN COMMISSIONED**): memo merged
  (`docs/dyadic/nc-design.md`). The corrected-L_c headline ELABORATES VERBATIM (spike: zero
  errors, one intentional sorry at the assembly); quantification STRICTLY STRONGER than
  commissioned (all r : ℕ, all η : ℤ_[2] — neither r ≥ 1 nor IsUnit η consumed; 2 ≤ α =
  LabuteType.Valid); the refutation is visible in the proof shape (E_{r,η} evaluates to the
  central element with b_q(L_c c₀, c₁)); **both feared gaps are NON-GAPS** (padicOmega2
  additivity unneeded — product-conjugator spelling + zpowHat_mul; reduction rules 1+2
  ALREADY PROVED in the spike at std-3 — norm vanishing needs no semisimplicity). Plan:
  NC2 (defs+kit, opus) ∥ NC3 (ω₂/norm, opus) → NC4 (δ/D/E seams, fable) → NC5 (assembly,
  fable) → NC6 (handles+companion+pin, opus); new plain-import dir `GQ2/Dyadic/NpcJet/`
  (module-rule-forced, avoids WNP reserved paths). Adopted under the blanket (flagged):
  Q1 file map approved; Q2 hypothesis-minimal headline + `hVu_of_simple` companion; Q3
  WNP-a pre-agrees `npcWord`; Q4 the stale WNP spec bullet corrected inline (dated); Q6
  M_c docstring-only. Q5 (timing): **NC2+NC3 dispatched now (opus — parallel, disjoint
  files; lg→dyadic-nc2, wl→dyadic-nc3)**; NC4/NC5 (fable) queue behind MC3/MC4/HM6 slots.
  Timing rec adopted: prove now — no G-1/WW/AX dependence; WNP-c's centerpiece pulled
  forward, not WW duplication. Elaboration frictions recorded for NC2+ (Prod-literal Mul
  shadowing → typed constructors; `CentExt.fib` needs `(c := …)`).
- 2026-07-30 (orchestrator, WL-recon outcomes): memo merged (`docs/dyadic/wl-recon.md`).
  Measured corrections to SQ1's framing: the frozen Γ_R chain is **8615 ln** (not 1855);
  n=1 coverage = mathematics ~100%, Lean text ~25% (WW's structural recursion REPLACES the
  per-factor ledgers); handles ~85% from MC2+HM; the 2287-ln dévissage is **WW3's to do
  ONCE** (the Roe/Devissage clone experiment: 5 branch words ≈ 11k avoidable lines —
  regression-target-not-source, decisively; exception: WW4 CONSUMES the
  presentation-independent Gauss endgame, 1932 ln citable). Spike facts: type-L n=1 forces
  K = ℚ₂ (`by decide`); BOTH candidate L words identify letter-for-letter at n=1
  (wildRelator / wildRelatorR; sole bridge = one norm_cast on IntegerPower). Adopted under
  the standing blanket (flagged): (i) Q2 — **SQ5's full word-theorem restatement MOVES to
  AS4** (module-rule impossibility: Roe/Main is plain, Sanity spec'd module; AS4 is cheaper
  than budgeted since the terminal theorem is hypothesis-free); (ii) Q3 — **WL-c SPLITS
  into c1 (Stokes/Hessian/det/phase, opus, ~420) + c2 (scalar/Hilbert hHilb, FABLE, ~220,
  SCHEDULED FIRST — the only can-fail item)**; revised WL sizing ≈1360 ln across 4 tickets
  with the measured 1.52× overrun factor; (iii) Q5 — WL-a carries a q_K > 2 pin (the n=1
  base is structurally blind to q_K-vs-2 slips); (iv) Q1 — the S2.4 §8.1-inventory
  correction rides with the errata bundle's cover note. **Q4 (fold the target tables into
  WW1/WW3/WW4 and dispatch them early as G-1-independent) = OWNER QUESTION** — the G-1 gate
  text lists WW as held; early release is the owner's call (WL-recon recommends yes; it
  would parallelize wave 2 ahead of R5).
- **2026-07-30 (owner): R3(a) + dispatch authorizations EXECUTED.** Model policy per the
  owner's request: **fable** for the hard seams (MC3, MC4, NC1 now; HM6 + S4.4 queued),
  **opus** for well-specified fills (S4.3, WL-recon) — the boards' original model-column
  philosophy restored now that fable capacity is available; commit-early discipline
  mandatory in every fable prompt. Dispatched HERE: **MC3** (fable, mc worktree
  dyadic-mc — MC-M: Smith–Witt classification + S1/S2 lifting + binder-consuming assembly;
  owns MarkedCore/M.lean; reserved names `m*`/`_m`), **MC4** (fable, ww worktree NEW branch
  dyadic-mc4 — MC-N mirror; owns MarkedCore/N.lean; reserved names `n*`/`_n`; the
  (ℤ/2×ℤ₂²)⋊GL₂(ℤ₂) stabilizer per MC1 §3), **NC1** (fable, lg worktree NEW branch
  dyadic-nc1 — the R3(a) commission: design memo + spike for the corrected-L_c
  universal-second-jet theorem; owns docs/dyadic/nc-design.md), **WL-recon** (opus, NEW
  worktree gq2-dyadic-wl — owns docs/dyadic/wl-recon.md). **HM6** (fable) queued for the
  first freed slot: the rank-four core↔core mixing spike (memo §V7; N-side q-direction
  verified, M-side 24 ansatz failures — the genuinely open seam; a green result removes one
  G-Lab obligation and would discharge the MCoreMix/NCoreMix binders MC3/MC4 are consuming).
- 2026-07-30 (orchestrator, HM5 outcomes — **HM LANE CLOSED**): merged, import registered;
  audit green (3411 jobs, census 11). 814 ln / 52 decls + 18 stress examples, ALL ≤ std-3 —
  measured: NO B3c (chiM/chiN are combinatorial closed forms; dyadicOrientation never
  enters), NO B8. **Headlines `mHandleMixLift`/`nHandleMixLift`**: clearing + χ-preservation
  in one existential, general (α,h), with the standard-marking instantiations non-vacuous.
  **Structural finding**: one pivot slot read two ways — ν'(pivot) unit steers the clearing,
  χ_P(pivot) trivial makes χ-preservation free; the negative rows PROVE Φ_j moves any
  character with a different pivot value ⇒ TRANSPORTED orientations must be checked, not
  assumed (the χ-twin of memo §6.4's residue). Lane inventory: HM1–HM5 = 4839 ln, handle
  stratum = THEOREM for M/N; binders remaining = exactly MC1's S1∪S2 + S3-core-mix (the
  MC5 two-of-three). Deferred with precise framing: the L-family instantiation is BLOCKED
  by SQ1-R1 (the L_sq pivot χ_sq(σ) = S is NOT clear-blind — the reachable-block
  identification must be redone; assigned to MC5); the M-side transported ν'(c̄) unit row is
  a one-line F4/MC5 data check. New repo constructs: `include hA in` (first use, verified on
  rc2); the `endStabilizer` submonoid pattern replacing closure_induction (one-line
  discharge). **MC3/MC4 are now maximally set up** (MC1 skeletons + MC2 + HM1–5 assets +
  adopted G-Lab binders + the MC5 three-way split + the SQ1-R1 correction) — NOT dispatched
  this session (dispatch decision = owner/next session).
- 2026-07-30 (orchestrator, HM4 outcomes — **THE HANDLE STRATUM IS A THEOREM**): merged,
  import registered; audit green (3411 jobs, census 11). 1259 ln / 121 decls, 117 exactly
  std-3, rest ⊆ {Quot.sound}; NO B8, no new axioms. Landed: `exists_frameClear` (the §5.3
  ν-clearing, two-step-per-handle + induction), **`exists_dmClear_nu`/`exists_dnClear_nu`
  (the restated obligation as a THEOREM, both cores, general (α,h))** + the nuM/nuN
  corollaries, and the MC5 split shape (`MLiftSplit`/`NLiftSplit` with
  handle = THEOREM (`mLiftSplit_handle`/`nLiftSplit_handle`), S1∪S2 + S3-core-mix = the two
  BLab-style `def` binders — MC5 supplies two of three via `mLiftSplit_iff`). Adopted:
  Submonoid-not-Subgroup A(P,h) (inverses are generators); the honest scope note (the
  handle BLOCK is proved, the core block stays MC5's); schematic stratum parameters
  (MC3/MC4's frames don't exist yet); the `frameEnd`/`autEnd` Pi-instance barriers
  (engineering note for the lane). Non-vacuity pinned (ν_M(C₀) = ν_N(σ) = 1 — memo §6.4
  residue 2 is a transported-data question only). **HM5 dispatched** (thinner than
  budgeted per HM4's finding: unit rows + polish; the L-family instantiation belongs to
  SqCore and is deferred to the SQ lane with the SQ1-R1 frame caveat).
- 2026-07-30 (orchestrator, HM3 outcomes): merged, import registered; audit green (3409
  jobs incl. the new file, census 11). 1302 ln / 155 decls, ALL exactly std-3 — no B8. The
  complete §5 dictionary landed: frame action + bridges, transvection matrices, Eichler
  elements with N² = 0 and E^n = 1+nN, θ_w-conjugation reaching every 2-adic parameter
  ({n·w⁻¹} = ℤ₂), and **the 2×2 local-ring SL₂ = E₂ argument (mathlib has no elementary-
  generation theorem — proved directly, 5-factor planeDiag decomposition)**; end-to-end
  probe: the group-level τ_c(−1)∘τ_{v_j}(1)∘Φ_j IS frameEichlerU j 1 on the ν-frame, one
  `rw`. Adopted deltas: frames stated against CHARACTERS (MDecomposition/NDecomposition are
  MC3/MC4 items and don't exist yet — the e-row form is a coordinate composition; no memo
  identity failed); the family swap inherited from HM2 (E_j's c̄-coefficient +1 — immaterial,
  §4 realizes every coefficient); E'_j simplified (plain conjugate suffices); ℕ-exponents in
  the θ-conj headlines (valuation split). **HM4 dispatched** (mc, sequential — the
  ν-clearing theorem + the restated obligation + the MC5 hLift split shape).
- 2026-07-30 (orchestrator, HM2 outcomes): merged, import registered; audit green 3408
  jobs, census 11. 830 ln / 94 decls, ALL ≤ std-3 — **no B8, no B3c** (memo V4 now
  measured). `dmMixEquiv`/`dnMixEquiv` assembled as ContinuousMulEquivs (continuity free via
  m/nLiftHom; no pro-2 bookkeeping); the 4-step recipe worked verbatim (packaged as
  `handleWord_update_split` + `commP_handleMixD_mul`); the realized element is the memo's
  §4.4 M-family form (one definition serves both cores — L-family display is its h=1,j=0
  shadow); M-family inverse at general (h,j) DERIVED (`group`-verified two-sided in the
  free group). **Lean-confirmed: the abelian collapse sends both moved letters to c̄−v̄_j —
  memo §5.2's k ≡ k′ cup condition holds identically** (Φ_j is already E_j-like; HM3's
  τ-normalization pins the pure Eichler form). Two rw-frictions recorded for HM3 (the
  higher-order `key n` pattern; unfold named generators up front). **HM3 dispatched** (mc,
  sequential).
- 2026-07-30 (orchestrator, cross-campaign from S3.2): ⚠ **the draft's eq:Ncross is refuted
  as displayed** — machine-verified: `L_c = A⁻¹+B+BA⁻¹ = 1+(1+A⁻¹)(1+B)` and `M_c =
  adj(L_c)`, NOT the draft's `M_c = A, L_c = A⁻¹` (discrepancy `B(1+A⁻¹)`, vanishing iff
  A = 1); the draft's CONCLUSION (L_c invertible on ramified simples) SURVIVES; symbolic in
  r and η. Consequences here: **WNP-b/c's deliverable is now precise** (prove the corrected
  L_c; decide which L_c the field's determinant form demands — that decision also disposes
  of S3.2's four cheaper parked survivors); errata bundle gains item 5. Also: gate G is
  BLIND to E_{r,η} (raw = corrected on every finite target, both evaluators) — the S₃
  twisted-path module is the ONLY separating gate; WC-Npc stays open (second jet exact but
  twisted-path-only; freeze blocked pending an invariant-refinement ramified simple or a
  Fox/norm replacement argument).
- 2026-07-30 (orchestrator, HM1 outcomes): merged, import registered; audit green 3407
  jobs, census 11. 634 ln / 55 decls, ALL std-3-or-subset — **NO B8** (memo V4 confirmed:
  the mixing construction needs no peripheral action). Inventory = the three families
  (handle splitting w/ congr lemmas; the two commP expansions non-simp; exact ℤ₂
  transvections incl. the assembled `{m,n}RelWord_tau_handle{U,V}` rows). **Acceptance
  probe STRONGER than asked: the full HM2-shape obligation is `group`-provable at general
  (h, j) from the committed API** — HM2 reduces to the ContinuousMulEquiv assembly; the
  4-step recipe is in the module docstring. Adopted: the naming convention (Lean suffix =
  the letter that MOVES; memo τ-subscript = the letter whose power is USED — documented
  in-file); the deliberate negative-row absences (no mWord_tau_a/c, no nWord_tau_a — memo
  §5.1 ✗ rows; the M-side ν'(c̄) residue stays live); 634-vs-250 line overage accepted
  (relator-level assembly belongs here so HM3/HM4 consume shapes, not fragments);
  `mem_take/drop_finRange` flagged as mathlib-upstream candidates. **HM2 dispatched**
  (mc worktree, sequential).
- 2026-07-30 (orchestrator, SQ23 outcomes): **`marked_square_core_rank3` is a COMMITTED
  sorry-free theorem** (`GQ2/Dyadic/SqCore/{Cores,Rank3}.lean`, 853 ln, merged, imports
  registered; audit green 3406 jobs, census 11, capstones byte-identical). Prints exactly as
  the memo predicted (headline std-3+B3c+B8; the STRUCTURE carries B3c only — consumers
  mentioning the type inherit no B8; sqWord_eq_drWord is [propext] alone). Adopted: memo
  governs the file-map swap (frame+Gram in Rank3 on DR — the R3 mitigation; bridge in
  Cores); named-generator keying (sqGen/dsqSigma/dsqX0/dsqX1) + bundled `sqCore_cupGram`/
  `sqCore_nu` single-handle theorems; docstring-recorded prints + StressTests-section idiom
  (no #print in committed files); the two local instances restated (local instance doesn't
  export — flagged upstream-de-privatize candidate). n=1 word identification realized at
  pro-2 level (`gammaRPro2EquivDSqZero` via maxPro2Bridge); the FULL word-theorem
  restatement in SQ vocabulary deferred to SQ5/WL-recon (needs the heavy `Roe.Main` import —
  deliberate). **The R2-commissioned obligation is DISCHARGED; L_sq's gate-C park is
  dissolvable pending the S2.7 record flip (after S2.6 lands).** Remaining SQ lane:
  SQ4 Certificate.lean (blocked on MC5), SQ5 Sanity.lean.
- 2026-07-30 (orchestrator, SQ1 outcomes — **THE COMMISSIONED THEOREM ALREADY EXISTS**):
  memo `sq-design.md` merged. **`L_sq`'s rank-3 core IS `GQ2.drWord`** (Roe's `D_R` core;
  the full n=1 word is Roe's `Γ_R` incl. the tame relation) — the two campaigns indexed the
  same core under different names; `main_presentation_literal_roe_unconditional` is the
  hypothesis-free terminal theorem. Orientation = HENSEL (unique ℤ₂-root of `Z³+2Z²+1`,
  already complete in `OrientationRoot.lean`/`ChiR.lean` — this IS the page's C_mark = 3);
  **`bLab` applies DIRECTLY** (BLabHypothesis is specialized to this very core — no new
  instance, no G-Lab item); **spike DISCHARGED `marked_square_core_rank3` in 4 lines**
  (263-ln scratch, 0 errors; prints std-3+B3c+B8, census stays 11). SQ2+ = 4 tickets ≈810
  ln, NO matching-engine port. Rulings (blanket-adopted, flagged): (i) Q1 YES — **SQ23
  dispatched** (one agent, `SqCore/Cores.lean` + `Rank3.lean`, ww worktree branch
  dyadic-sq1); Certificate.lean waits on MC5, Sanity.lean follows; (ii) Q2 ACCEPT B8 in the
  rank-3 discharge (MC2's hypothesis-threading remains the general-K pattern; documented
  asymmetry); (iii) Q3 BOTH — dated correction appended to S2.4's memo (⚠ its §1.1
  "χ(σ)=1 for type L" is FALSE for L_sq — χ_sq(σ) = S, infinite order; MC5 must redo the
  §6.4 mixing analysis in the L_sq frame; compounds MC-HM's L_sq residue) + travels with the
  errata bundle; (iv) Q4 WL-recon ticket AUTHORIZED (Γ_R's frozen word-certificate base
  ≈1855 ln plausibly halves WL-b/WL-c) — QUEUED behind capacity; (v) Q5 (flip L.py gate-C
  records — the park dissolves by the "selected core" clause) DEFERRED until S2.6 lands
  (file contention), then a small ticket. **R2 re-read recorded: nothing favours reverting
  to L_tw** — L_sq's rank-3 word is a THEOREM while L_tw's is verifier-only; the one
  L_sq-only cost is the bounded R1 mixing-frame redo.
- 2026-07-30 (orchestrator, MC-HM outcomes — **SPIKE GREEN**): `HandleMixLift` is **PROVED
  mathematically** (memo `handlemixlift-spike.md`, merged): the [[σ,v₁],u₁] obstruction kills
  only the naive ansatz; the UNIQUE |A| ≤ 6 mixing solution fixes x₀/σ/v literally with
  Φ(P) = P on the nose (Nielsen-reduction two-sided inverse); 2-adic exponents via integer
  powers × diag(w,w⁻¹) conjugation — NO Aut-compactness, NO B8; verified uniformly (L
  collector/tw h ≤ 4; N and M h ≤ 3, α ≤ 4 incl. the second Eichler family). S2.4 §6.6's
  residual gap is EMPTY. **Lean discharge = HM1–HM5 (~900–1400 ln, no new machinery, no
  axiom)** vs 2–4k/core for the levelwise alternative. Rulings (blanket-adopted, flagged):
  (i) memo Q3 = YES — replace the binder by the consumed statement `ν_P ∈ ν'·A(P,h)` and
  DISCHARGE via HM1–HM5 (the §1 binder def stays as fallback until HM4 lands); **HM1
  dispatched** (new file `GQ2/Dyadic/MarkedCore/HandleMix.lean` — Cores.lean stays closed);
  (ii) memo Q4 (HM6, the rank-four core↔core mixing bonus that would remove one G-Lab
  obligation — M-variant fails 24 ansatz forms, N-variant only q-direction verified) —
  **HELD for owner** (new research direction beyond the charter); (iii) memo Q5 = errata
  draft item 1 rewritten CONSTRUCTIVELY (amendment offer, not gap report); (iv) memo Q1
  (is L_sq still live given its shared-letter residue) — DEFERRED to SQ1's landing (the two
  memos together give the owner the full L_sq picture); (v) memo Q2 (ν'(c̄) unit for M) —
  recorded, ties to MC1 Q4 / errata item 3. Consequences adopted: MC5's `hLift` splits three
  ways; `marked_L_core_stabilize` + collector/tw analogues lose `hMix`; S2.5 Flip A
  unaffected (condition is `HandlesFresh`), Flip B still refused.
- **2026-07-30 (owner, via R2 blanket adoption — flagged for override): G-Lab ADOPTED per
  the MC1 memo recommendation** — stay parametrized: `MLabHypothesis`/`NLabHypothesis` +
  `MMixHypothesis`/`NMixHypothesis` remain hypothesis binders (never axioms); the MC3a
  direct-proof spike is AUTHORIZED (MC1 Q1); B8-dependence for the S2 scalings accepted
  (Q2, memo rec); abstract-G quantification confirmed (Q3). **MC5 scope WIDENED to the odd
  (L) family** (S2.4's mapping; = MC1 §9 Q6). Owner's R2 decision on the simp board selects
  **L_sq** as the primary word — SQ1 (rank-3 sq-comm marked-core/orientation theorem,
  design-memo-first) is the commissioned cross-campaign work and lands HERE (simp-campaign
  Lean deliverables rule). Dispatched: **SQ1** (ww worktree, branch `dyadic-sq1`, owns
  `docs/dyadic/sq-design.md`), **MC-HM** (mc worktree, branch `dyadic-mc`, owns
  `docs/dyadic/handlemixlift-spike.md` — the S2.4 Q1 bounded Dehn–Nielsen/Sp-realization
  spike; would settle L/N/M stabilization at once; binder shape `HandleMixLiftHypothesis`
  BLab-pattern). MC3/MC4 queue behind capacity (per MC1: stabilizer classification is
  unconditional linear algebra and can land first; lifting consumes the binders).
  **Packet errata draft** written at `docs/dyadic/packet-errata-draft.md` (owner sends):
  proof.tex:757 Nielsen remark incomplete (S2.4 Cor 6.3.1); §14 completion criterion
  implicitly assumes the S3 stratum (MC1 §7.3); compact-M marked CoV missing from vendored
  sources (MC1 §7.2); Prop 8.1's implicit r ≥ 1 (F4).
- 2026-07-29/30 (orchestrator, AX4-b + AX4 FLIP — **AXIOM LANE CLOSED**): AX4-b landed (all
  60 decls std-3; structure per memo §2.3 verbatim, K/R implicit so §2.4 text elaborates;
  `card_gr_zero` route for the ⊥ f-computation — cheaper than the memo's step 1; W₂
  threaded as hypotheses at ⊥ (naming the axiom is forbidden below the layer; "closed
  subgroup of pro-p is pro-p" absent from repo — memo-sanctioned follow-up); memo §2.5's
  f-consistency stress NOT landed (needs the norm-power identity, absent — R3 caveat
  recorded); 3 name-distinct Aux restatements with dedup notes). Then atomic flip 890a960
  (amended once: the literature-axioms B10 row's real spelling differed from the step-8
  regex — row added, commit amended pre-audit): **B10-K live, census 10 → 11**, same eight
  surfaces as AX3's flip + the TWO new Axioms.lean imports (UnitFiltration +
  OrientedTameBundle; closure grows by exactly 3 files, no cycle — AX4-b verified).
  Post-flip audit green: census 11, capstones frozen 9-set, twins identical, 3404 jobs.
  ⚠ recorded: every B10-K consumer also prints B5+B5-K (type mentions markedRecipAt —
  inherent to the owner-approved parametrization; check-5 unaffected, ℚ₂ capstones consume
  neither). **The axiom lane's endstate is reached: exactly two new axioms (B5-K, B10-K),
  both owner-approved at G-AX, census 9 → 11. Consumers may now migrate binders → axioms;
  the interim binder spellings in LG5/F4/MC-lane remain valid (satisfied by the axioms).**
- 2026-07-29 (orchestrator, AX3-b + AX3 FLIP): AX3-b landed (full build 3403 green pre-flip,
  census 9 unchanged by the bundle, 0 new axioms; §3/§4 quantify over arbitrary
  `LocalReciprocity` — MANDATORY, the file sits below Axioms.lean; auxiliary axiom-free
  `MarkedPair` hosts the §1.5 derivation and IS the R2 mock's home; `epsilonOf : Bool` per
  F1's convention; R6 instance pin `GalKsub` confirmed real; **Q7 side-answer found**:
  mathlib's rank-one norm identification = `Algebra.norm_algebraMap` +
  `IntermediateField.finrank_bot`, recorded in the §4 docstring). Consumer probes: F4
  instantiation elaborates as REAL theorems (Branches' import closure has no Foundations —
  importable); LG4c/LG5's `InvolutionFieldPackage` norm clause is a per-tower-step statement
  served by `norm_partner_of_hasEqualNormValueGroups` — NO change needed in their files.
  Then the **atomic AX3 census flip (6320493)**: B5-K `markedRecipAt` into Axioms.lean;
  EXPECTED_AXIOMS 9→10 with the capstone census FROZEN at the nine ℚ₂-side axioms (audit
  message decoupled — K-side axioms must never appear in ℚ₂ capstone prints);
  ledger/probe/closure-script/yaml/comparator rows; literature-axioms B5-K row (⏳ PDFs
  unverified per owner Q7); memo postscript. **Post-flip audit green: census 10, capstones
  at the frozen 9-set, twins identical, check_dyadic green.** AX4-b dispatched (ww worktree,
  branch dyadic-ax4b): the `OrientedTameQuotientK` structure + derived layer per ax4-proposal
  §2/§5 + owner answers, quantified over an arbitrary bundle (same below-Axioms discipline);
  AX4 flip (census 10 → 11, B10-K) follows its landing.
  only pair never co-built pre-merge) collided on exactly ONE duplicate declaration,
  `phiResK_mapCoeff1` (both retyped the same ℚ₂ lemma with identical statements) — pj build
  caught it at import time; **orchestrator integration fix on `dyadic`**: deleted Ramified's
  copy, added `import GQ2.Dyadic.LocalGauss.ReadPerOrbitK` (LG4c's = canonical per the
  permanent-home convention); full audit re-run VALID and green (3401 jobs, census 9; the
  immediately-prior check-script pass was stale-olean and is disregarded). Process note for
  future parallel same-lane dispatches: give each agent a reserved-name list or require a
  lane-prefix on shared-model retypes. **LG5 dispatched** (lg worktree branch `dyadic-lg5`
  re-synced post-fix): Main.lean assembly of packet Thm 6.15 per LG4b's composition recipe +
  LG4c's adapter note + the cup11Fun bridges; regressions n=1 (both signs, rfl where
  possible), n=2 unramified +1, ramified +1 at every n.

**Owner decision sheet (2026-08-01, CURRENT):** `~/claude/handoffs/gq2-dyadic-owner-decisions-2026-08-01.md` — A: the two items actually waiting (ASK lane assignment, errata send); B: five riding decisions flagged for override; C: four open-no-deadline items; D: the gate calendar. Supersedes the 07-30 sheet (all of whose items are resolved).
**Session handoff (2026-07-30, Fable-credit interruption):** `~/claude/handoffs/gq2-dyadic-campaigns-2026-07-30.md`.

## Obligation tracker

| obligation | tickets | status |
|---|---|---|
| SD-n | SD1 ✓ → SD-R1/R2/R3 ✓ → SD2 ✓ → SD3 ✓ | **CLOSED at the generic level 2026-07-31**: `GQ2.Dyadic.thm_4_2_of_sourcesN` is a sorry-free theorem printing **exactly std-3 — zero B-axioms** (the frozen model needs std-3 ∪ {B1,B6,B7,B9,B11a}; the B-set enters only through the record instantiations); n=1 regression = `thm_4_2`'s exact statement, rfl-level, byte-identical print; #Sur + reconstruction corollaries std-3. Remaining is NOT SD work: ASK supplies the `G_K` record + `hq0`/`hqe`/`hnuP` + the two §10 instantiation-side conditions |
| MC-M | MC1 ✓ → MC2 ✓ → MC3 ✓ → MC5 ✓ | **theorem-complete-modulo-binders 2026-07-31**: classification + matching + certificate all theorems, all std-3, zero census citers; residual = `MMixHypothesis` + S2 scaling + the compact-M CoV datum `IsUnit ν'(C̄₀)` (errata item 3) |
| MC-N | MC1 ✓ → MC2 ✓ → MC4 ✓ → MC5 ✓ | **theorem-complete-modulo-binders 2026-07-31**: residual = EXACTLY `NScalingHypothesis` (S2 unit scaling; S3 discharged by HM6ef) + pair-unimodularity marked datum |
| LG-K | LG1 ✓ → LG2a ✓ → LG2 ✓ → LG3 ✓ → LG4a/b/c ✓ → LG5 ✓ | **CLOSED at Lean level 2026-07-29** — `GQ2.Dyadic.local_gauss_K` (packet Thm 6.15) sorry-free at census 9; residual surface = EXACTLY the AX3/AX4 binders (AX4 → `tameFK`/`htameFK`/`hfac`; AX3 → `InvolutionFieldPackage` + `(k₀,htriv,hker₀)` + `(g₀,hg₀,hg₀rt)`), replaced at G-AX; AS1 consumes `local_gauss_K` + `ramifiedCertificateOfSubtype` and drops `DyadicLocalInput.eulerChar` for `card_H1_eq_of_markingK` |
| ⚠ CB (count bridge) | CB1 ✓ → CB-S (gate) → CB-P/CB-0 → CB-1…CB-6 | **NEW LANE, opened 2026-08-01** — AS1 found the five branch lanes closed at certificates while `SourceDataN` consumes counts, with no owner; CB1 measured it at ~10–13k generic (vs ~36k cloned) and **promoted WW3b's non-degree-generic count-clause warning to this tracker as the spike's target**; the pro-2 half is Labute-free (no G-Lab) |
| WC-N0 | F2 ✓, WW1–WW5 ✓ → WN0-a ✓ / b ✓ / c ✓ | **word-certificate layer COMPLETE 2026-07-31** (the pilot lane, end-to-end at Def 9.1 items (1)–(6); remaining = AS1 assembly + the AS2 √−2 instance) |
| WC-M0 | F2 ✓, WW1–WW5 ✓ → WM0-a ✓ / b ✓ / c ✓ + WM0-d ✓ | **word-certificate layer COMPLETE 2026-08-01** (both projector branches + the S4.1 §9.4 order-rejection formula with its 𝔽₁₆ pin + **the final single-equation assembly at both branches, √2/√5 end-to-end**; the seventeenth-root pin is a `QuadraticFp2` API item, out of lane) |
| WC-Npc | F2 ✓, WW1–WW5 ✓ → WNP-a ✓ / b ✓ / c ✓ | **word-certificate layer COMPLETE 2026-08-01** (the corrected `L_c` row, end to end; Hessian by assembly over the NC lane's theorem; `L_c` per-module invertibility closed with the r-dichotomy finding; remaining = AS1 assembly + AS3's per-field kernel check) |
| WC-Mpc | F2 ✓, WW1–WW5 ✓ → WMP-a ✓ / b ✓ / c ✓ / d ✓ | **word-certificate layer COMPLETE 2026-08-01** — the hardest word, end to end: `Sh_M` on the displayed alphabet + the certificate shrink, the σ-column coincidence lemma, both jets of the hat copy zero, `mpcCopiesCancel` with no surviving T-dependent central term, the Stokes family/endpoint/duality/Grams, and the linear row's one-entry collapse; **MERGE GATE 9 CLOSED**. Residual is all AS-lane: `hsimp` per-simple-module duality, WW4 items 3 (per-χ shifts) and 5 (`HessRelZTarget`, needs the unowned NpcJet↔WordCoh bridge), the cited gate-F witness, and P4's central clause per module (assumed — the parity escape is not Lean-able at the PWord layer) |
| WC-L | F2 ✓, WW1–WW5 ✓ → WL-a ✓ / b ✓ / c ✓ | **word-certificate layer COMPLETE 2026-08-01** (L_sq end to end; n=1 IS Γ_R; handle stability as an AddMonoidHom factorization; **`hHilb` DISCHARGED as a theorem**, both sides of packet item (5) on the same normal form; remaining = FD1's three field facts (in flight) + AS1/AS4) |

## Wave 0 — foundations (lane F, worktree `gq2-dyadic-f`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| F0 | campaign setup: branch, worktree, refs, surveys, plan, board | — (orchestrator) | `docs/dyadic/**` | — | **done 2026-07-28** |
| F1 | parameters, semantic generators, markings, branch data | opus | `GQ2/Dyadic/Parameters.lean` | — | **done 2026-07-29** (f7c8d05 → merged; 906 ln, 163 decls, 0 sorries, std-3; module-style; η:ℤ₂ˣ + etaUnit hook, ε:Bool; Marking n FunLike + n=1 equivQ2 adapter; equivFin fixes Fox column order; import registered by orchestrator; independently re-typechecked) |
| F2 | reflected profinite word syntax + ω₂ finite evaluation | opus (was fable) | `GQ2/Dyadic/Word/Syntax.lean`, `GQ2/Dyadic/Word/Eval.lean` | F1 | **done 2026-07-29** (6882edb → merged 25e0953, imports registered c9da9dd; 684+772 ln, 0 sorries, std-3 on 37 decls; **etaHatZ BUILT** (~110 ln on Zhat — no gap, no hypothesis threading); quadruple generic (`eval_eq_evalFin`, `ResolvedAt`/`_of_dvd`, `map_eval*`, `eval_map_eq_one_iff`) + `eval_subst`/`eval_pro2`/`eval_killWild` soundness + Gate-B T1/T2 as theorems; n=1 Γ_A stress by `rfl` + zmod8 genuine-ω₂ pin; wave-boundary audit green (3388 jobs, census 9, check-5 ran); z2pow ratification + gotchas in log) |
| F3 | tame quotient at general q + boundary specializations + relative Goursat | opus | `GQ2/Dyadic/{TameQuotientK,TameBoundary}.lean` (split per AX4 Q4) | F1, F2 | **done 2026-07-29** (d8338ca+2bbce88+e23facd → merged, imports registered 456843a; 2017 ln, 0 sorries, 143 decls swept std-3 (B5/B10 do NOT leak despite BoundaryFrame import); audit green 3394 jobs; leaf closure = STRICT SUBSET of Axioms.lean's 31 modules, mock-AX4 elaboration green — **AX4 R5 discharged**; `tq_two_equiv` is literally `refl` (R7 closed, no second tame copy); mandated exports landed (+`[DiscreteTopology H]` on gen_tq_quotient); Lem 3.1/3.2/3.3 + Prop 3.4 (universal-property form) + Thm 3.5; ⚠ general-q center correction + AX4-memo arithmetic fix in log) |
| F4 | arithmetic branches: (C,I,λ,γ), sign-row exclusion, √-10 corollary | opus | `GQ2/Dyadic/Branches.lean` | F1 | **done 2026-07-29** (5d4cddf on `dyadic-f4` → merged, import registered 1de39d6; 848 ln, std-3 on all 37 decls (no literature-axiom leaks), audit green 3389 jobs; `CyclotomicFrobeniusDatum`+`MarkedSplitting`, Prop 8.1 via `classification_of_even`, Cor 8.2 √-10 `(r,ε,η)=(1,1,1)` pins, both-directions η adapter, ε-∀-quantified exhaustiveness + `eps_both_occur`; **r=2 mock bundle with u⁻¹ swap discrimination**; MarkedRecip clause = `unramified_of_even` binder (census untouched, pre-G-AX auditable); CoV gap NOT hit; findings in log) |
| F5 | finite-target sanity harness (python; incl. the retired `rel_minus10` regression row + mutant rows) | opus | `scripts/dyadic_sanity_counts.py` | — | **done 2026-07-31** (74fdd22 → merged; 593 ln, 16 rows green in 3.4 s, deterministic (3 runs byte-identical, hash-seed-proof); D5 hook auto-activated (F6 pre-wired the path — no script edit); 5 frozen quadratic rows + retired-√−10 regression row + draft-§7.3-√10 pointwise-agreement row + 8 mutant rows, mutation-tested with teeth; ⚠ THREE FINDINGS adopted — forward-E_m is F5-UNREJECTABLE (see log + WM0 spec correction), the ref script's d = 10 word was the draft word not the frozen row (re-pointed count-neutrally), counts are blind to 3 of 4 mutants (pointwise/witness modes used instead); Npc (2,1,1) pin 6/1568/120 banked for WL-a/WNP-a) |
| F6 | gates infra: `check_dyadic.sh`, allowlist workflow, docs index link | opus | `scripts/check_dyadic.sh`, `docs/README.md` (one line) | — | **done 2026-07-29** (1d6fd7d → merged; check_dyadic.sh 289 ln: D1 delegate + D2 obligation guard (continuation-line-aware, fails on untracked) + D3 sign-row guard (declarations only) + D4/D5 WW5/F5 hooks; all green 2.2s; docs index line added) |

**Ticket specs.**
- **F1**: `FieldParameters` (`n`, `f`, `qK = 2^f`, `1 ≤ n`), `LabuteType (L | M α | N α)`
  (`2 ≤ α`), inductive `Generator n = sigma | tau | wild (Fin (n+1))` (semantic, not bare
  `Fin (n+3)` — prevents coordinate-order mistakes), `Marking n G` (`Generator n → G` bundled
  with dot-notation letters), `Marking.map` functoriality, numeric conventions
  (`m = 2^(α−1)`, `p_α = 2 + 2^α`, `s = 2^r`, `p = ε·2^(r−1)`), and the **five-row branch
  datum** (L | N0 | Npc r≥1 η∈ℤ₂ˣ | M0 | Mpc r≥1 η odd) — the sign row does not exist
  (packet Prop. 8.1; plan §1 table). `n = 1` adapter: `Generator 1 ≃` the old 4-generator
  `Marking` of `GQ2/Words.lean:66` (σ,τ,x₀,x₁ ↔ sigma,tau,wild 0,wild 1). Acceptance: builds
  green, no axioms, adapter round-trips by `decide`/`rfl`.
- **F2** (**API freeze at G1 — everything downstream consumes this**): inductive `PWord (Gen)`
  with constructors `one | gen | mul | inv | conj | comm | zpow (ℤ) | z2pow (ℤ_[2]) |
  profPow (Zhat)`; `x^{-g}` is sugar for `conj (inv x) g`, never an exponent (packet Rem. 2.3).
  Denotations: (i) into any `[CompactSpace][TotallyDisconnectedSpace]` topological group via a
  marking, using `zpowHat` (`GQ2/Zhat.lean:181`) for `profPow`; (ii) into any finite group via
  packet Lem. 2.2 (`g^{ω₂}` = 2-primary component; reuse `omega2Exp`/`powOmega2`
  `GQ2/Words.lean:42,49` + `GQ2/Omega2.lean` congruence API). Prove once, generically, the
  quadruple the ℚ₂ code hand-writes per word (recon/wc-survey §1c): profinite/finite agreement
  (`map_zpowHat_omega2` `GQ2/Zhat.lean:253` pattern), ℕ-exponent form + `_of_dvd` bridge,
  naturality under `ContinuousMonoidHom`, and evaluation-through-quotient. Substitution
  operators for the two boundary specializations (kill-wild: `wild i ↦ 1`; pro-2: `tau ↦ 1`,
  `profPow ω₂ ↦ id` on σ-letters). δ-letter `δ_i = (x_i τ)^{ω₂} x_i^{-1}` and `σ₂ = σ^{ω₂}` as
  derived syntax. Stress: re-derive one existing Γ_A letter ledger entry (e.g.
  `GQ2/GammaA.lean:107-139` shape) from the generic theorems at `n = 1`; zmod8-style genuine-ω₂
  pin (à la `wildValueR_zmod8` `GQ2/Roe/Words.lean:244`).
- **F3**: `T_q = ⟨σ,τ | τ^σ = τ^q⟩_prof` for `q = 2^f` (generalizing `Ttame`
  `GQ2/BoundaryFrame.lean:120` / `GQ2/TameQuotient.lean:21` which hard-code q=2 — new file, do
  not edit the ℚ₂ ones); packet Lem. 3.1 (tame inertia pro-odd: conjugate ⇒ equal order ⇒
  `gcd(m,q)=1`), Lem. 3.2 (`ker ν₂` pro-odd), Lem. 3.3 (`O₂(T_q) = 1` via the
  `C_{q^{2^k}−1} ⋊ C_{2^k}` quotients — the order of `q` mod `q^{2^k}−1` is exactly `2^k`),
  Prop. 3.4 (tame + maximal-pro-2 specializations of an admissible `Γ_R`, via F2 substitution
  operators), Thm. 3.5 (joint boundary surjectivity = relative Goursat over `ℤ₂`: pro-odd vs
  pro-2 common quotient is trivial). Model files: `GQ2/Tame.lean`, `GQ2/Subdirect.lean`.
- **F4**: `CyclotomicFrobeniusDatum` (`r`, `λ : C →* Multiplicative (ZMod 2^r)` surjective,
  `I = ker λ`, `γ` coset with `λ γ = 1` — draft §2 eq. 2.1–2.3); the **data-level part of
  packet Prop. 8.1**: for `C = ⟨−1⟩ × ⟨u⟩`, `λ(−1) = ε·2^{r−1}`, `λ(u) = η`: η even ⇒
  `r = 1 ∧ ε = 1 ∧ ker λ = ⟨u⟩`; the field-interpretation clause ("hence K(i)/K unramified")
  is stated against the AX3 `MarkedRecip` interface as a hypothesis-shaped corollary (no new
  axiom here). Packet Cor. 8.2: `ℚ₂(√-10)` parameters `(r,ε,η) = (1,1,1)` — the ℤ₂-arithmetic
  (`u = (−3)^{-1} ≡ 5 (mod 8)`, `(−2)/5 = (−10)/25` square) as concrete lemmas. Exhaustiveness:
  the five-row branch datum of F1 covers all `(type, r, ε, η)` with η odd in the M-procyclic
  row (no sign row).
- **F5**: port `refs/check_dyadic_current.py` into `scripts/dyadic_sanity_counts.py` (repo
  conventions per `scripts/roe_sanity_counts.py`): corrected quadratic-field words vs expected
  table (S₃: 6,6,0,6,6 · D₈: 1568×5 · A₄: 120,120,480,120,120 for d = −2,2,5,10,−10), the
  √-10 procyclic-vs-relative-norm agreement, and **mutant rejection** rows (wrong conjugation
  side, un-reversed `E_m`, sign-row word) so transcription errors in wave 2 fail loudly.
  Regressions only — never cited by a proof.
- **F6**: `scripts/check_dyadic.sh` = `check_axioms.sh` + obligation-grep (the nine obligation
  ids and their Lean names must never occur in an `axiom` declaration) + hook for the WW5 hash
  check + python sanity invocation; document the per-ticket `SORRY_ALLOWLIST` workflow at the
  top; add the `docs/dyadic/` line to `docs/README.md`.

## Wave 1 — four parallel lanes + AX

Gate **G1** (owner or orchestrator API review of F1+F2) before SD2/MC2/LG2/WW1 start;
SD1/MC1/LG1 (design memos, read-only vs Lean) may run immediately.

### Lane SD — SD-n (worktree `gq2-dyadic-sd`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| SD1 | design memo: two-sided degree-n source record | fable | `docs/dyadic/sd-design.md` | recon/sd-survey, G-1 ✓ | **done 2026-07-31** (3c1a74b+c978cb2 → merged; 766-ln memo; **structural discovery: the §4–§9 generic machinery is typed at the concrete ℚ₂ boundary** — SD-n is a boundary-abstracted CLONE of the b-typed recursion spine (≈9.1k ln, LG1 "in-place is A6-incompatible" precedent), frozen-file edit list **EMPTY**; n=1 bridge DEFINITIONAL (probe P1: `boundarySubgroupQ 2 nuTwo = boundarySubgroup := rfl`); deep layer (VLiftCount master count, descent/keystone/Fourier, §§5–7, Reconstruction) reused untouched; §6 = the WW4 phase-interface baseline (RATIFIED, Q7); Q1–Q7 adoption calls in log; ⚠ packet-citation off-by-one nit → errata cover note) |
| SD-R1 | spine clone I: frame layer + Covers/Partition/Recursion + Block trio + Prop 7.4 (SEAM A) | opus | `GQ2/Dyadic/Recursion/` (part I) | SD1 ✓ | **done 2026-07-31** (0d8ee17…80b1341, 10 commits one-per-file → merged, 10 imports registered; **2788 ln, every decl std-3 and PRINT-EQUAL to its model**, 0 sorries, frozen-file edit list EMPTY as designed; 1751 ln vs the 3050 budget (57%) excluding the unbudgeted SEAM-A work; **SEAM A DISCHARGED** (`PropSevenFour.lean` — only `hv_average_helperK` does real work, exactly the four ruled name swaps; `lemma_7_2`'s five head binders measured entirely decorative → `lemma_7_2_core`); **SEAM B threaded** as binders `hrel2`/`hrel2HV` on the six Block productions, VERIFIED FREE at q = 2 (`tame_rel_map_q` elaborates — n=1 regression untouched); the two expected omega seams are downstream (SD-R2/SD-R3), part I hit zero; **Fourier.lean needs NO clone** (10/10 decls boundary-free, consumed by import); `SourceNumerics` landed verbatim with the three one-line n=1 bridges SD2 owes; scope adjustments adopted → SD-R2/R3 rows; survived the session-limit kill with 6 files already committed) |
| SD-R2 | spine clone II: §9 Terminal/Induction + MStageCount + SEAM B | opus | `GQ2/Dyadic/Recursion/` (part II) | SD-R1 ✓ | **done 2026-07-31** (8463b5a…b30ad41, 5 commits → merged, 4 imports registered; 1654 ln vs the 2200 budget INCLUDING the unbudgeted 457-ln SEAM-B file (spine alone 54%); 33/33 decls std-3, 0 sorries, edit list EMPTY; **SEAM B FULLY DISCHARGED**: `ActsThroughTameQ q` + `kappa0_exists_tameK`/`kappa0_existsK` + general-q siblings via `_of_odd_normal` + the PJ1 leaves (the caution honored), all six threaded binders REMOVED, `actsThroughTameQ_two` is `rfl` and q = 2 typechecks DIRECTLY against the frozen def; the predicted omega seam VERIFIED then fixed (`Nat.eq_of_mul_eq_mul_left` at `hcS` — SD3 feeds `homScalar_pos`); the other two cancellations correctly did NOT move (the 2 of (139) is degree-independent); three unexpected seams absorbed (`tame_two_nilpotentK` fourth exponent pin; ~110 ln of private-helper copies; **`LiftsOverK` landed EARLY** — SD-R3 imports, never redefines); ⚠ two stale-docstring finds in frozen ℚ₂ files (KappaNormalForm:323/394 + Induction:86 cite decls that no longer exist; Induction:243 cites a moved path) → internal docs-cleanup queue, NOT the packet bundle) |
| SD-R3 | spine clone III: Phase140 + RStage + bridges + generic-Prop89 + Block/RStage move-ins + VLiftCount vH-wrapper | opus | `GQ2/Dyadic/Recursion/` (part III) | SD-R2 ✓ | **done 2026-07-31** (9eb094f…8487aa6, 9 commits → merged, 8 imports registered; 1968 ln (69% of budget; 58% excl. the one over-run), 41/41 decls std-3 print-equal-or-smaller, 0 sorries, edit list EMPTY; **HEADLINE: `closedRecursionK_of_source` prints std-3 where its model needs B6+B7** — the two-sided refactor removes those axioms from the spine structurally (they re-enter only via the supply package); predicted omega seam discharged (`nPhaseK_eq_of_strata`, positivity-cancel at threaded `hcS`, stated over two different Γ₁/Γ₂); seams absorbed: the "thin" vH-wrapper was NOT thin (~130 ln of private-chain copies → re-exported once as `masterCountRaw`), the two-`sign`s ambiguity (⚠ CONVENTION for all future clones: do not `open QuadraticFp2` in sign-carrying files), `rhoPrimeK_surjective` rescued from the instantiation-named `Half139Local.lean` (budget-grep false negative); **THE SPINE CLONE IS COMPLETE** (SD-R1+R2+R3 = 22 files ≈6.4k ln); SD3 consumption chain fully wired (exact names in report); survived the second session-limit kill with 7 files banked) |
| ASK | K-side `*Local` supply package (the G_K record instantiation leaf pack; **SCOPE SHRUNK by SD-R3**: `prop_8_9_of_inputs`/`prop_8_9_of`/`prop_8_9_of_source`/`prop_8_9` + `rhoPrime_surjective` need NO clone — remove from budget; B6/B7 enter HERE, not in the spine) | opus | `GQ2/Dyadic/Instances/KSupply.lean` (name provisional) | SD1 ✓, LG5 ✓ | **LANE SETTLED 2026-08-01 (owner, in session): AS lane** — `GQ2/Dyadic/Instances/KSupply.lean`. The differences were file path, worktree and board row only (LG5's endpoint composes with AS1's record friction-free, so the package needs no LG internals); the one real consideration is that **LG-K is CLOSED on the obligation tracker and reopening it to hold new work would muddy that record**, while this is instantiation work, which is the AS lane's purpose. Queued behind CB-1 |
| SD2 | `SourceNumerics n` + parameterized record + n=1 adapters + `sourceF_N` | fable | `GQ2/Dyadic/SourceDataN.lean` | SD1 ✓, SD-R1–3 ✓ | **done 2026-07-31** (1b09302 → merged, import registered; 524 ln, 14 decls, 0 sorries, NO `decide`; 21-field record on the abstract slot with the hZcard shape rule honored and the 12 dropped fields dropped; **ALL THREE n=1 adapters DEFINITIONAL** — `sourceA_N_b`/`sourceR_N_b`/`sourceF_N_b` are `rfl`, incl. the load-bearing probe `blockEnrichmentDK … = blockEnrichmentD … := rfl` (every ∃-spec boundary-free ⇒ `Exists.choose` agrees by proof irrelevance — NO enrichment transport); prints EQUAL to the frozen models' (sourceA std-3; sourceR +B3c/B5/B8; sourceF +B1/B6/B7/B9/B11a = thm_4_2's own set — packaging costs zero axioms); only non-rfl = the two expected §1.4 value bridges (2-3 ln each via SD-R1's Numerics lemmas); `SourceMarking` SKIPPED per the Q2 fallback's own condition (no canonical marked points on the abstract slot — documented); `sourceF_N` gained `(R, horient)` + two instance binders (memo §3.1's migration — ASK expects the K-analogues); ⚠ two consumer gotchas recorded: `GQ2.Dyadic.GammaR` shadows frozen `GQ2.GammaR` (write qualified) + lambda instance-implicit binding in gaussZ witnesses) |
| SD3 | two-sided degree-n induction + ℚ₂ regression | opus | `GQ2/Dyadic/ThmFourTwoN.lean` | SD2 ✓ | **done 2026-07-31** (4eced35…61f4e56 → merged, import registered; 798 ln, 26 decls, 0 sorries, NO decide; **`thm_4_2_of_sourcesN` prints EXACTLY std-3 — zero B-axioms** (model needs +{B1,B6,B7,B9,B11a}); `prop_8_9_of_sourcesN` compiled FIRST TRY (zero resisting seams, both positivity-cancels fed `SN.homScalar_pos`); **n=1 regression `thm_4_2_via_N` is a single application** — byte-identical binders, conclusion AND axiom print to the frozen `thm_4_2`; bonus Γ_R regression under `hBLab`; #Sur + reconstruction corollaries std-3; ~130 ln §10-frame K-clone absorbed (memo assigned, spine lacked); `boundaryFrameK` rfl-inverse added; ASK interface note: `htame`/`hwild` stay instantiation-side — NOT record fields; SD-n tracker row FLIPPED) |

- **SD1**: starting from `recon/sd-survey.md`, fix the exact parameterization: (i) the
  `SourceNumerics n` field list (packet §11: `homScalar = 2^(n+2)` replacing `hom8 = 8`
  `GQ2/SourceData.lean:131`; `z1Simple = |V|^(n+1)` replacing the `^2`s at :143/:174/:217;
  Gauss magnitude exponent `n·d/2` + sign `ε_K(V)` replacing `∓2^m` at :235/:259; `cardH2 = 2`
  stays); (ii) the two degree-one **type** fields (`Ttame` → F3's `T_q`; `PiBd` → the branch
  core from MC2, or an abstract marked-pro-2 slot so SD does not wait on MC); (iii) the
  **two-sided** restatement (packet Thm 11.1: `S₁, S₂` both records — the current B-side
  `*_local` lemma pack `ThmFourTwo.lean:128-131, Prop89Close.lean:349-357` becomes the
  `G_K`-record instantiation supplied later by LG/AX); (iv) which literal shapes inside
  `lemma_8_3` (`SectionEight/Partition.lean:209`) and `ClosedRecursion`
  (`SectionEight/Recursion.lean:383-431`) become parameters, with the minimal-diff edit list
  for frozen ℚ₂ files (wrappers keep names; byte-identical capstone axiom prints — plan A6);
  (v) plain-import placement (recon §5). Owner-visible deliverable; orchestrator reviews
  before SD2.
- **SD2**: implement per SD1. `n = 1` instance must reproduce `BoundaryMaps.sourceA`
  (`GQ2/SourceData.lean:297`) and `Roe.sourceR` (`GQ2/Roe/Main.lean:388`) definitionally
  (adapters, `rfl`-level where possible). Full build green including all ℚ₂ capstones.
- **SD3**: thread the strong induction (`ThmFourTwo.lean:386`, lanes at :104/:290,
  `SectionNine/Induction.lean:503` untouched) over the parameterized two-sided record;
  conclusion `#Sur(S₁,G) = #Sur(S₂,G)` for every finite `G` + reconstruction corollary via the
  existing `Reconstruction.lean` API. Regression: `thm_4_2` (:443) still derivable as the
  `n = 1` specialization; `scripts/check_axioms.sh` check 5 green.

### Lane MC — MC-M, MC-N (worktree `gq2-dyadic-mc`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| MC1 | design memo: rank-four frames, Smith–Witt stabilizer generators, lifting strategy | opus (was fable) | `docs/dyadic/mc-design.md` | recon/mc-survey | **done 2026-07-29** (a2ed4c5 → merged a296a7a; 876-ln memo: closed-form frames+orientations for both cores (M = ℚ₂ re-index under 2↦m, N = new no-forced-row frame), 7/6 Nielsen families, **three-strata lifting** (S1 Nielsen ✓ / S2 via B8 / S3 mixing = Labute content → `MMixHypothesis`/`NMixHypothesis` binders), G-Lab sheet rec = stay parametrized; ⚠ torsion-premise correction + compact-M CoV gap + packet-§14 criterion flag — see log; owner Qs 1–6 in memo §9) |
| MC2 | presented cores D_P, characters, abelian 4-frames | opus | `GQ2/Dyadic/MarkedCore/Cores.lean` | MC1, F1 | **done 2026-07-29** (7ccb3b2 → merged, import registered; 1907 ln, 0 sorries, 30 headline decls std-3 — **B8 threaded as explicit `PeripheralCyclotomicAction` hypothesis, census axiom NOT consumed** (enters only at MC3/MC4); audit green 3394 jobs; **memo closed forms verified EXACTLY incl. uniqueness** (no-Hensel confirmed); α-independent cup Gram both cores; mod-4 `diagCoeff` rule + `IsCupCocycle` layer = the reusable exponent asset; both §10 assets landed (`IsFreePro2Pair`, `peripheralTriple_scaling` ×4 instantiations); deviations + 2 infra gaps + stale-comment find in log) |
| MC3 | **MC-M**: classification + lifting for `M_α` (uniform in α) | fable→opus | `GQ2/Dyadic/MarkedCore/M.lean` | MC2 | **done 2026-07-30** (a059a6d → merged, import registered; 1748 ln, 0 sorries, **all 150 decls ≤ std-3, ZERO B8/B3c citers**; audit green 3418 jobs; salvage triaged (all 489 ln kept, ~35 rewritten — the file had **10** errors, not the 5 reported; the stale docstring advertised four decls that never existed and was rewritten); `mStabilizer_classification` = ∃! over `MStabParam` + `mNielsen_factorization` (explicit 7-family witnesses with the even parameter adjustments); MC2 DID land `MDecomposition` (dispatch note was wrong) — consumed, so the classification is at rank four; S2 lift NOT built (see log) — hence no B8 consumer; ⚠ **variance discrepancy vs MC4 — ADJUDICATION ticket MC-VAR dispatched**) |
| MC4 | **MC-N**: classification + lifting for `N_α` (uniform in α) | fable→opus | `GQ2/Dyadic/MarkedCore/N.lean` | MC2 | **done 2026-07-30** (2f28429 → merged, import registered; 1822 ln, 0 sorries, **EVERY decl std-3 — no B8, no B3c**; audit green 3417 jobs; **`nStabilizer_classification` is an IFF**, unconditional, uniform in α ≥ 2, with `St_N ≅ (ℤ/2 × ℤ₂²) ⋊ GL₂(ℤ₂)` in closed form (`nStabParam_tauSolve_unique`); Witt half = ONE kernel `decide` over 2⁹; **the six-family list is COMPLETE at the frame level** (memo §3.3 re-derived independently — and the ROW convention is the right one, the transpose convention kills N1); SL₂ block realized unconditionally; S2 threaded as binders (B8 route cited not executed — the deliberate deviation, see log); ⚠ **`nCoreMixHypothesis_not_of_mix`: HM4's schematic S3 binder is UNSATISFIABLE** — see log) |
| MC-CoV | errata item 3, derived rather than asked | opus | `GQ2/Dyadic/MarkedCore/CompactCoV.lean` | MC5 ✓ | **done 2026-08-01** (bfbad18+adb9829 → merged, import registered; 590 ln, 30 decls, 0 sorries, **every headline std-3 with zero B8/B3c** — MC3/MC5's record holds; **THE SUBSTITUTION**: `A = x₀⁻¹σ^{−m}`, `B = x₁`, `C₀ = σ`, `D = x₂` with `m = 2^{α−1}` (inverse `σ = C₀`, `x₀ = A⁻¹C₀^{−m}`), giving `χ_M = (1,−1,1,u)` with `u = (1−2^α)⁻¹` and `ν_M = (−m,0,1,0)` — **it reproduces the packet's OWN word specialization** (proof.tex:885's `A₀ = x₀⁻¹σ^{−m}`) and the frozen row 4, and IS MC2's `nuM`/`chiM` exactly, with the residual freedom classified from MC3 (`γ = ν′(C̄₀)⁻¹` gives the packet normalization); **MC1's degeneration mechanism CONFIRMED BUT INCOMPLETE** — `ε·2^{r−1} = ε/2` is real but not decisive: at r = 0 the modulus is `ℤ/2⁰ = 0`, so λ ≡ 0 and **both ε and η cease to exist**, and the Frobenius changes slot (procyclic `D = σ^η`, `C₀ = x₂σ^{2^r}`; compact `C₀ = σ`, `D = x₂`) ⇒ **the compact row is not a limit of the procyclic formula in ANY sense**, so no coefficient repair could have produced it; ⚠ **THE FLAGGED CHOICE**: `IsUnit ν′(C̄₀)` is **provably not dischargeable from nothing** (a rank-four marking is a free triple, and the pivot's unit-ness is an `St_M`-INVARIANT — every χ-preserving cup isometry enters the shear doubled), so the binder had to be REPLACED not deleted; the agent chose `MChiKerUnimodular` and proved it EQUIVALENT at rank four — and that is **literally the packet's own condition `r = 0`** (`ν_ur(ker χ) = 2^r ℤ₂`), i.e. the branch condition selecting the compact row, so on the compact branch the datum is a THEOREM; two alternatives rejected with reasons (surjectivity of ν′ is REFUTED not merely weaker; the N-side generator-form clause would have imported a new obligation from the `M4/M6/M7` non-symplectic residue); √2 and √5 both pinned and discharged; **MC-M's binder inventory drops to `MMixHypothesis` alone, matching the N-side's `NScalingHypothesis` alone**; ⚠ new errata lines: the campaign's "Prop 8.1" is `prop:sign-excluded`, which LaTeX compiles as **Proposition 9.1** (off-by-one, consistent across three campaign docs), and `dyadic-presentations.tex`'s assembly table still lists three M rows including the superseded sign row) |
| MC5-swap | adopt MC-CoV's `_of_chiKer` forms at the compact-`M` consumer sites | opus | `GQ2/Dyadic/MarkedCore/{Certificate,M}.lean` | MC-CoV ✓ | **PARTIAL 2026-08-01 — the code swap is IMPOSSIBLE as scoped, and the agent proved it with Lake rather than reasoning** (7f6d009 → merged; build green 3485, audit clean): `CompactCoV.lean:8` is `public import …MarkedCore.Certificate`, so the chain is **CompactCoV → Certificate → Variance → M** and both target files sit strictly BELOW `CompactCoV` — naming any `_of_chiKer` theorem in them is a build cycle (reproduced: *"build cycle detected … bad import"*). This blocks BOTH of MC-CoV's variants, recommended and not. There is also **no consumer above `CompactCoV` to swap** — a repo-wide grep puts every caller of the three theorems inside these two files plus `CompactCoV` itself; `Count/*`, `CertificateMain` and the branch certificates mention the M certificate only in prose. **The docs half landed**: six sites' docstrings now point up at the discharged compact counterpart, and three stale claims are corrected (the module docstring still asserted the compact-M CoV is "MISSING from the vendored sources", that the file "does not invent the substitution", and that the K-side discharge is "packet-author territory" — MC-CoV superseded all three, and that prose feeds the errata record); **general-`h` statements survive VERBATIM, proved mechanically** — comment-stripped byte-comparison gives identical code, 558 + 1138 lines, no statement/signature/proof/import/attribute changed; prints identical before/after (225 std-3 of 231, **zero B8/B3c/B5/B10/sorryAx/native_decide**); ⚠ **the substantive point was already true**: `hpivot` was never a binder in the campaign's sense — it is marked DATA, the exact analogue of the N side's `hpair`, and `MMixHypothesis` already carries `IsUnit ν'(C̄₀)` as one of its own clauses, so **MC-M's residual reads `MMixHypothesis` alone (matching the N side) regardless of the swap**; what MC-CoV changed is that the datum is now SUPPLIED (it is the compact row's `r = 0` branch condition) rather than an errata gap; ⚠ correction to MC-CoV's report: its cited `Certificate.lean:672` is not an `hpivot` binder (the six are at 571/606/684/728/762/818; 672 is inside `marked_matching_certificate_N`'s body) |
| MC-CoV-split | **OPTIONAL tidiness, not on any critical path**: split `CompactCoV` at §6 (the discharge below, the three MC5-facing restatements above) so `Certificate.lean` can import the discharge and the compact-`M` sites cite the theorem instead of taking the datum. MC5-swap established this is the only unblocking route. **Deliberately not dispatched**: MC-M's residual list is already correct without it, and AS3 can discharge the datum at its instances directly from `CompactCoV`'s landed `mCoVPin_discharge_sqrt_{two,five}` — the split changes ergonomics, not what is provable | opus | `GQ2/Dyadic/MarkedCore/CompactCoV.lean` + the two consumers | MC5-swap ✓ | queued, low priority |
| MC5 | handles + `MarkedCoreCertificate` + marked-matching reduction | **fable** (upgraded 2026-07-31) | `GQ2/Dyadic/MarkedCore/Certificate.lean` | MC3 ✓, MC4 ✓, MC-OB ✓ | **done 2026-07-31** (d55c0be+491976d → merged, import registered; 1051 ln, 54 decls + 10 stress, 0 sorries, **43/43 headlines exactly std-3 — zero B8/B3c/B5-K anywhere** (SqCore consumed via the std-3 h-generic values, K-layer MarkedRecip-bundle-parametrized); certificates on the abstract `(G, χ_G, ν_G)` slot (SD1 Q4 pattern); **Prop 7.2 landed: N-core needs ONLY the S2 `NScalingHypothesis`** (S3 = HM6ef's theorem), M-core = `MMixHypothesis` + the explicit `IsUnit ν'(C̄₀)` CoV datum (errata item 3, never invented); engine port at pure-algebra level (masters/Nakayama-span/N3-pivot-solve/χ-contract via `nCoreIdx_cases`; `evalMatrix` deliberately not duplicated — carried by the MC3/MC4 classifications, RATIFIED); MC-OB instantiation: the `?RelWord_centLift_fib` fibres ARE `relZ` (rfl via `relZ_ofDRCoh`) + `MarkedRelator`/`PresentedBy` bundles at rank 4+2h; **L_sq redo DONE**: collector pivot σ̄ is χ-obstructed (S ≡ 13 (16) pin), corrected pivot `w = σ·x₀^{−c}` (S = X^c) with **unit row ν_sq(w) = 1 exact** + `SqHandleMixHypothesis` in pivot-w form; survived the session-limit kill (1045-ln salvage committed on resume); binder inventory + SQ4 inputs in log) |

- **MC1**: starting from `recon/mc-survey.md`, write per-core: the abelianization
  decomposition (rank-4 analogue of `BDecomposition` `GQ2/SectionThree.lean:422` — `M_α`:
  `A²[A,B]C₀^{2^α}[C₀,D]` and `N_α`: `x₀^{2+2^α}[x₀,x₁][σ,x₂]` have different torsion, so two
  frames), the invariant triple (canonical orientation, torsion relation vector, mod-2 cup
  form) in that frame, the **finite Nielsen-generator list** for the Smith–Witt stabilizer
  (packet §14 completion criterion), the per-generator lifting constructions
  (presentation-side generator-word automorphisms — D_R pattern, no B8), uniformity in `α ≥ 2`,
  and the statement skeletons for MC3/MC4/MC5 including the per-core hypothesis `def`s
  `MLabHypothesis`/`NLabHypothesis` (BLabHypothesis pattern, `GQ2/Roe/MarkedPro2.lean:141`).
  Owner-visible; feeds gate **G-Lab**.
- **MC2**: define `D_{M,α,n}` / `D_{N,α,n}` via `profinitePresentation`
  (`GQ2/ProfinitePresentation.lean:43`, rank-generic) with hyperbolic handles; standard
  `χ_P : D_P → ℤ₂ˣ`, `ν_P : D_P → ℤ₂` (`ν(σ)=1`, `ν(x_i)=0`); topological generation
  (`dr_topGen` pattern `GQ2/Roe/DRAbelianization.lean`); abelianization computations + the two
  4-frames per MC1; rank-4 Demushkin bookkeeping via generic `GQ2/Demushkin.lean`
  (`card_H1 = 2^(n+2)`, `card_H2 = 2`, cup Gram — DRDemushkin/DRWordCoh as templates).
- **MC3/MC4** (the obligations): every automorphism of `D_P^ab` preserving (orientation,
  relation vector, cup form) is a product of the listed Nielsen generators (Smith normal form +
  Witt cancellation on the abelian side), and each generator lifts to `Aut(D_P)`
  (explicit generator-word automorphisms; port the matching engine masters → mod-2 span →
  `evalMatrix` invertibility → solve → contract from `GQ2/Roe/MarkedMatching.lean:307-1112`
  to the 4-frame). Composition gives every required marking correction `u` with
  `χ_P ∘ u = χ_P`, `ν'∘u = ν_P` (packet Prop. 7.2 shape). Unconditional — no Labute
  hypothesis, no census axioms beyond std-3 (mirror the Labute-lane discipline,
  `GQ2/Roe/Labute/Assembly.lean:49-51`).
- **MC5**: hyperbolic-handle stability (Nielsen moves preserving the commutator product);
  `MarkedCoreCertificate K P` (ledger §5.1 fields: `abstractEquiv`, `orientation`,
  `correction`, `correction_chi`, `correction_nu`); packet Prop. 7.2 (marked-matching
  reduction): transport `ν_K` through the hypothesized abstract iso, Smith/Witt produce the
  abelian correction, lift by MC3/MC4. Consumes `MLabHypothesis`/`NLabHypothesis` +
  AX3 (`MarkedRecip`) statement-level interface as explicit binders. **G-Lab decision recorded
  here when made.**

### Lane LG — LG-K (worktree `gq2-dyadic-lg`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| LG1 | design memo: rebase map + Euler-char derivation spike | fable | `docs/dyadic/lg-design.md` | recon/lg-survey | **done 2026-07-29** (5ae7b0b → merged; **AX2 NOT NEEDED — Euler char DERIVABLE from B7** via coinduced module, gap list L0–L6 ≈850 ln → LG2a; 13/13 clone, 0 in-place; retype surface corrected to ≈9.2k ln; parity via arf_eq_of_free s:=n) |
| LG2a | Euler characteristic over K derived from B7 (memo L0–L6, `EulerShapiro.lean`) | opus | `GQ2/Dyadic/LocalGauss/EulerShapiro.lean` | LG1 ✓ | **done 2026-07-29** (c0b4449 → merged, import registered; 800 ln, std-3 + B7 ONLY; `localEulerCharacteristic_open` (workhorse, U.index = n) + `absGalK_localEulerCharacteristic` + degree-2 Shapiro NEW to repo; L4 was easier than estimated, L1/L5 harder; ⚠ AbsGalQ2-vs-Gal instance trap documented — see report/handoff) |
| LG2 | group-generic `Q⁰` + polarization over a local dualizing source | opus | `GQ2/Dyadic/LocalGauss/{Q0,PairingK}.lean` (per LG1 memo §6) | LG1 | **done 2026-07-29** (d54b270+4acea44+5c6600a → merged, imports registered; 1339 ln, 0 sorries, per-decl prints STRICT SUBSET of models (bundle parameterization made pairingK std-3; sole designed exception tateDualityKer = +tateDualityAt matching its model); audit green 3391 jobs census 9; Prop 6.6 all three clauses (`Q0loc_H1mk`, `polar_Q0loc`, `nonsingular_Q0loc`); n=1 pins `rfl`-equal to SectionSix; **(H3) isotropy splice deferred to LG4 by design** (deep-unit content needing the N_K-anchoring convention — H1anchor/H2anchor supplied as the memo's mitigation); smul trap + notes in log) |
| LG3 | unramified sign `(−1)^n 2^{nd/2}` (Hermitian rank-n) | opus | `GQ2/Dyadic/LocalGauss/Unramified.lean` | LG2, AX2 | **done 2026-07-29** (ba09366 → merged, import registered; 1103 ln plain-import, 0 sorries, 24/27 decls std-3 (3 Euler consumers print exactly the model's std-3+B7); audit green 3395 jobs; **`s := n` route worked with NO obstruction** — freeness by field-linearity, no #H¹ hypothesis (strictly weaker than the ℚ₂ Schur transfer); all five memo deliverables at memo names + packaged `prop_6_18_unramified_K` over FieldParameters; **n=1 pin is a kernel `rfl`** (`example : @prop_6_18_unramified_K_q2 = @UnramifiedModel.prop_6_18_unramified := rfl` — drift becomes a compile error); AX3/AX4 as 3 binders exactly per AX4 memo §0 row; MuTwoPolarDual Γ-clone + lemma_6_14K landed HERE (LG4 consumes, not re-clones — LG4a notified mid-flight); smul trap fired twice, as predicted) |
| LG4a | deep-unit package + (H3) splice + InflationVanishesK + vanish core | opus (was fable) | `GQ2/Dyadic/LocalGauss/DeepPackage.lean` | LG2 | **done 2026-07-29** (2224565…c0b6536 → merged, import registered; 1488 ln, 66 decls, 0 sorries, prints ⊆ models (§4/§6 = std-3+B11a, strictly smaller than models); audit green 3396; **anchoring convention DISSOLVED the nested-subtype risk** (element-map via `anc : Γ →ₜ* GalQ2`, `kerAnc`/`ancSubgroup`/`hker` — no cohomology transport, LG2's H1anchor unused; anchor types use `GalQ2` NOT `AbsGalQ2`); InflationVanishesK via coprime averaging at general q through F3's TameQ.*; `arf_Q0loc_zero_of_deep` discharges the ENTIRE vanish side of the join; AX3/AX4 not needed here; 2 named seams → LG4b/LG4c) |
| LG4b | dim lane + join + endpoint `prop_6_18_ramified_K` | opus | `GQ2/Dyadic/LocalGauss/Ramified.lean` | LG4a | **done 2026-07-29** (cb42f5d…4fa8105 → merged + orchestrator dedup fix (see log); 1710→1687 ln, 55 decls, 0 sorries; **audit green 3401 jobs census 9**; FamiliesExtendK DISCHARGED; dim lane `lemma_6_17_dim_final_K` prints a STRICT SUBSET of its model (B6 dropped — D is a parameter); join verbatim in LG4a's §8 signature; endpoint in 2 forms (`_of_data` closes the dim side); **n=1 pin is a mechanical `rfl`** vs DetRamified; ResidueLift THREADED (residual = (k,htriv,hker)+(g₀,hg₀,hg₀rt), reusable verbatim at anc = U.subtype); 2 new hypotheses beyond LG4a's convention: `hancinj`+`hancind` (both free at U.subtype); LG5 composition recipe in report) |
| LG4c | vanish-chain retype (memo §7.1 scope block) + `lemma_6_17_vanish_final_K` | opus | `GQ2/Dyadic/LocalGauss/{OrbitVanishK,ReadPerOrbitK,InvolutionSpliceK,VanishCloseK}.lean` | LG4a | **done 2026-07-29** (72cce81+212c656+87f6aae+fa2fdef → merged, 4 imports registered; 1644 ln, 0 sorries, per-decl prints EXACTLY the models' sets (3 non-std-3 decls match B9/B11a patterns); audit green 3400; **endpoint = `Q0locVanishesOnDeep` with ZERO glue** (compiling example plugs into `arf_Q0loc_zero_of_deep`); actual retype ≈35 decls — the chain was far more ambient-free than hit counts implied; σ-twist trap PROVEN inapplicable here (2 documented reasons — belongs to IndMod/sigmaFun territory); smul trap ×5 incl. NEW `cup11Fun`-product variant flagged for LG5; `InvolutionFieldPackage` = the single AX3-interface entry point; findings in log) |
| LG5 | assemble general local Gauss theorem + n=1/n=2 regressions | opus | `GQ2/Dyadic/LocalGauss/Main.lean` | LG3, LG4 | **done 2026-07-29** (3e050fe+6318912+465d2cd → merged, import registered; 716 ln, 0 sorries, prints = EXACT UNION of the three endpoint sets, nothing new; final audit green **3402 jobs census 9**; **`local_gauss_K` = packet Thm 6.15, memo skeleton verbatim**; adapter was 12 lines (mismatch purely mechanical); the two endpoints' splitting fields COINCIDE (13-field `RamifiedCertificate`, not 15; `hcert : ramified → Nonempty _` strictly better than the memo's ∨); zero glue beyond the adapter; n=1 pins `rfl` at engine level (`↥⊤ ≠ AbsGalQ2` defeats assembled-level rfl — documented, owner-visible); n=2 +1 and ramified-+1-at-every-n corollaries; §7 campaign instantiation friction-free (`ramifiedCertificateOfSubtype` discharges 4/13 fields — its binder list IS AS1's arithmetic input); push_neg deprecated on rc2 (use `push Not`) — lane note) |

- **LG1**: from `recon/lg-survey.md`: fix the clone-vs-retype list for the 13 `AbsGalQ2`-typed
  files (~6,700 lines; parameterize by `IsLocalDualizingGroup G 2` / `K.fixingSubgroup` —
  targets already exist, `GQ2/TateDuality.lean:208,244`); **spike the Shapiro derivation of the
  general-K Euler characteristic** from ℚ₂-B7 (precedent `Shapiro.finite_H1_open`
  `GQ2/Shapiro/Finiteness.lean:262`) and report feasibility → decides AX2's fate; confirm AX6
  (Shapiro–Evens) is unnecessary (producers `GQ2/Shapiro/Deepness.lean:55/71/190` already
  abstract, B9 already base-general); statement skeletons for LG2–LG5.
- **LG2**: packet Prop. 6.6 — `Q⁰_{K,V}` well-defined on `H¹(K,V)` (cohomologous cocycles ⇒
  `V`-conjugate graph homs ⇒ equal pullbacks of the normalized extraspecial class `κ_q⁰`) and
  `B_{Q⁰}(x,y) = inv_K(x ∪_{b_q} y)`, nonsingular by B6. Rebase `Q0loc`
  (`GQ2/SectionSix.lean:157`) + `Q0locLayer` quadratic-structure block
  (`GQ2/DeepPart/Q0locLayer.lean:44-306`) per LG1. The extraspecial datum (`κ_q⁰` existence +
  normalization) stays part of the determinant datum, as in `GQ2/OrbitData.lean:74`.
- **LG3**: packet Lem. 6.7 + Prop. 6.8: `E = End_H(V) = 𝔽_{2^{2e}}`, Hermitian
  diagonalization, one line has Gauss sum `−2^e` (norm-map fibres of size `2^e+1`), orthogonal
  sums multiply ⇒ `(−1)^n 2^{n·dim V/2}`. Reuse `HermitianCount.lean` (already generic) +
  thread the parity through `arf_eq_of_free_norm_one`'s `s`-slot (`GQ2/GaussSigns.lean:613`);
  re-derive `c_cyclic` (`GQ2/UnramifiedModel.lean:69`) at general residue degree. `#H¹ = |V|^n`
  from AX2/LG1-derivation.
- **LG4** (the obligation's core): the four-leaf `DeepUnitPackage` (packet Def. 6.11):
  (a) projective inflation–restriction `H¹(K,V) ≅ Hom_H(V^∨, L^×/L^{×2})` (retype
  `InflationVanishes`/`FamiliesExtend`, `GQ2/LocalKummer.lean:304,898`); (b) Hilbert
  orthogonality on the square-class filtration (already generic: `HilbertLedger.lean`,
  `DeepCount/`; unit filtration `dyadicUnitFiltration'` already general); (c) `X₊` of dimension
  `n·dim V/2` (the `n` enters only through the Euler collapse — recon §2c); (d) vanishing of
  the normalized graph obstruction on `X₊` (retype the shell; Shapiro–Evens/deep-Evens-norm
  producers reused verbatim; middle-layer argument per packet Rem. 6.13 — odd inertia
  characters vs trivial-inertia exceptional pieces, NO "even inertia order" case). Then packet
  Prop. 6.12 (X₊ totally singular Lagrangian) + Prop. 6.14 (split form ⇒ sign +1).
- **LG5**: packet Thm. 6.15 assembled; regression pins `sign(n=1, unram) = −1`,
  `sign(n=2, unram) = +1`, `sign(ramified) = +1`, and the ℚ₂ specializations against
  `DetRamified.prop_6_18_ramified` / `UnramifiedModel.prop_6_18_unramified` values.

### Lane WW — word-certificate infrastructure (worktree `gq2-dyadic-ww`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| WW1 | generic Fox evaluator + literal defect formula | fable | `GQ2/Dyadic/Word/Fox.lean` | F2 ✓, G-1 ✓ | **done 2026-07-31** (6b45797+69c0719 → merged, import registered; 1161 ln, 106 decls, 0 sorries, 66/66 std-3, no B-axiom leaks through the WildRow imports; evaluator = `evalFin` at the semidirect `foxLift` (the exact identity, not first-order); rfl-level per-constructor rules; Prop 4.1 complete (defect formula/shift/coker iff/ker-torsor/three-term complex) + Prop 4.2 + Lem 4.3 chain-map naturality; **both mandated n=1 hand-row regressions PROVED** (`foxD_gammaAWildWord_split` = `liftMarking_wildValue_u`'s row, `foxD_gammaRWildWord_split` = `liftMarking_wildValueR_u`'s row, + bonus ramified pin); lift-level engine (2·ord, η̂-on-pro-odd, augmentation-1) mirrored from the Sage semantics; WW2 interface notes + `(A := …)` pitfall in log) |
| WW2 | Fox certificates: row/col ops + replay + normal forms | fable | `GQ2/Dyadic/Word/FoxCert.lean` | WW1 ✓ | **done 2026-07-31** (757b361+a7edce4 → merged, import registered; 1093 ln, 103 decls, 0 sorries, 23/23 headlines exactly std-3 (rest strict subsets); **atom-generic certificate grammars** (`FoxCertificate`/`FoxRowCertificate` with bundled per-op invertibility fields — ops stay pure data; `FoxCoeff`/`TameSym` with split/ramified interpretations; WNP instantiates its own η̂-alphabet); replay rfl-level except ω₂ (routed through WW1's hand-row lemmas, `powOmega2` never unfolded); **the mandated Γ_R end-to-end regression landed THREE ways** (published row `(0,1,1+S⁻¹,0)` at every split simple, the pivot-op replay to `single .tau`, the ramified twin `(0,0,S⁻¹,0)`) + a kernel-`decide` demo cert; resolver correctness generalized to modulus 2·N; survived the session-limit kill (1069-ln salvage committed on resume); dedup/hoist notes + toolchain gotchas in report — fold-into-Fox candidates + the `evalFin_congr_of_orderOf_dvd`↔`evalZ_congr_of_parity` joint hoist recorded for a cleanup pass) |
| WW3 | Stokes chain map + composition-series extension | fable | `GQ2/Dyadic/Word/Stokes.lean` | F2 ✓, G-1 ✓ | **done 2026-07-31** (aad2e25…b50c6b4 → merged, import registered; 1580 ln, 98 decls, 0 sorries, 11/11 headline prints exactly std-3; second-order rule DEFINITIONAL via `evalZ` at the lifted marking (F2 naturality applies verbatim); frozen `lemma_5_7_*` TRANSPORTED not re-proved (freeGroupCongr); chain map η under the `IsStokesEndpoint` condition (per-word `decide`); **packet Lem 5.1 landed as the once-only dévissage engine** — `stokesDuality_of_simple` extends quasi-iso to ALL finite elementary modules incl. nonsplit, via mapping cones + `StokesSES` calculus (wl-recon V6/R5 satisfied: 5 branch words ≈ 11k avoidable lines saved); WMP consumables landed (`heisJetZero` no-cross-term family = the "copies cancel" step); Γ_A endpoint stress pin; ⚠ ONE follow-up gap flagged → WW3b row (universal-coefficient step, ~150 ln); WW4 interface + 3 mathlib-upstream candidates in log) |
| WW3b | H¹ perfect-pairing extraction: finite-elementary universal-coefficient step `H^k(Hom(K•,𝔽₂)) ≅ Hom(H^{2−k}(K•),𝔽₂)` + right-side/cardinality clauses over the same ElemDualPack (WW3's flagged gap; ~100–150 ln) | opus | `GQ2/Dyadic/Word/StokesDual.lean` (new leaf; Stokes.lean stays closed) | WW3 ✓ | **done 2026-07-31** (7dec72a → merged, import registered; 603 ln (363 code), 35 decls, 0 sorries, **15/15 headlines exactly std-3, zero `decide`**; UC at k = 0,1,2 + `pairing_vanish_right` (deliberately NOT via UC — holds under strictly weaker hypotheses) + `stokesChi1_bijective` H¹ perfect pairing + three card clauses; **4× size finding RATIFIED as structural, not scaffolding**: WW3's quotient-free `StokesQuasiIso` carries no cohomology objects, so count-consumers pay a one-time 80-ln H⁰/H¹/H² bridge (the frozen ℚ₂ chain had `H0w/Z1w/H1w/H2w` as objects but 4-generator-hardwired); ⚠ TWO record-design cautions for the `StokesDualityCertificate` author: `IsSelfDual`'s second numeric clause (`#Z¹w = #A²·…`) is NOT degree-generic (do not expect it), and `card_wordH0/H2` are phrased against `(heisD0 c).ker` — carry a generation hypothesis if `fixedPts` shape is wanted; survived the session-limit kill (611-ln salvage committed on resume; `abbrev` switch deleted the semireducible-def workarounds) |
| WW4 | Hessian certificates + affine phase interface (SD1 §6 baseline; deviations via memo amendment) | fable | `GQ2/Dyadic/Word/Hessian.lean`, `GQ2/Dyadic/Word/Phase.lean` | WW3 ✓, SD1 §6 ✓ | **done 2026-07-31** (c467072+db7c674+054ac8b → merged, imports registered; 1287 ln, 87 decls, 0 sorries, 52/52 prints exactly std-3; CentExt-κ⁰ PWord evaluation on WW3's evalZ pattern (no new recursion); **the ℤ/4 lift-level boundary PROVED not hypothesized** (`kappa0_pow_eq_one_of_snd_pow` + sharpness pin — "4, not 2" is a theorem); Lem 6.1 via a self-contained Fourier double count; `PhaseCoverCertificate`/`HessianCertificate` landed with **five §6.3 amendments ADOPTED and appended to sd-design.md** (headline: `kappa_id` pins an abstract `diag` datum, NECESSARY for the corrected-Npc endpoint whose diagonal is not q); FOUR worked rows (compact-N twist-immune, both compact-M projector forms — P=1 IS the N construction, S4.1's invisibility made literal — and the Npc SHAPE with two-sided CoV witness; the literal `npc_cross_operators` bridge is WNP-c's, module-rule-blocked here); `affinePhase` stays a certificate INPUT (row-5 constraint honored); L_sq deliberately absent (rank-3 core, not a plus form); the WMP "no affine shift" corollary stated against `heisJetZero` as mandated; **the six-item WMP-c gap list is the WMP-c dispatch's spine** (in the report); survived the session-limit kill (clean re-create, nothing had survived on disk); κ⁰-cocycle third-copy dedup note (MC-OB precedent)) |
| WW5 | one-expression-tree TeX generator + hash gate | opus | `scripts/dyadic_word_tex.py`, `GQ2/Dyadic/Word/Export.lean` | F2 ✓, G-1 ✓ | **done 2026-07-31** (2ba8166 → merged, import registered, D4 ACTIVATED (worker-tested line, orchestrator-applied); 1466+805 ln; **NO second tree encoding** — an S1.8 certificate IS a valid interchange file, hash = sha256 over the same canonical JSON (`AST_SCHEMA_VERSION` outside the hashed bytes, matching ast.py); python self-test 25/25 with FOUR frozen-row cross-repo digest pins + byte-identical LaTeX vs `pretty_latex`; Lean kernel byte-pins reproduce two digests in-kernel (own `natToString` — `toString`/`Char.ofNat` don't kernel-reduce), all std-3; ⚠ SIX wave-2 gating mismatches recorded in log — **Shadow denotation is the WMP-a blocker**; mandate correction: `search.json` carries no word_ast — the 55b24a4b… tree lives in the certificate twin, pinned there) |
| WAH | `Words/` alphabet hoist: one shared `Words/Alphabet.lean` replacing the five lanes' duplicated toolkit (the CAUSE of the 2026-08-01 root-build collision, whose emergency fix only patched the symptom) | opus | `GQ2/Dyadic/Words/Alphabet.lean` + de-dup edits in the five `Words/*` files and their `open` lines | wave 2 complete ✓ | **done 2026-08-01** (4 commits → merged, import registered; 26 decls replacing 94 copies, 68 duplicates deleted, zero statement changes, zero renames; see the log entry for the upgrades taken/rejected, the three documented handle shapes, and the M0Fox vacuous-bridge follow-up) |
| MC-OB | relator-generic `obsH2`/`relZ` port (MC2 log item (v)) | opus | `GQ2/Dyadic/Word/WordCoh.lean` | MC2 ✓, F2 ✓ | **done 2026-07-31** (8feffa8…d51167d → merged, import registered; 1504 ln, 145 decls, 0 sorries, **module-style ACHIEVED** (DRWordCoh is already a module — imported for pins only; WordCoh2 untouched, not imported); all 33 headlines std-3, census 11 unchanged; **8 regression pins incl. `rfl`-level `relZ_*_eq_drRelZ` and `obsH2_eq_obsH2_DR`** — the generic obsH2 at D_R IS `GQ2.obsH2_DR`; consumer API = `relZ`/`relZFam` + `obsH2_injective` + **`card_H2_le_two`** (the Demushkin #H² ≤ 2 half) + `obsH2_eq_of_factor` (MC2's Gram-value slot) + `MarkedRelator`/`PresentedBy` bundles; deviations + layer-order note in log) | |

- **WW1**: structural-recursion Fox evaluator on `PWord` into `WordLift A C`
  (`GQ2/FoxHeisenberg/Basic.lean:76` reused): rules `D(uv) = D(u) + ū·D(v)`,
  `D(u⁻¹) = −ū⁻¹·D(u)`, profinite powers via F2 finite evaluation; the evaluated two-relator
  Jacobian `d¹_{R,ρ} : A^{Generator n} → A²`; packet Prop. 4.1 (defect changes by `d¹(a)`;
  lift ⟺ defect dies in coker; lift set a `ker d¹`-torsor; conjugation gives the three-term
  complex), Prop. 4.2 (admissibility adds no equation — preimage of a finite normal 2-subgroup
  under elementary 2-extension is a finite 2-group), Lem. 4.3 (coefficient exactness,
  coordinatewise). Regression: at `n = 1` the evaluator's rows equal the hand rows
  `liftMarking_wildValue_u` (`GQ2/FoxHeisenberg/WildRow.lean:277`) / `liftMarking_wildValueR_u`
  (`GQ2/Roe/WildRow.lean:219`).
- **WW2**: `ElementaryRowOp`/`ElementaryColOp` over the relevant operator coefficients
  (invertibility witnesses carried), `applyOps` replay, `FoxNormalForm` targets,
  `FoxCertificate` (ledger §3/§7 shape: ops list + target + `verifies : applyOps … = target`),
  with kernel-checkable verification on module instances (`decide`/`rfl`; simple tame modules
  handled through the abstract `S`/`T`/`U`-operator identities the ℚ₂ code already uses —
  see `pairingR_operator_injective` chain). Design for quantification "for every simple tame
  module": certificate stated over the operator algebra, specialized per module class
  (split/unramified/ramified), mirroring the existing split/ramified row pairs.
- **WW3**: reuse the already-`n`-generic `stokesEval`/`lemma_5_7_left/right`
  (`GQ2/FoxHeisenberg/Heisenberg.lean:325-533`) + `MixedBilinear.lean`; add the `PWord`
  denotation into `HeisLift` (rule `β(uv) = β(u) + β(v) + D^∨(u)(ū·D(v))`), the natural chain
  map `η_A : C•(A) → Hom(C•(A^∨), 𝔽₂)[−2]`, and packet Lem. 5.1 (composition-series extension
  by five lemma / mapping cones — REQUIRED for nonsplit coefficients; dimension equalities are
  insufficient). Scalar lane: cup–Bockstein extraction hooks (marked local Hilbert matrix
  comparison shape, `GQ2/Roe/TrivialSelfDual.lean` Gram-by-`decide` pattern).
- **WW4**: `PWord` extraspecial evaluation (the `CentExt κ⁰` route,
  `GQ2/GaussZ/RelatorGammaA.lean:223` pattern, generalized); `HessianCertificate` = change of
  variables (`LinearEquiv` with inverse witness) + quadratic normal-form target + polar +
  quadratic verification + `PhaseCoverCertificate`. `Phase.lean`: packet Lem. 6.1 (affine Gauss
  translation `Σ(−1)^{Q+ℓ} = (−1)^{Q(y)}·Σ(−1)^Q`), Cor. 6.2 (`ε(Q)·2^m`, zero counts),
  Def. 6.3 (affine determinant interface) — **aligned with the actual SourceData obligation
  families (half-torsor, separation, nondegeneracy, cocycle cardinality, Gauss residue), per
  the ledger's B4 warning; coordinate field shapes with SD1's memo before freezing.**
- **WW5**: serialize `PWord` trees to TeX matching the draft's displayed formulas; content
  hash of the tree emitted into both the TeX comment and a Lean `#eval`-checkable constant;
  `check_dyadic.sh` hook (F6) compares. Acceptance-appendix generator skeleton (ledger §7's
  ten items) filled per branch in wave 2.

### Lane AX — axiom proposals (owner-gated; run in `gq2-dyadic-f` or integration worktree)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| AX1 | statement design: `G_K` topological finite generation (NSW 7.4.1) | opus | `docs/dyadic/ax1-proposal.md` | — | **done 2026-07-29** (043c46f; **ALSO NOT AN AXIOM — provable from B1** via profinite Nielsen–Schreier, scratch-verified std-3+B1; Route D adopted: census 9→9, B1 untouched; implementation = FG1) |
| AX2 | Euler characteristic over `K` — derivation spike verdict, else proposal | opus | `docs/dyadic/ax2-proposal.md` | LG1 ✓ | **closed 2026-07-29 — NOT NEEDED** (derivable from B7; implementation = LG2a; census unchanged) |
| AX3 | marked local reciprocity over `K` (`MarkedRecip`: full ν_ur + `(C,I,λ,γ)`) | fable | `docs/dyadic/ax3-proposal.md` | — | **FLIPPED 2026-07-29** — owner G-AX sign-off (Q1–Q7, see log); AX3-b bundle (d964e02 → merged, 1568 ln, all 12 fields elaborate as written, F4-compat proven, `norm_partner` bridge serves LG binders, def-move with byte-identical consumers) then atomic census commit 6320493: **B5-K `markedRecipAt` live, census 9 → 10**; post-flip audit green (3403 jobs; ℚ₂ capstones print the FROZEN 9-set — no leak; twins identical); citations owner-approved as targets, **PDFs unverified** (annotations retained) |
| AX4 | oriented tame quotient of `G_K` at `q_K` | opus | `docs/dyadic/ax4-proposal.md` | AX3 | **FLIPPED 2026-07-29/30** — owner G-AX sign-off (Q1–Q7; Q8 moot); AX4-b bundle (dedf9c7 → merged: `OrientedTameBundle.lean` 866 ln, 60 decls std-3, memo §2.3 verbatim with Q3/Q6 baked in, K=⊥ regression COMPUTES f — the R2 guard) then atomic flip 890a960: **B10-K `orientedTameQuotientAt` live, census 10 → 11**; post-flip audit green (3404 jobs; capstones at the frozen 9-set; twins identical); ⚠ consumers of B10-K also print B5+B5-K (type mentions `markedRecipAt` — inherent); citations owner-approved as targets, PDFs unverified |
| AX5 | ramified-simple projectivity — try-prove-first, else proposal | opus | `docs/dyadic/ax5-proposal.md` (+`GQ2/Dyadic/Projectivity.lean` if proved) | — | **done 2026-07-29** (a49d1d6 → merged 94f74f6; **VERDICT: PROVABLE, census +0** — general-q theorem verified by 922-ln spike over RegularSummand chain, std-3; consumer finding: InflationVanishes needs averaging NOT projectivity; implementation → PJ1) |

| PJ1 | projectivity implementation: general-q leaves + hypothesis swap (per ax5-proposal §4.2/§6, in-place edits APPROVED) | opus | `GQ2/Dyadic/Projectivity.lean`, `GQ2/RegularSummand/Trace.lean`, `GQ2/RegularSummand/Involution.lean` | AX5 ✓ | **done 2026-07-29** (65c93bc → merged, import registered; headline `GQ2.Dyadic.lemma_6_11_of_tame_pair_pow` + 4 leaves std-3; q=2 wrappers byte-identical (verified vs git show); FULL build 3382 jobs green + check-5 RAN clean (5 capstones, 3 twin pairs, census 9); pj worktree kept as the BUILT audit worktree; deferred: one-line docstring refresh in RegularSummand.lean umbrella (pre-existing drift class)) |

| FG1 | G_K finite generation as a THEOREM from B1 (ax1-proposal §3.2, Route D) | opus | `GQ2/Dyadic/FinitelyGeneratedK.lean` | AX1 ✓ | **done 2026-07-29** (cb314e1 → merged, import registered; 129 ln, std-3+B1 print verified; memo proof verbatim; ⚠ naming hazard logged: a future k=⊥ regression must NOT reuse the base name absGalQ2_isTopologicallyFinitelyGenerated — census infra substring-pins it; worktree removed) |

Protocol per AX ticket: memo with exact Lean statement + citation + normalization notes +
consumers → owner sign-off (**G-AX**) → census flip commit (statement into
`GQ2/Foundations/Axioms.lean`, `EXPECTED_AXIOMS` bump, `docs/literature-axioms.md` row) using
the b9a checklist template (`docs/orchestration/b9a-tickets.md`). Until sign-off, consumers
bind the statement as an explicit hypothesis. AX6 (Shapiro–Evens over `K`) intentionally
absent — LG1 confirms B9 + abstract producers suffice; resurrect only if LG1 refutes.
**Never in this lane: the nine obligations; any per-field presentation isomorphism; the
rank-four Demushkin classification (that is gate G-Lab, default = hypothesis binders).**

## Wave 2 — branch word certificates (after G1 + WW lane; pilot first)

Pilot lane WN0 runs first end-to-end; **G2 review** before the other four dispatch. Each lane
`X-a` also adds its python-harness rows (F5) and Lean small-group stress pins. All branch words
are `PWord` trees exported through WW5 (one-tree gate). Endpoint targets: plan §1 table.

### Lane WN0 — WC-N0, compact `N_α` (worktree `gq2-dyadic-wn0`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| WN0-a | word + boundary specializations + sanity pins | opus | `GQ2/Dyadic/Words/N0.lean` | F1–F4 ✓, WW5 ✓, MC2 ✓, S5.G artifacts ✓ | **done 2026-07-31** (03fe115+8c17c7e+097b1f6 → merged, import registered; 641 ln, 54 decls, 0 sorries, 27/27 headlines std-3-or-smaller, census 11 untouched; **all four frozen N_compact digests reproduced in-kernel** via WW5's pins (no second string literal — `rawNCompact 2 0 = Export.frozenNCompactAlpha2H0` is `rfl`) + `denote_rawNCompact_*` certifying the SEMANTIC word is the certificate's word; pro-2 boundary = MC2's `nWord` core via ONE certified move (`invConj_mul_self`) + associativity — exact AST equality is false and honestly said so; tame boundary stated as the VALUE `τ^{ω₂}` (which surfaced the KillsWild finding); √−2 instance + zmod8 genuine-ω₂ pin + S₃ stress with explicit witnesses; ⚠ `KillsWild` finding + template rules → log; **the file is non-module (FORCED — TameBoundary is non-module) ⇒ Words/ + Certificates/ layers are non-module, lane convention RATIFIED**) |
| WN0-b | Fox certificate (invertible `1−S^{-1}` unramified block) | opus | `GQ2/Dyadic/Certificates/N0Fox.lean` | WN0-a ✓, WW1 ✓, WW2 ✓ | **done 2026-07-31** (7e5019c…8490635 → merged, import registered; 1265 ln, 91 decls, 0 sorries, 62 exactly-std-3 + 29 strictly-less, census 11; universal wild row `(0,P,0,0,S⁻¹+P)` + tame row matching the frozen Sage certificate ENTRY-FOR-ENTRY; **both frozen one-op normal forms certified op-for-op** (unram `FoxRowOp.addSnd S` = Sage `AddRow(1,0,S)`; ram `FoxColOp.scale x₂ S S⁻¹` = Sage `ScaleCol(x2,S)` with the carried inverse AS the witness); **the `1−S⁻¹` exhibit is an IFF** (`isUnit_oneSubSInvEnd_iff`: invertible iff `V^S = 0` — nontrivial simple unram yes, scalar no, exactly the frozen note); handle columns zero at EVERY h via `foxD_comm_of_trivial` (no freshness needed); √−2 instance pinned; finding: α ≥ 1 suffices at first order — α ≥ 2 is Hessian-only, matching S3.1's Sage measurement; hoist candidates (trivAct-as-subgroup, `foxD_prodList_of_trivial`, …) + gotcha list in-file → cleanup queue) |
| WN0-c | Stokes + scalar + Hessian + phase certificates | fable | `GQ2/Dyadic/Certificates/N0.lean` | WN0-b ✓, WW3 ✓, WW4 ✓ | **done 2026-07-31** (3afe535…d49961e, 8 commits → merged, import registered; 1456 ln, 94 decls, 0 sorries, 94/94 std-3-or-smaller, census 11; **THE PILOT LANE IS END-TO-END**: Hessian word-side equation `hessRelZ_nCompact` = `q(c₀)+b_q(c₀,c₁)+Σb_q(dⱼ,eⱼ)` at general h + EVERY resolver, landing on WW4's `compactN_certificate` endpoint (identity CoV) with the word-level Gauss consumption; Stokes rows exact-in-resolver + the honest e ≡ 1 (4) class; `IsStokesEndpoint` proved GENERALLY (α ≥ 1, all h, even q, odd e — stronger than per-word decide); duality via `stokesDuality_of_simple`; two scalar Grams by kernel decide (e=1/e=3 twins = S1.T's mod-4 sensitivity as a matrix pair); phase = the c₁-Lagrangian Gauss `2^{nd}` clause in SN shape; **√−2 honest eval carries NO boundary hypotheses** (the x₂-no-primal finding: this row needs no ω₂-representative pin); handles: planes invisible on rank-one + VISIBLE on the extraspecial witness by decide; ⚠ ~350-ln toolkit re-derivation per future -c lane unless hoisted → WWH dispatched; -c pattern notes + WM0/WNP/WMP one-line route notes in report) |

- **WN0-a**: `R_{N,α,0} = x₀^{p_α}[x₀,x₁]·x₂^{-σ}(x₂τ)^{ω₂}·H_h` (draft eq:Ncompact-word;
  `p_α = 2+2^α`, handles `H_h`, **conjugator is σ not σ₂**); tame specialization → 1 (δ-letters
  die, balanced exponents cancel — packet Prop. 9.2 proof shape), pro-2 specialization →
  `x₀^{2+2^α}[x₀,x₁][σ,x₂]` = MC2's compact `N` core; α=2/q=2 instance pin
  `x₀⁶[x₀,x₁]x₂^{-σ}(x₂τ)^{ω₂}` (the √-2 relation) + zmod8/small-group stress.
- **WN0-b/c**: full packet Def. 9.1 items (3)–(6) via WW machinery; the unramified Fox block
  must exhibit the invertible `1−S^{-1}` term produced by `x₂^{-σ}` (packet §14); Hessian
  endpoint `q(c₀)+b_q(c₀,c₁)`; `c₁`-Lagrangian ⇒ Gauss `2^{nd/2}`; affine phases per WW4.

### Lane WM0 — WC-M0, compact `M_α` (worktree `gq2-dyadic-wm0`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| WM0-a | word + boundary + sanity (mutant rejection re-scoped to WM0-c) | opus | `GQ2/Dyadic/Words/M0.lean` | G2 ✓ | **done 2026-07-31** (8916946…2b48059 → merged, import registered; 1106 ln, 103 decls, 0 sorries, all std-3-or-smaller; **five candidates = FOUR trees** — the q2/q4 shared hash stated as the theorem `astHash_q2_eq_q4` (q_K lives in the tame relation, not the word), all five manifest digests reproduced in-build + the freeze-row cross-pin; pro-2 = MC2's `mWord` at `A₀ = x₀⁻¹σ^{−m}` — the certificate's `gate_C_core_displayed` string VERBATIM; tame VALUE = `τ^{ω₂}·𝓔(σ₂^m,σ₂^m;τ^{ω₂},τ^{ω₂})` with `eval_eRevW_eq_eBlock` riding S1.9's Blocks API; √2/√5 pins; mutant handling HONEST per the correction (two blindness theorems proved, rejection of record = S4.1 §9.4, Lean rejection = WM0-c); ⚠ deviations for other lanes: **NO handle node at h=0 on this row** (five children; opposite of N's trailing-.one gotcha), `deltaC ≠ deltaW` as trees (bridge provided), 1 ≤ α is a real pro-2 hypothesis, nested namespace = the alphabet-dup workaround → WAH; WM0-b scaffolding landed (`mWordWith` block-slot abstraction + congr lemmas)) |
| FD1 | the three field-side facts for packet item (5) | opus | `GQ2/Dyadic/FieldData.lean` | LG5 ✓, WL-c ✓ | **done 2026-08-01** (6302080…961c95c → merged, import registered; 508 ln, 29 decls, 0 sorries; **all three landed as THEOREMS, no new axioms** — exactly three census axioms file-wide (B6, B7, B11a), census unchanged at 11, no B3c/B5-K/B8/B9/B10-K leak; (i) `dim H¹ = n+2` in all three vocabularies (`card_H1_zmodTwo`/`finrank_H1_zmodTwo`/`demushkinRank_galK`) — the two missing Euler factors are NEW here (`#H² = 2` existed only at G_ℚ₂, never at G_K) plus a new global `Module (ZMod 2) (H1 …)` instance; (ii) `nondegFp2_cupFormK` with the B6-slot bridge `rfl` on representatives; (iii) **`(−1,−1)_K = −1` was NOT a fourth arithmetic input** — it is a PARITY COROLLARY of (i)+(ii) via the new `diag_eq_one_iff_odd` (alternating-correction argument reusing WL-c's `exists_symplectic_equiv` unchanged); capstone `exists_cupFormK_normalForm` = `⟨1⟩ ⊥ H^{⊥(h+1)}` at rank n+2 — **the same normal form WL-c's relator side lands on**; ⚠ TWO FINDINGS: (a) `b e e = 1` characterizes **[K:ℚ₂] ODD, not q_K = 2** (`cupFormK_kappa_self_iff` proves it; ℚ₂(√2) is the counterexample — q_K = 2 but n even) → L.lean's docstring CORRECTED by the orchestrator, no consumer affected; (b) **the even-n lanes (every M/N row) fall on the other side of that iff** — they get `b e e = 0` and need a rank-2 non-alternating head, a separate splitting theorem → **FD2 opened**; facts (i)/(ii) are degree-general and serve them unchanged) |
| FD2 | the even-`n` cup-form normal form | opus | `GQ2/Dyadic/FieldDataEven.lean` | FD1 ✓ | **done 2026-08-01** (ea90d1d+3194c29+fedbc1d → merged, import registered; 534 ln, 29 decls, 0 sorries; **no new axioms** — 25 decls std-3 (incl. the splitting theorem itself: **the even case needed NO arithmetic input the odd case lacked**, so not a G-AX matter), 4 at FD1's B6/B7/B11a; census 11; **the head landed as `[[1,1],[1,0]]` — matching MC2's M/N relator Gram EXACTLY** (`mRelWord/nRelWord_centLift_fib` open with `κ(m₀,m₀)+(κ(m₀,m₁)+κ(m₁,m₀))`), so the field side lands on the relator side's normal form on the nose, as it already did for type L; the economy beat the brief: **no plane search, no basis change** — any `f` with `b f f = 1` works and its Gram is FORCED (`b f e = b e f = b f f = 1` IS the Labute identity, `b e e = 0` is FD1's parity result), and the complement is alternating FOR FREE (membership in the perp includes `b e u = 0`, which IS `b u u = 0`); counting pin `m = h+1` corroborated independently by MC2's `1+h` planes at `coreRank = n+2`; ⚠ **the even case is a genuine DICHOTOMY, not one normal form** — `e ≠ 0` is a real hypothesis with no odd analogue, at `e = 0` the answer is `H^{⊥(h+2)}` with no head, and the two are NOT isometric despite equal rank (obstruction PROVED by kernel decide, not asserted); both branches + a branch-free disjunction delivered; **M/N item (5) now owes just two things**: `κ_K ≠ 0` from the ramified-i binder (reduced to the one-line `kappaK_eq_zero_iff` — AS1's, cheap) and the cross-vocabulary two-sided assembly) || WM0-b | Fox certificate (reversed correction order) | opus | `GQ2/Dyadic/Certificates/M0Fox.lean` | WM0-a ✓ | **done 2026-08-01** (824a786…67cb949, 9 commits → merged, import registered; 1545 ln, 96 decls, 0 sorries, 28/28 headlines std-3; universal row `(0, P·S₂^{−2m}, P·S₂^{−m}+P, P·S₂^{−m}+P·S₂^{−2m}, S⁻¹+P)` = the frozen JSON entry-for-entry INCLUDING print order; 12 certificates incl. √2/√5/(2,0,2) both branches; **normal forms are LITERALLY the pilot's** (imports N0Fox, reuses its forms + ops — the frozen shared-with-WC-N0 note mechanized, strengthened to the same-row theorem on unramified simples); ⚠ THREE FINDINGS: the σ-column cancels over ℤ (the differentiated Prop 9.2 power balance — not a char-2 fact), NO α-hypothesis at first order (α is gate-C-only on this row), and **S₂ = 1 is a HYPOTHESIS not an interpretation** (unramified-simple certs carry hS₂; N never met this — no σ₂-letter); E_m^rev rows landed HONESTLY (nonzero; invisible in each specialization for two DIFFERENT reasons) + order-invisibility as a THEOREM chain, rejection correctly left to WM0-c; ⚠ new gotcha relayed mid-flight to WNP-b/WMP-b: `deltaC` silently collides with the frozen peripheral `GQ2.deltaC`; 7 more hoist candidates → cleanup queue) |
| WM0-c | Stokes/scalar/Hessian/phase: both projector normal forms + the order rejection | fable→**opus** (quota) | `GQ2/Dyadic/Certificates/M0.lean` | WM0-b ✓ | **done 2026-08-01** (52d5fe7…f9992e8, 9 commits → merged, import registered; 1461 ln, 88 decls, 0 sorries, 20/20 headlines exactly std-3; **THE LANE HEADLINE: `swapDifference_formula` proves S4.1 §9.4 in the class-two algebra** (`Q(fwd)+Q(rev) = b_q(Wd₀,d₀)+b_q(Wd₁,d₁)+b_q((1+W²)d₁,d₀)`) — route: reversal adds the FULL polarization over six pairs (charges cancel — which is why the DIFFERENCE is proof-grade where neither value is), then W-invariance collapses to three; both visibility corollaries are theorems ⇒ the freeze's criterion `(1+P) ≠ 0 ∧ σ₂^m ≠ 1`; **the negative pin LANDED** — `fifthRoot_orders_differ` on an explicit 𝔽₁₆ fifth-root orbit, everything kernel-`decide`d; **size wall reported HONESTLY**: that orbit covers NEITHER displayed instance (√2 is (3,2) — provably blind by the agent's own corollary; √5 is (2,4)), both need the dim-8 seventeenth-root orbit whose `f_cocycle`/`polar_add` three-variable identities cost 256³ ≈ 1.7e7 kernel steps vs the affordable 16³ — route recorded as a `QuadraticFp2` API item, NOT a word-lane item; both WW4 endpoints REUSED not restated, with the word side supplying the projector mechanism (`hessDeltaCert_P1/_P0`) and the P=1 collapse making the compact-M row LITERALLY the compact-N row; `IsStokesEndpoint` proved generally and is CHEAPER than the pilot's; ⚠ **residual documented, not hidden**: the final single-equation assembly `hessRelZ_mCompact_P{0,1}` is not in the file (every ingredient is; needs one transport lemma + bookkeeping, est. half a day) → **WM0-d**; WW API finding: the pilot's `heisF_deltaInner/_deltaBlock` are hardwired at one δ-letter — index-generic restatements belong in the toolkit) |

- `R_{M,0} = A₀²[A₀,x₁]σ₂^{2m}·J₂·E_m^rev·H_h` with `A₀ = x₀^{-1}σ₂^{-m}`,
  `J₂ = x₂^{-σ}(x₂τ)^{ω₂}`, `E_m^rev = δ₁^{σ₂^{2m}}δ₁^{σ₂^m}δ₀^{σ₂^m}δ₀` (draft
  eq:Mcompact-word); pro-2 core `A₀²[A₀,x₁]σ^{2m}[σ,x₂]` with `2m = 2^α` (packet Prop. 9.2).
  **[CORRECTED 2026-07-31, twice-over]** The draft's forward-order rejection story is wrong
  in reason AND witness (S4.1/errata item 6: the forward form is NONSINGULAR — the failure
  is second-order via a linear form, with a proof-grade difference formula in (q,b_q,P,W);
  the fifth-root orbit covers neither displayed instance, the seventeenth-root covers both),
  AND the mutant is **F5-unrejectable**: forward and reversed 𝓔-blocks agree pointwise on
  EVERY marking of S₃/D₈/A₄ (and S₄, SL(2,3), GL(2,3)) — structural, by the freeze's
  coverage criterion (a separating orbit needs dim ≥ 2^α; these wild layers have 𝔽₂-dim
  ≤ 2). F5's row is pinned NOT-SEPARATED so it fails loudly if a target ever separates.
  **WM0-a must NOT promise a finite-target rejection of the forward order** — the rejection
  of record is S4.1's §9.4 difference formula, and the Lean-side mutant rejection belongs at
  the WM0-c second-order certificate level. Projector cases `P=1`:
  `q(c₀)+b_q(c₀,c₁)`, `P=0`: `q(c₁)+b_q(c₀,c₁)`, each with explicit change of variables
  (ledger §7). Instances √2 (`m=4`) and √5 (`m=2`) pinned in AS3.

### Lane WNP — WC-Npc, procyclic `N_α` (worktree `gq2-dyadic-wnp`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| WNP-a | word + boundary + sanity | opus | `GQ2/Dyadic/Words/Npc.lean` | G2 ✓ | **done 2026-07-31** (af4c600…60b5297 → merged, import registered; 1038 ln, 84 decls, 0 sorries, 84/84 std-3-or-less; ONE family `rawNpc α r h num den` covers all 7 frozen instances — 7/7 hash pins green, denote bridges all rfl FIRST TRY; `wf_rawNpc` conditional on η-oddness (an improvement — WF here IS η being a 2-adic unit); **npcWord pre-agreement = value-level bridge `eval_npcW_eq_eval_npcWord`** (literal cross-identification impossible for 4 machine-checked syntactic reasons D1–D4; D5 NON-divergence: `EtaData.toZhat` IS `etaHatZ` definitionally — no η̂ bridge owed); pro-2 = MC2's `nWord` at twisted Labute letters (x₁↦σ^{η̂}, σ↦g), E_{r,η} invisible at BOTH boundaries for OPPOSITE reasons (proved); ⚠ findings: **η̂-words are NOT IsOmega2Only** (numeric-pin route unavailable — forwarded to WMP-a mid-flight), abelian targets are blind to η/r/corrections (proved — the S₃-MODULE gate is forced), h-general route = NC6's `_handles_std` + `eval_handlesW` NOT a cast; ⚠ alphabet toolkit now duplicated 2× heading to 5× → **WAH hoist queued post-wave**) |
| WNP-b | Fox certificate: replay `E_{r,η}`, cross operators for ALL allowed `(r,η)` | fable→**opus** (quota) | `GQ2/Dyadic/Certificates/NpcFox.lean` | WNP-a ✓ | **done 2026-08-01** (3a98b33…e779824, 9 commits across two workers → merged, import registered; 1963 ln, 120 decls, 0 sorries; 82 exactly-std-3 + 38 smaller, **no census axiom in ANY decl** — stronger than no-leak; alphabet `NpcSym = std (TameSym n) | etaA k` with THREE design calls (B needs no atom — a ℤ-exponent; η never enters the data — the A-element is a parameter, so ONE formal row serves every η and resolver; `.etaA` stays opaque); **`foxD_eBlockW = 0` uniform in α/r/h/η/class/resolver** — and the mechanism is the finding: `L_c = A⁻¹+B+BA⁻¹` is FULLY PRESENT at first order, then annihilated by the commutator with x₁ ⇒ `foxD_npcW_eq_uncorrected` (gate D cannot distinguish corrected from uncorrected — the Lean shard of S3.2's blindness); NC seam bridged BOTH halves (`foxD_dBlockW_lcOp` + `npc_cross_operators_npcW` through WNP-a's value bridge); **ZERO instance-only certificates** — everything symbolic in (r,η), and stated for ALL r : ℕ (spec asked r ≥ 1); ⚠ structural finding: the **unramified honest stop** — after one row op two non-unit entries remain, so the compact lane's diagonal endpoint DOES NOT EXIST uniformly here; per-module iff-criteria replace it; M0Fox duplication ledgered (branch predates its merge); `#print axioms` needs `_root_.`-qualified names in this file) |
| WNP-c | Stokes/scalar/Hessian/phase (`Q₀(c₀)+b_q(c₁,L_c c₀)`, explicit invertible `L_c`) | fable→**opus** (quota) | `GQ2/Dyadic/Certificates/Npc.lean` | WNP-b ✓ | **done 2026-08-01** (fa7fd0d…8dc34d2, 7 commits → merged, import registered; 1650 ln, 87 decls, 0 sorries, 77 exactly-std-3, **no census axiom in any decl**; **THE HESSIAN WAS PURE ASSEMBLY — the NC-lane transport worked exactly as architected**: `npc_word_eq_certQ` is literally `funext fun p => npc_cross_operators_npcW …`, the certificate is one application of WW4's `npcShape_certificate`, general-h is one application of NC6's `_handles_std`; **NO jet content re-derived** (4 lines of `smul_add` to package `lcOp` as an AddMonoidHom is the entire new Hessian-side content); the genuinely new mathematics is the **Stokes layer** (which the NC lane does not cover — it computes a different pairing): `heisJet_dBlockW` shows `L_c` acts on BOTH jet coordinates, and `heisF_eBlockW` shows **the correction block is jet-zero but its central value is nonzero** — *that is exactly where gate-D blindness stops: `L_c` is annihilated at first order and PAIRED at second*; **the standing `L_c` residual is CLOSED**: general kernel-iff + battery (NC6's carrier: invertible at r=1 where `L_c = g`; **identically ZERO at r=0** where A=B=g and g²+g+1=0) — ⚠ the dichotomy turns on r, and `r ≥ 1` is precisely the side condition `npc_cross_operators` deliberately does NOT consume, so it becomes load-bearing again at AS3; ⚠ finding: the corrected `L_c` admits **NO uniform fixed-point description** (unlike both `oneSub*` criteria) — it is a sum of three actions and which cancel is per-module; S₃ gate landed REJECT-sound with **PASS explicitly non-evidential inside the theorem docstrings**, not just the header; σ-offset convention forced (η̂-opacity) ⇒ a 4×4 Gram, not the compact lane's 5×5) |

- `R_{N,α,r,η} = x₀^{p_α}[x₀,σ^{η̂}]·x₂^{-g}(x₂τ)^{ω₂}·E_{r,η}·H_h`, `g = x₁σ^{2^r}`,
  `D_{r,η} = δ₀^{σ^{η̂}}δ₀^{σ^{−2^r}}δ₀^{σ^{η̂−2^r}}`, `E_{r,η} = [D_{r,η}, x₁]` (draft
  eq:Npc-word; `η̂ ∈ Ẑˣ` = 2-component η, odd components 1). `E_{r,η}` is invisible at
  tame/pro-2/first Fox order, essential at second order: cross operators become `M_c = A`,
  `L_c = A^{-1}` with `A = S^{η̂}`, `B = S^{2^r}` (draft eq:Ncross) **[CORRECTION 2026-07-30:
  eq:Ncross is REFUTED as displayed — the true operators are `L_c = A⁻¹+B+BA⁻¹`,
  `M_c = adj(L_c)` (S3.2 machine-verified; errata item 5; NC1's Lean design governs;
  WNP-a pre-agrees `npcWord` with `GQ2/Dyadic/NpcJet/`)]** — certificates must cover
  **all** `r ≥ 1`, `η ∈ ℤ₂ˣ` symbolically. Sanity: the 2-dim `S₃`-module radical detection for
  the uncorrected word (mutant row).

### Lane WMP — WC-Mpc, procyclic `M_α` (worktree `gq2-dyadic-wmp`) — hardest word

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| WMP-a | word (both copies) + boundary + sanity | fable | `GQ2/Dyadic/Words/Mpc.lean` | G2 ✓ | **done 2026-08-01** (8bcf650…f50a781 → merged, import registered; 1714 ln, 160 decls, 0 sorries, 160/160 std-3-or-smaller; **6/6 hash pins incl. merge-gate-9's √−10 55b24a4b…** + the rfl registry pin + two constructor-level kernel pins (OrbitNorm, ZhatPower/etahat — the constructors no WW5 row exercised); ONE builder `rawMpc α r p η h` reduces byte-identically to all six emitted trees; **Prop 9.2 landed as the value-then-vanishing pair** (`prop_9_2_balance` = the ℤ-display −2m·2^r + 2^α·2^r = 0; the hat copy dies at BOTH boundaries by the balance and nothing else); pro-2 = eq:Mpc-core via `mWord` + coreMark form (the MC-M interface); ε-collapse visible in the √−10/√10 instance forms; OrbitNorm bridges rfl at concrete m (rule-2 friction was one level down — the monadic List.range coercion, split lemma provided); reused WNP-a's `toZhat_ne_omega2` per the mid-flight relay; ⚠ display finding: the h=0 Mpc trees carry NO HyperbolicHandles node (third handle-shape variant); new ℤ̂-commutation helpers close the shadow memo's σ-power gap Lean-side → WW-hoist candidates; the WMP-b handoff list (Sh_M operator + σ-column lemma + hat-vanishing row) and the WMP-c spine are in the module docstring) |
| WMP-b | Fox certificate (linear copy; hat copy has zero first derivative) | fable→**opus** (quota) | `GQ2/Dyadic/Certificates/MpcFox.lean` | WMP-a ✓ | **done 2026-08-01** (3985d91…8ebd1f0, 8 commits → merged, import registered; 1646 ln, 142 decls, 0 sorries, 17/17 headlines exactly std-3; **`Sh_M` landed as a genuine `PWord → PWord` operator on a REIFIED DISPLAYED ALPHABET `MLetter`** — the structural insight: it CANNOT live on `Generator n`, where `denote` has already inlined every Auxiliary, so a generator-level substitution produces exactly the memo's rejected reading; σ₂ and the Tietze `D` are atomic but DERIVED (`shM_omega2Pow_sigma` recovers them from σ ↦ σ), not assumed; **the certificate shrink `foxEval_inlineM_shM_mpcLinM` is hypothesis-free and delivers BOTH halves in one theorem** (gates B/C = the balance pair, d¹ = the raw word's under transport); syntactic equality correctly NOT claimed (three obstructions named, each the substitution's own created unit); **the σ-column coincidence lemma landed with its char-2 product corollary** — new `foxColumn` abstraction, `D(σ₂)` never computed, **the geometric-sum identity nowhere used**; ⚠ WM0-b contrast recorded in-file: compact-M's σ-column cancels over ℤ (bare x₁ acts trivially) but HERE `B = x₁σ₂^p` does not and char 2 closes it — conflating them is an error; **`foxD_mpcHatW_ram = 0`** at every (α,r,p), every η̂ display, general h (Rem 5.4's first-order half); E₀₁^pc BOTH halves (nonzero row + `foxD_e01_reproduced_by_shadow`); ⚠ **WW2 certificate records + the √−10 instance DELIBERATELY DEFERRED to WMP-c for a documented structural reason** — the row's honest first-order statement is split by column (the σ-entry is a statement about the PAIR), so no single normal form exists for the hat copy alone; the available certificate is the product's, which is what AS3 needs; 7 more hoist candidates) |
| WMP-c | self-replication cancellation + the deferred product certificate + `affinePhase` (WMP-b's five-item handoff) | fable→**opus** (quota) | `GQ2/Dyadic/Certificates/Mpc.lean` | WMP-b ✓ | **done 2026-08-01** (b5a3bd4…e245e6d, 7 commits → merged, import registered; 1154 ln, 57 decls, 0 sorries, 47 exactly-std-3, **no `decide` at all** — the orbit-pin budget was never drawn on; ALL FIVE handoff items delivered: `hlin` discharged (new lane-generic `ActsAsPow` + 7 closure lemmas), the pair's WW2 row certificate + √−10 gate-9 wiring, **the hat copy's DUAL jet proved** (`foxD_mpcHatW_ram_dual` — not a re-derivation: `foxD_mpcHatW_ram` is module-generic, so the dual jet is that theorem at `A := ElemDual V`; the new mathematics is `elemDual_fpf`, that an injective `τ−1` on finite V is surjective) ⇒ `heisJetZero` membership and **`mpcCopiesCancel` with NO `T`-dependent central term surviving or needing computation** (T enters only through `val(R_lin)`, which multiplies zero); `affinePhase` WW4-items **1/2/6 CONSTRUCTED**, item 3 half (`mpcShadow_no_affine_shift` — the corollary WW4 named and left unwritten), item 5 named-open (`HessRelZTarget`), and it stayed a certificate INPUT throughout (SD1 §6.3 row-5 satisfied literally); E₀₁^pc epistemics in a three-row docstring table with gate-D silence PROVED and the gate-F justification CITED not claimed; ⚠ **P4's central clause is ASSUMED, not discharged — and the reason is a real limit**: the memo's table shows it FAILING on three of four ramified simples while the conclusion survives via a parity escape, and that escape is not Lean-able here (a mod-2 occurrence count needs an abelianized letter-multiset `PWord` does not carry) — documented in-file, not glossed; ⚠ **ORCHESTRATOR DISPATCH ERROR**: the brief framed the task list around WMP-b's handoff and omitted the standard `-c` closer items (Stokes family, endpoint, duality, Gram) that every sibling carries; the agent delivered the five and flagged the omission honestly → **WMP-d opened**) |
| WMP-d | complete the Mpc lane: Stokes family + endpoint + duality + Gram + `hlinrow` | opus | `GQ2/Dyadic/Certificates/MpcStokes.lean` | WMP-c ✓ | **done 2026-08-01** (0fa8122…e007db1, 7 commits → merged, import registered; 1168 ln, 80 decls, 0 sorries, **all 80 ≤ std-3**; **WMP-c's odd-count intelligence HELD and is now machine-checked** (`epsZ_e2W`: `e2W` carries `dW 2` exactly 1+2m times in BOTH emitted z-spellings — the 2m cancel pairwise, the head survives, so `E₂^pc` IS visible) ⇒ endpoint via the tame row pilot-style, `mpc_isStokesEndpoint` for all α ≥ 1, r, p, h, every η̂, even q, odd e (contrast with compact-M's syntactic death recorded in-file); **MERGE GATE 9 IS CLOSED** — `sqrtNeg10ProductCert` is a TERM, not a transport awaiting a hypothesis (`hlinrow` discharged, `hσzero` by rfl; only the per-module ramified class conditions remain, which every sibling carries and AS1 supplies); **`hlinrow` closed form, sharper than needed**: the orbit-norm block did NOT resist, and the whole linear row **collapses to ONE entry** `D(R_lin^pc)(a) = S₂^{−s}σ^{−n}a(x₂)` at every (α,r,p,η,h) — three cancellations do it (E₀₁^pc reproduces A²[A,B]'s x₀/x₁ columns exactly; C₀^{2^α} splits; what remains is the orbit norm's REFLECTION, so E₂^pc cancels it), with a consistency check against compact-M's ramified row (also one x₂-entry, one σ-power); §6 is NEW mathematics (no lane had computed a linear-copy row with an orbit-norm block; the reflection identity and the column collapse are new); ⚠ two findings beyond the ask: the √−10 scalar Gram is NOT the pilot's (ε moves the σ-row's {τ,x₀} entries because p = ε·2^{r−1} is odd here — second-order, consistent with WMP-c's first-order zero σ-column), and the linear row has NO σ/τ/x₀/x₁ entry at all) |
- **[NOTE 2026-07-31, from WW5's gap list; NUANCED same day by S5.G]** `Shadow`
  parses/serializes/hashes on both sides but has NO Lean denotation. S5.G measured the
  frozen artifacts: **no frozen word carries a `.shadow` node** — the hat copy is
  materialized as explicit `Auxiliary` nodes (`Ahat`/`Bhat`/`C0hat`), and no symbolic
  exponent survives either (all literal `Int`; spec always `.etahat`; ω₂ always
  `.omega2Power`). So **WMP-a's word statement is UNBLOCKED** (state the tree as emitted,
  hash-pinned via `general_2adic/generated/MANIFEST.json`, keyed by `candidate_id` — NOT
  `word_hash`, which q2/q4 twins share). The Lean-side `Sh_M` substitution operator
  (S4.2's frozen substitution — x₀↦δ₀, x₁↦δ₁, x₂↦1, δ₂↦1, τ↦1, σ↦σ, δ-letters atomic —
  as a `PWord → PWord` transform) is owed where **WMP-b/c prove the hat copy IS the
  substitution's image** (the S4.2 certificate-shrink route); scope it there, or as a
  small WW follow-on, at dispatch time. **[S4.5 riders, 2026-07-31]** the procyclic block
  swap is DECIDED EQUAL proof-grade (freeze row 5 updated; frozen spelling stands):
  (i) `E₂^pc`'s second-order content is EMPTY on the gate-E marking — any block-order
  statement WMP-c makes is a gate-D statement, not a Hessian one; (ii) the equality rests
  on the x₂-has-no-primal-letter convention — if the Lean marking ever gives the boundary
  generator a primal coordinate, block order becomes load-bearing again
  (`general_2adic/artifacts/reports/s45-swap-decision.md` §3.2 formula applies).
- `R_{M,pc} = R_lin^pc·R̂^pc·D₀²[D₀,D₁]·H_h` (draft eq:Mpc-word) with
  `C₀ = x₂σ₂^s, A = x₀^{-1}C₀^{-m}, B = x₁σ₂^p, D = σ^{η̂}`; `E₀₁^pc`, `E₂^pc` (increasing
  `j`); hat copy on `D_i = δ_i` with `Ĉ = σ₂^s`. Packet Prop. 9.2: hat-copy total power
  `−2m·2^r + 2^α·2^r = 0` ⇒ specializes to 1; draft Rem. 5.4: on ramified simples `R̂` has
  zero first Fox derivative and **exactly reproduces the raw extraspecial determinant incl.
  `T`-dependent central terms**; the copies cancel in char 2; `D₀²[D₀,D₁]` leaves
  `Q₊(c₀,c₁) = q(c₀)+b_q(c₀,c₁)` — a word identity, not finite-order interpolation.
  **√-10 gate**: instance uses `(r,ε,η) = (1,1,1)` (packet Cor. 8.2; the sign row does not
  exist); the field-specific relative-norm word (draft §7.4, F5's `rel_minus10`) is retained
  only as a regression alternative; the old `D₀²[D₀,D₁]`-only correction is FALSE at
  `V = 𝔽₆₄`, `|ζ| = 9`, `S = x^32`, `q = Tr_{𝔽₈/𝔽₂}(x⁹)` (2-dim mixed-Hessian radical) —
  negative test. √10 instance parameters from draft §7.3 (marking `ν(a,b,c,d) = (−4,0,2,1)`,
  word `R₁₀ = A²[A,x₁]C₀⁴[C₀,σ]E₁₀`), harmonized with the packet's procyclic parameters.

### Lane WL — WC-L, odd degree (worktree `gq2-dyadic-wl`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| WL-a | word + boundary + sanity (L_sq; Γ_R cross-identification; q_K>2 pin) | opus | `GQ2/Dyadic/Words/L.lean` | G2 ✓ | **done 2026-07-31** (1cf0acf+b011204 → merged, import registered; 1054 ln, 90 decls, 0 sorries, 90/90 exactly std-3 — **zero B3c/B8** (SqCore/Certificate imported but the rank-3 discharge never applied); 4/4 hash pins + WW5 kernel-pin inheritance by rfl; **`eval_lSqW_zero` = Roe's `wildRelatorR` LITERALLY** — gap = the zpow realignment (TWO forms needed: ℕ-exponent for sqWord, ℤ-exponent for WW1's tree — the one surprise) + prodList associativity; pro-2 = `SqCore.sqRelWord` at every odd degree, h=0 carried onto D_R via SQ4's `sqEquivDRMarked`, letter map uniform (no reindexing); **q_K=4 pin on D₅×D₃**: genuine τ^σ=τ⁴-not-τ² pair, frozen word dies, the σ₂→σ slip mutant does NOT (invisible on all 2-groups — ω₂ = id there); tame VALUE = τ^{ω₂}; `not_killsWild` reproduces — **the KillsWild finding is LANE-WIDE, not a compact-N accident**; ⚠ emitter drops the handle node entirely at n=1 (four children — third handle-shape variant across rows!); collector = docstring-only safety net, no tree needed) |
| WL-b | Fox certificate (n=1 base + handle stability) | opus | `GQ2/Dyadic/Certificates/LFox.lean` | WL-a ✓ | **done 2026-08-01** (984045c+880a469 → merged with the orchestrator's one-line namespace adaptation; 1216 ln, 91 decls, 0 sorries, all headlines std-3, zero B3c/B8; **⚠ FOUND THE ROOT-BUILD BREAK** (the WL-a/WN0-a 20-name collision — see the integration-fix log entry); universal row `(0,P,S⁻¹+P,0,…)` — **the SAME formal row as compact-N's on a different column** (L_sq's odd −3 power contributes the whole a(x₀) where N's even p_α gives 0 — augmentation-1 mechanism, errata-pile note); the square-commutator block is INVISIBLE at first order (no σ₂/hU hypothesis anywhere — matches the Γ_R hand row); n=1 transport: the two Fox carriers are the SAME AddMonoidHom (`foxDHom_lSqW_zero`), WW2's targets/ops/verifies reused VERBATIM (one universe twin `{P : Type*}` restatement, rfl-pinned to WL-a's); **handle stability = an AddMonoidHom factorization through `coreRestrict h`** (degree n = n=1 ⊕ 2h zero columns, as an identity); q_K pin = a THEOREM (the wild row cannot see the σ₂ slot, a fortiori q_K — the sensitivity lives at word level); ⚠ tame-relator row items are word-independent and belong in a FoxCert hoist (recorded), `isUnit_oneSubSInvEnd_iff` cited-not-copied (same ticket)) |
| WL-c | Stokes/scalar/Hessian/phase (n=1 core + hyperbolic handles) | fable→**opus** (quota) | `GQ2/Dyadic/Certificates/L.lean` | WL-b ✓ | **done 2026-08-01** (d6b2533…d411a11, 11 commits → merged, import registered; 1650 ln, 96 decls, 0 sorries, 84 exactly-std-3 + 12 smaller, **ZERO B3c/B8** — the rank-3 discharge never consumed; **HEADLINE: `hHilb` is DISCHARGED as an unconditional THEOREM, not the authorized binder** — WL-recon V8/R4 priced it as the lane's only can-fail item on the (independently confirmed) grounds that mathlib has no 𝔽₂ Witt cancellation/Arf/hyperbolic API, but **the inference was wrong: the object is not a quadratic form** (`SqCore/Rank3.lean:224` already rules it a symmetric BILINEAR Gram, and over 𝔽₂ the diagonal of a symmetric biadditive form is automatically additive) ⇒ the Labute identity says `e` represents the linear diagonal, `e` lands in the alternating radical, `q_K = 2` is the single equation `b e e = 1` (automatic for odd n), `W = ⟨e⟩ ⊥ ker d` splits ORTHOGONALLY and the residue is symplectic — **no cancellation theorem anywhere**; `exists_symplectic_equiv` proved from scratch (card-decreasing plane-splitting induction producing an explicit LinearEquiv), `exists_cupForm_normalForm` = `b ≅ ⟨1⟩ ⊥ H^{⊥m}`; **and the relator side meets it**: `sqRelWord_centLift_fib` gives `⟨1⟩ ⊥ H^{⊥(h+1)}` at rank n+2 — packet item (5)'s two sides now land on the SAME normal form; c1 complete (Stokes rows exact-in-resolver + the honest class, `IsStokesEndpoint` proved GENERALLY, duality, three kernel-`decide` Grams incl. the q_K=4 second-order discriminator, the Hessian connection BUILT since WW4 left L_sq out — at h=0 it is `qDouble` on the nose = the frozen `Γ_R` endpoint `QZeroR`, which makes wl-recon §2.5's 1932-ln Gauss layer apply BY CITATION); ⚠ residual is only field-side: three NAMED facts for AS4 (dim H¹ = n+2 — derivable from `absGalK_localEulerCharacteristic` but stated NOWHERE; cup perfectness; q_K=2/the κ vector) → **FD1 opened**; `HessianCertificate` record deliberately not built (`affinePhase` needs the Arf-dependent Gauss value = an INPUT per SD1 §6.3's row-5 rule — AS1's); new errata-pile findings: the odd cube denotes as a single letter with zero central charge (the second-order face of WL-b's augmentation-1 mechanism), and this row's κ⁰-consumption is strictly larger than compact-N's (`dat.m`, not only f_diag/f_polar — endpoint still twist-immune, the CALCULUS is not)) |

- **[RE-POINTED 2026-07-31 at G-1 — the selected type-L word is `L_sq`, NOT the collector.]**
  The frozen word (selection-freeze.md row 1, R2 decision) is
  `R^{sq}_{L,n} = (x₀^σ)⁻¹(x₀⁻³τ)^{ω₂}x₁²[x₁,x₁^{σ₂}]·∏_{j=1}^{(n−1)/2}[x_{2j},x_{2j+1}]`,
  L = 11+n. Pro-2 core = rank-3 sq-comm core ⊕ handles; the orientation theorem is the
  committed `marked_square_core_rank3` (SqCore lane); at n = 1 the word IS Roe's `Γ_R`, so
  WL-a cross-identifies against `wildRelatorR` (`GQ2/Roe/GammaR.lean:77`) and AS4 wraps the
  `Γ_R` capstone. ⚠ χ_sq(σ) = S (infinite order — SQ1-R1): the mixing-frame analysis is
  MC5's redo; the HandleMixLift construction needs a change of variables on this word's
  handle block (shared commutator letters — errata item 1 note). The collector text below
  is retained as the SAFETY-NET regression row (it stays proved at n = 1) and as the L_tw
  fallback's shared-core reference; do not build WL-b/c against it.
- `R_{L,K} = h₀·u₁^{-1}x₁^σ·c₀·∏_{j=1}^{m}[x_{2j},x_{2j+1}]` (draft eq:Lword; letters
  `u_i = (x_iτ)^{ω₂}`, `d₀ = u₀x₀^{-1}`, `z₀ = x₀^{σ₂}`, `c₀ = [d₀,z₀]`, `g₀ = σ₂²` — **not**
  `σ₂^{q_K}`; `d_g = d₀^{g₀}`, `h_c = [d_g,d₀]`, `h₀ = x₀^{g₀}x₀·d_g d₀ d₀² h_c`). Pro-2 core
  `x₀^{σ²}x₀[x₁,σ]·∏[x_{2j},x_{2j+1}]`. `n = 1` base must recover the Roe–Turturean form —
  cross-identify against `wildRelator`/`wildRelatorR` (`GQ2/GammaA.lean:89`,
  `GQ2/Roe/GammaR.lean:77`) — feeding the AS4 wrapper gate. Handles: unramified sign ×
  `(−1)^{n−1} = +1` per handle pair (keeps `(−1)^n` for odd `n`), ramified stays `+`.

## Wave 3 — assembly (lane AS, worktree `gq2-dyadic-as`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| AS1 | `WordCertificate` + `DyadicLocalInput` records + certificate-main theorem | fable→**opus** (quota) | `GQ2/Dyadic/CertificateMain.lean` | SD3 ✓, MC5 ✓, LG5 ✓, WW1–WW4 ✓ | **done 2026-08-01** (b902f9f+489ea5e+a103283 → merged, import registered; 706 ln, 16 decls, 0 sorries, **all 8 headlines exactly std-3 — ZERO B-axioms, nothing for G3 to adjudicate on this file** (the B-set enters only through AS2–AS5's instantiations); **`candidate_equiv_absoluteGalois` proves packet Thm 1.1 in THREE assembly lines** (`W.toSource`, pair over the shared slot, one call to SD3's `nonempty_continuousMulEquiv_of_sourcesN`), hypothesis surface beyond the two records = `2 ≤ q`, `Even q`, `Surjective nuP`, all automatic at q_K = 2^f; records landed at 17 and 13 fields (no `eulerChar` — LG1's ruling honored); the one line of mathematics is FD2's assigned `kappaK_ne_zero_of_ramified`, stated through `¬HasEqualNormValueGroups`/`ki_unramified` and **never through `qK`**; **SIX ledger-vs-reality divergences reported, two of them STRUCTURAL BLOCKERS → CB1 and F3b opened** (below); the other four: `MarkedCoreCertificate` is three records not one, the ledger's §5.3 signature is one argument too wide (once SD-n went two-sided the core certificate stopped being an assembly input — it produces the arithmetic side's `pro2`, ASK's level), and the two sides are asymmetric because **ASK is queued, not done**) |
| CB1 | design memo: the certificate⇒count bridge | opus | `docs/dyadic/cb-design.md` | AS1 ✓ | **done 2026-08-01** (0827d45+c0847c4 → merged; 819 ln, 11 §§ + 2 appendices; **VERDICT (c) MIXED, decisively weighted GENERIC — but a large new lane either way**: the ℚ₂ ancestor is **15,064 ln / 44 files for ONE word** in six layers, of which the campaign has ALREADY rebuilt two generically (A1+A2 = 5,306 ln → the 10,255-ln `Word/` evaluator stack); what is unbuilt is A3 transport + A4 counts = **7,189 ln per word**, so cloning ×5 ≈ 36k against ~10–13k generic; **the measurement**: normalizing source names and comparing sorted line multisets, **54.8% of the Γ_R stack's 5,060 code lines also occur in Γ_A's**, banding structurally (counting machinery 56–75%, presentation-comparison and Gauss 29–45%); **10 of 11 `SourceDataN` clauses are generic over the abstract carrier — only `gaussZ_*` is per-branch**; ⚠ **landed-code finding**: five ℚ₂ files' docstrings claim word-independent content is "imported and reused verbatim" — measured duplication is 55%; the abstraction was DESCRIBED, never BUILT, because `GQ2.SourceData` had concrete carriers and there was nowhere to put it — `SourceDataN` is source-abstract, so this campaign has the home ℚ₂ lacked; **pro-2 gap: LABUTE-FREE, NO G-Lab consequence** (`BLabHypothesis` enters `exists_pro2R` at exactly ONE line through the ARITHMETIC leg; the candidate leg `MaxPro2Bridge.lean` is 504 ln with ZERO BLab occurrences vs 77 in `Roe/Main.lean`; `exists_pro2R` does not generalize, `maxPro2Bridge` does, and the two-sided flip already moved Labute to the arithmetic side as `MarkedCoreCertificate.abstractEquiv`); **AS2 is NOT blocked behind the whole lane — it is blocked behind CB-P + CB-1** (4 tickets, ~2.2–2.8k landed); new-beyond-AS1: **L has no `FoxCertificate` either** (4 row-certs, 0 Jacobian — CB-3 must not assume one per branch); **the memo's main design instruction: the eleven clauses are ONE theorem, not eleven** — at ℚ₂ all factor through `prop_5_15_R`/`IsSelfDual_R`, and a lane reading only the field list would rebuild the ℚ₂ stack's SHAPE rather than its CONTENT) |
| CB-S | the gating spike | opus | `GQ2/Dyadic/Count/Spike.lean` | CB1 ✓ | **done 2026-08-01 — VERDICT GREEN** (275161c+647794d → merged; 400 ln vs the 300 budget, all 17 headlines std-3, 0 sorries, no `decide`; **`IsSelfDual`'s count clause IS degree-generic**: the honest form is division-free and duality-free, `#Z¹w·#A^{|ρ|} = #A^{|ι|}·#H²w`, with duality entering exactly once through WW3b's own `card_wordH2`; **WW3b was right about the literal `²` and wrong about the statement — the `²` is the presentation DEFICIENCY `|ι|−|ρ| = 4−2` of the ℚ₂ marking, not a degree constant**, and it disappears under abstract elimination; ONE theorem `isSelfDualN_of_stokesDuality` yields all three `IsSelfDual` clauses from a single `StokesDuality` payload, and TWO different `SourceDataN` clause shapes read off it with no further cohomological input (`tcocycle_card` IS `S.cardZ1` once `tMult T = T^(n+1)` absorbs the deficiency; `hZcard` confirms SD-R3's shape rule); derivation-2's side condition DISCHARGED not assumed; WW3b's *second* caution (the `ker d⁰ ↔ fixedPts` bridge) proved in 20 lines as a bonus; **worked at N0, not hand-checked** — `|ι| = 2h+5`, `|ρ| = 2`, so N0 sits at `n = 2h+2` and at h = 0 that is `n = 2 = [ℚ₂(√−2):ℚ₂]`, with the `standardNumerics` value bridge closing with NO fudge) |
| CB-1 | the lane's load-bearing ticket: the `z1Equiv` comparison isomorphism | opus | `GQ2/Dyadic/Count/Compare.lean` | CB-S ✓ | **done 2026-08-01** (95e3d5b…6979c0f, 4 commits → merged, import registered; **783 ln vs the 1,100 budget (71%)**, 35 decls, all 29 headlines exactly std-3 (two print a strict subset), no sorries/`decide`/axioms; **the lane's risk item came in EASIER, not harder — 240 ln against the ℚ₂ ancestor's 492-line file, for a strictly MORE general statement**, on two findings: (1) **`heisD1` factors through the split group** — `heisD1 c w x k` is the `.a`-coordinate of a Heisenberg evaluation at zero dual offsets, which `agHom` projects onto `WordLift A C = A ⋊ C`, so kernel membership is LITERALLY "the Fox lifted marking kills every relator", degree-generic with no marking arity anywhere; (2) **therefore no explicit inverse is needed** — ℚ₂ hand-builds one (≈300 of its 492 lines); here injectivity and surjectivity are each ONE application of the presentation property and `AddEquiv.ofBijective` finishes (price: a noncomputable inverse, which no count notices); **2 of 11 `SourceDataN` fields now consumable — and VERIFIED, not asserted**: each field goal was stated VERBATIM in the recursion's own vocabulary and closed (`tcocycle_card` on the first try with `hcomp := rfl` — the imported `cActT` instance IS the one the field is stated against; `hZcard` needed one `letI` from a PRE-EXISTING defeq-not-syntactic seam the ℚ₂ proofs also lean on implicitly); N0/√−2 closes on BOTH sides at `n = 2h+2` (= 2 at h = 0), the recursion-vocabulary counterpart of CB-S's `sqrtNegTwo_cardZ1`; CB-S's flagged `DualityAssembly` hoist is NOT urgent (already in the spike's closure); module closure 128 → 146, driven by a deliberate `RadicalEdge.GammaA` import for `cActT` (re-declaring locally would diamond at CB-4) — and `LocalLiftingDuality` arrives WITHOUT any print moving; ⚠ **ONE NEW OBLIGATION CREATED**: `IsMarkedPresentation` (3 fields: letters topologically generate, relators die, relator-killing markings of finite discrete groups extend) is a hypothesis class, never an axiom, and is **unbuilt for `GammaR n q R`** — route is `presentationLift` + `profinitePresentation` with one seam (word-lane relators are `FreeGroup ι`, `GammaR`'s presentation is over `FreeProfiniteGroup (Generator n)`); **relayed to GR1 mid-flight, since its redefinition changes exactly which universal property `GammaR` has** — clause (iii) is a universal property, and an admissible limit may support only the restricted form) |
| CB-MP | the restricted `IsMarkedPresentation` + the `Γ_R` instance | opus | `GQ2/Dyadic/Count/Presentation.lean` (new) + `Count/Compare.lean` | CB-1 ✓, GR1 ✓ | **done 2026-08-01** (8add36e+a08c119 → merged, import registered + orchestrator rename `wildLetters` → `wildAlphabet` for a clash with Wild.lean's group-element set of the same name; 471 + 921 ln, 58 decls, 0 sorries; **`IsAdmissibleMarkedPresentation` = CB-1's class with clause (iii) restricted to wild-2 markings**, shared clauses (i)/(ii) verbatim so the plain class IMPLIES it as a theorem (`IsMarkedPresentation.toAdmissible`, for every `J`); the instance `isAdmissibleMarkedPresentation_gammaR` is built on GR1's `gammaLift`; **`z1Equiv` SURVIVES the weakening — but it genuinely costs two side conditions and the agent did not paper over them**: injectivity is untouched (it never uses clause (iii)); surjectivity consumes it at exactly one marking (`foxLift c x`), which is not automatically admissible, so nine declarations acquire `hA₂` and `hwild2` — and **`hwild2` is proved NECESSARY, not convenient** (`baseProj` is surjective, so by `map_normalClosure` the image IS `normalClosure (c '' J)`), while `hA₂` is sufficient-not-necessary and flagged as such; **both discharged at the pilot** so no branch inherits an obligation; **the exclusion is real**: `not_isWildTwo_zmodThree` shows CB-W's counterexamples fail the restricted clause exactly, while they still extend over `GammaBare`; prints held (34 of 37 std-3 in Compare, the 3 subsets being CB-1's two plus one new; all of Presentation std-3-or-less); ⚠ a unification trap recorded — adding the `J` parameter made two pilot proof terms diverge at 10⁶ heartbeats until pinned with `(h := 0)`; **the count lane's remaining item is `ResolvesGammaRelators` per frozen family** (CB-MP deliberately did not discharge it: the branch families are `heisToFree`-resolved at an integer representative of ω₂ while `(freeMarking n).eval R` evaluates ω₂ intrinsically, so they are different elements of `F` in general — word-lane work) → **CB-RES**) |
| CB-RES | discharge `ResolvesGammaRelators` for the five frozen families | opus | `GQ2/Dyadic/Count/Resolve.lean` | CB-MP ✓ | **done 2026-08-01 — A PROVED NEGATIVE, and it found the cause** (4065f8e…387287e, 5 commits → merged, import registered; 805 ln, 66 decls, 0 sorries, 26/26 headlines std-3; **the reduction**: `heisToFree` IS `PWord.evalZ FreeGroup.of` and `map_evalZ` is naturality with no topology, so both of CB-MP's equations are ONE statement reducing to `ResolvedAt`; **the tame equation is generic** — one theorem, every degree/q/resolver, and it covers both lanes' identically-bodied `tameRelW` constants by `rfl`; **the wild equation is FALSE at all five intrinsic branch words**: `zpowHat_omega2_ne_zpow` — in a free profinite group `Y^ᶻω₂ ≠ Y^k` for EVERY integer `k`, by two congruences with no case analysis (`omega2Exp (2^a) ≡ 1 mod 2^a` forces `k = 1`; then `3 ∣ omega2Exp 3` forces `3 ∣ 1`); **two things make this stronger than "the `of_two` route fails"**: the refuting characters land in **2-groups**, so CB-MP's admissibility restriction does not rescue it, and since a 2-group character's kernel is itself R-admissible, `N_R` sits inside it ⇒ `lift_gammaGen_nCompactFam_ne_one` shows the word-lane relator is **nontrivial in `Γ_R` ITSELF** — the `rel` clause is FALSE at the intrinsic word, not merely unproved; the sharpest pin is at `lSqFam 0 4 1`, where the resolver is exact on the whole 2-part and what still fails is the ODD part of ω₂ — precisely the direction the pro-2 clause leaves free; generic (all-parameter) refutations landed for both N rows, the M/L rows refuted at their frozen pins only (positional projection — the one gap); **what IS provable**: all five satisfy `ResolvesGammaRelators` **at `resolvedRelator e R`**, giving CB-MP's instance with ZERO hypotheses — so the question was never the hypothesis shape but **which `R` the count lane hands `GammaR`**, and §7/§8 prove `Γ_{resolveWord e R}` is genuinely a different group) |
| CB-TR | the target-resolved redesign | opus | `Count/{Compare,Presentation}.lean` + new `Count/Frozen.lean` | CB-RES ✓ | **done 2026-08-01 — THE SEAM DISSOLVED** (7c2fb59…455f0a4, 5 commits → merged, `Frozen` registered, and the orchestrator retired `Resolve.lean`'s now-stale payoff block (the project was red by design until then); 92 decls, **85 exactly std-3** + 7 strict subsets, no new axioms/sorries/decides; **clause (iii) now reads the intrinsic `PWord` relators at each finite discrete target** — and clause (ii) had to move too (a relator equation *in `Γ`* is meaningless once relators are `PWord`s), both asked only of `Γ`'s finite discrete quotients, so no compactness was added; the word lane meets it through ONE new predicate at ONE target, `ResolvesAt`, with `.pushforward` transporting along target homs (one hypothesis, not two) and `resolvesAt_heisToFree` proving it at `omega2Exp N`; **`ResolvesGammaRelators` has ZERO consumers and is retired — `isAdmissibleMarkedPresentation_gammaR` takes NO hypotheses at all**; `hA₂`/`hwild2` survived VERBATIM (verified unedited — CB-MP's necessity analysis holds); **the five families and both √−2 pilots close at the GENUINE `Γ_R`**, not `Γ_{resolveWord e R}`; ⚠ **the finding for the branches**: `omega2Exp 6 = 3`, so the frozen `e = 3` is correct only at exponent dividing 6 — but the counting target `A ⋊ C` is a 2-group whenever `C` is, and `omega2Exp (2^a) = 1`, so **`e = 1` is the resolver at every 2-group**; CB-RES's refutation witnesses land in ℤ/8 and ℤ/4, exactly where `omega2Exp = 1 ≠ 3` — its §7/§8 are now the SHARPNESS statement for the discharge; new leaf `Count/Frozen.lean` isolates the four heavy `Words.*` imports (+68 modules, driven by the Roe.Labute span stack behind `Words.Mpc`) so `Presentation.lean` stays at 149 for CB-4) |
| CB-FR | CB-TR's items 3–5 | opus | `GQ2/Dyadic/Count/Frozen.lean` | CB-TR ✓ | **done 2026-08-01** (0db58bc…0db971f, 7 commits → merged; 121 → 634 ln, 47 theorems, 46 exactly std-3 + 1 strict subset, no sorries, **no `decide` at all**; `mCompactFam`/`lSqFam`/`mpcFam` discharged in two lines each exactly as CB-TR predicted, generically at `omega2Exp N` then pinned BOTH ways per row; ⚠ **CB-TR's framing needed one correction**: there are **no `z2pow` nodes in `npcW` at all** — the η̂-twist is a `.profPow` at `etaHatZ η`, so what the row needs is a **second VALUE of the ℤ̂-resolver**, not a ℤ₂-resolver (`zpowHat_etaHatZ_zpow : x^ᶻη̂ = x^(1 + padicOmega2Exp (η−1) N)`); **a second sharp negative**: ω₂ kills pro-odd elements while η̂ FIXES them, so `not_constant_resolver_of_odd` — no constant resolves both at any odd order > 1 — hence `no_constant_pin_npcFam_at_six`: at exponent level 6 the procyclic-N row has **no honest constant `e` whatsoever**; ⚠ **CB-TR's "if C is a 2-group" worry does NOT materialise** — the counting target `Bg ⧸ D.M` is not a 2-group and is not assumed to be (it surjects onto the finite tame head, whose τ-image has odd order), so `e = 3` is the honest pin for the four ω₂-only rows, **which is exactly why the negative bites on the fifth**; **Stokes audit clean — no branch is pinned at an unusable `e`** (all five generic endpoint theorems are already generic in `e` under `Odd e`, and 1 is odd, so nothing was re-pinned); §6 reduces the standing `orderOf x ∣ 6` to `orderOf g ∣ 3` on the lower group — **the 6 is 2 (lift level) × 3 (τ)**) |
| CB-FR2 | the forced follow-through: **replace `npcFam`'s constant with the two-valued resolver** (the 2-group route is unavailable — the counting target is not a 2-group, which CB-FR proved), discharge `∀ g : Bg ⧸ D.M, orderOf g ∣ 3` (all that is left of `hord`), and cover the procyclic-M `.hat` display | opus | `GQ2/Dyadic/Count/Frozen.lean` | CB-FR ✓ | **dispatched 2026-08-01** |
| CB-2 | **the first of the nine clause tickets** — the scalar block (`homCard`, `cardH2`, and whatever of `lem86`/`hsep`/`hpartial` shares the factoring); CB-S moved this ticket's RISK up ("the lane's real content moved here; 900 may be optimistic") while noting the only genuine duality content is already landed by WW3b | opus | `GQ2/Dyadic/Count/Scalar.lean` (new leaf) | CB-1 ✓, CB-S ✓, CB-FR ✓ | **dispatched 2026-08-01** |
| CB-W | `hwild` | opus | `GQ2/Dyadic/Count/Wild.lean` | CB-0 ✓, F3b ✓ | **done 2026-08-01 — REFUTED, and correctly** (23beb98+860204f+7361414 → merged; 585 ln vs the 500 budget, 48 decls, 0 sorries, 15/15 headlines std-3; **`hwild` is FALSE for all five branches — CB-0's `R = 1` was not special** — so `WordCertificate n q R …` is an EMPTY type (`isEmpty_wordCertificate`); the argument is a counting fact about the DEFINITION, not any word: `gammaRelators` is a TWO-relator presentation and only one relator constrains the wild letters, so σ,τ ↦ 1 with the wild letters into ℤ/3 kills the tame relator for free and leaves ONE 𝔽₃-linear condition on `n+1 ≥ 2` unknowns, which always has a nonzero solution; the agent never needs to know what `R` is (`Marking.map_eval` computes the test value linearly from one element); **it stopped at the boundary correctly** — did not touch `GammaR`, did not axiomatize (which would have made the candidate layer INCONSISTENT, not merely unproved); ~100% generic (each branch discharge is one `omega`; Mpc needs no `1 ≤ α`); **the ℚ₂ compactness ARGUMENT transferred (§7, first try) but its HYPOTHESIS did not** — both ℚ₂ precedents run over an admissible limit whose `IsAdmissibleU` INCLUDES the `Pro2Core` clause, so pro-2-ness is built into the definition and the ~80 lines are the work of passing it to the limit; §7's `isProP_wildPartR_iff_pro2Core`/`hwild_iff_pro2Core` is exactly the clause missing from `GammaR`; **`proTwoWord`'s "landed for all five" VERIFIED correct by composition** (unlike `tameSpecialization` — but 4/5 are `h = 0`-only, and M0/Mpc need `1 ≤ α`); ⚠ its `Count/Routine.lean` complaint is STALE — that file compiles at head (the branch predated the orchestrator's merge fix), verified `routine_exit=0`) |
| GR1 | the `GammaR` definitional correction | opus | `GQ2/Dyadic/AdmissibleR.lean` (new) + `Count/WildDischarge.lean` (new) + `TameBoundary.lean` + 3 retargets | CB-W ✓ | **done 2026-08-01** (fdb641e+9722881+f2e54e1 → merged, imports registered; **`Γ_R` is now the ADMISSIBLE LIMIT** `F ⧸ N_R`, `N_R = ⋂{U open normal : both relators die in F/U ∧ the wild normal closure is a 2-group}` — `GammaA.lean:211`'s `N_A` transcribed, the pro-2 clause now INSIDE the definition as plan §1 and campaign §3 require (ℚ₂'s `Generates` clause dropped as automatic for canonical quotients, its only job being a surjectivity step GR1 does by comparing kernels); **`hwild` IS A THEOREM** — `hwild_of_tameSpecializes`/`isProP_wildPartR`, generic in n/q/R, no `1 ≤ n`, no per-branch content, **no axiom**; the five branch handles and the pilot are one-liners; **CB-W's §7 bridge discharged it EXACTLY as designed, consumed unmodified** (CB-W built the compactness half, the definition supplied the input half, no adapter); non-vacuity checked (Γ_R still surjects onto the infinite `T_q` and onto the pro-2 `D_N` — a too-large `N_R` would have made `hwild` true but empty); **CB-W's and CB-0's refutations RETAINED as true statements about `GammaBare`** — the bare two-relator presentation, now named for what it is, with `bareToGammaR` surjective and the sharpest pairing at the pilot: same word, same q, same tame specialization, `pilot_not_hwild_bare` vs `pilot_hwild`, different group; 3 declarations DELETED because they are now false (`isEmpty_wordCertificate` and two others), each replaced in place by a ⚠ note; blast radius SIX files with `CertificateMain` unchanged and compiling verbatim and **`Words/*` untouched — verified by diff and grep, not assumed** (the only `GammaR` hit there is the frozen ℚ₂ `GQ2.Roe.GammaR`); every headline std-3; **12 of 17 fields now closed, only CB-1's four analytic clauses open**; ⚠ **the coordinator's relayed question answered: the RESTRICTED form of `IsMarkedPresentation` clause (iii) survives, and this is not slack** — the plain clause is EQUIVALENT to being the bare presentation, and CB-W's ℤ/3 markings are exactly the counterexamples, so CB-MP must build the restricted form and CB-1's `z1Equiv` consumer needs the restricted hypothesis (machine: `gammaLift` + `NR_le_ker_of_isOpen`)) |
| AS1-b | adopt F3b's Gate-B entry points in `CertificateMain.lean` | opus | `GQ2/Dyadic/CertificateMain.lean` | F3b ✓ | **done 2026-08-01** (1bf1c22 → merged; **706 → 640 ln, six declarations removed, none added** — a pure reduction; the swap verified CONTENT-FREE before deleting (`TameSpecializes = TameSpec.TameSpecializes := rfl` and the `tameOfSpec` twin both compile) and repo-wide grep confirmed no consumer outside the two files; the four field bodies took the new interface with **zero source-text change** (`open TameSpec` re-resolves the bare identifiers); **`candidate_equiv_absoluteGalois`'s printed statement is BYTE-IDENTICAL to baseline**, as are all four records — the only audit diff is inside `WordCertificate.mk`, where the names now print qualified; all four headlines still exactly std-3, zero B-axioms; ⚠ **ONE SIMPLIFICATION UNAVAILABLE, compiler-confirmed**: `toSource.surj` CANNOT become `gammaR_boundary_surjective_of_spec` — that theorem is stated at the CANONICAL pro-2 quotient while `SourceDataN.surj` lives at the record's ABSTRACT slot; the agent verified by compiling the substitution and reading the type mismatch, not by reasoning, and the existing call is not by-hand (it is F3's §3 theorem — the very one the new theorem itself calls — instantiated at the abstract slot, legitimate because `ker_pro2` pins `pro2` as THE maximal pro-2 map); recorded in-file as "Owed by: nobody" since an abstract-slot twin would only re-wrap one line; `killsWild_of_tau` never appeared in this file) || AS3 | instances √2, √5 (M0) · √10, √-10 (Mpc, procyclic gate) | opus | `GQ2/Dyadic/Instances/{Sqrt2,Sqrt5,Sqrt10,SqrtNeg10}.lean` | AS1, WM0-c, WMP-c | pending |
| CB-P | the candidate-side pro-2 bridge | opus | `GQ2/Dyadic/Count/ProTwo.lean` | CB1 ✓ | **done 2026-08-01** (ad1e488…c60613f → merged, import registered; 701 ln vs the 700 budget — dead on; all 12 headlines std-3, **zero BLab, zero B8**; CB1's Labute-free measurement HELD exactly, **no new G-Lab item**; closes all four pro-2 fields with a typechecked field-fit example; hypothesis surface = one `CorePresentation` + `q ≠ 0` + `Even q`, no rank/q/α/Demushkin pin; N0 pilot at general rank 4+2h; **701 lines covers ALL five branches where ℚ₂ spent 504 on one plus a ~500-ln twin** — F3's `prop_3_4_two` already IS the generic keystone; ⚠ `presentedBy_DSq` does not exist in the repo (3-line constructor, needed before L instantiates); the other four branches each need one `CoreReindex` + a six-line restatement, **L cheapest**) |
| CB-0 | the routine `WordCertificate` fields | opus | `GQ2/Dyadic/Count/Routine.lean` | CB1 ✓ | **done 2026-08-01** (30a539b+0a4a52f → merged, import registered (+ orchestrator `open TameSpec` merge fix); 480 ln, 37 decls, 16/16 std-3; **6 of 17 fields closed**, verified at the pilot by substitution; **found the campaign's missing profinite Lemma 3.1 step** (`tqTau_zpowHat_omega2` — the composition `CertificateMain:362` asserted existed nowhere); ⚠ only THREE branches state the tame value as `= τ^{ω₂}` (M0/Mpc differ) so the generic hook is the weaker implication; ⚠ **refuted `hwild` as routine** → CB-W) |
| CB-2…CB-6 | the count lane's remaining clause tickets — `homCard`, `cardH2`, `liftsOver_card`, `lem86`, `stageR136`, `hsep`, `hpartial`, `gaussZ_unramified`, `gaussZ_ramified` (9 of the 11 `SourceDataN` clauses; CB-1 closed `tcocycle_card` + `hZcard`). **CB-S's spike shrank these ~700 ln** and CB-1 reports they are now "short derivations rather than transports", all routing through `z1Equiv`/`card_Z1_eq_card_wordZ1`, which exists. Sizes from CB1 §: scalar 900, lifting 1600, stokes 1800 (−400), gauss 1900, gauss-L 1100, gauss-M 1300, five instantiations 5×500 | opus | `GQ2/Dyadic/Count/*` | **CB-TR** (the interface must settle first) | queued — **the bulk of the remaining campaign** |
| WW6 | the `NpcJet ↔ WordCoh` bridge | opus | `GQ2/Dyadic/Word/NpcBridge.lean` (new plain leaf) | — | **done 2026-08-01** (e7887c2+c1bf638 → merged, import registered; 843 ln, 67 decls, all std-3-or-subset, 0 sorries, **no `decide`**, name hygiene scripted against all of `GQ2/`; **the carrier correspondence is the IDENTITY and nothing had to be assumed** — `Sd` and `SemiProd` are the same lambda so every `MulEquiv` field is `rfl`, the two κ⁰s agree pointwise, and **`centExtEquiv_fib` is `rfl`**, which is the load-bearing line since every NC jet value is a `.fib`; WWH's "same mathematics" measurement discharged as THEOREMS in both directions; ⚠ **a real asymmetry no report had noted: the `Word/` kit is strictly SMALLER** — six NC2 laws had no module-side statement (`cLine_inv`, `sliceElt_mul_cLine`, `cLine_mul_sliceElt`, `sliceElt_conj`, `sliceElt_sq`, the whole `y^k` power law) and are now supplied by transport; `npc_cross_operators` citable in pure `Word/` vocabulary in THREE forms incl. at the hash-pinned frozen tree; **`npcMarkingW_eq_lift`: the two lanes were never marking differently — only the carrier differed**, and WN0-b's `hessMark` at `(c₀,c₁,0)` was already right; **`HessRelZTarget` DISCHARGED on the N row** (beyond brief) and fully stated on the M row; ⚠ **the M row's remaining blocker is NOT the bridge** — it is a missing `mpcW` **jet theorem** that exists nowhere (`Certificates/Mpc.lean` never evaluates `mpcW` at a graph-type κ⁰-marking; a bridge is a transport and there was nothing to transport) → **WMP-J**; ⚠ **WWH's "unmergeable" reading was one direction too strong** — the module rule forbids `Word/Hessian` importing `NpcJet`, not the converse, and `NpcJet/Defs` already imports a module file, so retirement is POSSIBLE: costed at 111 `sliceElt` + 41 `cLine` internal occurrences but only **five external lines**, prerequisite already paid by §4 — **recommended NOT now** (touches a closed audited lane for no new mathematics); exported `finiteSemiProd` because N0.lean's `local instance` cannot be consumed downstream) |
| WMP-J | **the `mpcW` jet theorem** — the `npc_cross_operators` analogue for the procyclic-M row, which WW6 reduced the whole of WW4 gap item 5 to; also pin `d₀` from the `TwistedClass2Domain` normalization (WMP-c kept it abstract) and land the √−10 second-order counterpart of merge gate 9 | opus | `GQ2/Dyadic/Certificates/MpcJet.lean` (new leaf) | WW6 ✓, WMP-b/c/d ✓ | **dispatched 2026-08-01** |
| AS2 | **pilot instance `ℚ₂(√−2)`** (compact `N₂`) end-to-end | opus | `GQ2/Dyadic/Instances/SqrtNeg2.lean` | AS1 ✓, WN0-c ✓, **CB lane** | **BLOCKED on the CB lane** (CB-TR then the clause tickets); CB-S measured the shortest path as CB-P + CB-1, both now done, so AS2 unblocks as soon as the clause values exist |
| AS3 | instances √2, √5 (M0) · √10, √−10 (Mpc, procyclic gate) | opus | `GQ2/Dyadic/Instances/{Sqrt2,Sqrt5,Sqrt10,SqrtNeg10}.lean` | AS1 ✓, WM0-c ✓, WM0-d ✓, WMP-c ✓, WMP-d ✓, **CB lane** | **BLOCKED on the CB lane**; note **merge gate 9 is already CLOSED** (WMP-d) and √2/√5 are complete at both projector branches (WM0-d), so this is instantiation only |
| AS4 | `n = 1` wrapper: L-word machinery recovers the ℚ₂ theorem | opus | `GQ2/Dyadic/Instances/QTwo.lean` | AS1, WL-c | pending |
| AS5 | final ramified-i theorem + axiom report + acceptance appendix + trust-boundary doc | fable | `GQ2/Dyadic/Main.lean`, `docs/dyadic/literature-axioms-dyadic.md` | AS2–AS4, all WC lanes, F4 | pending |

- **AS1**: `WordCertificate` (ledger §5.2 fields: `tameSpecialization`, `proTwoSpecialization`,
  `exactLifting`, `stokes`, `scalar`, `determinant`) and `DyadicLocalInput K` (packet §12
  bundle); packet Thm. 1.1: certificates + local inputs ⇒
  `Nonempty (ContinuousMulEquiv (candidateGroup K R) G_K)` by assembling and calling SD3 —
  **the proof is assembly only**; no per-field content.
- **AS2** (gate **G2** after landing): first complete general-K result. Everything upstream is
  exercised: F3 boundary, MC-N certificate (with its hypothesis binder state per G-Lab), LG5
  at `n = 2`, WN0 certificates, SD3 at `n = 2`.
- **AS3**: the quadratic-field table; **merge-gate 9: √-10 via procyclic `(1,1,1)`**;
  cross-check counts vs F5 harness (regression note only, not proof).
- **AS4**: merge-gate 8 witness — existing ℚ₂ capstone names still compile and the new `n = 1`
  route reproduces the statement (cross-identification with
  `main_presentation_literal`/`_roe`).
- **AS5**: `Γ_{R_K} ≅ G_K` for every ramified-i `K` (branch-by-branch via F4 exhaustiveness);
  `#print axioms` report per branch capstone (std-3 + documented census only);
  `literature-axioms-dyadic.md` (trust boundary — extends `docs/literature-axioms.md` style);
  run WW5 acceptance-appendix generation for all five branches; extend `check_axioms.sh`
  check-5 capstone list (F6's script); board archived; owner gate **G3**.

## Standing notes for dispatch prompts

- Repo conventions: `lake build` from the worktree root; mathlib pinned (`lakefile.toml`);
  toolchain v4.31.0-rc2; `lake exe cache get` once per new worktree.
- The ℚ₂ development is **frozen** (plan A6): generalize by new files + wrappers; in-place
  edits only where a lane's design memo lists them and the orchestrator approved.
- Copyright header (Apache 2.0, authors line) per existing files; namespace `GQ2.Dyadic`.
- Cite packet/draft/ledger by anchor (e.g. "packet Prop. 8.1", "draft eq:Mpc-word",
  "ledger §7") — all vendored under `docs/dyadic/refs/`.
- When a ticket discovers a statement is false or a hypothesis is missing: stop, report,
  do not "fix" the mathematics silently — the packet governs; deviations go to the
  orchestrator log.
