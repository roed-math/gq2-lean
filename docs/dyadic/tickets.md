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

## Obligation tracker

| obligation | tickets | status |
|---|---|---|
| SD-n | SD1 → SD2 → SD3 | pending |
| MC-M | MC1 → MC2 → MC3 (+MC5) | pending |
| MC-N | MC1 → MC2 → MC4 (+MC5) | pending |
| LG-K | LG1 ✓ → LG2a/LG2 → LG3/LG4a/LG4b → LG5 | in progress |
| WC-N0 | F2, WW1–WW5 → WN0-a/b/c | pending |
| WC-M0 | F2, WW1–WW5 → WM0-a/b/c | pending |
| WC-Npc | F2, WW1–WW5 → WNP-a/b/c | pending |
| WC-Mpc | F2, WW1–WW5 → WMP-a/b/c | pending |
| WC-L | F2, WW1–WW5 → WL-a/b/c | pending |

## Wave 0 — foundations (lane F, worktree `gq2-dyadic-f`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| F0 | campaign setup: branch, worktree, refs, surveys, plan, board | — (orchestrator) | `docs/dyadic/**` | — | **done 2026-07-28** |
| F1 | parameters, semantic generators, markings, branch data | opus | `GQ2/Dyadic/Parameters.lean` | — | **done 2026-07-29** (f7c8d05 → merged; 906 ln, 163 decls, 0 sorries, std-3; module-style; η:ℤ₂ˣ + etaUnit hook, ε:Bool; Marking n FunLike + n=1 equivQ2 adapter; equivFin fixes Fox column order; import registered by orchestrator; independently re-typechecked) |
| F2 | reflected profinite word syntax + ω₂ finite evaluation | opus (was fable) | `GQ2/Dyadic/Word/Syntax.lean`, `GQ2/Dyadic/Word/Eval.lean` | F1 | **re-dispatched 2026-07-29 (opus)** with S1.M EtaHat-canonical note + build-in-worktree protocol adaptation (see log) |
| F3 | tame quotient at general q + boundary specializations + relative Goursat | opus | `GQ2/Dyadic/TameBoundary.lean` | F1, F2 | pending |
| F4 | arithmetic branches: (C,I,λ,γ), sign-row exclusion, √-10 corollary | opus | `GQ2/Dyadic/Branches.lean` | F1 | pending |
| F5 | finite-target sanity harness (python) | opus | `scripts/dyadic_sanity_counts.py` | — | pending |
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
| SD1 | design memo: two-sided degree-n source record | fable | `docs/dyadic/sd-design.md` | recon/sd-survey | pending |
| SD2 | `SourceNumerics n` + parameterized record + n=1 adapters | fable | `GQ2/Dyadic/SourceDataN.lean` (+approved edits per SD1) | SD1, F1 | pending |
| SD3 | two-sided degree-n induction + ℚ₂ regression | opus | `GQ2/Dyadic/ThmFourTwoN.lean` (+approved edits per SD1) | SD2 | pending |

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
| MC1 | design memo: rank-four frames, Smith–Witt stabilizer generators, lifting strategy | opus (was fable) | `docs/dyadic/mc-design.md` | recon/mc-survey | **re-dispatched 2026-07-29 (opus)**, worktree synced to 0ed4244 |
| MC2 | presented cores D_P, characters, abelian 4-frames | opus | `GQ2/Dyadic/MarkedCore/Cores.lean` | MC1, F1 | pending |
| MC3 | **MC-M**: classification + lifting for `M_α` (uniform in α) | fable | `GQ2/Dyadic/MarkedCore/M.lean` | MC2 | pending |
| MC4 | **MC-N**: classification + lifting for `N_α` (uniform in α) | fable | `GQ2/Dyadic/MarkedCore/N.lean` | MC2 | pending |
| MC5 | handles + `MarkedCoreCertificate` + marked-matching reduction | opus | `GQ2/Dyadic/MarkedCore/Certificate.lean` | MC3, MC4 | pending |

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
| LG2 | group-generic `Q⁰` + polarization over a local dualizing source | opus | `GQ2/Dyadic/LocalGauss/Q0.lean` (+clone-retype list per LG1) | LG1 | pending |
| LG3 | unramified sign `(−1)^n 2^{nd/2}` (Hermitian rank-n) | opus | `GQ2/Dyadic/LocalGauss/Unramified.lean` | LG2, AX2 | pending |
| LG4 | **deep-unit package + ramified sign `+2^{nd/2}`** | fable | `GQ2/Dyadic/LocalGauss/DeepPackage.lean`, `…/Ramified.lean` | LG2 | pending |
| LG5 | assemble general local Gauss theorem + n=1/n=2 regressions | opus | `GQ2/Dyadic/LocalGauss/Main.lean` | LG3, LG4 | pending |

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
| WW1 | generic Fox evaluator + literal defect formula | fable | `GQ2/Dyadic/Word/Fox.lean` | F2 | pending |
| WW2 | Fox certificates: row/col ops + replay + normal forms | fable | `GQ2/Dyadic/Word/FoxCert.lean` | WW1 | pending |
| WW3 | Stokes chain map + composition-series extension | fable | `GQ2/Dyadic/Word/Stokes.lean` | F2 | pending |
| WW4 | Hessian certificates + affine phase interface | fable | `GQ2/Dyadic/Word/Hessian.lean`, `GQ2/Dyadic/Word/Phase.lean` | WW3 | pending |
| WW5 | one-expression-tree TeX generator + hash gate | opus | `scripts/dyadic_word_tex.py`, `GQ2/Dyadic/Word/Export.lean` | F2 | pending |

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
| AX3 | marked local reciprocity over `K` (`MarkedRecip`: full ν_ur + `(C,I,λ,γ)`) | fable | `docs/dyadic/ax3-proposal.md` | — | **done 2026-07-29** (1c6ec04 → merged; ONE axiom proposed: `markedRecipAt`, 12-field `MarkedRecip R K`, census +1→10 **pending owner G-AX**; χ_K/C derivable, ν_ur^K+rec_K axiom-backed, λ/I/γ derived; (r,ε,η) extraction API + 5 instance vectors; ⚠ synthetic r=2 mock test mandated; owner Qs 1–7 in memo) |
| AX4 | oriented tame quotient of `G_K` at `q_K` | opus | `docs/dyadic/ax4-proposal.md` | AX3 | **done 2026-07-29** (56b565c → merged; **genuine axiom, +1 → census 11 with AX3, owner-gated**; 5-clause `OrientedTameQuotientK (markedRecipAt K) FF` parametrized by `DyadicUnitFiltration` — SOUNDNESS-CRITICAL (free f proves False: T₂ᵃᵇ=Ẑ vs T₄ᵃᵇ=Ẑ×ℤ/3); AX3-before-AX4 flip ordering; √5 (q_K=4) is the ONLY q≠2 instance — #Hom(T_q,ℤ/3) regression mandated; owner Qs 1–8) |
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
| WN0-a | word + boundary specializations + sanity pins | opus | `GQ2/Dyadic/Words/N0.lean` | F1–F4, WW5, MC2 | pending |
| WN0-b | Fox certificate (invertible `1−S^{-1}` unramified block) | opus | `GQ2/Dyadic/Certificates/N0Fox.lean` | WN0-a, WW1, WW2 | pending |
| WN0-c | Stokes + scalar + Hessian + phase certificates | fable | `GQ2/Dyadic/Certificates/N0.lean` | WN0-b, WW3, WW4 | pending |

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
| WM0-a | word + boundary + sanity (incl. reversed-`E_m` mutant rejection) | opus | `GQ2/Dyadic/Words/M0.lean` | G2 | pending |
| WM0-b | Fox certificate (reversed correction order) | opus | `GQ2/Dyadic/Certificates/M0Fox.lean` | WM0-a | pending |
| WM0-c | Stokes/scalar/Hessian/phase: **both projector normal forms** | fable | `GQ2/Dyadic/Certificates/M0.lean` | WM0-b | pending |

- `R_{M,0} = A₀²[A₀,x₁]σ₂^{2m}·J₂·E_m^rev·H_h` with `A₀ = x₀^{-1}σ₂^{-m}`,
  `J₂ = x₂^{-σ}(x₂τ)^{ω₂}`, `E_m^rev = δ₁^{σ₂^{2m}}δ₁^{σ₂^m}δ₀^{σ₂^m}δ₀` (draft
  eq:Mcompact-word); pro-2 core `A₀²[A₀,x₁]σ^{2m}[σ,x₂]` with `2m = 2^α` (packet Prop. 9.2).
  Forward `E_m` order is **singular** on a primitive-5th-root orbit (det
  `R^{-2}(1+R+R²+R³+R⁴)`) — F5 mutant row must reject it. Projector cases `P=1`:
  `q(c₀)+b_q(c₀,c₁)`, `P=0`: `q(c₁)+b_q(c₀,c₁)`, each with explicit change of variables
  (ledger §7). Instances √2 (`m=4`) and √5 (`m=2`) pinned in AS3.

### Lane WNP — WC-Npc, procyclic `N_α` (worktree `gq2-dyadic-wnp`)

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| WNP-a | word + boundary + sanity | opus | `GQ2/Dyadic/Words/Npc.lean` | G2 | pending |
| WNP-b | Fox certificate: replay `E_{r,η}`, cross operators for ALL allowed `(r,η)` | fable | `GQ2/Dyadic/Certificates/NpcFox.lean` | WNP-a | pending |
| WNP-c | Stokes/scalar/Hessian/phase (`Q₀(c₀)+b_q(c₁,L_c c₀)`, explicit invertible `L_c`) | fable | `GQ2/Dyadic/Certificates/Npc.lean` | WNP-b | pending |

- `R_{N,α,r,η} = x₀^{p_α}[x₀,σ^{η̂}]·x₂^{-g}(x₂τ)^{ω₂}·E_{r,η}·H_h`, `g = x₁σ^{2^r}`,
  `D_{r,η} = δ₀^{σ^{η̂}}δ₀^{σ^{−2^r}}δ₀^{σ^{η̂−2^r}}`, `E_{r,η} = [D_{r,η}, x₁]` (draft
  eq:Npc-word; `η̂ ∈ Ẑˣ` = 2-component η, odd components 1). `E_{r,η}` is invisible at
  tame/pro-2/first Fox order, essential at second order: cross operators become `M_c = A`,
  `L_c = A^{-1}` with `A = S^{η̂}`, `B = S^{2^r}` (draft eq:Ncross) — certificates must cover
  **all** `r ≥ 1`, `η ∈ ℤ₂ˣ` symbolically. Sanity: the 2-dim `S₃`-module radical detection for
  the uncorrected word (mutant row).

### Lane WMP — WC-Mpc, procyclic `M_α` (worktree `gq2-dyadic-wmp`) — hardest word

| id | title | model | files owned | depends on | status |
|---|---|---|---|---|---|
| WMP-a | word (both copies) + boundary + sanity (√-10 procyclic + relative-norm alternative + order-9 negative test) | fable | `GQ2/Dyadic/Words/Mpc.lean` | G2 | pending |
| WMP-b | Fox certificate (linear copy; hat copy has zero first derivative) | fable | `GQ2/Dyadic/Certificates/MpcFox.lean` | WMP-a | pending |
| WMP-c | Stokes/scalar/Hessian/phase: **self-replication cancellation incl. every `T`-dependent central term** | fable | `GQ2/Dyadic/Certificates/Mpc.lean` | WMP-b | pending |

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
| WL-a | word + boundary + sanity | opus | `GQ2/Dyadic/Words/L.lean` | G2 | pending |
| WL-b | Fox certificate (`n=1` base + handle stability) | opus | `GQ2/Dyadic/Certificates/LFox.lean` | WL-a | pending |
| WL-c | Stokes/scalar/Hessian/phase (`n=1` core + hyperbolic handles) | fable | `GQ2/Dyadic/Certificates/L.lean` | WL-b | pending |

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
| AS1 | `WordCertificate` + `DyadicLocalInput` records + certificate-main theorem | fable | `GQ2/Dyadic/CertificateMain.lean` | SD3, MC5, LG5, WW1–WW4 | pending |
| AS2 | **pilot instance `ℚ₂(√-2)`** (compact `N₂`) end-to-end | opus | `GQ2/Dyadic/Instances/SqrtNeg2.lean` | AS1, WN0-c | pending |
| AS3 | instances √2, √5 (M0) · √10, √-10 (Mpc, procyclic gate) | opus | `GQ2/Dyadic/Instances/{Sqrt2,Sqrt5,Sqrt10,SqrtNeg10}.lean` | AS1, WM0-c, WMP-c | pending |
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
