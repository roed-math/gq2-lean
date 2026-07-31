# Dyadic campaign — formalization plan (general 2-adic fields, ramified-i case)

**Created 2026-07-28.** Owner brief: extend the `gq2-lean` formalization of the `G_{ℚ₂}`
presentation to all finite `K/ℚ₂` with `K(i)/K` ramified (Diekert 1984 covers the unramified-`i`
case and is out of scope for Lean here — the final theorem is the ramified-`i` statement).
Work lives on branch **`dyadic`**; `master` stays focused on `ℚ₂`. Board:
[`tickets.md`](tickets.md). References + authority order: [`refs/README.md`](refs/README.md).
Recon surveys (repo state at `d0714a7`): [`recon/`](recon/).

> **✅ 2026-07-31 — GATE G-1 RELEASED.** The simplification campaign signed R0–R5; the word
> selection is **FROZEN** at `general_2adic/artifacts/reports/selection-freeze.md` (the five
> rows + certificate hashes + per-row Lean-facing obligations). Headlines: type L = **`L_sq`**
> (stabilized square-commutator; rank-3 core = `GQ2.drWord`, orientation theorem
> `marked_square_core_rank3` already committed); compact N unchanged; noncompact N with the
> **corrected `L_c = A⁻¹+B+BA⁻¹`** (NC lane theorem); compact M with `E_m^rev`; procyclic M
> at **L = 67** with the `E₂^pc` orbit-norm block and the shadow copy (√−10 = procyclic
> `(1,1,1)`; the relative-norm word retired to regression-only). Word-dependent lanes
> (WW, W*, AS) and SD-n are released; the board log's 2026-07-31 entry carries the lane
> re-points (⚠ WL's spec was written against the collector — re-pointed at `L_sq`).
>
> *(Historical: campaign held at G-1 2026-07-29 → 31 while the simplification campaign ran;
> word-independent lanes were owner-released early and largely completed in that window.)*

## 0. Binding constraints (owner directives, 2026-07-28)

1. **The nine obligations MC-M, MC-N, WC-L, WC-N0, WC-Npc, WC-M0, WC-Mpc, LG-K, SD-n are proof
   obligations, never axioms** — not even temporarily. Permitted interim states: explicit
   hypothesis binders (the `BLabHypothesis` pattern) and `SORRY_ALLOWLIST`-listed in-flight
   files. Never an `axiom` declaration.
2. **The proof packet overrides the drafts wherever they disagree** (override list in
   `refs/README.md`; headline: no sign-Frobenius row in ramified-`i`; `ℚ₂(√-10)` is procyclic
   `M₂` with `(r,ε,η) = (1,1,1)`).
3. **Axiom hygiene is unchanged**: every nonstandard axiom must be an independently published
   input, lives only in `GQ2/Foundations/Axioms.lean`, is owner-approved before insertion
   (census bump in the same commit), and is enforced by `scripts/check_axioms.sh`
   (kernel `decide` only, no `native_decide`, no field-specific presentation-isomorphism
   axiom, no theorem whose proof is a finite-target test).

## 1. Mathematical target

For `K/ℚ₂` finite with `K(i)/K` ramified, `n = [K:ℚ₂]`, `q_K = 2^f`:

```
Γ_R = ⟨ σ, τ, x₀, …, x_n | τ^σ = τ^{q_K}, R = 1, ⟪x₀,…,x_n⟫-closure pro-2 ⟩_prof
```

with `R` one of five families (packet corrects the draft's six):

| branch | applies to | word (draft ref) | pro-2 core | quadratic endpoint (ledger §7) | obligation |
|---|---|---|---|---|---|
| `L` | `n` odd | eq:Lword | `P_{L,n}` (eq:Lcore) | existing `n=1` core + hyperbolic handles | **WC-L** |
| `N` compact | `N_α`, `r=0` | eq:Ncompact-word | eq:Ncompact-core | `q(c₀)+b_q(c₀,c₁)` | **WC-N0** |
| `N` procyclic | `N_α`, `r≥1` | eq:Npc-word | eq:Npc-core | `Q₀(c₀)+b_q(c₁,L_c c₀)`, `L_c` invertible | **WC-Npc** |
| `M` compact | `M_α`, `r=0` | eq:Mcompact-word | (compact `M` core) | two projector forms, explicit change of vars | **WC-M0** |
| `M` procyclic | `M_α`, `r≥1` (`η` odd — automatic in ramified-`i`) | eq:Mpc-word | eq:Mpc-core | self-replication cancellation + split form incl. every `T`-dependent central term | **WC-Mpc** |

**Main theorem shape** (packet Thm 1.1, "kernel-checkable"): marked-core certificate (packet
Def. 7.1) + word certificate (packet Def. 9.1) + standard local inputs (packet §12) ⇒
`Γ_{R_K} ≅ G_K`, identifying tame quotient, maximal pro-2 quotient, cyclotomic orientation,
and the full `ℤ₂`-valued unramified character. The final Lean theorem assembles certificates
and calls the degree-`n` source-generic reconstruction — no per-field isomorphism axiom.

## 2. The nine obligations → lanes

| ID | content (packet §14 completion criterion) | lane | key insight from recon |
|---|---|---|---|
| **SD-n** | replace hard-coded `8`, `\|V\|²`, base Gauss exponent in `SourceData` by parameter fields; induction unchanged | SD | record has 5 degree-one *value* fields + 2 degree-one *type* fields (`Ttame` q=2, `PiBd` rank-3); **the `G_ℚ₂` target slot is pinned** — the parameterized theorem must be the packet's two-sided Thm 11.1 (`S₁,S₂` both records), with the B-side `*_local` lemmas becoming the `G_K` record instantiation |
| **MC-M** | rank-four `M_α` marked automorphism lifting: finite Nielsen-generator list lifts the Smith–Witt stabilizer on the abelianization | MC | rank-3 route fully mapped (classify on `D^ab` via a coordinate frame → lift by explicit generator-word automorphisms → matching engine); strategy rank-generic, code 100% rank-3-hardwired; new cores are *presented* groups so lifts are presentation-side (no B8) |
| **MC-N** | same for the `N_α` relation vector and cup form | MC | ditto; `N` and `M` have different torsion structure ⇒ two genuinely different 4-frames |
| **WC-L** | universal word certificate for `R_L`; `n=1` base + handle stability | WL | Stokes layer already `n`-generic; word syntax/certificates must be built (F2/WW lane) |
| **WC-N0** | compact `N_α` certificate; unramified block must contain the invertible `1−S^{-1}` from `x₂^{-σ}` | WN0 | first end-to-end pilot (`ℚ₂(√-2)`) |
| **WC-Npc** | noncompact `N_α`: replay `E_{r,η}` symbolically; cross operators `M_c = A`, `L_c = A^{-1}` for all allowed `r,η` | WNP | |
| **WC-M0** | compact `M_α`: reversed correction order; both projector normal forms | WM0 | forward order provably singular on a 5th-root orbit — regression must catch |
| **WC-Mpc** | procyclic `M_α`: both linear and self-replicating copies, all `T`-dependent central terms, affine phases | WMP | hardest word; includes the `ℚ₂(√-10)` gate |
| **LG-K** | field-generic deep-unit package; square-class filtration as named local input | LG | ~4,400 lines already field-generic; ~6,700 lines mechanical retyping (`AbsGalQ2` → `IsLocalDualizingGroup G 2`); genuinely new: general-K Euler char (try-derive via Shapiro), general tame quotient `q_K`, `(−1)^n` parity threading (parity engines exist) |

Plus shared foundations (F lane) and assembly (AS lane) that are not themselves listed
obligations: parameters/branch data, reflected word syntax, general tame boundary
(packet §3: `O₂(T_q)=1`, specializations, relative Goursat), arithmetic branch corrections
(packet §8), certificate-main assembly, field instances.

## 3. Architecture decisions

**A1 — Reflected word syntax (`PWord`) is the word-level backbone** (packet §9.1 checker
design). One inductive syntax `one | gen | mul | inv | conj | comm | zpow (ℤ) | z2pow (ℤ₂) |
profPow (Ẑ)` over `Generator n = σ | τ | wild (Fin (n+1))`, with:
- denotation into any profinite group via a marking (`zpowHat` for `profPow`), and into any
  finite group via packet Lem. 2.2 finite ω₂-evaluation — generating *once, generically* the
  "profinite form / ℕ-exponent form / `_eq_` bridge / `_map` naturality" quadruple that the
  ℚ₂ development hand-writes per word (~4 lemmas × word; see `recon/wc-survey.md` §1c);
- generic Fox (`WordLift`), Stokes (`HeisLift`), and extraspecial evaluators by structural
  recursion, plugging into the already-`n`-generic `stokesEval`/`lemma_5_7_*`/`MixedBilinear`
  layer;
- certificate structures `FoxCertificate` (elementary row/col op lists + replay),
  `HessianCertificate` (change of variables + polar + quadratic + affine-phase data) — kernel
  `decide`/`rfl` replay only, no CAS trust;
- the one-expression-tree TeX generator + hash (merge gate: paper formulas generated from the
  same tree as Lean).
Rationale: five branch families × (Fox + Stokes + Hessian + two specializations) ≫ the cost of
the evaluator; and the acceptance-appendix + one-tree gates are otherwise unmeetable.
Adapters at `n=1` cross-check the generic rows against the existing Γ_A/Γ_R hand rows
(regression, not replacement — the ℚ₂ development is frozen).

**A2 — SD-n goes two-sided.** `thm_4_2_of_sources` currently proves
`exactImageCount S.b = exactImageCount B.bF` with the B-side pinned to `G_ℚ₂` twins
(`lemma_8_2_local`, `stageR136_local`, `phase140_local`, …). The degree-`n` version takes two
parameterized records (packet Thm 11.1) so that `G_K` enters as a record instantiation whose
leaves are supplied by LG-K + the boundary + the general local inputs. The recursion skeleton
(`SectionNine/Induction.lean` strong induction) is untouched; the literal `8`/`^2` shapes in
`lemma_8_3`/`ClosedRecursion` become `2^(n+2)`/`^(n+1)` parameters. `n=1` wrappers must
reproduce the current records definitionally (existing capstones keep compiling, byte-identical
axiom prints).

**A3 — MC follows the D_R pattern, not the D₀ pattern.** The standard cores `D_P` are
*presented* pro-2 groups (like `DR`), so: presentation via `profinitePresentation`
(rank-generic already), abelian 4-frames per core family (new math — `M` and `N` differ),
classification of orientation/relation-vector/cup-preserving automorphisms of `D_P^ab`
uniformly in `α`, lifts as explicit generator-word automorphisms (Nielsen moves — no B8
dependence), then the marked-matching engine (masters → mod-2 span → invertible eval matrix →
solve → contract) ported from `Fin 3` to `Fin 4`. Hyperbolic handles by Nielsen moves
preserving the commutator product. The **abstract Demushkin isomorphism `D_P ≅ D_K`**
(packet Def. 7.1 item 1) is threaded as per-core hypothesis `def`s
(`MLabHypothesis α n` / `NLabHypothesis α n` — the `BLabHypothesis` pattern, an explicit
binder, never an axiom); discharge route = owner gate **G-Lab** (options: rank-four levelwise
campaign à la `GQ2/Roe/Labute/`; or an owner-approved published-literature axiom
(Labute 1967); or stay hypothesis-parametrized).

**A4 — LG-K rebasing strategy: parameterize in place where a file is already
`IntermediateField`-generic, clone-and-retype where it is `AbsGalQ2`-typed.** The abstraction
target `IsLocalDualizingGroup G 2` + `TateDualityG G 2` already exists and B6 is already
quantified over it. The three genuinely new pieces: (i) general-K Euler characteristic —
**try-derive-first** from ℚ₂-B7 via Shapiro/induced modules (`Shapiro.finite_H1_open`
precedent) before proposing an axiom; (ii) oriented tame quotient at `q_K = 2^f` (axiom
extension of B5/B10, published); (iii) `(−1)^n` unramified parity via the existing
`arf_eq_of_free*` engines' `s`-slot.

**A5 — File/namespace layout.** New code in `GQ2/Dyadic/` (namespace `GQ2.Dyadic`), one import
line per file in `GQ2.lean` (orchestrator-owned). Files:

```
GQ2/Dyadic/Parameters.lean            F1   params, Generator n, Marking n, branch data
GQ2/Dyadic/Word/Syntax.lean           F2   PWord + denotations + ω₂ finite evaluation
GQ2/Dyadic/Word/Eval.lean             F2   naturality, two-form bridges, specialization maps
GQ2/Dyadic/TameBoundary.lean          F3   T_{q}, O₂=1, specializations, relative Goursat
GQ2/Dyadic/Branches.lean              F4   (C,I,λ,γ), sign-row exclusion, √-10 corollary
GQ2/Dyadic/Word/Fox.lean              WW1  generic Fox evaluator + defect formula
GQ2/Dyadic/Word/FoxCert.lean          WW2  row/col-op certificates + replay
GQ2/Dyadic/Word/Stokes.lean           WW3  Heisenberg second order + chain map + 5-lemma ext
GQ2/Dyadic/Word/Hessian.lean          WW4  extraspecial evaluator + HessianCertificate
GQ2/Dyadic/Word/Phase.lean            WW4  affine Gauss translation + phase-cover interface
GQ2/Dyadic/MarkedCore/Cores.lean      MC2  presented D_P per family, χ_P, ν_P, abelian frames
GQ2/Dyadic/MarkedCore/M.lean          MC3  MC-M
GQ2/Dyadic/MarkedCore/N.lean          MC4  MC-N
GQ2/Dyadic/MarkedCore/Certificate.lean MC5 handles + MarkedCoreCertificate + marked reduction
GQ2/Dyadic/LocalGauss/…               LG2–LG5 (Unramified, DeepPackage, Ramified, Main)
GQ2/Dyadic/SourceDataN.lean           SD2  parameterized record + n=1 adapter
GQ2/Dyadic/ThmFourTwoN.lean           SD3  two-sided degree-n induction
GQ2/Dyadic/Words/{L,N0,Npc,M0,Mpc}.lean        branch words + boundary specializations
GQ2/Dyadic/Certificates/{L,N0,Npc,M0,Mpc}.lean branch Fox/Stokes/scalar/Hessian certificates
GQ2/Dyadic/CertificateMain.lean       AS1  packet Thm 1.1 assembly
GQ2/Dyadic/Instances/…                AS2–AS4 (√-2, √2, √5, √10, √-10, n=1 wrapper)
GQ2/Dyadic/Main.lean                  AS5  final ramified-i theorem + axiom report
scripts/dyadic_sanity_counts.py       F5   finite-target regressions (S₃/D₈/A₄)
scripts/dyadic_word_tex.py            WW5  one-expression-tree TeX + hash
```

⚠ **Module-system rule** (R31a pitfall, one-directional): `module`-style files cannot import
plain-import files. `SourceData`/`ThmFourTwo`/`Prop89Close`/`SectionNine`/`Roe/Main` are
plain-import, so `SourceDataN.lean`, `ThmFourTwoN.lean`, `CertificateMain.lean`, `Main.lean`,
and anything else above the §8/§9 stack **must be plain-import**. Leaf files (Parameters, Word/*,
MarkedCore/*, LocalGauss/* where they avoid the stack) should be `module`-style like the rest of
the library when their imports allow. Workers check imports before choosing the header; when in
doubt, plain-import.

**A6 — ℚ₂ path is frozen.** No behavioral edits to existing ℚ₂ theorems. Where SD-n or LG-K
must generalize a shared file in place, existing declaration names keep working (wrappers), the
full build stays green, and the audited ℚ₂ capstones print byte-identical axiom sets
(`scripts/check_axioms.sh` check 5).

## 4. Axiom plan (owner-gated lane AX)

Already general enough (no work): **B6** `tateDualityAt` (any local dualizing `G`), **B9**
`relativeStiefelWhitney_dyadic` (any finite dyadic base), **B11a**
`hilbertSymbol_normCriterion_finiteDyadic` (any finite dyadic base); discharged-generic
theorems `dyadicUnitFiltration'` (unit filtration, any finite `k/ℚ₂`), `Shapiro.finite_H1_open`.

Extensions to propose (each: statement-design memo → owner sign-off → census bump in the same
commit; all are published inputs per packet §12):

| ID | content | extends | citation | note |
|---|---|---|---|---|
| AX1 | `G_K` topologically finitely generated (`n+2` generators) | B1 | NSW 7.4.1 | needed by reconstruction at `K` |
| AX2 | local Euler characteristic over `K` | B7 | NSW 7.3.1 | **try-derive-first** from ℚ₂-B7 via Shapiro (`finite_H1_open` precedent); axiom only on failure |
| AX3 | marked local reciprocity over `K`: full `ℤ₂`-valued `ν_ur` + marked cyclotomic quotient `(C,I,λ,γ)` (packet `MarkedRecip`) | B5, B3c | Serre LF; NSW VII | feeds B1-boundary, branch classification, MC5 |
| AX4 | oriented tame quotient of `G_K` at `q_K = 2^f` | B10 | NSW 7.5; Serre LF IV | pairs with AX3 normalization |
| AX5 | faithful ramified simple tame `𝔽₂[H]`-module is projective | — | Rim / Curtis–Reiner | **try-prove-first** (module free over Sylow ⇒ projective may be within reach) |
| AX6 | Shapiro–Evens normalized orbit formula over `K` | B9? | Evens 1963; Kahn 1984 | likely **not needed**: `Shapiro/Deepness.lean` producers already abstract + B9 already base-general — LG1 confirms |
| — | Demushkin classification for rank-four cores | — | Labute 1967 | **NOT an axiom by default** — per-core hypothesis `def`s (A3), owner gate G-Lab |

The trust boundary must never contain an assertion that a candidate word presents `G_K`
(packet §12), and never any of the nine obligations (§0.1).

## 5. Parallelism protocol (worktrees + file ownership)

The roe campaign ran one shared worktree and documented shared-index races; this campaign uses
**per-lane worktrees** instead:

- Integration: branch `dyadic`, worktree `~/claude/gq2-dyadic`. Orchestrator-only writes
  (board, GQ2.lean import registry, merges, docs).
- Lane `X` ∈ {F, SD, MC, LG, WW, WN0, WM0, WNP, WMP, WL, AS}: branch `dyadic-x`, worktree
  `~/claude/gq2-dyadic-x`, created from `dyadic` at first dispatch
  (`git -C ~/claude/gq2-lean worktree add ~/claude/gq2-dyadic-x -b dyadic-x dyadic`;
  then `cd … && lake exe cache get` before first build). Keep ≤ 4–5 lane worktrees alive at
  once (disk); `git worktree remove` when a lane closes.
- **File ownership is exclusive per ticket** (the "files owned" board column). Two lanes never
  own the same file. Cross-lane needs go through the orchestrator (either re-assignment or a
  merge into `dyadic` followed by lane rebases).
- Workers commit **path-limited** (`git commit -- <files>`) on green, message
  `dyadic <ID>: <summary>`; commit fast after green (uncommitted tracked edits have been lost
  to swarm resets before). Workers NEVER edit the board and NEVER merge; they end with a report
  (files, commit hash, sorry/axiom state, deviations, discoveries affecting later tickets).
- Orchestrator merges lane → `dyadic` at ticket or wave boundaries (after running
  `scripts/check_axioms.sh` + full build in the integration worktree), updates the board, and
  periodically merges `master` → `dyadic` if `master` moves.
- `GQ2.lean`: workers touch it only to add the import line for a NEW file they create,
  committed path-limited together with that file.
- Model tiers: **fable** = design tickets and hard seams; **opus** = well-specified fills.
  One ticket = one agent dispatch.

## 6. Gates

| gate | trigger | content |
|---|---|---|
| **G-1** | simplification campaign R5 (word selection frozen) | **RELEASED 2026-07-31** (R5 flipped; freeze doc = `selection-freeze.md`): word-dependent lanes released; WW/W*/AS re-pointed at the frozen words + generated definitions (S5.G emits them); SD-n un-gated per the simplification doc §12.1 |
| **G0** | after G-1 (word-independent lanes may be owner-released earlier) | **satisfied 2026-07-31** (owner-delegated with the R4/R5 instruction, flagged for override — the plan+board have been operating under progressive owner releases since R0) |
| **G1** | F1+F2 land | API freeze: `Generator n`/`Marking n`/`PWord` signatures reviewed before the four lanes fork (everything downstream consumes them) |
| **G-Lab** | MC5 statement lands | owner picks the discharge route for the per-core Demushkin-classification hypotheses (levelwise campaign / published axiom / stay parametrized) |
| **G-AX** | per AX ticket | owner approves each census flip (b9a checklist template) |
| **G2** | AS2 lands | end-to-end review of the `ℚ₂(√-2)` pilot before mass-producing the other four branches |
| **G3** | AS5 lands | final census sign-off; decide whether/when `dyadic` merges to `master` |

## 7. Merge gates (mechanical; every lane → `dyadic` merge)

1. Full build green in the lane worktree; `scripts/check_axioms.sh` passes on the merge result.
2. No `sorry` outside `SORRY_ALLOWLIST`-ticketed in-flight files; allowlist empty at wave close.
3. No new `axiom` outside owner-approved AX tickets (census count exact, bumped in-commit).
4. None of the nine obligations appears as an `axiom` (grep-level check; they may appear as
   hypothesis `def`s or allowlisted sorries only).
5. No field-specific presentation-isomorphism axiom; no theorem proved by finite-target testing
   (finite-target counts live in `scripts/` + `Sanity`-style stress lemmas only).
6. Full `ℤ₂`-valued unramified marking in every marked statement (mod-2 is not enough).
7. Branch words: TeX and Lean generated from one expression tree (WW5 hash check), explicit
   Fox/Hessian certificate replay, affine phase interface present (not just base Gauss signs).
8. `n=1` wrappers keep every existing ℚ₂ theorem name compiling; audited ℚ₂ capstones print
   byte-identical axiom sets.
9. `ℚ₂(√-10)` instance uses the procyclic row `(r,ε,η) = (1,1,1)`.
10. Kernel `decide` only; no `native_decide`; no unchecked CAS equality.

## 8. Wave graph (details on the board)

```
W0  F1 → F2 → (G1) → F3, F4;  F5, F6 parallel;  SD1/MC1/LG1 recon may start immediately
W1  SD lane ∥ MC lane ∥ LG lane ∥ WW lane   (+ AX statement memos; G-Lab, G-AX)
W2  WN0 pilot → (G2) → WM0 ∥ WNP ∥ WMP ∥ WL   (word certificates per branch)
W3  AS1 (certificate-main) → AS2–AS4 (instances) → AS5 (main theorem + census report) → (G3)
```

Critical path: F2 → WW1/WW2 → WN0 → AS1 → AS2. Fattest tail: G-Lab discharge (if the owner
orders rank-four levelwise campaigns, they are `GQ2/Roe/Labute/`-sized per core family) and
WMP (the self-replicating procyclic `M` word).
