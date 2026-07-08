# Step 2 — proving Theorem 1.2 from the axioms

Master plan for the proof phase.  Step 1 (statement formalization, [`tickets-step1.md`](tickets-step1.md))
delivered the axiom layer; step 2 proves the paper's own tower — §§2–10 — **from** those axioms,
ending with a sorry-free `main_presentation_literal`.  The live board is [`tickets.md`](tickets.md)
(IDs `P-xx`); this file is the rationale and the dependency map.

The paper is **in-repo**: `paper/A_Profinite_Presentation_for_G__Q_2.pdf` (readable per page
range).  The DAG below refines `docs/proof-architecture.md` (written before step 1; its `P`/`H`
infrastructure gaps are now the ten axioms plus this repo's def-layers) using the paper's App. D
dependency certificate as recorded in `docs/literature-axioms.md` §"dependency structure".

## Where step 1 left us

* **Ten `axiom`s** in `GQ2/Foundations/Axioms.lean` (labels B1, B2, B3c, B4, B5, B6, B7, B7′,
  B8, B9; B3b deliberately has **no** axiom — the classification is carried at field level by
  B4 + the B3c orientation interface, per T-10/T-11), guarded by `scripts/check_axioms.sh`.
  Reviewer packet: `docs/review-packet.md`.
* **Exactly three `sorry`s** — the intentional gap map:
  1. `GQ2.exists_contSurj_of_card_le` (`Reconstruction.lean`) — the one missing lemma of
     Lemma 2.5; its full proof recipe (cofiltered inverse system of nonempty finite level sets +
     `nonempty_sections_of_finite_inverse_system`) is already documented at the sorry.
  2. `GQ2.main_surjection_count` (`Statement.lean`) — eq. (154): the §§3–10 tower.  **The bulk of
     step 2.**
  3. `GQ2.main_presentation_literal` (`GammaA.lean`) — Theorem 1.2 literal form; wiring theorem
     `main_presentation` is *proved*, so this needs only Prop 2.3 + t.f.g. of `Γ_A` +
     `main_surjection_count`.
* **Already proved and waiting to be consumed** (see `docs/STATUS.md`): Lemma 2.1 + Lemma 2.2
  (`Subdirect.lean`: subdirect products / pushforwards of admissible markings), **Lemma 3.1 in
  full** (`Tame.lean`), Lemma 9.1 and the Lemma 9.2 core (`FiniteGroupLemmas.lean`), the Hopfian
  argument and the whole Lemma 2.5 assembly minus one lemma (`Reconstruction.lean`), `Γ_A` with
  `NA_le_ker` + the profinite⟺finite relator bridges (`GammaA.lean`), and every axiom's
  definition layer (`Demushkin`, `Orientation`, `Kummer`, `MuN`, `TateDuality`, `EulerCharacteristic`,
  `Reciprocity`, `EvensKahn`, `PeripheralAction`, `DyadicPresentation`, `MaxProP`, `Zhat`).

## Done criterion

`lake build GQ2` green with **zero sorries**; `scripts/check_axioms.sh` green with an **empty**
sorry allowlist and census still **10**; and for every theorem, `#print axioms` ⊆ std-3 ∪
{the ten B-axioms} — with each interior node's B-set matching the paper's App. D certificate row
(the *certificate check*, P-01/P-20).

## The DAG (✓ = already proved · Ⓐ = axiom · ☐ = step-2 work)

```
Theorem 1.2 literal  (main_presentation_literal)                                   ☐ P-19
  ├─ main_presentation (wiring)                                                    ✓
  ├─ Lemma 2.5 reconstruction  = assembly ✓ + exists_contSurj_of_card_le           ☐ P-02
  ├─ Γ_A top. fin. gen.                                                            ☐ P-03
  ├─ B1 (G_ℚ₂ t.f.g.)                                                              Ⓐ
  ├─ Prop 2.3  |Sur(Γ_A,G)| = admissibleCount G                                    ☐ P-05
  │    ├─ NA_le_ker + relator bridges (T-21) ✓ · Lemmas 2.1/2.2 ✓
  │    └─ universal marking admissible-in-the-limit (relators ∈ N_A, pro-2 core)   ☐ P-04
  └─ eq. (154)  main_surjection_count                                              ☐ P-18
       ├─ Prop 3.2  common tame quotient  (Γ_A side: Lemma 3.1 ✓; local: B10)      ☐ P-09
       ├─ Prop 1.1  marked Demushkin normalization  (B4 + B3c-interface + §3)      ☐ P-10
       │    └─ Lemmas 3.4–3.8  (eq. (13) ledger: B5, B7′, B2, B8, Kummer)          ☐ P-06..P-08
       ├─ Thm 4.2  boundary-framed exact-image theorem  (statement: P-11)          ☐ P-17
       │    ├─ §5  Fox–Heisenberg complex; 5.7/5.8/5.10/5.11/5.13/5.15             ☐ P-12/P-13
       │    ├─ §§6–7  Evens norm’n 6.13, Shapiro/cor 6.15→6.17, Gauss sign 6.8/6.9,
       │    │        Hilbert ledger 6.16→6.18 (B7′), transgression 6.21  (B6,B9)   ☐ P-14/P-15
       │    ├─ §8  half-torsor count 8.6; closed recursion Prop 8.9 (136)–(142)    ☐ P-16
       │    └─ §9  induction on |L_Y|: 9.1 (Lemma 9.2 ✓) · 9.2 (B6,B7; (145)) ·
       │            9.3 (Frattini/Fourier/central formula (151); B9) · Lemma 9.4   ☐ P-17
       └─ Lemma 10.1  exhaustion by tame boundary frames ⇒ (154)                   ☐ P-18
```

Two independent tracks until the final assembly: **Track A** (P-02..P-05, pure profinite/finite
group theory, no arithmetic axioms) and **Track B** (P-06..P-18, the arithmetic tower).  Track A
is fully parallelizable *now*.

## Conventions (delta from step 1)

1. **No new axioms.**  The census is frozen at 11 (10 at kickoff; **B10**, the tame quotient of `G_ℚ₂`, added by explicit decision after the P-06 escalation).  If a proof seems to need an unstated classical
   input, that is a design escalation (flag on the board, discuss), never an `axiom` commit.
2. **Statement-first for interior nodes.**  Every §4–§10 node lands first as a *sorried* theorem
   with paper eq./§ cross-references and a design note (an F-ticket), then its proof (O-tickets).
   `SORRY_ALLOWLIST` in `scripts/check_axioms.sh` is the **live gap map**: it grows only in
   statement-ticket commits (each entry cites its `P-xx`), shrinks in proof-ticket commits, and is
   empty at step-2 end.  Statement tickets are review gates (packet v3, P-20).
3. **Axiom-dependence discipline.**  Each ticket declares its allowed B-set (from the App. D
   certificate); acceptance includes `#print axioms` of the new theorems ⊆ std-3 ∪ declared set.
   Track-A tickets declare **∅** (std-3 only, except P-19's B1).  P-01 adds a batch ledger so this
   is checked repo-wide, not just per-session.
4. **Model split** as in step 1: **F** = Fable for design/statement tickets, **O** = Opus for
   recipe-documented or well-specified proofs.
5. **Shared-file protocol** (parallel sessions): `GQ2/Foundations/Axioms.lean` is **frozen** (any
   edit is a red flag); `check_axioms.sh` allowlist edits are one-line and ticket-scoped;
   `docs/tickets.md` edits are own-row only; new work goes in new files (one file per paper
   section: `Prop23.lean`, `SectionThree.lean`, `BoundaryFrame.lean`, `FoxHeisenberg.lean`, …).
6. **Scratch / prototype convention** (P-24 guard hardening): throwaway prototypes that
   `import GQ2.*` belong in the **session scratchpad** or a repo-root **`scratch/`** (gitignored),
   *not* under `GQ2/`.  The guard scans `GQ2/**` + `GQ2.lean` but certifies only the **committed**
   library, so a `sorry` / `axiom` / `native_decide` in an *untracked* file **WARN**s (does not
   FAIL) — a mid-flight scratch never blocks another session's commit.  A prototype left under
   `GQ2/` still runs via `lake env lean`, but expect WARN noise until it is moved out or committed;
   a genuine new module simply WARNs until its first commit (expected).  Delete throwaway scratches
   when done — the `WF72.lean` lesson (the guard hardening removes the failure *mode*, not the
   habit).

## Tooling (imported from LeanBridge, P-00)

`.claude/tools/lean4/`: `sorry_analyzer.py` (gap-map reports), `check_axioms.sh` (**per-declaration**
batch axiom checker — distinct from the repo guard `scripts/check_axioms.sh`), `smart_search.sh` /
`search_mathlib.sh` (LeanSearch/Loogle/local), `suggest_tactics.sh`, `find_golfable.py`,
`analyze_let_usage.py`, `count_tokens.py`.  `.claude/docs/lean4/`: working references for
sorry-filling, compiler-guided repair, axiom elimination (step-3 prep), proof golfing, and the
lean-lsp tool API.  The lean-lsp MCP + lean4 skill remain the primary interactive loop; the
scripts give sessions a uniform in-repo fallback.

## Wave schedule

- **Wave 1** (parallel, now): P-01 (O) · P-02 (O) · P-03 (O) · P-04 (**F**) · P-06 (**F**) ·
  P-11 (**F**).
- **Wave 2**: P-05 (**F**) · P-07/P-08 (O) · P-09 (O) · P-10 (O) · P-12/P-14 (**F**) · P-20 at
  statement freeze.
- **Wave 3**: P-13/P-15 (O) · P-16 (**F**→O) · P-17 (**F**→O).
- **Wave 4**: P-18 (O) · P-19 (O).

## Risks

1. **Thm 4.2's statement** (boundary-framed marked targets, exact-image counts) is the
   design-critical object of the whole step — everything in §§5–9 is phrased against it.
   Mitigation: P-11 is Fable-only, statement-first, human-reviewable (P-20) before the proof
   waves; prefer *paper-verbatim* encodings over clever ones (the Γ_A-side count must literally
   match §5's finite complex).
2. **§§6–7 arithmetic** (Gauss sums, transfer forms, hyperbolicity) may want infrastructure beyond
   the EvensKahn/TateDuality def-layers.  Timebox; gaps become design notes on the board, not
   axioms.
3. **Prop 2.3's pro-2-core-in-the-limit** (P-04) is the subtlest Track-A step (an inverse-limit
   argument over admissible quotients).  Fable ticket; `Subdirect.lean`'s Lemma 2.1 is the
   intended engine.
4. **Statement drift vs the paper** — every interior statement carries its eq./§ citation;
   extraction tickets read the PDF directly; packet v3 diffs statements against the paper.
5. **Contention** — the shared-file protocol above; sessions claim tickets by editing their
   own board row (◐ + session note) before starting.

## Steps 3–4 (unchanged horizon)

Step 3 = per-axiom elimination (B7′/B2 first; B5/B6 via the ClassFieldTheory project), step 4 =
delete `Axioms.lean`.  Out of scope here, but P-01's axiom ledger and the certificate check are
built to make step 3 mechanical to plan.
