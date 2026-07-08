# Status ledger

Current-tree record of the GQ2 library, organized by **layer** (per-declaration axiom data lives in
the machine ledger — see below — so this file stays maintainable as the tree grows).  Refreshed
**2026-07-03** at the step-1→step-2 boundary (all statement tickets `T-xx` landed; proof tickets
`P-xx` beginning).  See [`step2-plan.md`](step2-plan.md) for the proof-phase DAG,
[`tickets.md`](tickets.md) for the live board, and [`literature-axioms.md`](literature-axioms.md) for
the App. D certificate.

## Snapshot (machine-checked)

* **Build:** `lake build GQ2` green.  Pinned Mathlib `ec410d2` + ClassFieldTheory `3565c752`,
  toolchain `leanprover/lean4:v4.31.0-rc2` (see `lakefile.toml` / `lean-toolchain`).
* **Axiom census: 10** (frozen), all in `GQ2/Foundations/Axioms.lean` — the ten classical
  literature leaves B1–B9 (+B3c).  Guarded by `scripts/check_axioms.sh` (placement, census, no
  `native_decide`, sorry-allowlist).
* **Open `sorry`s: 3** (the intentional step-2 gap map) — `exists_contSurj_of_card_le`,
  `main_surjection_count`, `main_presentation_literal`.
* **Axiom ledger** (`GQ2/AxiomLedger.lean`, ticket P-01): **613** tracked declarations, **601** at
  the standard three axioms only, **0** stray/unknown non-standard axioms.  The only current B-axiom
  consumers are B7's six Euler-characteristic stress tests; every other B-leaf has **0** consumers so
  far (the arithmetic tower that will consume B1–B6/B7′/B8/B9 is still sorried — P-06…P-18).

### Verify from scratch

    lake build GQ2                     # green (only the 3 sorries warn)
    bash scripts/check_axioms.sh       # placement / census(=10) / no native_decide / sorry-allowlist
    lake env lean GQ2/AxiomLedger.lean # per-declaration axiom certificate (diff vs App. D §C)

Per-declaration deep checks use the lean-lsp `lean_verify` tool or `#print axioms <name>`.

## The axiom layer — 10 leaves (`GQ2/Foundations/Axioms.lean`)

| B | axiom | def-layer for its statement | paper node it feeds |
|---|---|---|---|
| B1 | `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` | (bare Mathlib) | `main_presentation` t.f.g. hyp |
| B2 | `Foundations.cyclotomicCharacter_two_surjective` | (Mathlib `cyclotomicCharacter`) | Lemma 3.6 (peripheral lift) |
| B3c | `dyadicOrientation` | `Orientation.lean` (T-11) | Prop 1.1 orientation row |
| B4 | `Foundations.absGalQ2_maxProTwo_presentation` | `DyadicPresentation.lean` (T-08) + `MaxProP.lean` (T-05) | Prop 1.1 |
| B5 | `localReciprocity` | `Reciprocity.lean` (T-17) | Lemma 3.5, Prop 3.2 |
| B6 | `tateDuality` | `TateDuality.lean` (T-14) | §5.15, §9.2 |
| B7 | `Foundations.absGalQ2_localEulerCharacteristic` | `Cohomology.lean` (T-02) | §9.2 |
| B7′ | `HilbertSymbol.hilbertSymbol_dyadic` | `HilbertSymbol.lean` (T-07) | Lemma 3.5, §6 |
| B8 | `peripheralCyclotomicAction` | `PeripheralAction.lean` (T-12) | Lemma 3.6 |
| B9 | `evensKahn_dyadic` | `EvensKahn.lean` (T-18) | §6 |

B3's remaining pieces are deliberately **not** axioms: `IsDemushkin` + invariants (`Demushkin.lean`,
T-09) are proved-when-instantiable; the rank-3 `q=2` classification (B3b) is carried at field level by
B4 + the B3c interface (no separate axiom).  `Foundations.lean` is now a one-line pointer to
`Foundations/Axioms.lean` (post-T-19).

## The three open `sorry`s (step-2 gap map)

| declaration | file:line | closes with |
|---|---|---|
| `GQ2.exists_contSurj_of_card_le` | `Reconstruction.lean:167` | **P-02** (König on the cofiltered system; recipe at the sorry) |
| `GQ2.main_surjection_count` | `Statement.lean:49` | **P-18** (eq. (154): the whole §§3–10 tower, P-06…P-17) |
| `GQ2.main_presentation_literal` | `GammaA.lean:285` | **P-19** (`main_presentation` at `Γ_A` + P-03/P-05 + P-18) |

Transitively sorry-tainted (via `exists_contSurj_of_card_le`): `reconstruction`,
`reconstruction_of_equinum`, `main_presentation` — all clear once P-02 lands.  (Ledger gap-map: 6.)

## Definition layers (statement tickets T-05…T-18)

Each provides the Lean vocabulary its axiom's *type* is written in; the axiom itself is in
`Axioms.lean`.  All are `lake build`-green and — except the B7 Euler stress tests, which apply their
axiom directly — bundle-parametrized and therefore **axiom-free** (std-3).

| file (ticket) | provides | hosts |
|---|---|---|
| `MaxProP.lean` (T-05) | `maxProPQuotient p G` + pro-`p`-ness + universal property + idempotence | — |
| `HilbertSymbol.lean` (T-07) | `hilbertSymbol`, `ε`, `ω`, `ℤ₂ˣ` square classes; symmetry/`(a,−a)=1` | B7′ |
| `DyadicPresentation.lean` (T-08) | `D₀ = ⟨A,S,Y ∣ A²S⁴[S,Y]⟩` as a profinite presentation | B4 |
| `Demushkin.lean` (T-09) | `IsDemushkin` (fin. gen. pro-`p`, `dim H¹=n`, `dim H²=1`, cup nondegenerate) + rank | — (B3a) |
| `Orientation.lean` (T-11) | `DyadicOrientation` bundle (B4 iso + descended cyclotomic char, Labute values) | B3c |
| `PeripheralAction.lean` (T-12) | `PeripheralCyclotomicAction` on `Δ = maxPro2(F₂)` peripherals (Lemma 3.6) | B8 |
| `Kummer.lean` (T-13) | `kummerClass : kˣ → H¹(k,𝔽₂)` cocycle; `[ab]=[a]+[b]`, `[a]=0 ⇔ square` | — (I5) |
| `TateDuality.lean` (T-14) | Tate-dual module + `TateDuality n` perfect-pairing bundle | B6 |
| `MuN.lean` (T-15) | `μₙ` as a finite discrete `G_ℚ₂`-module (Galois action + continuity) | — (I10) |
| `EulerCharacteristic.lean` (T-16) | local Euler char: `#H¹ = #H⁰·#H²·2^{v₂#M}` + finiteness | B7 |
| `Reciprocity.lean` (T-17) | `LocalReciprocity` bundle (`rec`, `ν_ur`; norm-kernels, eq. (13) rows) | B5 |
| `EvensKahn.lean` (T-18) | corestriction, index-2 Evens norm, eq. (111) ingredients (deg ≤ 2) | B9 |

## Proved infrastructure (no `sorry`, std-3)

**Track A — profinite / finite group theory** (feeds P-02…P-05, the non-arithmetic assembly):
* `Reconstruction.lean` — Lemma 2.5: `profinite_hopfian`, `finite_continuousMonoidHom`,
  `reconstruction`/`reconstruction_of_equinum` (modulo the one P-02 sorry),
  `continuousMulEquivOfBijective`.
* `Subdirect.lean` — Lemmas 2.1/2.2: `map_admissible`, `prod_tameRel`/`prod_wildRel` (admissibility
  is cofinal under quotients and closed under subdirect products).
* `Tame.lean` — **Lemma 3.1 in full** (`tame_odd_order`, `zpowers_normal_of_tame`, `tame_semidirect`,
  `tame_zpowers_disjoint`, `tame_normal_two_subgroup_central`); Lemma 3.3.
* `FiniteGroupLemmas.lean` — Lemma 9.1 (`coprime_fiber_product`, via Goursat) + Lemma 9.2 core
  (`oddOrder_twoQuotient_split`, Schur–Zassenhaus).

**Continuous cohomology ≤ 2** (coefficient system for B3/B6/B7/B9):
* `DiscreteModule.lean` (T-01) — discrete `G`-module conventions; open stabilizers/kernels.
* `Cohomology.lean` (T-02/T-03) — `H⁰/H¹/H²` by inhomogeneous cochains; functoriality
  (`Hicomap`, `res`, `inf`, `mapCoeff`); trivial-action characterization.
* `CupProduct.lean` (T-04) — `cup11`/`cup02`/`cup20` relative to a `G`-pairing; the B3-critical
  `H¹×H¹→H²`.
* `CtsCohBridge.lean` — degree-0 bridge to Mathlib's `continuousCohomology`.

**Profinite foundations** (`Γ_A` machinery, absent from Mathlib):
* `FreeProfinite.lean` — `FreeProfiniteGroup` + universal property; `ProfiniteQuotient.lean` —
  `profiniteQuotient`/`quotientMk`/`quotientLift`; `ProfinitePresentation.lean` —
  `profinitePresentation`.
* `Zhat.lean` (T-06) — `ℤ̂`, `ω₂ : ℤ̂`, `ẑ`-exponentiation `x ^ᶻ γ` with naturality + finite-quotient
  evaluation; `Omega2.lean`/`AppendixB.lean`/`Words.lean` — the `ω₂` calculus + App. A/B
  cross-checks (incl. the exact `omega2Exp 85667662080 = 40491355905`).

**Paper §2 / Theorem 1.2 wiring:**
* `GammaA.lean` (T-21) — the eq.-(7) marked quotient `Γ_A`, `NA_le_ker`, profinite⟺finite relator
  bridges; `Statement.lean` — `main_presentation` (wiring, proved) + `main_surjection_count`
  (sorried) + `admissibleCount`.

## Not part of the deliverable

`Sanity.lean`, `CFTTest.lean` (import smoke-tests), `ReconScratch.lean` (P-02 scratch),
`AxiomLedger.lean` (the P-01 tool — not imported by `GQ2.lean`, so not built by `lake build GQ2`).
