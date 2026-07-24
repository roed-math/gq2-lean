# Roe-candidate verification: formalization plan

**Goal.** Formalize `paper/roe-presentation-verification.tex` (GPT 5.6, 2026-07-24): the
candidate presentation found by Fable in early June —

```
Γ_R = ⟨ σ, τ, x₀, x₁ | τ^σ = τ²,  r_R = (x₀^σ)⁻¹ · (x₀⁻³τ)^ω₂ · x₁² · [x₁, x₁^σ₂] ⟩
```

(with the normal closure of `x₀, x₁` pro-2, marked-quotient semantics as for `Γ_A`) — satisfies
`Γ_R ≅ G_ℚ₂`. The note is a **replacement theorem**: it re-verifies the four candidate-specific
inputs of the Roe–Turturean paper (tame + marked pro-2 boundary; Fox row; Stokes/duality;
quadratic Gauss signs) and reuses the paper's finite-target induction unchanged.

**End state** (mirrors the `Γ_A` capstones):

```lean
GQ2.Roe.admissibleCountR (G) : ℕ                    -- markings satisfying WildRelR
GQ2.Roe.main_surjection_count :
  ∀ G finite, contSurjCount G = Roe.admissibleCountR G
GQ2.Roe.main_presentation_literal :
  Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)
```

Plan owner: David Roe. Board: `roe-tickets.md` (same directory). Campaign branch `roe`,
worktree `~/claude/gq2-roe`. Prepared 2026-07-24 from a three-agent survey of the tree
(source-interface genericity; word-level Fox machinery; pro-2/Demushkin layer).

---

## 1. Survey verdict — what is reused, what is new

Quantitative headline: **the §§7–10 induction engine contains zero references to the wild
word** (grep-verified across `SectionSeven/`, `SectionNine/`, `SectionTen.lean`, `DeepCount/`,
`DeepPart/`, `RecursionSplice.lean`, `Prop89Close.lean`, `ThmFourTwo.lean`, `HomCounting.lean`,
`AdmissibleCount.lean`). The wild word reaches the induction only through interface numerics,
exactly as the note's Cor 6.19 claims. The wild word appears in just 4 induction-adjacent
files, all interface-supply lemmas: `SectionEight/ScalarCount.lean`, `MStageCountGammaA.lean`,
`SectionTenSources.lean`, `AdmissibleLimit.lean`.

| Layer | Status for Γ_R | Key anchors |
|---|---|---|
| Reconstruction (Lem 2.5) | reuse verbatim | `reconstruction` Reconstruction.lean:367 |
| Schematic endgame | reuse verbatim | `main_presentation` Statement.lean:88 (already abstract in the candidate; only the count function is `admissibleCount` — clone or generalize, trivial) |
| §7 block selection, §8 recursion core, §9 solver, §10 exhaustion | reuse verbatim | `prop_8_9_aux` Recursion.lean:~735; `count_eq_of_closedRecursion` SectionNine/Induction.lean:503 (already two-abstract-sources); `mStage_partition`:467; `lemma_10_1`/`card_contSurj_eq` SectionTen.lean:217,241 |
| ω₂ calculus, Fox/Heisenberg primitives | reuse verbatim | `WordLift.pow_u` Basic.lean:159, `powOmega2_u_of_trivial`:172, `powOmega2_u_of_oddFixedPointFree`:235, `commP_u_of_trivial`:291, `HeisLift.commP_z_of_trivial` Heisenberg.lean:278, `mul_z_of_trivial`:226, `d1Fun_add`:345 (word-generic by functoriality) |
| Stokes (Lem 5.7) | reuse verbatim | `stokesEval`/`lemma_5_7_left/right` Heisenberg.lean:325,445,523 |
| Cone dévissage (Lem 5.11) | reuse verbatim | `selfdualW_two_of_three` Devissage/LESMaster.lean:556 |
| §6 Gauss/determinant apparatus | reuse verbatim (abstract in (q,U)) | `qDouble`/`lemma_6_6` SectionSix.lean:212,222, `lemma_6_8`:268, `prop_6_9_*`:328,381, `prop_6_18_*` DetRamified.lean, `exists_datum_of_invariant_quadratic` KappaNormalForm.lean:804, `equivariant_lift_of_factorSet` Transgression.lean:488; `sigma2_pairing_operator_injective` TameSimple.lean:303 (same `U = σ^ω₂`) |
| Tame group theory + ν template | reuse verbatim | `tame_odd_order` Tame.lean:55, `maxProPMk_tameTau` TameTwoQuotient.lean:63, `Ttame`/`nuT`/`nuTwo`/`presentationLift` BoundaryFrame.lean:101–248 |
| Aut(D₀) machinery ("Prop 3.9") | reuse verbatim (about the shared D₀) | `prop_3_8_classification` AnabelianBridge/Classification.lean:342, `prop_3_8_lift` Construction.lean:1089 (consumes B8), `BDecomposition` SectionThree.lean:422, `prop_1_1` PropOneOneAssembly.lean:298 (assembly template) |
| ℤ₂ˣ arithmetic | reuse verbatim | `zpowZtwo_injective_of_norm` ZtwoPowering.lean:~635, `norm_inv_neg_three_sub_one`:673 (η = (−3)⁻¹ generates 1+4ℤ₂ — already proved), `pow_bijective_of_odd`, mathlib `hensels_lemma` (in-repo precedent: `hensel_sq` SectionThree.lean:829, X²−w only) |
| **Candidate definitions** | clone (small) | `Marking`/`Admissible`/`admissibleCount` Words.lean:66–141; `NA`/`IsAdmissibleU`/`GammaA` GammaA.lean:206–234; `prop_2_3` Prop23.lean:196; `AdmissibleLimit.lean` |
| **Word-level closed forms (§§4–5 of the note)** | **new, small** — the four seams | replaces `WildRow.lean` (423 ln), parts of `HessianRow.lean` (`heisMarking_wildValue_z(_ramified)`:493–535, `lemma_5_13_split/ramified`:647,696), `expMod2_wildValueExp` Traced.lean:97, `mixedB_cocycle` MixedBilinear.lean:350 + `TrivialSelfDual` Gram. New word is simpler: no h₀/d₀/z₀/g₀, bare `x₁²` |
| **§5 duality assembly for Γ_R** | re-instantiate | `prop_5_15` DualityAssembly.lean:574 = `prop_5_15_of_simple` DevissageInduction.lean:158 ∘ `selfDual_of_simple` DualityAssembly.lean:553 — generic scaffolding over `t : Marking C` with `hw : t.WildRel` hypothesis; needs the `WildRelR` variant wired through |
| **Marked pro-2 identification D_R ≅ D₀ (§3 of the note)** | **new — the hard part** | Nothing exists: no Zassenhaus filtration, no abstract canonical orientation, no Labute classification (B3c `dyadicOrientation` Foundations/Axioms.lean:201 axiomatizes the G_ℚ₂(2) package only; `IsDemushkin` Demushkin.lean:109 exists but is not load-bearing). See §3 below |
| **Assembly seam (BoundaryMaps / prop_8_9 / thm_4_2 / eq_154)** | generalize + instantiate | `BoundaryMaps` BoundaryFrame.lean:368 types its A-side to `GammaA` (fields wild-word-free); `prop_8_9_of` RecursionSplice.lean:49 splices `B.bA`/`B.bF`; `thm_4_2` ThmFourTwo.lean:400; `eq_154`/`main_surjection_count'` SectionTenSources.lean:103,119 |

---

## 2. Architecture of the new development

- **Namespace/layout.** All new material in `GQ2/Roe/` under namespace `GQ2.Roe`, importing
  `GQ2.*` freely. The existing Γ_A proof is frozen: its files are touched only by the two
  named refactor tickets (R30, R31), each with a byte-identical-capstone regression gate.
- **Paper-tag ledger.** New files carry `⟦…⟧` anchors to the note's labels (`thm:main`,
  `lem:tame`, `lem:pro2word`, `lem:initial`, `prop:orientation`, `prop:markedpro2`,
  `prop:jacobian`, `lem:normalforms`, `lem:trivial`, `lem:stokes`, `prop:hessian`,
  `prop:duality`, `prop:quadratic`, `cor:gauss`, `prop:interface`), pointing at
  `paper/roe-presentation-verification.tex`.
- **Formalize the interface.** P5 introduces `GQ2.SourceData` — the note's Prop 7.1 /
  paper's Cor 6.19 as a first-class structure (source `Γ`, boundary map
  `b : ContinuousMonoidHom Γ ↥boundarySubgroup`, top. f.g., tame-coordinate
  surjectivity + pro-2 kernel package, `#Hom(Γ,𝔽₂) = 8`, M-stage multiplicity, half-torsor
  input, Gauss-Z residues, enrichment compatibility — exact field list fixed by the R30
  design ticket from `thm_4_2`'s proof-time uses). `thm_4_2`/`prop_8_9` generalize to
  `(S₁ S₂ : SourceData)`; the Γ_A instance re-derives the old capstones byte-identically;
  Γ_R is the second instance. This makes the note's headline claim a Lean object and
  prevents a third clone later.
- **No group-level shortcut.** Γ_R ≅ Γ_A holds only *a posteriori*; no Nielsen/Tietze
  transformation between the two 4-generator presentations is known (note §8). The reuse
  happens at the linearized/cochain level, where the new Fox row is the old matrix with the
  two wild columns interchanged.

---

## 3. The critical path: identifying (D_R, ν_R) ≅ (G_ℚ₂(2), ν_ur)

The note's §3 is the genuinely new mathematics, and the original formalization *bought* the
corresponding fact for G_ℚ₂(2) as axiom B3c. Two viable routes; decision at owner gate G1.

**Route N — explicit Nielsen identification (preferred if the spike lands).**
Search (outside Lean, finite-quotient tooling from `~/claude/q2_galois_presentation/`) for
explicit words giving mutually inverse maps `D_R ⇄ D₀ = ⟨A,S,Y | A²S⁴[S,Y]⟩`, **with
ν-compatibility imposed as a search constraint** (`ν₀(φ s) = 1`, `ν₀(φ x) = ν₀(φ y) = 0`);
then the found iso is already marked and `prop_3_8_*` correction is unnecessary. Lean
verification is pure word algebra in the style of `DyadicNielsen.d0PiEquiv`
(DyadicNielsen.lean:192): relator-membership ledgers + `group` tactic + density for the
inverse. Skips Labute, Zassenhaus, and the orientation computation entirely; **no new
axiom**. Risk: the search may fail or produce unusably long words/ledgers.

**Route L — the note's route, with one new frozen literature axiom.**
1. `D_R` as a pro-2 presentation (clone `DyadicPresentation.lean`); τ dies via
   `maxProPMk_tameTau`; `powOmega2` is the identity on pro-2 elements (`zpowZtwo` laws).
2. **Demushkin-ness of D_R** (note lem:initial): dim H¹ = 3 (Frattini/abelianization:
   B_R = ℤ₂² ⊕ C₂), dim H² = 1 (one-relator central-extension route: clone
   `WordCoh2`/`CardH2GammaA` pattern with an explicit small-group witness), cup–Bockstein
   matrix `[[0,1,0],[1,0,0],[0,0,1]]` nonsingular (shares machinery with the note's
   lem:trivial Gram, ticket R13). Feeds the existing abstract `IsDemushkin` predicate —
   its first load-bearing use. *No Zassenhaus filtration formalized*: we take the
   cochain/cup route the repo already knows, not the note's `D₂/D₃` initial-form phrasing.
3. **Canonical orientation χ_R** (note prop:orientation): define the Labute descent
   characterization (a character χ such that every crossed derivation into ℤ₂(χ) kills the
   relator); realize crossed derivations via a hom `F₃ → ℤ₂(χ) ⋊ ℤ₂ˣ` (the `WordLift A ⋊ C`
   pattern, Basic.lean:76, at the new coefficients ℤ₂(χ) — the one genuinely new calculus);
   extract the character relation + three coefficient equations; exclude branch `Y = X²`;
   solve `X³ + 2X² + 1 = 0` by mathlib `hensels_lemma` (f(1) ≡ 0, f′(1) = 7 odd; lift to
   `X ≡ 5 mod 16`, `S ≡ 13 mod 16`); conclude `v₂(X−1) = v₂(S−1) = 2` and
   `im χ_R = {±1} × (1+4ℤ₂)` via `zpowZtwo_injective_of_norm`.
4. **New axiom B-Lab** (owner sign-off required, exception to the frozen census):
   Labute 1967, Théorème 8 + 4, the single instance
   `IsDemushkin 2 G → rank 3 → q = 2 → im χ_G = {±1}×(1+4ℤ₂) → Nonempty (G ≃ₜ* D₀)`,
   stated against the descent-characterized orientation, with the full convention docstring
   per `docs/orchestration/formalization-plan.md` ground rules. Quarantined in
   `Foundations/Axioms.lean`, ledgered, gated by `check_axioms.sh`.
5. **Marked matching** (note prop:markedpro2): unique `b` with `S = X^b`
   (`zpowZtwo_bijective`), basis change `k = s̄ − b·x̄` (clone `BDecomposition`),
   ν/χ-preserving iso on abelianizations, correct the abstract iso via
   `prop_3_8_classification` + `prop_3_8_lift` — direct reuse, they live on the D₀ side.

Route L formalizes the note faithfully (its §3.2 is the "main new calculation") at the cost
of one new axiom and ~1.5–3k extra lines vs Route N. **Recommendation: run the R2 spike
first (cheap, high upside); default to Route L if it fails. Both routes are fully planned
below so the gate is a selection, not a replan.**

Fat-tail risk, stated honestly: if the spike fails **and** the owner declines B-Lab, the
fallback is formalizing Labute's classification abstractly — a multi-week project on its
own. Everything else in this plan is insulated from that decision.

---

## 4. Phases and tickets

Ticket sizing follows the b9a campaign (one ticket = one dispatch = one disjoint file set).
`model`: fable = design/hard seams, opus = well-specified construction/proof. Full row
detail on the board; dependency edges there.

**P0 — candidate definitions & epi-semantics** (~600–900 ln, low risk)
- R1 (fable): `GQ2/Roe/Words.lean` — `aR = powOmega2 (x₀⁻³ * τ)`, `cR = commP x₁ (x₁ ^c σ₂)`,
  `wildValueR`, `WildRelR`, `AdmissibleR`, `admissibleCountR`; `wildValueExpR` + the
  `_of_dvd` finite-exponent-independence lemma (pattern: Traced.lean:75,122,133); stress
  tests incl. mod-2 exponent sanity. Skeleton + fills in one ticket (small).
- R3 (opus): `GQ2/Roe/GammaR.lean` — `IsAdmissibleUR`/`NR`/`GammaR`/`NR_le_ker` (clone
  GammaA.lean:206–234); `GQ2/Roe/AdmissibleLimit.lean` clone.
- R4 (opus): `GQ2/Roe/Prop23.lean` — `prop_2_3_R : Nat.card (ContSurj GammaR G) = admissibleCountR G`.
- R5 (opus): numerical cross-check à la `Sanity.lean`/App-B: evaluate `admissibleCountR` on
  small groups (C₂, C₄, D₄, Q₈, …) by `decide`/`Decidable` instances and compare against the
  June LMFDB-verified finite-quotient counts (archive `~/claude/q2_galois_presentation/`).
  Early end-to-end guard against transcription errors in the relator. **Do this before any
  deep proof work consumes the definitions.**

**P1 — tame quotient & unramified character** (~200–400 ln, low risk)
- R6 (opus): `GQ2/Roe/Tame.lean` — note lem:tame: `τ^ω₂ = 1` in every finite quotient
  (`tame_odd_order` + `powOmega2`), wild relator redundant mod ⟨⟨x₀,x₁⟩⟩, tame quotient =
  `Ttame`, `νR` via `presentationLift` template, `W_R = O₂` (`tame_normal_two_subgroup_central`).

**P2 — marked pro-2 identification** (route-dependent; the critical path)
- R2 (fable, off-Lean spike, timeboxed): Nielsen search for ν-constrained `D_R ⇄ D₀` word
  pairs; deliverable = words + finite-level verification + ledger-size estimate, or a
  documented negative. Runs in parallel with P0/P1.
- **G1 (owner gate): route selection; if Route L, sign off the B-Lab axiom statement.**
- Route N: R7n (fable) `GQ2/Roe/DRPresentation.lean` + `GQ2/Roe/NielsenIso.lean` skeleton
  (maps, relator ledgers as `sorry`); R8n/R9n (opus ×2) ledger fills (forward/backward);
  R10n (opus) marked matching = direct ν check + `maxProP` universal property;
  R11n (fable) `(D_R, ν_R) ≅ (G_ℚ₂(2), ν_ur)` assembly via `prop_3_10_local_marked` bridge.
- Route L: R7 (fable) `GQ2/Roe/DRPresentation.lean` + design memo fixing statements;
  R8 (opus) B_R abelianization bookkeeping (`BDecomposition` clone, t = ȳ−2x̄);
  R9 (fable) `GQ2/Roe/CrossedDerivation.lean` — χ-twisted ℤ₂(χ)⋊ℤ₂ˣ calculus + the four
  equations (note eq:charrelation/Cx/Cs/Cy); R10 (opus) branch exclusion + cubic Hensel +
  mod-16 congruences (`GQ2/Roe/OrientationRoot.lean`); R11 (opus) `im χ_R` via
  `zpowZtwo_injective_of_norm`; R12 (fable) Demushkin-ness: dim H¹ = 3;
  R13 (opus) dim H² = 1 + cup Gram (shared with R21); R14 (fable) B-Lab axiom insertion +
  ledger + gates (mirrors the b9a T5 flip checklist); R15 (fable) marked matching assembly
  (`prop_1_1` clone: S = X^b, k-shear, `prop_3_8_classification`/`_lift`).

**P3 — word-level closed forms & §5 duality for r_R** (~1.2–2 k ln, low-moderate risk)
- R20 (opus, read-only recon): map the exact parameter boundary of the §5 scaffolding —
  which of `Traced`/`MixedBilinear`/`MixedBObs`/`DualityAssembly`/`Devissage*` take the word
  as data vs bake `wildValue`; deliverable = seam list consumed by R21–R26 prompts.
  (Survey says: dévissage + assembly generic over `t, hw`; verify and pin cite lines.)
- R21 (fable): `GQ2/Roe/WildRow.lean` skeleton + the split/ramified evaluated rows —
  note prop:jacobian: `L_w = P·b + (P + S⁻¹)·c` (from `WordLift.pow_u`,
  `powOmega2_u_of_*`, `commP_u_of_trivial`, `conjP_u_of_*`; expect ≪ the paper's 423 ln —
  no h₀). Includes trivial-module differential `(b,b)` corollary (note lem:trivial).
- R22 (opus): normal forms `lemma_5_13_split/ramified` analogues (`(0,0,0,d)` unique reps).
- R23 (opus): Stokes endpoint — `expMod2` of `wildValueExpR` = `(0,1,0,0)` (note lem:stokes;
  ~20 ln, pattern Traced.lean:97) + chain-map rows `mixedB_tameRow/_wildRow` analogues.
- R24 (opus): mixed Hessian — `heisMarking` central coordinate for r_R: `x₁²` diagonal via
  `HeisLift.mul_z_of_trivial`, commutator term verbatim via `commP_z_of_trivial`; pairing
  operator `1 + U + U⁻¹` invertibility is `sigma2_pairing_operator_injective` as-is
  (note prop:hessian).
- R25 (opus): trivial-module Gram `a·c′ + c·a′ + d·d′` nonsingular + `mixedB_cocycle`
  analogue (note lem:trivial; cleaner than the paper's — diagonal (3,3) entry).
- R26 (fable): `prop_5_15_R`/`prop_5_16_R` assembly through `selfDual_of_simple` +
  `prop_5_15_of_simple` + generic dévissage (note prop:duality).

**P4 — quadratic obstruction & Gauss signs for r_R** (~0.5–1 k ln, low risk)
- R27 (opus): base word expansion `Q_R⁰(d) = q(d) + b_q(d, U⁻¹d)` (note prop:quadratic) =
  the R24 Hessian feeding the abstract `qDouble` seam; zero counts/Gauss signs by
  instantiating `lemma_6_6`/`lemma_6_8`/`prop_6_9_*`/`prop_6_18_*` (note cor:gauss);
  transgression/shear carry-over is formal (`κ = κ⁰ + Γ_γ + inf δ`, abstract in the class).

**P5 — source interface & assembly** (~1.5–2.5 k ln, moderate risk, serialized where it
touches existing files)
- R30 (fable): design + refactor: extract `GQ2.SourceData` from `BoundaryMaps`' A-side and
  `thm_4_2`/`prop_8_9`'s proof-time uses; generalize `thm_4_2` → `thm_4_2_of_sources`,
  `prop_8_9` → over `SourceData`; re-derive the Γ_A capstones **byte-identically**.
  Sole owner of the touched existing files; regression gate: full build green +
  `check_axioms.sh` + old capstone statements unchanged (`git diff` on their `#print`).
- R31 (opus): Γ_R supply lemmas, one file each where possible: `lemma_8_2_R`
  (#Hom(Γ_R,𝔽₂) = 8 — from the marked pro-2 boundary), `liftsOver_card_R` (M-stage
  multiplicity; MStageCountGammaA.lean:485 docstring says source-generic once a base lift
  exists — thin wrapper over `prop_5_15_R` + `markC_admissible_R`), `lemma_8_6_R`
  (half-torsor), Gauss-Z package (`GaussZ/FinalGammaR` clone of `FinalGammaA`), plus
  `RStage`/`Phase140` Γ_R analogues if R30's field list demands them (recon note in R30
  fixes the exact list — several may collapse into `SourceData` fields discharged by P3/P4).
- R32 (fable): `SectionTenSources` analogue: tame-coordinate surjectivity, `ker φ_R = W_R`,
  pro-2 kernel (from P1/P2); `SourceData` instance `sourceR`; `eq_154_R`;
  `main_surjection_count_R`; `main_presentation_literal_roe` (via the `main_presentation`
  schematic + `prop_2_3_R` + f.g. of Γ_R).

**P6 — gates, docs, site** (2–3 tickets, low risk)
- R40 (opus): `check_axioms.sh` extension (new terminal theorem in the expected-axiom
  audit), `AxiomLedger` entries, `formalization.yaml` second `main_results` entry,
  `comparator-config.json`/`Challenge.lean` pair for Γ_R, README.
- R41 (opus): docs sweep (this plan's status, `docs/README.md` index, literature-axioms
  entry if Route L), blueprint/verso chunk for the note on the gq2 site (separate repo;
  coordinate, do not block).
- G2 (owner gate): final axiom-census sign-off (census unchanged on Route N; +B-Lab on
  Route L), review packet addendum.

---

## 5. Difficulty estimate

| Phase | New lines | Tickets | Risk |
|---|---|---|---|
| P0 definitions + semantics | 600–900 | 4 | low |
| P1 tame | 200–400 | 1 | low |
| P2 pro-2 identification | 800–1,500 (N) / 2,500–4,500 (L) | 5 (N) / 9 (L) | **moderate-high** |
| P3 word level + §5 duality | 1,200–2,000 | 7 | low-moderate |
| P4 quadratic/Gauss | 500–1,000 | 1 | low |
| P5 interface + assembly | 1,500–2,500 | 3 (large) | moderate |
| P6 gates/docs | 200–400 | 2 | low |
| **Total** | **≈ 5–8 k (N) / 7–12 k (L)** | **≈ 23–27 dispatches** | |

Calibration: the original tower is ~91 k lines built in ~8 swarm-days to sorry-free (plus
6 days polish); the post-completion axiom campaigns (B7′, B11b, B12, B13, B9a) each ran
6–10 tickets in 1–3 days at comparable per-ticket size. This campaign is **roughly 10 % of
the original by volume, ~25–35 % by difficulty-weighted effort** (three novel seams: the
χ-twisted derivation calculus, the D_R identification, the SourceData refactor).

**Wall-clock estimate: 4–7 swarm-days (Route N landing) / 6–9 (Route L), i.e. one to two
calendar weeks** including the two owner gates, at b9a cadence with 2–3 parallel lanes.
Fat tail: if the Nielsen spike fails *and* B-Lab is declined, add 3–6 weeks to formalize
Labute's classification — the only unbounded item, and it is quarantined behind gate G1.

Confidence: high on P0/P1/P3/P4 (compositional APIs verified present; the new word is
strictly simpler at every word-level seam), moderate on P2/P5 (novel content + the one
refactor of frozen code).

---

## 6. Orchestration protocol (lessons-learned, binding)

1. **Single-writer board.** Workers never edit `roe-tickets.md`. A worker's deliverable is
   its files + commit + a final report (files, commit hash, sorry/axiom state, deviations,
   anything discovered that changes later tickets). The orchestrator alone updates rows.
2. **Disjoint file ownership.** Every ticket lists files owned; new files preferred; no two
   same-wave tickets share a file. Existing-file edits are dedicated serialized tickets
   (R30 pattern) with regression gates.
3. **One campaign worktree, commit-on-green.** Branch `roe`, worktree `~/claude/gq2-roe`.
   Parallel workers share the worktree on disjoint files and commit *immediately* after
   their files build green (`roe Rn: <summary>`): uncommitted tracked-file edits are lost
   to swarm resets; untracked files survive. Merge `roe` → `master` at wave boundaries
   after gates. If concurrent `lake` builds contend, stagger with per-file `lake build
   GQ2.Roe.<Mod>` targets.
4. **Orchestrator stays light.** No `lean_*` tools, no bulk file reads in the main session.
   Dispatch batched Agent calls whose prompts carry: worktree path, branch, build command,
   files owned, exact target statements (with the paper-tag anchors), reusable-declaration
   cites from §1, gates, report format. One-line scoreboard between waves.
5. **Model routing.** fable: R1, R2, R7/R7n, R9, R12, R14, R15, R11n, R21, R26, R30, R32.
   opus: the rest. Route escalations through the orchestrator, not sideways.
6. **Skeleton-first.** Each phase's lead ticket produces a compiling `sorry`-skeleton +
   design memo (`roe-<ticket>-design.md` here) before fills are dispatched.
7. **Recon-first.** R20-style read-only recon tickets run against the main checkout and
   produce citation-dense reports; they are cheap and de-risk every fill prompt.
8. **Gates per wave.** `lake build` green; `scripts/check_axioms.sh`; zero sorries at wave
   close; axiom certificate via the `AxiomLedger` pattern; Γ_A capstones untouched.
   No new `axiom` outside gate G1's B-Lab decision; axiom quarantine in
   `Foundations/Axioms.lean` stands.
9. **Stress-test discipline.** Every new definition ships 2–3 provable sanity lemmas in the
   same commit; R5's numerical cross-check runs before deep proofs consume the definitions.
10. **Convention checklist.** `x ^c g = g⁻¹xg`; `commP x y = x⁻¹y⁻¹xy`; `ω₂` via
    `omega2Exp`/`powOmega2` at finite level and `zpowZtwo` profinitely (`−3 ≡ 1 mod 2`
    matters in R21); orientation and character conventions per B3c's docstring; every new
    axiom/statement docstring states its conventions and cites the note's equation.

## 7. Definition of done

`GQ2.Roe.main_presentation_literal` sorry-free; `#print axioms` = std-3 ∪ current census
(∪ {B-Lab} iff Route L, owner-approved); `check_axioms.sh` green with the new terminal
theorem; Γ_A capstones and their axiom certificates byte-identical to pre-campaign;
comparator pair passing; `formalization.yaml`, ledger, README, and this plan's status
updated; board archived per `docs/orchestration/README.md` conventions.
