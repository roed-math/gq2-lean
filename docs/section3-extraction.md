# §3 statement extraction — design note (ticket P-06)

Companion to [`GQ2/SectionThree.lean`](../GQ2/SectionThree.lean): maps every §3 interior node
(paper: Prop. 1.1, Prop. 3.2, Lemmas 3.4–3.8, displays (8)–(18)) to its Lean encoding, and
records the absorption, deviation, and escalation decisions.  Proof tickets: P-07 (3.5),
P-08 (3.7/3.8), P-09 (3.2), P-10 (1.1).

## Statement inventory

| Paper node | Lean name (`GQ2.SectionThree.*`) | Status | Proof ticket / Ax |
|---|---|---|---|
| §3 opening display (`T_tame`) | `Ttame`, `tameSigma`, `tameTau`, `tame_relation` | **proved** (def-layer) | — |
| Lemma 3.1 | `GQ2.Tame` (step 1) | **proved** | — |
| Prop. 3.2, `Γ_A` side | `prop_3_2_gammaA` | sorried | P-09 (Lemma 3.1 + T-21 bridges) |
| Prop. 3.2, local side (+ Lemma 3.3 char.) | `LocalTameQuotient`, `prop_3_2_local` | sorried | P-09 — **escalation, see below** |
| Lemma 3.3 (`O₂ = W`) | folded into `LocalTameQuotient.maximal` / design note §3.3 | — | — |
| Lemma 3.4 | **absorbed** (see below) | — | — |
| eq. (9)/(11) (`B = C₂t ⊕ ℤ₂S̄ ⊕ ℤ₂Ȳ`) | `BDecomposition`, `b_decomposition` | sorried | P-07 (std-3 presented-group algebra) |
| Lemma 3.5, `(ν_ur, χ_D)` rows of (13) | `GQ2.Reciprocity` stress tests (step 1) | **proved** | — |
| Lemma 3.5, `ā²s̄⁴ = 1` | `GQ2.abelianized_relator` (step 1) | **proved** | — |
| Lemma 3.5, marked abelianization | `lemma_3_5_marked_abelianization` | sorried | P-07 (B5) |
| Lemma 3.5, cup/initial-form clause | `lemma_3_5_hilbert_ledger` | sorried | P-07 (B7′) |
| Lemma 3.5, `(ν_ur, χ_D)` injective | `lemma_3_5_injective` | sorried | P-07 (via `b_decomposition`) |
| Lemma 3.6 | **absorbed** (= axiom B8) | — | P-08 notes below |
| Lemma 3.7 (eq. (15)) | `lemma_3_7` | sorried | P-08 (B2, B8) |
| Prop. 3.8, lifting half (eq. (17)/(18)) | `prop_3_8_lift` | sorried | P-08 |
| Prop. 3.8, classification half (eq. (18)) | `prop_3_8_classification` | sorried | P-08 |
| Prop. 1.1 (eq. (4)) | `prop_1_1` | sorried | P-10 (B3c, B4, B5, B7′) |

`SORRY_ALLOWLIST` entry: `GQ2/SectionThree.lean` (this ticket; removed as P-07/P-08/P-09/P-10
close the ten sorries).

## Absorptions (paper nodes that are already axioms or theorems)

* **Lemma 3.4** ("`D₀` is the standard rank-3, `q = 2` Demushkin group; `G_{ℚ₂}(2)` is
  abstractly isomorphic to `D₀`; the canonical orientation takes the values
  `(−1, 1, (−3)⁻¹)`").  Its paper proof is *pure citation* (Labute [2], Théorèmes 4 and 8).
  In the axiom design of step 1 the three clauses are carried by:
  - abstract isomorphism → **axiom B4** (`absGalQ2_maxProTwo_presentation`), a *continuous*
    isomorphism, which is stronger and is what downstream consumes;
  - orientation values → **axiom B3c** (`dyadicOrientation`, route (ii): the interface with
    the descended cyclotomic character and the Theorem 4(2) values);
  - "is *the* standard rank-3 `q = 2` Demushkin group" → deliberately-unformalized Labute
    content, per the standing **B3b no-axiom decision** (T-10/T-11; `GQ2/Demushkin.lean`
    §QInvariant docstring: "`demushkinQ D₀ = 2` itself is Labute-content and is not
    attempted").  Introducing sorried statements for it would create gaps that are provable
    from *no* census axiom — contradicting the freeze rules.
* **Lemma 3.6** is **axiom B8** verbatim: the T-12 bundle `PeripheralCyclotomicAction` was
  designed as exactly Lemma 3.6's group-theoretic conclusion (with the flagged `π₁`
  deviation).  P-08's "proof of 3.6" is the axiom itself; its real work is 3.7/3.8.
* **Lemma 3.5's rows of eq. (13)** and the abelianized relation are proved, bundle-
  parametrized, in `GQ2/Reciprocity.lean`: `nu_ur_recip_uniformizer` (`ν(rec 2) = −1`),
  `nu_ur_recip_neg4` (`ā ↦ −2`), `nu_ur_recip_neg3` (`ȳ ↦ 0`), `chiCyc_recip_neg4`
  (`ā ↦ −1`), `chiCyc_recip_neg3` (`ȳ ↦ (−3)⁻¹`), `abelianized_relator` (`ā²s̄⁴ = 1`).

## Encoding decisions and deviations

* **`T_tame`** is the profinite presentation `profinitePresentation {tameRelator2}` on
  `σ = of 0`, `τ = of 1` — the paper's `⟨σ, τ | τ^σ = τ²⟩_prof` verbatim.  *Coordination:*
  P-11's in-flight `GQ2/BoundaryFrame.lean` defines its own `GQ2.Ttame` with the same
  relator word (both wave-1 tickets are dependency-free by design, so neither could import
  the other).  The two constants are definitionally equal; **P-09 (or the P-12 review pass)
  deduplicates** — a one-line refactor.  Same remark for `wildPart` (`W_A`) versus whatever
  P-04's `AdmissibleLimit.lean` lands for the pro-2 core: `SectionThree` is fully namespaced
  (`GQ2.SectionThree.*`), so there is no name-collision risk meanwhile.
* **`W_F` (local wild inertia) is encoded intrinsically** as the maximal closed normal pro-2
  subgroup (the fields of `LocalTameQuotient`): Mathlib has no ramification theory, and paper
  **Lemma 3.3** proves `O₂(G_{ℚ₂}) = W_F`, so the 2-core characterization *is* the faithful
  intrinsic rendering; the `maximal` field pins `W` uniquely, realizing the "canonical" of
  Prop. 3.2 on the local side.  (Lemma 3.3's `Γ_A`-half, `O₂(Γ_A) = W_A`, is not separately
  stated — outside the ticket's node list; its finite engine is proved in `GQ2/Tame.lean`
  and P-09/P-18 can state it if consumed.)  Lean detail: `normal` is an instance-binder
  field so that the `equiv` field's quotient `AbsGalQ2 ⧸ W` elaborates.
* **"Canonical" in Prop. 3.2**: `Γ_A` side pinned on generators (`σ ↦ σ`, `τ ↦ τ`; unique
  because the marked generators topologically generate); local side pinned by uniqueness of
  `W` only — the residual choice of isomorphism is invisible to the downstream *counts*
  (Lemma 10.1 sums over all frames; a different choice permutes frames bijectively).  If
  P-11's boundary design needs a ν-compatibility pinning (`ν_t ∘ e = ν_ur`-descent), add it
  as a strengthening field then — do not weaken this statement.
* **eq. (11) as a bundle** (`BDecomposition`): a continuous isomorphism
  `B = D₀^{ab} ≅ ℤ/2 × ℤ₂ × ℤ₂` pinning the basis `(t, S̄, Ȳ)`, `t = Ā + 2S̄`.  Statements
  3.7/3.8 are parametrized over the bundle (house style, cf. the B5 stress tests).
  Dictionary: `Ā = t − 2S̄ ↦ (1, −2, 0)`; the scalar `u ∈ ℤ₂ˣ` acts coordinatewise, and on
  the `ℤ/2`-coordinate an odd scalar acts trivially — so paper (15) `Ā ↦ uĀ, S̄ ↦ uS̄`
  reads `(1,−2,0) ↦ (1,−2u,0)`, `(0,1,0) ↦ (0,u,0)`, and paper (18) `α_{u,b}` reads as in
  `prop_3_8_lift`.  A continuous group isomorphism of pro-2 abelian groups is automatically
  `ℤ₂`-linear (`x ↦ x^{u}` is a limit of integer powers), so the coordinate transcription is
  exactly the paper's `ℤ₂`-module statement; making that transcription rigorous is part of
  P-08's proof obligation, not extra statement content.
* **Lemma 3.5's "initial form" clause is stated in Hilbert-symbol vocabulary**
  (`lemma_3_5_hilbert_ledger`): the six values of `( · , · )₂` on the square-class basis
  `(−1, 2, −3)` — nontrivial exactly at `(−1,−1)` and `(2,−3)`.  Under the dual-basis
  dictionary `α ↔ [−1], β ↔ [2], γ ↔ [−3]` this *is* the quadratic initial form
  `α² + βγ + γβ` (= the degree-2 initial form of `r₀ = A²S⁴[S,Y]`, paper display after
  (13)).  The paper's bridge "under Kummer theory, cup product is the Hilbert symbol" is
  *not* needed to state or use §3 (Prop. 1.1's proof consumes only the rows and the
  injectivity); the cup-level reading first appears in §6, where axiom **B9** natively
  speaks `trivialCupPairing` on `kummerClass`es.  **Foreseen for P-14**: if §6 needs the
  general cup↔symbol identification (beyond what B9 supplies at its diagonalizations), that
  is a design escalation to raise *there*, not a §3 gap.
* **Zassenhaus/graded "initial form" machinery is not encoded** — the paper's phrase
  "a Demushkin relator for lifts of these classes has the same quadratic initial form as
  `r₀`" is the *interpretation* of the six-value ledger; no graded-Lie layer exists in the
  repo, and nothing downstream consumes one at statement level.
* **Prop. 1.1** is packaged as `∃ e : G_{ℚ₂}(2) ≅ D₀` with the `ν_ur`-row read through
  arbitrary lifts to `G_{ℚ₂}` (T-11 house style — cf. `chiCyc_eq_neg_one_of_lift_A`), and
  parametrized over `R : LocalReciprocity` (`ν_ur` is unique given the bundle clauses, by
  density).  `a = e⁻¹(A), s = e⁻¹(S), y = e⁻¹(Y)` then topologically generate and satisfy
  `a²s⁴[s,y] = 1` by transport of `d0_relation` — implied by the iso form, not separately
  stated.  The marked-abelianization clause of Lemma 3.5 quantifies over lifts the same way
  (`rec`-classes live in `G^{ab}`; all lifts agree in `D^{ab}`, an obligation of P-07's
  proof).
* `unitNeg4`/`unitNeg3` re-expose (public) the private `uNeg4`/`uNeg3` of
  `GQ2/Reciprocity.lean`; `s̄ = rec(2)⁻¹` appears as `(R.recip uniformizer)⁻¹` (paper:
  `s̄ = rec(1/2)`).
* `topAbelianization` (T-10) now carries its canonical quotient topology + topological-group
  instances (registered in `SectionThree` with explicit names, per the instance-collision
  convention).

## Escalations (step-2 rule 1)

1. **Prop. 3.2, local side (`prop_3_2_local`) is not provable from the frozen census.**
   The paper's proof cites "the standard description of the tame quotient in the geometric
   normalization" — a classical input (NSW (7.5.2)-family: `G_{ℚ₂}/W_F ≅ Ẑ^{(2′)} ⋊ Ẑ`,
   geometric Frobenius squaring) that no B-axiom covers: the census is 2-centric, and B5
   sees only the abelianization (the tame quotient is metabelian-but-nonabelian and carries
   the full prime-to-2 inertia).  The board row P-09's "local side: B5 `ν_ur`" is therefore
   optimistic; its acceptance criteria already pre-authorize this flag ("if the local side
   needs more than the B5 bundle exposes, that is a design escalation, not a bundle edit").
   Options for the census discussion: (a) add the tame-quotient description as an eleventh
   classical leaf (it is as citable as B1/B4); (b) restructure Lemma 10.1's consumption so
   only the `Γ_A`-side identification plus abstract local wild-quotient data is needed —
   whether that suffices depends on P-11's Thm 4.2 statement, so decide after P-11 lands.
   Until resolved, `prop_3_2_local` is an honest, faithfully-stated gap.
2. **P-10 prerequisite (no census impact)**: the lift-quantified `ν_ur`-rows need "every two
   lifts agree", i.e. `ν_ur ∘ toAb` kills `proPKernel 2 AbsGalQ2` — via T-05's
   `proPKernel_le_ker` once `IsProP 2 (Multiplicative ℤ_[2])` is proved (open subgroups of
   `ℤ₂` are `2^kℤ₂`; provable, medium effort).  Same family as the flagged
   `IsProP 2 ℤ₂ˣ` O-finish refinement of T-11.
3. **Foreseen (P-14)**: the §6 cup↔symbol seam noted above.

## Marked half (P-11 handoff): Prop. 3.10 / Prop. 3.14 — `GQ2/SectionThreeMarked.lean`

Taken mid-ticket from P-11's board handoff ("P-06 states Prop 3.10/3.14 against these defs");
phrased against `GQ2/BoundaryFrame.lean` (`Ttame`, `PiBd`, `piSigma/piX0/piX1`, `Ztwo`,
`nuT`, `nuTwo`, `BoundaryMaps`).  Separate file so the core §3 statements depend only on
step-1 modules while this half imports the P-11 layer (committed as `f4f911e` while this
ticket was in flight).  Same namespace `GQ2.SectionThree`.

| Paper node | Lean name | Proof ticket |
|---|---|---|
| Prop. 3.10, `Γ_A` half (eq. (20)) | `prop_3_10_gammaA` | P-09 (word collapse: Lemma 3.1 forces `τ = 1`, `ω₂ = id`, (6) ⇒ (20)) |
| Prop. 3.10 local half = Cor. 3.12 (`(Π,ν₂) ≅ (D,ν_ur)`) | `prop_3_10_local_marked` | P-10 (Prop 1.1 + Nielsen (23)/(24)) |
| Prop. 3.14 arrows `ν_t, ν₂ ↠ Z₂` | `nuT_surjective`, `nuTwo_surjective` | P-09 |
| Prop. 3.14 (eq. (27) data) | `prop_3_14 : Nonempty BoundaryMaps` | P-09/P-10 jointly |

Encoding notes:
* **Prop. 3.11 (Nielsen) and Remark 3.13 are proof steps**, not statements — they are how
  P-10 derives `prop_3_10_local_marked` from `prop_1_1`; stating them separately would add
  allowlist surface without downstream consumers.
* **The `Z₂`-seam**: `nuTwo` targets `Ztwo = maxProPQuotient 2 ℤ̂` (P-11's boundary
  constituent) while B5's `ν_ur` targets `Multiplicative ℤ₂`.  `prop_3_10_local_marked`
  quantifies the identification explicitly (`ι : Ztwo ≅ Multiplicative ℤ₂`, pinned by
  `ι(ztwoOne) = ofAdd 1`), keeping the statement self-contained; constructing `ι` is P-10
  infrastructure (from `GQ2/Zhat.lean`'s structure), same family as escalation 2 above.
* **`BoundaryMaps` has no arithmetic `ν_ur`-anchor** (its `compat…` fields are internal
  tame-vs-pro-2 compatibilities): downstream counting (Thm 4.2 quantifies over any witness;
  Lemma 10.1 partitions for any fixed witness) never consumes the anchor.  The paper's
  "the same **natural** unramified character" is carried by `prop_3_10_local_marked`, which
  ties `ν₂` to `ν_ur` through the marked isomorphism — P-18 can compose the two if eq. (154)
  turns out to need the anchored form (P-11's in-file "residual-slack" flag, same locus).

## Verification

`lake build GQ2` green — 15 new `sorry` warnings, all P-06 (10 in `GQ2/SectionThree.lean`,
5 in `GQ2/SectionThreeMarked.lean`), all allowlisted; `scripts/check_axioms.sh` fully green
on the shared working tree (axiom placement, allowlist, census 10, no `native_decide`).
