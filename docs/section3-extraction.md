# §3 statement extraction — design note (ticket P-06)

Companion to [`GQ2/SectionThree.lean`](../GQ2/SectionThree.lean): maps every §3 interior node
(paper: Prop. 1.1, Prop. 3.2, Lemmas 3.4–3.8, displays (8)–(18)) to its Lean encoding, and
records the absorption, deviation, and escalation decisions.  Proof tickets: P-07 (3.5),
P-08 (3.7/3.8), P-09 (3.2), P-10 (1.1).

## Statement inventory

| Paper node | Lean name (`GQ2.SectionThree.*`) | Status | Proof ticket / Ax |
|---|---|---|---|
| §3 opening display (`T_tame`) | `GQ2.Ttame`/`tameSigma`/`tameTau` (P-11 layer), `GQ2.tame_relation` (`TameQuotient.lean`) | **proved** (def-layer) | — |
| Lemma 3.1 | `GQ2.Tame` (step 1) | **proved** | — |
| Prop. 3.2, `Γ_A` side | `prop_3_2_gammaA` | **proved** (`Prop32.lean`, std-3, no axioms) | P-09 ☑ |
| Prop. 3.2, local side (+ Lemma 3.3 char.) | `LocalTameQuotient` (extends B10's `TameQuotientData`), `prop_3_2_local` | **proved** (`Prop32.lean`, std-3 + B10 exactly) | P-09 ☑ |
| Lemma 3.3 (`O₂ = W`) | folded into `LocalTameQuotient.maximal` / design note §3.3 | — | — |
| Lemma 3.4 | **absorbed** (see below) | — | — |
| eq. (9)/(11) (`B = C₂t ⊕ ℤ₂S̄ ⊕ ℤ₂Ȳ`) | `BDecomposition`, `b_decomposition` | **proved** | P-07 (std-3; coordinate homs `τ,σ,γ` via `d0LiftHom`+`abLift`, `φ` bijective) |
| Lemma 3.5, `(ν_ur, χ_D)` rows of (13) | `GQ2.Reciprocity` stress tests (step 1) | **proved** | — |
| Lemma 3.5, `ā²s̄⁴ = 1` | `GQ2.abelianized_relator` (step 1) | **proved** | — |
| Lemma 3.5, marked abelianization | `lemma_3_5_marked_abelianization` | **proved mod `markedHom_bijective`** | P-07 (B5; plumbing std-3, sole gap = census-gated reciprocity iso, Escalation 5) |
| Lemma 3.5, cup/initial-form clause | `lemma_3_5_hilbert_ledger` | **proved** | P-07 (B7′) |
| Lemma 3.5, `(ν_ur, χ_D)` injective | `lemma_3_5_injective` | **proved** | P-07 (std-3; via `D0ab_coord`, **not** `b_decomposition`) |
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

* **`T_tame`** is `GQ2.Ttame` = `profinitePresentation {tameWord}` on `σ = of 0`,
  `τ = of 1` — the paper's `⟨σ, τ | τ^σ = τ²⟩_prof` verbatim.  *(History: P-06 and P-11,
  dependency-free wave-1 tickets, initially built identical copies; **deduplicated onto the
  P-11 layer** in the B10 follow-up commit — `SectionThree`'s copy removed, `tame_relation`
  proved in `GQ2/TameQuotient.lean`.)*  The companion `wildPart` dedup **landed 2026-07-03**:
  `SectionThree.wildPart` is now *definitionally* P-04's `GQ2.wildCore`
  (`wildPart := wildCore`; the old `normalClosure {gammaX0, gammaX1}`-closure shape is kept
  available as the `rfl`-lemma `wildPart_eq_closure`, and the generator spellings agree by
  `rfl` — `gammaSigma_def`…`gammaX1_def` bridge to the raw `quotientMk` spelling of the
  P-11 `BoundaryMaps` pinning fields).  Payoff: `isProP_wildPart` (= P-04's
  `isProP_wildCore`, the pro-2 clause of eq. (7) in the limit) plus `wildPart_isClosed`
  are now available to P-09/P-10 with no re-derivation.
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

1. **RESOLVED — axiom B10 added (user census decision, same day).**  Prop. 3.2's local side
   was not provable from the step-1 census (2-centric; B5 sees only the abelianization, and
   the tame quotient carries the full prime-to-2 inertia).  Resolution = option (a): the
   classical tame-quotient description is now axiom **B10** (`GQ2.tameQuotient :
   TameQuotientData`, `GQ2/TameQuotient.lean` + `GQ2/Foundations/Axioms.lean`; census 10 →
   11; citation NSW (7.5.3) (Iwasawa) + (7.5.2), verified against the PDF).  Deliberately
   **minimal**: the axiom asserts a closed normal pro-2 `W` with `G_ℚ₂/W ≅ T_tame`;
   Lemma 3.3's *maximality* (which pins `W` and makes the quotient canonical) is the paper's
   own proved content and stays a theorem — `LocalTameQuotient extends TameQuotientData`
   adds the `maximal` field, and P-09 proves `prop_3_2_local` from B10 + the Lemma 3.3
   argument (`T_tame` has no nontrivial closed normal pro-2 subgroup, via `GQ2/Tame.lean`).
   The `Ttame` dedup landed in the same change: `SectionThree` now uses the P-11 layer's
   `GQ2.Ttame`/`tameSigma`/`tameTau`, and `tame_relation` moved to `GQ2/TameQuotient.lean`.
2. **P-10 prerequisite (no census impact)**: the lift-quantified `ν_ur`-rows need "every two
   lifts agree", i.e. `ν_ur ∘ toAb` kills `proPKernel 2 AbsGalQ2` — via T-05's
   `proPKernel_le_ker` once `IsProP 2 (Multiplicative ℤ_[2])` is proved (open subgroups of
   `ℤ₂` are `2^kℤ₂`; provable, medium effort).  Same family as the flagged
   `IsProP 2 ℤ₂ˣ` O-finish refinement of T-11.
3. **Foreseen (P-14)**: the §6 cup↔symbol seam noted above.

4. **RAISED by P-08 (Opus, 2026-07-03) — P-08 is infrastructure-blocked; needs a new
   foundations ticket.**  When this note scoped 3.7/3.8 as "provable via B2/B8 + ℤ₂-linear
   coordinate transcription", it under-estimated the depth: **all three** P-08 statements
   route through infrastructure absent from the step-1 def-layers.  Precise gap map (against
   the paper's own proofs of Lemma 3.7 / Prop. 3.8, pp. 8–9):

   * **`lemma_3_7`** (Ψ_u ∈ Aut(D₀), Ā↦uĀ, S̄↦uS̄).  The paper *constructs* Ψ_u from B8's
     φ_u on `Δ = ⟨P,T⟩_pro2` through: (a) the identification `E□ = ⟨P,T,A | PTA²⟩ ≅ ⟨P,A⟩`
     and `E = ⟨S,A⟩` with `P = S³`, `T = S⁻³A⁻²` — a chain of **pro-2 free-group / one-relator
     (HNN) manipulations** with no repo analogue; (b) **`x ↦ xᵐ` bijective for odd `m`, with
     inverse `x ↦ x^{m⁻¹}`** (cube roots; `m⁻¹ ∈ ℤ₂`) — i.e. **ℤ₂-powering on pro-2 groups**,
     which T-12 *explicitly deferred* (`maxPro2(ℤ̂) ≅ ℤ₂`, its "nice-to-have"; no `ι : ℤ₂ → ℤ̂`
     exists — confirmed absent); (c) **surjective-on-Frattini ⇒ surjective** (pro-2 Burnside
     basis theorem) feeding `profinite_hopfian` (have the Hopfian half; missing the Frattini
     criterion).  None of (a)/(b)/(c) is ⭐⭐ proof-ticket work; (a)+the B8(`Fin 2`)→D₀(`Fin 3`)
     transport is the paper's genuine anabelian argument.
   * **`prop_3_8_lift`** = `lemma_3_7` (u-part, so all of the above) **plus** the shear
     `Θ_b` (paper (19)) whose `Y ↦ Y·S^b`, `A ↦ A^{S^b}` need `S^b` for `b ∈ ℤ₂` — **ℤ₂-powering
     again**.  (`Θ_b` for `b ∈ ℤ` *is* elementary and self-contained — a genuine
     `ContinuousMulEquiv D0 D0` via `presentationLift` + the identity `Θ_b(r₀) = r₀^{Sᵇ}`; it is
     the natural first deliverable once someone picks this up, but it only realizes `α_{1,b}`
     for integer `b`, so it does not close the statement.)
   * **`prop_3_8_classification`** (orientation-preserving auto of `B` ⟹ `α_{u,b}`, unique).
     This one needs **no** pro-2 powering — it is `ℤ₂`-module algebra on
     `B ≅ ℤ/2 × ℤ₂ × ℤ₂` — **but** its core step (`ξ(Ȳ) = Ȳ + b·S̄`, forcing the `Ȳ`-coordinate
     to `1`) needs **`η = (−3)⁻¹` generates a torsion-free procyclic pro-2 group**
     (`η^y = 1 → y = 0` for the `ℤ₂`-power, i.e. `1 + 4ℤ₂ ≅ ℤ₂` — the *exceptional `p = 2`*
     `exp`/`log` iso, not in Mathlib's `PadicInt` API).  **This same 2-adic fact is a
     prerequisite of P-07's `lemma_3_5_injective`** ("`η` topologically generates `1 + 4ℤ₂`",
     escalation-note dictionary) — it is **shared P-07/P-08 infrastructure**.

   **Recommended resolution** (mirrors escalation 1's option-(a) style, but a *foundations*
   ticket, not an axiom): a new ticket **"P-2x: ℤ₂-powering on pro-2 groups"** delivering
   (i) `x ^ᶻ⟨2⟩ u` for `u ∈ ℤ₂` on any pro-2 group (via `maxPro2(ℤ̂) ≅ ℤ₂`, finishing the
   T-12 nice-to-have) with odd-power bijectivity, (ii) the `1 + 4ℤ₂ ≅ ℤ₂` procyclic fact for
   the `η`-injectivity (shared with P-07), and (iii) the Frattini/Burnside "surjective-on-
   `G/Φ(G)` ⇒ surjective" criterion for pro-2 groups.  With (i)–(iii): `prop_3_8_classification`
   and the `Θ_b`/`α_{1,b}` half become tractable; `lemma_3_7`'s full B8→D₀ transport is still
   the hardest node (the anabelian bridge) and may warrant its own sub-ticket.  **Pending a
   census/scope decision** (as B10 was), P-08 stays open; no fake proofs land.  The `Ttame`
   dedup task (chip `task_88b19198`) is orthogonal and still stands.

   *Resolution (user decision, 2026-07-03):* ticket **P-21** opened on the board (Fable) —
   `GQ2/ZtwoPowering.lean`, delivering (i)+(ii) [with the `1+4ℤ₂` fact recast as
   `IsProP 2 ℤ₂ˣ` + `η`-injectivity, the form P-07/P-08 actually consume] and scoping (iii)
   Frattini as its phase 2; the `ι`-seam of `prop_3_10_local_marked` is (i)'s iso.  No new
   axiom needed — the census stays 11.

   *The (a) gap is closed (Fable, 2026-07-03, user-directed):* **`lemma_3_7` is proved** in
   `GQ2/AnabelianBridge.lean` (`GQ2.lemma_3_7`, statement verbatim; `#print axioms` = std-3 + B8
   only — `SectionThree.lemma_3_7` should delegate to it once P-07's co-owned edits to
   `SectionThree.lean` settle).  Two structural notes:
   1. **B8 statement amendment** (`hι_proj`, flagged in `GQ2/PeripheralAction.lean`'s
      docstring): the T-12 bundle's `ι` was pinned only by continuity + `ι 1 = ω₂`, which is
      *too weak to consume* — `ι u`'s action is undetermined for `u ≠ 1`.  P-21's
      `zhatProjTwo` makes the intended pinning (`ι(u) ≡ u` on the pro-2 part) expressible:
      `hι_proj : zhatProjTwo (ι u) = ofAdd u`.  Consistency at `u = 1` is the proved
      `zhatProjTwo_omega2`; classically `ι(u) = u·ω₂` satisfies everything.  Same review
      posture as before: Lemma 3.6 ⟹ the (strengthened) bundle.
   2. **The paper's `E□`/θ_u/cube-root scaffolding is inlined** (deviation, documented in the
      bridge's docstring): B8's three rows combine into one `Δ`-identity
      (`peripheral_identity`), which is pushed along `λ : Δ → D₀` (`P ↦ s³, T ↦ s⁻³a⁻²`,
      free — no relator check) to exactly the conjugation identity the `Ψ_u`-relator check
      needs (in the HNN form (16), `demushkin_relator_iff`).  Surjectivity is the P-21 (iv)
      Frattini criterion (index-2 quotients see `Ψ_u` as the identity on generators);
      Hopficity closes.  The Tietze elimination and odd-power bijectivity are thereby not
      needed for 3.7 (the latter remains available for `prop_3_8_lift`'s `Θ_b`-legs).

5. **RAISED by P-07 (Opus, 2026-07-03) — `lemma_3_5_marked_abelianization` needs the pro-2
   reciprocity *iso*, which B5 does not currently pin.**  The other three §3.5 clauses are
   **done** (`lemma_3_5_hilbert_ledger` B7′; `lemma_3_5_injective`, `b_decomposition` std-3).
   The marked-abelianization clause asks for `e : D₀^ab ≅ (G_ℚ₂(2))^ab` sending `Ā,S̄,Ȳ` to the
   `rec`-classes `−4, 1/2, −3`.  **Reduction (worked out):** the lift-quantified matching is
   `e(abMk d0A) = π(R.recip unitNeg4)` where `π : AbsGalQ2ab → (G_ℚ₂(2))^ab` is the descent of
   `abMk ∘ maxProPMk` through `toAb` (abelian target; this discharges "all lifts agree").  A hom
   `e` with these values *is definable* (the relation `π(rec(−4))²·π(rec(1/2))⁴ = π(rec(1)) = 1`
   holds since `rec` is a hom and `(−4)²(1/2)⁴ = 1`) — but showing it is an **iso** needs
   `{π(rec(−4)), π(rec(1/2)), π(rec(−3))}` to coordinatize `(G_ℚ₂(2))^ab`, i.e. that `rec`'s image
   topologically generates the pro-2 abelianization and separates the three classes.  That is the
   classical local-reciprocity iso on the pro-2 part (`ℚ₂ˣ`'s pro-2 completion `≅ ℤ₂×ℤ/2×ℤ₂`,
   `{−4,1/2,−3}` a basis), which B5 gives only the *coordinate values* of (`nu_ur_recip_*`,
   `chiCyc_recip_*`), not surjectivity/injectivity.  **The paper proves 3.5-marked *before* 3.8,
   so this is NOT a `prop_3_8` dependency** — it is local CFT.  **Resolution (needs user census
   decision, cf. B10/B11):** either (a) strengthen B5 with a "recip induces the pro-2-ab iso"
   clause, or (b) derive it from B5's `norm_reciprocity` clause via a limit argument (substantial:
   `ℚ₂ˣ` structure + dense image + the three-classes-generate).  Same infrastructure family as
   P-10 (`prop_1_1`).  **Reduction landed in code (Opus, same day):** `markedPi` (the `π` descent),
   `markedHom` (definable hom, relation `(−4)²·2⁻⁴=1` verified) and the three generator-matching
   clauses are all **std-3**; `lemma_3_5_marked_abelianization` is **proved modulo the single lemma
   `markedHom_bijective`** (`SectionThree.lean`, now the only remaining sorry — precisely this gap).
   Whoever resolves the census decision just proves `markedHom_bijective : Bijective (markedHom R)`.

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
