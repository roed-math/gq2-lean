# Formalization plan: eliminating the nine literature axioms

Master plan for the four-step program (2026-07-02):

1. **Formalize the statements** of B1–B9 (`docs/literature-axioms.md`), building the missing
   definitions, with human-checkable output. ← *this document's focus*
2. Add each statement temporarily as an `axiom` and prove the paper's own results from them.
3. Plan the full formalization of each of the nine statements and their dependencies.
4. Remove the axioms; whole proof typechecks.

Ticket board: `docs/tickets.md`. Model routing: hard *design* work → Fable; well-specified
construction/proof work → Opus. Every ticket names its stress tests.

---

## Ground rules

- **Axiom quarantine.** Every `axiom` lives in exactly one file, `GQ2/Foundations/Axioms.lean`
  (defs live in sibling modules). One place for humans to review; one place to empty in step 4.
  The two existing axioms (B1, B2) migrate there.
- **Stress-test discipline.** Every new *definition* ships with 2–3 provable sanity lemmas in the
  same commit (the user's requirement: proving basic propositions stress-tests definitions).
  A definition without stress tests is not done.
- **Convention checklist.** The dangerous bugs are conventions, not mathematics: arithmetic vs
  geometric Frobenius, `χ(rec u) = u` vs `u⁻¹`, left vs right conjugation (`x^g = g⁻¹xg` here),
  cocycle sign conventions. Each axiom's docstring must state its conventions explicitly and cite
  the paper equation it matches. Human review specifically targets these.
- **Faithfulness deviations are flagged, never silent.** Where we state the *consequence used*
  rather than the literature statement (see B8, B9, B3-orientation below), the axiom docstring and
  the review doc say so prominently.
- **Guard script.** `scripts/check_axioms.sh` verifies the axiom inventory of the main theorems is
  exactly {propext, Classical.choice, Quot.sound} ∪ declared-B-axioms (ticket T-19).

---

## The two key unlocks (do these first)

### U1. `Ẑ` and `ẑ`-exponentiation are nearly free (T-06)

The audit called `ZHat` a missing foundation. It isn't anymore — we already own the machinery:

- `Zhat := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))`
  (finite quotients of ℤ are exactly ℤ/N, so this *is* `lim ℤ/N`).
- For `x` in any profinite group `G`, the hom `n ↦ xⁿ : ℤ →* G` lifts uniquely through the
  completion: `zpowHat x : Zhat ⟶ G` via `ProfiniteCompletion.lift`. Define `x ^ᶻ γ := zpowHat x γ`.
- **Naturality is free from `lift_unique`**: `f (x ^ᶻ γ) = (f x) ^ᶻ γ` for continuous `f`.
- **`ω₂ : Zhat`** is the compatible family `(omega2Exp N)_N` — compatibility (`N ∣ M ⇒
  omega2Exp M ≡ omega2Exp N [MOD N]`) follows from the two defining congruences we already proved
  (`oddPart_dvd_omega2Exp`, `omega2Exp_modEq_one`) by CRT, exactly like `powOmega2_pow_eq`.
- **Headline stress test**: for `f : G →* F` continuous, `F` finite:
  `f (x ^ᶻ ω₂) = powOmega2 (f x)` — ties the profinite definition to the entire existing finite
  calculus (`powOmega2_map`, App. A/B files).

Payoff: the four marking words become literal elements of `FreeProfiniteGroup (Fin 4)`, so
**`Γ_A := profinitePresentation (Fin 4) {tame relator, wild relator}` becomes definable and
Theorem 1.2 becomes stateable in its literal form** (T-21) — the single biggest
human-checkability win available. Also unblocks B8's statement.

Note: only the *additive* (group) structure of `Ẑ` is needed for step 1; no ring structure.
(`ω₂² = ω₂` and friends can wait.)

### U2. Continuous cohomology in degrees ≤ 2, by explicit cocycles (T-02)

B3, B6, B7, B9 all sit on `H⁰/H¹/H²(G, M)` for profinite `G` and finite discrete `M`, plus cup
products. We do **not** build derived functors. Explicit continuous cochains suffice and are
maximally human-checkable:

- `M`: use existing Mathlib classes, no new structure —
  `[AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M]`. (Stress test: the action kernel is open, i.e. factors through a finite
  quotient.)
- `H⁰ = M^G`; `H¹ = ` continuous 1-cocycles / 1-coboundaries; `H² = ` continuous 2-cocycles /
  2-coboundaries (inhomogeneous, Serre GC I §2.2 conventions).
- Cup products only in the shapes needed, defined relative to a `G`-pairing `M × N →+ P`:
  `(0,2), (1,1), (2,0)`; the `(1,1)` formula is `(a ∪ b)(g,h) = a g · g•(b h)`.
- Functoriality needed: inflation (from a finite quotient), restriction (to an open subgroup),
  corestriction in degree 1 (explicit coset-sum formula; needed by B9), coefficient functoriality.
- Comparison stress tests: for trivial action, `H¹(G,M) ≃ ContinuousAddMonoidHom G M`; for finite
  `G`, agreement with Mathlib's `groupCohomology.H1/H2` (via the CFT dep's explicit cocycle API).

This is the widest dependency and the most design-sensitive item → Fable ticket.

---

## Per-leaf statement plans

Legend: 🟢 statement already done · 🟡 stateable with listed infra · 🔴 hard design decision inside.

### B1 (`G_ℚ₂` top. f.g.) — 🟢 done
Already a faithful axiom (`Foundations.lean`). Migrates to `Axioms.lean` unchanged.

### B2 (2-adic cyclotomic surjectivity) — 🟢 done
Same.

### B4 (`G_ℚ₂(2) ≅ D₀`) — 🟡 needs I4 (max pro-2 quotient)
- **I4**: `maxProPQuotient p G := profiniteQuotient (⋂ {U : OpenNormalSubgroup G | IsPGroup p (G⧸U)})`
  — the intersection is filtered (`G/(U⊓V) ↪ G/U × G/V`), quotient machinery exists. Prove: it is
  pro-`p`; universal property (continuous homs to pro-`p` groups factor uniquely). Stress tests:
  finite `G` recovers the largest `p`-quotient; `(pro-p G)(p) = G`.
- Relator `r₀ = A²S⁴[S,Y]` is `ω₂`-free — expressible in `FreeProfiniteGroup (Fin 3)` today.
- **Axiom B4**: `Nonempty (ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) (profinitePresentation (Fin 3) {r₀}))`.
- Later strengthen (after B3a): `IsDemushkin (maxProPQuotient 2 AbsGalQ2)` + rank 3.

### B8 (Galois action on `π₁(ℙ¹∖{0,1,∞})`) — 🟡 needs I4 + U1 · **faithfulness deviation**
The literature statement needs étale `π₁` (infeasible). The paper only uses the *group-theoretic
output* (Lemma 3.6): on `Δ := maxProPQuotient 2 (FreeProfiniteGroup (Fin 2))` with generators
`P, T` and `C := (PT)⁻¹`, for every `u ∈ ℤ₂ˣ` there is a continuous automorphism `φ_u` and
elements `c_P, c_T, c_C` with `φ_u(P) = c_P⁻¹ P^u c_P` etc. We state **exactly this** as the
axiom, with `P^u` via ẑ-exponentiation (`u` embedded in `Ẑ`, or ℤ₂-exponentiation on pro-2 groups
via `maxPro2(Ẑ)` — design note in T-12; relating `maxPro2(Ẑ) ≅ PadicInt 2` is a nice-to-have).
**Flag for reviewers**: the axiom is Lemma 3.6's conclusion; its literature proof is Stix §3.3 +
Def. 37 (+ Deligne). Reviewers check the implication, not a π₁ formalization.

### B7′ (dyadic Hilbert symbol) — 🟡 no shared infra; start immediately
- Define `hilbertSymbol a b : Prop`/`±1` for `a b : ℚ₂ˣ` via solvability of `z² = ax² + by²`
  (elementary; no cohomology). Define `ε, ω : ℤ₂ˣ → ZMod 2` (`(u−1)/2`, `(u²−1)/8` mod 2 —
  `PadicInt` API).
- **Axiom B7′** = Serre CiA III §1.2 Thm 1, `p = 2` case.
- Stress tests (theorems, not axioms): `(a,b) = (b,a)`; `(a,−a) = 1` (witness `(0,1,1)`);
  invariance under squares; `ε(u)+ε(v) = ε(uv)` mod the correction (or just ε well-defined).

### B7 (local Euler characteristic) — 🟡 needs U2 only; easy once it exists
**Axiom**: for finite discrete `G_ℚ₂`-module `M`: `Finite (H^i)` for `i=0,1,2` and
`Nat.card H¹ = Nat.card H⁰ * Nat.card H² * 2 ^ (padicValNat 2 (Nat.card M))`.
(Finiteness asserted inside the axiom — it is *not* provable from our infra and shouldn't be.)

### B6 (local Tate duality) — 🟡 needs U2 + I10 (μ-modules) · 🔴 pairing formulation
- **I10**: `μ_n ⊂ AlgebraicClosure ℚ₂` as a finite discrete `G_ℚ₂`-module (Mathlib has
  `rootsOfUnity` + the Galois action; continuity from Krull-open stabilizers).
- Dual module `M' = Hom(M, μ)` with `(g•φ)(m) = g•φ(g⁻¹•m)`.
- **Axiom B6** (bundling the invariant map, itself CFT): ∃ `inv : H²(G_ℚ₂, μ_{tors}) ≃+ ℚ/ℤ`-style
  identification such that for every finite discrete `M` and `0 ≤ i ≤ 2` the cup pairing
  `H^i(M') × H^{2−i}(M) → H²(μ) → ℚ/ℤ` is perfect (induces iso onto the Pontryagin dual;
  finite abelian dual = `AddMonoidHom · (AddCircle (1:ℚ))` or `ℚ⧸ℤ` — decide in T-14).
- 🔴 decisions: colimit `μ = ⋃ μ_n` vs per-`n` statement (per-`n` with `n`-torsion `M` is simpler
  and suffices for the paper's 𝔽₂-modules — recommended); dual-group encoding.

### B3 (Labute classification) — split into three
- **B3a `IsDemushkin`** (🔴 Fable, needs U2): fin. gen. pro-`p`; `dim H¹(G,𝔽_p) = n < ∞`;
  `dim H²(G,𝔽_p) = 1`; cup `H¹ × H¹ → H²` nondegenerate. Stress tests: `ℤ₂`-analogue fails
  (`H² = 0` — provable? if hard, test instead: free pro-2 has `H² = 0` on finite level inflations;
  pick cheap ones); `H¹(G,𝔽₂) ≃ ContinuousMonoidHom G 𝔽₂`.
- **B3b Thm 8 statement** (🟡): note Thm 8's hypotheses are about the *local field*, so at
  statement level B3b ≡ B4 (already covered). We state the abstract classification only in the
  rank-3 `q=2` instance actually used: a Demushkin pro-2 group with `n = 3`, `q = 2`,
  `Im χ = {±1}×U₂⁽²⁾` is `≅ D₀`. Requires the invariants, hence B3c. If B3c stalls, B4 alone
  carries the proof (Prop 1.1 route) — B3b is then documentation.
- **B3c canonical orientation** (🔴 hardest design): Labute Thm 4 characterizes the unique
  `χ : G → U_p` via Prop 6's equivalent properties of `I(χ)` (dualizing-module flavor). Options:
  (i) formalize Prop 6(iii)-style finite-level characterization (read Labute §3 from the PDF at
  execution time and pick the most cohomology-light equivalent); (ii) *interface route*: for the
  local case define `χ_D := ` pullback of `cyclotomicCharacter` and state Thm 4 case (2)'s value
  computation `(χ(x₁), χ(x₂), χ(x₃)) = (−1, 1, (1−2^f)⁻¹)` under the B4 iso — this is what
  Lemmas 3.4/3.5 actually consume. Recommendation: do (ii) now (feeds step 2), keep (i) as a
  stretch ticket. **Flag deviation** if only (ii) ships.

### B5 (local reciprocity) — 🔴 Fable design; CFT-informed
CFT's blueprint states reciprocity at **finite level** (`Gal(l/k)ᵃᵇ ≅ kˣ/N lˣ`, Frobenius ↦
uniformizer) — align with that shape for future compatibility. Recommended **bundle axiom**
(avoids constructing `ℚ₂^{ur}` and residue towers):
∃ `rec : ℚ₂ˣ →* AbsGalQ2^{ab}` continuous with dense image, and `ν_ur : AbsGalQ2 →* ℤ₂`(-style
unramified coordinate) such that:
  (a) for every finite abelian `L/ℚ₂` in `ℚ̄₂`, the induced `ℚ₂ˣ → Gal(L/ℚ₂)` is surjective with
      kernel `N_{L/ℚ₂} Lˣ`;
  (b) `ν_ur ∘ rec = −v₂` (geometric-Frobenius↦1 normalization; matches `ν_ur(ā) = −2` for
      `ā = rec(−4)`, paper Lemma 3.5);
  (c) `χ_cyc (rec u) = u⁻¹` for `u ∈ ℤ₂ˣ` (paper's orientation row, eq. (13)).
Conventions here are the #1 review target. Alternative (more literal, more infra): Frobenius via
CFT's `IsNonarchimedeanLocalField.Unramified` — survey in T-00 before committing.

### B9 (Evens/Kahn/Kozlowski) — 🔴 Fable design; needs U2 + cor + norm + forms
Scope to what eq. (111) uses, in Galois cohomology over `k = ℚ₂`-adjacent fields (Kahn's own
setting), degrees ≤ 2:
- Kummer class `[a] ∈ H¹(k, 𝔽₂)` for `a ∈ kˣ` (I5: explicit cocycle `g ↦ [g√a = ±√a]`).
- `cor : H¹(L) → H¹(k)` for `[L:k] = 2` (explicit formula).
- **Evens norm** `N^{Ev} : H¹(L,𝔽₂) → H²(k,𝔽₂)` for index 2 — transcribe the paper's own explicit
  two-point cocycle (95)–(98) as the *definition*; stress test against Evens Thm 1's expansion
  `N(1+x) = 1 + tr(x) + N(x)` shape at finite level.
- Transfer form: `Tr_{L/k}⟨a⟩ := (x ↦ Tr_{L/k}(a x²))` via `Algebra.traceForm` scaling.
- Degree-≤2 SW classes of a rank-2 form: define for *diagonalized* forms
  (`w₁⟨a,b⟩ = [a]+[b]`, `w₂ = [a]∪[b]`); the axiom asserts (111) for the concrete forms used
  (well-definedness across diagonalizations is Delzant — fold into the axiom or restrict to the
  diagonal representatives the paper fixes). 🔴 decide in T-18.
- **Axiom B9** = eq. (111) (= Kahn Thm 2 rank-1 + Evens Thm 1 index-2, truncated to deg ≤ 2).
  **Flag deviation**: truncation + concrete-forms scoping.

---

## Wave schedule

- **Wave 0** (done this turn): plan, tickets, CFT clone/skim.
- **Wave 1** (parallel): T-06 (U1: Ẑ/ω₂ — Fable) · T-02 (U2 design — Fable) ·
  T-01 (I1 modules — Opus) · T-05 (I4 max pro-p — Opus) · T-07 (B7′ — Opus) · T-00 (CFT survey — Opus).
- **Wave 2**: T-21 (Γ_A + literal Thm 1.2 — Opus, after T-06) · T-12 (B8 — Opus, after T-05/06) ·
  T-08 (B4 — Opus, after T-05) · T-03/T-04 (cohomology lemma layer + cup — Opus, after T-02) ·
  T-13 (Kummer — Opus) · T-15 (μ-modules — Opus).
- **Wave 3**: T-09 (B3a — Fable) · T-14 (B6 — Fable draft/Opus finish) · T-16 (B7 — Opus) ·
  T-17 (B5 — Fable) · T-18 (B9 — Fable design/Opus finish) · T-11 (B3c — Fable).
- **Wave 4**: T-19 (Axioms.lean + guard) · T-20 (human review packet v2: Lean names beside each
  B-entry + deviations table) → **hand to expert reviewers before step 2**.

## Risks

1. **Convention bugs** (Frobenius/cyclotomic/conjugation directions) — mitigated by per-axiom
   convention docstrings, stress tests, human review focus.
2. **Axiom inconsistency** (an over-strong axiom set could prove `False`) — mitigated by minimal
   per-axiom content, keeping *provable* things as theorems (never axioms), stress tests.
3. **H²-level facts are unprovable with cocycle-only infra** (e.g. finiteness) — keep them inside
   the axioms; do not chase them.
4. **B5/B9 statement scope creep** — timebox; fall back to the interface bundles described above.
5. **CFT dep drift** — our Mathlib pin is CFT's; new-clone survey is read-only reference, not a dep bump.

## Steps 2–4 (sketch, to be planned after step 1)

- Step 2 = prove the paper-internal tower (Prop 3.2 local side, Lemmas 3.4–3.8, Prop 1.1, §§5–9,
  Thm 4.2, Lemma 10.1, eq. (154)) from the B-axioms. Its own decomposition doc once statements
  are frozen and human-reviewed.
- Step 3 = per-axiom elimination plans (B7′ and B2 look easiest; B6/B7 hardest; coordinate with
  the CFT project — their Tate-cohomology machinery is the intended engine for B5/B6).
- Step 4 = delete `Axioms.lean`, run the guard, done.
