# Review packet (v3) — the formalized statements behind Theorem 1.2

**Audience**: expert reviewers checking that this repository faithfully states (a) the known
**literature results** it assumes as `axiom`s and (b) the paper's own **interior nodes** it proves
from them.  You do **not** need to read Lean proofs: every `axiom` is quoted with a citation and a
docstring, everything *proved* is machine-checked (kernel axioms `propext`, `Classical.choice`,
`Quot.sound` only — "std-3" below), and the per-node axiom footprint is reported in §5.

**What v3 adds over v2.**  §2 (the axioms) is unchanged except that the two P-23 leaves B11a/B11b
now carry their **line-checked Serre citations** (previously "pending PDF verification — P-20").
New: **§4** quotes the paper's interior-node statements and — critically — the **statement
amendments** where the Lean statement carries hypotheses beyond the paper's printed text; **§5** is
the **App. D certificate diff**, a per-node `#print axioms` footprint checked against the paper's
proof-dependency certificate (Appendix D) and the §C reduction claims.  The P-22
citation-faithfulness classification (§2) is carried forward.

**Context.**  The repo formalizes the *statement* of the paper's Theorem 1.2 (a profinite
presentation of `G_{ℚ₂}`) and reduces its proof to (a) the paper's own §§3–10 argument (interior
nodes, §4; the still-open ones are the `sorry`s of §6) and (b) **fifteen classical literature
results B1–B13**, stated as Lean `axiom`s (§2).  (The census was ten at the step-1 freeze; **B10**
and the base-generalized **B9 + B11** were added by explicit, recorded census decisions during
step 2; **B11 was then split into the two classical leaves B11a/B11b by P-23** — user-approved
2026-07-04, census 12→13 — see the amendment history at the end of §2.)  The two review questions
are:

> **(Q1 — axioms, §2/§3)** Does each `axiom` correctly state the cited literature result, including
> all normalizations and conventions?
>
> **(Q2 — interior nodes, §4/§5)** Does each interior-node *Lean statement* match the paper's, and
> where it carries an **added hypothesis**, is that addition sound (a genuine standing assumption of
> the paper, not a smuggled weakening)?

Full citations with per-result discussion: [`literature-axioms.md`](literature-axioms.md).
Design rationale: [`formalization-plan.md`](formalization-plan.md).  Ticket-level acceptance
records: [`tickets-step1.md`](tickets-step1.md) (the live step-2 board is
[`tickets.md`](tickets.md)).

## 1. How to verify mechanically

```bash
lake exe cache get          # fetch Mathlib build cache (once)
lake build GQ2              # full build: `sorry`s only in the allowlisted files (§6 + the
                            # step-2 statement files tracked in docs/tickets.md)
./scripts/check_axioms.sh   # axiom hygiene: all `axiom`s in GQ2/Foundations/Axioms.lean,
                            # census = 13, sorries ⊆ allowlist, no native_decide
lake env lean GQ2/AxiomLedger.lean   # the repo-wide per-declaration certificate (P-01): every
                            # decl's transitive axiom footprint, B-labelled, with the sorry gap-map
```

For any individual theorem, `#print axioms <name>` in a scratch file shows its axiom footprint;
every *theorem* in the repo is std-3, plus (for declared consumers) exactly the B-axioms it
consumes.  §5 tabulates these footprints for the interior nodes; [`GQ2/AxiomLedger.lean`](../GQ2/AxiomLedger.lean)
is the mechanical, whole-library version.

## 2. The axioms: Lean names per B-leaf

All fifteen live in [`GQ2/Foundations/Axioms.lean`](../GQ2/Foundations/Axioms.lean) — the single
file permitted to declare axioms.  "Defs" = the file with the supporting definitions (each of
which is *fully proved*, never assumed).

| Leaf | Result (one line) | Citation (key) | Lean axiom | Defs |
|---|---|---|---|---|
| **B1** | `G_{ℚ₂}` is topologically finitely generated | NSW (7.5.14), Jannsen–Wingberg | `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated` | — (bare Mathlib) |
| **B2** | `Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ` (2-adic cyclotomic surjectivity) | Washington, Thm 2.5 | `GQ2.Foundations.cyclotomicCharacter_two_surjective` | — (Mathlib `cyclotomicCharacter`) |
| **B3c** | the canonical orientation of `G_{ℚ₂}(2) ≅ D₀`: `(χ(A), χ(S), χ(Y)) = (−1, 1, (−3)⁻¹)` | Labute, Thm 4 case (2) | `GQ2.dyadicOrientation` | `GQ2/Orientation.lean` |
| **B4** | `G_{ℚ₂}(2) ≅ D₀ = ⟨A,S,Y \| A²S⁴[S,Y]⟩` | NSW (7.5.11)(ii); Labute Thm 8 at `d = 1` | `GQ2.Foundations.absGalQ2_maxProTwo_presentation` | `GQ2/DyadicPresentation.lean`, `GQ2/MaxProP.lean` |
| **B5** | local reciprocity for `ℚ₂` (norm kernels; `ν_ur∘rec = −v₂`; `χ_cyc∘rec = (·)⁻¹`) | NSW (7.1.1)/(7.1.5); Serre LF XI–XIII | `GQ2.localReciprocity` | `GQ2/Reciprocity.lean` |
| **B6** | local Tate duality, per-`n`, **at every finite `k/ℚ₂`** (`inv : H²(G_k,μₙ) ≅ ℤ/n`, cup pairings perfect) | NSW (7.2.6) | `GQ2.tateDualityAt` (base `GQ2.tateDuality` = the `k=ℚ₂` member) | `GQ2/TateDuality.lean` |
| **B7** | local Euler characteristic: `#H¹ = #H⁰·#H²·2^{v₂(#M)}` (+ finiteness) | NSW (7.3.1) (Tate) | `GQ2.Foundations.absGalQ2_localEulerCharacteristic` | `GQ2/EulerCharacteristic.lean` |
| **B7′** | dyadic Hilbert symbol: `(2^α u, 2^β v)₂ = (−1)^{ε(u)ε(v)+αω(v)+βω(u)}` | Serre CiA III §1.2 Thm 1 | `GQ2.HilbertSymbol.hilbertSymbol_dyadic` | `GQ2/HilbertSymbol.lean` |
| **B8** | cyclotomic action on the peripheral generators of `Δ = maxPro2(F₂)` (Lemma 3.6) | Stix §3.3, Def. 37; Deligne | `GQ2.peripheralCyclotomicAction` | `GQ2/PeripheralAction.lean` |
| **B9** | Evens/Kahn eq. (111): `w(Tr⟨a⟩) = w(Tr⟨1⟩)(1 + cor[a] + N^{Ev}[a])`, deg ≤ 2, over any **finite dyadic base `k`** | Kahn Th. 2; Kozlowski 1.1; Evens Th. 1 | `GQ2.evensKahn_dyadic` | `GQ2/EvensKahn.lean` |
| **B10** | the tame quotient of `G_{ℚ₂}`, **oriented** (B10′): closed normal pro-2 `W` with `G_{ℚ₂}/W ≅ ⟨σ,τ ∣ τ^σ = τ²⟩_prof`, plus reciprocity-orientation (units ↦ `ker ν_t`; `rec(2)` ↦ geometric coordinate `ztwoOne⁻¹`) | NSW (7.5.3) (Iwasawa), (7.5.2); Serre LF IV; Neukirch ANT V (6.2), V (1.2) | `GQ2.tameQuotient` | `GQ2/TameQuotient.lean` |
| **B11a** | dyadic norm criterion over finite bases: `[a]∪[b] = 0 ⟺ b = x² − ay²` in `k` | **Serre LF Ch. XIV §2, Prop. 7 (iii)** — `(a,b)ᵥ=1 ⟺ b ∈ N_{K(a^{1/n})/K}`; symbol `(a,b)ᵥ = inv_K(a∪b)` (§2, p. 208); the `n=2` case | `GQ2.hilbertSymbol_normCriterion_finiteDyadic` | `GQ2/Foundations/Axioms.lean` |
| **B11b** | units are norms from an unramified quadratic extension (`IsUnramifiedQuadraticSpectral` ⟹ every base unit is a norm) | **Serre LF Ch. V §2, Prop. 3 + Cor./Rem. 1** — `N(Uⁿ_L)=Uⁿ_K`, and a finite residue field gives `U_K = N_{L/K}(U_L)` | `GQ2.unramifiedQuadratic_units_are_norms` | `GQ2/Foundations/Axioms.lean` |
| **B12** | local Kummer theory: `kummerClassK` surjects onto `H¹(G_k, 𝔽₂)` (injectivity proved, not assumed) | NSW (6.2.1) + Ch. VI §2 display + (6.2.2); Serre LF XIV §2 p. 206 | `GQ2.kummerClassK_surjective` | `GQ2/EvensKahn.lean` (map), `GQ2/Kummer.lean` (injectivity) |
| **B13** | dyadic unit filtration: uniformizer + `‖2‖ = ‖π‖^e` + graded counts `2^f − 1` / `2^f` | Serre LF IV §2, Prop. 6 | `GQ2.dyadicUnitFiltration` | `GQ2/UnitFiltration.lean` |

*(P-20, 2026-07-05, **corrected by P-15f1, 2026-07-06, against the updated scan**: the B11a/B11b
citations are line-checked against the `references/` Serre *Local Fields* (GTM 67) scan.
**B11a** = **Ch. XIV §2 "The Symbol (a,b)", Proposition 4, clause iii)** (pp. 206–207): "in order
that `(a,b) = 0`, it is necessary and sufficient that `b` be a norm in the extension
`K(a^{1/n})/K`" — Ch. XIV runs Props 1–3 in §1 and Props 4–5 in §2; the previously recorded
"Prop. 7 iii, p. 209" came from the pre-update scan.  The symbol-as-cup identification is **§2,
Proposition 5** (`(a,b) = i(φ_a ⌣ φ_b)`), so at `n = 2` this is
`[a]∪[b] = 0 ⟺ b ∈ N_{K(√a)/K} ⟺ b = x²−ay²`; §2 Remark 3 gives the `n = 2` conic form.  **B11b** = **Ch. V §2 "The Unramified Case",
Proposition 3** (p. 82) with its **Corollary + Remark 1**: `N(Uⁿ_L)=Uⁿ_K` for `n≥1`, and the three
equivalent conditions `[K*:NL*]=f ⟺ U_K=NU_L ⟺ K̄*=NL̄*`, the last holding when the residue field is
finite (Remark 1) — so for `K` with finite residue field (`ℚ₂`: residue `𝔽₂`) and `L/K` unramified,
`U_K = N_{L/K}(U_L)`, every unit is a norm.  This rests on Prop. 1 (`N: Uⁿ_L→Uⁿ_K`) and Prop. 2
(graded pieces = residue-field norm/trace) of the same §2.)*

*(P-23, 2026-07-04: the old single `axiom GQ2.dyadicNormCriterion` was split into the two classical
leaves B11a/B11b above; it survives as a same-name **theorem** over them, so every consumer's
`.1`/`.2` projection is unchanged. The repo-specific "unramified = equal spectral-norm value groups"
proxy is isolated as the `def GQ2.IsUnramifiedQuadraticSpectral` — a named convention, not an
axiom.)*

### Citation-faithfulness classification

Added per the adversarial review (`docs/adversarial-axioms-review.md` §6, 2026-07-04).  This
groups the fifteen leaves by **how directly the Lean statement matches a single published
theorem**, so a reviewer does not mistake a "nearby true theorem" for "this exact Lean interface
appears verbatim in the cited literature."  It carries **no soundness claim** — every leaf is
believed true; it is a guide to *where the translation layers are*.

| Tier | Leaves | What the reviewer checks |
|---|---|---|
| **Direct classical theorem** | B1, B6, B7, B7′, B12 | the Lean statement *is* the cited theorem, modulo notation (B12: the surjective half only — the injective half is proved) |
| **Classical theorem + encoding choices** | B4, B5, B9, B10, B13 | the cited theorem plus documented repo encodings (bundle shape, diagonalization, base generalization; B10: Iwasawa presentation + the ANT V (6.2) orientation clauses read through `toAb`-lifts, pinned to the B5 constant) |
| **Composite / project interface** | B3c, B8, B11a, B11b | a cited theorem bundled with **additional inputs**, each flagged in the axiom's docstring |
| **Available / unused** | B2 | in the census but consumed by no current declaration |

The **composite tier** is where human review time is best spent — those four leaves are *not*
verbatim single-citation theorems:

* **B3c** = Labute's orientation values + the local-Galois fact (Demushkin dualizing character =
  cyclotomic character, through this quotient map) + a normalized B4 isomorphism.  It **subsumes a
  marked B4**, so a downstream `#print axioms` showing `dyadicOrientation` need not also list B4
  unless B4 is consumed independently.  (Confirmed in §5: `prop_1_1`/`prop_3_10_local_marked` show
  `dyadicOrientation` **without** `absGalQ2_maxProTwo_presentation`.)
* **B8** = Stix (peripheral inertia acts through the cyclotomic character) + **cyclotomic
  surjectivity** (B2 globally / B5's `χ_cyc∘rec = (·)⁻¹` locally), needed for the all-units
  quantifier.  Statement kept in all-units form (P-22); the cyclotomic-image weakening was declined.
* **B11a/B11b** = Serre's Hilbert-symbol norm criterion (B11a) + unramified-unit-norm
  surjectivity (B11b).  **P-23 (done 2026-07-04, census 12→13)** split the old single
  `dyadicNormCriterion` axiom into these two classical leaves; the repo-specific
  "unramified = equal spectral-norm value groups" proxy — the least citation-faithful piece — is
  isolated as the **`def IsUnramifiedQuadraticSpectral`** (a named convention, *not* an axiom, so
  it adds no proof-theoretic strength) and consumed as B11b's hypothesis.  `dyadicNormCriterion`
  survives as a same-name **theorem** over B11a+B11b, so its consumers took zero edits.  Both leaves
  are consumed together at exactly one node — `lemma_6_16`, the deep-unit Hilbert ledger (§5).

B3c/B8 are documented composites with statements unchanged (**P-22**, user decision 2026-07-04);
B2's unused status is recorded on its axiom docstring and re-confirmed by the §5 footprint scan.

### Census amendment history (step 2)

* **B10** (`tameQuotient`) — added by explicit census decision resolving the **P-06 escalation**:
  the step-1 census was 2-centric and had no prime-to-2 tame structure (needed by Prop. 3.2's
  local side).  Census 10 → 11.  **Strengthened in place to the oriented form B10′**
  (**P-25 escalation**, user-approved 2026-07-06; census unchanged): two reciprocity-orientation
  clauses (Neukirch ANT V (6.2) units ↦ inertia; V (1.2) / NSW (7.1.2)(i) units are unramified
  norms) — discharges `tame_reciprocity` (Prop 3.14's `compatF`), whose derivation from B5's
  `norm_reciprocity` alone is blocked by absent local ramification theory in Mathlib
  (`docs/p25-tame-reciprocity-plan.md`).
* **B9 base-generalization + B11** — by explicit census decision (**P-15 escalation**,
  user-approved 2026-07-03): the paper applies eq. (111) and the §6.3 symbol arithmetic over
  *arbitrary finite dyadic bases* (Lemmas 6.16/6.17), while the step-1 layer had scoped B9 and
  the symbol theory to `k = ℚ₂`.  The cited theorems are base-general (Kahn's Théorème 2 needs
  no local hypothesis), so the former scoping was itself the deviation.  A reduction of the
  general-base statements to the `ℚ₂` forms is **not** available: restriction from `ℚ₂` reaches
  only a 3-dimensional subspace of `k^×/(k^×)²` (which has dimension `[k:ℚ₂]+2`), and the
  corestriction route is equivalent to cor-invariant compatibility — itself a general-base CFT
  input.  Census 11 → 12.  Review focus: the B9 statement is unchanged except for the base and
  the (equivalent) canonical-root/subgroup-relative phrasing of the Kummer classes
  (`kummerClassK`); B11 is new.
* **B11 split into B11a + B11b** — by explicit census decision (**P-23**, adversarial review
  rec 2, user-approved 2026-07-04): the single `dyadicNormCriterion` axiom bundled two classical
  facts (Serre's symbol/norm criterion and unramified-unit-norm surjectivity) with one repo
  convention ("unramified = equal spectral-norm value groups").  It is split into the two
  classical leaves `hilbertSymbol_normCriterion_finiteDyadic` (B11a) +
  `unramifiedQuadratic_units_are_norms` (B11b); the convention is isolated as the
  `def IsUnramifiedQuadraticSpectral` (**not** an axiom — it asserts nothing).
  `dyadicNormCriterion` is re-derived as a **same-name theorem** over the two leaves, so no
  consumer changed and every downstream `#print axioms` now surfaces B11a/B11b in place of the old
  single leaf.  Census 12 → 13.
* **B12 + B13** (`kummerClassK_surjective`, `dyadicUnitFiltration`) — by explicit census
  decision (**P-15f1 instantiation**, user-approved 2026-07-06): Lemma 6.17's dimension
  clause reduces (P-15f1 Layers 1–2b, all std-3, `GQ2/LocalKummer.lean`:
  `dim_deepPart_of_data`) to one `DeepKummerData` instance, whose literature content is
  exactly local Kummer theory (B12) and the (93) unit-filtration graded structure (B13).
  Everything else in the instance is proved, not assumed: `H^{1,2}(H_V, V) = 0` via coprime
  averaging (Brown III (10.2)), the square-class graded computation, the Hensel top
  (`sq_of_near_one`), the graded duality, Lemma 6.10, and — separately, as paper content —
  Lemma 6.11 projectivity for the deep-count multiplicativity.  B12 is surjectivity-only
  (injectivity proved); B13's proposed (F2) inertia-twist clause was found derivable and
  deliberately excluded.  Precise-citation record: `docs/p15f1-axiom-proposal.md`.
  Census 13 → 15.

**B3a/B3b are deliberately not axioms.**  B3a (the *definition* of a Demushkin group) is
formalized and stress-tested (`GQ2.IsDemushkin`, `GQ2.demushkinRank`, `GQ2.demushkinQ` in
`GQ2/Demushkin.lean` — `ℤ/2` is Demushkin of rank 1 and `q = 2`; the trivial group is not).
B3b (the abstract rank-3 `q = 2` classification) is carried at the field level by **B4**: an
abstract classification axiom would need Labute's *canonical-character* characterization
(his Prop. 6), which is deliberately deferred — an axiom quantified over an arbitrary character
with the right image would be a **different and possibly false** statement.

### Supporting definitions a reviewer may want to sanity-check

These are *constructions with full proofs* (std-3), so the review question is only whether the
**definition** matches the literature convention:

* `GQ2.ContCoh.H0/H1/H2` — continuous inhomogeneous-cochain cohomology, degrees ≤ 2 (Serre,
  *Galois Cohomology* I §2.2 conventions; `mem_Z1_iff`/`mem_Z2_iff` display the cocycle
  identities).  Cup products `cup02/cup11/cup20` in `GQ2/CupProduct.lean`.
* `GQ2.maxProPQuotient p G` — the maximal pro-`p` quotient, with its universal property
  (`GQ2/MaxProP.lean`).
* `GQ2.D0`, `GQ2.d0Relator`, generators `d0A/d0S/d0Y`, relation `d0_relation`
  (`GQ2/DyadicPresentation.lean`); free profinite groups and presented groups in
  `GQ2/FreeProfinite.lean`, `GQ2/ProfinitePresentation.lean`.
* `GQ2.Kummer.kummerClass : kˣ → H¹(G_k, 𝔽₂)` — the explicit Kummer cocycle
  `g ↦ [g√a ≠ √a]` (`GQ2/Kummer.lean`); relativized to subgroups in `GQ2/EvensKahn.lean`
  (`kummerZ1On`).
* `GQ2.MuN n` — `μₙ ⊂ ℚ̄₂` as a finite discrete `G_{ℚ₂}`-module (`GQ2/MuN.lean`); its dual
  `GQ2.MuDual n M = Hom(M, μₙ)` with the conjugation action (`GQ2/TateDuality.lean`).
* `GQ2.corFun` (degree-1 corestriction, index 2) and `GQ2.evensNormFun` (the index-two Evens
  norm, *defined* by the paper's two-point graph cocycle (98), with its 2-cocycle property
  proved) — `GQ2/EvensKahn.lean`.
* `GQ2.Zhat`, `GQ2.omega2`, ẑ-exponentiation `x ^ᶻ γ` (`GQ2/Zhat.lean`); `GQ2.GammaA` — the
  paper's presented group, eq. (7) verbatim (`GQ2/GammaA.lean`).
* `GQ2.IsUnramifiedQuadraticSpectral` — B11b's "unramified" proxy (equal spectral-norm value
  groups); a **named convention**, not an axiom (P-23).

## 3. Axiom deviations table (all flagged in-file at the axiom/definition)

| Leaf | Deviation from the literal literature statement | Why |
|---|---|---|
| B3b | no abstract classification axiom; field-level instance = B4 | needs Labute Prop. 6's canonical character (route (i), deferred); arbitrary-character version could be false |
| B3c | **interface form** (route (ii)): a B4 iso with cyclotomic values `(−1, 1, (−3)⁻¹)`; the *abstract* dualizing characterization of "canonical" is not formalized | what the paper's Lemmas 3.4/3.5 consume; route (i) is a stretch goal |
| B3c | the descent of `χ_cyc` to `G_{ℚ₂}(2)` is carried as bundle *data* | avoids formalizing `IsProP 2 ℤ₂ˣ`; with it, descent follows from `proPKernel_le_ker` (refinement) |
| B5 | injectivity of `rec` omitted | follows from the norm-kernel clause in the limit (`⋂_L N L^× = 1`); bundle kept minimal |
| B5 | `ν_ur` targets `Multiplicative ℤ₂`, never `ℤ` | a continuous hom from compact `G^{ab}` to discrete `ℤ` is trivial — a `ℤ`-target axiom would be *inconsistent* |
| B6 | per-`n` form (no `μ = ⋃μₙ`, no `ℚ/ℤ`); cross-`n` compatibility of `inv` not asserted | suffices for the paper's `n = 2` uses; avoids module colimits |
| B6 | Pontryagin duals encoded as `⋯ →+ ZMod n`; perfectness in one currying per degree pair; `inv` unnormalized | for `n`-torsion finite groups `Hom(−,ℚ/ℤ) ≅ Hom(−,ℤ/n)`; the opposite currying follows by counting; the paper's explicit `n=2` cup values come from B7′ |
| B6 | **base-generalized to every finite `k/ℚ₂`** (bundle `TateDualityAt G n` over the group `G = G_k`, gated by a local-Galois embedding `G ↪ G_ℚ₂` of finite index); the old `ℚ₂`-only `tateDuality` is the `k=ℚ₂` member (an in-repo `def`, no longer an axiom) | **census-neutral**, the exact base-generalization pattern of B9/B11 (2026-07-03) — NSW (7.2.6) already states Tate duality for arbitrary `p`-adic `k`, so the `ℚ₂`-only form under-used its own citation. Needed by **P-15f7**: the `(1,1)` pairing at `G_K = ker ρ` (`K` the splitting field) is the invariant nondegenerate `B` of `card_equivHoms_deep_eq_quot` (`GQ2/DeepDuality.lean`). Induced symbol-side content (mod-2 Hilbert pairing on `K^×/2`): **FV Ch. IV §5 Prop (5.1)(1)(5)(6)(9) + Corollary p.145 + Thm (5.2)** (nondegeneracy, perp-biduality `A=A^⊥⊥`); **O'Meara ITQF 63:13** (an independent nondegeneracy home); Serre LF XIV §1 Prop 3 Cor — all line-verified 2026-07-06, `docs/p15f7-axiom-proposal.md` |
| B7 | the `H⁰`-finiteness clause is retained although independently provable (`finite_H0`) | verbatim transcription of the literature statement |
| B8 | the **group-theoretic conclusion** of Lemma 3.6 only — no étale `π₁` | Mathlib has no anabelian `π₁`; reviewers check the implication "Lemma 3.6 ⇒ bundle", not a `π₁` formalization |
| B12 | surjectivity only; injectivity carried as a proved theorem | leaf-minimality (B5-injectivity precedent); `kummerClass_eq_zero_iff` is proved via Mathlib's infinite Galois correspondence |
| B13 | spectral-norm vocabulary; graded pieces enter through their **cardinalities**; no valuation ring/residue field constructed; the (F2) inertia-twist clause excluded (derivable) | the form the multiplicity count consumes; each retained clause is Serre LF IV §2 Prop. 6 verbatim-adjacent; minimality (`docs/p15f1-axiom-proposal.md`) |
| B8 | the cyclotomic exponent `ι : ℤ₂ˣ → ℤ̂` is bundle data, pinned by continuity and `ι(1) = ω₂` | full pinning is the ring structure of `ℤ̂`, out of scope |
| B9 | truncated to degrees ≤ 2; asserted at the paper's fixed diagonalizations `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩`, `Tr⟨1⟩ ≃ ⟨2, 2d⟩` with `w₁⟨x,y⟩ = [x]+[y]`, `w₂⟨x,y⟩ = [x]∪[y]` | no quadratic-form/SW machinery needed; Delzant well-definedness absorbed into the scoping; deg-1 component ⟺ classical `cor[a] = [N_{L/k}a]` |
| B9 | Kummer classes over a general base `k` use canonical square roots (`sqrtCl`) and live over the subtype group `G_k = k.fixingSubgroup ≤ G_{ℚ₂}` (`kummerClassK`) | class independent of the root (proved, T-13); one fixed algebraic closure throughout — no closure-transport |
| B11a | "`b` is a norm from `k(√a)`" encoded by the norm form `∃ x y, b = x² − ay²` | elementary and extension-plumbing-free; for `a` a square the norm form is universal, so the criterion needs no non-square hypothesis |
| B11b | "`k(√a)/k` unramified" encoded as elementwise equality of norm value groups (spectral norm on `ℚ̄₂`, the `def IsUnramifiedQuadraticSpectral`) | matches the `IsDeepUnit`/`lemma_6_16` convention; avoids ramification-index bookkeeping (`e = v_k(2)`: depth `≥ e+1 ⟺ ‖·‖ < ‖2‖`) |
| B11a | Steinberg `[x]∪[1−x] = 0` and `[2]∪[−1] = 0` are not separate clauses | consequences of the criterion via the norm representations `1−x = 1²−x·1²`, `−1 = 1²−2·1²` |
| general | cohomology is this repo's explicit `ContCoh` (degrees ≤ 2), not Mathlib's homogeneous `continuousCohomology` | Mathlib's has no low-degree cochain surface yet; `H⁰` agreement is proved (`GQ2/CtsCohBridge.lean`), `H¹/H²` comparison is Mathlib's own open TODO ([`cts-cohomology-gap.md`](cts-cohomology-gap.md)) |

Bundle-style axioms (B5, B6, B8, B3c) assert *existence of data with properties* (structure
types `LocalReciprocity`, `TateDuality n`, `PeripheralCyclotomicAction`, `DyadicOrientation`);
their stress tests are parametrized over an *arbitrary* bundle and are therefore axiom-free —
they certify the clauses are usable and mutually consistent, e.g. the B3c values reproduce the
paper's eq. (13) row *independently derived* from B5's normalizations.  This bundle shape also
explains a pattern in §5: an interior node *parametric over* `(R : LocalReciprocity)` or
`(D : TateDuality n)` shows **std-3**; the leaf surfaces as an axiom only where the axiom *term*
(`GQ2.localReciprocity`, `GQ2.tateDuality`) is instantiated.

## 4. The paper's interior nodes: statements (check against the *paper*)

These are the paper's **own** §§3–10 lemmas and propositions — its contribution, reducing eq. (154)
to the leaves of §2.  Unlike §2 (check against the literature), the review question here is **Q2**:
does the Lean *statement* match the paper's, and are any added hypotheses sound?  Machine status:
every node below is either **std-3 + its declared leaves** (proved) or an intentional **`sorry`**
(open; §6).  The paper's internal dependency edges (Appendix D) and the per-node axiom footprints
are diffed in §5.

**Locator.**  Paper node → Lean declaration (all under `namespace GQ2` and sub-namespaces
`FoxH`/`SectionThree`/`SectionSix`/`SectionSeven`/`SectionEight`/`RepIndependence`/`DeepPart`):

| Paper node | paper display | Lean declaration | file | status |
|---|---|---|---|---|
| Prop 1.1 (marked Demushkin normalization) | §3, `⟨a,s,y \| a²s⁴[s,y]⟩`, `ν_ur=(−2,1,0)` | `SectionThree.prop_1_1` | `PropOneOneAssembly.lean` | proved |
| Prop 2.3 (surjection count) | `\|Sur(Γ_A,G)\| = admissibleCount G` | `prop_2_3` | `Prop23.lean` | proved |
| Lemma 3.1 / 3.3 (tame quotient group theory) | `t^s=t²` finite ⇒ `C_e⋊C_n`, `O₂=W` | `Tame.tame_semidirect`, `Tame.tame_normal_two_subgroup_central`, `Tame.tame_zpowers_disjoint` | `Tame.lean` | proved |
| Prop 3.2 (common tame quotient, local side) | `G_ℚ₂/W_F ≅ T_tame` | `prop_3_2_local` | `Prop32.lean` | proved |
| Prop 3.10 (local marked anabelian iso) | `(Π,ν₂) ≅ (G_ℚ₂(2), ν_ur)` | `prop_3_10_local_marked` | `SectionThreeMarked.lean` | proved |
| Prop 3.14 (boundary-maps bundle) | the 21-field `BoundaryMaps` | `prop_3_14` | `SectionThreeMarked.lean` | `sorry` (one gap) |
| Lemma 5.7 (finite-word Stokes) | eqs. (38)/(39) | `FoxH.lemma_5_7_left`, `FoxH.lemma_5_7_right` | `FoxHeisenberg.lean` | proved |
| Prop 5.8 / Prop 5.10 (Fox–Heisenberg chain map) | (41) = chain identity (47) | `FoxH.prop_5_8_left`, `FoxH.prop_5_8_right` | `FoxHeisenberg.lean` | proved |
| Lemma 5.11 (exact-cone dévissage, 2-of-3) | §5 | `lemma_5_11` | `Devissage.lean` | proved |
| Lemma 5.12 / 5.13 (simple normal forms) | §5 | `FoxH.lemma_5_12`, `FoxH.lemma_5_13_split`, `FoxH.lemma_5_13_ramified` | `FoxHeisenberg.lean` | proved |
| Prop 5.15 (elementary-module duality) | §5 | `prop_5_15` (+ `FoxH.prop_5_15_of_simple`) | `DualityAssembly.lean` | proved |
| Lemma 5.16 (local lifting duality) | §5 | `FoxH.prop_5_16` | `LocalLiftingDuality.lean` | proved |
| Lemma 6.6 (Wall doubling) | (86) | `SectionSix.lemma_6_6` | `SectionSix.lean` | proved |
| Lemma 6.8 (ramified Hermitian + fixed space) | (87)/(88) | `SectionSix.lemma_6_8` | `SectionSix.lean` | proved |
| Prop 6.9 (candidate ramified Gauss sign) | (91) | `SectionSix.prop_6_9_unramified`, `SectionSix.prop_6_9_ramified` | `SectionSix.lean` | proved |
| Lemma 6.13 (universal two-point `D₈` class) | (96) | `SectionSix.lemma_6_13_dihedral`, `SectionSix.lemma_6_13_evens` | `SectionSix.lean` | proved |
| Lemma 6.14 (regular-module realization) | (102) | `RepIndependence.lemma_6_14` | `RepIndependence.lean` | proved |
| Lemma 6.15 (normalized Shapiro–cor identity) | (103)–(105) | `SectionSix.lemma_6_15_involution` (+ `_square`, `_free`) | `SectionSix.lean` | proved |
| Lemma 6.16 (deep-unit Hilbert-symbol ledger) | (105) | `SectionSix.lemma_6_16` | `SectionSix.lean` | proved |
| Lemma 6.17 (deep half totally singular) | §6.3 | `SectionSix.lemma_6_17_dim`, `SectionSix.lemma_6_17_vanish` | `SectionSix.lean` | `sorry` |
| Prop 6.18 (local ramified hyperbolicity) | (115) | `DeepPart.prop_6_18_ramified` (+ `SectionSix.prop_6_18_unramified`) | `DeepPart.lean` / `SectionSix.lean` | `sorry` |
| Lemma 6.21 (qualified determinant transgression) | (116) | `SectionSix.lemma_6_21` | `SectionSix.lean` | proved |
| Lemma 6.22 (marking-preserving shear) | §6.4 | `SectionSix.lemma_6_22` | `SectionSix.lean` | proved |
| Lemma 7.2 / Prop 7.4 (minimal-block form) | §7 | `SectionSeven.lemma_7_2`, `SectionSeven.prop_7_4` | `SectionSeven.lean` | proved |
| Lemma 8.6 (radical-edge variation) | (139) | `SectionEight.lemma_8_6_local` (+ `_gammaA`) | `SectionEight.lean` | local proved; Γ_A side `sorry` |
| Prop 8.9 (closed recursion) | (136)–(142) | `SectionEight.prop_8_9` | `SectionEight.lean` | `sorry` |
| Thm 4.2 (boundary-framed exact-image) | §4/§9 | `thm_4_2` | `BoundaryFrame.lean` | `sorry` |
| Lemma 10.1 (exhaustion by tame frames) | §10 | *(folded into `main_surjection_count`; not yet a standalone decl — P-18)* | `Statement.lean` | `sorry` |
| eq. (154) (surjection-count identity) | (154) | `main_surjection_count` | `Statement.lean` | `sorry` |
| Thm 1.2 (literal presentation) | Thm 1.2 | `main_presentation_literal` | `GammaA.lean` | `sorry` |

### 4.1 Statement amendments beyond the paper (review-critical)

Several §6 nodes carry hypotheses **added during formalization** beyond the paper's printed
statement.  Each is a documented standing assumption of the paper's §6.3 setup (or a genuine
correction), flagged in-file "flag for P-20" and reproduced here for scrutiny.  **These are the
Q2 review targets** — a reviewer should confirm each addition is a real hypothesis of the paper's
argument, not a smuggled weakening of the conclusion.

* **`lemma_6_17_dim` — the load-bearing one (P-15f1, user-approved 2026-07-05).**  The paper's
  Lemma 6.17 "the deep half is totally singular, `#X₊² = #H¹`" is **false as stated without the
  invariant quadratic form**.  The Lean statement adds the §6.3 standing package
  `(q, hq : IsQuadraticFp2 q, hns : Nonsingular q, hinv : IsInvariant C q)` whose polar makes `V`
  **self-dual**, plus `hc : Surjective ⇑c` and `hV2`.  *Counterexamples without self-duality*:
  `H_V = C₇⋊C₃` acting on `V = 𝔽₈` satisfies every other hypothesis but has `#H¹ = 8`, not a perfect
  square; and `#V = 2^{2m}` does not repair it (`C₁₅⋊C₄` on `𝔽₁₆` gives `dim X₊ = 1 ≠ 2`).  The
  paper's proof silently uses self-duality for the equal `V`-isotypic multiplicities in dual depth
  pairs.  Full route analysis: [`docs/p15f1-scoping.md`](p15f1-scoping.md).
* **`lemma_6_8` (P-15f / P-15b).**  Adds `hc : Surjective ⇑c` (§6.3: `ρ` classifies onto `C`), the
  invariant nonsingular form `(q, hq, hns, hinv)`, `hV2`, the simplicity of the `⟨T⟩`-isotypic
  piece `hWtsimple`, and — flagged as a **genuine remaining gap** — the isotypic data
  `hVU` ((88a) `#V^U = 2^{rs}`) and `hrank` ((88b) `rank(1+U) ≡ s`) **as hypotheses**: deriving them
  needs the `S`-action / `ω₂`-cycle structure absent from the supplied `⟨cτ⟩`-equivariance `he`
  (see [`docs/p15b-field-core-scoping.md`](p15b-field-core-scoping.md)).
* **`lemma_6_17_vanish` (P-15f).**  Adds `hc` and `hV2` — same §6.3 standing assumptions (the orbit
  analysis runs over the splitting field `K = ℚ̄₂^{ker ρ}` with `Gal(K/ℚ₂) ≅ C`, which needs `ρ`
  onto `C`).
* **`prop_6_18_unramified` (P-15f).**  Adds `hc : Surjective ⇑c` (as in the ramified case).
* **`lemma_6_14` (P-15d).**  Adds the compatibility hypotheses `Q⁰_loc` requires: `hdatW`
  (equivariant factor set), `hiC` (`i` a `C`-module map, eq. (77)'s `i⋊1`), `hρW`.
* **`lemma_6_21` (P-15i).**  Restores the paper's *relative* clause `κ⁰_q` (a zero-section-normalized
  equivariant class restricting to `q` on `V`), dropped by an earlier consequence-form extraction;
  without it the intrinsic equivariance obstruction blocks the proof
  ([`docs/p15i-transgression-gap.md`](p15i-transgression-gap.md)).
* **`lemma_6_6` — a paper-silent hypothesis, not a formalization artifact.**  Wall's doubling
  (86) is proved via an abstract Wall count that **requires** a 2-power-order monodromy hypothesis
  (`hU2 : ∃ n, U^[2^n] = id`).  The hypothesis is *essential*: the biadditive form `ω = [[1,1],[0,1]]`
  on `𝔽₂²` gives `∑(−1)^{…} = −8 ≠ 4 = (−2)^k`.  **The paper's induction sketch is silent on it.**
  In the repo the hypothesis is always discharged (the monodromy is `S^{ω₂}`, of 2-power order), so
  this is a *gap in the paper's exposition*, not in the formalization — flagged here for the record.

## 5. Appendix D certificate diff (per-node `#print axioms`)

The paper's **Appendix D** is a *proof-dependency certificate*: nine rows, each naming a
"proved input" and its "first downstream use" — an **internal implication chain** among the paper's
own lemmas (it names no literature axioms).  The certificate check has two layers: **(a)** does the
repo realize each App. D edge, and **(b)** does each node's machine-checked `#print axioms` footprint
match the literature leaves that edge chain reduces to (`literature-axioms.md` §C)?  All footprints
below are verified against a green build; the whole-library version is
[`GQ2/AxiomLedger.lean`](../GQ2/AxiomLedger.lean).

**Reading the footprint.**  `std-3` = `[propext, Classical.choice, Quot.sound]` (no mathematical
content).  A leaf label (B5, B6, …) means the node invokes that **axiom term**; a node *parametric*
over a bundle (`LocalReciprocity`, `TateDuality n`) shows std-3 and does **not** list the leaf (§3),
so the footprint is the *minimal* honest dependency.  `sorryAx` = the node is still an intentional
open leaf (§6).

### 5a. Appendix D's nine edges, as realized

| # | App. D: proved input → first downstream use | Lean input (footprint) | Lean downstream use (footprint) | edge |
|---|---|---|---|---|
| 1 | Stokes 5.7 & Prop 5.8 → chain map (Prop 5.10) | `lemma_5_7_left/right`, `prop_5_8_left/right` — **std-3** | chain map = the traced Prop 5.8 identities — **std-3** | ✔ realized, std-3 |
| 2 | dévissage 5.11 & 5.13 → duality Prop 5.15 | `lemma_5_11`, `lemma_5_13_split/ramified` — **std-3** | `prop_5_15` — **std-3** | ✔ realized, std-3 |
| 3 | two-point `D₈` class 6.13 → half-orbit Evens normalization | `lemma_6_13_dihedral/evens` — **std-3** | (feeds 6.15/6.16) | ✔ realized, std-3 |
| 4 | Shapiro–cor 6.15 → deep-half vanishing 6.17 | `lemma_6_15_involution` — **std-3** | `lemma_6_17_dim/vanish` — **sorryAx** | input ✔; **use OPEN** |
| 5 | ramified Hermitian 6.8 → Gauss sign Prop 6.9 | `lemma_6_8` — **std-3** | `prop_6_9_ramified` — **std-3** | ✔ realized, std-3 |
| 6 | deep-unit ledger 6.16 → hyperbolicity Prop 6.18 | `lemma_6_16` — **std-3 + B9 + B11a + B11b** | `prop_6_18_ramified` — sorryAx + B7; `prop_6_18_unramified` — sorryAx | input ✔ (**B9/B11 land here**); **use OPEN** |
| 7 | determinant transgression 6.21 → split `B/T ≅ V⋊C` | `lemma_6_21` — **std-3** | (consumed §§8–9) | ✔ realized, std-3 |
| 8 | radical-edge 8.6 → half-torsor count | `lemma_8_6_local` — **std-3 + B6 + B7**; `lemma_8_6_gammaA` — **sorryAx** | (half-torsor count, §8) | local ✔; **Γ_A side OPEN** |
| 9 | closed recursion 8.9 → Thm 4.2 | `prop_8_9` — **sorryAx** | `thm_4_2` — **sorryAx** | both **OPEN** |

Every App. D **input** node is realized; five are fully proved (rows 1, 2, 3, 5, 7 — std-3),
one carries its expected literature leaves (row 6 — B9/B11a/B11b at the deep-unit ledger), and the
still-open **use** nodes (rows 4, 6, 8-Γ_A, 9) are the remaining §6.3/§8/§9 tower, tracked in §6.
No proved node's footprint exceeds std-3 ∪ {its declared leaves}.

### 5b. Top-level and §3 nodes: footprint vs claimed reduction

| Node | claimed reduction (`§C` / App. D) | verified footprint | note |
|---|---|---|---|
| Prop 2.3 | elementary | **std-3** | ✔ |
| Prop 1.1 | B3, B4, B5, B7′ | **B3c + B8** | tighter: B3c **subsumes marked B4** (P-22); B5/B7′ enter at the `lemma_3_5_hilbert_ledger` sub-node, not Prop 1.1 itself (`lemma_3_5_hilbert_ledger` = std-3 + B7′) |
| Lemma 3.1 / 3.3 | finite group theory | **std-3** | ✔ |
| Prop 3.2 (local) | B10 (local side) | **B10** | ✔ — the `AxiomLedger` header's "Prop 3.2 → B5" is **pre-B10 stale** (predates the P-06 census decision); §C already says B10 |
| Prop 3.10 (local marked) | — | **B3c + B8** | anabelian iso through the marked B4 (= B3c) + peripheral action |
| Prop 3.14 (BoundaryMaps) | assembly | **B3c + B5 + B8 + B10′** | ✔ **sorryAx-free** (2026-07-06) — the orientation bridge is B10′'s clauses; `(B : BoundaryMaps)` for §§4–8 fully discharged |
| Prop 5.15 (duality) | §C annotates "uses B6" | **std-3** | tighter: the elementary-module duality is combinatorial; **B6 lands at `prop_5_16`** (std-3 + B6 + B7), where `H²` is actually computed |
| Lemma 8.6 (local) | — | **B6 + B7** | Tate duality + Euler characteristic at the half-torsor count |
| eq. (154) `main_surjection_count` | Thm 4.2 + Lem 10.1 + Prop 2.3 | **sorryAx** | **OPEN** — the §§3–10 tower (§6) |
| Thm 1.2 `main_presentation_literal` | + Prop 2.3 + reconstruction | **sorryAx** | **OPEN** — depends on `main_surjection_count` |

**Consumption of every leaf (honesty check, cross-checked with `AxiomLedger`).**  B3c/B8 → Prop 1.1,
Prop 3.10, Prop 3.14; B5 → Prop 3.14 (as axiom; bundle-parametric elsewhere); B6 → Prop 5.16,
Lemma 8.6-local; B7 → Prop 5.16, Prop 6.18-ram, Lemma 8.6-local; B7′ → `lemma_3_5_hilbert_ledger`;
B9/B11a/B11b → Lemma 6.16; B10 → Prop 3.2-local, Prop 3.14.  **B1** discharges the top-level t.f.g.
hypothesis of `main_presentation_literal`; **B4** is subsumed by the marked B3c and never surfaces
independently; **B2** has **zero consumers** (the "available/unused" tier, §2).  No leaf is dangling
except the deliberately-unused B2.

## 6. What remains assumed beyond the axioms (the open `sorry`s)

The step-1 gap map was three top-level `sorry`s; one (`exists_contSurj_of_card_le`, the Lemma 2.5
König step) is now **proved** (P-02).  The remaining gaps are the paper's own §§3–10 tower, all in
the `check_axioms.sh` allowlist and enumerated as the OPEN nodes of §4/§5:

| Declaration | Content | Status |
|---|---|---|
| `GQ2.main_surjection_count` (`Statement.lean`) | the §§3–10 argument, surjection-count form of Thm 1.2 (eq. (154)) | **step 2** — the top of the open tower |
| `GQ2.main_presentation_literal` (`GammaA.lean`) | Theorem 1.2 as printed (`Γ_A ≅ G_{ℚ₂}`) | follows from `main_surjection_count` + Prop 2.3 + the proved `reconstruction` |
| `GQ2.thm_4_2` (`BoundaryFrame.lean`) | boundary-framed exact-image theorem (§9 induction) | App. D row 9 use; open |
| `GQ2.prop_8_9` (`SectionEight.lean`) | closed recursion (136)–(142) | App. D row 9 input; open |
| `GQ2.lemma_6_17_dim` / `_vanish`, `GQ2.…prop_6_18_*` (`SectionSix.lean`, `DeepPart.lean`) | deep-half singularity + local ramified hyperbolicity (§6.3 Kummer cores) | App. D rows 4/6 use; open |
| `GQ2.…lemma_8_6_gammaA` (`SectionEight.lean`) | radical-edge variation, `Γ_A` side | App. D row 8, Γ_A side; open |
| `GQ2.prop_3_14` (`BoundaryMapsWitness.lean`) | one field (`tame_reciprocity`) of the `BoundaryMaps` bundle | the tame↔reciprocity orientation bridge; flagged for a census decision |

Everything else — the reconstruction theorem (Lemma 2.5), the profinite presentation machinery,
`Γ_A`, `ω₂`, Props 1.1/2.3/3.2/3.10, Lemmas 3.1/3.3, the whole §5 duality tower, and the proved §6
inputs (6.6/6.8/6.9/6.13/6.14/6.15/6.16/6.21/6.22) and §7 (7.2/7.4) — is fully proved, std-3 plus
the leaves listed in §5.

## 7. Known consistency cross-checks (already machine-verified)

* B3c values ↔ B5 normalizations: `χ_D`-row of eq. (13) derived from each independently.
* B3c values respect the `D₀` relation: `(−1)²·1⁴·[χS,χY] = 1`.
* B7′ reproduces `(−1,−1)₂ = −1` (the sign-convention anchor).
* B7 at `𝔽₂`-modules gives `#H¹ = #H⁰·#H²·#M` (the paper's §9.2 usage).
* `μₙ` is a legal duality argument for B6 (finite, discrete, `n`-torsion), and `#H²(μₙ) = n`.
* The B4 relator is realizable in a genuine finite 2-group (`DihedralGroup 4` marking).
* App. B's `S₃`-marking is admissible and `Γ_A ↠ S₃` (the presented group is nonvacuous).
* Lemma 6.6's Wall count needs a 2-power monodromy (`ω=[[1,1],[0,1]]/𝔽₂²` ⇒ `−8≠4`) — §4.1.
* Lemma 6.17 needs the invariant self-dual form (`C₇⋊C₃/𝔽₈` ⇒ `#H¹=8`, not a square) — §4.1.
