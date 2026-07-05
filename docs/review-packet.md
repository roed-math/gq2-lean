# Review packet — the formalized statements of Theorem 1.2's literature inputs

**Audience**: expert reviewers checking that this repository's *axioms* faithfully state known
literature results.  You do **not** need to read Lean proofs: every `axiom` is quoted with a
citation and a docstring, and everything *proved* in the repository is machine-checked (kernel
axioms `propext`, `Classical.choice`, `Quot.sound` only — "std-3" below).

**Context.**  The repo formalizes the *statement* of the paper's Theorem 1.2 (a profinite
presentation of `G_{ℚ₂}`) and reduces its proof to (a) the paper's own §§3–9 argument (left as
explicit `sorry`s, see §4) and (b) **thirteen classical literature results B1–B11**, stated as
Lean `axiom`s.  (The census was ten at the step-1 freeze; **B10** and the base-generalized
**B9 + B11** were added by explicit, recorded census decisions during step 2; **B11 was then split
into the two classical leaves B11a/B11b by P-23** — user-approved 2026-07-04, census 12→13 — see
the amendment history at the end of §2.)  The review question is:

> **Does each axiom below correctly state the cited literature result — including all
> normalizations and conventions?**

Full citations with per-result discussion: [`literature-axioms.md`](literature-axioms.md).
Design rationale: [`formalization-plan.md`](formalization-plan.md).  Ticket-level acceptance
records: [`tickets-step1.md`](tickets-step1.md) (the live step-2 board is
[`tickets.md`](tickets.md)).

## 1. How to verify mechanically

```bash
lake exe cache get          # fetch Mathlib build cache (once)
lake build GQ2              # full build: `sorry`s only in the allowlisted files (§4 + the
                            # step-2 statement files tracked in docs/tickets.md)
./scripts/check_axioms.sh   # axiom hygiene: all `axiom`s in GQ2/Foundations/Axioms.lean,
                            # census = 13, sorries ⊆ allowlist, no native_decide
```

For any individual theorem, `#print axioms <name>` in a scratch file shows its axiom
footprint; every *theorem* in the repo is std-3, plus (for declared consumers, e.g. the B7
consequence suite) exactly the B-axiom it consumes.

## 2. The axioms: Lean names per B-leaf

All twelve live in [`GQ2/Foundations/Axioms.lean`](../GQ2/Foundations/Axioms.lean) — the single
file permitted to declare axioms.  "Defs" = the file with the supporting definitions (each of
which is *fully proved*, never assumed).

| Leaf | Result (one line) | Citation (key) | Lean axiom | Defs |
|---|---|---|---|---|
| **B1** | `G_{ℚ₂}` is topologically finitely generated | NSW (7.5.14), Jannsen–Wingberg | `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated` | — (bare Mathlib) |
| **B2** | `Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ` (2-adic cyclotomic surjectivity) | Washington, Thm 2.5 | `GQ2.Foundations.cyclotomicCharacter_two_surjective` | — (Mathlib `cyclotomicCharacter`) |
| **B3c** | the canonical orientation of `G_{ℚ₂}(2) ≅ D₀`: `(χ(A), χ(S), χ(Y)) = (−1, 1, (−3)⁻¹)` | Labute, Thm 4 case (2) | `GQ2.dyadicOrientation` | `GQ2/Orientation.lean` |
| **B4** | `G_{ℚ₂}(2) ≅ D₀ = ⟨A,S,Y \| A²S⁴[S,Y]⟩` | NSW (7.5.11)(ii); Labute Thm 8 at `d = 1` | `GQ2.Foundations.absGalQ2_maxProTwo_presentation` | `GQ2/DyadicPresentation.lean`, `GQ2/MaxProP.lean` |
| **B5** | local reciprocity for `ℚ₂` (norm kernels; `ν_ur∘rec = −v₂`; `χ_cyc∘rec = (·)⁻¹`) | NSW (7.1.1)/(7.1.5); Serre LF XI–XIII | `GQ2.localReciprocity` | `GQ2/Reciprocity.lean` |
| **B6** | local Tate duality, per-`n` (`inv : H²(μₙ) ≅ ℤ/n`, cup pairings perfect) | NSW (7.2.6) | `GQ2.tateDuality` | `GQ2/TateDuality.lean` |
| **B7** | local Euler characteristic: `#H¹ = #H⁰·#H²·2^{v₂(#M)}` (+ finiteness) | NSW (7.3.1) (Tate) | `GQ2.Foundations.absGalQ2_localEulerCharacteristic` | `GQ2/EulerCharacteristic.lean` |
| **B7′** | dyadic Hilbert symbol: `(2^α u, 2^β v)₂ = (−1)^{ε(u)ε(v)+αω(v)+βω(u)}` | Serre CiA III §1.2 Thm 1 | `GQ2.HilbertSymbol.hilbertSymbol_dyadic` | `GQ2/HilbertSymbol.lean` |
| **B8** | cyclotomic action on the peripheral generators of `Δ = maxPro2(F₂)` (Lemma 3.6) | Stix §3.3, Def. 37; Deligne | `GQ2.peripheralCyclotomicAction` | `GQ2/PeripheralAction.lean` |
| **B9** | Evens/Kahn eq. (111): `w(Tr⟨a⟩) = w(Tr⟨1⟩)(1 + cor[a] + N^{Ev}[a])`, deg ≤ 2, over any **finite dyadic base `k`** | Kahn Th. 2; Kozlowski 1.1; Evens Th. 1 | `GQ2.evensKahn_dyadic` | `GQ2/EvensKahn.lean` |
| **B10** | the tame quotient of `G_{ℚ₂}`: closed normal pro-2 `W` with `G_{ℚ₂}/W ≅ ⟨σ,τ ∣ τ^σ = τ²⟩_prof` | NSW (7.5.3) (Iwasawa), (7.5.2); Serre LF IV | `GQ2.tameQuotient` | `GQ2/TameQuotient.lean` |
| **B11a** | dyadic norm criterion over finite bases: `[a]∪[b] = 0 ⟺ b = x² − ay²` in `k` | Serre LF XIV §2 *(display numbers pending PDF verification — P-20)* | `GQ2.hilbertSymbol_normCriterion_finiteDyadic` | `GQ2/Foundations/Axioms.lean` |
| **B11b** | units are norms from an unramified quadratic extension (`IsUnramifiedQuadraticSpectral` ⟹ every base unit is a norm) | Serre LF V §2 *(display numbers pending PDF verification — P-20)* | `GQ2.unramifiedQuadratic_units_are_norms` | `GQ2/Foundations/Axioms.lean` |

*(P-23, 2026-07-04: the old single `axiom GQ2.dyadicNormCriterion` was split into the two classical leaves B11a/B11b above; it survives as a same-name **theorem** over them, so every consumer's `.1`/`.2` projection is unchanged. The repo-specific "unramified = equal spectral-norm value groups" proxy is isolated as the `def GQ2.IsUnramifiedQuadraticSpectral` — a named convention, not an axiom.)*

### Citation-faithfulness classification

Added per the adversarial review (`docs/adversarial-axioms-review.md` §6, 2026-07-04).  This
groups the thirteen leaves by **how directly the Lean statement matches a single published
theorem**, so a reviewer does not mistake a "nearby true theorem" for "this exact Lean interface
appears verbatim in the cited literature."  It carries **no soundness claim** — every leaf is
believed true; it is a guide to *where the translation layers are*.

| Tier | Leaves | What the reviewer checks |
|---|---|---|
| **Direct classical theorem** | B1, B6, B7, B7′, B10 | the Lean statement *is* the cited theorem, modulo notation |
| **Classical theorem + encoding choices** | B4, B5, B9 | the cited theorem plus documented repo encodings (bundle shape, diagonalization, base generalization) |
| **Composite / project interface** | B3c, B8, B11a, B11b | a cited theorem bundled with **additional inputs**, each flagged in the axiom's docstring |
| **Available / unused** | B2 | in the census but consumed by no current declaration |

The **composite tier** is where human review time is best spent — those four leaves are *not*
verbatim single-citation theorems:

* **B3c** = Labute's orientation values + the local-Galois fact (Demushkin dualizing character =
  cyclotomic character, through this quotient map) + a normalized B4 isomorphism.  It **subsumes a
  marked B4**, so a downstream `#print axioms` showing `dyadicOrientation` need not also list B4
  unless B4 is consumed independently.
* **B8** = Stix (peripheral inertia acts through the cyclotomic character) + **cyclotomic
  surjectivity** (B2 globally / B5's `χ_cyc∘rec = (·)⁻¹` locally), needed for the all-units
  quantifier.  Statement kept in all-units form (P-22); the cyclotomic-image weakening was declined.
* **B11a/B11b** = Serre's Hilbert-symbol norm criterion (B11a) + unramified-unit-norm
  surjectivity (B11b).  **P-23 (done 2026-07-04, census 12→13)** split the old single
  `dyadicNormCriterion` axiom into these two classical leaves; the repo-specific
  "unramified = equal spectral-norm value groups" proxy — the least citation-faithful piece — is
  isolated as the **`def IsUnramifiedQuadraticSpectral`** (a named convention, *not* an axiom, so
  it adds no proof-theoretic strength) and consumed as B11b's hypothesis.  `dyadicNormCriterion`
  survives as a same-name **theorem** over B11a+B11b, so its consumers took zero edits.

B3c/B8 are documented composites with statements unchanged (**P-22**, user decision 2026-07-04);
B2's unused status is recorded on its axiom docstring.

### Census amendment history (step 2)

* **B10** (`tameQuotient`) — added by explicit census decision resolving the **P-06 escalation**:
  the step-1 census was 2-centric and had no prime-to-2 tame structure (needed by Prop. 3.2's
  local side).  Census 10 → 11.
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

## 3. Deviations table (all flagged in-file at the axiom/definition)

| Leaf | Deviation from the literal literature statement | Why |
|---|---|---|
| B3b | no abstract classification axiom; field-level instance = B4 | needs Labute Prop. 6's canonical character (route (i), deferred); arbitrary-character version could be false |
| B3c | **interface form** (route (ii)): a B4 iso with cyclotomic values `(−1, 1, (−3)⁻¹)`; the *abstract* dualizing characterization of "canonical" is not formalized | what the paper's Lemmas 3.4/3.5 consume; route (i) is a stretch goal |
| B3c | the descent of `χ_cyc` to `G_{ℚ₂}(2)` is carried as bundle *data* | avoids formalizing `IsProP 2 ℤ₂ˣ`; with it, descent follows from `proPKernel_le_ker` (refinement) |
| B5 | injectivity of `rec` omitted | follows from the norm-kernel clause in the limit (`⋂_L N L^× = 1`); bundle kept minimal |
| B5 | `ν_ur` targets `Multiplicative ℤ₂`, never `ℤ` | a continuous hom from compact `G^{ab}` to discrete `ℤ` is trivial — a `ℤ`-target axiom would be *inconsistent* |
| B6 | per-`n` form (no `μ = ⋃μₙ`, no `ℚ/ℤ`); cross-`n` compatibility of `inv` not asserted | suffices for the paper's `n = 2` uses; avoids module colimits |
| B6 | Pontryagin duals encoded as `⋯ →+ ZMod n`; perfectness in one currying per degree pair; `inv` unnormalized | for `n`-torsion finite groups `Hom(−,ℚ/ℤ) ≅ Hom(−,ℤ/n)`; the opposite currying follows by counting; the paper's explicit `n=2` cup values come from B7′ |
| B7 | the `H⁰`-finiteness clause is retained although independently provable (`finite_H0`) | verbatim transcription of the literature statement |
| B8 | the **group-theoretic conclusion** of Lemma 3.6 only — no étale `π₁` | Mathlib has no anabelian `π₁`; reviewers check the implication "Lemma 3.6 ⇒ bundle", not a `π₁` formalization |
| B8 | the cyclotomic exponent `ι : ℤ₂ˣ → ℤ̂` is bundle data, pinned by continuity and `ι(1) = ω₂` | full pinning is the ring structure of `ℤ̂`, out of scope |
| B9 | truncated to degrees ≤ 2; asserted at the paper's fixed diagonalizations `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩`, `Tr⟨1⟩ ≃ ⟨2, 2d⟩` with `w₁⟨x,y⟩ = [x]+[y]`, `w₂⟨x,y⟩ = [x]∪[y]` | no quadratic-form/SW machinery needed; Delzant well-definedness absorbed into the scoping; deg-1 component ⟺ classical `cor[a] = [N_{L/k}a]` |
| B9 | Kummer classes over a general base `k` use canonical square roots (`sqrtCl`) and live over the subtype group `G_k = k.fixingSubgroup ≤ G_{ℚ₂}` (`kummerClassK`) | class independent of the root (proved, T-13); one fixed algebraic closure throughout — no closure-transport |
| B11 | "`b` is a norm from `k(√a)`" encoded by the norm form `∃ x y, b = x² − ay²` | elementary and extension-plumbing-free; for `a` a square the norm form is universal, so the criterion needs no non-square hypothesis |
| B11 | "`k(√a)/k` unramified" encoded as elementwise equality of norm value groups (spectral norm on `ℚ̄₂`) | matches the `IsDeepUnit`/`lemma_6_16` convention; avoids ramification-index bookkeeping (`e = v_k(2)`: depth `≥ e+1 ⟺ ‖·‖ < ‖2‖`) |
| B11 | Steinberg `[x]∪[1−x] = 0` and `[2]∪[−1] = 0` are not separate clauses | consequences of the criterion via the norm representations `1−x = 1²−x·1²`, `−1 = 1²−2·1²` |
| general | cohomology is this repo's explicit `ContCoh` (degrees ≤ 2), not Mathlib's homogeneous `continuousCohomology` | Mathlib's has no low-degree cochain surface yet; `H⁰` agreement is proved (`GQ2/CtsCohBridge.lean`), `H¹/H²` comparison is Mathlib's own open TODO ([`cts-cohomology-gap.md`](cts-cohomology-gap.md)) |

Bundle-style axioms (B5, B6, B8, B3c) assert *existence of data with properties* (structure
types `LocalReciprocity`, `TateDuality n`, `PeripheralCyclotomicAction`, `DyadicOrientation`);
their stress tests are parametrized over an *arbitrary* bundle and are therefore axiom-free —
they certify the clauses are usable and mutually consistent, e.g. the B3c values reproduce the
paper's eq. (13) row *independently derived* from B5's normalizations.

## 4. What remains assumed beyond the axioms (the three `sorry`s)

| Declaration | Content | Status |
|---|---|---|
| `GQ2.main_surjection_count` (`GQ2/Statement.lean`) | the paper's own §§3–9 argument (surjection-count form of Thm 1.2) | **step 2** of the program: to be proved *from* B1–B9 |
| `GQ2.main_presentation_literal` (`GQ2/GammaA.lean`) | Theorem 1.2 as printed (`Γ_A ≅ G_{ℚ₂}`) | follows from `main_surjection_count` + Prop. 2.3 + the proved `reconstruction` |
| `GQ2.exists_contSurj_of_card_le` (`GQ2/Reconstruction.lean`) | a compactness assembly step (König-type) | Mathlib-provable, not a literature gap; proof recipe in its docstring |

Everything else — including the reconstruction theorem (Lemma 2.5, for topologically finitely
generated profinite groups), the profinite presentation machinery, `Γ_A`, `ω₂`, and all
supporting lemmas — is fully proved.

## 5. Known consistency cross-checks (already machine-verified)

* B3c values ↔ B5 normalizations: `χ_D`-row of eq. (13) derived from each independently.
* B3c values respect the `D₀` relation: `(−1)²·1⁴·[χS,χY] = 1`.
* B7′ reproduces `(−1,−1)₂ = −1` (the sign-convention anchor).
* B7 at `𝔽₂`-modules gives `#H¹ = #H⁰·#H²·#M` (the paper's §9.2 usage).
* `μₙ` is a legal duality argument for B6 (finite, discrete, `n`-torsion), and `#H²(μₙ) = n`.
* The B4 relator is realizable in a genuine finite 2-group (`DihedralGroup 4` marking).
* App. B's `S₃`-marking is admissible and `Γ_A ↠ S₃` (the presented group is nonvacuous).
