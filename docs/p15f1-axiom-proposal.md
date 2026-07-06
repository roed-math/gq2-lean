# P-15f1 axiom proposal — precise statements, citations, paste-ready blocks

**Date**: 2026-07-05 (Fable).  **Status**: ✅ **EXECUTED 2026-07-06** (user-approved) — the
two leaves landed as **B12 = `kummerClassK_surjective`** and **B13 = `dyadicUnitFiltration`**
(census 13 → 15; P-25 had *strengthened B10 in place*, so no index shift).  Defs file:
`GQ2/UnitFiltration.lean` (all proved).  The §6 blocks below were applied (adapted) to
`GQ2/Foundations/Axioms.lean`, `scripts/check_axioms.sh`, `GQ2/AxiomLedger.lean`,
`docs/literature-axioms.md` (incl. the B11a Prop-4 correction and the B10–B11 §B backfill
note), and `docs/review-packet.md` (incl. the census bullet, deviations rows, classification
rows, and the B11a Prop-4 correction).  One statement-design delta from §2 is recorded in the
B13 docstring: the (F2) inertia-twist clause was found **derivable** (exact `ℚ̄₂`-algebra +
the `he` normalization) and is deliberately not a field.

Supersedes §§3–4 of `docs/p15f1-leaf-candidates.md` (which retains the discovery narrative).
All citations below marked `[✓]` are **line-verified against the current `references/` PDFs**
(including the *updated* Serre *Local Fields* scan and the *new* Brown scan).

---

## 0. What this proposal contains

| Item | Kind | Census effect |
|---|---|---|
| **B∘1 `kummerClassK_surjective`** | new leaf | +1 |
| **B∘2 `dyadicUnitFiltration`** | new leaf (two-clause bundle) | +1 |
| `hinf`/`hext` (`H^{1,2}(H_V,V) = 0`) | **not a leaf** — in-repo proof plan with Brown citations | 0 |
| Lemma 6.11 projectivity | **not a leaf** — prove in-repo; Curtis–Reiner replaced (see §5) | 0 |
| eq. (94) orthogonality (L3) | **not proposed** — deferred to P-15f2 scoping (see §4.3) | 0 |
| **B11a citation correction** | fix to an existing review-packet entry | 0 |

Net census: `(13 + P-25's leaf) + 2`.

---

## 1. B∘1 — `kummerClassK_surjective` (local Kummer theory, surjective half)

**Mathematical statement.** Let `k` be a finite extension of `ℚ₂`.  The Kummer class map
`kˣ → H¹(G_k, ℤ/2)`, `a ↦ [g ↦ g(√a)/√a]`, descends to an **isomorphism**
`k^×/(k^×)² ≅ H¹(G_k, ℤ/2)` (continuous cochain cohomology; `μ₂ = {±1} ≅ ℤ/2`, canonical in
char 0).  **The leaf asserts only surjectivity** — injectivity is already proved in-repo
(`Kummer.kummerClass_eq_zero_iff : kummerClass a = 0 ↔ IsSquare a`, via
`InfiniteGalois.mem_range_algebraMap_iff_fixed`), so the axiom is strictly weaker than the
literature statement.

**Proposed Lean** (the map already exists — `GQ2/EvensKahn.lean:474`, the B9 input shape):

```lean
/-- **B∘1 (local Kummer theory, surjective half).**  Citation: NSW [1] Ch. VI §2 —
(6.2.1) (Hilbert's Satz 90) and the Kummer-sequence isomorphism
`H¹(G_K, μ_n) ≅ K^×/K^{×n}` displayed immediately after it (electronic ed. p. 344),
dual form (6.2.2); at `n = 2`.  Secondary: Serre LF [7] Ch. XIV §2 (p. 206), the
isomorphism `K*/K*ⁿ ≅ {characters of order dividing n}` (construction from Ch. X §3).
Injectivity is NOT assumed (proved: `Kummer.kummerClass_eq_zero_iff`). -/
axiom kummerClassK_surjective (k : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] k] :
    Function.Surjective (kummerClassK k)
```

**Citations.**
- **NSW [1], Ch. VI §2**: **(6.2.1) Theorem (Hilbert's Satz 90)** `[✓ verbatim]`, and the
  derivation displayed immediately after it `[✓ verbatim]`: from `1 → μ_n → K̄^× → K̄^× → 1`
  and `H¹(G_K, K̄^×) = 1`, "we obtain … an isomorphism `H¹(G_K, μ_n) ≅ K^×/K^{×n}`"; the
  numbered dual is **(6.2.2) Theorem** (`G(K_n|K) ≅ Hom(K^×/K^{×n}, μ_n)`) `[✓ verbatim]`.
- **Serre LF [7], Ch. XIV §2** (p. 206) `[✓ verbatim in the updated scan]`: "the map
  `a ↦ χ_a` defines an isomorphism of `K*/K*ⁿ` onto the group of those characters of `G`
  having order dividing `n`", with the construction of `φ_a` referenced to **Ch. X §3**.

**Deviations (for the review-packet §3 table).**
1. *Surjectivity-only* — the injective half is proved, not assumed (leaf-minimality, same
   spirit as the B5 "injectivity of `rec` omitted" row).
2. *Flavor* — stated for the `IntermediateField`-subtype group `H1 ↥(k.fixingSubgroup) (ℤ/2)`
   through the canonical root `sqrtCl` (identical to B9's `kummerClassK` input shape; the
   root-independence is T-13's `kummerCocycleFun_root_indep`, proved).
3. `μ₂ ≅ ℤ/2` is used silently (canonical in char 0; both NSW and the repo state coefficients
   this way).

**Consumers.** P-15f1 instantiation: transports the B∘2 filtration to `H¹(N, 𝔽₂)`
(`N = ker ρ = G_K`) and anchors `F 0 = ⊤` (every class is a Kummer class).  Likely also
P-15f2.

**Alternative to leafing** (recorded for honesty): surjectivity is provable-with-effort —
char-0 quadratic subextensions come from completing the square, and Mathlib's infinite Galois
correspondence pairs index-2 open subgroups with quadratic extensions.  Medium project; the
leaf can be discharged later without consumer churn (B11 precedent: axiom → same-name theorem).

---

## 2. B∘2 — `dyadicUnitFiltration` (the (93) core: unit-filtration graded structure)

**Mathematical statement** (two clauses; `L` a finite extension of `ℚ₂` here — applied to the
tame splitting field `K`; `U^{(0)} = U_L`, `U^{(i)} = 1 + 𝔭_L^i`):

- **(F1) Graded pieces.**  `U^{(0)}/U^{(1)} ≅ L̄^×` (residue multiplicative group) and, for
  `i ≥ 1`, `U^{(i)}/U^{(i+1)} ≅ 𝔭_L^i/𝔭_L^{i+1}` canonically — a 1-dimensional `L̄`-vector
  space, so (non-canonically) `≅ L̄⁺`.
- **(F2) Galois action on the graded pieces.**  For `s` in the inertia group and `π` a
  uniformizer, `s ↦ s(π)/π mod U^{(1)}` is a well-defined, uniformizer-independent
  homomorphism (into `μ ⊂ L̄^×` in the tame case), and the induced action on
  `U^{(j)}/U^{(j+1)} ≅ L̄·π^j` is by its `j`-th power twisted against the residue action:
  `s·(1 + uπ^j) ≡ 1 + s̄(u)·θ(s)^j·π^j (mod U^{(j+1)})`, where `θ(s) = s(π)/π mod 𝔭`.

**Citations.**
- **(F1) = Serre LF [7], Ch. IV §2, Proposition 6** `[✓ verbatim in the updated scan, pp. 66–67]`:
  "(a) `U_L/U_L^{(1)} = L̄^*` …  (b) For `i ≥ 1`, the group `U^{(i)}/U^{(i+1)}` is canonically
  isomorphic to the group `𝔭_L^i/𝔭_L^{i+1}`, which is itself isomorphic (non-canonically) to
  the additive group of the residue field `L̄`."
- **(F2)'s mechanism = Serre LF [7], Ch. IV §2, Proposition 7** `[✓ verbatim]`: "The map
  which, to `s ∈ G_i`, assigns `s(π)/π`, induces … an isomorphism `θ_i` of `G_i/G_{i+1}` onto
  a subgroup of `U^{(i)}/U^{(i+1)}`.  This isomorphism is independent of the choice of
  uniformizer `π`" — together with the same section's Prop. 5 (`s ∈ G_i ⟺ s(π)/π ∈ U^{(i)}`).
  The displayed twist formula is the (two-line) computation the paper itself performs inside
  Lemma 6.10's proof; the clause is flagged **composite** (B3c precedent): Prop. 6 + Prop. 7 +
  an elementary expansion, stated as one bundle clause because the consumer needs the twist
  *formula*, not the two propositions separately.
- Note the paper's own bracket for (93)/(94) — "[7, Chapter XIV, Sections 2–3]" — is coarse:
  XIV §§2–3 is symbol theory; the filtration lives in **Ch. IV §2**.  (Worth passing to the
  author with the next erratum batch.)

**Proposed Lean shape** (sketch — final signature is instantiation-phase design; the depth
predicate follows the `IsDeepUnit` spectral-norm idiom, made integer-graded by carrying a
uniformizer):

```lean
structure DyadicUnitFiltration (k : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] k] where
  π : (↥k)ˣ                                  -- a uniformizer: ‖π‖ = max {‖x‖ : x ∈ k, ‖x‖ < 1}
  hπ : ...
  gr : ℕ → Type                              -- graded carriers, ≅ residue field (i ≥ 1)
  grEquiv : ∀ i ≥ 1, (unit-depth-i classes) ≃+ gr i        -- (F1), canonical
  inertia_twist : ...                         -- (F2): the θ^j-twist + residue semilinearity
axiom dyadicUnitFiltration (k) [FiniteDimensional ℚ_[2] k] : DyadicUnitFiltration k
```

**What is deliberately EXCLUDED from the leaf** (provable in-repo; listed so a reviewer sees
minimality):
- the square-class graded computation (93) itself — from (F1)+(F2) by elementary char-2
  algebra: squares from depth `j < e` land at depth `2j` and fill it (residue field perfect,
  Frobenius onto), squares from depth `j > e` land at `e + j`, and depth `2e` is governed by
  the Artin–Schreier map `x ↦ x² + θx` (kernel of order 2) — the repo already has the
  Artin–Schreier counting (`exists_add_pow_eq`, DeepPart §HermitianCount);
- `U^{(2e+1)} ⊆ (L^×)²` — Hensel; **already proved** (`sq_of_near_one`, P-15e);
- `−1 ∈ U^{(e)}` — `v(−1−1) = v(2) = e`, trivial;
- the graded duality `gr_j ≅ (gr_{2e−j})^∨` and the multiplicity symmetry `hpair` — character
  inversion `θ^{2e−j} = θ^{−j}` (from (F2), `θ` valued in odd-order roots of unity) + finite
  module bookkeeping;
- Lemma 6.10 (middle layer, `d e = 0`) — **paper content**, proved in the paper from (F2)'s
  description; will be formalized, not leafed.

**Consumers.**  P-15f1 instantiation: `hpair`, `hmid`, and (with B∘1 + 6.11) the two family
counts of `GQ2.LocalKummer.DeepKummerData`.

---

## 3. NOT leafed: `hinf`/`hext` — in-repo proof plan (Brown citations for docstrings)

The two deferred Props of `GQ2/LocalKummer.lean` (`InflationVanishes`, `FamiliesExtend`) are
`H¹(H_V, V) = 0` and `H²(H_V, V) = 0` content.  The paper proves them (proof of (78), p. 25)
**without projectivity**:

- *unramified*: `H_V` is cyclic of **odd** order (the 2-primary part of the unramified image
  acts trivially on a simple char-2 module) — averaging kills all positive-degree cohomology;
- *ramified*: `I ◁ H_V` odd tame inertia, `V^I = 0` (simple, inertia nontrivial), `|I|` odd
  kills `H^j(I, V)` for `j > 0` — collapse.

**Docstring citation**: **Brown [5], Ch. III §10, Corollary (10.2)** `[✓ verbatim in the new
scan]`: "If `G` is finite, then `H^n(G, M)` is annihilated by `|G|` for all `n > 0`.  If `|G|`
is invertible in `M` …, then `H^n(G, M) = 0` for all `n > 0`."  (Also available if the
Sylow-restriction form is ever preferred: **Brown III (10.3) Theorem** `[✓ verbatim]` —
`res` maps `H^n(G,M)_{(p)}` isomorphically onto the `G`-invariants of `H^n(H,M)`, `H` a
`p`-Sylow.)

**In-repo route (no spectral sequence).**  For `hinf`: a continuous cocycle `b` on `G_ℚ₂`
vanishing on `N = ker ρ` descends to `H_V`; kill `b|_I` by the `|I|`-average (odd order
invertible on 2-torsion `V`); then for `i ∈ I, h ∈ H_V` the two evaluations of `b(ih)`
(cocycle expansion vs. `ih = h(h⁻¹ih)`) force `i • b(h) = b(h)`, i.e. `b(h) ∈ V^I = 0` — so
`b ≡ 0` after the adjustment.  ~30–50 lines.  `hext` is the same collapse one degree up
(2-cocycle averaging + the analogous two-way evaluation); medium.

---

## 4. Other non-proposals

**4.1 Total counts** — `#H¹(ℚ₂,V) = #V` is banked (`card_H1_eq_card_of_simple`, B6/B7).

**4.2 Lemma 6.11 (projectivity)** — recommendation unchanged: **prove in-repo** (it feeds
only the deep-count multiplicativity `Ext¹(V^∨, U_{e+1}) = 0`, where the §3 coprime trick
provably does not substitute).  References in §5.

**4.3 eq. (94) (`U_i^⊥ = U_{2e−i+1}`) — deferred to P-15f2's scoping.**  f1 no longer needs
it (Route B).  f2's minimal need is the single instance `(U_{e+1}, U_{e+1}) = 1`, which has a
candidate route through the existing **B11a** + a conductor bound, avoiding (94).  If the
sharp (94) is later wanted as a leaf: its *nondegeneracy* half is coverable by verified
pieces — Serre LF **XIV §1, Prop. 3 Corollary** `[✓]` (a character killed by all `(χ,b)_v` is
trivial) + **XIV §2, Prop. 4(v)** `[✓]` (antisymmetry) + **Prop. 5** `[✓]`
(`(a,b) = i(φ_a ⌣ φ_b)`, the symbol-equals-cup bridge) — but the *filtration-orthogonality*
half is **not a numbered theorem in any currently-provided PDF**.  Standard homes:
O'Meara, *Introduction to Quadratic Forms*, §63 (quadratic defect), or Fesenko–Vostokov,
*Local Fields and Their Extensions* (2nd ed., **freely downloadable from Fesenko's Nottingham
page** — recommend adding to `references/` before any L3 decision).

---

## 5. Curtis–Reiner replacement (the user's question)

Curtis–Reiner was cited only as background for Lemma 6.11's Clifford-theory step.  Since the
recommendation is to *prove* 6.11 (no axiom), these are **proof-guidance/§C citations**, not
axiom-grade; but for precision:

- **Primary textbook replacement**: **P. Webb, *A Course in Finite Group Representation
  Theory***, CUP 2016 — the author distributes the full PDF freely
  (`https://www-users.cse.umn.edu/~webb/RepBook/RepBookLatex.pdf`); recommend adding it to
  `references/`.  Clifford's theorem: **Ch. 5 §5.3** ("More on Induction and Restriction:
  Theorems of Mackey and Clifford"); relative projectivity + **Higman's criterion**: **Ch. 11**.
  Exact theorem numbers to be line-verified once the PDF is in `references/` (the project's
  `[✓]` discipline).
- **Canonical originals** (precise anchors, both short):
  - A. H. Clifford, *Representations induced in an invariant subgroup*, Ann. of Math. (2)
    **38** (1937), 533–550 — Clifford's theorem (restriction to a normal subgroup:
    semisimplicity + transitively-permuted isotypic components).
  - D. G. Higman, *Modules with a group of operators*, Duke Math. J. **21** (1954), 369–376 —
    origin of **Higman's criterion** (relative projectivity via the relative trace; for us:
    `[H_V : P]` odd invertible ⟹ `V|_P` free ⟹ `V` projective).
- Also fine (not free): D. J. Benson, *Representations and Cohomology I*, CUP 1991 (relative
  projectivity §3.6); Alperin, *Local Representation Theory*, CUP 1986.  **Serre's *Linear
  Representations of Finite Groups* does NOT cover this** (no relative projectivity) — not a
  substitute.

---

## 6. Paste-ready blocks (⏸ apply only after P-25's census lands; re-base indices)

### 6.1 `docs/literature-axioms.md` — append to §B after B9 ⁽*⁾

> ⁽*⁾ Note while editing: §B currently ends at B9 — B10/B11a/B11b have no §B entries (they are
> recorded in §E and the review-packet only).  Consider backfilling them in the same edit.

```markdown
### B∘1. Local Kummer theory (surjective half)  ✅ faithful
- **Statement.** For `k` finite over `ℚ₂`, the Kummer class map descends to an isomorphism
  `k^×/(k^×)² ≅ H¹(G_k, ℤ/2)`.  Leafed: **surjectivity only** — injectivity is proved
  (`Kummer.kummerClass_eq_zero_iff`, via Mathlib's infinite Galois correspondence).
- **Citation.** **NSW [1], Ch. VI §2: (6.2.1) (Hilbert's Satz 90) + the Kummer-sequence
  isomorphism displayed after it; dual form (6.2.2)** `[✓ verified in the provided NSW]`.
  Secondary: **Serre LF [7], Ch. XIV §2 (p. 206)** — `K*/K*ⁿ ≅ {characters of order ∣ n}`
  (construction Ch. X §3) `[✓ verified in the provided scan]`.
- **Lean.** `GQ2.kummerClassK_surjective` — surjectivity of the existing `kummerClassK`
  (`GQ2/EvensKahn.lean`, the B9 input shape; canonical root `sqrtCl`, subtype-group flavor).
- **Used at.** Lemma 6.17 (P-15f1: transport of the unit filtration to `H¹(G_K, 𝔽₂)`); §6.3.

### B∘2. Dyadic unit-filtration graded structure  ✅ faithful (composite clause F2)
- **Statement.** `L` finite over `ℚ₂`, `U^{(i)} = 1 + 𝔭_L^i`.  (F1) `U^{(0)}/U^{(1)} ≅ L̄^×`
  and `U^{(i)}/U^{(i+1)} ≅ 𝔭^i/𝔭^{i+1} ≅ L̄⁺` canonically (`i ≥ 1`).  (F2) inertia acts on
  `U^{(j)}/U^{(j+1)}` by the `j`-th power of the tame character `θ(s) = s(π)/π mod 𝔭`
  (uniformizer-independent), semilinearly over the residue action.
- **Citation.** **(F1) = Serre LF [7], Ch. IV §2, Prop. 6** `[✓ verified verbatim, pp. 66–67]`.
  **(F2) = Serre LF [7], Ch. IV §2, Prop. 7 (+ Prop. 5)** `[✓ verified verbatim]` + the
  two-line expansion the paper performs in Lemma 6.10's proof (composite clause, B3c
  precedent).  NB the paper's own bracket for (93)/(94) ("[7, Ch. XIV §§2–3]") is coarse —
  the filtration is Ch. IV §2.
- **Lean.** `GQ2.dyadicUnitFiltration` (bundle; depth via the `IsDeepUnit` spectral-norm
  idiom with a carried uniformizer).  Excluded because provable: the square-class graded
  computation (93), `U^{(2e+1)} ⊆ squares` (= `sq_of_near_one`, proved P-15e), `−1 ∈ U^{(e)}`,
  the graded duality/`hpair`, Lemma 6.10 (paper content, formalized).
- **Used at.** Lemma 6.17 dim clause (P-15f1 `DeepKummerData` instantiation).
```

### 6.2 `docs/literature-axioms.md` §E — add to the verified list

```markdown
- **B∘1** — NSW **(6.2.1)** (Satz 90) + the displayed Kummer isomorphism
  `H¹(G_K, μ_n) ≅ K^×/K^{×n}` of Ch. VI §2 and its dual **(6.2.2)** — verified verbatim;
  Serre LF **Ch. XIV §2 p. 206** (isomorphism onto characters; construction Ch. X §3) —
  verified verbatim in the updated scan.
- **B∘2** — Serre LF **Ch. IV §2, Prop. 6** (graded pieces of the unit filtration) and
  **Prop. 7** (+ Prop. 5) (`s(π)/π`, uniformizer-independent) — verified verbatim in the
  updated scan.  The (93) square-class consequence and the Hensel top are *proved*, not leafed.
- **Correction (B11a)** — in the updated Serre scan the norm criterion is
  **Ch. XIV §2, Proposition 4, clause iii)** (pp. 206–207), not "Prop. 7 iii (p. 209)" as
  previously recorded (Ch. XIV runs Props 1–3 in §1, Prop 4–5 in §2).  Bonus: **XIV §2
  Prop. 5** is `(a,b) = i(φ_a ⌣ φ_b)` — the symbol-equals-cup bridge the Lean statement
  uses, worth adding to the B11a note.
```

### 6.3 `docs/review-packet.md` §2 table — two rows (after B11b)

```markdown
| **B∘1** | local Kummer theory: `kummerClassK` is surjective onto `H¹(G_k, 𝔽₂)` (injectivity proved, not assumed) | NSW (6.2.1)+(6.2.2) & Ch. VI §2 display; Serre LF XIV §2 p. 206 | `GQ2.kummerClassK_surjective` | `GQ2/EvensKahn.lean` (map), `GQ2/Kummer.lean` (injectivity) |
| **B∘2** | dyadic unit filtration: graded pieces `≅ L̄` + tame-character twist `θ^j` on `gr_j` | Serre LF IV §2, Prop. 6 + Prop. 7 | `GQ2.dyadicUnitFiltration` | `GQ2/LocalKummer.lean` |
```

### 6.4 `docs/review-packet.md` — census amendment history bullet

```markdown
* **B∘1 + B∘2** (`kummerClassK_surjective`, `dyadicUnitFiltration`) — by explicit census
  decision (**P-15f1 instantiation**, user-approved 2026-07-__): Lemma 6.17's dimension
  clause reduces (P-15f1 Layers 1–2b, all std-3) to one `DeepKummerData` instance, whose
  literature content is exactly local Kummer theory + the (93) unit-filtration graded
  structure.  Everything else in the instance is proved: `H^{1,2}(H_V,V) = 0` via coprime
  averaging (Brown III.(10.2)), the square-class computation, the Hensel top
  (`sq_of_near_one`), the graded duality, Lemma 6.10, and — separately, as paper content —
  Lemma 6.11 projectivity for the deep-count multiplicativity.  Census (13+P-25) → +2.
```

### 6.5 `docs/review-packet.md` §3 deviations table — two rows

```markdown
| B∘1 | surjectivity only; injectivity carried as a proved theorem | leaf-minimality (B5-injectivity precedent); `kummerClass_eq_zero_iff` is proved via Mathlib InfiniteGalois |
| B∘2 | clause (F2) is composite: Serre IV §2 Props 5+7 + the elementary twist expansion | the consumer needs the twist *formula*; B3c composite precedent; each ingredient line-verified |
```

### 6.6 `docs/review-packet.md` §2 — B11a citation fix (edit the existing P-20 paragraph)

Replace `**Ch. XIV §2 "The Symbol (a,b)", Proposition 7, clause iii)** (p. 209)` by
`**Ch. XIV §2 "The Symbol (a,b)", Proposition 4, clause iii)** (pp. 206–207)` and append:
"`(§1 runs Props 1–3; §2 opens at Prop 4.  §2's Prop. 5 — (a,b) = i(φ_a ⌣ φ_b) — is the
symbol-equals-cup bridge; Remark 3 gives the n = 2 conic form.)`"  (The previous numbering
came from the pre-update scan; B11b's Ch. V §2 Prop. 3 + Corollary + Remark 1 citation was
re-checked against the updated scan and is **correct as recorded**.)
```
