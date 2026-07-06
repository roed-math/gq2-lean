# P-15f1 scoping: `lemma_6_17_dim` — the deep-half dimension count

**Date**: 2026-07-05 (Fable).  **Ticket**: P-15f1 (split from P-15f).
**Target**: `GQ2/SectionSix.lean` `lemma_6_17_dim` — `#X₊² = #H¹(ℚ₂, V)` for ramified `V`.

---

## 1. SOUNDNESS FINDING: the frozen statement is FALSE without self-duality

The paper's Lemma 6.17 lives under the §6.3 standing setup: *"Let q : V → 𝔽₂ be the
invariant nonsingular quadratic form under consideration"* (§6.3 opening sentence).  The
polar of `q` makes `V` **self-dual** (`V ≅ V^∨` as `H_V`-modules), and the proof uses this:
*"self-duality of V gives equal V-isotypic multiplicities in each pair"*.  Our frozen
`lemma_6_17_dim` carries **no `q` and no self-duality hypothesis** — the extraction dropped
the standing assumption (same genre as the earlier `hc`/`hV2`/`hVU` gaps).

### Counterexample 1 (numeric refutation, no deepPart computation needed)

Take `H_V = C₇ ⋊ C₃` (tame-realizable over `ℚ₂`: `τ ↦ ε` of order 7, `σ ↦ s` of order 3
with `sεs⁻¹ = ε²` — consistent with `στσ⁻¹ = τ²` since `ord₇(2) = 3`), and
`V = 𝔽₈` with `ε` = multiplication by a primitive 7th root `ζ` and `s` = Frobenius `x ↦ x²`
(consistency: `s(εv) = ζ²v² = ε²(sv)` ✓).  Then:
- `V` is simple (`x⁷−1`'s cubic factor), faithful, `hV2` ✓, ramified (`hram` ✓ — `ε ≠ 1` on `V`);
- `#H⁰ = #H² = 1` (simple faithful nontrivial + dual likewise; B6-dual argument);
- B7 Euler: `#H¹ = ‖#V‖₂⁻¹ = 8`.

But `#X₊²` is a perfect square and **8 is not** — the statement fails for *every* value of
`#X₊`.  (Here `V ≇ V^∨`: inertia weights `{ζ, ζ², ζ⁴}` vs `{ζ⁶, ζ⁵, ζ³}`.)

### Counterexample 2 (`hcard : #V = 2^{2m}` does NOT repair it)

`H_V = C₁₅ ⋊ C₄` (`ord₁₅(2) = 4`, `⟨2⟩ = {1,2,4,8} ∌ −1`), `V = 𝔽₁₆`, `#V = 2⁴` (`m = 2`... `2m = 4`).
`V ≇ V^∨` again (weight orbit not inversion-closed).  Splitting field: `e = 15`, `f = 4`.
`V^∨`-multiplicities sit at odd depths `j ∈ {7, 11, 13, 29}` (`j ≡ −2^i mod 15`): three below
the middle depth `e = 15`, one above.  So `dim X₊ = 1` while `½ dim H¹ = 2`:
`#X₊² = 4 ≠ 16 = #H¹`.  Even-dimensionality is not the missing content; **self-duality is**.

### Proposed amendment (needs user greenlight — frozen P-14 statement, co-owned with P-15f2)

Add to `lemma_6_17_dim` exactly the vanish-clause's form package:

```
(q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
```

(no `dat`/`hdat`/`D` needed — `q` enters only through its polar's self-duality
`exists_polarSelfDual` ✓ banked).  Consumer-compatible: `prop_6_18_ramified` has all four.
P-20 flag in the docstring, per the amendment ledger convention.

---

## 2. Route decision: the paper's filtration count (Route B), NOT the pairing route

Two candidate proofs of the dim clause:

- **Route A (self-perp)**: prove `hself : X₊ = X₊⊥` for `polar (Q0loc)` and use the banked
  `card_deepPart_sq_of_selfperp`.  Needs (94)-orthogonality **and** maximality **and** the
  compatibility of the `H¹`-cup pairing with Hilbert symbols under the Kummer identification
  (projection-formula machinery) — strictly more infrastructure than Route B.
- **Route B (paper)**: `H¹(ℚ₂,V) ≅ Hom_{H_V}(V^∨, M_K)` (`M_K = K^×/K^{×2}`), exactness of
  `Hom_{H_V}(V^∨, −)` on the unit filtration, dual pairing of depth-`j` and depth-`(2e−j)`
  graded pieces, middle layer `V`-free (Lemma 6.10).  Then `#X₊ = 2^{½ dim}` **directly** —
  no `H¹`-pairing at all.  `card_deepPart_sq_of_selfperp` simply isn't used.

**Decision: Route B.**  Note (94)'s Hilbert orthogonality is then needed only by **P-15f2**
(free orbits) — for f1 the graded duality `gr_{2e−j} ≅ (gr_j)^∨` can be proved from the
explicit character description of the graded pieces (inertia `ζ ↦ ζ^j` twist of `k_K`;
`ζ^{2e} = 1` since `|inertia| = e`), no Hilbert pairing required.

### The multiplicity bookkeeping (why projectivity is unavoidable)

With `V^∨` projective-irreducible, `d(W) := dim Hom_{H_V}(V^∨, W)` is exact in `W`, hence
(i) additive over the filtration and (ii) equal to (composition multiplicity of `V^∨` in
`W`)·`dim End(V^∨)` — and composition multiplicities are duality-symmetric, giving
`d(gr_{2e−j}) = d((gr_j)^∨) = d(gr_j)` **through self-duality `V ≅ V^∨`**.  Ledger:

| depth `j` | `gr_j` | `d_j` |
|---|---|---|
| valuation layer `M_K/O^×`-part | `ℤ/2` trivial | 0 (`V` nontrivial) |
| `j = 0` | `k^×/(k^×)²= 0` (odd) | 0 |
| `1 ≤ j < 2e` even | `0` (eq. 93) | 0 |
| `1 ≤ j < 2e` odd, `j ≠ e` | `k_K(χ^j)` | paired: `d_j = d_{2e−j}` |
| `j = e` (odd since `e` odd) | inertia-trivial (Lemma 6.10) | 0 (`V` ramified, `hram`) |
| `j = 2e` | `ℤ/2` (`−1`-ish class), inertia-trivial | 0 |
| `j > 2e` | `⊆ squares` (Hensel, `sq_of_near_one` ✓) | 0 |

`X₊ = Hom(V^∨, U_{e+1}$-image$)` collects `Σ_{j>e} d_j = Σ_{j<e} d_j = ½ Σ d_j` ✓.

---

## 3. Architecture: parametric `DeepKummerData`, axiom decision deferred

Follow the **B6/TateDuality pattern**: define a structure bundling exactly what the count
consumes, prove `lemma_6_17_dim` parametrically over it (std-3 + structure-parametric), and
separate the instantiation into (a) literature-leaf candidates and (b) paper-proved content
that must be formalized, at the very end.

### Leaf candidates (literature only — [Serre LF XIV §§2–3], [NSW]; USER APPROVAL PENDING)

- **L1 (local Kummer bijectivity)**: `kummerClassK : kˣ → H¹(G_k, 𝔽₂)` (✓ exists, P-15e)
  descends to a **bijection** `k^×/k^{×2} ≅ H¹(G_k, 𝔽₂)` for finite dyadic `k`.
  (Injectivity plausibly provable from `two_values_of_fixed`; surjectivity = Kummer theory
  proper.  Mathlib's infinite Galois correspondence may make even surjectivity provable —
  quadratic subextensions via completing the square — but it is a real project; leaf first,
  discharge later if desired.)
- **L2 (dyadic square-class filtration, eq. (93))**: the `Gal(K/ℚ₂)`-submodule filtration of
  `M_K` by the `U_i`-images with graded pieces `k_K` at odd `1 ≤ j < 2e` (inertia acting by
  the `j`-th power character, Frobenius semilinearly), `0` at even depths, `ℤ/2` boundary
  layers, `U_{2e+1} ⊆` squares.
- **L3 (Hilbert orthogonality, eq. (94))**: `U_i^⊥ = U_{2e−i+1}`, `−1 ∈ U_e` — **needed by
  P-15f2, not by f1** (state it in the same leaf bundle for f2 to consume).

### Paper-proved content (NOT leafable without explicit escalation; formalize)

- **P1 (Lemma 6.10)**: `e` odd + middle-layer inertia-triviality — short, from L2's character
  data.
- **P2 (Lemma 6.11, projectivity of `V`, `V^∨`)**: Clifford/weight-orbit argument + Higman/
  Sylow criterion.  **The mountain** (Mathlib has neither Clifford theory nor the modular
  Sylow projectivity criterion).  Plan: make the consequence (`Hom`-exactness on the
  filtration + composition-multiplicity identity) a **structure field for now**, flagged
  `paper-proved content, must be discharged before any axiom is declared`; formalize as an
  isolated final brick, escalating only if it stalls.
- **P3 (inflation–restriction)** for the repo's continuous `H1` at `N = ker ρ` (note `V` has
  trivial `N`-action, so `V^N = V`): `res` injective mod inflation from `H¹(H_V, V)`, image
  the invariants, obstruction in `H²(H_V, V)`; both outer groups die by P2 (cohomological
  triviality of projectives: summand-of-coinduced + concrete Shapiro vanishing).
- **P4 (bridge)**: `deepPart ρ` (Kummer-coordinate definition) = `Hom_{H_V}(V^∨, U_{e+1})`
  under L1 — Quotient.out plumbing over the P-15f `kummerRestrict`/`phiRestrict` layer ✓.
- **P5 (bookkeeping)**: the halving arithmetic (§2 table) — easy.

### Effort map

P5 < P1 < P4 ≈ P3 < L1-if-proved ≪ P2.  Multi-session; the parametric development
unblocks everything except the final instantiation TODAY, with no census change.

---

## 4. Immediate work order (own file `GQ2/LocalKummer.lean`)

1. `structure DeepKummerData` (fields = L1/L2/L3 + the flagged P2-consequence field).
2. The halving core (P5) — pure finite-module arithmetic, std-3, no blockers.
3. `lemma_6_17_dim`-parametric: `theorem dim_deepPart_of_data (DK : DeepKummerData …) : …`.
4. P4 bridge, P3 inf-res, P1 — in that order (P4 pins the statement shapes).
5. Escalation checkpoint: present the L1/L2/L3 leaf bundle for census approval; then P2.

**Amendment gate**: step 3's statement needs the §1 amendment; SectionSix edit only after
user confirms (co-owned file, frozen P-14 statement).
