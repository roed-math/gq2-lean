# B11b discharge plan: prove `unramifiedQuadratic_units_are_norms` (census −1)

**Goal.**  Replace the axiom (`Foundations/Axioms.lean`, namespace `GQ2`)

```lean
axiom unramifiedQuadratic_units_are_norms
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (a : (↥k)ˣ) (δa : AlgebraicClosure ℚ_[2])
    (hδa : δa ^ 2 = ((a : ↥k) : AlgebraicClosure ℚ_[2]))
    (hunram : IsUnramifiedQuadraticSpectral k δa) :
    ∀ u : (↥k)ˣ, ‖((u : ↥k) : AlgebraicClosure ℚ_[2])‖ = 1 →
      ∃ x y : ↥k, (u : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2
```

by a proof — Serre, *Local Fields*, Ch. V §2 ("norms of unramified extensions are the units
times the norms of uniformizers"), for the quadratic case, in the repo's spectral vocabulary
(`IsUnramifiedQuadraticSpectral` = equal norm value groups; "norm from `k(√a)`" = the norm form
`x² − a y²`).  All std-3.

**Estimated effort**: **4½–6 lane-sessions** (recon ½ · quadratic layer 1 · residue layer 1–1½
**(the F pocket)** · approximation engine 1 · capstone ½–¾ · flip ½).
Board: [`b11b-tickets.md`](b11b-tickets.md).  **Depends on B13** (`b13-proof-plan.md`): the
filtration capstone `dyadicUnitFiltration'` is invoked at **both** `k` and `L = k(δa)` — B11b-3
onward is gated on B13-5's capstone (not on its census flip).

## 0. Shared-tree constraints

As on the B13 board: development in the named new files only (`GQ2/TeichmullerLift.lean`,
`GQ2/UnramifiedQuadraticNorms.lean`); no shared-file edits before the flip (B11b-5, **user
gate**); census (12 at writing, 11 after B13's flip) decrements only at B11b-5; standard
per-increment gates (own-file build, `lean_verify` std-3, `check_axioms`, own-files staging).
NB `GQ2/UnramifiedNorm.lean` already exists (unrelated, P-16d6e-era) — hence the
`UnramifiedQuadraticNorms` name.

## 1. Mathematical route

Fix `k`, `a`, `δa` (`δa² = a`), `hunram`.  Write `q̄₂`-norms plainly; `U^{(i)}` is the B13
filtration.

**(D) Degenerate case** `δa ∈ k`: `u = x² − a y²` solves with
`x = (1+u)/2, y = (u−1)/(2δa)` — `x² − δa²y² = (x−δa y)(x+δa y) = 1·u` (char 0, `2` invertible
in `k`).  So assume `δa ∉ k`.

**(Q) The quadratic layer.**  `L := k⟮δa⟯` (an `IntermediateField ℚ_[2] ℚ̄₂` containing `k`),
with basis `{1, δa}` over `k` (`δa ∉ k`, `δa² ∈ k`): every `z ∈ L` is uniquely `x + y·δa`
(`x, y ∈ k`).  The **involution**: a global `g ∈ ℚ̄₂ ≃ₐ[ℚ₂] ℚ̄₂` fixing `k` pointwise with
`g δa = −δa` (the two roots of the `k`-minpoly `X² − a` are conjugate: lift the `k`-embedding
`k⟮δa⟯ → ℚ̄₂`, `δa ↦ −δa`, to an endomorphism of `ℚ̄₂` by `IsAlgClosed.lift`, bijective by
`Algebra.IsAlgebraic.algHom_bijective`).  Then on `L`: `σ(x + yδa) = x − yδa`;
`N(z) := z·σz = x² − a y² ∈ k` and `s(z) := z + σz = 2x ∈ k`; `σ` **preserves norms**
(`norm_galois`, the 3-line `NormedAlgebra.norm_eq_spectralNorm` + `spectralNorm_eq_of_equiv`
argument at `HilbertLedger.lean:313` — re-derived upstream), hence preserves `O_L`, `𝔪_L`, and
every depth ball.

**(F) Filtration transfer.**  B13 at `k` gives `π` with `hπ_max`.  `hunram` says every nonzero
`z ∈ L` has `‖z‖ = ‖w‖` for some nonzero `w ∈ k`; hence `π` satisfies the max-property **for
`L` too** (`z ∈ L`, `‖z‖ < 1 ⟹ ‖z‖ = ‖w‖ < 1, w ∈ k ⟹ ≤ ‖π‖`) — one uniformizer serves both
fields, and `σπ = π`.  B13's construction applied to `L` (or its interface re-run at this `π`)
gives the finite residue field `l := O_L/𝔪_L ⊇ k̄ := O_k/𝔪_k`, both char 2.

**(R) The residue layer — the crux.**  Let `σ̄ : l → l` be the induced map (well-defined by
norm-preservation).  **Claim: `σ̄ ≠ id`.**  Suppose `σ̄ = id`.
1. *Teichmüller in `L`*: for a unit `w ∈ O_L`, the sequence `w^{qⁿ}` (`q := #l`) is Cauchy —
   `w^q ≡ w (mod 𝔪_L)` (Lagrange in `l`), and squaring at least deepens congruences by one
   (`x ≡ y (mod π^d) ⟹ x² ≡ y² (mod π^{d+1})`, char-2 binomial: `x² − y² = (x−y)(x+y)`,
   `‖x+y‖ ≤ max(‖2x‖, ‖x−y‖)`); `L` complete ⟹ `ω := lim w^{qⁿ} ∈ O_L` with `ω^{q−1} = 1`,
   `ω ≡ w (mod 𝔪_L)` (the `sq_of_near_one` Cauchy-iteration template, `cauchySeq_of_le_geometric`).
2. *Root separation*: distinct `m`-th roots of unity (`m := q − 1`, **odd**) satisfy
   `‖ζ − ζ'‖ = 1` — `∏_{ζ'' ≠ ζ}(ζ − ζ'') = m·ζ^{m−1}` (derivative of `X^m − 1`), of norm 1
   (`m` odd, 2-adic!), with every factor `≤ 1`, so every factor `= 1`
   (the `ResidueLift.exists_nthRoot_near` product technique, run in reverse).
3. So `σ̄ = id` forces `σω = ω` for every such Teichmüller unit (`σω` is an `m`-th root of
   unity in the same residue class), i.e. `ω ∈ L^σ = k` (coordinates: `σz = z ⟺ y = 0`), i.e.
   every residue of `l` lies in `k̄` — `l = k̄`.
4. *Successive approximation*: `l = k̄ ⟹ L = k` — every `z ∈ O_L` is a `π`-adic limit of
   partial sums with `O_k`-coefficients (lift residues, divide by `π`, recurse), and `k` is
   closed in `L` (finite-dimensional subspace); scale by `π^{−j}` for general `z ∈ L`.
   Contradiction with `δa ∉ k`.  ∎(Claim)

Consequently the **trace residue** `s̄ : l → l`, `z̄ ↦ z̄ + σ̄z̄`, is nonzero (char 2:
`s̄z̄ = 0 ⟺ σ̄z̄ = z̄`; pick `z̄` outside the fixed field), `l^{σ̄}`-linear with image inside
`l^{σ̄}`, hence **surjective onto `l^{σ̄}` ⊇ k̄** (a nonzero linear map onto a 1-dimensional
target).  *No finite-field Galois theory needed.*

**(A) The approximation engine.**  Given a norm-one unit `u`:
* *Start (depth 1)*: residues of `k̄` are squares (`x ↦ x²` is bijective on a finite char-2
  field — Frobenius); pick `x₀ ∈ O_k` with `u ≡ x₀² (mod 𝔪_k)`; then `w₀ := x₀` has
  `N(w₀) = x₀²` and `u/N(w₀) ∈ U^{(1)}_k`.
* *Increments (depth `n ≥ 1` → `n+1`)*: if `u/N(wₙ) = 1 + cπⁿ` (`c ∈ O_k`), choose `z₀ ∈ O_L`
  with `s̄(z̄₀) = c̄` (surjectivity of `s̄` onto `⊇ k̄`; note `σπ = π` makes the depth-`n` twist
  trivial: `s(π^n z₀) = π^n s(z₀)`).  Set `wₙ₊₁ := wₙ(1 + π^n z₀)`:
  `N(1 + π^n z₀) = 1 + π^n s(z₀) + π^{2n} N(z₀)`, so
  `u/N(wₙ₊₁) ∈ U^{(n+1)}_k` (`2n ≥ n+1`).  All `wₙ` stay norm-one.
* *Limit*: `‖wₙ₊₁ − wₙ‖ ≤ ‖π‖^n` ⟹ Cauchy ⟹ `w ∈ L` (complete); `N` is continuous
  (`σ` is a `k`-linear isometry on the finite-dimensional `L`); `N(wₙ) → u`
  (`‖N(wₙ) − u‖ ≤ ‖π‖^n`) ⟹ `N(w) = u`.  Extract coordinates `w = x + yδa` ⟹
  `u = x² − a y²` in `↥k` (coercion injective).  ∎

## 2. Verified ingredient inventory (2026-07-09)

| ingredient | status | note |
|---|---|---|
| `dyadicUnitFiltration'` at `k` and `L` | **B13 capstone** | the dependency; plain `∀ k` theorem, no baggage |
| `norm_galois` (σ-invariance of the spectral norm) | ✓ proved downstream | `HilbertLedger.lean:310–315` — **re-derive upstream** (3 lines: `NormedAlgebra.norm_eq_spectralNorm`, `spectralNorm_eq_of_equiv`) |
| `sq_of_near_one` Cauchy template (`cauchySeq_of_le_geometric`, limits in `↥·`) | ✓ pattern | `HilbertLedger.lean:46–50` — technique reuse, not import |
| `exists_nthRoot_near` product-of-root-distances technique | ✓ pattern | `ResidueLift.lean` (downstream; consumed B13 — mine the *technique*) |
| `IsAlgClosed.lift` + `Algebra.IsAlgebraic.algHom_bijective` (build σ) | ✓ probed | + minpoly-root embedding for `δa ↦ −δa` (recon pins the adjoin-lift name) |
| quadratic-adjoin coordinate API (`k⟮δa⟯`, basis `{1, δa}`) | ◐ | originals in `QuadraticAdjoin.lean` (downstream); `KummerSurjectivity.lean` re-proved pieces as `private` — **recon decides: re-port vs un-private vs fresh `adjoin.powerBasis`** |
| Frobenius bijective on finite char-2 fields | ◐ name | `frobeniusEquiv`/perfect-field route — recon pins |
| completeness/closedness of `L`, continuity of fin-dim linear maps | ✓ | `FiniteDimensional.complete`, `Submodule.closed…`, `LinearMap.continuous_of_finiteDimensional` |

## 3. File placement

* `GQ2/TeichmullerLift.lean` (NEW, lane A): imports `GQ2.UnitFiltrationCounts` (B13) + Mathlib —
  the **σ-free** bricks: Teichmüller units in a complete finite subextension (§1(R)1), odd-root
  separation (§1(R)2), successive approximation `l = k̄ ⟹ L = k`-shape lemma (§1(R)4, stated
  for a pair `k ≤ L` with a shared uniformizer).  Independently reusable.
* `GQ2/UnramifiedQuadraticNorms.lean` (NEW, lane B): imports `GQ2.TeichmullerLift` — quadratic
  layer (σ, coordinates, `N`, `s`, `norm_galois` port), the residue layer's σ̄-argument, the
  engine, the **capstone** `unramifiedQuadratic_units_are_norms'` (byte-exact statement).
* Both upstream of `Foundations/Axioms.lean` ⟹ zero-churn flip.  After this flip,
  `dyadicNormCriterion` rests on **B11a alone**.

## 4. Increments

### B11b-0 — recon (O, ½ session)
Pin: the adjoin/minpoly-embedding names for σ (`IntermediateField.adjoin` power basis /
`minpoly` root-lift / `IsAlgClosed.lift` composition — prototype the full σ construction in
`lean_run_code`); the coordinate-API decision (§2 row 6 — likely smallest: fresh
`adjoin.powerBasis`-based coordinates in lane B, ~40 lines); Frobenius-bijective name;
`Fintype/Nat.card` glue at `l`.  **Go/no-go on the σ prototype.**

### B11b-1 — quadratic layer (O, 1 session; lane B)
`L`, `k ≤ L`, `FiniteDimensional ℚ_[2] L`, basis/coordinates, σ (global lift, restriction
facts, `σ|k = id`, `σδa = −δa`, `σ² = id` on `L`, fixed points = `k`), `norm_galois` port,
`N`/`s` with `N(x+yδa) = x² − ay²`, the degenerate case (D).

### B11b-2 — residue layer (F→O, 1–1½ sessions; lane A then B; **the risk pocket**)
Lane A (σ-free, can run ∥ B11b-1): Teichmüller limit (§1(R)1), root separation (§1(R)2),
approximation lemma (§1(R)4).  Then (needs σ): `σ̄` well-defined, the `σ̄ = id ⟹ L = k`
contradiction (§1(R)3), `s̄ ≠ 0`, `s̄` surjective onto `⊇ k̄`.
*F-escalation triggers*: the Teichmüller Cauchy bookkeeping fights for > ½ session (junk-value
or filter friction — the `sq_of_near_one` template should prevent it), or the fixed-field step
(`σz = z ⟺ y = 0` at residue level) turns out to need more than coordinates.

### B11b-3 — approximation engine (O, 1 session; lane B; **gated on B13 capstone**)
π-transfer via `hunram` (trivial, §1(F)); filtration instances at `k`, `L`; the depth-1 start
(Frobenius square); the increment step; the Cauchy limit; `N`-continuity; coordinate extraction.

### B11b-4 — capstone (O, ½–¾ session; lane B)
`unramifiedQuadratic_units_are_norms'` with the **byte-exact** axiom statement (unpack
`IsUnramifiedQuadraticSpectral`, wire (D) ∨ (Q–A)); `lean_verify` = std-3.

### B11b-5 — census flip (O, ½ session + coordination; **user-approval gate**)
The B7′-5b pattern: same-name theorem in `Axioms.lean` (import the capstone file);
`EXPECTED_AXIOMS` −1 + history; `AxiomLedger.bAxioms`; docs rows + census notes (note
`dyadicNormCriterion` now rests on B11a alone); regenerate `atlas-audit.md`; spot
`lean_verify` on consumers (`SectionSix.lemma_6_16`, `VanishClose.lemma_6_17_vanish_final`,
`dyadicNormCriterion` — B11b must vanish, B11a must remain); archive board + plan.

## 5. Risks

* **σ construction** (B11b-1): instance-heavy `AlgHom` lifting through `IsAlgClosed.lift` at
  an `IntermediateField` — the recon prototype de-risks or F-escalates *before* lane work.
* **The residue crux** (B11b-2): the argument is fully designed above but is genuinely novel
  formal work (no Mathlib unramifiedness theory is being borrowed); the three σ-free bricks
  are independently testable, which contains the blast radius.
* **Coordinate non-integrality**: elements of `O_L` can have non-integral `k`-coordinates
  (e.g. `(−1+√−3)/2`); the engine deliberately never takes coordinates of `O_L`-elements —
  only of the final limit `w ∈ L` (where integrality is irrelevant).  Keep it that way.
* **Depth arithmetic** in the increment (`2n ≥ n+1`, cross terms) — routine but easy to
  off-by-one; state the increment lemma with explicit `‖·‖ ≤ ‖π‖^{n+1}` conclusions.
* `q − 1` odd ⟹ norm-1 derivative — uses `#l = 2^F` from B13 at `L`; keep `m := 2^F − 1`
  literal to make oddness a one-liner.

## 6. Out of scope

B11a (`hilbertSymbol_normCriterion_finiteDyadic` — cohomological cup-pairing content, a
different class of discharge); any general `Algebra.norm`/`Valued` bridge (the norm form *is*
the interface); ramification theory beyond what §1(F) extracts from `hunram`.
