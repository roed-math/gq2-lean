# B13 discharge plan: prove `dyadicUnitFiltration` (census −1)

**Goal.**  Replace the axiom (`Foundations/Axioms.lean`, namespace `GQ2`)

```lean
axiom dyadicUnitFiltration (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] k] :
    DyadicUnitFiltration k
```

by a proof — the local structure theory of a finite extension `k/ℚ₂` in the repo's
spectral-norm vocabulary (Serre, *Local Fields*, Ch. IV §2 Prop. 6 + Ch. I–II discreteness;
`DyadicUnitFiltration` structure in `GQ2/UnitFiltration.lean`: a **uniformizer** `π` with the
max-norm property, the `‖2‖ = ‖π‖^e` **normalization**, and the **graded counts**
`#(U⁰/U¹) = 2^f − 1`, `#(U^i/U^{i+1}) = 2^f`).  Everything is std-3 (topology + finite
pigeonholes; **no** B-axioms, no `native_decide`).

**Estimated effort**: **3–4 lane-sessions** (recon ¼ · topology ½–1 · uniformizer ½–1 ·
residue+counts 1–1½ · assembly+flip ½).  Board: [`b13-tickets.md`](b13-tickets.md).

**Design headline (B13-0 recon result, 2026-07-09, probes verified in `lean_run_code`):**
no spectral-norm *value formula* is needed anywhere.  Discreteness of the value group comes
from **compactness + a pigeonhole on `O/2O`**, and the residue counts from **explicit graded
isomorphisms** — all elementary ultrametric algebra over four Mathlib pillars, each confirmed
present in the pinned revision:

* `ProperSpace ℚ_[2]` — an **instance** (`inferInstance` closes it);
* `FiniteDimensional.proper 𝕜 E` (`[LocallyCompactSpace 𝕜]`) and `FiniteDimensional.complete`
  — so `↥k` is a proper, complete normed `ℚ₂`-space;
* `AddSubgroup.quotient_finite_of_isOpen` — open subgroup of a compact group has finite
  quotient;
* `Finite.isField_of_domain`, `FiniteField.card`, `Fintype.card_units` — finite-field
  arithmetic for the counts.

The `NormedField ↥k`-restricts-`ℚ̄₂` (`rfl`) + `CompleteSpace ↥k := FiniteDimensional.complete`
incantations are already exercised at `GQ2/HilbertLedger.lean:49` (`sq_of_near_one`).

## 0. Shared-tree constraints

* Development in **two new files** (`GQ2/UnitFiltrationTop.lean`, `GQ2/UnitFiltrationCounts.lean`
  — the merge-safe one-file-per-lane convention, `docs/orchestration/b7prime-b34-coordination.md`
  precedent); **do not edit** `GQ2/UnitFiltration.lean` (shared: imported by
  `Foundations/Axioms.lean`), `Foundations/Axioms.lean`, `check_axioms.sh`, `AxiomLedger.lean`
  until the flip (B13-5, **user-approval gate**).
* Census is **12**; stays 12 until B13-5 decrements it.  Standard gates per increment: own-file
  `lake build`; `lean_verify` = std-3 exactly on every new declaration; `scripts/check_axioms.sh`;
  stage only own files, print the staged set.
* `GQ2.lean` registration: one import line per new file, added by the lane that owns the file.

## 1. Mathematical route

Fix `k` with `[k : ℚ₂] < ∞`, inside `ℚ̄₂` with Mathlib's spectral-norm `NormedField` structure
(multiplicative, ultrametric — `IsUltrametricDist` is already used by `UnitFiltration.lean`).

**(T) Topology.**  `↥k` is a finite-dimensional normed `ℚ₂`-space, hence **complete**
(`FiniteDimensional.complete`) and **proper** (`FiniteDimensional.proper`, `ℚ₂` locally compact
via `PadicInt.compactSpace`).  The unit ball `O := {x ∈ k : ‖x‖ ≤ 1}` is a subring (ultrametric),
closed and bounded, hence **compact**; the balls `2O = {‖x‖ ≤ ‖2‖}` and (later) `{‖x‖ ≤ ‖π‖}`
are **open** additive subgroups (ultrametric: closed balls are open).  So `O/2O` is **finite**
(`AddSubgroup.quotient_finite_of_isOpen`), say `#(O/2O) = M`.

**(U) Uniformizer via pigeonhole.**  *Gap lemma:* for every `x ∈ k` with `‖x‖ < 1`,
`‖x‖ ≤ ‖2‖^{1/M}` — among `1, x, x², …, x^M` two agree mod `2O` (pigeonhole), say
`x^i ≡ x^j (mod 2O)`, `i < j`; then `x^i(1 − x^{j−i}) ∈ 2O` with `‖1 − x^{j−i}‖ = 1`
(ultrametric, `‖x^{j−i}‖ < 1`), so `‖x‖^i ≤ ‖2‖`; and `i ≥ 1` because `i = 0` would put
`1 − x^j ∈ 2O`, i.e. `1 ≤ ‖2‖`.  Hence `‖x‖ ≤ ‖2‖^{1/i} ≤ ‖2‖^{1/M}`.  *Attainment:* the set
`K = {x ∈ k : ‖2‖ ≤ ‖x‖ ≤ ‖2‖^{1/M}}` is compact (closed bounded in proper `↥k`), nonempty
(`2 ∈ K`), and contains every norm in `(‖2‖^{1/M}, 1)`… none exist; the sup of norms over the
punctured ball is attained on `K` (`IsCompact.exists_isMaxOn`, norm continuous).  The maximizer
`π` satisfies `π ≠ 0`, `‖π‖ < 1`, and `hπ_max : ∀ x ∈ k, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖`.

**(E) Normalization.**  Let `e := max {j : ‖π‖^j ≥ ‖2‖}` (finite: `‖π‖^j → 0`; `e ≥ 1` since
`‖π‖ ≥ ‖2‖^{... } > ‖2‖`… directly: `‖π‖ ≥ ‖2‖` by maximality at `x = 2`).  Then `x := 2/π^e ∈ k`
has `‖x‖ ≤ 1`; if `‖x‖ < 1` then `‖x‖ ≤ ‖π‖` (max property) forces `‖2‖ ≤ ‖π‖^{e+1}`,
contradicting maximality of `e`; so `‖x‖ = 1` and `‖2‖ = ‖π‖^e`.  *(Only `hπ_max` is used — no
value-group cyclicity needed.)*

**(R) Residue field.**  `𝔪 := {x ∈ O : ‖x‖ ≤ ‖π‖}`.  Key exchange, used everywhere below:
`‖x‖ < 1 ⟺ ‖x‖ ≤ ‖π‖` (max property) — so `𝔪 = {‖x‖ < 1}`, and `𝔪 = πO` (`x/π ∈ O`).  `O/𝔪`
is a **finite** (`𝔪` open in compact `O`) **commutative ring**, an **integral domain**
(`‖xy‖ = ‖x‖‖y‖ < 1 ⟹` a factor is `< 1`), hence a **field** (`Finite.isField_of_domain`),
of **characteristic 2** (`2 ∈ 𝔪`: `‖2‖ < 1`); so `#(O/𝔪) = 2^f` (`FiniteField.card`) with
`f ≥ 1` (`0 ≠ 1` in `O/𝔪` since `1 ∉ 𝔪`).

**(G) Graded counts.**  Two explicit group homomorphisms with kernel/surjectivity checks:

* `U⁰ = normUnits k → (O/𝔪)ˣ`, `u ↦ ū` (well-defined: `‖u‖ = 1 ⟹ ū ≠ 0`, invertible in a
  field).  Kernel `= U¹` (`ū = 1̄ ⟺ ‖u − 1‖ ≤ ‖π‖`); **surjective** (`ā ≠ 0` lifts to `a ∈ O∖𝔪`,
  which has `‖a‖ = 1` by the exchange, hence is a norm-one unit).  So
  `U⁰/U¹ ≃ (O/𝔪)ˣ`, of card `2^f − 1` (`Fintype.card_units`).
* For `i ≥ 1`: `U^{(i)} → (O/𝔪, +)` (as `→* Multiplicative (O/𝔪)`), `u ↦ ((u−1)/π^i)‾`
  (in `O`: `‖u−1‖ ≤ ‖π‖^i`).  Homomorphism: `(uv−1) = (u−1) + (v−1) + (u−1)(v−1)` and the cross
  term has norm `≤ ‖π‖^{2i}`, so `/π^i` puts it in `𝔪` (`i ≥ 1`).  Kernel `= U^{(i+1)}`
  (`(u−1)/π^i ∈ 𝔪 ⟺ ‖u−1‖ ≤ ‖π‖^{i+1}`); **surjective** (`ā` lifts to `u := 1 + aπ^i`, a
  norm-one unit by the ultrametric).  So `U^{(i)}/U^{(i+1)} ≃ (O/𝔪, +)`, of card `2^f`.

Both quotients are transported to the structure's `Nat.card (… ⧸ (…).subgroupOf …)` shape by
`QuotientGroup.quotientKerEquivOfSurjective` + `Nat.card_congr` (the B12-1 hom/kernel idiom).  ∎

## 2. Verified ingredient inventory (2026-07-09, probes green)

| ingredient | status | note |
|---|---|---|
| `NormedField ℚ̄₂` (spectral), mult. + `IsUltrametricDist` | ✓ in use | `UnitFiltration.lean`, `SectionSix.lean:47` |
| `NormedField ↥k` restricting `ℚ̄₂`'s (`rfl`), `CompleteSpace ↥k` | ✓ pattern | `HilbertLedger.lean:49` (downstream — **re-derive upstream**, few lines) |
| `PadicInt.compactSpace`, `ProperSpace ℚ_[2]` (instance) | ✓ probed | |
| `FiniteDimensional.proper`, `FiniteDimensional.complete` | ✓ probed | needs `LocallyCompactSpace ℚ_[2]` ✓ (proper ⟹) |
| `AddSubgroup.quotient_finite_of_isOpen` | ✓ probed | compact + open subgroup |
| `IsCompact.exists_isMaxOn` | ✓ probed | attainment |
| `Finite.isField_of_domain`, `FiniteField.card`, `Fintype.card_units` | ✓ probed | counts (`Fintype` vs `Nat.card` glue: recon) |
| ultrametric ball-subgroup lemmas | ✓ house style | `depthUnits` proofs in `UnitFiltration.lean` are the template |
| quotient-count plumbing (`quotientKerEquivOfSurjective`, `subgroupOf`) | ✓ precedent | B12-1/B12-3 idiom |

Residual pins for B13-0 (¼ session): the exact instance path for `NormedField ↥k` /
`ProperSpace ↥k` at `IntermediateField` subtypes (vs `Subfield`; `SubfieldClass` instances);
`Fintype` vs `Finite`/`Nat.card` forms of the two card lemmas; whether balls-in-`↥k` compactness
is smoothest via `ProperSpace ↥k` or via `Metric.isCompact_of_isClosed_isBounded`; the
`Multiplicative (O/𝔪)` hom-target idiom.

## 3. File placement

* `GQ2/UnitFiltrationTop.lean` (NEW, lane A): imports `GQ2.UnitFiltration` + Mathlib —
  instances on `↥k`, the ball subring `O`, openness/compactness, `O/2O` finite, the gap lemma,
  uniformizer `π` + `hπ_max`, the `he` normalization, `𝔪 = πO`.
* `GQ2/UnitFiltrationCounts.lean` (NEW, lane B): imports `GQ2.UnitFiltrationTop` — residue
  field `O/𝔪` (finite, field, char 2, `2^f`), the two graded isomorphisms, the `Nat.card`
  counts, and the **capstone**
  `theorem dyadicUnitFiltration' (k) [FiniteDimensional ℚ_[2] k] : DyadicUnitFiltration k`.
* Both strictly upstream of `Foundations/Axioms.lean` (`UnitFiltration` imports `EvensKahn`,
  already upstream) ⟹ the flip is the B11/B12/B7′ zero-churn pattern.
* **Statement shape note**: the capstone is a plain `theorem` over every finite `k` — the B11b
  lane (see `b11b-proof-plan.md`) invokes it at **both** `k` and the quadratic extension
  `L = k(δa)`, so it must NOT be `private` and must carry no `k`-specific baggage.

## 4. Increments

### B13-0 — recon (O, ¼ session)
The §2 residual pins, `lean_run_code`-verified; write the exact instance incantations into the
board (the B7′-0 turnkey style).

### B13-1 — topology layer (O, ½–1 session; lane A)
`NormedField ↥k`/`CompleteSpace`/`ProperSpace ↥k` instances (or ball-compactness directly);
`O` as a `Subring ↥k` with compact carrier; `2O` and `π`-balls as open additive subgroups;
`Finite (O ⧸ 2O)`-form pigeonhole input.  Deliverable interface: `M`, `card_O_mod_two` +
ball-topology lemmas.

### B13-2 — uniformizer + normalization (O, ½–1 session; lane A)
Gap lemma (`‖x‖ ≤ ‖2‖^{1/M}` on the open punctured ball — phrase as
`‖x‖ ^ M ≤ ‖2‖` to stay in `ℝ`-friendly algebra); attainment (`IsCompact.exists_isMaxOn`);
`π`, `hπ_ne/lt/max`; `e` by `Nat.find`-style maximality, `he`, `he_pos`; the exchange
`‖x‖ < 1 ⟺ ‖x‖ ≤ ‖π‖`; `𝔪 = πO`.

### B13-3 — residue field (O, ½ session; lane B, against lane A's interface)
`O/𝔪` finite + domain + field + char 2; `f`, `hf_pos`, `#(O/𝔪) = 2^f`, `#(O/𝔪)ˣ = 2^f − 1`.
Can start against *hypothesis-π* (`hπ_max` as an assumption) if lane A is still in flight.

### B13-4 — graded isomorphisms + counts (O, 1 session; lane B)
The two homs of §1(G): well-definedness, hom law, kernel, surjectivity; quotient equivs;
`Nat.card` transport to the exact `DyadicUnitFiltration`-field shapes (mind the
`(depthUnits k π (i+1)).subgroupOf (depthUnits k π i)` form).

### B13-5 — assembly + census flip (O, ½ session + coordination; **user-approval gate**)
Capstone `dyadicUnitFiltration'` assembling all fields; `lean_verify` = std-3.  Flip (B7′-5b
pattern): `Axioms.lean` axiom → same-name theorem (import `GQ2.UnitFiltrationCounts`);
`EXPECTED_AXIOMS` −1 + history; `AxiomLedger.bAxioms` row; docs
(`literature-axioms.md` B13 → discharged, onepage, `tickets.md` census); regenerate
`atlas-audit.md`; spot `lean_verify` on B13 consumers (`ResidueLift.exists_rootOfUnity_near`,
`DimClose.lemma_6_17_dim_of_residueLift` — B13 must vanish, nothing else may change); archive
this board + plan to `docs/orchestration/`.

## 5. Risks

* **Instance-shape friction** at `↥k` (`IntermediateField` subtype vs `Subfield` instances;
  `ProperSpace` synthesis) — the one place recon must be careful; fallback: transport
  compactness through an explicit `≃L[ℚ₂] (Fin d → ℚ₂)` (fin-dim, both directions continuous).
* **`Nat.card` plumbing** through `subgroupOf`-quotients — familiar from B12; mechanical but
  fiddly; the `Multiplicative` wrapper for the additive target.
* The **gap-lemma exponent algebra** (`‖x‖^i ≤ ‖2‖`, `1 ≤ i ≤ M` ⟹ bound) — real-number
  monotonicity bookkeeping; keep it in the `‖x‖^M ≤ ‖2‖`-form to avoid `rpow`.
* No mathematical risk pockets: every step above is verified elementary ultrametric algebra.

## 6. Out of scope

B11b (its own plan, `b11b-proof-plan.md` — **consumes this lane's capstone at `k` and `L`**);
any `e·f = [k:ℚ₂]` refinement (not in the axiom); valuation-ring/`Valued` re-foundations
(deliberately avoided — the repo vocabulary is the norm); B11a (cohomological, separate class).
