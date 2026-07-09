# B13 discharge — ticket board  (prove `dyadicUnitFiltration`, census −1)

**Status (2026-07-09): planned, not started — B13-0 is ready to run.**  Design fixed during the
planning session (Fable pass, this board + [`b13-proof-plan.md`](b13-proof-plan.md)): the
compactness + `O/2O`-pigeonhole route to the uniformizer (**no spectral-norm value formula
anywhere**), explicit graded isomorphisms for the counts, and the four Mathlib pillars
(`ProperSpace ℚ_[2]` instance, `FiniteDimensional.proper/complete`,
`AddSubgroup.quotient_finite_of_isOpen`, finite-field card lemmas) probed green in
`lean_run_code`.  Census is **12**; **B13-5 decrements it, gated on explicit user approval.**

Conventions as on [`tickets.md`](tickets.md) — **Model**: **F** = Fable (design-heavy), **O** =
Opus (well-specified), **F→O** = Fable design then Opus close.  **Gates for every ticket**:
own-file `lake build`; `lean_verify` = exactly `{propext, Classical.choice, Quot.sound}` on
every new declaration; `scripts/check_axioms.sh` (census stays 12 until B13-5); stage only your
own files and print the staged set.  Development in **two new files** —
`GQ2/UnitFiltrationTop.lean` (lane A), `GQ2/UnitFiltrationCounts.lean` (lane B) — one lane per
file (merge-safety, `docs/orchestration/b7prime-b34-coordination.md` precedent); **do not edit**
`GQ2/UnitFiltration.lean` (shared: `Foundations/Axioms.lean` imports it).

| # | St | Model | Ticket | Est. | Deps |
|---|----|-------|--------|------|------|
| B13-0 | ⬜ | O | Recon: instance incantations at `↥k`, card-lemma forms, ball-compactness path | ¼ | — |
| B13-1 | ⬜ | O | Topology layer: instances, ball subring `O`, open balls, `O/2O` finite | ½–1 | B13-0 |
| B13-2 | ⬜ | O | Uniformizer: gap pigeonhole + attainment + `hπ_max`, `he`, `𝔪 = πO` | ½–1 | B13-1 |
| B13-3 | ⬜ | O | Residue field `O/𝔪`: finite, field, char 2, `2^f` (hypothesis-π form ok) | ½ | B13-1 (∥ B13-2 vs interface) |
| B13-4 | ⬜ | O | Graded isomorphisms + the two `Nat.card` counts | 1 | B13-2 ∧ B13-3 |
| B13-5 | ⬜ | O | Capstone `dyadicUnitFiltration'` + census flip (**user gate**) | ½ | B13-4 |

Est. in lane-sessions.  Limited parallelism: **B13-3 ∥ B13-2** if lane B states its layer over
a hypothesis-`π` (`hπ_max` as an assumption) and instantiates later.  Total ≈
**3–4 lane-sessions**.

---

## B13-0 — recon  (O, ¼ session)

Pin, `lean_run_code`-verified, and record here in turnkey form (the B7′-0 style):

1. ✓ **RESOLVED at planning time** (2026-07-09 probe, all green in one `lean_run_code` pass):
   `NormedField ↥k := inferInstance`; `CompleteSpace ↥k := FiniteDimensional.complete ℚ_[2] ↥k`;
   `ProperSpace ↥k := FiniteDimensional.proper ℚ_[2] ↥k` (synthesizes directly at the
   `IntermediateField` subtype); `‖x‖ = ‖(x : ℚ̄₂)‖` by `rfl`; `IsUltrametricDist ↥k`
   by `inferInstance`; and `IsCompact {x : ↥k | ‖x‖ ≤ 1}` via
   `isCompact_closedBall (0 : ↥k) 1` + `simpa [Metric.closedBall, dist_zero_right]`.
   No fallback needed.
2. `Fintype` vs `Finite`/`Nat.card` forms of `FiniteField.card` and `Fintype.card_units`
   (the structure's fields are `Nat.card`).
3. The open-subgroup finite-quotient form to use for `O/2O` (`AddSubgroup.quotient_finite_of_isOpen`
   needs `CompactSpace` on the ambient — phrase `O` as the ambient compact group, `2O` as an
   `AddSubgroup ↥O`-style subgroup, or use the `subgroupOf` form; decide and record).
4. The `Multiplicative (O/𝔪)`-target idiom for B13-4's additive-quotient hom.

## B13-1 — topology layer  (O, ½–1 session; lane A, `GQ2/UnitFiltrationTop.lean`)

Instances (per B13-0.1); `O : Subring ↥k` (ultrametric ball — the `depthUnits` subgroup proofs
in `UnitFiltration.lean` are the template); compactness of `O`; balls `{‖x‖ ≤ r}` are open
additive subgroups; `Finite (O ⧸ 2O)`-form + `M := Nat.card (O ⧸ 2O)`.

## B13-2 — uniformizer + normalization  (O, ½–1 session; lane A)

Plan §1(U)/(E): the **gap lemma** — among `1, x, …, x^M` two agree mod `2O` ⟹
`‖x‖^i ≤ ‖2‖` with `1 ≤ i ≤ M` (the `i = 0` case contradicts `‖1 − x^j‖ = 1`); keep the
conclusion in the power form `‖x‖ ^ M ≤ ‖2‖` (no `rpow`).  Attainment on
`K = {‖2‖ ≤ ‖x‖ ≤ …}` via `IsCompact.exists_isMaxOn` ⟹ `π`, `hπ_ne/lt/max`.  `e` maximal with
`‖π‖^e ≥ ‖2‖` (`Nat.find` on the complement; `e ≥ 1` from `‖π‖ ≥ ‖2‖` at `x = 2`); the
`2/π^e`-unit argument ⟹ `he`.  The **exchange** `‖x‖ < 1 ⟺ ‖x‖ ≤ ‖π‖` and `𝔪 = πO`.

## B13-3 — residue field  (O, ½ session; lane B, `GQ2/UnitFiltrationCounts.lean`)

Plan §1(R), stated over hypothesis-`π` (`hπ_max` assumption) if lane A is in flight:
`O/𝔪` finite (`𝔪` open in compact `O`), domain (norm multiplicativity), field
(`Finite.isField_of_domain`), char 2 (`2 ∈ 𝔪`), `#(O/𝔪) = 2^f` with `f ≥ 1`
(`FiniteField.card`; `1 ∉ 𝔪`), `#(O/𝔪)ˣ = 2^f − 1` (`Fintype.card_units`).

## B13-4 — graded isomorphisms + counts  (O, 1 session; lane B)

Plan §1(G).  Two homs with kernel + surjectivity, then `Nat.card` transport
(`QuotientGroup.quotientKerEquivOfSurjective` + `Nat.card_congr`, the B12-1 idiom) to the
**exact** `DyadicUnitFiltration`-field shapes
(`Nat.card (↥(normUnits k) ⧸ (depthUnits k π 1).subgroupOf (normUnits k))` etc.):

- `U⁰ →* (O/𝔪)ˣ`, `u ↦ ū`; kernel `U¹`; surjective via the exchange (`a ∈ O ∖ 𝔪 ⟹ ‖a‖ = 1`).
- `U^{(i)} →* Multiplicative (O/𝔪)` (`i ≥ 1`), `u ↦ ((u−1)/π^i)‾`; hom law via the cross-term
  depth `2i ≥ i+1`; kernel `U^{(i+1)}`; surjective via `u := 1 + aπ^i`.

## B13-5 — capstone + census flip  (O, ½ session + coordination; **user-approval gate**)

`theorem dyadicUnitFiltration' (k) [FiniteDimensional ℚ_[2] k] : DyadicUnitFiltration k` —
a plain public theorem (**B11b consumes it at `k` and at `L = k(δa)`** — no `private`, no
`k`-specific baggage); `lean_verify` = std-3.  Then the flip (B7′-5b pattern): `Axioms.lean`
axiom → same-name theorem (+ import); `EXPECTED_AXIOMS` −1 + history note;
`AxiomLedger.bAxioms` row; `literature-axioms.md` B13 row → discharged (keep the Serre LF IV §2
Prop. 6 citation), onepage, `tickets.md` census notes; regenerate `atlas-audit.md`; spot
`lean_verify` on B13 consumers (`ResidueLift.exists_rootOfUnity_near`,
`DimClose.lemma_6_17_dim_of_residueLift`: B13 vanishes, nothing else changes); archive this
board + plan to `docs/orchestration/`.  Quiet tree; coordinate with any active B11b lane
(B11b needs only the capstone, not the flip).
