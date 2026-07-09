# B13 discharge — ticket board  (prove `dyadicUnitFiltration`, census −1)

**Status (2026-07-09): B13-0 ☑ done — B13-1 ready to start.**  Design fixed during the
planning session (Fable pass, this board + [`b13-proof-plan.md`](b13-proof-plan.md)): the
compactness + `O/2O`-pigeonhole route to the uniformizer (**no spectral-norm value formula
anywhere**), explicit graded isomorphisms for the counts, and the four Mathlib pillars
(`ProperSpace ℚ_[2]` instance, `FiniteDimensional.proper/complete`,
`AddSubgroup.quotient_finite_of_isOpen`, finite-field card lemmas) probed green in
`lean_run_code`.  **B13-0 recon adds the route-shortening find
`IsUltrametricDist.closedBall_openAddSubgroup`** (ball = bundled `OpenAddSubgroup`) and turnkey
closers for all four pins (§B13-0).  Census is **12**; **B13-5 decrements it, gated on explicit
user approval.**

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
| B13-0 | ☑ 07-09 | O | Recon: instance incantations at `↥k`, card-lemma forms, ball-compactness path | ¼ | — |
| B13-1 | ☑ 07-09 | O | Topology layer: `unitBall`/`dyadicBall`, `O/2O` finite, pigeonhole (`UnitFiltrationTop.lean`) | ½–1 | B13-0 |
| B13-2 | ☑ 07-09 | O | Uniformizer: gap + attainment + `hπ_max` + `he` (`UnitFiltrationTop.lean`) | ½–1 | B13-1 |
| B13-3 | ☑ 07-09 | O | Residue field `O/𝔪`: finite, field, char 2, `2^f` (hypothesis-π form ok) | ½ | B13-1 (∥ B13-2 vs interface) |
| B13-4 | ☑ 07-09 | O | Graded isomorphisms + the two `Nat.card` counts (`UnitFiltrationCounts.lean`) | 1 | B13-2 ∧ B13-3 |
| B13-5 | ⬜ | O | Capstone `dyadicUnitFiltration'` + census flip (**user gate**) | ½ | B13-4 |

Est. in lane-sessions.  Limited parallelism: **B13-3 ∥ B13-2** if lane B states its layer over
a hypothesis-`π` (`hπ_max` as an assumption) and instantiates later.  Total ≈
**3–4 lane-sessions**.

---

## B13-0 — recon  ☑ DONE 2026-07-09 (commit below; all four pins turnkey, `lean_run_code`-green)

**Go/no-go: GO — no surprises, and one route-shortening find.**  Turnkey closers below.  The
headline: **`IsUltrametricDist.closedBall_openAddSubgroup`** (`Mathlib.Analysis.Normed.Group.Ultra`)
gives the closed ball *directly* as a bundled `OpenAddSubgroup ↥k` — the plan's separate
"ball subgroup + prove-it-open" story collapses to one term, shrinking B13-1.

1. ✓ **Instances** (planning probe): `NormedField ↥k := inferInstance`;
   `CompleteSpace ↥k := FiniteDimensional.complete ℚ_[2] ↥k`;
   `ProperSpace ↥k := FiniteDimensional.proper ℚ_[2] ↥k` (direct at the `IntermediateField`
   subtype); `‖x‖ = ‖(x : ℚ̄₂)‖` by `rfl`; `IsUltrametricDist ↥k := inferInstance`;
   unit ball compact via `isCompact_closedBall (0 : ↥k) 1`.  No fallback needed.
2. ✓ **Card forms.**  `FiniteField.card F 2 : ∃ n : ℕ+, Nat.Prime 2 ∧ Fintype.card F = 2 ^ ↑n`
   — so `f := ↑n` with `1 ≤ f` free from `n.2`; bridge `Fintype F := Fintype.ofFinite F` and
   `Nat.card_eq_fintype_card`; units by `Fintype.card_units` (`Nat.card Fˣ = 2^f − 1`).  Verified:
   `[Field F] [Finite F] [CharP F 2] ⟹ ∃ f, 1 ≤ f ∧ Nat.card F = 2^f ∧ Nat.card Fˣ = 2^f − 1`.
3. ✓ **`O/2O` finite** (the crux — full assembly green):
   ```lean
   open IsUltrametricDist Metric
   noncomputable def Oball : OpenAddSubgroup ↥k := closedBall_openAddSubgroup ↥k (r := 1) one_pos
   noncomputable def twoOball : OpenAddSubgroup ↥k :=
     closedBall_openAddSubgroup ↥k (r := ‖(2 : ℚ̄₂)‖) (norm_pos_iff.mpr two_ne_zero)
   -- membership is `rfl`-level:  x ∈ (Oball k).toAddSubgroup ↔ ‖x‖ ≤ 1   := mem_closedBall_zero_iff
   -- CompactSpace ↥(Oball k).toAddSubgroup :
   --   isCompact_iff_compactSpace.mp (by rw [(rfl : ↑(Oball k).toAddSubgroup = closedBall 0 1)];
   --                                     exact isCompact_closedBall 0 1)
   -- Finite (↥(Oball k).toAddSubgroup ⧸ (twoOball k).toAddSubgroup.addSubgroupOf (Oball k).toAddSubgroup) :
   --   AddSubgroup.quotient_finite_of_isOpen _
   --     (continuous_subtype_val.isOpen_preimage _ (twoOball k).isOpen)
   ```
   **Name pins**: additive `subgroupOf` is **`AddSubgroup.addSubgroupOf`**; radius positivity
   `norm_pos_iff.mpr two_ne_zero`; membership `Metric.mem_closedBall_zero_iff`.
4. ✓ **Residue + counts idioms.**  Unit ball as a ring: `Osub : Subring ↥k`, carrier `{‖x‖ ≤ 1}`,
   `mul_mem'` by `mul_le_one₀ hx (norm_nonneg _) hy` (+ the `IsUltrametricDist.norm_add_le_max`
   `add_mem'` from `depthUnits`).  Endpoint `Finite.isField_of_domain S` (`[Finite] [IsDomain]`).
   `Nat.card` quotient plumbing (B13-4): `Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
   f hf).toEquiv` after rewriting the `addSubgroupOf`-subgroup to `f.ker`.  Additive graded hom to
   `Multiplicative (O/𝔪)`: `{ toFun := fun g => Multiplicative.ofAdd (φ g), map_one' := by simp […],
   map_mul' := fun x y => by simp [hm, ofAdd_add] }`.

*Model note*: O — done; the route is fully de-risked.  B13-1's deliverable interface is just
`Oball`/`twoOball` (above) + `M := Nat.card (↥O ⧸ (2O).addSubgroupOf O)`; the `Subring Osub`
and `𝔪`-ideal move to B13-3 (they carry the multiplicative structure the counts need).

## B13-1 — topology layer  ☑ DONE 2026-07-09 (commit below; `GQ2/UnitFiltrationTop.lean`, registered)

**Landed** (all std-3, `lean_verify` on `exists_pow_sub_dyadic` = std-3, full `lake build GQ2` green):
`unitBall`/`dyadicBall : OpenAddSubgroup ↥k` (off `closedBall_openAddSubgroup`), `@[simp]`
`mem_unitBall`/`mem_dyadicBall`, `unitBall_pow_mem`, the `CompactSpace ↥(unitBall k).toAddSubgroup`
and `Finite (↥O ⧸ (dyadicBall).addSubgroupOf (unitBall))` instances, and the deliverable pigeonhole

```lean
theorem exists_pow_sub_dyadic {x : ↥k} (hx : ‖x‖ ≤ 1) :
    ∃ i j : ℕ, i < j ∧ ‖x ^ i - x ^ j‖ ≤ ‖(2 : ℚ̄₂)‖
```

(`Fintype.exists_ne_map_eq_of_card_lt` on `i ↦ ⟦xⁱ⟧ ∈ O/2O`; `QuotientAddGroup.eq_iff_sub_mem` +
`AddSubgroup.mem_addSubgroupOf` extract the ball membership; `norm_sub_rev` handles the WLOG).

**For B13-2**: call `exists_pow_sub_dyadic` (with `‖x‖ ≤ 1` from `‖x‖ < 1`), then factor
`xⁱ − xʲ = xⁱ(1 − xʲ⁻ⁱ)`: for `‖x‖ < 1`, `‖1 − xʲ⁻ⁱ‖ = 1` (ultrametric), so `‖x‖ⁱ ≤ ‖2‖`, and
`i = 0` is impossible (`‖1 − x^{j}‖ = 1 > ‖2‖`) ⟹ `i ≥ 1`.  `M` was folded into the pigeonhole
(internal `Fintype.card`), not exported.  The unit-ball `Subring Osub` + residue field are B13-3.

## B13-2 — uniformizer + normalization  ☑ DONE 2026-07-09 (commit `c354b1f`; `UnitFiltrationTop.lean`)

**Landed** (all std-3, `check_axioms` green, own-file + B13-3-rebuild green).  Appended to lane A's
`UnitFiltrationTop.lean`:

* **`norm_two_lt_one`** `‖(2:ℚ̄₂)‖ < 1` — `spectralNorm_extends` (spectral norm extends the base
  norm) + `Padic.norm_p` (`‖2‖_{ℚ₂} = 2⁻¹`).  The load-bearing fact.
* **`dyadicIndex k := #(O/2O)`**, `one_le_dyadicIndex`, and `exists_pow_sub_dyadic` refined to
  expose `j ≤ dyadicIndex k` (the raw B13-1 pigeonhole folded into the bounded form).
* **`uniform_gap`** `‖x‖ < 1 → ‖x‖ ^ dyadicIndex k ≤ ‖2‖` (power form, **no `rpow`**): factor
  `xⁱ(1 − xʲ⁻ⁱ)`, `‖1 − xʲ⁻ⁱ‖ = 1` via `norm_add_eq_max_of_norm_ne_norm`, then `‖x‖^M ≤ ‖x‖ⁱ`.
* **`exists_uniformizer`** — `π` norm-maximal below 1, attained by `IsCompact.exists_isMaxOn` on the
  compact **`{‖y‖^M ≤ ‖2‖}`** (`Metric.isCompact_of_isClosed_isBounded` in the proper `↥k`;
  `uniform_gap` puts every norm-`< 1` element there).  *(This replaces the plan's `K = {‖2‖ ≤ ‖x‖ ≤
  …}` set — the `‖y‖^M ≤ ‖2‖` ball is cleaner and rpow-free.)*
* **`exists_ramificationIndex`** — exact `‖2‖ = ‖π‖^e`, `e ≥ 1`: `e := Nat.find` least with
  `‖π‖^{e+1} < ‖2‖`; exactness from `hmax` applied to `2/π^e`.  *(Norm algebra only — no
  finite-dimensionality; usable at hypothesis-π.)*
* **`exists_uniformizer_data`** — the `ℚ̄₂`-form package `∃ π ∈ k, π ≠ 0 ∧ ‖π‖ < 1 ∧ hπ_max ∧
  1 ≤ e ∧ ‖2‖ = ‖π‖^e`, exactly B13-5's π+e input.

The **exchange** `‖x‖ < 1 ↔ ‖x‖ ≤ ‖π‖` is just `hπ_max` + `‖π‖ < 1` (packaged in
`exists_uniformizer`); `𝔪 = πO` belongs to B13-3's residue field (☑, `UnitFiltrationCounts.lean`),
which is already stated over hypothesis-π and instantiates at this `π` in B13-5.

## B13-3 — residue field  ☑ done 2026-07-09 (commit pending; `GQ2/UnitFiltrationCounts.lean`)

Delivered (all std-3; `lake build` green 8593 jobs; guard census 12).  **Decoupled from B13-2
entirely** — `𝔪` is defined **intrinsically** as `{‖x‖ < 1}` (the non-units), *not* via a
uniformizer, so no `hπ_max` hypothesis was needed and the file is independent of lane A.  Public
API (namespace `GQ2.UnitFiltrationCounts`, for B13-4/B13-5):
- `Osub k : Subring ↥k` (`{‖x‖ ≤ 1}`; `mul_mem'` via `mul_le_one₀`, `add_mem'` via
  `norm_add_le_max`) + its `CompactSpace` (carrier = `closedBall 0 1`, `refine
  isCompact_iff_compactSpace.mp` — B13-1's pattern).
- `maxIdeal k : Ideal ↥(Osub k)` (`{‖·‖ < 1}`) + `@[simp] mem_maxIdeal`; `IsPrime` instance.
- `Finite (↥(Osub k) ⧸ maxIdeal k)` (`AddSubgroup.quotient_finite_of_isOpen`; `𝔪` open via
  `continuous_subtype_val.isOpen_preimage {‖·‖<1}`).
- `ResidueField k` (abbrev) + `noncomputable instance : Field` via `(Finite.isField_of_domain
  _).toField` (reuses the `Ideal.Quotient` `CommRing`, diamond-free).
- `norm_two_lt_one` (`‖(2:ℚ̄₂)‖ < 1` via `norm_algebraMap'` + `Padic.norm_p`), `two_eq_zero`,
  and `CharP (ResidueField k) 2` (from `(2:F)=0` via `CharP.exists` + `CharP.char_is_prime` +
  `cast_eq_zero_iff` + `Nat.prime_dvd_prime_iff_eq`).
- **`residue_card`** — `∃ f, 1 ≤ f ∧ Nat.card (O/𝔪) = 2^f ∧ Nat.card (O/𝔪)ˣ = 2^f − 1`
  (`FiniteField.card` + `Nat.card_eq_fintype_card` + `Fintype.card_units`).

Note for B13-4: the reduction map is `Ideal.Quotient.mk (maxIdeal k)`; the residue field is a
finite field, so `frobeniusEquiv`/`FiniteField` API applies.  (`Field` instance is `.toField`,
not `Ideal.Quotient.field` — the `IsMaximal`→auto-`Field` path did *not* fire on the abbrev.)

## B13-4 — graded isomorphisms + counts  ☑ DONE 2026-07-09 (commit `9fbb14d`; `UnitFiltrationCounts.lean`)

**Landed** (all std-3, `check_axioms` green, own-file build green).  Appended to lane B's
`UnitFiltrationCounts.lean` (namespace `GQ2.UnitFiltrationCounts`), parameterized by a uniformizer
`π : ↥k` (B13-2's `exists_uniformizer`):

* `gradeZeroHom : U⁰ →* (O/𝔪)ˣ` (`normUnitToOsubUnit` then `Units.map (Ideal.Quotient.mk 𝔪)`);
  `gradeZeroHom_ker = U¹` (the `‖x‖ < 1 ↔ ‖x‖ ≤ ‖π‖` exchange), `gradeZeroHom_surjective`,
  hence `card_gradeZero : #(U⁰/U¹) = #(O/𝔪)ˣ`.
* `gradeIHom : U^{(i)} →* Multiplicative (O/𝔪)` (`u ↦ (u−1)/πⁱ mod 𝔪`, `i ≥ 1`) — the hom law is
  **`depthRes_add`**, the cross-term `(u−1)(v−1)/πⁱ` having residue 0 (norm `≤ ‖π‖ⁱ < 1`);
  `gradeIHom_ker = U^{(i+1)}` (the **scaled exchange** `‖x‖ < ‖π‖ⁱ ↔ ‖x‖ ≤ ‖π‖^{i+1}`),
  `gradeIHom_surjective` (witness `1 + a·πⁱ`), hence `card_gradeI : #(U^i/U^{i+1}) = #(O/𝔪)`.
* **`exists_gradeCounts`** (the B13-5 input): `∃ f ≥ 1, #(U⁰/U¹) = 2^f − 1 ∧ ∀ i ≥ 1,
  #(U^i/U^{i+1}) = 2^f` — the isos composed with B13-3's `residue_card`.

`Nat.card` transport is `Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective … ).toEquiv`
(the B12-1 idiom); `Nat.card (Multiplicative X) = Nat.card X` by `rfl` (type synonym).  **B13-5** now
has all four structure inputs: π + e (B13-2) and f + the graded counts (here).

*(Original ticket text.)*  Plan §1(G).  Two homs with kernel + surjectivity, then `Nat.card`
transport to the **exact** `DyadicUnitFiltration`-field shapes:

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
