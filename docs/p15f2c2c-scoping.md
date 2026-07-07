# P-15f2c2c scoping — the analytic `hunram` (unramified ⟹ equal value groups)

**Created 2026-07-08 (Opus).** Self-contained scoping for **P-15f2c2c**, the last open
mathematical input of the involution vanish route of P-15f2 (`lemma_6_17_vanish`). c2c was
designed in the 2026-07-07 c2 split (`docs/p15f2c-design.md`, commit `2d011e1`) but never got a
board row — this doc + the new `docs/tickets.md` row restore it.

---

## 0. TL;DR

**Deliverable.** Discharge the analytic `hunram` hypothesis that c2b threads through
`ShapiroDeepness.hvanish_involution` / `hvanish_involution_of_deepClass` and that
`SectionSix.lemma_6_16` / `HilbertLedger.cup_unramified_unit` ultimately consume:

```lean
hunram : ∀ x : AlgebraicClosure ℚ_[2], x ≠ 0 → x ∈ L →
  ∃ y : AlgebraicClosure ℚ_[2], y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖
```

for the involution tower `k = fixedField U₀ ≤ L = fixedField (ker ρ)`, `[L : k] = 2`. This is
exactly **`‖L^×‖ = ‖k^×‖`** — the value groups of the two fields coincide, i.e. `L/k` is
**unramified**.

**Status of the datum (c2b Step-0, ✓).** `L/k` is *always* unramified at an involution orbit:
`ρ(ĝ)` has order 2 in `C`, but `C`'s tame inertia `⟨c tameTau⟩` has **odd** order
(`Tame.tame_odd_order` on the tame relation `σ⁻¹τσ = τ²`), so `ρ(ĝ) ∉ inertia`. c2c is therefore
a genuine **TRUE** proof obligation, not a statement amendment.

**The catch (why this is a real ticket).** The repo works in **spectral-norm vocabulary only** —
B13's docstring is explicit: "no valuation ring, residue field, or ramification bookkeeping is
introduced." And **`inertia` is not formally defined** anywhere in the repo (all occurrences are
prose or the *finite-field* Frobenius `frobFixed` of `𝔽_{2^{2m}}`, unrelated). So c2c cannot cite
a mathlib "unramified ⟹ equal value groups" and must argue residue-field-free.

---

## 1. The two `hunram`s (do not conflate)

| name | statement | where | meaning |
|---|---|---|---|
| **group-level** | `c tameTau = 1` | `SectionSix.lean:309` (`prop_6_9_unramified`), `PhaseGaussLIndep.lean:83` | tame inertia dies under `c` |
| **analytic** (c2c) | `∀ x∈L, x≠0 → ∃ y∈k, y≠0 ∧ ‖x‖=‖y‖` | `SectionSix.lean:755` (`lemma_6_16`), `ShapiroDeepness.lean:187` | equal value groups `‖L^×‖ = ‖k^×‖` |

c2c bridges the group-level unramifiedness (available as `ρ(ĝ) ∉ inertia`) to the analytic form.

---

## 2. Decomposition

### Half (A) — the value-group lemma [model O, landable now, NEW `GQ2/UnramifiedNorm.lean`]

**Claim.** Given B13 `DyadicUnitFiltration` data `Fk` for `k` and `FL` for `L` with **equal
uniformizer norm** `‖FL.π‖ = ‖Fk.π‖`, the analytic `hunram` holds.

**Proof.**
1. *Value-group generation.* For a finite dyadic field `F` with filtration `F_`
   (`π := F_.π ∈ F`, `hπ_max` discreteness), every nonzero `x ∈ F` has `‖x‖ = ‖π‖^n` for a unique
   `n : ℤ`. Route: `DeepCount.norm_step_down` (`GQ2/DeepCount.lean:152`) is exactly the discreteness
   step-down — `x ∈ F`, `‖x‖ < ‖π‖^i ⟹ ‖x‖ ≤ ‖π‖^(i+1)`. Iterate up from `‖x‖ ≤ 1` for the
   `‖x‖ ≤ 1` case; for `‖x‖ > 1` apply to `x⁻¹` (still in `F`) and negate the exponent. The norm
   lands in the multiplicative subgroup `⟨‖π‖⟩ ⊆ ℝ_{>0}`, so `‖x‖ = ‖π‖^n`. **This is the only
   nontrivial part of (A).**
2. *Transport.* For `x ∈ L^×`, write `‖x‖ = ‖FL.π‖^n = ‖Fk.π‖^n` (hypothesis) `= ‖Fk.π^n‖`, with
   `Fk.π^n ∈ k` (a field, `Fk.hπ_mem` + closure under `zpow`), nonzero (`Fk.hπ_ne`). Take
   `y := Fk.π^n`. ∎

**The `e`-form.** Equivalently take the input `FL.e = Fk.e` (equal absolute ramification index):
both satisfy `‖2‖ = ‖π‖^e` (`he`), and `‖2‖`, `‖π_·‖ ∈ (0,1)`, so equal `e` forces
`‖FL.π‖ = ‖Fk.π‖` (`e`-th roots of the same `‖2‖ ∈ (0,1)`, `pow_left_injective`-style). Provide
both entry points so f2d/half-(B) can supply whichever is natural.

*Estimated size:* ~120–180 ln. No new axioms (uses only B13 + `DeepCount`/`HilbertLedger` norm
lemmas). Target `#print axioms = std-3 + {B13}` (B13 via `dyadicUnitFiltration`).

### Half (B) — the ramification bridge [**DERIVE, no new axiom** — plan of record 2026-07-08]

**Claim.** For the involution tower, `‖FL.π‖ = ‖Fk.π‖` (equivalently `FL.e = Fk.e`).

**User decision (2026-07-08): no new axiom.**  A full audit of the existing axioms found the
derivation **feasible** — the key discovery is that **B5's `norm_reciprocity` clause is the full
finite-level norm-group correspondence** (`GQ2/Reciprocity.lean:216`): for every finite *abelian*
`F/ℚ₂`, `ℚ₂ˣ → Gal(F/ℚ₂)` (= `restrictAb ∘ recip`) is surjective with kernel exactly
`normSubgroup F = range (Units.map (Algebra.norm ℚ₂))`.  Combined with B10′'s orientation
(`nuT_recip_unit`: units have trivial `ν_t`-coordinate) and B13's value-group discreteness, the
ramified case is refutable with **zero census change**.  Axiom trace of the finished `hunram`:
std-3 + {B5 `localReciprocity`, B10′ `tameQuotient`, B13 `dyadicUnitFiltration`} (+ B9/B11a/B11b
downstream via `lemma_6_16`, unchanged).

#### The derivation (evidence-checked against the repo)

Setting: `L := splitField ρ = fixedField (kerGal ρ)` (`GQ2/ResidueLift.lean:284` — banked, with
`fixingSubgroup_splitField`, `splitField_finiteDimensional`), `k = fixedField U₀`,
`Gal(L/k) = ⟨ĝ⟩` order 2 (c2b's `hindex`/`hs`).  `ρ = c ∘ B.tameF` (frozen `hfac`,
`SectionSix.lean:885`), `C = ⟨s, t⟩` with `s := c tameSigma`, `t := c tameTau`,
`s⁻¹ts = t²` (`tame_relation`), so `⟨t⟩ ◁ C`, `C/⟨t⟩ = ⟨s̄⟩` **cyclic**, and
`r := ord t` is **odd** (`Tame.tame_odd_order`).

1. **`m := e_{L/k} ∣ 2`** *(axiom-free)*.  The quadratic norm trick: for `x ∈ L^×`,
   `x · (ĝ•x) ∈ k` (fixed by `⟨L.fixingSubgroup, ĝ⟩ = k.fixingSubgroup`;
   `fixedField_fixingSubgroup`) and `‖x·ĝx‖ = ‖x‖²` (`norm_galois`).  So `‖x‖² ∈ ‖k^×‖` for
   all `x ∈ L^×`; at `x = π_L`, zpow-injectivity gives `m ∣ 2` (via `norm_eq_zpow`, half A).
2. **`e_L = e(L/F₀) · e_{F₀}` and `e(L/F₀) ∣ r`** *(axiom-free)*, where
   `F₀ := L^{⟨t⟩} = fixedField (ρ⁻¹⟨t⟩)`: the coset-norm `∏_{γ ∈ ⟨t⟩} γ•x ∈ F₀` has norm
   `‖x‖^r`, so `‖L^×‖^r ⊆ ‖F₀^×‖`; `e`-multiplicativity is zpow bookkeeping (half A).
3. **`e_{F₀} = [U : U ∩ N(F₀ˣ)]`** *(B5(a))*.  `F₀/ℚ₂` is finite Galois with **abelian** group
   `C/⟨t⟩` (cyclic), so `norm_reciprocity` applies: `[ℚ₂ˣ : N] = #Gal(F₀/ℚ₂) = n₀`.
   Analytically `v₂(N(F₀ˣ)) = (n₀/e_{F₀})·ℤ` (`Algebra.norm_eq_prod_automorphisms` +
   `norm_galois` lifted along `AlgEquiv.liftNormal`/`restrictNormalHom_surjective`, then
   `‖N x‖ = ‖x‖^{n₀}` + B13-zpow), and the index through `v₂ : ℚ₂ˣ ↠ ℤ` factors as
   `n₀ = (n₀/e_{F₀})·[U : U∩N]` — so `e_{F₀} = [U : U∩N] = #(unit-image in Gal(F₀/ℚ₂))`.
4. **The unit-image is odd** *(B10′ + procyclic factoring)*.  The composite
   `AbsGalQ2 → Gal(F₀/ℚ₂) ↠ (2-part)` kills `ker B.tameF` and `τ`, i.e. factors through a
   continuous `φ : Ttame → Q` (finite 2-group) with `φ(tameTau) = 1`.  **Factoring lemma
   (N3)**: any such `φ` factors through `nuT` — either (i) via `maxProPQuotient 2 Ttame ≅ Ztwo`
   (τ dies in every finite 2-quotient by `tame_odd_order`; T-05 `proPKernel_le_ker` gives the
   factoring; identify with `nuT` on the topological generator), or (ii) the direct procyclic
   closure argument in `ℤ₂ × Q`.  Then `nuT_recip_unit` (B10′, threaded as an orientation
   hypothesis on `B.tameF`, discharged at `boundaryMapsWitness`) kills the unit-image in the
   2-part: `e_{F₀}` is **odd**.
5. **Assembly**: `e_L = e(L/F₀)·e_{F₀} ∣ r·e_{F₀}` odd, and `e_L = m·e_k`, so `m` is odd; with
   `m ∣ 2`: `m = 1`, i.e. `‖π_L‖ = ‖π_k‖`.  Feed half A's `hunram_of_uniformizer_norm_eq` ⟹
   **`hunram`**. ∎

#### Bricks (work order)

| brick | content | deps | est. |
|---|---|---|---|
| **N1** | Galois coset-norm kit: `∏_{coset reps} g•x ∈ fixedField`, `‖N x‖ = ‖x‖^{index}`; corollaries `m ∣ 2`, `e(L/F) ∣ #Gal(L/F)`, `e`-multiplicativity | InfiniteGalois + `norm_galois` + half A | 1–1.5 sess. |
| **N2** | the CFT index: `e_{F₀} = [U : U∩N] = #(unit-image)` via B5(a) + `Algebra.norm_eq_prod_automorphisms` + `v₂`-SES bookkeeping; `IsGalois ℚ₂ F₀` plumbing | N1, B5 | ~1 sess. |
| **N3** | the `ν_t`-factoring: continuous `Ttame → Q` (2-group) killing `τ` factors through `nuT`; + the B10′-orientation threading (`hnuT_unit` hypothesis, witness discharge) | T-05 / profinite layer | 0.5–1 sess. |
| **N4** | assembly + the c2b interface (`hunram`-producer over the f2-tower data; `splitField`-identification) | N1–N3, half A ✓ | ~0.5 sess. |

**Interface flags** (for the c2b/f2d owner and P-20):
* the `hunram`-producer needs the `ρ/c/B/hfac` tame data + the B10′-orientation hypothesis in
  scope — all present in the frozen `lemma_6_17_vanish` signature **except the orientation**,
  which must thread as one added hypothesis of the *moved* statement (precedent: the `hc`/`hV2`
  amendments) and is discharged at `boundaryMapsWitness`;
* `lemma_6_17_vanish`'s docstring predicts "Ax: B6, B7′, B9" — the trace will gain
  B5/B10′/B13 (existing axioms, census unchanged) — deviation note for P-20.

---

## 3. Interface pins (verified 2026-07-08)

| need | pinned name | where |
|---|---|---|
| target `hunram` shape | `hvanish_involution` / `hvanish_involution_of_deepClass` (hypothesis) | `ShapiroDeepness.lean:187,228` |
| downstream consumer | `SectionSix.lemma_6_16` (`:755`), `HilbertLedger.cup_unramified_unit` (`:293`) | — |
| B13 filtration data | `DyadicUnitFiltration` (`π`, `hπ_mem`, `hπ_ne`, `hπ_lt`, `hπ_max`, `e`, `he_pos`, `he`, `f`) | `UnitFiltration.lean:153` |
| B13 axiom | `dyadicUnitFiltration k [FiniteDimensional ℚ_[2] k]` | `Foundations/Axioms.lean:599` |
| discreteness step-down | `norm_step_down (hπk) (hπ0) (hπmax) (hx) (h : ‖x‖<‖π‖^i) : ‖x‖ ≤ ‖π‖^(i+1)` | `DeepCount.lean:152` |
| Galois-invariance of `‖·‖` | `norm_galois (g) (x) : ‖g • x‖ = ‖x‖` | `HilbertLedger.lean:312` |
| group-level unramified (contrast) | `prop_6_9_unramified` `(hunram : c tameTau = 1)` | `SectionSix.lean:306` |
| Step-0 odd-order inertia | `Tame.tame_odd_order (hs) (h : s⁻¹ t s = t²) : Odd (orderOf t)` | `Tame.lean:42` |

Norm facts: `‖·‖` on `ℚ̄₂` is the spectral norm (`NormedAlgebra.norm_eq_spectralNorm ℚ_[2]`),
ultrametric (`IsUltrametricDist`); `‖2‖ = ‖(2:ℚ_[2])‖ < 1` (`Padic.norm_p_lt_one`).

---

## 4. Work order

1. ✅ board row (`docs/tickets.md`) + this scoping doc.
2. **(A)** `GQ2/UnramifiedNorm.lean` — the value-group lemma (this session's target). Register in
   `GQ2.lean`; gate `#print axioms = std-3 + {B13}`.
3. **(B)** flag the axiom-vs-derive decision to the f2-lead; on sign-off, land the chosen bridge.
4. f2d consumes: `hunram := unramifiedNorm … (bridge-supplied ‖π_L‖=‖π_k‖)` into
   `hvanish_involution_of_deepClass`.

## 5. Coordination

* **Own file** `GQ2/UnramifiedNorm.lean` — write-disjoint from c1 (`ShapiroRead.lean`), c2a
  (`QuadraticAdjoin.lean`), c2b (`ShapiroDeepness.lean`). Shared worktree: stage only files
  touched here; commit each green piece promptly.
* `docs/tickets.md` is co-owned and the f2-lead may be mid-edit — the c2c row was added as a single
  new row (no edits to neighbours); cross-flag before further board edits.
* Half (B)'s axiom is a **census change** — owner sign-off required (do not add unilaterally).
