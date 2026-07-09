# B11b discharge — ticket board  (prove `unramifiedQuadratic_units_are_norms`, census −1)

**Status (2026-07-09): B11b-0/1/2 ☑ done — the residue layer (the risk pocket) is landed and
std-3; only the engine chain remains, and B11b-3 is gated on the B13 capstone**
([`b13-tickets.md`](b13-tickets.md) — the capstone theorem, not its census flip).  Design fixed during the planning session (Fable pass,
this board + [`b11b-proof-plan.md`](b11b-proof-plan.md)): the norm-form engine runs a
**depth-by-depth approximation** against the B13 filtration, whose only genuinely novel brick
is the **residue layer** — Teichmüller units + odd-root separation ⟹ `σ̄ ≠ id` ⟹ the trace
residue `s̄` covers `k̄`.  Census decrements at B11b-5, **gated on explicit user approval**;
after this flip `dyadicNormCriterion` rests on **B11a alone**.

Conventions as on [`tickets.md`](tickets.md) (Model **F**/**O**/**F→O**; gates: own-file
`lake build`, `lean_verify` = std-3 exactly, `scripts/check_axioms.sh`, own-files staging with
printed staged set).  Development in **two new files** — `GQ2/TeichmullerLift.lean` (lane A,
σ-free bricks), `GQ2/UnramifiedQuadraticNorms.lean` (lane B, σ + engine + capstone) — one lane
per file; **do not edit** shared files before the flip.  NB: `GQ2/UnramifiedNorm.lean` already
exists and is unrelated — do not touch it.

| # | St | Model | Ticket | Est. | Deps |
|---|----|-------|--------|------|------|
| B11b-0 | ☑ 07-09 | O | Recon: σ-construction prototype (**go/no-go**), coordinate-API decision, name pins | ½ | — |
| B11b-1 | ☑ 07-09 | O | Quadratic layer: `L`, coordinates, σ, `norm_galois` port, `N`/`s`, degenerate case | 1 | B11b-0 |
| B11b-2 | ☑ 07-09 | F→O *(ran F)* | Residue layer: Teichmüller + root separation + `σ̄ ≠ id` + `s̄` surjectivity | 1–1½ | A-half: B11b-0 · B-half: B11b-1 |
| B11b-3 | ⬜ | O | Approximation engine: π-transfer, depth-1 start, increments, limit | 1 | B11b-1 ∧ B11b-2 ∧ **B13 capstone** |
| B11b-4 | ⬜ | O | Capstone `unramifiedQuadratic_units_are_norms'` (byte-exact) | ½–¾ | B11b-3 |
| B11b-5 | ⬜ | O | Census flip (**user gate**) | ½ | B11b-4 |

Est. in lane-sessions.  **B11b-2(lane A) ∥ B11b-1**; B11b-1→4 in lane B.  Total ≈
**4½–6 lane-sessions**.

---

## B11b-0 — recon  ☑ done 2026-07-09  (all `lean_run_code`-verified)

**Go/no-go: GO — and the σ construction is *simpler* than planned** (a route change that
de-risks B11b-1 and shrinks §1(Q)/§2).

1. **σ prototype — GO, via `exists_conj`, not `IsAlgClosed.lift`.**  `QuadraticAdjoin.exists_conj`
   (downstream) already builds exactly this σ *without* PowerBasis / minpoly-lift / `IsAlgClosed.lift`
   / `algHom_bijective` — it uses the **infinite Galois correspondence**
   (`InfiniteGalois.fixedField_fixingSubgroup ⊥` ⟹ `fixedField ⊤ = ⊥`; `δa ∉ ⊥` ⟹ some
   `σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂` moves `δa`; `(σδa)² = δa²` ⟹ `σδa = −δa`).  Re-derives **standalone
   (Mathlib only)** — verified.  **σ is a `↥k`-algebra equiv** (fixes `k` pointwise for free; use
   `.restrictScalars ℚ_[2]` only if a `G_{ℚ₂}`-element is ever needed — the residue/engine work
   wants the `↥k`-form).  `σ²|_L = id` (`σδa = −δa`, `σ|k = id`).  Prototype (re-port target for
   B11b-1), needs porting `mem_bot_iff_mem` too (`QuadraticAdjoin.lean:80`):
   ```lean
   -- hbot : δa ∉ (⊥ : IntermediateField ↥k ℚ̄₂) via `IntermediateField.mem_bot` + `rintro ⟨y,hy⟩; exact hδk (hy ▸ y.2)`
   -- htop : fixedField ⊤ = ⊥ via `← fixingSubgroup_bot` + `InfiniteGalois.fixedField_fixingSubgroup ⊥`
   -- hmove : ∃ σ, σ δa ≠ δa (by_contra ⟹ δa ∈ fixedField ⊤ = ⊥); then (σδa+δa)(σδa−δa)=0, σ.commutes.
   ```
2. **Coordinate API — decision: re-port `QuadraticAdjoin.exists_coords`' `modByMonic`-remainder
   technique** (`p %ₘ minpoly ↥k δa`, remainder linear ⟹ `z = x + yδa`; proven, ~40 lines; needs
   `(minpoly ↥k δa).natDegree = 2` from `δa ∉ k`, `δa² = d`).  `Submodule.mem_span_pair`
   (`z ∈ span R {x,y} ↔ ∃ a b, a•x+b•y = z`) confirmed as the lighter alternative if the minpoly
   bookkeeping bloats.  (Fresh `adjoin.powerBasis` rejected — `exists_coords` is more directly
   re-portable.)
3. **Name pins** (`lean_run_code`-verified):
   * `cauchySeq_of_le_geometric` / `cauchySeq_of_le_geometric_two` — `Analysis/SpecificLimits/Basic.lean` ✓
   * **Frobenius bijective on a finite char-2 field** (`x ↦ x²`) — turnkey:
     ```lean
     have h := (frobeniusEquiv l 2).bijective   -- PerfectRing l 2 := inferInstance (finite ⟹ perfect)
     have he : ⇑(frobeniusEquiv l 2) = (fun x : l => x ^ 2) := by ext x; rw [frobeniusEquiv_apply, frobenius_def]
     rwa [he] at h
     ```
   * **Deferred to the B13 capstone** (residue-field `l` interface not built until B13-5): `Fintype`/
     `Nat.card` glue at `l`, and `#l = 2^F` ⟹ `m := 2^F − 1` odd.  Pin against B13's actual `l` at
     B11b-3 start — not a blocker (B11b-1/2-laneA don't need `l`).

## B11b-1 — quadratic layer  ☑ done 2026-07-09 (commit pending)

Delivered in `GQ2/UnramifiedQuadraticNorms.lean` (**imports Mathlib only** — the
`GQ2.TeichmullerLift` import is deferred to B11b-3, which is the first to need the σ-free bricks;
so this file is independent of the B11b-2 lane-A agent and B13).  All std-3; `lake build` green
(8583 jobs); guard all-pass census 12.  Public API (parametric over `σ` — B11b-4 obtains it):
- `norm_galois (g : ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) : ‖g x‖ = ‖x‖` + `norm_conj_eq (σ : ℚ̄₂ ≃ₐ[↥k] ℚ̄₂)` (via
  `.restrictScalars ℚ_[2]`) — `spectralNorm` re-derivation, 3 lines.
- `mem_bot_iff_mem`, **`exists_conj`** (σ with `σδa = −δa`, the B11b-0 `exists_conj` re-port).
- `conj_base` (σ fixes `k`), `conj_apply` (`σ(x+yδa) = x−yδa`), `norm_coord`
  (`(x+yδa)(x−yδa) = ↑(x²−ay²)`), `trace_coord` (`= ↑(x+x)`).
- `minpoly_natDegree_eq_two`, **`exists_coords`** (`z ∈ ↥k⟮δa⟯ ⟹ z = x+yδa`, `modByMonic`
  remainder), **`conj_fixed_iff`** (`σz = z ↔ z ∈ k` on the adjoin — the fixed-field fact the
  residue layer needs).
- **`norm_form_of_mem`** — the degenerate `δa ∈ k` case (`x = (1+u)/2`, `y = (u−1)/(2δ')`,
  `field_simp` + `linear_combination`).

Notes for B11b-2/3 (same coercions): (a) the `↥k → ℚ̄₂` numeral coe needs care — `trace_coord`
states `x+x` not `2x` to sidestep `((2:↥k):ℚ̄₂)`; (b) `modByMonic_add_div (p q)` takes the
polynomial (no monic hyp); `natDegree_modByMonic_lt` needs `q ≠ 1`.

## B11b-2 — residue layer  ☑ done 2026-07-09  (every decl `lean_verify` = std-3 exactly)

**Landed**: lane A in `GQ2/TeichmullerLift.lean` (commit `5784a9e`); lane-B closure appended to
`GQ2/UnramifiedQuadraticNorms.lean` (which now imports `GQ2.TeichmullerLift`).  Own-file builds
green (8583/8584 jobs); guard all-pass, census 12.  Neither F-escalation trigger fired (the
`↥L`-Cauchy ran on the `sq_of_near_one` template unchanged; the fixed-point step is exactly
`conj_fixed_iff`).  **Design deltas over the plan — all simplifications, no weakening:**

1. **No residue-field interface anywhere** (recon note 3 realized): lane A abstracts every B13
   input into a norm hypothesis, so `TeichmullerLift.lean` imports **Mathlib only** (not
   `UnitFiltrationCounts` — plan §3 deviation, noted in its header); the lane-B closure states
   `σ̄ = id` as `∀ z ∈ O_L, ‖σz − z‖ < 1` and takes `(q, hqn : ‖q‖ < 1, hqodd : Odd (q−1),
   hlag : Lagrange at L)` as hypotheses — **B11b-3 discharges them from B13-at-`L`**
   (`q := 2^F`).
2. **Contraction in one step, no iterated squaring** (`norm_pow_sub_pow_le`):
   `‖a^q − b^q‖ ≤ max(‖q‖, ‖a−b‖)·‖a−b‖` on the unit ball for ANY `q` with `‖q‖ < 1` — the
   geometric sum `∑ aⁱb^{q−1−i}` is `q·a^{q−1}` up to a multiple of `a − b`.
3. **Root separation without the derivative product** (`norm_sub_eq_one_of_pow_eq_one`):
   `m = ∑_{i<m}(1 − ηⁱ)` once `∑ηⁱ = 0`, each term `≤ ‖1 − η‖`, `‖m‖ = 1` for odd `m`
   (`norm_natCast_eq_one_of_odd`, via `Padic.norm_natCast_eq_one_iff`) — no root-set
   enumeration, no polynomial derivatives.
4. **`s̄`-surjectivity strengthened to exact coverage** (`trace_covers`): the `σ̄ ≠ id` witness
   `z₁ = x + yδa` has **unit** trace value `t := s(z₁) = 2x ∈ k` (char-2 shift: `s(z₁)` and
   `σz₁ − z₁` differ by `2z₁`, norm `< 1`), and `s` is `k`-linear, so `z := (c/t)z₁` gives
   `z + σz = c` **on the nose** for every integral `c ∈ k` — the engine gets exact increments;
   no `mod 𝔪` bookkeeping, no `l^{σ̄}`-linear algebra.

Decls (lane A): `norm_finset_sum_le` (private), `norm_pow_sub_pow_le_norm_sub`,
`norm_pow_sub_pow_le`, `norm_natCast_eq_one_of_odd`, `norm_one_sub_eq_one_of_pow_eq_one`,
`norm_sub_eq_one_of_pow_eq_one`, `exists_teichmuller`, `le_of_shared_uniformizer`.
(lane B): `norm_two_lt_one`, `le_of_conj_residue_trivial` (**the crux**), `exists_conj_unit`,
`trace_covers` (**the engine deliverable**).

### (original ticket text)

**Lane A (σ-free, `GQ2/TeichmullerLift.lean`, can start after B11b-0, ∥ B11b-1):**
- *Teichmüller units* (plan §1(R)1): in a complete finite subextension with the B13 filtration,
  for a norm-one `w` the sequence `w^{qⁿ}` (`q = #residue`) is Cauchy (squaring deepens
  congruence: `x² − y² = (x−y)(x+y)`, `‖x+y‖ ≤ max(‖2x‖, ‖x−y‖)`), with limit `ω`:
  `ω^{q−1} = 1`, `ω ≡ w (mod 𝔪)`.  Template: `HilbertLedger.sq_of_near_one`'s
  `cauchySeq_of_le_geometric` pattern.
- *Odd-root separation* (§1(R)2): distinct `m`-th roots of unity (`m` odd) have
  `‖ζ − ζ'‖ = 1` (derivative product `= m·ζ^{m−1}`, norm 1; every factor `≤ 1` and product
  `= 1` ⟹ all `= 1`).  Technique: `ResidueLift.exists_nthRoot_near` in reverse.
- *Successive approximation* (§1(R)4): shared uniformizer + equal residues (`l = k̄`) ⟹
  `L = k` (π-adic partial sums with `O_k`-coefficients; `k` closed in `L`; scale into `O_L`).

**Lane B closure (needs σ from B11b-1):** `σ̄ : l → l` well-defined (norm preservation);
**`σ̄ = id ⟹ L = k`** (Teichmüller units are σ-fixed by root separation ⟹ `l = k̄` ⟹
approximation ⟹ contradiction with `δa ∉ k`); hence `s̄(z̄) = z̄ + σ̄z̄` is nonzero (char 2:
kernel = fixed field), `l^{σ̄}`-linear into `l^{σ̄}`, surjective onto `l^{σ̄} ⊇ k̄`.

*F-escalation triggers*: Teichmüller Cauchy bookkeeping > ½ session; or the residue-level
fixed-point identification resists the coordinate argument.

## B11b-3 — approximation engine  (O, 1 session; lane B; **gated on B13 capstone**)

Plan §1(F)+(A): π-transfer (`hunram` + `hπ_max` at `k` ⟹ `hπ_max` at `L`, `σπ = π`);
filtration data at `k`, `L` via `dyadicUnitFiltration'`; depth-1 start (`u ≡ x₀² (mod 𝔪)` —
Frobenius bijective on finite char-2 `k̄`); the increment
`wₙ₊₁ = wₙ(1 + πⁿz₀)` with `s̄(z̄₀) = c̄` (state with explicit `‖·‖ ≤ ‖π‖^{n+1}` conclusions —
cross term at depth `2n ≥ n+1`); Cauchy ⟹ limit `w`; `N` continuous (σ a `k`-linear isometry,
fin-dim) ⟹ `N(w) = u`.  **Never take coordinates of `O_L`-elements** (non-integral
coordinates exist, e.g. `(−1+√−3)/2`) — coordinates only of the final `w`.

## B11b-4 — capstone  (O, ½–¾ session; lane B)

`unramifiedQuadratic_units_are_norms'` with the **byte-exact** axiom statement (unfold
`IsUnramifiedQuadraticSpectral` into the §1(F) transfer; dispatch degenerate ∨ main);
coordinate extraction to `x y : ↥k` (coercion injectivity); `lean_verify` = std-3.

## B11b-5 — census flip  (O, ½ session + coordination; **user-approval gate**)

The B7′-5b pattern: `Axioms.lean` axiom → same-name theorem (+ import of
`GQ2.UnramifiedQuadraticNorms`); `EXPECTED_AXIOMS` −1 + history note; `AxiomLedger.bAxioms`
row; docs rows + census notes (**note: `dyadicNormCriterion` now rests on B11a alone**);
regenerate `atlas-audit.md`; spot `lean_verify` on consumers (`SectionSix.lemma_6_16`,
`VanishClose.lemma_6_17_vanish_final`, `dyadicNormCriterion`: B11b vanishes, B11a remains);
archive board + plan to `docs/orchestration/`.  Quiet tree.
