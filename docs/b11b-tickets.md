# B11b discharge — ticket board  (prove `unramifiedQuadratic_units_are_norms`, census −1)

**Status (2026-07-09): planned, not started — B11b-0 and the lane-A half of B11b-2 are ready;
the engine (B11b-3→) is gated on the B13 capstone** ([`b13-tickets.md`](b13-tickets.md) — the
capstone theorem, not its census flip).  Design fixed during the planning session (Fable pass,
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
| B11b-0 | ⬜ | O | Recon: σ-construction prototype (**go/no-go**), coordinate-API decision, name pins | ½ | — |
| B11b-1 | ⬜ | O | Quadratic layer: `L`, coordinates, σ, `norm_galois` port, `N`/`s`, degenerate case | 1 | B11b-0 |
| B11b-2 | ⬜ | F→O | Residue layer: Teichmüller + root separation + `σ̄ ≠ id` + `s̄` surjectivity | 1–1½ | A-half: B11b-0 · B-half: B11b-1 |
| B11b-3 | ⬜ | O | Approximation engine: π-transfer, depth-1 start, increments, limit | 1 | B11b-1 ∧ B11b-2 ∧ **B13 capstone** |
| B11b-4 | ⬜ | O | Capstone `unramifiedQuadratic_units_are_norms'` (byte-exact) | ½–¾ | B11b-3 |
| B11b-5 | ⬜ | O | Census flip (**user gate**) | ½ | B11b-4 |

Est. in lane-sessions.  **B11b-2(lane A) ∥ B11b-1**; B11b-1→4 in lane B.  Total ≈
**4½–6 lane-sessions**.

---

## B11b-0 — recon  (O, ½ session)

1. **σ prototype (go/no-go)**: in `lean_run_code`, construct for concrete-shape `k`, `δa ∉ k`
   with `δa² ∈ k` a global `g : ℚ̄₂ ≃ₐ[ℚ₂] ℚ̄₂` fixing `k` with `g δa = −δa` — expected route:
   `k`-embedding of `k⟮δa⟯` by minpoly-root transport (`IntermediateField.adjoin` power basis /
   `minpoly` lift), extended by `IsAlgClosed.lift`, upgraded by
   `Algebra.IsAlgebraic.algHom_bijective`.  If the instance stack fights, F-escalate **here**,
   before lane work starts.
2. Coordinate API decision (plan §2 row 6): fresh `adjoin.powerBasis`-based `{1, δa}`
   coordinates (~40 lines, expected) vs re-port of `QuadraticAdjoin` pieces vs un-`private`-ing
   `KummerSurjectivity` helpers.
3. Name pins: Frobenius-bijective on finite char-2 fields (`frobeniusEquiv`/perfect-field
   route); `Fintype/Nat.card` glue at `l`; `cauchySeq_of_le_geometric` shape at `↥L`.

## B11b-1 — quadratic layer  (O, 1 session; lane B)

Plan §1(Q)+(D): `L := k⟮δa⟯` with `k ≤ L`, `FiniteDimensional ℚ_[2] L`; unique coordinates
`z = x + yδa`; σ (global lift; `σ|_k = id`, `σδa = −δa`, `σ² = id` on `L`, fixed points
exactly `k` — coordinates); **`norm_galois` port** (3 lines,
`NormedAlgebra.norm_eq_spectralNorm ℚ_[2]` + `spectralNorm_eq_of_equiv` — original at
`HilbertLedger.lean:313`, downstream, so re-derive); σ preserves `O_L`/depth balls;
`N(z) := z·σz = x² − ay² ∈ k`, `s(z) := z + σz = 2x ∈ k`; the degenerate `δa ∈ k` case
(`x = (1+u)/2`, `y = (u−1)/(2δa)`).

## B11b-2 — residue layer  (F→O, 1–1½ sessions; **the risk pocket**)

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
