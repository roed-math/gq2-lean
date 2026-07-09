# B7′ discharge plan: prove `hilbertSymbol_dyadic` (census 13 → 12)

**Goal.**  Replace the axiom (`Foundations/Axioms.lean`, namespace `GQ2.HilbertSymbol`)

```lean
axiom hilbertSymbol_dyadic (α β : ℤ) (u v : ℤ_[2]ˣ) :
    hilbertSymbol (unit2 ^ α * unitCoe u) (unit2 ^ β * unitCoe v)
      = signOf (ε u * ε v + (α : ZMod 2) * ω v + (β : ZMod 2) * ω u)
```

by a proof — Serre, *A Course in Arithmetic*, Ch. III §1.2, Theorem 1, `p = 2` case (`ε, ω`:
Ch. II §3.3; PDF in `references/`).  `hilbertSymbol` is defined by **solvability of
`a X² + b Y² = Z²`** (`IsHilbertSolvable`, `GQ2/HilbertSymbol.lean:40`), so this is a genuine
theorem about ternary conics over `ℚ₂`, not a definitional unfold.  Everything is std-3
(2-adic Hensel + finite `decide`s; **no** B-axioms, no `native_decide` — the guard forbids it).

**Estimated effort** (repo units): **4–5½ lane-sessions** (≈ 2 lane-days; B7′-3 ∥ B7′-4).
Board: [`b7prime-tickets.md`](b7prime-tickets.md).

## 0. Shared-tree constraints

* All development in **two new files** (`GQ2/DyadicSquares.lean`, `GQ2/HilbertSymbolDyadic.lean`);
  do **not** edit `GQ2/HilbertSymbol.lean` (shared; its docstring's mention of the pruned stress
  tests can get a one-line pointer touch-up at the flip, optional).
* Census is in flux (B2 + B12 removal landed 2026-07-09, `EXPECTED_AXIOMS=13`); B7′-5 rebases on
  whatever the census is at flip time and decrements it.  Standard gates per increment:
  own-file `lake build`; `lean_verify` = std-3 exactly; `scripts/check_axioms.sh`; stage only own
  files, print the staged set.

## 1. Mathematical route

Both sides of the axiom depend only on `(α mod 2, β mod 2, u mod 8, v mod 8)`:
the RHS by definition (`ε, ω` factor through `PadicInt.toZModPow 3`; `(α : ZMod 2)` sees parity),
the LHS because `hilbertSymbol` is square-class invariant (`hilbertSymbol_mul_sq_left`, pruned but
recoverable — §2) and **`u ≡ v (mod 8)` units differ by a square** (the Hensel criterion, §4-B7′-1).
So the axiom reduces to finitely many **leaves parameterized by residues** — no unit literals:

```lean
-- shape of a −1 leaf:   ∀ u v : ℤ_[2]ˣ, toZModPow 3 ↑u = 3 → toZModPow 3 ↑v = 7 →
--                          hilbertSymbol (unitCoe u) (unitCoe v) = -1
-- shape of a +1 leaf:   … → hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = 1
```

**Family reduction.**  After parity reduction, `(α%2, β%2) ∈ {(0,0), (0,1), (1,0), (1,1)}`;
`(1,0)` follows from `(0,1)` by symmetry (`hilbertSymbol_comm`), and — the key design move —
**`(1,1)` reduces to `(0,1)`** via the *elementary* identity

```lean
(a, b) = (a, -(a*b))        -- hilbertSymbol_neg_mul_right
```

proved from the **norm-form characterization** `IsHilbertSolvable a b ↔ IsSquare a ∨
∃ s t, b = s² − a t²` (solve for `b` when `y ≠ 0`; `y = 0` forces `a` square) plus the
**Brahmagupta identity** `(s² − at²)(s′² − at′²) = (ss′ + att′)² − a(st′ + ts′)²` (`ring`) and
`−a = 0² − a·1²`.  Then `(2u, 2v) = (2u, −4uv) = (2u, −uv)` (square-invariance), whose RHS-side
bookkeeping matches by `ε(−uv) = 1 + ε(u) + ε(v)`, `ω(−uv) = ω(u) + ω(v)` and `ε² = ε` in `𝔽₂`
(checked on paper: exponent `ε(u)(1+ε(u)+ε(v)) + ω(u)+ω(v) = ε(u)ε(v)+ω(u)+ω(v)` ✓).
*This kills the only family whose direct witnesses would have needed `u mod 16` — the
alternative (leaves at mod-16 residues) quadruples the leaf count and was rejected.*

**Leaf inventory** (residues `{1,3,5,7}`, `ε = (0,1,0,1)`, `ω = (0,1,1,0)`; symmetry halves):

* **+1 leaves, freebies (~11)**: `u₀ = 1` ⟹ `u` is a square ⟹ symbol `1` for every `b`
  (glue `hilbertSymbol_isSquare_left`, witness `(x,y,z) = (1,0,c)`).
* **+1 leaves, explicit witnesses (7)**: unit·unit `{3,5}, {5,5}, {5,7}` and `(u,2v)` with
  `u₀=7, v₀∈{1,5}` / `u₀=3, v₀∈{3,7}` — all hit by `(x,y) ∈ {(1,1),(1,2),(2,1)}` with values
  `∈ {9, 17, 23→(2,1):17, 25, 33}` ≡ 1 (mod 8), certified by the Hensel square criterion
  (paper-verified: `3·4+5=17`, `5+4·5=25`, `5+4·7=33`, `7+2=9`, `7+10=17`, `3+6=9`, `3+14=17`).
* **−1 leaves, `decide` (11)**: unit·unit `{3,3},{3,7},{7,7}`; `(u,2v)` at `u₀=3,v₀∈{1,5}`,
  `u₀=5,v₀∈{1,3,5,7}`, `u₀=7,v₀∈{3,7}`.  Each: no *primitive* solution mod 8
  (spot-verified on paper for `(3,7)-type` and `(5, 2·1)`; a stubborn leaf may need mod 16 — §5).

**Necessity engine** (−1 leaves): `¬IsHilbertSolvable` from a mod-`2^k` obstruction, via
(i) *integralization* — scale a nontrivial `ℚ₂` triple by `2^N` into `ℤ₂` (homogeneity),
(ii) *primitivity descent* — if all of `x,y,z` are non-units then all are `2∣·`
(`PadicInt.norm_lt_one_iff_dvd`, zero included), halve and recurse on the `ℕ`-measure
`Σ (if c = 0 then 0 else c.valuation.toNat)` (strictly decreases: some coordinate is nonzero,
its valuation drops by 1, zeros stay zero; `Nat.strong_induction_on`),
(iii) *mod transfer* — push the primitive `ℤ₂` equation through the ring hom `toZModPow k`
(`IsUnit.map` preserves the odd coordinate), contradicting a `decide`-checked
`∀ x y z : ZMod (2^k), (IsUnit x ∨ IsUnit y ∨ IsUnit z) → A·x² + B·y² ≠ z²` (512 triples at
`k = 3`; `IsUnit` on `ZMod` is decidable).

**Sufficiency engine** (+1 leaves): glue `hilbertSymbol_eq_one_of_value` — if
`a·x² + b·y² = (w : ℚ₂)` with `w : ℤ_[2]`, `toZModPow 3 w = 1`, then `w = t²` (Hensel), `t ≠ 0`,
so `(x, y, t)` solves it.  Witness values are unit sums like `u + 4v` whose mod-8 residue is
computed from the leaf's residue hypotheses (`2·u` mod 16 is determined by `u` mod 8 — the one
sub-lemma this needs).

## 2. Verified ingredient inventory (2026-07-09)

**Current `GQ2/HilbertSymbol.lean`** (100 lines, imports Mathlib only — upstream of Axioms ✓):
`IsHilbertSolvable` (:40), `signOf` (:44), `hilbertSymbol` (:48, classical `if`),
`epsResidue`/`omegaResidue` (:61/:64, via `ZMod.val`), `ε`/`ω` (:67/:70, via `toZModPow 3`),
`toZModPow_neg_one`, `ε_neg_one`, `ω_neg_one`, `unit2` (:94), `unitCoe` (:97).

**Recoverable verbatim from git** (pruned 2026-07-08 as then-unconsumed, commit `2a238af`;
`git show 2a238af^:GQ2/HilbertSymbol.lean`, 184 lines — all proofs definition-level
`ring`/`tauto`/`field_simp`/`decide`, confirmed self-contained):
`isHilbertSolvable_comm`, `isHilbertSolvable_self_neg`, `isHilbertSolvable_mul_sq_left`,
`hilbertSymbol_comm`, `hilbertSymbol_self_neg`, `hilbertSymbol_mul_sq_left`,
`epsResidue_mul_of_isUnit`, `omegaResidue_mul_of_isUnit`, `ε_mul`, `ω_mul`
(needed for the (1,1)-family bookkeeping!), `epsResidue_table`, `omegaResidue_table`.
Restore into the **new** file (same namespace, no clashes — the originals are deleted).

**Mathlib pins** (against the pinned revision):
| decl | location | role |
|---|---|---|
| `hensels_lemma` (`‖F.aeval a‖ < ‖F.derivative.aeval a‖^2 → ∃ z, F.aeval z = 0 ∧ …`) | `NumberTheory/Padics/Hensel.lean:458` | square criterion at `F = X² − C w`, `a = 1` |
| `PadicInt.ker_toZModPow` / `norm_le_pow_iff_mem_span_pow` | `RingHoms.lean:457` / `PadicIntegers.lean:466` | `toZModPow 3 w = 1 ⟺ ‖w−1‖ ≤ 2⁻³` |
| `PadicInt.isUnit_iff : IsUnit z ↔ ‖z‖ = 1` | `PadicIntegers.lean:366` | unit bookkeeping |
| `PadicInt.norm_lt_one_iff_dvd` (name to re-confirm) | `PadicIntegers.lean` | non-unit ⟺ `2 ∣ ·` (descent) |
| `PadicInt.cast_toZModPow`, `zmod_congr_of_sub_mem_span` | `RingHoms.lean:494/:129` | residue plumbing |
| `Padic.norm_eq_zpow_neg_valuation` | (verified during c2c2) | integralization bound |
| `Subgroup`… not needed here; `IsUnit.map`, `map_pow/add/mul`, `ZMod` decidability | core | mod transfer, `decide` leaves |

Residual pins for B7′-0 — **all resolved 2026-07-09** (`lean_run_code`-verified; exact closers
in `b7prime-tickets.md` §B7′-0): parity cast via `ZMod.intCast_eq_intCast_iff` +
`Int.emod_emod_of_dvd`; the descent primitive is `PadicInt.norm_lt_one_iff_dvd` (it *does*
exist); `decide` runs fast with no `native_decide` at both `ZMod 8` (512) and `ZMod 16` (4096),
and **`IsUnit` is decidable on `ZMod n`** (so `IsUnit.map` transfers directly); Hensel plumbing
`aeval 1 (X²−C w).derivative = 2` and `‖(2:ℤ_[2])‖ = 2⁻¹` (`PadicInt.norm_p`) confirmed.

**Axiom consumers**: `SectionThree.lean` only (+ `AxiomLedger`, the `example` in `Axioms.lean`).
Flip = same-name theorem in namespace `GQ2.HilbertSymbol` inside `Axioms.lean`, zero churn.

## 3. File placement

* `GQ2/DyadicSquares.lean` (NEW, imports Mathlib only): the ℤ₂ square criterion — independently
  reusable (it is the `k = ℚ₂` germ of the B13/B11b unit-filtration work).
* `GQ2/HilbertSymbolDyadic.lean` (NEW, imports `GQ2.HilbertSymbol` + `GQ2.DyadicSquares`):
  restored identities, norm-form layer, engines, leaves, capstone `hilbertSymbol_dyadic'`.
* Both strictly upstream of `Foundations/Axioms.lean` (`HilbertSymbol.lean` imports Mathlib
  only) ⟹ the flip is the B11/B12 pattern: `Axioms.lean` imports the new file and re-declares
  `theorem hilbertSymbol_dyadic … := HilbertSymbolDyadic…`; the `example ((-1,-1)₂ = -1)`
  faithfulness check stays, now a consequence of a theorem.

## 4. Increments

### B7′-0 — residual recon (O, ¼ session)
The four residual pins of §2 (cast lemma, dvd-name, `decide` timing, `Polynomial.derivative`
plumbing).  Everything else was pinned during planning (this document).

### B7′-1 — `GQ2/DyadicSquares.lean` (O, ½–1 session)
```lean
theorem isSquare_of_toZModPow_eq_one {w : ℤ_[2]} (hw : PadicInt.toZModPow 3 w = 1) : IsSquare w
theorem toZModPow_sq_eq_one {t : ℤ_[2]} (ht : IsUnit t) : PadicInt.toZModPow 3 (t ^ 2) = 1
theorem exists_unit_sq_eq {u v : ℤ_[2]ˣ}
    (h : PadicInt.toZModPow 3 (u : ℤ_[2]) = PadicInt.toZModPow 3 (v : ℤ_[2])) :
    ∃ w : ℤ_[2]ˣ, u = v * w ^ 2
```
First: `hensels_lemma` at `F := X² − C w`, `a := 1` (`‖1 − w‖ ≤ 2⁻³ < ‖2‖² = 2⁻²`); root is a
unit (`‖z‖² = ‖w‖ = 1`).  Second: `t` odd ⟹ `t² ≡ 1 (mod 8)` (compute in `ZMod 8`: image of `t`
is a unit; `decide` over the 4 odd residues).  Third: apply the first to `u * v⁻¹` (residue `1`
by multiplicativity), upgrade the root to `ℤ_[2]ˣ`.

### B7′-2 — identities + norm-form layer (O, ¾–1 session)
In `GQ2/HilbertSymbolDyadic.lean`, namespace `GQ2.HilbertSymbol`:
1. **Restore** the twelve pruned declarations (§2) verbatim; add
   `hilbertSymbol_mul_sq_right` (via `comm`) and `hilbertSymbol_isSquare_left`
   (`a = c²` ⟹ witness `(1, 0, c)`).
2. **Norm-form layer**: `isHilbertSolvable_iff` (`↔ IsSquare a ∨ ∃ s t, b = s² − a t²`,
   `a ≠ 0`), Brahmagupta (`ring`), `hilbertSymbol_neg_mul_right : (a, -(a*b)) = (a, b)`.
3. **Parity reduction** `symbol_zpow_reduce` (`unit2^α = unit2^(α%2) * (unit2^(α/2))²`,
   `Int.emod_add_ediv` + `zpow_add`) and the residue-dispatch helper
   (`toZModPow 3 ↑u` is a unit of `ZMod 8`, hence `∈ {1,3,5,7}` by `decide` + `rcases`).
Sequencing: item 1 needs nothing; items 2–3 are independent of B7′-1 except the final dispatch.

### B7′-3 — necessity engine (O, 1–1½ sessions)
1. `exists_int_triple` (integralization; ~25 ln) and `exists_primitive_triple` (the descent;
   design in §1, ~60 ln — the fiddliest brick of the lane).
2. `not_isHilbertSolvable_of_mod (A B : ℤ_[2]) (k) (h : ∀ x y z : ZMod (2^k), (IsUnit x ∨
   IsUnit y ∨ IsUnit z) → toZModPow k A * x^2 + toZModPow k B * y^2 ≠ z^2) :
   ¬ IsHilbertSolvable (A : ℚ_[2]) (B : ℚ_[2])` — chains 1 + `IsUnit.map` + ring-hom transfer.
3. The **11 −1-leaves**, each `decide` at `k = 3` (residue hypotheses pin `toZModPow 3 A`;
   `2·v mod 16` from `v mod 8` where needed); coercion seams via one simp lemma
   `((unitCoe u : ℚ_[2]ˣ) : ℚ_[2]) = ((u : ℤ_[2]) : ℚ_[2])`.

### B7′-4 — sufficiency engine (O, ½ session; ∥ B7′-3)
`hilbertSymbol_eq_one_of_value` glue (§1) + the **7 witness leaves** + the `u₀ = 1` freebie
family via `hilbertSymbol_isSquare_left` ∘ `isSquare_of_toZModPow_eq_one` ∘ `unitCoe`-push.

### B7′-5 — assembly, capstone, flip (O, ¾ session + **user census gate**)
1. Dispatch pyramid: parity split (R1) → `(1,0)` by `comm` → `(1,1)` by
   `hilbertSymbol_neg_mul_right` + square-invariance + `ε_mul/ω_mul/ε_neg_one/ω_neg_one`
   (`ε² = ε` by `decide`) → residue `rcases` into the 18 leaves + freebies; RHS evaluated by
   `decide` at known residues.  Capstone `hilbertSymbol_dyadic'` with the **exact** axiom
   statement; `lean_verify` = std-3.
2. Census flip (B11/B12 pattern, coordinate with the in-flight census state):
   `Axioms.lean` axiom → same-name theorem; `EXPECTED_AXIOMS` −1 + history note;
   `AxiomLedger.bAxioms`; live docs (`literature-axioms.md` B7′ row → discharged,
   one-pager, `tickets.md` census notes); regenerate `atlas-audit.md`
   (`lake exe atlas graph-data -o atlas-graph.json && python3 scripts/atlas_audit.py
   atlas-graph.json`); spot `lean_verify` on the `SectionThree.lean` consumer (B7′ must vanish
   from its trace, nothing else may change).

## 5. Risks

* **A −1 leaf surviving mod 8** (needs mod 16): `(ZMod 16)³ = 4096` triples — plain `decide`
  should still be fine; if a leaf needed mod 32 (not expected — Serre's table is a mod-8
  statement), split that leaf over mod-16 residue hypotheses instead of enlarging the modulus.
  `native_decide` is banned by the guard; never reach for it.
* **Descent recursion friction** (junk values, measure): design fixed in §1 (dvd-based, zeros
  handled uniformly, `ℕ`-measure); escalate to F only if it fights for > ½ session.
* **Hensel plumbing**: `hensels_lemma` is `Polynomial`-valued (`aeval`); computing
  `(X² − C w).derivative` and its norms is minor but fiddly; `norm_num`-style norm facts
  (`‖(2 : ℤ_[2])‖ = 2⁻¹`) exist in Mathlib.
* **Coercion seams** (`ℤ_[2]ˣ → ℤ_[2] → ℚ_[2]` vs `unitCoe`, `unit2`): one simp-lemma layer,
  written once in B7′-3.3.

## 6. Out of scope

B11a (the norm criterion over all finite dyadic `k`) — B7′ is its `k = ℚ₂`, cup-free shadow and
the `DyadicSquares` + norm-form layers here will be reusable there, but nothing in this lane
touches cohomology.  B13/B11b: separate lanes (share `DyadicSquares`).  No edits to
`GQ2/HilbertSymbol.lean` or any shared file before the flip.
