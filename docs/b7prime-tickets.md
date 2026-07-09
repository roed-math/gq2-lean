# B7′ discharge — ticket board  (prove `hilbertSymbol_dyadic`, census −1)

**Status (2026-07-09): planned, not started — B7′-0 is ready to run.**  Design was fixed during
the planning session (Fable pass, this board + plan): route selection (norm-form identity
`(a,b) = (a,−ab)` to kill the `(2u,2v)` family instead of a mod-16 leaf blowup), leaf shape
(abstract mod-8 residue hypotheses, no unit literals), and the primitivity-descent design.  The
census is in flux (B2 + B12 removal landed 2026-07-09 → 13); **B7′-5 decrements whatever the
census is at flip time, gated on explicit user approval.**

Route, inventory, and leaf tables: [`b7prime-proof-plan.md`](b7prime-proof-plan.md) (§ refs
below).  Conventions as on [`tickets.md`](tickets.md) — **Model**: **F** = Fable (design-heavy),
**O** = Opus (well-specified), **F→O** = Fable design then Opus close.  **Gates for every
ticket**: own-file `lake build`; `lean_verify` = exactly `{propext, Classical.choice,
Quot.sound}` on every new declaration (no B-axioms anywhere in this lane); **no
`native_decide`** (guard-enforced — plain `decide` only, moduli chosen small);
`scripts/check_axioms.sh`; stage only your own files and print the staged set.  Development in
two new files only — `GQ2/DyadicSquares.lean`, `GQ2/HilbertSymbolDyadic.lean` — both upstream
of `Foundations/Axioms.lean`; **do not edit `GQ2/HilbertSymbol.lean`** (shared).

| # | St | Model | Ticket | Est. | Deps |
|---|----|-------|--------|------|------|
| B7′-0 | ☑ 07-09 | O | Residual recon: 4 pins (cast lemma, dvd name, `decide` timing, `Polynomial` plumbing) | ¼ | — |
| B7′-1 | ☑ 07-09 | O | `DyadicSquares.lean`: the mod-8 square criterion (Hensel) | ½–1 | B7′-0 |
| B7′-2 | ⬜ | O | Identities restore (git) + norm-form/Brahmagupta + parity reduction | ¾–1 | B7′-0 (final dispatch also B7′-1) |
| B7′-3 | ⬜ | O | Necessity engine: integralize + descent + mod transfer + 11 `decide` leaves | 1–1½ | B7′-1 ∧ B7′-2 |
| B7′-4 | ⬜ | O | Sufficiency engine: value glue + 7 witness leaves + square-left freebies | ½ | B7′-1 ∧ B7′-2 |
| B7′-5 | ⬜ | O | Assembly pyramid + capstone + census flip (**user gate**) | ¾ | B7′-3 ∧ B7′-4 |

Est. in lane-sessions (~½–1 day each).  **B7′-3 ∥ B7′-4**; B7′-1 ∥ B7′-2 (except the dispatch
helper).  Total ≈ **4–5½ lane-sessions** (~2 lane-days at swarm cadence).

---

## B7′-0 — residual recon  ☑ done 2026-07-09  (all four pins resolved, `lean_run_code`-verified)

**Go/no-go: GO — no surprises; the route is fully de-risked.**  Turnkey results for B7′-1/2/3:

1. **Parity cast** ✓ — term-mode, no fallback needed:
   ```lean
   ((α % 2 : ℤ) : ZMod 2) = (α : ZMod 2) :=
     (ZMod.intCast_eq_intCast_iff _ _ _).mpr (Int.emod_emod_of_dvd α (dvd_refl 2))
   ```
   (`show (α%2) % (2:ℤ) = α % 2 by omega` also closes the `ModEq`, if the defeq ever balks.)
2. **Descent primitive** ✓ — exists (local_search missed it, loogle caught it):
   `PadicInt.norm_lt_one_iff_dvd (x : ℤ_[p]) : ‖x‖ < 1 ↔ ↑p ∣ x`
   (`PadicIntegers.lean`); the `(↑2 : ℤ_[2]) ∣ x` vs `(2:ℤ_[2]) ∣ x` cast closes by `norm_num`.
   Siblings for the `ℤ`/`ℕ`-cast coordinates: `norm_int_lt_one_iff_dvd`, `norm_natCast_lt_one_iff`.
3. **`decide` timing** ✓ — **both** primitivity predicates decide fast with **no timeout, no
   `native_decide`**, at *both* moduli:
   * `∀ x y z : ZMod 8,  (¬2∣x ∨ ¬2∣y ∨ ¬2∣z) → 3*x^2 + 7*y^2 ≠ z^2` — `by decide` ✓ (512)
   * same with `(IsUnit x ∨ IsUnit y ∨ IsUnit z)` — `by decide` ✓ (**`IsUnit` is decidable on
     `ZMod n`** — so the transfer can carry `IsUnit.map` hypotheses directly, no dvd rephrasing)
   * `ZMod 16` (4096 triples) — `by decide` ✓ (the fallback modulus is confirmed viable)
   * side-benefit: `(3,7)` is confirmed a **genuine mod-8 −1 leaf** (hand-check ✓ too).
4. **Hensel plumbing** ✓:
   * `aeval (1:ℤ_[2]) (X^2 - C w).derivative = 2` — `by simp; norm_num`
   * `‖(2 : ℤ_[2])‖ = 2⁻¹` — `rw [show (2:ℤ_[2]) = ((2:ℕ):ℤ_[2]) by push_cast; ring,
     PadicInt.norm_p]; norm_num`
   (`hensels_lemma` at `F := X² − C w`, `a := 1`: `‖1−w‖ ≤ 2⁻³ < 2⁻² = ‖F′(1)‖²` when
   `toZModPow 3 w = 1`; root is a unit by `‖z‖² = ‖w‖ = 1`.)

*Model note*: O — done; nothing invalidated the route.  Prior planning pins stand
(`hensels_lemma` `Hensel.lean:458`, `ker_toZModPow`/`isUnit_iff`/`cast_toZModPow`,
pruned-lemma recovery at `git show 2a238af^:GQ2/HilbertSymbol.lean`).

## B7′-1 — `GQ2/DyadicSquares.lean`  ☑ done 2026-07-09 (commit pending)

Delivered (all std-3, `lake build GQ2.DyadicSquares` green 8583 jobs, guard all-pass at
census 13):
- `isSquare_of_toZModPow_eq_one {w} (hw : toZModPow 3 w = 1) : IsSquare w` — Hensel at
  `F = X² − C w`, `a = 1`.  Norm bound `‖w−1‖ ≤ 2⁻³` via
  `(norm_le_pow_iff_mem_span_pow (w−1) 3).mpr (… ← ker_toZModPow)`; `hnorm` closed by
  `lt_of_le_of_lt hbound (by norm_num)` against `‖2‖² = 2⁻²` (`norm_p`); root extracted with
  `hz' : z²−w = 0` ⟹ `linear_combination -hz'`.
- `toZModPow_sq_eq_one {t} (ht : IsUnit t) : toZModPow 3 (t²) = 1` — `map_pow` +
  `(by decide : ∀ x : ZMod (2^3), IsUnit x → x² = 1) _ (ht.map _)`.
- `exists_unit_sq_of_toZModPow_eq_one {m : ℤ₂ˣ} : toZModPow 3 ↑m = 1 → ∃ w, m = w²`
  (helper: `isUnit_of_mul_isUnit_left` upgrades the `IsSquare` root to a unit).
- `exists_unit_sq_eq {u v : ℤ₂ˣ} : toZModPow 3 ↑u = toZModPow 3 ↑v → ∃ w, u = v·w²` — the
  square-class reduction B7′-2 consumes (units-algebra closer
  `mul_comm/mul_assoc/inv_mul_cancel/mul_one`, **not** `group`: `ℤ₂ˣ` is commutative and
  `group` doesn't use it).

Imports Mathlib only; upstream of Axioms ✓; independently reusable (ℚ₂-germ of B13/B11b).

## B7′-2 — identities + norm-form layer  (O, ¾–1 session)

Plan §4-B7′-2, in `GQ2/HilbertSymbolDyadic.lean` (namespace `GQ2.HilbertSymbol`):
1. **Restore verbatim from git** (`2a238af^`): `isHilbertSolvable_comm`/`_self_neg`/
   `_mul_sq_left`, `hilbertSymbol_comm`/`_self_neg`/`_mul_sq_left`,
   `epsResidue_mul_of_isUnit`, `omegaResidue_mul_of_isUnit`, `ε_mul`, `ω_mul`,
   `epsResidue_table`, `omegaResidue_table` — once-green, definition-level proofs.
   Add `hilbertSymbol_mul_sq_right` (via `comm`), `hilbertSymbol_isSquare_left`.
2. Norm-form characterization `isHilbertSolvable_iff` + Brahmagupta (`ring`) +
   **`hilbertSymbol_neg_mul_right : (a, -(a*b)) = (a, b)`** — the (1,1)-family killer.
3. Parity reduction `symbol_zpow_reduce` + the residue-dispatch helper
   (`toZModPow 3 ↑u ∈ {1,3,5,7}`).

*Model note*: O — half the ticket is a restoration job; the new mathematics (norm-form ⟺,
Brahmagupta) is `rcases` + `ring` at the definition.  The ε/ω-bookkeeping identity for the
(1,1) reduction is paper-verified in plan §1 (exponent algebra in `𝔽₂`).

## B7′-3 — necessity engine  (O, 1–1½ sessions)

Plan §4-B7′-3: `exists_int_triple` (clear denominators by `2^N`, homogeneity),
`exists_primitive_triple` (**the fiddliest brick** — all-non-unit ⟹ all `2∣·` ⟹ halve;
`ℕ`-measure `Σ (if c = 0 then 0 else c.valuation.toNat)`, `Nat.strong_induction_on`; design
written in plan §1), `not_isHilbertSolvable_of_mod` (ring-hom transfer + `IsUnit.map`), the
coercion simp layer, then the **11 −1-leaves** by `decide` at `ZMod 8`.

*Model note*: O.  **F-escalation triggers**: (a) the descent recursion fights Lean for more
than ~½ session (junk-value or termination friction — the design dodges both, but this is
where it would surface); (b) a leaf's mod-8 `decide` is *true-but-insufficient* (the
obstruction needs mod 16): switch that leaf to `k = 4`; if a leaf resists mod 16, stop and
escalate — that would contradict the classical table and means a statement-shape error.

## B7′-4 — sufficiency engine  (O, ½ session; ∥ B7′-3)

Plan §4-B7′-4: `hilbertSymbol_eq_one_of_value` (value `≡ 1 (mod 8)` ⟹ Hensel root `t` ⟹
`(x, y, t)` solves; `z ≠ 0` gives nontriviality), the **7 explicit-witness leaves**
(witnesses `(1,1)/(1,2)/(2,1)`, values `9/17/25/33` — table in plan §1), and the `u₀ = 1`
freebie family.  Needs the one sub-lemma `2u mod 16` from `u mod 8` for the `(u, 2v)` values.

*Model note*: O — witnesses are pre-computed in the plan; each leaf is `norm_num`/`decide`
arithmetic feeding one glue lemma.

## B7′-5 — assembly + capstone + census flip  (O, ¾ session; **user-approval gate**)

Plan §4-B7′-5: the dispatch pyramid (parity → `comm` → `neg_mul_right` for (1,1) with
`ε_mul/ω_mul/ε_neg_one/ω_neg_one` + `ε² = ε` — paper-checked; → residue `rcases` → leaves),
capstone `hilbertSymbol_dyadic'` with the **byte-exact** axiom statement, `lean_verify` std-3.
Then the flip (B11/B12 pattern): `Axioms.lean` same-name theorem in namespace
`GQ2.HilbertSymbol` (the `example (-1,-1)₂ = -1` stays, now derived); `EXPECTED_AXIOMS` −1 +
history note; `AxiomLedger.bAxioms`; live docs rows (B7′ → *discharged, proved in-repo*, keep
the Serre citation); regenerate `atlas-audit.md`; spot `lean_verify` on `SectionThree.lean`
consumers (B7′ vanishes from traces, e.g. `prop_8_9` / `thm_4_2` cones shrink by one leaf).
Coordinate: rebase on the census state at flip time (B2/B12 removal was in flight when this
board was written); quiet tree; archive this board + plan to `docs/orchestration/` per the
B12 precedent.

*Model note*: O — mechanical; the gates are procedural (user approval, quiet tree,
four-shared-file blast radius).
