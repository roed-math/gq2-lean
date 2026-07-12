import GQ2.HilbertSymbolDyadic
import GQ2.DyadicSquares

/-!
# B7′-4 — the sufficiency engine and the `+1` witness leaves

The **B7′-4 deliverable** of the `hilbertSymbol_dyadic` axiom-discharge initiative
(board `docs/b7prime-tickets.md`, plan `docs/b7prime-proof-plan.md`, coordination
`docs/b7prime-b34-coordination.md`).  It supplies, in namespace `GQ2.HilbertSymbol`, the `+1`
side of the leaf dispatch: the Hensel **value glue** plus the seven explicit-witness leaves and
the `u ≡ 1 (mod 8)` freebie family.

* `hilbertSymbol_eq_one_of_value` — if `a·x² + b·y²` equals a 2-adic integer `≡ 1 (mod 8)` (hence
  a square `t²` by `DyadicSquares.isSquare_of_toZModPow_eq_one`, `t ≠ 0`), then `(x, y, t)` is a
  nontrivial zero, so `(a, b)₂ = 1`.
* seven witness leaves (`hilbertSymbol_uu_*` for unit·unit `{3,5},{5,5},{5,7}`, `hilbertSymbol_u2v_*`
  for `(u, 2v)` `{3,3},{3,7},{7,1},{7,5}`), each `refine`-ing the glue at the witness/value from
  plan §1;
* `hilbertSymbol_left_one` — `u ≡ 1 (mod 8) ⟹ (u, b)₂ = 1` for any `b`, via
  `hilbertSymbol_isSquare_left` (a unit `≡ 1 (mod 8)` is a square).

**Placement** (per `b7prime-b34-coordination.md`): own new file, imports `GQ2.HilbertSymbolDyadic`
(shared coercion helpers `unit2_coe`/`unitCoe_coe`, and `hilbertSymbol_isSquare_left`) +
`GQ2.DyadicSquares` (Hensel square criterion); namespace `GQ2.HilbertSymbol`; strictly upstream of
`Foundations/Axioms.lean`.  The `−1` necessity leaves are B7′-3 (`HilbertSymbolNecessity.lean`);
the dispatch capstone is B7′-5 (`HilbertSymbolDyadicClose.lean`, downstream of both).

**Residue → leaf map (for B7′-5 dispatch).**  Unit·unit `(u,v)` is `+1` iff not both `∈ {3,7}`:
`u ≡ 1` or `v ≡ 1` → `hilbertSymbol_left_one` (the latter after `hilbertSymbol_comm`); else the
three `hilbertSymbol_uu_*` (with `comm` covering the swaps).  For `(u, 2v)`: `u ≡ 1` →
`hilbertSymbol_left_one`; the `+1` non-`1` cases are exactly `hilbertSymbol_u2v_{33,37,71,75}`.
-/

namespace GQ2.HilbertSymbol

open scoped Classical

open PadicInt

/-- **The Hensel value glue.**  If `a·x² + b·y²` equals a 2-adic integer `w ≡ 1 (mod 8)` — hence a
square `t²` with `t ≠ 0` — then `(x, y, t)` is a nontrivial zero of `a X² + b Y² − Z²`, so the
Hilbert symbol is `+1`. -/
theorem hilbertSymbol_eq_one_of_value {a b : ℚ_[2]ˣ} (x y w : ℤ_[2])
    (hw : toZModPow 3 w = 1)
    (heq : (a : ℚ_[2]) * (x : ℚ_[2]) ^ 2 + (b : ℚ_[2]) * (y : ℚ_[2]) ^ 2 = (w : ℚ_[2])) :
    hilbertSymbol a b = 1 := by
  obtain ⟨t, ht⟩ := DyadicSquares.isSquare_of_toZModPow_eq_one hw
  have hw0 : w ≠ 0 := by intro h; rw [h, map_zero] at hw; exact absurd hw (by decide)
  have ht0 : (t : ℚ_[2]) ≠ 0 := by
    rw [Ne, PadicInt.coe_eq_zero]; intro h; exact hw0 (by rw [ht, h, mul_zero])
  have hsolv : IsHilbertSolvable (a : ℚ_[2]) (b : ℚ_[2]) :=
    ⟨(x : ℚ_[2]), (y : ℚ_[2]), (t : ℚ_[2]), Or.inr (Or.inr ht0), by
      rw [heq, ht]; push_cast; ring⟩
  rw [hilbertSymbol, if_pos hsolv]

/-- `((2 : ℤ₂) : ℚ₂) = 2`.  Mathlib's `PadicInt.coe_natCast`/`coe_intCast` are `norm_cast` lemmas
but there is no `coe_ofNat`, so `push_cast` cannot normalise the `OfNat` numeral coe on its own;
these two feed it explicitly in the witness-leaf value computations. -/
private lemma padic_coe_two : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by norm_cast

/-- `((4 : ℤ₂) : ℚ₂) = 4` (companion of `padic_coe_two`). -/
private lemma padic_coe_four : ((4 : ℤ_[2]) : ℚ_[2]) = 4 := by norm_cast

/-! ## The seven `+1` witness leaves (plan §1) -/

/-- Unit·unit leaf `{3,5}`: witness `(x,y) = (2,1)`, value `4u + v ≡ 1 (mod 8)`. -/
theorem hilbertSymbol_uu_35 {u v : ℤ_[2]ˣ}
    (hu : toZModPow 3 (u : ℤ_[2]) = 3) (hv : toZModPow 3 (v : ℤ_[2]) = 5) :
    hilbertSymbol (unitCoe u) (unitCoe v) = 1 := by
  refine hilbertSymbol_eq_one_of_value 2 1 (4 * (u : ℤ_[2]) + (v : ℤ_[2])) ?_ ?_
  · simp only [map_add, map_mul, map_ofNat, hu, hv]; decide
  · rw [unitCoe_coe, unitCoe_coe]; push_cast [padic_coe_two, padic_coe_four]; ring

/-- Unit·unit leaf `{5,5}`: witness `(1,2)`, value `u + 4v ≡ 1 (mod 8)`. -/
theorem hilbertSymbol_uu_55 {u v : ℤ_[2]ˣ}
    (hu : toZModPow 3 (u : ℤ_[2]) = 5) (hv : toZModPow 3 (v : ℤ_[2]) = 5) :
    hilbertSymbol (unitCoe u) (unitCoe v) = 1 := by
  refine hilbertSymbol_eq_one_of_value 1 2 ((u : ℤ_[2]) + 4 * (v : ℤ_[2])) ?_ ?_
  · simp only [map_add, map_mul, map_ofNat, hu, hv]; decide
  · rw [unitCoe_coe, unitCoe_coe]; push_cast [padic_coe_two, padic_coe_four]; ring

/-- Unit·unit leaf `{5,7}`: witness `(1,2)`, value `u + 4v ≡ 1 (mod 8)`. -/
theorem hilbertSymbol_uu_57 {u v : ℤ_[2]ˣ}
    (hu : toZModPow 3 (u : ℤ_[2]) = 5) (hv : toZModPow 3 (v : ℤ_[2]) = 7) :
    hilbertSymbol (unitCoe u) (unitCoe v) = 1 := by
  refine hilbertSymbol_eq_one_of_value 1 2 ((u : ℤ_[2]) + 4 * (v : ℤ_[2])) ?_ ?_
  · simp only [map_add, map_mul, map_ofNat, hu, hv]; decide
  · rw [unitCoe_coe, unitCoe_coe]; push_cast [padic_coe_two, padic_coe_four]; ring

/-- `(u, 2v)` leaf `{3,3}`: witness `(1,1)`, value `u + 2v ≡ 1 (mod 8)`. -/
theorem hilbertSymbol_u2v_33 {u v : ℤ_[2]ˣ}
    (hu : toZModPow 3 (u : ℤ_[2]) = 3) (hv : toZModPow 3 (v : ℤ_[2]) = 3) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = 1 := by
  refine hilbertSymbol_eq_one_of_value 1 1 ((u : ℤ_[2]) + 2 * (v : ℤ_[2])) ?_ ?_
  · simp only [map_add, map_mul, map_ofNat, hu, hv]; decide
  · rw [unitCoe_coe, Units.val_mul, unit2_coe, unitCoe_coe]; push_cast [padic_coe_two]; ring

/-- `(u, 2v)` leaf `{3,7}`: witness `(1,1)`, value `u + 2v ≡ 1 (mod 8)`. -/
theorem hilbertSymbol_u2v_37 {u v : ℤ_[2]ˣ}
    (hu : toZModPow 3 (u : ℤ_[2]) = 3) (hv : toZModPow 3 (v : ℤ_[2]) = 7) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = 1 := by
  refine hilbertSymbol_eq_one_of_value 1 1 ((u : ℤ_[2]) + 2 * (v : ℤ_[2])) ?_ ?_
  · simp only [map_add, map_mul, map_ofNat, hu, hv]; decide
  · rw [unitCoe_coe, Units.val_mul, unit2_coe, unitCoe_coe]; push_cast [padic_coe_two]; ring

/-- `(u, 2v)` leaf `{7,1}`: witness `(1,1)`, value `u + 2v ≡ 1 (mod 8)`. -/
theorem hilbertSymbol_u2v_71 {u v : ℤ_[2]ˣ}
    (hu : toZModPow 3 (u : ℤ_[2]) = 7) (hv : toZModPow 3 (v : ℤ_[2]) = 1) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = 1 := by
  refine hilbertSymbol_eq_one_of_value 1 1 ((u : ℤ_[2]) + 2 * (v : ℤ_[2])) ?_ ?_
  · simp only [map_add, map_mul, map_ofNat, hu, hv]; decide
  · rw [unitCoe_coe, Units.val_mul, unit2_coe, unitCoe_coe]; push_cast [padic_coe_two]; ring

/-- `(u, 2v)` leaf `{7,5}`: witness `(1,1)`, value `u + 2v ≡ 1 (mod 8)`. -/
theorem hilbertSymbol_u2v_75 {u v : ℤ_[2]ˣ}
    (hu : toZModPow 3 (u : ℤ_[2]) = 7) (hv : toZModPow 3 (v : ℤ_[2]) = 5) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = 1 := by
  refine hilbertSymbol_eq_one_of_value 1 1 ((u : ℤ_[2]) + 2 * (v : ℤ_[2])) ?_ ?_
  · simp only [map_add, map_mul, map_ofNat, hu, hv]; decide
  · rw [unitCoe_coe, Units.val_mul, unit2_coe, unitCoe_coe]; push_cast [padic_coe_two]; ring

/-! ## The `u ≡ 1 (mod 8)` freebie family -/

/-- **Freebie**: a first slot `u ≡ 1 (mod 8)` is a square, so `(u, b)₂ = 1` for every `b`.  Covers
every leaf with `u ≡ 1` in both families (and, after `hilbertSymbol_comm`, every `v ≡ 1`). -/
theorem hilbertSymbol_left_one {u : ℤ_[2]ˣ}
    (hu : toZModPow 3 (u : ℤ_[2]) = 1) (b : ℚ_[2]ˣ) :
    hilbertSymbol (unitCoe u) b = 1 := by
  refine hilbertSymbol_isSquare_left ?_ b
  obtain ⟨t, ht⟩ := DyadicSquares.isSquare_of_toZModPow_eq_one hu
  exact ⟨(t : ℚ_[2]), by rw [unitCoe_coe, ht]; push_cast; ring⟩

end GQ2.HilbertSymbol
