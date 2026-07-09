import GQ2.HilbertSymbol

/-!
# B7′-2 — elementary identities, the norm-form layer, and parity reduction

This file is the **B7′-2 deliverable** of the `hilbertSymbol_dyadic` axiom-discharge initiative
(board `docs/b7prime-tickets.md`, plan `docs/b7prime-proof-plan.md`, §4-B7′-2).  It supplies, in
namespace `GQ2.HilbertSymbol`, the elementary Hilbert-symbol algebra the later engines
(B7′-3/4/5) rely on:

1. **Restored elementary identities** — twelve once-green, definition-level theorems pruned on
   2026-07-08 (commit `2a238af`) as then-unconsumed, restored here verbatim-modulo-nothing (the
   base definitions in `GQ2/HilbertSymbol.lean` are unchanged): the symmetry / self-negation /
   square-class lemmas for `IsHilbertSolvable` and `hilbertSymbol`, and the `ε`/`ω` residue
   homomorphism + table facts.  Added: `hilbertSymbol_mul_sq_right` (square-class invariance on
   the right, via `comm`) and `hilbertSymbol_isSquare_left` (a square first slot ⇒ symbol `1`).
2. **The norm-form characterization** `isHilbertSolvable_iff` (`↔ IsSquare a ∨ b ∈ {s² − a t²}`),
   the **Brahmagupta identity** (the norm set is multiplicatively closed), and the key
   **`hilbertSymbol_neg_mul_right : (a, -(a·b)) = (a, b)`** — the elementary identity that collapses
   the `(1,1)` parity family onto `(0,1)`, so the leaves live at mod 8 (no mod-16 blowup).
3. **Parity reduction** `symbol_zpow_reduce` (`2^α = 2^(α%2)·(2^(α/2))²`) and the residue-dispatch
   helper `toZModPow_unit_mem` (`u mod 8 ∈ {1,3,5,7}`), which feed the final leaf `rcases`.

**Placement.**  It imports `GQ2.HilbertSymbol` only (Mathlib-only, upstream of
`Foundations/Axioms.lean`), keeping the eventual flip (B7′-5) the zero-churn B11/B12 pattern.  The
`GQ2.DyadicSquares` import (B7′-1's Hensel square criterion) is **not** needed here and is deferred
to B7′-3/4, which add it to this file's header when they land the necessity/sufficiency engines.
-/

namespace GQ2.HilbertSymbol

open scoped Classical

/-! ## Restored elementary identities (definition-level; from `2a238af^`) -/

/-- The defining locus is symmetric: swap the roles of `X` and `Y`. -/
theorem isHilbertSolvable_comm (a b : ℚ_[2]) :
    IsHilbertSolvable a b ↔ IsHilbertSolvable b a := by
  constructor <;>
  · rintro ⟨x, y, z, hne, heq⟩
    exact ⟨y, x, z, by tauto, by rw [← heq]; ring⟩

/-- `a X² + (-a) Y² = Z²` has the nontrivial solution `(1, 1, 0)`. -/
theorem isHilbertSolvable_self_neg (a : ℚ_[2]) : IsHilbertSolvable a (-a) :=
  ⟨1, 1, 0, Or.inl one_ne_zero, by ring⟩

/-- Rescaling the first slot by a nonzero square does not change the locus (`X ↦ c X`). -/
theorem isHilbertSolvable_mul_sq_left (a b : ℚ_[2]) {c : ℚ_[2]} (hc : c ≠ 0) :
    IsHilbertSolvable (a * c ^ 2) b ↔ IsHilbertSolvable a b := by
  constructor
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨c * x, y, z, ?_, by rw [← heq]; ring⟩
    rcases hne with h | h | h
    · exact Or.inl (mul_ne_zero hc h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨x / c, y, z, ?_, by rw [← heq]; field_simp⟩
    rcases hne with h | h | h
    · exact Or.inl (div_ne_zero h hc)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- **Symmetry** of the Hilbert symbol: `(a, b)₂ = (b, a)₂`. -/
theorem hilbertSymbol_comm (a b : ℚ_[2]ˣ) : hilbertSymbol a b = hilbertSymbol b a := by
  rw [hilbertSymbol, hilbertSymbol]
  by_cases h : IsHilbertSolvable (a : ℚ_[2]) (b : ℚ_[2])
  · rw [if_pos h, if_pos ((isHilbertSolvable_comm _ _).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((isHilbertSolvable_comm _ _).mpr hc))]

/-- `(a, -a)₂ = 1`. -/
theorem hilbertSymbol_self_neg (a : ℚ_[2]ˣ) : hilbertSymbol a (-a) = 1 := by
  have h : IsHilbertSolvable (a : ℚ_[2]) ((-a : ℚ_[2]ˣ) : ℚ_[2]) := by
    rw [Units.val_neg]; exact isHilbertSolvable_self_neg _
  rw [hilbertSymbol, if_pos h]

/-- **Square-class invariance** in the first slot: `(a c², b)₂ = (a, b)₂`. -/
theorem hilbertSymbol_mul_sq_left (a b c : ℚ_[2]ˣ) :
    hilbertSymbol (a * c ^ 2) b = hilbertSymbol a b := by
  have hcoe : ((a * c ^ 2 : ℚ_[2]ˣ) : ℚ_[2]) = (a : ℚ_[2]) * (c : ℚ_[2]) ^ 2 := by
    push_cast; ring
  rw [hilbertSymbol, hilbertSymbol, hcoe]
  by_cases h : IsHilbertSolvable ((a : ℚ_[2]) * (c : ℚ_[2]) ^ 2) (b : ℚ_[2])
  · rw [if_pos h, if_pos ((isHilbertSolvable_mul_sq_left _ _ c.ne_zero).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((isHilbertSolvable_mul_sq_left _ _ c.ne_zero).mpr hc))]

/-- **Square-class invariance** in the second slot: `(a, b c²)₂ = (a, b)₂` (via `comm`). -/
theorem hilbertSymbol_mul_sq_right (a b c : ℚ_[2]ˣ) :
    hilbertSymbol a (b * c ^ 2) = hilbertSymbol a b := by
  rw [hilbertSymbol_comm a (b * c ^ 2), hilbertSymbol_mul_sq_left, hilbertSymbol_comm b a]

/-- A **square first slot** gives symbol `1`: witness `(1, 0, c)` with `a = c²`. -/
theorem hilbertSymbol_isSquare_left {a : ℚ_[2]ˣ} (ha : IsSquare (a : ℚ_[2])) (b : ℚ_[2]ˣ) :
    hilbertSymbol a b = 1 := by
  obtain ⟨c, hc⟩ := ha
  have h : IsHilbertSolvable (a : ℚ_[2]) (b : ℚ_[2]) :=
    ⟨1, 0, c, Or.inl one_ne_zero, by rw [hc]; ring⟩
  rw [hilbertSymbol, if_pos h]

/-- On the unit residues `{1,3,5,7} ⊂ ℤ/8`, `ε` is additive. -/
theorem epsResidue_mul_of_isUnit {r s : ZMod 8} (hr : IsUnit r) (hs : IsUnit s) :
    epsResidue (r * s) = epsResidue r + epsResidue s := by
  obtain ⟨r, rfl⟩ := hr
  obtain ⟨s, rfl⟩ := hs
  revert r s
  decide

/-- On the unit residues `{1,3,5,7} ⊂ ℤ/8`, `ω` is additive. -/
theorem omegaResidue_mul_of_isUnit {r s : ZMod 8} (hr : IsUnit r) (hs : IsUnit s) :
    omegaResidue (r * s) = omegaResidue r + omegaResidue s := by
  obtain ⟨r, rfl⟩ := hr
  obtain ⟨s, rfl⟩ := hs
  revert r s
  decide

/-- `ε` is a homomorphism `ℤ₂ˣ → 𝔽₂`: `ε(uv) = ε(u) + ε(v)`. -/
theorem ε_mul (u v : ℤ_[2]ˣ) : ε (u * v) = ε u + ε v := by
  simp only [ε, Units.val_mul, map_mul]
  exact epsResidue_mul_of_isUnit (u.isUnit.map _) (v.isUnit.map _)

/-- `ω` is a homomorphism `ℤ₂ˣ → 𝔽₂`: `ω(uv) = ω(u) + ω(v)`. -/
theorem ω_mul (u v : ℤ_[2]ˣ) : ω (u * v) = ω u + ω v := by
  simp only [ω, Units.val_mul, map_mul]
  exact omegaResidue_mul_of_isUnit (u.isUnit.map _) (v.isUnit.map _)

/-- Residue table for `ε`: `ε ≡ 0` on `{1, 5}` (`≡ 1 mod 4`), `ε ≡ 1` on `{3, 7}` (`≡ 3 mod 4`). -/
theorem epsResidue_table :
    epsResidue 1 = 0 ∧ epsResidue 3 = 1 ∧ epsResidue 5 = 0 ∧ epsResidue 7 = 1 := by
  decide

/-- Residue table for `ω`: `ω ≡ 0` on `{1, 7}` (`≡ ±1 mod 8`), `ω ≡ 1` on `{3, 5}` (`≡ ±3 mod 8`). -/
theorem omegaResidue_table :
    omegaResidue 1 = 0 ∧ omegaResidue 3 = 1 ∧ omegaResidue 5 = 1 ∧ omegaResidue 7 = 0 := by
  decide

/-! ## The norm-form characterization, Brahmagupta, and the `(1,1)`-family reduction

`hilbertSymbol` is `+1` exactly when the ternary form is solvable; solving for `b` when `y ≠ 0`
(and for `a` when `y = 0`) turns this into membership of `b` in the set of norms `{s² − a t²}` from
`ℚ₂(√a)` (or `a` being a square).  The norm set is multiplicatively closed (Brahmagupta), contains
`-a` (`= 0² − a·1²`), and is closed under division by squares — the three facts that make
`(a, -(a·b)) = (a, b)`. -/

/-- **Norm-form characterization**: the form `a X² + b Y² = Z²` has a nontrivial `ℚ₂`-zero iff `a`
is a square or `b` is a norm `s² − a t²` from `ℚ₂(√a)`. -/
theorem isHilbertSolvable_iff (a b : ℚ_[2]) :
    IsHilbertSolvable a b ↔ IsSquare a ∨ ∃ s t : ℚ_[2], b = s ^ 2 - a * t ^ 2 := by
  constructor
  · rintro ⟨x, y, z, hne, heq⟩
    by_cases hy : y = 0
    · left
      subst hy
      have hx : x ≠ 0 := by
        rintro rfl
        have hz : z ^ 2 = 0 := by rw [← heq]; ring
        have hz0 : z = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
        rcases hne with h | h | h
        · exact h rfl
        · exact h rfl
        · exact h hz0
      exact ⟨z / x, by rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx hx)]; linear_combination heq⟩
    · exact Or.inr ⟨z / y, x / y, by field_simp; linear_combination heq⟩
  · rintro (⟨c, hc⟩ | ⟨s, t, hst⟩)
    · exact ⟨1, 0, c, Or.inl one_ne_zero, by rw [hc]; ring⟩
    · exact ⟨t, 1, s, Or.inr (Or.inl one_ne_zero), by rw [hst]; ring⟩

/-- **Brahmagupta**: the norm set `{s² − a t²}` is closed under multiplication. -/
theorem brahmagupta (a s t s' t' : ℚ_[2]) :
    (s ^ 2 - a * t ^ 2) * (s' ^ 2 - a * t' ^ 2)
      = (s * s' + a * t * t') ^ 2 - a * (s * t' + t * s') ^ 2 := by
  ring

/-- **The `(1,1)`-family killer**: `(a, -(a·b))₂ = (a, b)₂`.  Both `-(a·b)` and `b` differ by the
norm `-a`, and the norm set is multiplicatively closed and square-divisible — so `b` is a norm iff
`-(a·b)` is.  This collapses the `(1,1)` parity family onto `(0,1)`, keeping all leaves at mod 8. -/
theorem hilbertSymbol_neg_mul_right (a b : ℚ_[2]ˣ) :
    hilbertSymbol a (-(a * b)) = hilbertSymbol a b := by
  have ha : (a : ℚ_[2]) ≠ 0 := a.ne_zero
  have hcoe : ((-(a * b) : ℚ_[2]ˣ) : ℚ_[2]) = -((a : ℚ_[2]) * (b : ℚ_[2])) := by push_cast; ring
  have key : IsHilbertSolvable (a : ℚ_[2]) ((-(a * b) : ℚ_[2]ˣ) : ℚ_[2])
      ↔ IsHilbertSolvable (a : ℚ_[2]) (b : ℚ_[2]) := by
    rw [isHilbertSolvable_iff, isHilbertSolvable_iff, hcoe]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨s, t, hst⟩
      exact ⟨t, s / a, by field_simp; linear_combination -hst⟩
    · rintro ⟨s, t, hst⟩
      exact ⟨a * t, s, by rw [hst]; ring⟩
  rw [hilbertSymbol, hilbertSymbol]
  by_cases h : IsHilbertSolvable (a : ℚ_[2]) (b : ℚ_[2])
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (key.mp hc)), if_neg h]

/-! ## Parity reduction and residue dispatch -/

/-- **Parity split of the `2`-power slot**: `2^α = 2^(α mod 2) · (2^(α / 2))²`, so the symbol only
sees `α mod 2` after square-class invariance. -/
theorem symbol_zpow_reduce (α : ℤ) :
    unit2 ^ α = unit2 ^ (α % 2) * (unit2 ^ (α / 2)) ^ 2 := by
  rw [← zpow_natCast (unit2 ^ (α / 2)) 2, ← zpow_mul, ← zpow_add]
  congr 1
  push_cast
  omega

/-- **Residue dispatch**: the mod-8 residue of a `2`-adic unit is one of `{1,3,5,7}` — the four
unit residues, over which the leaf `rcases` runs. -/
theorem toZModPow_unit_mem (u : ℤ_[2]ˣ) :
    PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 ∨ PadicInt.toZModPow 3 (u : ℤ_[2]) = 3 ∨
      PadicInt.toZModPow 3 (u : ℤ_[2]) = 5 ∨ PadicInt.toZModPow 3 (u : ℤ_[2]) = 7 := by
  have hu : IsUnit (PadicInt.toZModPow 3 (u : ℤ_[2])) := u.isUnit.map _
  revert hu
  generalize PadicInt.toZModPow 3 (u : ℤ_[2]) = r
  revert r
  decide

end GQ2.HilbertSymbol
