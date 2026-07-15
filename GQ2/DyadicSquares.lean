/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section


/-!
# The dyadic square criterion

Groundwork for the in-repo proof of **B7′** (`hilbertSymbol_dyadic`).  This file is the 2-adic
**square-lifting** input, independent of the Hilbert symbol and reusable (it is the `k = ℚ₂`
germ of the B13/B11b unit-filtration square-class computations).

`ℤ₂ˣ` squares are exactly the units `≡ 1 (mod 8)`:

* `isSquare_of_toZModPow_eq_one` — `w ≡ 1 (mod 8)` ⟹ `w` is a square (Hensel's lemma at
  `X² − w`, base point `1`: `‖1 − w‖ ≤ 2⁻³ < 2⁻² = ‖2‖²`);
* `toZModPow_sq_eq_one` — the converse for units (an odd square is `≡ 1 (mod 8)`);
* `exists_unit_sq_eq` — two units with equal image mod `8` differ by a unit square.

All std-3 (2-adic Hensel + a finite `decide` over `ZMod 8`).
-/

namespace GQ2.DyadicSquares

open PadicInt Polynomial

/-- **A 2-adic integer `≡ 1 (mod 8)` is a square.**  Hensel's lemma applied to `F = X² − w` at
the approximate root `a = 1`: `‖F 1‖ = ‖1 − w‖ ≤ 2⁻³ < 2⁻² = ‖2‖² = ‖F′ 1‖²`. -/
theorem isSquare_of_toZModPow_eq_one {w : ℤ_[2]} (hw : toZModPow 3 w = 1) : IsSquare w := by
  -- `w − 1` lies in the kernel of reduction mod `8`, so `‖w − 1‖ ≤ 2⁻³`.
  have hmem : w - 1 ∈ RingHom.ker (toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) := by
    rw [RingHom.mem_ker, map_sub, map_one, hw, sub_self]
  have hbound : ‖w - 1‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    have h := (norm_le_pow_iff_mem_span_pow (w - 1) 3).mpr (by rwa [← ker_toZModPow])
    simpa using h
  -- Norm of the derivative value `F′ 1 = 2`.
  have hnorm2 : ‖(2 : ℤ_[2])‖ ^ 2 = (2 : ℝ) ^ (-2 : ℤ) := by
    rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by push_cast; ring, norm_p]
    norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := X ^ 2 - C w) (a := 1) (by
    have hval : aeval (1 : ℤ_[2]) (X ^ 2 - C w) = 1 - w := by simp
    have hder : aeval (1 : ℤ_[2]) (X ^ 2 - C w).derivative = 2 := by simp; norm_num
    rw [hval, hder, hnorm2, norm_sub_rev]
    exact lt_of_le_of_lt hbound (by norm_num))
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 - w = 0 := by simpa using hz
  linear_combination -hz'

/-- **The converse for units.**  An odd 2-adic integer squares to `≡ 1 (mod 8)`. -/
theorem toZModPow_sq_eq_one {t : ℤ_[2]} (ht : IsUnit t) : toZModPow 3 (t ^ 2) = 1 := by
  rw [map_pow]
  exact (by decide : ∀ x : ZMod (2 ^ 3), IsUnit x → x ^ 2 = 1) _ (ht.map _)

/-- A unit that is `≡ 1 (mod 8)` is a **unit** square. -/
theorem exists_unit_sq_of_toZModPow_eq_one {m : ℤ_[2]ˣ} (hm : toZModPow 3 (m : ℤ_[2]) = 1) :
    ∃ w : ℤ_[2]ˣ, m = w ^ 2 := by
  obtain ⟨r, hr⟩ := isSquare_of_toZModPow_eq_one hm
  have hru : IsUnit r := isUnit_of_mul_isUnit_left (hr ▸ m.isUnit)
  obtain ⟨w, hw⟩ := hru
  exact ⟨w, Units.ext (by rw [Units.val_pow_eq_pow_val, hw, sq, ← hr])⟩

/-- **Two units equal mod `8` differ by a unit square.**  The square-class reduction driving the
Hilbert-symbol parity/residue dispatch (B7′-2). -/
theorem exists_unit_sq_eq {u v : ℤ_[2]ˣ}
    (h : toZModPow 3 (u : ℤ_[2]) = toZModPow 3 (v : ℤ_[2])) :
    ∃ w : ℤ_[2]ˣ, u = v * w ^ 2 := by
  have hm : toZModPow 3 ((u * v⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [Units.val_mul, map_mul, h, ← map_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, map_one]
  obtain ⟨w, hw⟩ := exists_unit_sq_of_toZModPow_eq_one hm
  exact ⟨w, by rw [← hw, mul_comm v (u * v⁻¹), mul_assoc, inv_mul_cancel, mul_one]⟩

end GQ2.DyadicSquares
