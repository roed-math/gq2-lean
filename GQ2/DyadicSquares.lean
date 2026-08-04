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

/-- A controlled version of the dyadic square criterion.  A unit which is `1` modulo
`2^(n+2)` has a square root which is itself `1` modulo `2^(n+1)`.

Writing `m = 1 + 2^(n+2) a`, solve
`b + 2^n b² = a` by Hensel at the approximate root `b = a`.  Its derivative is odd, while
the error `2^n a²` is even.  Then `w = 1 + 2^(n+1)b` has the required properties. -/
theorem exists_deep_unit_sq {n : ℕ} (hn : 2 ≤ n) {m : ℤ_[2]ˣ}
    (hm : toZModPow (n + 2) (m : ℤ_[2]) = 1) :
    ∃ w : ℤ_[2]ˣ, m = w ^ 2 ∧ toZModPow (n + 1) (w : ℤ_[2]) = 1 := by
  have hmem : (m : ℤ_[2]) - 1 ∈ RingHom.ker (toZModPow (n + 2) : ℤ_[2] →+* ZMod (2 ^ (n + 2))) := by
    rw [RingHom.mem_ker, map_sub, map_one, hm, sub_self]
  rw [ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  let F : Polynomial ℤ_[2] :=
    X + C (((2 : ℕ) : ℤ_[2]) ^ n) * X ^ 2 - C a
  have hval : aeval a F = (((2 : ℕ) : ℤ_[2]) ^ n) * a ^ 2 := by
    simp [F]
  have hder : aeval a F.derivative = 1 + (((2 : ℕ) : ℤ_[2]) ^ (n + 1)) * a := by
    simp [F, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_mul, Polynomial.derivative_pow]
    ring
  have hdermod : toZModPow 1 (aeval a F.derivative) = 1 := by
    rw [hder, map_add, map_one, map_mul, map_pow]
    have htwo : toZModPow (p := 2) 1 (((2 : ℕ) : ℤ_[2])) = 0 := by
      rw [map_natCast]
      decide
    rw [htwo, zero_pow (by omega), zero_mul, add_zero]
  have hderunit : IsUnit (aeval a F.derivative) := by
    by_contra hu
    have hmax : aeval a F.derivative ∈ IsLocalRing.maximalIdeal ℤ_[2] :=
      (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [PadicInt.maximalIdeal_eq_span_p] at hmax
    have hker : aeval a F.derivative ∈ RingHom.ker (toZModPow (p := 2) 1) := by
      rw [ker_toZModPow, pow_one]
      exact hmax
    rw [RingHom.mem_ker, hdermod] at hker
    exact (by decide : (1 : ZMod (2 ^ 1)) ≠ 0) hker
  have herror : ‖aeval a F‖ < ‖aeval a F.derivative‖ ^ 2 := by
    rw [PadicInt.isUnit_iff.mp hderunit, one_pow, hval]
    have htwo : ‖(((2 : ℕ) : ℤ_[2]))‖ = (1 / 2 : ℝ) := by
      rw [PadicInt.norm_p]
      norm_num
    have hanorm : ‖a‖ ^ 2 ≤ (1 : ℝ) :=
      pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one a)
    calc
      ‖(((2 : ℕ) : ℤ_[2]) ^ n) * a ^ 2‖ = (1 / 2 : ℝ) ^ n * ‖a‖ ^ 2 := by
        rw [norm_mul, norm_pow, norm_pow, htwo]
      _ ≤ (1 / 2 : ℝ) ^ n * 1 :=
        mul_le_mul_of_nonneg_left hanorm (pow_nonneg (by norm_num) n)
      _ < 1 := by
        simpa only [mul_one] using
          (pow_lt_one₀ (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by omega))
  obtain ⟨b, hb, -⟩ := hensels_lemma (F := F) (a := a) herror
  have hb' : b + (((2 : ℕ) : ℤ_[2]) ^ n) * b ^ 2 = a := by
    have := hb
    simp [F] at this
    linear_combination this
  let r : ℤ_[2] := 1 + (((2 : ℕ) : ℤ_[2]) ^ (n + 1)) * b
  have hrmodone : toZModPow 1 r = 1 := by
    dsimp only [r]
    rw [map_add, map_one, map_mul, map_pow]
    have htwo : toZModPow (p := 2) 1 (((2 : ℕ) : ℤ_[2])) = 0 := by
      rw [map_natCast]
      decide
    rw [htwo, zero_pow (by omega), zero_mul, add_zero]
  have hrunit : IsUnit r := by
    by_contra hu
    have hmax : r ∈ IsLocalRing.maximalIdeal ℤ_[2] := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [PadicInt.maximalIdeal_eq_span_p] at hmax
    have hker : r ∈ RingHom.ker (toZModPow (p := 2) 1) := by
      rw [ker_toZModPow, pow_one]
      exact hmax
    rw [RingHom.mem_ker, hrmodone] at hker
    exact (by decide : (1 : ZMod (2 ^ 1)) ≠ 0) hker
  let w : ℤ_[2]ˣ := hrunit.unit
  refine ⟨w, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hrunit.unit_spec]
    dsimp only [r]
    calc
      (m : ℤ_[2]) = 1 + (((2 : ℕ) : ℤ_[2]) ^ (n + 2)) * a := by
        linear_combination ha
      _ = (1 + (((2 : ℕ) : ℤ_[2]) ^ (n + 1)) * b) ^ 2 := by
        rw [← hb']
        simp only [pow_add]
        ring
  · rw [hrunit.unit_spec]
    dsimp only [r]
    rw [map_add, map_one, map_mul, map_pow]
    have htwo : toZModPow (n + 1) (((2 : ℕ) : ℤ_[2])) ^ (n + 1) = 0 := by
      rw [map_natCast, ← Nat.cast_pow]
      exact ZMod.natCast_self _
    rw [htwo, zero_mul, add_zero]

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
