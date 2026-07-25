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
# The orientation cubic root and orientation-value arithmetic  (Roe note §3.3)

Formalises the **arithmetic content** of ⟦prop:orientation⟧ (Proposition 3.3 of the
verification note `paper/roe-presentation-verification.tex`), which computes the canonical
Demushkin orientation `χ_R` of `D_R` on generators via Labute's descent characterisation.
This file verifies the *outputs* of that computation — the cubic root and the unit-group
facts — not the crossed-derivation derivation of the descent equations (eqs.
(charrelation)/(Cx)/(Cs)/(Cy), the note's Labute step).

The note's display eq. (orientationvalues) records the generator values
`(S, X, Y) = (χ_R s, χ_R x, χ_R y)`:
```
Y = -X²,      X³ + 2X² + 1 = 0,      S = -X³ / (X² + X + 1),
```
with `Z³ + 2Z² + 1` having a **unique** root in `ℤ₂ˣ`, and
```
X ≡ 5 (mod 16),      S ≡ 13 (mod 16),      im χ_R = {±1} × (1 + 4ℤ₂).
```

## Main definitions

* `rootX : ℤ_[2]` — the unique 2-adic root `X` of `f(Z) = Z³ + 2Z² + 1`, obtained from
  mathlib's `hensels_lemma` at the approximate root `1` (`‖f 1‖ = ‖4‖ < 1 = ‖f′ 1‖² = ‖7‖²`);
* `Sval : ℤ_[2]` — `S = -X³ · (X²+X+1)⁻¹`, defined through the unit `X²+X+1`;
* `Yval : ℤ_[2]` — `Y = -X²`.

## Main results

* `rootX_isRoot` / `rootX_unique` — `X` is a root and the *only* root of `f` in `ℤ₂`
  (mod-2 analysis: `f ≡ (Z+1)(Z²+Z+1)` and `Z²+Z+1` has no root in `𝔽₂`, so every root is
  `≡ 1 mod 2`, hence inside the Hensel ball `‖· − 1‖ < ‖7‖ = 1` where the root is unique);
* `rootX_toZModPow_four : toZModPow 4 rootX = 5` and `Sval_toZModPow_four = 13` — eq.
  (orientationvalues)'s mod-16 congruences (`decide` over `ZMod 16`; the cubic has the unique
  residue `5` mod `16` and `Sval` is pinned by `Sval_mul_denom`);
* `norm_rootX_sub_one : ‖rootX − 1‖ = 1/4` and `norm_Sval_sub_one : ‖Sval − 1‖ = 1/4` — the
  `v₂ = 2` facts (the "`X`, `S` topologically generate `1 + 4ℤ₂`" input to the descent-depth
  `f = 2` of ⟦cor:abstractD0⟧); packaged as the exact-level forms
  `rootX_sub_one_eq`/`Sval_sub_one_eq` (`· − 1 = 4·unit`) that a downstream
  `zpowZtwo_injective`-style argument (`GQ2/ZtwoPowering.lean`) consumes directly;
* `denom_isUnit`, `rootX_isUnit`, `isUnit_sq_sub_self_sub_one_of_odd` — the unit facts used
  to define `Sval` and to exclude the `Y = +X²` branch downstream.

Cross-checked against the R2 spike's independent 2-adic computation
(`docs/orchestration/roe-r2-spike.md`): `X ≡ 5 (16)`, `S ≡ 13 (16)`, `v₂(X−1)=v₂(S−1)=2`,
and the deeper `X ≡ 21 (mod 32)` recorded here as the `rootX_toZModPow_five` stress test.

All std-3 (2-adic `hensels_lemma` + finite `decide` over `ZMod (2ⁿ)`).
-/

namespace GQ2.Roe

open PadicInt Polynomial

/-! ### Sanity checks feeding the Hensel invocation -/

/-- `f(1) = 1 + 2 + 1 = 4`, the numerator of the Hensel gap `‖f 1‖ = ‖4‖`. -/
theorem f_one_eq_four : (1 : ℤ_[2]) ^ 3 + 2 * (1 : ℤ_[2]) ^ 2 + 1 = 4 := by norm_num

/-! ### Small 2-adic helpers -/

/-- A 2-adic integer with residue `1` mod `2` is a unit (`x ∉ maximalIdeal = span{2}`). -/
private lemma isUnit_of_toZModPow_one_eq_one {x : ℤ_[2]} (h : toZModPow 1 x = 1) : IsUnit x := by
  by_contra hu
  have hmem : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := (IsLocalRing.mem_maximalIdeal _).mpr hu
  rw [PadicInt.maximalIdeal_eq_span_p] at hmem
  have hker : x ∈ RingHom.ker (toZModPow (p := 2) 1) := by
    rw [ker_toZModPow, pow_one]; exact hmem
  rw [RingHom.mem_ker, h] at hker
  exact absurd hker (by decide)

/-- `toZModPow 1 (4) = 0`: the constant `4` lies in `8ℤ₂`'s parent `2ℤ₂`. -/
private lemma toZModPow_one_four : toZModPow (p := 2) 1 (4 : ℤ_[2]) = 0 := by
  simp only [map_ofNat]; decide

/-- `‖(4 : ℤ₂)‖ = 1/4`. -/
private lemma norm_four : ‖(4 : ℤ_[2])‖ = 1 / 4 := by
  rw [show (4 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 2 by push_cast; ring, norm_pow, PadicInt.norm_p]
  norm_num

/-! ### The cubic root `X` -/

/-- **Hensel data for `f(Z) = Z³ + 2Z² + 1`.**  Mathlib's `hensels_lemma` at the approximate
root `1`: `‖f 1‖ = ‖4‖ < 1 = ‖7‖² = ‖f′ 1‖²` (with `f′(1) = 7` a unit).  Bundles the root,
its Hensel-ball membership `‖z − 1‖ < 1`, and ball-uniqueness. -/
theorem hensel_data :
    ∃ z : ℤ_[2], z ^ 3 + 2 * z ^ 2 + 1 = 0 ∧ ‖z - 1‖ < 1 ∧
      ∀ z' : ℤ_[2], z' ^ 3 + 2 * z' ^ 2 + 1 = 0 → ‖z' - 1‖ < 1 → z' = z := by
  set F : Polynomial ℤ_[2] := X ^ 3 + C 2 * X ^ 2 + C 1 with hF
  have hev : ∀ a : ℤ_[2], aeval a F = a ^ 3 + 2 * a ^ 2 + 1 := by
    intro a; simp [hF]
  have hev1 : aeval (1 : ℤ_[2]) F = 4 := by rw [hev]; norm_num
  have hdev : aeval (1 : ℤ_[2]) F.derivative = 7 := by
    rw [hF]
    simp [Polynomial.derivative_add, Polynomial.derivative_C]
    norm_num
  have h7 : ‖(7 : ℤ_[2])‖ = 1 := by
    rw [show (7 : ℤ_[2]) = ((7 : ℕ) : ℤ_[2]) by push_cast; ring, PadicInt.norm_natCast_eq_one_iff]
    decide
  have h4 : ‖(4 : ℤ_[2])‖ < 1 := by
    rw [show (4 : ℤ_[2]) = ((4 : ℕ) : ℤ_[2]) by push_cast; ring, PadicInt.norm_natCast_lt_one_iff]
    decide
  have hnorm : ‖aeval (1 : ℤ_[2]) F‖ < ‖aeval (1 : ℤ_[2]) F.derivative‖ ^ 2 := by
    rw [hev1, hdev, h7, one_pow]; exact h4
  obtain ⟨z, hz, hdist, _, huniq⟩ := hensels_lemma hnorm
  rw [hev] at hz
  rw [hdev, h7] at hdist
  refine ⟨z, hz, hdist, ?_⟩
  intro z' hz' hd'
  exact huniq z' (by rw [hev]; exact hz') (by rw [hdev, h7]; exact hd')

/-- The unique 2-adic root `X = χ_R(x)` of `Z³ + 2Z² + 1`, eq. (orientationvalues). -/
noncomputable def rootX : ℤ_[2] := hensel_data.choose

/-- `X³ + 2X² + 1 = 0` — the middle equation of eq. (orientationvalues). -/
theorem rootX_isRoot : rootX ^ 3 + 2 * rootX ^ 2 + 1 = 0 := hensel_data.choose_spec.1

/-- `X` lies in the Hensel ball `‖X − 1‖ < 1`, i.e. `X ≡ 1 mod 2`. -/
theorem rootX_dist : ‖rootX - 1‖ < 1 := hensel_data.choose_spec.2.1

/-- **Uniqueness of the root.**  Any 2-adic root of `f` equals `X`.  A root `z` satisfies
`z³ ≡ 1 mod 2` (as `2z² ≡ 0`), so `z ≡ 1 mod 2` (the only cube root of `1` in `𝔽₂`); hence
`z` lies in the Hensel ball `‖z − 1‖ < ‖7‖ = 1` where the root is unique. -/
theorem rootX_unique {z : ℤ_[2]} (hz : z ^ 3 + 2 * z ^ 2 + 1 = 0) : z = rootX := by
  have hz1 : toZModPow (p := 2) 1 z = 1 := by
    have h := congrArg (toZModPow (p := 2) 1) hz
    simp only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero] at h
    exact (by decide : ∀ r : ZMod (2 ^ 1), r ^ 3 + 2 * r ^ 2 + 1 = 0 → r = 1) _ h
  have hdist : ‖z - 1‖ < 1 := by
    have hmem : z - 1 ∈ RingHom.ker (toZModPow (p := 2) 1) := by
      rw [RingHom.mem_ker, map_sub, map_one, hz1, sub_self]
    rw [ker_toZModPow] at hmem
    calc ‖z - 1‖ ≤ (2 : ℝ) ^ (-(1 : ℕ) : ℤ) := (norm_le_pow_iff_mem_span_pow (z - 1) 1).mpr hmem
      _ < 1 := by norm_num
  exact hensel_data.choose_spec.2.2 z hz hdist

/-! ### The mod-16 congruence of `X` and derived units -/

/-- `toZModPow 4 X = 5` — eq. (orientationvalues)'s `X ≡ 5 (mod 16)`.  The cubic
`r³ + 2r² + 1 = 0` has the unique solution `r = 5` in `ZMod 16` (`decide`). -/
theorem rootX_toZModPow_four : toZModPow 4 rootX = 5 := by
  have h := congrArg (toZModPow (p := 2) 4) rootX_isRoot
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero] at h
  exact (by decide : ∀ r : ZMod (2 ^ 4), r ^ 3 + 2 * r ^ 2 + 1 = 0 → r = 5) _ h

/-- `X ≡ 1 mod 2` in `ZMod 2` form (residue of the unit `X`). -/
theorem rootX_toZModPow_one : toZModPow 1 rootX = 1 := by
  have h := congrArg (toZModPow (p := 2) 1) rootX_isRoot
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero] at h
  exact (by decide : ∀ r : ZMod (2 ^ 1), r ^ 3 + 2 * r ^ 2 + 1 = 0 → r = 1) _ h

/-- `X` is a 2-adic unit (residue `1` mod `2`). -/
theorem rootX_isUnit : IsUnit rootX := isUnit_of_toZModPow_one_eq_one rootX_toZModPow_one

/-- The denominator `X² + X + 1` of `S` is a unit (residue `1 + 1 + 1 = 1` mod `2`); the
"`the denominator is a unit`" clause following eq. (SfromX). -/
theorem denom_isUnit : IsUnit (rootX ^ 2 + rootX + 1) := by
  apply isUnit_of_toZModPow_one_eq_one
  rw [map_add, map_add, map_pow, map_one, rootX_toZModPow_one]
  decide

/-- `X² − X − 1` is a unit (residue `1` mod `2`); the "second factor is odd" step that kills
the `Y = +X²` branch in the ⟦prop:orientation⟧ proof. -/
theorem isUnit_sq_sub_self_sub_one_of_odd : IsUnit (rootX ^ 2 - rootX - 1) := by
  apply isUnit_of_toZModPow_one_eq_one
  rw [map_sub, map_sub, map_pow, map_one, rootX_toZModPow_one]
  decide

/-! ### The value `S = -X³/(X²+X+1)` -/

/-- `S = χ_R(s) = -X³ · (X²+X+1)⁻¹`, eq. (orientationvalues)/(SfromX).  Defined through the
unit `denom_isUnit` (division by a unit, no field structure needed). -/
noncomputable def Sval : ℤ_[2] := -rootX ^ 3 * ((denom_isUnit.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2])

/-- **Equation form of `S`** (preferred by downstream tickets): `S · (X²+X+1) = -X³`. -/
theorem Sval_mul_denom : Sval * (rootX ^ 2 + rootX + 1) = -rootX ^ 3 := by
  rw [Sval, mul_assoc, denom_isUnit.val_inv_mul, mul_one]

/-- `toZModPow 4 S = 13` — eq. (orientationvalues)'s `S ≡ 13 (mod 16)`.  From
`Sval_mul_denom` reduced mod 16: `S · 15 = 3`, and `15` is its own inverse in `ZMod 16`. -/
theorem Sval_toZModPow_four : toZModPow 4 Sval = 13 := by
  have h := congrArg (toZModPow (p := 2) 4) Sval_mul_denom
  simp only [map_mul, map_add, map_pow, map_one, map_neg] at h
  rw [rootX_toZModPow_four] at h
  have hA : ((5 : ZMod (2 ^ 4)) ^ 2 + 5 + 1) = 15 := by decide
  have hB : -(5 : ZMod (2 ^ 4)) ^ 3 = 3 := by decide
  rw [hA, hB] at h
  calc toZModPow 4 Sval = toZModPow 4 Sval * (15 * 15) := by
        rw [show (15 : ZMod (2 ^ 4)) * 15 = 1 from by decide, mul_one]
    _ = toZModPow 4 Sval * 15 * 15 := by ring
    _ = 3 * 15 := by rw [h]
    _ = 13 := by decide

/-! ### The value `Y = -X²` -/

/-- `Y = χ_R(y) = -X²`, the first equation of eq. (orientationvalues). -/
noncomputable def Yval : ℤ_[2] := -rootX ^ 2

/-- Definitional unfolding of `Y`. -/
theorem Yval_eq : Yval = -rootX ^ 2 := rfl

/-- `toZModPow 4 Y = 7`  (`Y ≡ -25 ≡ 7 mod 16`). -/
theorem Yval_toZModPow_four : toZModPow 4 Yval = 7 := by
  rw [Yval, map_neg, map_pow, rootX_toZModPow_four]; decide

/-- `Y ≠ X²`: the excluded `Y = +X²` branch is genuinely different from `Y = -X²`
(`2X² ≠ 0` as `X` is a unit). -/
theorem Yval_ne_sq : Yval ≠ rootX ^ 2 := by
  rw [Yval]
  intro h
  have h2 : (2 : ℤ_[2]) * rootX ^ 2 = 0 := by linear_combination -h
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 rootX_isUnit.ne_zero) h2

/-! ### Exact-level (`v₂ = 2`) facts -/

/-- **Exact-level form of `X`**: `X − 1 = 4·(unit)`.  Consumed directly by a downstream
`zpowZtwo_injective_of_exact_level`-style argument (cf. `GQ2/ZtwoPowering.lean`). -/
theorem rootX_sub_one_eq : ∃ a : ℤ_[2]ˣ, rootX - 1 = 4 * (a : ℤ_[2]) := by
  have hmem : rootX - 5 ∈ RingHom.ker (toZModPow (p := 2) 4) := by
    rw [RingHom.mem_ker, map_sub, rootX_toZModPow_four, map_ofNat, sub_self]
  rw [ker_toZModPow] at hmem
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hmem
  have hu : IsUnit (1 + 4 * k) := by
    apply isUnit_of_toZModPow_one_eq_one
    rw [map_add, map_one, map_mul, toZModPow_one_four, zero_mul, add_zero]
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  linear_combination hk

/-- **`v₂(X − 1) = 2`**, i.e. `‖X − 1‖ = 1/4`: `X ≡ 5 (16)` so `X − 1 = 4·unit`.  The paper's
"`X` topologically generates `1 + 4ℤ₂`" input. -/
theorem norm_rootX_sub_one : ‖rootX - 1‖ = 1 / 4 := by
  obtain ⟨a, ha⟩ := rootX_sub_one_eq
  rw [ha, norm_mul, PadicInt.isUnit_iff.mp a.isUnit, mul_one, norm_four]

/-- **Exact-level form of `S`**: `S − 1 = 4·(unit)`. -/
theorem Sval_sub_one_eq : ∃ a : ℤ_[2]ˣ, Sval - 1 = 4 * (a : ℤ_[2]) := by
  have hmem : Sval - 13 ∈ RingHom.ker (toZModPow (p := 2) 4) := by
    rw [RingHom.mem_ker, map_sub, Sval_toZModPow_four, map_ofNat, sub_self]
  rw [ker_toZModPow] at hmem
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hmem
  have hu : IsUnit (3 + 4 * k) := by
    apply isUnit_of_toZModPow_one_eq_one
    rw [map_add, map_mul, toZModPow_one_four, zero_mul, add_zero,
      show (3 : ℤ_[2]) = ((3 : ℤ) : ℤ_[2]) by push_cast; ring, map_intCast]
    decide
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  linear_combination hk

/-- **`v₂(S − 1) = 2`**, i.e. `‖S − 1‖ = 1/4`: `S ≡ 13 (16)` so `S − 1 = 4·unit`. -/
theorem norm_Sval_sub_one : ‖Sval - 1‖ = 1 / 4 := by
  obtain ⟨a, ha⟩ := Sval_sub_one_eq
  rw [ha, norm_mul, PadicInt.isUnit_iff.mp a.isUnit, mul_one, norm_four]

/-! ### Stress test: the deeper mod-32 congruence -/

/-- **Stress test** (`docs/orchestration/roe-r2-spike.md` §2, prec-`2²²⁰` table): `X ≡ 21
(mod 32)`.  Verified by the same `decide`-over-`ZMod 32` route directly from `rootX_isRoot`;
`21 ≡ 5 (mod 16)` cross-checks `rootX_toZModPow_four` and catches Newton-step sign slips. -/
theorem rootX_toZModPow_five : toZModPow 5 rootX = 21 := by
  have h := congrArg (toZModPow (p := 2) 5) rootX_isRoot
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero] at h
  exact (by decide : ∀ r : ZMod (2 ^ 5), r ^ 3 + 2 * r ^ 2 + 1 = 0 → r = 21) _ h

end GQ2.Roe

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Proposition 3.3 = ⟦prop:orientation⟧
    - eq. (orientationvalues) `Y = -X²`, `X³+2X²+1 = 0`, `S = -X³/(X²+X+1)`
      = `Yval_eq`, `rootX_isRoot`, `Sval_mul_denom`
    - `X ≡ 5 (16)`, `S ≡ 13 (16)` = `rootX_toZModPow_four`, `Sval_toZModPow_four`
    - `v₂(X−1) = v₂(S−1) = 2` = `norm_rootX_sub_one`, `norm_Sval_sub_one`
  * Corollary 3.4 = ⟦cor:abstractD0⟧ (secondary orientation depth `f = 2`, consumes the above)
-/
