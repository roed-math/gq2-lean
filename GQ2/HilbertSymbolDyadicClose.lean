/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.HilbertSymbolNecessity
public import GQ2.HilbertSymbolSufficiency

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# The dispatch pyramid and the capstone `hilbertSymbol_dyadic'`

This is the assembly of the necessity and sufficiency engines into Serre's dyadic Hilbert-symbol
formula, with a statement matching the public theorem in `Foundations/Axioms.lean`.

**The pyramid.**
1. **Parity** — `symbol_zpow_reduce` splits `2^α = 2^{α%2}·(2^{α/2})²` in each slot; square-class
   invariance (`hilbertSymbol_mul_sq_left/right`) kills the squares, and `(α : 𝔽₂) = (α%2 : 𝔽₂)`
   does the same on the formula side.  Four parity families remain.
2. **`(0,0)`, `(0,1)`** — `dyadic_uu` / `dyadic_u2v`: `rcases` over the 4×4 unit residues
   (`toZModPow_unit_mem`), each case closed by a B7′-3 `−1`-leaf, a B7′-4 `+1`-witness, or the
   `u ≡ 1` freebie, with the formula side evaluated by `decide` at the pinned residues.
3. **`(1,0)`** — `hilbertSymbol_comm` + `dyadic_u2v` with the slots swapped.
4. **`(1,1)`** — the design move: `(2u, 2v) = (2u, −(2u·2v)) = (2u, −uv·2²) = (2u, −uv)`
   (`hilbertSymbol_neg_mul_right` + square invariance), landing in `dyadic_u2v` at `(−uv, u)`;
   the `ε/ω` bookkeeping (`ε(−uv) = 1+ε(u)+ε(v)`, `ω(−uv) = ω(u)+ω(v)`, `ε² = ε`) is a 16-case
   `decide` in `𝔽₂`.

`Foundations/Axioms.lean` exposes the capstone `hilbertSymbol_dyadic'` under the public theorem name
`hilbertSymbol_dyadic`.
-/

namespace GQ2.HilbertSymbol

open scoped Classical
open PadicInt

/-! ## The two residue-dispatch families -/

/-- **The `(0,0)` family**: unit·unit symbols follow Serre's formula `(u, v)₂ = (−1)^{ε(u)ε(v)}`.
Dispatch over the sixteen residue pairs: `≡ 1` slots are freebies, `{3,5},{5,5},{5,7}` (and swaps)
are B7′-4 witnesses, `{3,3},{3,7},{7,7}` (and the swap) are B7′-3 `decide`-leaves. -/
theorem dyadic_uu (u v : ℤ_[2]ˣ) :
    hilbertSymbol (unitCoe u) (unitCoe v) = signOf (ε u * ε v) := by
  rcases toZModPow_unit_mem u with hu | hu | hu | hu <;>
    rcases toZModPow_unit_mem v with hv | hv | hv | hv
  -- u ≡ 1: freebies
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide]
    exact hilbertSymbol_left_one hu _
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide]
    exact hilbertSymbol_left_one hu _
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide]
    exact hilbertSymbol_left_one hu _
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide]
    exact hilbertSymbol_left_one hu _
  -- u ≡ 3
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide, hilbertSymbol_comm]
    exact hilbertSymbol_left_one hv _
  · rw [show signOf (ε u * ε v) = -1 from by rw [ε, ε, hu, hv]; decide]
    exact leaf_uu_3_3 u v hu hv
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide]
    exact hilbertSymbol_uu_35 hu hv
  · rw [show signOf (ε u * ε v) = -1 from by rw [ε, ε, hu, hv]; decide]
    exact leaf_uu_3_7 u v hu hv
  -- u ≡ 5
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide, hilbertSymbol_comm]
    exact hilbertSymbol_left_one hv _
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide, hilbertSymbol_comm]
    exact hilbertSymbol_uu_35 hv hu
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide]
    exact hilbertSymbol_uu_55 hu hv
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide]
    exact hilbertSymbol_uu_57 hu hv
  -- u ≡ 7
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide, hilbertSymbol_comm]
    exact hilbertSymbol_left_one hv _
  · rw [show signOf (ε u * ε v) = -1 from by rw [ε, ε, hu, hv]; decide, hilbertSymbol_comm]
    exact leaf_uu_3_7 v u hv hu
  · rw [show signOf (ε u * ε v) = 1 from by rw [ε, ε, hu, hv]; decide, hilbertSymbol_comm]
    exact hilbertSymbol_uu_57 hv hu
  · rw [show signOf (ε u * ε v) = -1 from by rw [ε, ε, hu, hv]; decide]
    exact leaf_uu_7_7 u v hu hv

/-- **The `(0,1)` family**: `(u, 2v)₂ = (−1)^{ε(u)ε(v) + ω(u)}`.  Dispatch over the sixteen
residue pairs: `u ≡ 1` is free, `(3,3),(3,7),(7,1),(7,5)` are B7′-4 witnesses, the remaining
eight are B7′-3 `decide`-leaves. -/
theorem dyadic_u2v (u v : ℤ_[2]ˣ) :
    hilbertSymbol (unitCoe u) (unit2 * unitCoe v) = signOf (ε u * ε v + ω u) := by
  rcases toZModPow_unit_mem u with hu | hu | hu | hu <;>
    rcases toZModPow_unit_mem v with hv | hv | hv | hv
  -- u ≡ 1: freebies
  · rw [show signOf (ε u * ε v + ω u) = 1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact hilbertSymbol_left_one hu _
  · rw [show signOf (ε u * ε v + ω u) = 1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact hilbertSymbol_left_one hu _
  · rw [show signOf (ε u * ε v + ω u) = 1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact hilbertSymbol_left_one hu _
  · rw [show signOf (ε u * ε v + ω u) = 1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact hilbertSymbol_left_one hu _
  -- u ≡ 3
  · rw [show signOf (ε u * ε v + ω u) = -1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact leaf_u2v_3_1 u v hu hv
  · rw [show signOf (ε u * ε v + ω u) = 1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact hilbertSymbol_u2v_33 hu hv
  · rw [show signOf (ε u * ε v + ω u) = -1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact leaf_u2v_3_5 u v hu hv
  · rw [show signOf (ε u * ε v + ω u) = 1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact hilbertSymbol_u2v_37 hu hv
  -- u ≡ 5
  · rw [show signOf (ε u * ε v + ω u) = -1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact leaf_u2v_5_1 u v hu hv
  · rw [show signOf (ε u * ε v + ω u) = -1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact leaf_u2v_5_3 u v hu hv
  · rw [show signOf (ε u * ε v + ω u) = -1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact leaf_u2v_5_5 u v hu hv
  · rw [show signOf (ε u * ε v + ω u) = -1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact leaf_u2v_5_7 u v hu hv
  -- u ≡ 7
  · rw [show signOf (ε u * ε v + ω u) = 1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact hilbertSymbol_u2v_71 hu hv
  · rw [show signOf (ε u * ε v + ω u) = -1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact leaf_u2v_7_3 u v hu hv
  · rw [show signOf (ε u * ε v + ω u) = 1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact hilbertSymbol_u2v_75 hu hv
  · rw [show signOf (ε u * ε v + ω u) = -1 from by rw [ε, ε, ω, hu, hv]; decide]
    exact leaf_u2v_7_7 u v hu hv

/-! ## The capstone -/

/-- `(α : 𝔽₂)` only sees the parity `α % 2` (B7′-0 pin 1). -/
private lemma intCast_emod_two (α : ℤ) : ((α % 2 : ℤ) : ZMod 2) = (α : ZMod 2) :=
  (ZMod.intCast_eq_intCast_iff _ _ _).mpr (Int.emod_emod_of_dvd α (dvd_refl 2))

/-- **Serre's dyadic Hilbert-symbol formula** (*A Course in Arithmetic*, Ch. III §1.2, Theorem 1,
`p = 2`; `ε, ω` the residue characters of Ch. II §3.3): writing `a = 2^α u`, `b = 2^β v` with
`u, v ∈ ℤ₂ˣ`,
`(a, b)₂ = (−1)^{ε(u)ε(v) + α ω(v) + β ω(u)}`.

The public statement in `Foundations/Axioms.lean` is
`hilbertSymbol_dyadic := hilbertSymbol_dyadic'`.  This is proved from the definition of
`hilbertSymbol` by solvability of `a X² + b Y² = Z²` — 2-adic Hensel + finite `decide`s, std-3. -/
theorem hilbertSymbol_dyadic' (α β : ℤ) (u v : ℤ_[2]ˣ) :
    hilbertSymbol (unit2 ^ α * unitCoe u) (unit2 ^ β * unitCoe v)
      = signOf (ε u * ε v + (α : ZMod 2) * ω v + (β : ZMod 2) * ω u) := by
  -- Parity: reduce both slots (square-class invariance) and both casts to `% 2`.
  rw [show unit2 ^ α * unitCoe u = unit2 ^ (α % 2) * unitCoe u * (unit2 ^ (α / 2)) ^ 2 from by
        rw [symbol_zpow_reduce α, mul_right_comm],
      show unit2 ^ β * unitCoe v = unit2 ^ (β % 2) * unitCoe v * (unit2 ^ (β / 2)) ^ 2 from by
        rw [symbol_zpow_reduce β, mul_right_comm],
      hilbertSymbol_mul_sq_left, hilbertSymbol_mul_sq_right,
      ← intCast_emod_two α, ← intCast_emod_two β]
  rcases Int.emod_two_eq α with hα | hα <;> rcases Int.emod_two_eq β with hβ | hβ <;>
    rw [hα, hβ]
  -- (0,0): unit·unit
  · rw [zpow_zero, one_mul, one_mul, Int.cast_zero, dyadic_uu u v]
    congr 1; ring
  -- (0,1): (u, 2v)
  · rw [zpow_zero, one_mul, zpow_one, Int.cast_zero, Int.cast_one, dyadic_u2v u v]
    congr 1; ring
  -- (1,0): by symmetry from (0,1)
  · rw [zpow_one, zpow_zero, one_mul, Int.cast_one, Int.cast_zero, hilbertSymbol_comm,
      dyadic_u2v v u]
    congr 1; ring
  -- (1,1): (2u, 2v) = (2u, −uv) via the norm-form identity, then (0,1) at (−uv, u)
  · rw [zpow_one, Int.cast_one,
      ← hilbertSymbol_neg_mul_right (unit2 * unitCoe u) (unit2 * unitCoe v),
      show -(unit2 * unitCoe u * (unit2 * unitCoe v)) = unitCoe (-(u * v)) * unit2 ^ 2 from by
        ext
        push_cast [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val, unit2_coe, unitCoe_coe]
        ring,
      hilbertSymbol_mul_sq_right, hilbertSymbol_comm, dyadic_u2v (-(u * v)) u,
      show (-(u * v) : ℤ_[2]ˣ) = -1 * (u * v) from by
        ext; push_cast [Units.val_neg, Units.val_mul, Units.val_one]; ring,
      ε_mul, ε_mul, ε_neg_one, ω_mul, ω_mul, ω_neg_one]
    congr 1
    generalize ε u = a
    generalize ε v = b
    generalize ω u = c
    generalize ω v = d
    revert a b c d
    decide

end GQ2.HilbertSymbol
