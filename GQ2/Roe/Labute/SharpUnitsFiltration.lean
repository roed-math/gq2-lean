/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.DyadicSquares
import GQ2.Roe.Labute.TwoCentralTower

/-!
# The sharp lower two-central filtration on `ℤ₂ˣ`

This file proves the exact target-side arithmetic used by the sharp cyclotomic stage:

` λ_n(ℤ₂ˣ) = ker(ℤ₂ˣ → (ZMod 2^(n+1))ˣ) ` for `n ≥ 2`.

The one-step shift is essential.  The reverse containment uses controlled square roots:
an element which is `1` modulo `2^(n+2)` has a square root which is `1` modulo
`2^(n+1)`.
-/

namespace GQ2.Roe.Labute

open PadicInt

/-- The exact sharp filtration on the dyadic unit group. -/
theorem twoCentralSeries_units_eq_sharpKernel (n : ℕ) (hn : 2 ≤ n) :
    twoCentralSeries ℤ_[2]ˣ n =
      (Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom).ker := by
  apply le_antisymm (twoCentralSeries_units_le n hn)
  induction n, hn using Nat.le_induction with
  | base =>
      intro u hu
      have humod : PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 := by
        have h := congrArg Units.val (MonoidHom.mem_ker.mp hu)
        simpa using h
      obtain ⟨w, hw⟩ := GQ2.DyadicSquares.exists_unit_sq_of_toZModPow_eq_one humod
      rw [hw]
      exact sq_mem_twoCentralSeries_succ ℤ_[2]ˣ (Subgroup.mem_top w)
  | succ k hk ih =>
      intro u hu
      have humod : PadicInt.toZModPow (k + 2) (u : ℤ_[2]) = 1 := by
        have h := congrArg Units.val (MonoidHom.mem_ker.mp hu)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      obtain ⟨w, hw, hwmod⟩ := GQ2.DyadicSquares.exists_deep_unit_sq hk humod
      have hwker : w ∈
          (Units.map (PadicInt.toZModPow (k + 1)).toMonoidHom).ker := by
        rw [MonoidHom.mem_ker]
        apply Units.ext
        simpa using hwmod
      rw [hw]
      exact sq_mem_twoCentralSeries_succ ℤ_[2]ˣ (ih hwker)

end GQ2.Roe.Labute
