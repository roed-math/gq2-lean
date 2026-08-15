/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcRowData

/-!
# W81-NORMS: the four norm-character values at the two procyclic fields

Wave 80 reduced the two procyclic quadratic rows to four named inputs, of which three are
values of the norm-group character of `ℚ₂(√±10)` and the fourth is the pivot.  This module
computes the three, from the **mod-8 congruence on norms of spectral units** and nothing else:
no Hilbert-symbol calculator is used, and none is needed.

Declaration prefix `mpcNorm`, namespace `GQ2.Dyadic.Instances.MpcNorm`.
-/

namespace GQ2.Dyadic.Instances.MpcNorm

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcCert GQ2.Dyadic.Instances.MpcRow
open GQ2.Dyadic.FieldUnimod GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Fields GQ2.Dyadic.LSquare

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## §1 Squares modulo eight in `ℤ₂`

The whole arithmetic of this lane is the following pair of residue facts, and both are `decide`
over `ZMod 8`.  A `2`-adic *unit* squares to `1`; an arbitrary `2`-adic integer squares into
`{0, 1, 4}`.  Everything below is these two facts pushed through the norm form `t² − a s²`. -/

section ModEight

/-- **A `2`-adic unit squares to `1` modulo `8`.**  The reason the norm of a spectral unit of
`ℚ₂(√a)` has only two possible residues rather than four. -/
theorem mpcNorm_unit_sq_mod_eight (u : ℤ_[2]ˣ) :
    PadicInt.toZModPow 3 ((u : ℤ_[2]) ^ 2) = 1 := by
  rw [map_pow]
  have hu : IsUnit (PadicInt.toZModPow (p := 2) 3 (u : ℤ_[2])) := u.isUnit.map _
  revert hu
  generalize PadicInt.toZModPow (p := 2) 3 (u : ℤ_[2]) = r
  revert r
  decide

/-- **A `2`-adic integer squares into `{0, 1, 4}` modulo `8`.** -/
theorem mpcNorm_sq_mod_eight (y : ℤ_[2]) :
    PadicInt.toZModPow 3 (y ^ 2) = 0 ∨ PadicInt.toZModPow 3 (y ^ 2) = 1 ∨
      PadicInt.toZModPow 3 (y ^ 2) = 4 := by
  rw [map_pow]
  generalize PadicInt.toZModPow (p := 2) 3 y = r
  revert r
  decide

end ModEight

end

end GQ2.Dyadic.Instances.MpcNorm
