/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenModelDemushkin

/-!
# The compact-M `C0` pivot at the mod-two cup level

This file isolates the linear obstruction behind the general-h compact-M pivot premise.  The
landed even Gram pairs the `C0` coordinate with the `D` character.  Consequently a cup isometry
which fixes that character fixes the parity of `C0` on every covector.  The tempting local
symplectic shear `C0 ↦ C0 + U_j` therefore requires the companion correction
`V_j ↦ V_j + D`; the compact-M orientation detects that added `D` coordinate, and no sign
correction can hide it at `alpha >= 2`.

The conclusions here are deliberately at the proved mod-two/cup level.  The repository does
not yet package the adapter sending an arbitrary continuous automorphism of `DM alpha h` to its
pullback on the displayed mod-two character coordinates, together with cup naturality and the
consequence of preserving `chiM`.  Thus this module does not claim a group-automorphism no-go
theorem, nor does it claim that every abstract isometry is realized by a relator-preserving
automorphism.
-/

namespace GQ2.Dyadic.Instances.M0C0PivotAudit

open GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel

/-- At depth at least two, no sign correction can hide a nonzero `D` coordinate from the
compact-M orientation. -/
theorem chi_trivial_forces_d_zero
    {α : ℕ} (hα : 2 ≤ α) (b d : ℤ_[2])
    (hchi : mSign b * zpowZtwo isProP_two_unitsPadicInt (mUnit α) d = 1) :
    d = 0 := by
  apply (mChi_row_extract hα (b := b) (d := d) (w := 0) (ε := 0) ?_).2
  rw [show ((0 : ZMod 2).val) = 0 from rfl, pow_zero, one_mul,
    SectionThree.zpowZtwo_zero]
  exact hchi

/-- In particular the symplectic companion row `V ↦ V + D` cannot be made
orientation-trivial by adding any `B`-coordinate. -/
theorem no_chi_trivial_companion_d_one
    {α : ℕ} (hα : 2 ≤ α) (b : ℤ_[2]) :
    mSign b * zpowZtwo isProP_two_unitsPadicInt (mUnit α) 1 ≠ 1 := by
  intro h
  have := chi_trivial_forces_d_zero hα b 1 h
  norm_num at this

/-- A cup isometry fixing the cup-dual of the `C0` coordinate fixes the `C0` coordinate of
every covector. -/
theorem c0_fixed_of_evenCup_isometry
    {h : ℕ} (F : (Fin (coreRank h) → ZMod 2) → (Fin (coreRank h) → ZMod 2))
    (hF : ∀ v w, evenCupForm (F v) (F w) = evenCupForm v w)
    (hD : F (evenDualVector (2 : Fin (coreRank h))) = evenDualVector 2)
    (v : Fin (coreRank h) → ZMod 2) :
    F v 2 = v 2 := by
  calc
    F v 2 = evenCupForm (evenDualVector 2) (F v) :=
      (evenCupForm_evenDualVector_left (F v) 2).symm
    _ = evenCupForm (F (evenDualVector 2)) (F v) := by rw [hD]
    _ = evenCupForm (evenDualVector 2) v := hF _ _
    _ = v 2 := evenCupForm_evenDualVector_left v 2

/-- The local symplectic shear which adds a handle `U` coordinate to `C0` must simultaneously
add the `D` coordinate to the partner `V` coordinate. -/
theorem c0_handle_symplectic_shear
    (c d u v c' d' u' v' : ZMod 2) :
    (c + u) * d' + d * (c' + u') + u * (v' + d') + (v + d) * u' =
      c * d' + d * c' + u * v' + v * u' := by
  ring_nf
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [htwo]

/-- Conversely, if the cup-dual `D` character is fixed, no covector can acquire a handle
contribution in its `C0` coordinate. -/
theorem no_c0_handle_mix_of_evenCup_isometry
    {h : ℕ} (F : (Fin (coreRank h) → ZMod 2) → (Fin (coreRank h) → ZMod 2))
    (hF : ∀ v w, evenCupForm (F v) (F w) = evenCupForm v w)
    (hD : F (evenDualVector (2 : Fin (coreRank h))) = evenDualVector 2)
    (j : Fin h)
    (hmix : ∀ v, F v 2 = v 2 + v (handleIdxU j)) : False := by
  let v : Fin (coreRank h) → ZMod 2 := Pi.single (handleIdxU j) 1
  have hfix := c0_fixed_of_evenCup_isometry F hF hD v
  rw [hmix v] at hfix
  have hU : v (handleIdxU j) = 1 := by simp [v]
  have hC : v 2 = 0 := by
    simp [v, Ne.symm (handleIdxU_ne_of_val_lt j coreVal_two_lt)]
  rw [hU, hC, zero_add] at hfix
  exact one_ne_zero hfix

#print axioms c0_fixed_of_evenCup_isometry
#print axioms c0_handle_symplectic_shear
#print axioms no_c0_handle_mix_of_evenCup_isometry
#print axioms chi_trivial_forces_d_zero
#print axioms no_chi_trivial_companion_d_one

end GQ2.Dyadic.Instances.M0C0PivotAudit
