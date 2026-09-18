/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.MarkedCore.N
import GQ2.Dyadic.MarkedCore.FreeProTwoCharacterCorrection
import GQ2.Roe.Labute.AdditiveCharacters

/-!
# The ordinary head row of an actual N-relator correction

The full, arbitrary-rank N word has ordinary row `(2+2^alpha) f(x0)`.
Consequently an actual corrected relator defect in `lambda_(k+2)` forces
the head correction row into `2^k Z2` when `alpha >= 2`. This is an exact
group-word calculation, not an assumed associated-graded derivative identity.

The last specialization removes the head correction's ordinary coordinates
exactly in a free pro-two group while preserving its current filtered class.
It does not construct the initial corrections or preserve a relator equation
after replacement; those require the separate filtered group-congruence step.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

section OrdinaryRows
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {h : ℕ}

omit [IsTopologicalGroup G] in
/-- The ordinary row of the literal full N-relator, including every handle. -/
theorem nRelWord_ordinary_row (alpha : ℕ)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y : Fin (coreRank h) → G) :
    (f (nRelWord alpha y)).toAdd = (2 + (2 : ℤ_[2]) ^ alpha) * (f (y 0)).toAdd := by
  rw [map_nRelWord, nRelWord_comm, toAdd_pow, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]

omit [IsTopologicalGroup G] in
/-- Right-multiplying the marking by corrections changes only the ordinary
head row. The original relation need only agree with the target under `f`. -/
theorem nRelWord_correction_ordinary_row (alpha : ℕ)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y t : Fin (coreRank h) → G) (target : G)
    (hrow : f (nRelWord alpha y) = f target) :
    (f (nRelWord alpha (fun i => y i * t i) * target⁻¹)).toAdd =
      (2 + (2 : ℤ_[2]) ^ alpha) * (f (t 0)).toAdd := by
  have hb := congrArg Multiplicative.toAdd hrow
  rw [nRelWord_ordinary_row] at hb
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  rw [nRelWord_ordinary_row, map_mul, toAdd_mul, ← hb]
  ring

/-- For `alpha >= 2`, the head exponent is exactly twice a unit. -/
theorem nHeadExponent_two_unit {alpha : ℕ} (halpha : 2 ≤ alpha) :
    ∃ u : ℤ_[2]ˣ, 2 + (2 : ℤ_[2]) ^ alpha = 2 * (u : ℤ_[2]) := by
  obtain ⟨a, rfl⟩ : ∃ a, alpha = a + 2 := ⟨alpha - 2, by omega⟩
  obtain ⟨u, hu⟩ := isUnit_one_add_two_mul ((2 : ℤ_[2]) ^ a)
  refine ⟨u, ?_⟩
  rw [hu, pow_add]
  ring

/-- One extra ordinary digit at the head, derived from the actual relator
defect. No compactness, pro-two, or finite-generation assumption on `G`. -/
theorem nRelWord_correction_head_dvd {alpha k : ℕ} (halpha : 2 ≤ alpha)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y t : Fin (coreRank h) → G) (target : G)
    (hrow : f (nRelWord alpha y) = f target)
    (hdefect : nRelWord alpha (fun i => y i * t i) * target⁻¹ ∈
      twoCentralSeries G (k + 2)) :
    (2 : ℤ_[2]) ^ k ∣ (f (t 0)).toAdd := by
  obtain ⟨u, hu⟩ := nHeadExponent_two_unit halpha
  apply twoCentralSeries_z2_character_dvd_of_two_unit f u hdefect
  rw [nRelWord_correction_ordinary_row alpha f y t target hrow, hu]

end OrdinaryRows

/-- The actual defect supplies every coordinate divisibility needed for an
exact ordinary-character-zero head representative in the same filtered class.
No claim about replacing the other columns, or the new relator defect, is made. -/
theorem exists_freeTwo_nHead_characterZero_same_class {alpha h n m : ℕ}
    (halpha : 2 ≤ alpha) (y t : Fin (coreRank h) → FreeTwoRank n)
    (target : FreeTwoRank n)
    (hrow : ∀ f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]),
      f (nRelWord alpha y) = f target)
    (ht : t 0 ∈ twoCentralSeries (FreeTwoRank n : Type) m)
    (hdefect : nRelWord alpha (fun i => y i * t i) * target⁻¹ ∈
      twoCentralSeries (FreeTwoRank n : Type) (m + 2)) :
    ∃ t0 : FreeTwoRank n,
      t0 ∈ twoCentralSeries (FreeTwoRank n : Type) m ∧
      (t 0)⁻¹ * t0 ∈ twoCentralSeries (FreeTwoRank n : Type) (m + 1) ∧
      ∀ f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]),
        f t0 = 1 := by
  apply exists_freeTwo_characterZero_same_twoCentralClass n m (t 0) ht
  intro i
  exact nRelWord_correction_head_dvd halpha (freeTwoCoordinate n i)
    y t target (hrow _) hdefect

#print axioms nRelWord_ordinary_row
#print axioms nRelWord_correction_ordinary_row
#print axioms nHeadExponent_two_unit
#print axioms nRelWord_correction_head_dvd
#print axioms exists_freeTwo_nHead_characterZero_same_class

end
end GQ2.Dyadic.MarkedCore
