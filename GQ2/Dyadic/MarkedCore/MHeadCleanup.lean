/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.MarkedCore.Cores
import GQ2.Dyadic.MarkedCore.FreeProTwoCharacterCorrection
import GQ2.Roe.Labute.AdditiveCharacters

/-!
# The coupled ordinary head row of an actual M-relator correction

The full, arbitrary-rank `M_alpha` word has ordinary row
`2 f(x0) + 2^alpha f(x2)`: unlike the `N` word it is **coupled**, carrying the
`C` column as well as the `A` column. This module extracts the head digit from
that coupled row without setting the `C` row to zero and without any
orientation or vanishing-`C` premise.

Every declaration here carries the lane prefix `mHead`. That prefix is a naming
reservation for this module; it is not a claim about the peripheral head word
`GQ2.Dyadic.MarkedCore.mHead` of `Cores`, which is a different object.

Nothing here constructs the corrections, asserts a derivative image, or
preserves a relator equation after replacement.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

section OrdinaryRows
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {h : ℕ}

omit [IsTopologicalGroup G] in
/-- The **coupled** ordinary row of the literal full `M_alpha` relator, every
handle included: `2 f(A) + 2^alpha f(C)`. Unlike the `N` row it carries the `C`
column as well, so the head digit cannot be read off by cancelling a single
unit factor. -/
theorem mHead_ordinary_row (alpha : ℕ)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y : Fin (coreRank h) → G) :
    (f (mRelWord alpha y)).toAdd =
      2 * (f (y 0)).toAdd + (2 : ℤ_[2]) ^ alpha * (f (y 2)).toAdd := by
  rw [map_mRelWord, mRelWord_comm, toAdd_mul, toAdd_pow, toAdd_pow,
    nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

omit [IsTopologicalGroup G] in
/-- Right-multiplying the marking by corrections moves the target-relative
defect row to the corrections' own coupled row. The original relation need only
agree with the target under `f`; no relator equation is assumed. -/
theorem mHead_correction_ordinary_row (alpha : ℕ)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y t : Fin (coreRank h) → G) (target : G)
    (hrow : f (mRelWord alpha y) = f target) :
    (f (mRelWord alpha (fun i => y i * t i) * target⁻¹)).toAdd =
      2 * (f (t 0)).toAdd + (2 : ℤ_[2]) ^ alpha * (f (t 2)).toAdd := by
  have hb := congrArg Multiplicative.toAdd hrow
  rw [mHead_ordinary_row] at hb
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, mHead_ordinary_row, ← hb]
  simp only [map_mul, toAdd_mul]
  ring

end OrdinaryRows

/-- The scalar heart of the cleanup. One factor of two cancels from the coupled
row; the `C` summand is then already divisible by `2^d`, because `2^(alpha-1)`
contributes at least one further factor when `alpha >= 2` and the `C` row itself
carries `2^(d-1)`. No hypothesis forces `C = 0`. -/
theorem mHead_dvd_of_coupled_row {alpha d : ℕ} (halpha : 2 ≤ alpha) (hd : 1 ≤ d)
    {A C : ℤ_[2]} (hCrow : (2 : ℤ_[2]) ^ (d - 1) ∣ C)
    (hdefect : (2 : ℤ_[2]) ^ (d + 1) ∣ 2 * A + (2 : ℤ_[2]) ^ alpha * C) :
    (2 : ℤ_[2]) ^ d ∣ A := by
  obtain ⟨a, rfl⟩ : ∃ a, alpha = a + 2 := ⟨alpha - 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hCrow
  obtain ⟨c, rfl⟩ := hCrow
  obtain ⟨b, hb⟩ := hdefect
  refine ⟨b - 2 ^ a * c, ?_⟩
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0)
  linear_combination hb

section HeadDigit
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {h : ℕ}

/-- **T1.** One extra ordinary digit at the `A` column of an actual `M_alpha`
correction, at arbitrary rank and arbitrary target. The `C` column is only
assumed to lie in `lambda_d`; it is not set to zero, and no orientation premise
is used. No compactness, pro-two or finite-generation assumption on `G`. -/
theorem mHead_correction_dvd {alpha d : ℕ} (halpha : 2 ≤ alpha) (hd : 1 ≤ d)
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (y t : Fin (coreRank h) → G) (target : G)
    (hrow : f (mRelWord alpha y) = f target)
    (hC : t 2 ∈ twoCentralSeries G d)
    (hdefect : mRelWord alpha (fun i => y i * t i) * target⁻¹ ∈
      twoCentralSeries G (d + 2)) :
    (2 : ℤ_[2]) ^ d ∣ (f (t 0)).toAdd := by
  refine mHead_dvd_of_coupled_row halpha hd
    (twoCentralSeries_z2_character_dvd f hd hC) ?_
  rw [← mHead_correction_ordinary_row alpha f y t target hrow]
  exact twoCentralSeries_z2_character_dvd_succ f hdefect

end HeadDigit

#print axioms mHead_ordinary_row
#print axioms mHead_correction_ordinary_row
#print axioms mHead_dvd_of_coupled_row
#print axioms mHead_correction_dvd

end
end GQ2.Dyadic.MarkedCore
