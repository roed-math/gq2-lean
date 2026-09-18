/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.NInitialCupDepth
import GQ2.Roe.Labute.AdditiveCharacters

/-!
# The initial M-relator depth under full mod-two cup preservation

The M relator is `A^2 [A,B] C^(2^alpha) [C,D]` times the handles, so it is not
a text substitution of the N relator. Two M-specific facts replace the N head
argument, and both need `alpha >= 2`:

* `C^(2^alpha)` already dies modulo lambda-three, because `g^(2^alpha)` lies in
  `lambda_(alpha+1)` and `alpha + 1 >= 3`;
* the surviving head is the **square** `A^2`, and a square in the class-two
  quotient depends only on the class of its base modulo lambda-two. So the
  chosen lift need not fix the `A` letter literally: agreement modulo
  lambda-two is enough. This is exactly what the fixed-`T` initial lift
  supplies, since `T = A * C^(2^(alpha-1))` differs from `A` by a square when
  `alpha >= 2`.

Everything about the commutator tail is shared with the N calculation and is
imported from `NInitialCupDepth`: the actual double-coordinate expansion of a
commutator modulo lambda-three, and the contraction of a symmetric coefficient
matrix against the alternating bracket. Nothing here reproves it.

This is only the initial-depth step. No subsequent filtered correction, no
frame automorphism lift, and no converse is asserted in this file.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 Multiplicative GQ2.Roe GQ2.Roe.Labute
open GQ2.Dyadic.EvenModel
open NInitialCupDepth

section LevelThree

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- In the class-two quotient a square depends only on the class of its base in
the central involutive layer: if `p` and `q` differ by an element of
`Z_2 = lambda_2/lambda_3` then `p^2 = q^2`. -/
theorem mCupSq_eq_of_zLayer {p q : levelQuot G 3} (hz : p * q⁻¹ ∈ zLayer G 2) :
    p ^ 2 = q ^ 2 := by
  have hcomm : q * (p * q⁻¹) = (p * q⁻¹) * q :=
    Subgroup.mem_center_iff.mp (zLayer_le_center G 2 hz) q
  have hsq : (p * q⁻¹) ^ 2 = 1 := zLayer_sq G hz
  have hexp : p ^ 2 = (p * q⁻¹) ^ 2 * q ^ 2 := by
    have hre : (p * q⁻¹) ^ 2 * q ^ 2 = (p * q⁻¹) * ((p * q⁻¹) * q) * q := by
      rw [pow_two, pow_two]; group
    rw [hre, ← hcomm]
    group
  rw [hexp, hsq, one_mul]

/-- The actual `A`-head comparison: agreement modulo `lambda_2` already forces
equality of the squares in the class-two quotient. -/
theorem mCupSq_levelMk_eq_of_mem_two {u v : G}
    (huv : u * v⁻¹ ∈ twoCentralSeries G 2) :
    levelMk G 3 u ^ 2 = levelMk G 3 v ^ 2 :=
  mCupSq_eq_of_zLayer ⟨u * v⁻¹, huv, by rw [map_mul, map_inv]⟩

/-- The actual `C^(2^alpha)` block dies in the class-two quotient as soon as
`alpha >= 2`. This is where the M word differs from the N word, and it is the
only place `alpha >= 2` is used in the initial-depth calculation. -/
theorem mCupPow_eq_one {α : ℕ} (hα : 2 ≤ α) (p : levelQuot G 3) : p ^ 2 ^ α = 1 := by
  obtain ⟨g, rfl⟩ := levelMk_surjective G 3 p
  rw [← map_pow]
  have hm : g ^ 2 ^ α ∈ twoCentralSeries G 3 :=
    twoCentralSeries_antitone G (show 3 ≤ α + 1 by omega)
      (pow_two_pow_mem_twoCentralSeries_succ G g α)
  exact (QuotientGroup.eq_one_iff _).mpr hm

end LevelThree

section MTail

variable {h : ℕ}

/-- The exact class-two shape of the M relator: the `C`-power block is gone and
the surviving head is the square of the `A` letter, multiplied by the very same
commutator tail the N calculation controls. -/
theorem mCupRelWord_levelMk_eq_head_mul_tail {α : ℕ} (hα : 2 ≤ α)
    (m : Fin (coreRank h) → FreeTwoRank (coreRank h)) :
    levelMk (FreeTwoRank (coreRank h) : Type) 3 (mRelWord α m) =
      levelMk (FreeTwoRank (coreRank h) : Type) 3 (m 0) ^ 2 *
        ((freeTail m).toMul : levelQuot (FreeTwoRank (coreRank h) : Type) 3) := by
  rw [map_mRelWord]
  unfold mRelWord mWord
  dsimp only
  rw [mCupPow_eq_one hα, mul_one, freeTail_value]
  simp only [mul_assoc]

/-- **The initial M depth.** For `alpha >= 2`, an actual free-basis tuple whose
`A` letter agrees with the reference `A` letter modulo `lambda_2`, and which
preserves the full mod-two cup form in the row-vector variance, has the same M
relator as the reference tuple in the class-two quotient.

The head hypothesis is deliberately the weak one: literal fixing of the `A`
letter is **not** required, and is false for the fixed-`T` initial lift. -/
theorem mCupRelWord_level_three_eq {α : ℕ} (hα : 2 ≤ α)
    (m m' : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hhead : m 0 * (m' 0)⁻¹ ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) 2)
    (hcup : ∀ i j, evenCupForm (reducedRows m i) (reducedRows m j) =
      evenCupForm (reducedRows m' i) (reducedRows m' j)) :
    levelMk (FreeTwoRank (coreRank h) : Type) 3 (mRelWord α m) =
      levelMk (FreeTwoRank (coreRank h) : Type) 3 (mRelWord α m') := by
  have hrow : ∀ i, reducedRows m i 0 = reducedRows m' i 0 := by
    intro i
    have hdvd : (2 : ℤ_[2]) ^ 1 ∣
        toAdd (freeTwoCoordinate (coreRank h) i (m 0 * (m' 0)⁻¹)) :=
      twoCentralSeries_z2_character_dvd_succ (freeTwoCoordinate (coreRank h) i) hhead
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, pow_one] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have htwo : nRed (2 : ℤ_[2]) = 0 := by
      have h2 : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by push_cast; ring
      rw [h2, map_natCast]
      decide
    have : nRed (toAdd (freeTwoCoordinate (coreRank h) i (m 0))) -
        nRed (toAdd (freeTwoCoordinate (coreRank h) i (m' 0))) = 0 := by
      rw [← map_sub, hc, map_mul, htwo, zero_mul]
    exact sub_eq_zero.mp this
  have htail : freeTail m = freeTail m' := freeTail_eq_of_cup m m' hrow hcup
  rw [mCupRelWord_levelMk_eq_head_mul_tail hα, mCupRelWord_levelMk_eq_head_mul_tail hα,
    htail, mCupSq_levelMk_eq_of_mem_two hhead]

/-- The same statement as an actual error-membership: the M relator error of the
tuple lies in `lambda_3`. This is quotient membership of the genuine word, not
membership in a formal bracket span. -/
theorem mCupRelWord_error_mem_three {α : ℕ} (hα : 2 ≤ α)
    (m m' : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hhead : m 0 * (m' 0)⁻¹ ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) 2)
    (hcup : ∀ i j, evenCupForm (reducedRows m i) (reducedRows m j) =
      evenCupForm (reducedRows m' i) (reducedRows m' j)) :
    mRelWord α m * (mRelWord α m')⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) 3 := by
  apply (QuotientGroup.eq_one_iff _).mp
  change levelMk (FreeTwoRank (coreRank h) : Type) 3
    (mRelWord α m * (mRelWord α m')⁻¹) = 1
  rw [map_mul, map_inv, mCupRelWord_level_three_eq hα m m' hhead hcup, mul_inv_cancel]

end MTail

#print axioms mCupSq_eq_of_zLayer
#print axioms mCupSq_levelMk_eq_of_mem_two
#print axioms mCupPow_eq_one
#print axioms mCupRelWord_levelMk_eq_head_mul_tail
#print axioms mCupRelWord_level_three_eq
#print axioms mCupRelWord_error_mem_three

end
end GQ2.Dyadic.MarkedCore
