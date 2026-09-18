/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.MFullStabilizerLift

/-!
# The finite Nielsen-generator list at the rank-four M core

Wave 363. Work in progress.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 GQ2.SectionThree Multiplicative
open GQ2.Dyadic.EvenModel
open scoped GQ2.SectionThree.TopAbInstances

/-! ## The two mod-two reductions agree -/

/-- `N.lean`'s ring-hom reduction `nRed` and `M.lean`'s parity `mParityZ` are the same map.
Both files reduce a 2-adic integer mod two; only the packaging differs. -/
theorem mNielsenGen_nRed_eq_parity (x : ℤ_[2]) : nRed x = mParityZ x := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (mParityZ x) with h | h
  · obtain ⟨y, hy⟩ := (mParityZ_eq_zero_iff x).mp h
    rw [h, hy, map_mul, mFrame_nRed_two, zero_mul]
  · obtain ⟨y, hy⟩ := (mParityZ_eq_one_iff x).mp h
    rw [h, hy, map_add, map_one, map_mul, mFrame_nRed_two, zero_mul, add_zero]

/-! ## The mod-two coordinates of the full M frame -/

/-- The free cover used by the cup file and the one used by the matrix file are the same
continuous hom. -/
theorem mNielsenGen_cupFreeFrameProjection_eq {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (x : FreeTwoRank (coreRank h)) :
    mCupFreeFrameProjection ha h x = mFrameProjection ha h x := rfl

/-- **Every mod-two frame coordinate, evaluated on an arbitrary frame element.** -/
theorem mNielsenGen_coord {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (j : Fin (coreRank h))
    (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h j z) = nRed (mFrameCoordinateSection alpha z j) := by
  have hz : mCupFreeFrameProjection ha h
      (freeTwoCoordinateWord (coreRank h) (mFrameCoordinateSection alpha z)) = z :=
    mFrameProjection_coordinateSection ha h z
  conv_lhs => rw [← hz]
  rw [mCupFrameModTwoCoordinate_projection, freeTwoCoordinateWord_coordinate]

theorem mNielsenGen_coord_zero {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h 0 z) = z.toAdd.1 := by
  rw [mNielsenGen_coord ha h 0 z]
  show nRed (mSurjVec alpha _ _ _ _ _ 0) = _
  rw [mSurjVec_zero, mNielsenGen_nRed_eq_parity, mParityZ_natCast_val]

theorem mNielsenGen_coord_one {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h 1 z) = mParityZ z.toAdd.2.1 := by
  rw [mNielsenGen_coord ha h 1 z]
  show nRed (mSurjVec alpha _ _ _ _ _ 1) = _
  rw [mSurjVec_one, mNielsenGen_nRed_eq_parity]

theorem mNielsenGen_coord_two {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h 2 z) = mParityZ z.toAdd.2.2.1 := by
  rw [mNielsenGen_coord ha h 2 z]
  show nRed (mSurjVec alpha _ _ _ _ _ 2) = _
  rw [mSurjVec_two, map_add, map_mul, mFrame_nRed_halfExp ha, zero_mul, add_zero,
    mNielsenGen_nRed_eq_parity]

theorem mNielsenGen_coord_three {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h 3 z) = mParityZ z.toAdd.2.2.2.1 := by
  rw [mNielsenGen_coord ha h 3 z]
  show nRed (mSurjVec alpha _ _ _ _ _ 3) = _
  rw [mSurjVec_three, mNielsenGen_nRed_eq_parity]

/-! ## Every continuous mod-two character is its own coordinate expansion -/

theorem mNielsenGen_toAdd_zpowZtwo (q : Multiplicative (ZMod 2)) (a : ℤ_[2]) :
    toAdd (zpowZtwo isProP_two_multZMod2 q a) = mParityZ a * toAdd q := by
  have hq : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide
  rw [zpowZtwo_of_sq_eq_one isProP_two_multZMod2 q (hq q) a]
  show (PadicInt.toZModPow 1 a).val • toAdd q = _
  rw [nsmul_eq_mul]
  rfl

/-- **The character expansion.** A continuous mod-two character of the full M frame is
determined by its values on the canonical marks, linearly in the mod-two frame coordinates. -/
theorem mNielsenGen_character_apply {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (c : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2)))
    (z : MFrameModel h) :
    toAdd (c z) = ∑ j, toAdd (mCupFrameModTwoCoordinate ha h j z) *
      toAdd (c (mCupFrameCanonicalMark ha h j)) := by
  obtain ⟨x, rfl⟩ :=
    (mCupFrameOfDM_surjective ha).comp (mStageProjection_surjective alpha h) z
  have hx : (c.comp (mCupFreeFrameProjection ha h)) x =
      ∏ j, zpowZtwo isProP_two_multZMod2
        ((c.comp (mCupFreeFrameProjection ha h)) (freeTwoRankGen (coreRank h) j))
        (toAdd (freeTwoCoordinate (coreRank h) j x)) :=
    freeTwo_commutative_hom_coordinates isProP_two_multZMod2 (coreRank h) _ x
  have hgen : ∀ j, (c.comp (mCupFreeFrameProjection ha h)) (freeTwoRankGen (coreRank h) j) =
      c (mCupFrameCanonicalMark ha h j) := fun j =>
    congrArg c (mCupFreeFrameProjection_gen ha h j)
  simp only [hgen] at hx
  have hz : c (mCupFreeFrameProjection ha h x) =
      ∏ j, zpowZtwo isProP_two_multZMod2 (c (mCupFrameCanonicalMark ha h j))
        (toAdd (freeTwoCoordinate (coreRank h) j x)) := hx
  rw [show ((mCupFrameOfDM ha h) ∘ (mStageProjection alpha h)) x =
    mCupFreeFrameProjection ha h x from rfl, hz, toAdd_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mNielsenGen_toAdd_zpowZtwo, mCupFrameModTwoCoordinate_projection ha h j x,
    mNielsenGen_nRed_eq_parity]

end
end GQ2.Dyadic.MarkedCore
