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

/-! ## The frame action of a stabilizer parameter, as a continuous automorphism -/

private theorem mNielsenGen_cancel_two (a b : ZMod 2) : a + b + b = a := by revert a b; decide

private theorem mNielsenGen_parity_two : mParityZ (2 : ℤ_[2]) = 0 := by
  have h := mParityZ_two_mul 1
  rwa [mul_one] at h

/-- `MStabParam.act` written on the rank-four full M frame model `MFrameModel 0`. The empty
handle tail rides along untouched. -/
noncomputable def mNielsenGenMap (p : MStabParam) (z : MFrameModel 0) : MFrameModel 0 :=
  ofAdd (z.toAdd.1 + mParityZ z.toAdd.2.1 * p.tau + mParityZ z.toAdd.2.2.2.1 * mParityZ p.bc,
    z.toAdd.2.1 * (p.beta : ℤ_[2]) + z.toAdd.2.2.1 * (2 * p.c1) + z.toAdd.2.2.2.1 * (2 * p.d1),
    z.toAdd.2.1 * p.bc + z.toAdd.2.2.1 * (p.gamma : ℤ_[2]) + z.toAdd.2.2.2.1 * p.e,
    z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)

/-- The four core slots of `mNielsenGenMap p z` are literally `MStabParam.act`. -/
theorem mNielsenGenMap_toAdd (p : MStabParam) (z : MFrameModel 0) :
    (mNielsenGenMap p z).toAdd =
      ((p.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).1,
        (p.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.1,
        (p.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.1,
        (p.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.2,
        z.toAdd.2.2.2.2) := rfl

theorem mNielsenGenMap_comp_of_act (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (z : MFrameModel 0) :
    mNielsenGenMap p (mNielsenGenMap q z) = z := by
  have hl : mNielsenGenMap p (mNielsenGenMap q z) =
      ofAdd ((p.act (q.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1))).1,
        (p.act (q.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1))).2.1,
        (p.act (q.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1))).2.2.1,
        (p.act (q.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1))).2.2.2,
        z.toAdd.2.2.2.2) := rfl
  rw [hl, hpq (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)]
  rfl

theorem mNielsenGenMap_mul (p : MStabParam) (z w : MFrameModel 0) :
    mNielsenGenMap p (z * w) = mNielsenGenMap p z * mNielsenGenMap p w := by
  have hl : mNielsenGenMap p (z * w) = ofAdd
      (z.toAdd.1 + w.toAdd.1 + mParityZ (z.toAdd.2.1 + w.toAdd.2.1) * p.tau
         + mParityZ (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * mParityZ p.bc,
       (z.toAdd.2.1 + w.toAdd.2.1) * (p.beta : ℤ_[2])
         + (z.toAdd.2.2.1 + w.toAdd.2.2.1) * (2 * p.c1)
         + (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * (2 * p.d1),
       (z.toAdd.2.1 + w.toAdd.2.1) * p.bc
         + (z.toAdd.2.2.1 + w.toAdd.2.2.1) * (p.gamma : ℤ_[2])
         + (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * p.e,
       z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1, z.toAdd.2.2.2.2 + w.toAdd.2.2.2.2) := rfl
  have hr : mNielsenGenMap p z * mNielsenGenMap p w = ofAdd
      ((z.toAdd.1 + mParityZ z.toAdd.2.1 * p.tau + mParityZ z.toAdd.2.2.2.1 * mParityZ p.bc)
         + (w.toAdd.1 + mParityZ w.toAdd.2.1 * p.tau
           + mParityZ w.toAdd.2.2.2.1 * mParityZ p.bc),
       (z.toAdd.2.1 * (p.beta : ℤ_[2]) + z.toAdd.2.2.1 * (2 * p.c1)
           + z.toAdd.2.2.2.1 * (2 * p.d1))
         + (w.toAdd.2.1 * (p.beta : ℤ_[2]) + w.toAdd.2.2.1 * (2 * p.c1)
           + w.toAdd.2.2.2.1 * (2 * p.d1)),
       (z.toAdd.2.1 * p.bc + z.toAdd.2.2.1 * (p.gamma : ℤ_[2]) + z.toAdd.2.2.2.1 * p.e)
         + (w.toAdd.2.1 * p.bc + w.toAdd.2.2.1 * (p.gamma : ℤ_[2]) + w.toAdd.2.2.2.1 * p.e),
       z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1, z.toAdd.2.2.2.2 + w.toAdd.2.2.2.2) := rfl
  rw [hl, hr, mParityZ_add, mParityZ_add]
  exact congrArg ofAdd (Prod.ext (by ring) (Prod.ext (by ring) (Prod.ext (by ring)
    (Prod.ext rfl rfl))))

theorem mNielsenGenMap_continuous (p : MStabParam) : Continuous (mNielsenGenMap p) := by
  have hpar : Continuous mParityZ := mFrameParity_continuous
  have hA : Continuous fun z : MFrameModel 0 => z.toAdd.1 :=
    continuous_fst.comp continuous_toAdd
  have hB : Continuous fun z : MFrameModel 0 => z.toAdd.2.1 :=
    (continuous_fst.comp continuous_snd).comp continuous_toAdd
  have hC : Continuous fun z : MFrameModel 0 => z.toAdd.2.2.1 :=
    ((continuous_fst.comp continuous_snd).comp continuous_snd).comp continuous_toAdd
  have hD : Continuous fun z : MFrameModel 0 => z.toAdd.2.2.2.1 :=
    ((continuous_fst.comp continuous_snd).comp (continuous_snd.comp continuous_snd)).comp
      continuous_toAdd
  have hE : Continuous fun z : MFrameModel 0 => z.toAdd.2.2.2.2 :=
    ((continuous_snd.comp continuous_snd).comp (continuous_snd.comp continuous_snd)).comp
      continuous_toAdd
  refine continuous_ofAdd.comp (Continuous.prodMk ?_ (Continuous.prodMk ?_
    (Continuous.prodMk ?_ (Continuous.prodMk hD hE))))
  · exact (hA.add ((hpar.comp hB).mul continuous_const)).add
      ((hpar.comp hD).mul continuous_const)
  · exact ((hB.mul continuous_const).add (hC.mul continuous_const)).add
      (hD.mul continuous_const)
  · exact ((hB.mul continuous_const).add (hC.mul continuous_const)).add
      (hD.mul continuous_const)

/-- A pair of mutually inverse stabilizer parameters gives a continuous automorphism of the
rank-four full M frame. -/
noncomputable def mNielsenGenEquiv (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) :
    ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0) where
  toFun := mNielsenGenMap p
  invFun := mNielsenGenMap q
  left_inv := mNielsenGenMap_comp_of_act q p hqp
  right_inv := mNielsenGenMap_comp_of_act p q hpq
  map_mul' := mNielsenGenMap_mul p
  continuous_toFun := mNielsenGenMap_continuous p
  continuous_invFun := mNielsenGenMap_continuous q

@[simp] theorem mNielsenGenEquiv_apply (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) (z : MFrameModel 0) :
    mNielsenGenEquiv p q hpq hqp z = mNielsenGenMap p z := rfl

/-! ## Orientation: every stabilizer parameter preserves it -/

theorem mNielsenGenMap_parity_B (p : MStabParam) (z : MFrameModel 0) :
    mParityZ (mNielsenGenMap p z).toAdd.2.1 = mParityZ z.toAdd.2.1 := by
  have h : (mNielsenGenMap p z).toAdd.2.1 =
      z.toAdd.2.1 * (p.beta : ℤ_[2]) + z.toAdd.2.2.1 * (2 * p.c1)
        + z.toAdd.2.2.2.1 * (2 * p.d1) := rfl
  rw [h]
  simp only [mParityZ_add, mParityZ_mul, mNielsenGen_parity_two,
    mParityZ_of_isUnit p.beta.isUnit]
  ring

theorem mNielsenGenMap_coord_D (p : MStabParam) (z : MFrameModel 0) :
    (mNielsenGenMap p z).toAdd.2.2.2.1 = z.toAdd.2.2.2.1 := rfl

/-- **T1, orientation half.** The frame action of *every* rank-four stabilizer parameter
preserves the canonical M orientation: the integral `B` parity survives because `beta` is a
unit and the two other contributions are even, and the integral `D` coordinate is fixed
outright. -/
theorem mNielsenGen_orientation {alpha : ℕ} (ha : 2 ≤ alpha) (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) (z : MFrameModel 0) :
    mFrameOrientation ha 0 (mNielsenGenEquiv p q hpq hqp z) = mFrameOrientation ha 0 z :=
  (mFrameOrientation_preserved_iff ha 0 (mNielsenGenEquiv p q hpq hqp)).mpr
    (fun w => ⟨mNielsenGenMap_parity_B p w, mNielsenGenMap_coord_D p w⟩) z

/-! ## Cup: every stabilizer parameter is a full-frame cup isometry -/

private theorem mNielsenGen_sum_four (f : Fin (coreRank 0) → ZMod 2) :
    ∑ j, f j = f 0 + f 1 + f 2 + f 3 := by
  show ∑ j : Fin 4, f j = _
  rw [Fin.sum_univ_four]
  rfl

theorem mNielsenGen_evenCup_zero (v w : Fin (coreRank 0) → ZMod 2) :
    evenCupForm v w = v 0 * w 0 + (v 0 * w 1 + v 1 * w 0) + (v 2 * w 3 + v 3 * w 2) := by
  rw [evenCupForm]
  simp

/-- The mod-two frame coordinates of the image, in terms of those of the source: this is the
column-convention reduced matrix of the parameter, read semantically. -/
theorem mNielsenGen_image_coord_zero {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (z : MFrameModel 0) :
    toAdd (mCupFrameModTwoCoordinate ha 0 0 (mNielsenGenMap p z))
      = toAdd (mCupFrameModTwoCoordinate ha 0 0 z)
        + toAdd (mCupFrameModTwoCoordinate ha 0 1 z) * p.tau
        + toAdd (mCupFrameModTwoCoordinate ha 0 3 z) * mParityZ p.bc := by
  rw [mNielsenGen_coord_zero ha 0 (mNielsenGenMap p z), mNielsenGen_coord_zero ha 0 z,
    mNielsenGen_coord_one ha 0 z, mNielsenGen_coord_three ha 0 z]
  rfl

theorem mNielsenGen_image_coord_one {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (z : MFrameModel 0) :
    toAdd (mCupFrameModTwoCoordinate ha 0 1 (mNielsenGenMap p z))
      = toAdd (mCupFrameModTwoCoordinate ha 0 1 z) := by
  rw [mNielsenGen_coord_one ha 0 (mNielsenGenMap p z), mNielsenGen_coord_one ha 0 z]
  exact mNielsenGenMap_parity_B p z

theorem mNielsenGen_image_coord_two {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (z : MFrameModel 0) :
    toAdd (mCupFrameModTwoCoordinate ha 0 2 (mNielsenGenMap p z))
      = toAdd (mCupFrameModTwoCoordinate ha 0 1 z) * mParityZ p.bc
        + toAdd (mCupFrameModTwoCoordinate ha 0 2 z)
        + toAdd (mCupFrameModTwoCoordinate ha 0 3 z) * mParityZ p.e := by
  have h : (mNielsenGenMap p z).toAdd.2.2.1
      = z.toAdd.2.1 * p.bc + z.toAdd.2.2.1 * (p.gamma : ℤ_[2])
        + z.toAdd.2.2.2.1 * p.e := rfl
  rw [mNielsenGen_coord_two ha 0 (mNielsenGenMap p z), mNielsenGen_coord_one ha 0 z,
    mNielsenGen_coord_two ha 0 z, mNielsenGen_coord_three ha 0 z, h,
    mParityZ_add, mParityZ_add, mParityZ_mul, mParityZ_mul, mParityZ_mul,
    mParityZ_of_isUnit p.gamma.isUnit]
  ring

theorem mNielsenGen_image_coord_three {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (z : MFrameModel 0) :
    toAdd (mCupFrameModTwoCoordinate ha 0 3 (mNielsenGenMap p z))
      = toAdd (mCupFrameModTwoCoordinate ha 0 3 z) := by
  rw [mNielsenGen_coord_three ha 0 (mNielsenGenMap p z), mNielsenGen_coord_three ha 0 z]
  rfl

/-- The value of a mod-two character on the image of a frame element. -/
theorem mNielsenGen_char_image {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel 0) (Multiplicative (ZMod 2))) (z : MFrameModel 0) :
    toAdd (c (mNielsenGenMap p z))
      = (toAdd (mCupFrameModTwoCoordinate ha 0 0 z)
            + toAdd (mCupFrameModTwoCoordinate ha 0 1 z) * p.tau
            + toAdd (mCupFrameModTwoCoordinate ha 0 3 z) * mParityZ p.bc)
          * toAdd (c (mCupFrameCanonicalMark ha 0 0))
        + toAdd (mCupFrameModTwoCoordinate ha 0 1 z)
          * toAdd (c (mCupFrameCanonicalMark ha 0 1))
        + (toAdd (mCupFrameModTwoCoordinate ha 0 1 z) * mParityZ p.bc
            + toAdd (mCupFrameModTwoCoordinate ha 0 2 z)
            + toAdd (mCupFrameModTwoCoordinate ha 0 3 z) * mParityZ p.e)
          * toAdd (c (mCupFrameCanonicalMark ha 0 2))
        + toAdd (mCupFrameModTwoCoordinate ha 0 3 z)
          * toAdd (c (mCupFrameCanonicalMark ha 0 3)) := by
  rw [mNielsenGen_character_apply ha 0 c (mNielsenGenMap p z), mNielsenGen_sum_four,
    mNielsenGen_image_coord_zero ha p z, mNielsenGen_image_coord_one ha p z,
    mNielsenGen_image_coord_two ha p z, mNielsenGen_image_coord_three ha p z]

private theorem mNielsenGen_markCoord {alpha : ℕ} (ha : 2 ≤ alpha) (i j : Fin (coreRank 0)) :
    toAdd (mCupFrameModTwoCoordinate ha 0 j (mCupFrameCanonicalMark ha 0 i))
      = if i = j then 1 else 0 :=
  mCupFrameModTwoCoordinate_canonicalMark ha 0 j i

theorem mNielsenGen_char_mark_zero {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel 0) (Multiplicative (ZMod 2))) :
    toAdd (c (mNielsenGenMap p (mCupFrameCanonicalMark ha 0 0)))
      = toAdd (c (mCupFrameCanonicalMark ha 0 0)) := by
  rw [mNielsenGen_char_image ha p c (mCupFrameCanonicalMark ha 0 0)]
  simp only [mNielsenGen_markCoord ha, Fin.ext_iff, coreVal_zero, coreVal_one, coreVal_two,
    coreVal_three]
  norm_num

theorem mNielsenGen_char_mark_one {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel 0) (Multiplicative (ZMod 2))) :
    toAdd (c (mNielsenGenMap p (mCupFrameCanonicalMark ha 0 1)))
      = p.tau * toAdd (c (mCupFrameCanonicalMark ha 0 0))
        + toAdd (c (mCupFrameCanonicalMark ha 0 1))
        + mParityZ p.bc * toAdd (c (mCupFrameCanonicalMark ha 0 2)) := by
  rw [mNielsenGen_char_image ha p c (mCupFrameCanonicalMark ha 0 1)]
  simp only [mNielsenGen_markCoord ha, Fin.ext_iff, coreVal_zero, coreVal_one, coreVal_two,
    coreVal_three]
  norm_num

theorem mNielsenGen_char_mark_two {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel 0) (Multiplicative (ZMod 2))) :
    toAdd (c (mNielsenGenMap p (mCupFrameCanonicalMark ha 0 2)))
      = toAdd (c (mCupFrameCanonicalMark ha 0 2)) := by
  rw [mNielsenGen_char_image ha p c (mCupFrameCanonicalMark ha 0 2)]
  simp only [mNielsenGen_markCoord ha, Fin.ext_iff, coreVal_zero, coreVal_one, coreVal_two,
    coreVal_three]
  norm_num

theorem mNielsenGen_char_mark_three {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel 0) (Multiplicative (ZMod 2))) :
    toAdd (c (mNielsenGenMap p (mCupFrameCanonicalMark ha 0 3)))
      = mParityZ p.bc * toAdd (c (mCupFrameCanonicalMark ha 0 0))
        + mParityZ p.e * toAdd (c (mCupFrameCanonicalMark ha 0 2))
        + toAdd (c (mCupFrameCanonicalMark ha 0 3)) := by
  rw [mNielsenGen_char_image ha p c (mCupFrameCanonicalMark ha 0 3)]
  simp only [mNielsenGen_markCoord ha, Fin.ext_iff, coreVal_zero, coreVal_one, coreVal_two,
    coreVal_three]
  norm_num

private theorem mNielsenGen_cup_core (s m n a0 a1 a2 a3 b0 b1 b2 b3 : ZMod 2) :
    a0 * b0 + (a0 * (s * b0 + b1 + m * b2) + (s * a0 + a1 + m * a2) * b0)
        + (a2 * (m * b0 + n * b2 + b3) + (m * a0 + n * a2 + a3) * b2)
      = a0 * b0 + (a0 * b1 + a1 * b0) + (a2 * b3 + a3 * b2) := by
  revert s m n a0 a1 a2 a3 b0 b1 b2 b3
  decide

/-- **T1, cup half.** The frame action of *every* rank-four stabilizer parameter is a full
mod-two cup isometry of the actual M frame, in the semantic sense that quantifies over all
continuous mod-two frame characters. -/
theorem mNielsenGen_cupIsometry {alpha : ℕ} (ha : 2 ≤ alpha) (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) :
    MCupFrameCupIsometry ha (mNielsenGenEquiv p q hpq hqp) := by
  intro c d
  rw [mNielsenGen_evenCup_zero, mNielsenGen_evenCup_zero]
  simp only [mNielsenGenEquiv_apply]
  rw [mNielsenGen_char_mark_zero ha p c, mNielsenGen_char_mark_one ha p c,
    mNielsenGen_char_mark_two ha p c, mNielsenGen_char_mark_three ha p c,
    mNielsenGen_char_mark_zero ha p d, mNielsenGen_char_mark_one ha p d,
    mNielsenGen_char_mark_two ha p d, mNielsenGen_char_mark_three ha p d]
  exact mNielsenGen_cup_core _ _ _ _ _ _ _ _ _ _ _

end
end GQ2.Dyadic.MarkedCore
