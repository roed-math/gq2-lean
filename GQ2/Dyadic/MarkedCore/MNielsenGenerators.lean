/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.MFullStabilizerLift

/-!
# The finite Nielsen-generator list at the rank-four M core

Wave 363, lane MC-M. The packet (`docs/dyadic/refs/dyadic-presentations-formalization-proof.tex`,
row **MC-M**) asks for

> A finite list of orientation-preserving Nielsen generators lifts the Smith-Witt stabilizer
> on the abelianization; composition gives every required marking correction.

This file produces that list, at handle rank **zero** (the rank-four core) and for
`alpha >= 2`, as a corollary of wave 362's `mFullStabilizer_lift`.

## What is here

* **The bridge (T1).** `M.lean`'s classification `mStabilizer_classification` speaks of a
  seven-parameter `MStabParam` acting on the rank-four frame in the row convention, while
  wave 362's lifting theorem wants a `ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0)`
  satisfying `mFrameOrientation`-preservation and the semantic `MCupFrameCupIsometry`.
  `mNielsenGenMap` carries `MStabParam.act` onto `MFrameModel 0`; `mNielsenGen_orientation`
  and `mNielsenGen_cupIsometry` discharge both hypotheses **for every parameter** (each
  equivalence takes the parameter together with a supplied inverse parameter, `mNielsenGenEquiv
  p q hpq hqp`; no inverse or group structure on `MStabParam` exists in the tree, and the seven
  families supply their own inverses).
* **The seven families.** Each of `mFamM1` through `mFamM7` has an explicit inverse inside its own
  family, so `mNielsenGenM1` through `mNielsenGenM7` are honest continuous frame automorphisms.
* **The artifact (T2).** `mNielsenGen_finite_list`: for every stabilizer parameter there is a
  seven-element list of such generators, each of which lifts to `D_M`, whose composite is the
  parameter's own frame action, together with a lift of that composite; and
  `mNielsenGen_param_realized`, the same statement with the list projected away.
* **The quantifier closure.** `mNielsenGen_frameAction_of_realizes` identifies the frame
  automorphism that `mStabilizer_classification` classifies with `mNielsenGenMap` at its
  parameter, so `mNielsenGen_stabilizer_induced` reads over *every element of the Smith-Witt
  stabilizer* rather than over every `MStabParam`: each such element is induced by an actual
  `chiM`-preserving continuous automorphism of `D_M`, with the exact square
  `abMk (Psi x) = xi (abMk x)`.

## What this does *not* do

The lifts of the individual generators come from `mFullStabilizer_lift`, i.e. from
the uniform filtered-correction and compactness argument of waves 361/362. **No generator is
lifted by an explicit group-level construction here**, and no such construction is claimed.
Families M1 and M2 do have honest independent group-level lifts elsewhere in the repo
(`M.lean`'s `mLambdaEquiv` and HM4's `dmTauDEquiv`); this file supplies none for the others. See
`docs/dyadic/w363-nielsen-note.md`. [W364 correction (packet lane): the inventory of the others is:
M3 has a group-level construction only through `MScaling`, whose route consumes the standing
input `peripheralCyclotomicAction` (B8); M5 has `mMixFamily_coreMix` (`CoreMixM.lean:304`), the
pure M5 move at every parameter and every `h`, stated on `Z_2`-valued characters and so not
pinning the torsion coordinate; M4, M6, M7 have no group-level construction anywhere in the
repo.]

Scope of the list: the seven Nielsen *families*, each parameterized by a 2-adic number or unit;
what the theorem produces for a given stabilizer element is one member of each family. A
literally finite generating set is impossible here, the stabilizer not being finitely generated
as an abstract group.

Scope: handle rank **zero** only, since `mStabilizer_classification` and
`mNielsen_factorization` are rank-four statements. `alpha >= 2` throughout.

## How the cup condition is proved

`MCupFrameCupIsometry` quantifies over *all* continuous mod-two characters of the frame, and
the repo had no producer for it other than "comes from an actual core automorphism"
(`mCupFrameCupIsometry_of_aut`), which is exactly what is not available for families M4, M6, M7
(and only conditionally, or on ordinary characters, for M3 and M5; see the inventory above).
So the semantic condition is reduced here to a finite mod-two matrix identity:

* `mNielsenGen_coord_zero` through `mNielsenGen_coord_three` read the four mod-two frame coordinates off an arbitrary
  frame element (the forced `A`-row correction `2^(alpha-1)` is invisible mod two once
  `alpha >= 2`, which is where that binder is used);
* `mNielsenGen_character_apply` expands an arbitrary continuous mod-two character in those
  coordinates, using the free pro-two coordinate expansion
  `freeTwo_commutative_hom_coordinates` pushed through the surjection
  `mCupFreeFrameProjection`;
* `mNielsenGen_image_coord_*` compute the reduced **column-convention** matrix of a parameter
  directly from the semantics, and `mNielsenGen_cup_core` is the resulting finite `F2` check.

`MarkedCore/Variance.lean` is therefore not an input: nothing here reads `M.lean`'s
row-convention `mFrameMatrix`, so no transposition has to be arranged. The matrix that comes
out is the transpose of `mFrameMatrix_of_realizes`'s, as that dictionary predicts.

Every declaration in this file is std-3 (`propext`, `Classical.choice`, `Quot.sound`).
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

/-! ## The seven Nielsen families as frame automorphisms -/

theorem mNielsenGen_M1_inv {alpha : ℕ} (ha : 2 ≤ alpha) (k : ℤ_[2])
    (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    (mFamM1 alpha k).act ((mFamM1 alpha (-k)).act v) = v := by
  obtain ⟨v1, b, c, d⟩ := v
  rw [mFamM1_act ha, mFamM1_act ha]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * mParityZ (-k) + mParityZ b * mParityZ k = v1
    rw [mParityZ_neg]
    exact mNielsenGen_cancel_two v1 (mParityZ b * mParityZ k)
  · show c - -k * 2 ^ (alpha - 1) * b - k * 2 ^ (alpha - 1) * b = c
    ring

theorem mNielsenGen_M2_inv (e : ℤ_[2]) (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    (mFamM2 e).act ((mFamM2 (-e)).act v) = v := by
  obtain ⟨v1, b, c, d⟩ := v
  rw [mFamM2_act, mFamM2_act]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  show c + d * -e + d * e = c
  ring

theorem mNielsenGen_M3_inv (gamma : ℤ_[2]ˣ) (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    (mFamM3 gamma).act ((mFamM3 gamma⁻¹).act v) = v := by
  obtain ⟨v1, b, c, d⟩ := v
  rw [mFamM3_act, mFamM3_act]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  show c * ((gamma⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((gamma : ℤ_[2]ˣ) : ℤ_[2]) = c
  rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

theorem mNielsenGen_M4_inv (beta : ℤ_[2]ˣ) (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    (mFamM4 beta).act ((mFamM4 beta⁻¹).act v) = v := by
  obtain ⟨v1, b, c, d⟩ := v
  rw [mFamM4_act, mFamM4_act]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl rfl))
  show b * ((beta⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((beta : ℤ_[2]ˣ) : ℤ_[2]) = b
  rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

theorem mNielsenGen_M5_inv (bc : ℤ_[2]) (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    (mFamM5 bc).act ((mFamM5 (-bc)).act v) = v := by
  obtain ⟨v1, b, c, d⟩ := v
  rw [mFamM5_act, mFamM5_act]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ rfl))
  · show v1 + mParityZ d * mParityZ (-bc) + mParityZ d * mParityZ bc = v1
    rw [mParityZ_neg]
    exact mNielsenGen_cancel_two v1 (mParityZ d * mParityZ bc)
  · show b * bc + (b * -bc + c) = c
    ring

theorem mNielsenGen_M6_inv (c1 : ℤ_[2]) (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    (mFamM6 c1).act ((mFamM6 (-c1)).act v) = v := by
  obtain ⟨v1, b, c, d⟩ := v
  rw [mFamM6_act, mFamM6_act]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl rfl))
  show b + c * (2 * -c1) + c * (2 * c1) = b
  ring

theorem mNielsenGen_M7_inv (d1 : ℤ_[2]) (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    (mFamM7 d1).act ((mFamM7 (-d1)).act v) = v := by
  obtain ⟨v1, b, c, d⟩ := v
  rw [mFamM7_act, mFamM7_act]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl rfl))
  show b + d * (2 * -d1) + d * (2 * d1) = b
  ring

/-- Family **M1** `Lambda_k : B -> A^k B` as a frame automorphism. -/
noncomputable def mNielsenGenM1 {alpha : ℕ} (ha : 2 ≤ alpha) (k : ℤ_[2]) :
    ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0) :=
  mNielsenGenEquiv (mFamM1 alpha k) (mFamM1 alpha (-k)) (mNielsenGen_M1_inv ha k)
    (fun v => by simpa only [neg_neg] using mNielsenGen_M1_inv ha (-k) v)

/-- Family **M2** `E_e : D -> C0^e D` as a frame automorphism. -/
noncomputable def mNielsenGenM2 (e : ℤ_[2]) :
    ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0) :=
  mNielsenGenEquiv (mFamM2 e) (mFamM2 (-e)) (mNielsenGen_M2_inv e)
    (fun v => by simpa only [neg_neg] using mNielsenGen_M2_inv (-e) v)

/-- Family **M3** `Sigma_gamma : C0 -> C0^gamma` as a frame automorphism. -/
noncomputable def mNielsenGenM3 (gamma : ℤ_[2]ˣ) :
    ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0) :=
  mNielsenGenEquiv (mFamM3 gamma) (mFamM3 gamma⁻¹) (mNielsenGen_M3_inv gamma)
    (fun v => by simpa only [inv_inv] using mNielsenGen_M3_inv gamma⁻¹ v)

/-- Family **M4** `Sigma_beta : B -> B^beta` as a frame automorphism. -/
noncomputable def mNielsenGenM4 (beta : ℤ_[2]ˣ) :
    ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0) :=
  mNielsenGenEquiv (mFamM4 beta) (mFamM4 beta⁻¹) (mNielsenGen_M4_inv beta)
    (fun v => by simpa only [inv_inv] using mNielsenGen_M4_inv beta⁻¹ v)

/-- Family **M5** `X_b : B -> B C0^{B_c}`, `D -> t^{B_c} D` as a frame automorphism. -/
noncomputable def mNielsenGenM5 (bc : ℤ_[2]) :
    ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0) :=
  mNielsenGenEquiv (mFamM5 bc) (mFamM5 (-bc)) (mNielsenGen_M5_inv bc)
    (fun v => by simpa only [neg_neg] using mNielsenGen_M5_inv (-bc) v)

/-- Family **M6** `Y_c : C0 -> B^{2c1} C0` as a frame automorphism. -/
noncomputable def mNielsenGenM6 (c1 : ℤ_[2]) :
    ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0) :=
  mNielsenGenEquiv (mFamM6 c1) (mFamM6 (-c1)) (mNielsenGen_M6_inv c1)
    (fun v => by simpa only [neg_neg] using mNielsenGen_M6_inv (-c1) v)

/-- Family **M7** `Z_d : D -> B^{2d1} D` as a frame automorphism. -/
noncomputable def mNielsenGenM7 (d1 : ℤ_[2]) :
    ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0) :=
  mNielsenGenEquiv (mFamM7 d1) (mFamM7 (-d1)) (mNielsenGen_M7_inv d1)
    (fun v => by simpa only [neg_neg] using mNielsenGen_M7_inv (-d1) v)

/-! ## Composition: of frame automorphisms, and of their lifts -/

/-- An arbitrary coordinate map transported to the rank-four full M frame. It exists only so
that the composition calculus below is definitional. -/
noncomputable def mNielsenGenLift
    (F : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] → ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2])
    (z : MFrameModel 0) : MFrameModel 0 :=
  ofAdd ((F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).1,
    (F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.1,
    (F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.1,
    (F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.2,
    z.toAdd.2.2.2.2)

theorem mNielsenGenMap_eq_lift (p : MStabParam) :
    mNielsenGenMap p = mNielsenGenLift p.act := rfl

theorem mNielsenGenLift_comp
    (F G : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] → ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2])
    (z : MFrameModel 0) :
    mNielsenGenLift F (mNielsenGenLift G z) = mNielsenGenLift (F ∘ G) z := rfl

/-- `Psi` is an actual `chiM`-preserving continuous automorphism of the rank-four core
inducing `phi` on the full abelian frame, with the exact all-element commuting square. This
is verbatim the conclusion of `mFullStabilizer_lift` at `h = 0`. -/
def MNielsenGenLifts {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0)) : Prop :=
  ∃ Psi : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type),
    (∀ x, chiM alpha 0 (Psi x) = chiM alpha 0 x) ∧
    (∀ x, mPhiHom (mStageOneLe ha) 0 (abMk (Psi x)) =
      phi (mPhiHom (mStageOneLe ha) 0 (abMk x)))

/-- The identity frame automorphism lifts. -/
theorem mNielsenGenLifts_refl {alpha : ℕ} (ha : 2 ≤ alpha) :
    MNielsenGenLifts ha (ContinuousMulEquiv.refl (MFrameModel 0)) :=
  ⟨ContinuousMulEquiv.refl _, fun _ => rfl, fun _ => rfl⟩

/-- **The composite of the lifts is a lift of the composite.** -/
theorem mNielsenGenLifts_trans {alpha : ℕ} (ha : 2 ≤ alpha)
    {phi psi : ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0)}
    (h1 : MNielsenGenLifts ha phi) (h2 : MNielsenGenLifts ha psi) :
    MNielsenGenLifts ha (phi.trans psi) := by
  obtain ⟨P, hP1, hP2⟩ := h1
  obtain ⟨Q, hQ1, hQ2⟩ := h2
  refine ⟨P.trans Q, fun x => ?_, fun x => ?_⟩
  · exact (hQ1 (P x)).trans (hP1 x)
  · show mPhiHom (mStageOneLe ha) 0 (abMk (Q (P x))) = psi (phi _)
    rw [hQ2 (P x), hP2 x]

/-- The composite of a finite list of frame automorphisms, leftmost applied first. -/
noncomputable def mNielsenGenCompose
    (L : List (ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0))) :
    ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0) :=
  L.foldr (fun g e => g.trans e) (ContinuousMulEquiv.refl _)

theorem mNielsenGenLifts_compose {alpha : ℕ} (ha : 2 ≤ alpha)
    (L : List (ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0)))
    (h : ∀ g ∈ L, MNielsenGenLifts ha g) :
    MNielsenGenLifts ha (mNielsenGenCompose L) := by
  induction L with
  | nil => exact mNielsenGenLifts_refl ha
  | cons g L ih =>
      exact mNielsenGenLifts_trans ha (h g (List.mem_cons_self))
        (ih fun x hx => h x (List.mem_cons_of_mem g hx))

/-- Every frame automorphism built from a stabilizer parameter lifts. This is `T1` fed to
wave 362's unconditional `mFullStabilizer_lift`. -/
theorem mNielsenGenLifts_of_param {alpha : ℕ} (ha : 2 ≤ alpha) (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) :
    MNielsenGenLifts ha (mNielsenGenEquiv p q hpq hqp) :=
  mFullStabilizer_lift ha (mNielsenGenEquiv p q hpq hqp)
    (mNielsenGen_orientation ha p q hpq hqp) (mNielsenGen_cupIsometry ha p q hpq hqp)

/-! ## The packet's finite list -/

/-- **The finite list of Nielsen generators**, in the memo order
`Sigma_gamma, Lambda_k, X_b, E_e, Sigma_beta, Y_c, Z_d` (leftmost applied first). -/
noncomputable def mNielsenGenList {alpha : ℕ} (ha : 2 ≤ alpha) (gamma : ℤ_[2]ˣ)
    (k b e : ℤ_[2]) (beta : ℤ_[2]ˣ) (c d : ℤ_[2]) :
    List (ContinuousMulEquiv (MFrameModel 0) (MFrameModel 0)) :=
  [mNielsenGenM3 gamma, mNielsenGenM1 ha k, mNielsenGenM5 b, mNielsenGenM2 e,
    mNielsenGenM4 beta, mNielsenGenM6 c, mNielsenGenM7 d]

theorem mNielsenGenList_length {alpha : ℕ} (ha : 2 ≤ alpha) (gamma : ℤ_[2]ˣ)
    (k b e : ℤ_[2]) (beta : ℤ_[2]ˣ) (c d : ℤ_[2]) :
    (mNielsenGenList ha gamma k b e beta c d).length = 7 := rfl

theorem mNielsenGenCompose_list {alpha : ℕ} (ha : 2 ≤ alpha) (gamma : ℤ_[2]ˣ)
    (k b e : ℤ_[2]) (beta : ℤ_[2]ˣ) (c d : ℤ_[2]) (z : MFrameModel 0) :
    mNielsenGenCompose (mNielsenGenList ha gamma k b e beta c d) z =
      mNielsenGenLift ((mFamM7 d).act ∘ (mFamM6 c).act ∘ (mFamM4 beta).act ∘ (mFamM2 e).act ∘
        (mFamM5 b).act ∘ (mFamM1 alpha k).act ∘ (mFamM3 gamma).act) z := rfl

/-- Each generator preserves the orientation, is a cup isometry, and lifts. -/
theorem mNielsenGen_props_of_param {alpha : ℕ} (ha : 2 ≤ alpha) (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) :
    (∀ z, mFrameOrientation ha 0 (mNielsenGenEquiv p q hpq hqp z)
        = mFrameOrientation ha 0 z) ∧
      MCupFrameCupIsometry ha (mNielsenGenEquiv p q hpq hqp) ∧
      MNielsenGenLifts ha (mNielsenGenEquiv p q hpq hqp) :=
  ⟨mNielsenGen_orientation ha p q hpq hqp, mNielsenGen_cupIsometry ha p q hpq hqp,
    mNielsenGenLifts_of_param ha p q hpq hqp⟩

theorem mNielsenGenList_props {alpha : ℕ} (ha : 2 ≤ alpha) (gamma : ℤ_[2]ˣ)
    (k b e : ℤ_[2]) (beta : ℤ_[2]ˣ) (c d : ℤ_[2]) :
    ∀ g ∈ mNielsenGenList ha gamma k b e beta c d,
      (∀ z, mFrameOrientation ha 0 (g z) = mFrameOrientation ha 0 z) ∧
        MCupFrameCupIsometry ha g ∧ MNielsenGenLifts ha g := by
  intro g hg
  simp only [mNielsenGenList, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact mNielsenGen_props_of_param ha _ _ _ _

/-- **The packet's MC-M finite-list artifact at the rank-four core** (`h = 0`, `alpha >= 2`).

For every parameter `p : MStabParam`, equivalently (by `mStabilizer_classification`) for
every element of the Smith-Witt stabilizer of the rank-four abelianization, there is an
explicit list of **seven** frame automorphisms, each one a member of the memo's seven Nielsen
families at an explicit parameter, such that

1. every member preserves the canonical orientation and the full mod-two cup form, and
   therefore lifts to an actual `chiM`-preserving continuous automorphism of `D_M` with the
   exact all-element commuting frame square;
2. the composite of the list is the frame action of `p`; and
3. the composite of the lifts is a lift of that composite.

The lifts in (1) are supplied by wave 362's `mFullStabilizer_lift`, i.e. by the
uniform filtered-correction and compactness argument, **not** by an explicit
generator-by-generator group-level construction. -/
theorem mNielsenGen_finite_list {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam) :
    ∃ (k b₅ e₅ c₆ d₇ : ℤ_[2]) (β₄ : ℤ_[2]ˣ),
      (mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇).length = 7 ∧
      (∀ g ∈ mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇,
        (∀ z, mFrameOrientation ha 0 (g z) = mFrameOrientation ha 0 z) ∧
          MCupFrameCupIsometry ha g ∧ MNielsenGenLifts ha g) ∧
      (∀ z, mNielsenGenCompose (mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇) z
        = mNielsenGenMap p z) ∧
      MNielsenGenLifts ha
        (mNielsenGenCompose (mNielsenGenList ha p.gamma k b₅ e₅ β₄ c₆ d₇)) := by
  obtain ⟨k, b₅, e₅, c₆, d₇, β₄, hfac⟩ := mNielsen_factorization ha p
  refine ⟨k, b₅, e₅, c₆, d₇, β₄, mNielsenGenList_length ha _ _ _ _ _ _ _,
    mNielsenGenList_props ha _ _ _ _ _ _ _, fun z => ?_, ?_⟩
  · rw [mNielsenGenCompose_list, mNielsenGenMap_eq_lift, hfac]
  · exact mNielsenGenLifts_compose ha _
      (fun g hg => (mNielsenGenList_props ha _ _ _ _ _ _ _ g hg).2.2)

/-- **Every classified rank-four stabilizer parameter is realized by an actual core
automorphism**, as the composite of the seven Nielsen generators' lifts. -/
theorem mNielsenGen_param_realized {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam) :
    ∃ Psi : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type),
      (∀ x, chiM alpha 0 (Psi x) = chiM alpha 0 x) ∧
      (∀ x, mPhiHom (mStageOneLe ha) 0 (abMk (Psi x)) =
        mNielsenGenMap p (mPhiHom (mStageOneLe ha) 0 (abMk x))) := by
  obtain ⟨k, b₅, e₅, c₆, d₇, β₄, _, _, hcomp, Psi, hchi, hsq⟩ := mNielsenGen_finite_list ha p
  exact ⟨Psi, hchi, fun x => (hsq x).trans (hcomp _)⟩

/-! ## Closing the quantifier against `mStabilizer_classification` -/

/-- The canonical rank-four M frame, the `h = 0` instance of `mFrameExists_phiEquiv`. -/
noncomputable def mNielsenGenFrame {alpha : ℕ} (ha : 2 ≤ alpha) : MFrame alpha 0 where
  e := mFrameExists_phiEquiv (mStageOneLe ha) 0
  map_t := mPhiHom_t (mStageOneLe ha) 0
  map_B := mPhiHom_B (mStageOneLe ha) 0
  map_C := mPhiHom_C (mStageOneLe ha) 0
  map_D := mPhiHom_D (mStageOneLe ha) 0
  map_U := fun j => mPhiHom_U (mStageOneLe ha) j
  map_V := fun j => mPhiHom_V (mStageOneLe ha) j

/-- The frame action of a parameter, packaged as a continuous hom. -/
noncomputable def mNielsenGenHom (p : MStabParam) :
    ContinuousMonoidHom (MFrameModel 0) (MFrameModel 0) :=
  ⟨MonoidHom.mk' (mNielsenGenMap p) (mNielsenGenMap_mul p), mNielsenGenMap_continuous p⟩

/-- The canonical marks generate the full M frame topologically, so two continuous homs out
of it that agree on the marks agree. -/
theorem mNielsenGen_frame_hom_ext {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    (f g : ContinuousMonoidHom (MFrameModel h) X)
    (hgen : ∀ i, f (mCupFrameCanonicalMark ha h i) = g (mCupFrameCanonicalMark ha h i))
    (z : MFrameModel h) : f z = g z := by
  obtain ⟨x, rfl⟩ :=
    (mCupFrameOfDM_surjective ha).comp (mStageProjection_surjective alpha h) z
  have he : f.comp (mCupFreeFrameProjection ha h) = g.comp (mCupFreeFrameProjection ha h) := by
    apply presPro2_hom_ext
    intro i
    change f (mCupFreeFrameProjection ha h (freeTwoRankGen (coreRank h) i)) =
      g (mCupFreeFrameProjection ha h (freeTwoRankGen (coreRank h) i))
    rw [mCupFreeFrameProjection_gen]
    exact hgen i
  exact DFunLike.congr_fun he x

/-- **The frame action of a classified stabilizer element is `mNielsenGenMap` at its
parameter.** This is the step that turns "for every `p : MStabParam`" into "for every element
of the Smith-Witt stabilizer": `mStabilizer_classification` supplies the `p`, and this lemma
says the frame automorphism it classifies is exactly the one this file builds. -/
theorem mNielsenGen_frameAction_of_realizes {alpha : ℕ} (ha : 2 ≤ alpha) (p : MStabParam)
    (xi : ContinuousMulEquiv (topAbelianization (DM alpha 0 : Type))
      (topAbelianization (DM alpha 0 : Type)))
    (hp : p.Realizes (mNielsenGenFrame ha).toMDecomposition xi)
    (x : topAbelianization (DM alpha 0 : Type)) :
    mPhiHom (mStageOneLe ha) 0 (xi x) =
      mNielsenGenMap p (mPhiHom (mStageOneLe ha) 0 x) := by
  set E := mFrameExists_phiEquiv (mStageOneLe ha) 0 with hE
  set f : ContinuousMonoidHom (MFrameModel 0) (MFrameModel 0) :=
    (⟨E.toMulEquiv.toMonoidHom, E.continuous_toFun⟩ : ContinuousMonoidHom _ _).comp
      ((⟨xi.toMulEquiv.toMonoidHom, xi.continuous_toFun⟩ : ContinuousMonoidHom _ _).comp
        ⟨E.symm.toMulEquiv.toMonoidHom, E.symm.continuous_toFun⟩) with hf
  have hmark : ∀ i, E.symm (mCupFrameCanonicalMark ha 0 i) = abMk (dmGen alpha 0 i) :=
    fun i => E.symm_apply_apply _
  have hfapp : ∀ i, f (mCupFrameCanonicalMark ha 0 i) = E (xi (abMk (dmGen alpha 0 i))) :=
    fun i => congrArg (fun y => E (xi y)) (hmark i)
  -- the three classified rows, read back in `MFrameModel 0`
  have hrow : ∀ (i : Fin (coreRank 0)) (w : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]),
      (mNielsenGenFrame ha).toMDecomposition.e (xi (abMk (dmGen alpha 0 i))) = ofAdd w →
      f (mCupFrameCanonicalMark ha 0 i) = ofAdd (w.1, w.2.1, w.2.2.1, w.2.2.2, 0) := by
    intro i w hw
    rw [hfapp i]
    have h2 : mFrameModelZero (E (xi (abMk (dmGen alpha 0 i)))) = ofAdd w := hw
    exact mFrameModelZero.injective (h2.trans rfl)
  have hgen : ∀ i, f (mCupFrameCanonicalMark ha 0 i) = mNielsenGenHom p
      (mCupFrameCanonicalMark ha 0 i) := by
    have hi4 : ∀ i : Fin (coreRank 0), i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    intro i
    rcases hi4 i with rfl | rfl | rfl | rfl
    · have hA := mStabilizer_A_row (le_trans one_le_two ha)
        (mNielsenGenFrame ha).toMDecomposition xi hp
      rw [hrow 0 _ hA]
      show _ = mNielsenGenMap p (mCupFrameCanonicalMark ha 0 0)
      rw [show mCupFrameCanonicalMark ha 0 (0 : Fin (coreRank 0))
          = ofAdd ((1 : ZMod 2), 0, -(2 : ℤ_[2]) ^ (alpha - 1), 0, 0) from
        mPhiHom_A (mStageOneLe ha) 0]
      refine Multiplicative.toAdd.injective
        (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl))))
      · show (1 : ZMod 2) = 1 + mParityZ 0 * p.tau + mParityZ 0 * mParityZ p.bc
        rw [mParityZ_zero]; ring
      · show -(2 : ℤ_[2]) ^ (alpha - 1) * (2 * p.c1) =
          0 * (p.beta : ℤ_[2]) + -(2 : ℤ_[2]) ^ (alpha - 1) * (2 * p.c1) + 0 * (2 * p.d1)
        ring
      · show -(2 : ℤ_[2]) ^ (alpha - 1) * (p.gamma : ℤ_[2]) =
          0 * p.bc + -(2 : ℤ_[2]) ^ (alpha - 1) * (p.gamma : ℤ_[2]) + 0 * p.e
        ring
    · rw [hrow 1 _ hp.1]
      show _ = mNielsenGenMap p (mCupFrameCanonicalMark ha 0 1)
      rw [show mCupFrameCanonicalMark ha 0 (1 : Fin (coreRank 0))
          = ofAdd ((0 : ZMod 2), 1, 0, 0, 0) from mPhiHom_B (mStageOneLe ha) 0]
      refine Multiplicative.toAdd.injective
        (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl))))
      · show p.tau = 0 + mParityZ 1 * p.tau + mParityZ 0 * mParityZ p.bc
        rw [mParityZ_zero, mParityZ_one]; ring
      · show ((p.beta : ℤ_[2])) = 1 * (p.beta : ℤ_[2]) + 0 * (2 * p.c1) + 0 * (2 * p.d1)
        ring
      · show p.bc = 1 * p.bc + 0 * (p.gamma : ℤ_[2]) + 0 * p.e
        ring
    · rw [hrow 2 _ hp.2.1]
      show _ = mNielsenGenMap p (mCupFrameCanonicalMark ha 0 2)
      rw [show mCupFrameCanonicalMark ha 0 (2 : Fin (coreRank 0))
          = ofAdd ((0 : ZMod 2), 0, 1, 0, 0) from mPhiHom_C (mStageOneLe ha) 0]
      refine Multiplicative.toAdd.injective
        (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl))))
      · show (0 : ZMod 2) = 0 + mParityZ 0 * p.tau + mParityZ 0 * mParityZ p.bc
        rw [mParityZ_zero]; ring
      · show 2 * p.c1 = 0 * (p.beta : ℤ_[2]) + 1 * (2 * p.c1) + 0 * (2 * p.d1)
        ring
      · show ((p.gamma : ℤ_[2])) = 0 * p.bc + 1 * (p.gamma : ℤ_[2]) + 0 * p.e
        ring
    · rw [hrow 3 _ hp.2.2]
      show _ = mNielsenGenMap p (mCupFrameCanonicalMark ha 0 3)
      rw [show mCupFrameCanonicalMark ha 0 (3 : Fin (coreRank 0))
          = ofAdd ((0 : ZMod 2), 0, 0, 1, 0) from mPhiHom_D (mStageOneLe ha) 0]
      refine Multiplicative.toAdd.injective
        (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl))))
      · show mParityZ p.bc = 0 + mParityZ 0 * p.tau + mParityZ 1 * mParityZ p.bc
        rw [mParityZ_zero, mParityZ_one]; ring
      · show 2 * p.d1 = 0 * (p.beta : ℤ_[2]) + 0 * (2 * p.c1) + 1 * (2 * p.d1)
        ring
      · show p.e = 0 * p.bc + 0 * (p.gamma : ℤ_[2]) + 1 * p.e
        ring
  have hall := mNielsenGen_frame_hom_ext ha 0 f (mNielsenGenHom p) hgen
  have hx : f (E x) = E (xi x) := congrArg (fun y => E (xi y)) (E.symm_apply_apply x)
  exact hx.symm.trans (hall (E x))

/-- **Every element of the Smith-Witt stabilizer of the rank-four M abelianization is induced
by an actual `chiM`-preserving continuous automorphism of `D_M`** (at the canonical frame, with
the orientation character `chi` pinned to its four generator values, the statement's own
hypotheses), through the seven Nielsen
generators: `mStabilizer_classification` gives the parameter, `mNielsen_factorization` splits
it into the seven families, each lifts by `mFullStabilizer_lift`, and the composite
of those lifts is the automorphism produced here.

The conclusion is the exact square `abMk (Psi x) = xi (abMk x)`, so `xi` really is the map
induced by `Psi` on the topological abelianization. -/
theorem mNielsenGen_stabilizer_induced {alpha : ℕ} (ha : 2 ≤ alpha)
    (chi : ContinuousMonoidHom (topAbelianization (DM alpha 0 : Type)) ℤ_[2]ˣ)
    (hchiA : chi (abMk (dmA alpha 0)) = 1) (hchiB : chi (abMk (dmB alpha 0)) = -1)
    (hchiC : chi (abMk (dmC alpha 0)) = 1) (hchiD : chi (abMk (dmD alpha 0)) = mUnit alpha)
    (xi : ContinuousMulEquiv (topAbelianization (DM alpha 0 : Type))
      (topAbelianization (DM alpha 0 : Type)))
    (hxi : IsMStabilizer (mNielsenGenFrame ha).toMDecomposition chi xi) :
    ∃ Psi : ContinuousMulEquiv (DM alpha 0 : Type) (DM alpha 0 : Type),
      (∀ x, chiM alpha 0 (Psi x) = chiM alpha 0 x) ∧
      (∀ x, abMk (Psi x) = xi (abMk x)) := by
  obtain ⟨p, hp, -⟩ := mStabilizer_classification ha (mNielsenGenFrame ha).toMDecomposition
    chi hchiA hchiB hchiC hchiD xi hxi
  obtain ⟨Psi, hchi, hsq⟩ := mNielsenGen_param_realized ha p
  refine ⟨Psi, hchi, fun x => ?_⟩
  refine (mFrameExists_phiEquiv (mStageOneLe ha) 0).injective ?_
  show mPhiHom (mStageOneLe ha) 0 (abMk (Psi x)) = mPhiHom (mStageOneLe ha) 0 (xi (abMk x))
  rw [hsq x, mNielsenGen_frameAction_of_realizes ha p xi hp (abMk x)]

#print axioms mNielsenGen_nRed_eq_parity
#print axioms mNielsenGen_cupFreeFrameProjection_eq
#print axioms mNielsenGen_coord
#print axioms mNielsenGen_coord_zero
#print axioms mNielsenGen_coord_one
#print axioms mNielsenGen_coord_two
#print axioms mNielsenGen_coord_three
#print axioms mNielsenGen_toAdd_zpowZtwo
#print axioms mNielsenGen_character_apply
#print axioms mNielsenGen_cancel_two
#print axioms mNielsenGen_parity_two
#print axioms mNielsenGenMap
#print axioms mNielsenGenMap_toAdd
#print axioms mNielsenGenMap_comp_of_act
#print axioms mNielsenGenMap_mul
#print axioms mNielsenGenMap_continuous
#print axioms mNielsenGenEquiv
#print axioms mNielsenGenEquiv_apply
#print axioms mNielsenGenMap_parity_B
#print axioms mNielsenGenMap_coord_D
#print axioms mNielsenGen_orientation
#print axioms mNielsenGen_sum_four
#print axioms mNielsenGen_evenCup_zero
#print axioms mNielsenGen_image_coord_zero
#print axioms mNielsenGen_image_coord_one
#print axioms mNielsenGen_image_coord_two
#print axioms mNielsenGen_image_coord_three
#print axioms mNielsenGen_char_image
#print axioms mNielsenGen_markCoord
#print axioms mNielsenGen_char_mark_zero
#print axioms mNielsenGen_char_mark_one
#print axioms mNielsenGen_char_mark_two
#print axioms mNielsenGen_char_mark_three
#print axioms mNielsenGen_cup_core
#print axioms mNielsenGen_cupIsometry
#print axioms mNielsenGen_M1_inv
#print axioms mNielsenGen_M2_inv
#print axioms mNielsenGen_M3_inv
#print axioms mNielsenGen_M4_inv
#print axioms mNielsenGen_M5_inv
#print axioms mNielsenGen_M6_inv
#print axioms mNielsenGen_M7_inv
#print axioms mNielsenGenM1
#print axioms mNielsenGenM2
#print axioms mNielsenGenM3
#print axioms mNielsenGenM4
#print axioms mNielsenGenM5
#print axioms mNielsenGenM6
#print axioms mNielsenGenM7
#print axioms mNielsenGenLift
#print axioms mNielsenGenMap_eq_lift
#print axioms mNielsenGenLift_comp
#print axioms MNielsenGenLifts
#print axioms mNielsenGenLifts_refl
#print axioms mNielsenGenLifts_trans
#print axioms mNielsenGenCompose
#print axioms mNielsenGenLifts_compose
#print axioms mNielsenGenLifts_of_param
#print axioms mNielsenGenList
#print axioms mNielsenGenList_length
#print axioms mNielsenGenCompose_list
#print axioms mNielsenGen_props_of_param
#print axioms mNielsenGenList_props
#print axioms mNielsenGen_finite_list
#print axioms mNielsenGen_param_realized
#print axioms mNielsenGenFrame
#print axioms mNielsenGenHom
#print axioms mNielsenGen_frame_hom_ext
#print axioms mNielsenGen_frameAction_of_realizes
#print axioms mNielsenGen_stabilizer_induced

end
end GQ2.Dyadic.MarkedCore
