/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.MNielsenGenerators

/-!
# The rank-four M Nielsen list carried to every handle count by the identity handle tail

Wave 366, lane W366-HANDLES.

**Scope, stated first.** This file is *optional* mathematics beyond the packet's rank-four
rows. The owner has accepted (Option A, 2026-09-18) the compactness proof method and the
families reading of the finite lists at rank four; nothing here is needed for that
acceptance and nothing here changes it.

**No handle-mixing classification is claimed, and none exists in the repo.** What is proved
here is exactly the weaker statement flagged at `docs/dyadic/w363-nielsen-note.md`
(lines 190-200): the seven core families, extended by the **identity on the `2h` handle
coordinates**, still preserve `mFrameOrientation` and `MCupFrameCupIsometry` at every `h`,
hence still lift by `mFullStabilizer_lift`. The stabilizer elements covered are exactly
those that are a rank-four `MStabParam` action on the core block and the identity on the
handle block; a full-frame automorphism that moves the handle block is **not** covered.
`alpha >= 2` throughout.

`MNielsenHandles.mNielsenHdlStabilizerShape` (below) states, as an unproved named `Prop`,
what a full handle-mixing classification would have to say.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 GQ2.SectionThree Multiplicative
open GQ2.Dyadic.EvenModel
open scoped GQ2.SectionThree.TopAbInstances

/-! ## Index arithmetic on `Fin (coreRank h)` -/

/-- Every full-frame index is one of the four core indices or a handle index. -/
theorem mNielsenHdl_index_cases {h : ℕ} (j : Fin (coreRank h)) :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ ∃ k : Fin (2 * h), j = mHandleIdx k := by
  have h0 := coreVal_zero h
  have h1 := coreVal_one h
  have h2 := coreVal_two h
  have h3 := coreVal_three h
  have hlt : (j : ℕ) < 4 + 2 * h := by have := j.isLt; simpa only [coreRank] using this
  rcases Nat.lt_or_ge (j : ℕ) 4 with hj | hj
  · have hcase : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ (j : ℕ) = 3 := by omega
    rcases hcase with hv | hv | hv | hv
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (Or.inl (Fin.ext (by omega)))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by omega)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨(j : ℕ) - 4, by omega⟩, Fin.ext ?_⟩)))
    rw [mHandleIdx_val]
    show (j : ℕ) = 4 + ((j : ℕ) - 4)
    omega

/-- The four core indices are not handle indices. -/
theorem mNielsenHdl_core_ne_handle {h : ℕ} (k : Fin (2 * h)) :
    (0 : Fin (coreRank h)) ≠ mHandleIdx k ∧ (1 : Fin (coreRank h)) ≠ mHandleIdx k ∧
      (2 : Fin (coreRank h)) ≠ mHandleIdx k ∧ (3 : Fin (coreRank h)) ≠ mHandleIdx k := by
  have h0 := coreVal_zero h
  have h1 := coreVal_one h
  have h2 := coreVal_two h
  have h3 := coreVal_three h
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_, fun hc => ?_⟩ <;>
    · have := congrArg (fun i : Fin (coreRank h) => (i : ℕ)) hc
      rw [mHandleIdx_val] at this
      omega

/-- **The head-plus-handles splitting of a full-frame sum.** -/
theorem mNielsenHdl_sum_split {h : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin (coreRank h) → M) :
    ∑ j, f j = f 0 + f 1 + f 2 + f 3 + ∑ k : Fin (2 * h), f (mHandleIdx k) := by
  have hsplit : ∑ j : Fin (4 + 2 * h), f j
      = (∑ i : Fin 4, f (Fin.castAdd (2 * h) i)) + ∑ k : Fin (2 * h), f (Fin.natAdd 4 k) :=
    Fin.sum_univ_add f
  have hnat : ∀ k : Fin (2 * h), (Fin.natAdd 4 k : Fin (coreRank h)) = mHandleIdx k :=
    fun _ => rfl
  have e0 : (0 : Fin (coreRank h)) = Fin.castAdd (2 * h) (0 : Fin 4) :=
    Fin.ext (by rw [coreVal_zero]; rfl)
  have e1 : (1 : Fin (coreRank h)) = Fin.castAdd (2 * h) (1 : Fin 4) :=
    Fin.ext (by rw [coreVal_one]; rfl)
  have e2 : (2 : Fin (coreRank h)) = Fin.castAdd (2 * h) (2 : Fin 4) :=
    Fin.ext (by rw [coreVal_two]; rfl)
  have e3 : (3 : Fin (coreRank h)) = Fin.castAdd (2 * h) (3 : Fin 4) :=
    Fin.ext (by rw [coreVal_three]; rfl)
  calc ∑ j, f j = ∑ j : Fin (4 + 2 * h), f j := rfl
    _ = (∑ i : Fin 4, f (Fin.castAdd (2 * h) i)) + ∑ k : Fin (2 * h), f (Fin.natAdd 4 k) :=
        hsplit
    _ = f 0 + f 1 + f 2 + f 3 + ∑ k : Fin (2 * h), f (mHandleIdx k) := by
        rw [Fin.sum_univ_four, e0, e1, e2, e3]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => congrArg f (hnat k))

/-! ## The identity handle tail

`mNielsenHdlMap p` is `MStabParam.act` on the four core coordinates of `MFrameModel h`, with
the `2h` handle coordinates carried by the identity. `mNielsenHdlMap_core` and
`mNielsenHdlMap_handle` are the two halves of the claim that this really is the
identity-handle-tail extension of the rank-four `mNielsenGenMap`, and nothing more. -/

/-- The rank-four core of a full-frame element: the four core coordinates, handle tail
discarded. -/
def mNielsenHdlCore {h : ℕ} (z : MFrameModel h) : MFrameModel 0 :=
  ofAdd (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1, 0)

/-- **The identity-handle-tail extension of a rank-four stabilizer parameter's frame action.**
The four core slots are `MStabParam.act`, exactly as in `mNielsenGenMap`; the `2h` handle
slots are copied. -/
noncomputable def mNielsenHdlMap (p : MStabParam) {h : ℕ} (z : MFrameModel h) : MFrameModel h :=
  ofAdd (z.toAdd.1 + mParityZ z.toAdd.2.1 * p.tau + mParityZ z.toAdd.2.2.2.1 * mParityZ p.bc,
    z.toAdd.2.1 * (p.beta : ℤ_[2]) + z.toAdd.2.2.1 * (2 * p.c1) + z.toAdd.2.2.2.1 * (2 * p.d1),
    z.toAdd.2.1 * p.bc + z.toAdd.2.2.1 * (p.gamma : ℤ_[2]) + z.toAdd.2.2.2.1 * p.e,
    z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)

/-- At handle rank zero this is literally `mNielsenGenerators`' map. -/
theorem mNielsenHdlMap_zero (p : MStabParam) (z : MFrameModel 0) :
    mNielsenHdlMap p z = mNielsenGenMap p z := rfl

/-- **The core half of the extension claim**: on the rank-four core the extension is the
rank-four map. -/
theorem mNielsenHdlMap_core (p : MStabParam) {h : ℕ} (z : MFrameModel h) :
    mNielsenHdlCore (mNielsenHdlMap p z) = mNielsenGenMap p (mNielsenHdlCore z) := rfl

/-- **The handle half of the extension claim**: on the `2h` handle coordinates the extension
is the identity. This is the precise sense in which the handle block is *not* moved. -/
theorem mNielsenHdlMap_handle (p : MStabParam) {h : ℕ} (z : MFrameModel h) :
    (mNielsenHdlMap p z).toAdd.2.2.2.2 = z.toAdd.2.2.2.2 := rfl

theorem mNielsenHdlMap_comp_of_act (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) {h : ℕ} (z : MFrameModel h) :
    mNielsenHdlMap p (mNielsenHdlMap q z) = z := by
  have hl : mNielsenHdlMap p (mNielsenHdlMap q z) =
      ofAdd ((p.act (q.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1))).1,
        (p.act (q.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1))).2.1,
        (p.act (q.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1))).2.2.1,
        (p.act (q.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1))).2.2.2,
        z.toAdd.2.2.2.2) := rfl
  rw [hl, hpq (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)]
  rfl

theorem mNielsenHdlMap_mul (p : MStabParam) {h : ℕ} (z w : MFrameModel h) :
    mNielsenHdlMap p (z * w) = mNielsenHdlMap p z * mNielsenHdlMap p w := by
  have hl : mNielsenHdlMap p (z * w) = ofAdd
      (z.toAdd.1 + w.toAdd.1 + mParityZ (z.toAdd.2.1 + w.toAdd.2.1) * p.tau
         + mParityZ (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * mParityZ p.bc,
       (z.toAdd.2.1 + w.toAdd.2.1) * (p.beta : ℤ_[2])
         + (z.toAdd.2.2.1 + w.toAdd.2.2.1) * (2 * p.c1)
         + (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * (2 * p.d1),
       (z.toAdd.2.1 + w.toAdd.2.1) * p.bc
         + (z.toAdd.2.2.1 + w.toAdd.2.2.1) * (p.gamma : ℤ_[2])
         + (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * p.e,
       z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1, z.toAdd.2.2.2.2 + w.toAdd.2.2.2.2) := rfl
  have hr : mNielsenHdlMap p z * mNielsenHdlMap p w = ofAdd
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

theorem mNielsenHdlMap_continuous (p : MStabParam) (h : ℕ) :
    Continuous (mNielsenHdlMap p (h := h)) := by
  have hpar : Continuous mParityZ := mFrameParity_continuous
  have hA : Continuous fun z : MFrameModel h => z.toAdd.1 :=
    continuous_fst.comp continuous_toAdd
  have hB : Continuous fun z : MFrameModel h => z.toAdd.2.1 :=
    (continuous_fst.comp continuous_snd).comp continuous_toAdd
  have hC : Continuous fun z : MFrameModel h => z.toAdd.2.2.1 :=
    ((continuous_fst.comp continuous_snd).comp continuous_snd).comp continuous_toAdd
  have hD : Continuous fun z : MFrameModel h => z.toAdd.2.2.2.1 :=
    ((continuous_fst.comp continuous_snd).comp (continuous_snd.comp continuous_snd)).comp
      continuous_toAdd
  have hE : Continuous fun z : MFrameModel h => z.toAdd.2.2.2.2 :=
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

/-- **The extension as a continuous frame automorphism at every handle count.** As at rank
four, a mutually inverse pair of stabilizer parameters is supplied; no group structure on
`MStabParam` exists in the tree, and each of the seven families supplies its own inverse. -/
noncomputable def mNielsenHdlEquiv (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) (h : ℕ) :
    ContinuousMulEquiv (MFrameModel h) (MFrameModel h) where
  toFun := mNielsenHdlMap p
  invFun := mNielsenHdlMap q
  left_inv := mNielsenHdlMap_comp_of_act q p hqp
  right_inv := mNielsenHdlMap_comp_of_act p q hpq
  map_mul' := mNielsenHdlMap_mul p
  continuous_toFun := mNielsenHdlMap_continuous p h
  continuous_invFun := mNielsenHdlMap_continuous q h

@[simp] theorem mNielsenHdlEquiv_apply (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) (h : ℕ)
    (z : MFrameModel h) : mNielsenHdlEquiv p q hpq hqp h z = mNielsenHdlMap p z := rfl

/-! ## Orientation at every handle count

`mFrameOrientation` never reads the handle slots (`mFrameOrientation_apply`), so the identity
tail is invisible to it and the rank-four argument applies verbatim. -/

theorem mNielsenHdlMap_parity_B (p : MStabParam) {h : ℕ} (z : MFrameModel h) :
    mParityZ (mNielsenHdlMap p z).toAdd.2.1 = mParityZ z.toAdd.2.1 := by
  have hz : (mNielsenHdlMap p z).toAdd.2.1
      = z.toAdd.2.1 * (p.beta : ℤ_[2]) + z.toAdd.2.2.1 * (2 * p.c1)
        + z.toAdd.2.2.2.1 * (2 * p.d1) := rfl
  have h2 : mParityZ (2 : ℤ_[2]) = 0 := by
    have hh := mParityZ_two_mul 1
    rwa [mul_one] at hh
  rw [hz]
  simp only [mParityZ_add, mParityZ_mul, h2, mParityZ_of_isUnit p.beta.isUnit]
  ring

theorem mNielsenHdlMap_coord_D (p : MStabParam) {h : ℕ} (z : MFrameModel h) :
    (mNielsenHdlMap p z).toAdd.2.2.2.1 = z.toAdd.2.2.2.1 := rfl

/-- **T1, orientation half, at every handle count.** -/
theorem mNielsenHdl_orientation {alpha : ℕ} (ha : 2 ≤ alpha) (p q : MStabParam)
    (hpq : ∀ v, p.act (q.act v) = v) (hqp : ∀ v, q.act (p.act v) = v) (h : ℕ)
    (z : MFrameModel h) :
    mFrameOrientation ha h (mNielsenHdlEquiv p q hpq hqp h z) = mFrameOrientation ha h z :=
  (mFrameOrientation_preserved_iff ha h (mNielsenHdlEquiv p q hpq hqp h)).mpr
    (fun w => ⟨mNielsenHdlMap_parity_B p w, mNielsenHdlMap_coord_D p w⟩) z

/-! ## Cup at every handle count

`MCupFrameCupIsometry` quantifies over *pairs of continuous mod-two frame characters*, not
over pairs of mod-two vectors, so the rank-four statement cannot simply be transported: the
predicate at handle count `h` sees `4 + 2h` coordinates of every character. The route taken
here is the rank-four one of `MNielsenGenerators` run at general `h`. The character expansion
`mNielsenGen_character_apply` and the coordinate readings `mNielsenGen_coord_*` are already
stated at general `h`; what is new is the handle coordinate reading, the head-plus-handles
split of the expansion sum, and the observation that the handle marks are fixed **on the
nose** by the extension, so the handle block of `evenCupForm` is literally the same term on
both sides of the isometry equation. Only the head block then has to be checked, and that
check is the rank-four one. -/

/-- The mod-two reading of a handle coordinate of an arbitrary frame element. -/
theorem mNielsenHdl_coord_handle {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (k : Fin (2 * h))
    (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) z) = mParityZ (z.toAdd.2.2.2.2 k) := by
  rw [mNielsenGen_coord ha h (mHandleIdx k) z]
  show nRed (mSurjVec alpha _ _ _ _ _ (mHandleIdx k)) = _
  rw [mSurjVec_handle, mNielsenGen_nRed_eq_parity]

theorem mNielsenHdl_image_coord_zero {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h 0 (mNielsenHdlMap p z))
      = toAdd (mCupFrameModTwoCoordinate ha h 0 z)
        + toAdd (mCupFrameModTwoCoordinate ha h 1 z) * p.tau
        + toAdd (mCupFrameModTwoCoordinate ha h 3 z) * mParityZ p.bc := by
  rw [mNielsenGen_coord_zero ha h (mNielsenHdlMap p z), mNielsenGen_coord_zero ha h z,
    mNielsenGen_coord_one ha h z, mNielsenGen_coord_three ha h z]
  rfl

theorem mNielsenHdl_image_coord_one {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h 1 (mNielsenHdlMap p z))
      = toAdd (mCupFrameModTwoCoordinate ha h 1 z) := by
  rw [mNielsenGen_coord_one ha h (mNielsenHdlMap p z), mNielsenGen_coord_one ha h z]
  exact mNielsenHdlMap_parity_B p z

theorem mNielsenHdl_image_coord_two {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h 2 (mNielsenHdlMap p z))
      = toAdd (mCupFrameModTwoCoordinate ha h 1 z) * mParityZ p.bc
        + toAdd (mCupFrameModTwoCoordinate ha h 2 z)
        + toAdd (mCupFrameModTwoCoordinate ha h 3 z) * mParityZ p.e := by
  have hz : (mNielsenHdlMap p z).toAdd.2.2.1
      = z.toAdd.2.1 * p.bc + z.toAdd.2.2.1 * (p.gamma : ℤ_[2])
        + z.toAdd.2.2.2.1 * p.e := rfl
  rw [mNielsenGen_coord_two ha h (mNielsenHdlMap p z), mNielsenGen_coord_one ha h z,
    mNielsenGen_coord_two ha h z, mNielsenGen_coord_three ha h z, hz,
    mParityZ_add, mParityZ_add, mParityZ_mul, mParityZ_mul, mParityZ_mul,
    mParityZ_of_isUnit p.gamma.isUnit]
  ring

theorem mNielsenHdl_image_coord_three {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h 3 (mNielsenHdlMap p z))
      = toAdd (mCupFrameModTwoCoordinate ha h 3 z) := by
  rw [mNielsenGen_coord_three ha h (mNielsenHdlMap p z), mNielsenGen_coord_three ha h z]
  rfl

/-- **The handle coordinates of the image are the handle coordinates of the source.** -/
theorem mNielsenHdl_image_coord_handle {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (k : Fin (2 * h)) (z : MFrameModel h) :
    toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) (mNielsenHdlMap p z))
      = toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) z) := by
  rw [mNielsenHdl_coord_handle ha k (mNielsenHdlMap p z), mNielsenHdl_coord_handle ha k z,
    mNielsenHdlMap_handle p z]

/-- The value of a mod-two character on the image of a frame element, head block expanded
and handle block left as a sum. -/
theorem mNielsenHdl_char_image {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2))) (z : MFrameModel h) :
    toAdd (c (mNielsenHdlMap p z))
      = (toAdd (mCupFrameModTwoCoordinate ha h 0 z)
            + toAdd (mCupFrameModTwoCoordinate ha h 1 z) * p.tau
            + toAdd (mCupFrameModTwoCoordinate ha h 3 z) * mParityZ p.bc)
          * toAdd (c (mCupFrameCanonicalMark ha h 0))
        + toAdd (mCupFrameModTwoCoordinate ha h 1 z)
          * toAdd (c (mCupFrameCanonicalMark ha h 1))
        + (toAdd (mCupFrameModTwoCoordinate ha h 1 z) * mParityZ p.bc
            + toAdd (mCupFrameModTwoCoordinate ha h 2 z)
            + toAdd (mCupFrameModTwoCoordinate ha h 3 z) * mParityZ p.e)
          * toAdd (c (mCupFrameCanonicalMark ha h 2))
        + toAdd (mCupFrameModTwoCoordinate ha h 3 z)
          * toAdd (c (mCupFrameCanonicalMark ha h 3))
        + ∑ k : Fin (2 * h), toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) z)
            * toAdd (c (mCupFrameCanonicalMark ha h (mHandleIdx k))) := by
  have hsum : (∑ k : Fin (2 * h), toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k)
        (mNielsenHdlMap p z)) * toAdd (c (mCupFrameCanonicalMark ha h (mHandleIdx k))))
      = ∑ k : Fin (2 * h), toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) z)
          * toAdd (c (mCupFrameCanonicalMark ha h (mHandleIdx k))) :=
    Finset.sum_congr rfl fun k _ => by rw [mNielsenHdl_image_coord_handle ha p k z]
  rw [mNielsenGen_character_apply ha h c (mNielsenHdlMap p z), mNielsenHdl_sum_split, hsum,
    mNielsenHdl_image_coord_zero ha p z, mNielsenHdl_image_coord_one ha p z,
    mNielsenHdl_image_coord_two ha p z, mNielsenHdl_image_coord_three ha p z]

theorem mNielsenHdl_markCoord {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (i j : Fin (coreRank h)) :
    toAdd (mCupFrameModTwoCoordinate ha h j (mCupFrameCanonicalMark ha h i))
      = if i = j then 1 else 0 :=
  mCupFrameModTwoCoordinate_canonicalMark ha h j i

/-- A core mark has no handle coordinate. -/
theorem mNielsenHdl_markCoord_core_handle {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ}
    (i : Fin (coreRank h)) (hi : (i : ℕ) < 4) (k : Fin (2 * h)) :
    toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) (mCupFrameCanonicalMark ha h i))
      = 0 := by
  rw [mNielsenHdl_markCoord ha i (mHandleIdx k), if_neg]
  intro hc
  have hv := congrArg (fun t : Fin (coreRank h) => (t : ℕ)) hc
  rw [mHandleIdx_val] at hv
  omega

theorem mNielsenHdl_char_mark_zero {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2))) :
    toAdd (c (mNielsenHdlMap p (mCupFrameCanonicalMark ha h 0)))
      = toAdd (c (mCupFrameCanonicalMark ha h 0)) := by
  have htail : (∑ k : Fin (2 * h),
      toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) (mCupFrameCanonicalMark ha h 0))
        * toAdd (c (mCupFrameCanonicalMark ha h (mHandleIdx k)))) = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [mNielsenHdl_markCoord_core_handle ha 0 (by rw [coreVal_zero]; omega) k, zero_mul]
  rw [mNielsenHdl_char_image ha p c (mCupFrameCanonicalMark ha h 0), htail, add_zero]
  simp only [mNielsenHdl_markCoord ha, Fin.ext_iff, coreVal_zero, coreVal_one, coreVal_two,
    coreVal_three]
  norm_num

theorem mNielsenHdl_char_mark_one {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2))) :
    toAdd (c (mNielsenHdlMap p (mCupFrameCanonicalMark ha h 1)))
      = p.tau * toAdd (c (mCupFrameCanonicalMark ha h 0))
        + toAdd (c (mCupFrameCanonicalMark ha h 1))
        + mParityZ p.bc * toAdd (c (mCupFrameCanonicalMark ha h 2)) := by
  have htail : (∑ k : Fin (2 * h),
      toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) (mCupFrameCanonicalMark ha h 1))
        * toAdd (c (mCupFrameCanonicalMark ha h (mHandleIdx k)))) = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [mNielsenHdl_markCoord_core_handle ha 1 (by rw [coreVal_one]; omega) k, zero_mul]
  rw [mNielsenHdl_char_image ha p c (mCupFrameCanonicalMark ha h 1), htail, add_zero]
  simp only [mNielsenHdl_markCoord ha, Fin.ext_iff, coreVal_zero, coreVal_one, coreVal_two,
    coreVal_three]
  norm_num

theorem mNielsenHdl_char_mark_two {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2))) :
    toAdd (c (mNielsenHdlMap p (mCupFrameCanonicalMark ha h 2)))
      = toAdd (c (mCupFrameCanonicalMark ha h 2)) := by
  have htail : (∑ k : Fin (2 * h),
      toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) (mCupFrameCanonicalMark ha h 2))
        * toAdd (c (mCupFrameCanonicalMark ha h (mHandleIdx k)))) = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [mNielsenHdl_markCoord_core_handle ha 2 (by rw [coreVal_two]; omega) k, zero_mul]
  rw [mNielsenHdl_char_image ha p c (mCupFrameCanonicalMark ha h 2), htail, add_zero]
  simp only [mNielsenHdl_markCoord ha, Fin.ext_iff, coreVal_zero, coreVal_one, coreVal_two,
    coreVal_three]
  norm_num

theorem mNielsenHdl_char_mark_three {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (p : MStabParam)
    (c : ContinuousMonoidHom (MFrameModel h) (Multiplicative (ZMod 2))) :
    toAdd (c (mNielsenHdlMap p (mCupFrameCanonicalMark ha h 3)))
      = mParityZ p.bc * toAdd (c (mCupFrameCanonicalMark ha h 0))
        + mParityZ p.e * toAdd (c (mCupFrameCanonicalMark ha h 2))
        + toAdd (c (mCupFrameCanonicalMark ha h 3)) := by
  have htail : (∑ k : Fin (2 * h),
      toAdd (mCupFrameModTwoCoordinate ha h (mHandleIdx k) (mCupFrameCanonicalMark ha h 3))
        * toAdd (c (mCupFrameCanonicalMark ha h (mHandleIdx k)))) = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [mNielsenHdl_markCoord_core_handle ha 3 (by rw [coreVal_three]; omega) k, zero_mul]
  rw [mNielsenHdl_char_image ha p c (mCupFrameCanonicalMark ha h 3), htail, add_zero]
  simp only [mNielsenHdl_markCoord ha, Fin.ext_iff, coreVal_zero, coreVal_one, coreVal_two,
    coreVal_three]
  norm_num

#print axioms mNielsenHdl_coord_handle
#print axioms mNielsenHdl_image_coord_zero
#print axioms mNielsenHdl_image_coord_one
#print axioms mNielsenHdl_image_coord_two
#print axioms mNielsenHdl_image_coord_three
#print axioms mNielsenHdl_image_coord_handle
#print axioms mNielsenHdl_char_image
#print axioms mNielsenHdl_markCoord
#print axioms mNielsenHdl_markCoord_core_handle
#print axioms mNielsenHdl_char_mark_zero
#print axioms mNielsenHdl_char_mark_one
#print axioms mNielsenHdl_char_mark_two
#print axioms mNielsenHdl_char_mark_three

#print axioms mNielsenHdlCore
#print axioms mNielsenHdlMap
#print axioms mNielsenHdlMap_zero
#print axioms mNielsenHdlMap_core
#print axioms mNielsenHdlMap_handle
#print axioms mNielsenHdlMap_comp_of_act
#print axioms mNielsenHdlMap_mul
#print axioms mNielsenHdlMap_continuous
#print axioms mNielsenHdlEquiv
#print axioms mNielsenHdlEquiv_apply
#print axioms mNielsenHdlMap_parity_B
#print axioms mNielsenHdlMap_coord_D
#print axioms mNielsenHdl_orientation

#print axioms mNielsenHdl_index_cases
#print axioms mNielsenHdl_core_ne_handle
#print axioms mNielsenHdl_sum_split
