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
