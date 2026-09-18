/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.NNielsenFactorization

/-!
# The rank-four N Nielsen list carried to every handle count by the identity handle tail

Wave 366, lane W366-HANDLES, T2: the `N` twin of `MarkedCore/MNielsenHandles.lean`.

**Scope, stated first.** This file is *optional* mathematics beyond the packet's rank-four
rows. The owner has accepted (Option A, 2026-09-18) the compactness proof method and the
families reading of the finite lists at rank four; nothing here is needed for that
acceptance and nothing here changes it.

**No handle-mixing classification is claimed, and none exists in the repo.** The maps built
here are the identity on the `2h` handle coordinates, on the nose, and their core parameter
is a *rank-four* `NStabParam`. `nNielsenHdlMap_core` and `nNielsenHdlMap_handle` are the two
halves of that claim; a full-frame automorphism that moves the handle block satisfies
neither and is outside every theorem here. `alpha >= 2` throughout.

The N route to the cup condition is not the M route. `MNielsenHandles` could close its head
block with a `decide`, because `MStabParam.act` carries no relation between its entries. The
N head block does carry one: the `(sigma, x2)` block is a genuine `GL_2(Z_2)` and the check
needs `NStabParam.Admissible` through `N.lean`'s `NStabParam.rows_isCupIsometry`. So the
matrix criterion of `NNielsenGenerators.nNielsenGen_cup_of_mat`, which is stated at rank
four, is restated here at general `h` for the identity-tail maps. The index arithmetic
(`nNielsenHdl_sum_split`) is a copy of `MNielsenHandles`' for the `N` file's import closure,
which does not see that module.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 GQ2.SectionThree Multiplicative
open GQ2.Dyadic.EvenModel
open scoped GQ2.SectionThree.TopAbInstances

/-! ## Index arithmetic on `Fin (coreRank h)` -/

/-- **The head-plus-handles splitting of a full-frame sum.** A copy of
`MNielsenHandles.mNielsenHdl_sum_split`, which this file's import closure does not see. -/
theorem nNielsenHdl_sum_split {h : ℕ} {M : Type*} [AddCommMonoid M]
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

/-! ## The identity handle tail at N -/

/-- The rank-four core of a full `N`-frame element. -/
def nNielsenHdlCore {h : ℕ} (z : NFrameModel h) : NFrameModel 0 :=
  ofAdd (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1, 0)

/-- An arbitrary rank-four coordinate map transported to `NFrameModel h` by the identity
handle tail. -/
def nNielsenHdlLift {h : ℕ} (F : NVec → NVec) (z : NFrameModel h) : NFrameModel h :=
  ofAdd ((F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).1,
    (F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.1,
    (F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.1,
    (F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.2,
    z.toAdd.2.2.2.2)

theorem nNielsenHdlLift_comp {h : ℕ} (F G : NVec → NVec) (z : NFrameModel h) :
    nNielsenHdlLift F (nNielsenHdlLift G z) = nNielsenHdlLift (F ∘ G) z := rfl

/-- **The identity-handle-tail extension of a rank-four stabilizer parameter's frame
action.** -/
def nNielsenHdlMap (P : NStabParam) {h : ℕ} : NFrameModel h → NFrameModel h :=
  nNielsenHdlLift P.act

theorem nNielsenHdlMap_eq_lift (P : NStabParam) (h : ℕ) :
    nNielsenHdlMap P (h := h) = nNielsenHdlLift P.act := rfl

/-- At handle rank zero this is literally `NNielsenFactorization`'s map. -/
theorem nNielsenHdlMap_zero (P : NStabParam) (z : NFrameModel 0) :
    nNielsenHdlMap P z = nNielsenFacMap P z := rfl

/-- **The core half of the extension claim.** -/
theorem nNielsenHdlMap_core (P : NStabParam) {h : ℕ} (z : NFrameModel h) :
    nNielsenHdlCore (nNielsenHdlMap P z) = nNielsenFacMap P (nNielsenHdlCore z) := rfl

/-- **The handle half of the extension claim**: the `2h` handle coordinates are copied. -/
theorem nNielsenHdlMap_handle (P : NStabParam) {h : ℕ} (z : NFrameModel h) :
    (nNielsenHdlMap P z).toAdd.2.2.2.2 = z.toAdd.2.2.2.2 := rfl

theorem nNielsenHdlMap_comp_of_act (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) {h : ℕ} (z : NFrameModel h) :
    nNielsenHdlMap P (nNielsenHdlMap Q z) = z := by
  rw [nNielsenHdlMap_eq_lift, nNielsenHdlMap_eq_lift, nNielsenHdlLift_comp]
  have hid : P.act ∘ Q.act = id := funext hPQ
  rw [hid]
  rfl

theorem nNielsenHdlMap_mul (P : NStabParam) {h : ℕ} (z w : NFrameModel h) :
    nNielsenHdlMap P (z * w) = nNielsenHdlMap P z * nNielsenHdlMap P w := by
  have hl : nNielsenHdlMap P (z * w) = ofAdd
      (z.toAdd.1 + w.toAdd.1 + nRed (z.toAdd.2.1 + w.toAdd.2.1) * P.tau
          + nRed (z.toAdd.2.2.1 + w.toAdd.2.2.1) * P.tauSigma
          + nRed (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * P.tauX2,
       z.toAdd.2.1 + w.toAdd.2.1,
       (z.toAdd.2.1 + w.toAdd.2.1) * P.p + (z.toAdd.2.2.1 + w.toAdd.2.2.1) * P.g 0 0
         + (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * P.g 0 1,
       (z.toAdd.2.1 + w.toAdd.2.1) * P.q + (z.toAdd.2.2.1 + w.toAdd.2.2.1) * P.g 1 0
         + (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * P.g 1 1,
       z.toAdd.2.2.2.2 + w.toAdd.2.2.2.2) := rfl
  have hr : nNielsenHdlMap P z * nNielsenHdlMap P w = ofAdd
      ((z.toAdd.1 + nRed z.toAdd.2.1 * P.tau + nRed z.toAdd.2.2.1 * P.tauSigma
          + nRed z.toAdd.2.2.2.1 * P.tauX2)
        + (w.toAdd.1 + nRed w.toAdd.2.1 * P.tau + nRed w.toAdd.2.2.1 * P.tauSigma
          + nRed w.toAdd.2.2.2.1 * P.tauX2),
       z.toAdd.2.1 + w.toAdd.2.1,
       (z.toAdd.2.1 * P.p + z.toAdd.2.2.1 * P.g 0 0 + z.toAdd.2.2.2.1 * P.g 0 1)
         + (w.toAdd.2.1 * P.p + w.toAdd.2.2.1 * P.g 0 0 + w.toAdd.2.2.2.1 * P.g 0 1),
       (z.toAdd.2.1 * P.q + z.toAdd.2.2.1 * P.g 1 0 + z.toAdd.2.2.2.1 * P.g 1 1)
         + (w.toAdd.2.1 * P.q + w.toAdd.2.2.1 * P.g 1 0 + w.toAdd.2.2.2.1 * P.g 1 1),
       z.toAdd.2.2.2.2 + w.toAdd.2.2.2.2) := rfl
  rw [hl, hr, map_add, map_add, map_add]
  exact congrArg ofAdd (Prod.ext (by ring) (Prod.ext rfl (Prod.ext (by ring) (Prod.ext (by ring)
    rfl))))

theorem nNielsenHdlMap_continuous (P : NStabParam) (h : ℕ) :
    Continuous (nNielsenHdlMap P (h := h)) := by
  have hred : Continuous nRed := GQ2.Dyadic.Instances.DNAutomorphismCup.continuous_nRed
  have hT : Continuous fun z : NFrameModel h => z.toAdd.1 :=
    continuous_fst.comp continuous_toAdd
  have hA : Continuous fun z : NFrameModel h => z.toAdd.2.1 :=
    (continuous_fst.comp continuous_snd).comp continuous_toAdd
  have hB : Continuous fun z : NFrameModel h => z.toAdd.2.2.1 :=
    ((continuous_fst.comp continuous_snd).comp continuous_snd).comp continuous_toAdd
  have hC : Continuous fun z : NFrameModel h => z.toAdd.2.2.2.1 :=
    ((continuous_fst.comp continuous_snd).comp (continuous_snd.comp continuous_snd)).comp
      continuous_toAdd
  have hE : Continuous fun z : NFrameModel h => z.toAdd.2.2.2.2 :=
    ((continuous_snd.comp continuous_snd).comp (continuous_snd.comp continuous_snd)).comp
      continuous_toAdd
  refine continuous_ofAdd.comp (Continuous.prodMk ?_ (Continuous.prodMk hA
    (Continuous.prodMk ?_ (Continuous.prodMk ?_ hE))))
  · exact ((hT.add ((hred.comp hA).mul continuous_const)).add
      ((hred.comp hB).mul continuous_const)).add ((hred.comp hC).mul continuous_const)
  · exact ((hA.mul continuous_const).add (hB.mul continuous_const)).add
      (hC.mul continuous_const)
  · exact ((hA.mul continuous_const).add (hB.mul continuous_const)).add
      (hC.mul continuous_const)

/-- **The extension as a continuous frame automorphism at every handle count.** -/
def nNielsenHdlEquiv (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) (h : ℕ) :
    ContinuousMulEquiv (NFrameModel h) (NFrameModel h) where
  toFun := nNielsenHdlMap P
  invFun := nNielsenHdlMap Q
  left_inv := nNielsenHdlMap_comp_of_act Q P hQP
  right_inv := nNielsenHdlMap_comp_of_act P Q hPQ
  map_mul' := nNielsenHdlMap_mul P
  continuous_toFun := nNielsenHdlMap_continuous P h
  continuous_invFun := nNielsenHdlMap_continuous Q h

@[simp] theorem nNielsenHdlEquiv_apply (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) (h : ℕ)
    (z : NFrameModel h) : nNielsenHdlEquiv P Q hPQ hQP h z = nNielsenHdlMap P z := rfl

/-! ## Orientation at every handle count -/

/-- The integral `x1` coordinate is fixed on the nose at every `h`. -/
theorem nNielsenHdlMap_coord_x1 (P : NStabParam) {h : ℕ} (z : NFrameModel h) :
    (nNielsenHdlMap P z).toAdd.2.1 = z.toAdd.2.1 := rfl

/-- **T2, orientation half, at every handle count.** -/
theorem nNielsenHdl_orientation {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) (h : ℕ)
    (z : NFrameModel h) :
    nFrameOrientation ha h (nNielsenHdlEquiv P Q hPQ hQP h z) = nFrameOrientation ha h z :=
  (nFrameOrientation_preserved_iff ha h (nNielsenHdlEquiv P Q hPQ hQP h)).mpr
    (fun w => nNielsenHdlMap_coord_x1 P w) z

#print axioms nNielsenHdl_sum_split
#print axioms nNielsenHdlCore
#print axioms nNielsenHdlLift
#print axioms nNielsenHdlLift_comp
#print axioms nNielsenHdlMap
#print axioms nNielsenHdlMap_eq_lift
#print axioms nNielsenHdlMap_zero
#print axioms nNielsenHdlMap_core
#print axioms nNielsenHdlMap_handle
#print axioms nNielsenHdlMap_comp_of_act
#print axioms nNielsenHdlMap_mul
#print axioms nNielsenHdlMap_continuous
#print axioms nNielsenHdlEquiv
#print axioms nNielsenHdlEquiv_apply
#print axioms nNielsenHdlMap_coord_x1
#print axioms nNielsenHdl_orientation
