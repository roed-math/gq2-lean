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


/-! ## Cup at every handle count

The head block needs `NStabParam.Admissible`, through `N.lean`'s
`NStabParam.rows_isCupIsometry`: unlike the `M` head block it is not a `decide`, because the
`(sigma, x2)` block of an `N` stabilizer parameter is a genuine `GL_2(Z_2)` and the cup
condition on it is a relation, not an identity. The handle block, on the other hand, behaves
exactly as at `M`: the handle marks are fixed on the nose, so its contribution to
`evenCupForm` is literally the same term on both sides. -/

/-- The mod-two reading of a handle coordinate of an arbitrary `N`-frame element. -/
theorem nNielsenHdl_coord_handle {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (k : Fin (2 * h))
    (z : NFrameModel h) :
    toAdd (nFrameModTwoCoordinate ha h (mHandleIdx k) z) = nRed (z.toAdd.2.2.2.2 k) := by
  rw [nNielsenGen_coord ha h (mHandleIdx k) z]
  show nRed (nSurjVec _ _ _ _ _ (mHandleIdx k)) = _
  rw [nSurjVec_handle]

/-- A mod-two character on a frame element with trivial handle tail is its rank-four
coordinate expansion: the handle part of the expansion sum vanishes. -/
theorem nNielsenHdl_char_of_core {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ}
    (c : ContinuousMonoidHom (NFrameModel h) (Multiplicative (ZMod 2))) (u : NVec) :
    toAdd (c (ofAdd (u.1, u.2.1, u.2.2.1, u.2.2.2, (0 : Fin (2 * h) → ℤ_[2]))))
      = u.1 * toAdd (c (nFrameCanonicalMark ha h 0))
        + nRed u.2.1 * toAdd (c (nFrameCanonicalMark ha h 1))
        + nRed u.2.2.1 * toAdd (c (nFrameCanonicalMark ha h 2))
        + nRed u.2.2.2 * toAdd (c (nFrameCanonicalMark ha h 3)) := by
  have htail : (∑ l : Fin (2 * h), toAdd (nFrameModTwoCoordinate ha h (mHandleIdx l)
        (ofAdd (u.1, u.2.1, u.2.2.1, u.2.2.2, (0 : Fin (2 * h) → ℤ_[2]))))
      * toAdd (c (nFrameCanonicalMark ha h (mHandleIdx l)))) = 0 :=
    Finset.sum_eq_zero fun l _ => by
      rw [nNielsenHdl_coord_handle ha l]
      show nRed (0 : ℤ_[2]) * _ = 0
      rw [map_zero, zero_mul]
  rw [nNielsenGen_character_apply ha h c _, nNielsenHdl_sum_split, htail, add_zero,
    nNielsenGen_coord_zero ha h _, nNielsenGen_coord_one ha h _, nNielsenGen_coord_two ha h _,
    nNielsenGen_coord_three ha h _]
  rfl

/-- The value of a character on the image of a core mark, in the parameter's own mod-two
matrix. The three inputs are the mark's coordinates, the parameter's column at that mark,
and nothing else. -/
theorem nNielsenHdl_char_coreMark {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (P : NStabParam)
    (c : ContinuousMonoidHom (NFrameModel h) (Multiplicative (ZMod 2)))
    (jj : Fin (coreRank h)) (j : Fin 4) (v : NVec)
    (hmark : nFrameCanonicalMark ha h jj
      = ofAdd (v.1, v.2.1, v.2.2.1, v.2.2.2, (0 : Fin (2 * h) → ℤ_[2])))
    (hcol : P.act v = P.rows.col j) :
    toAdd (c (nNielsenHdlMap P (nFrameCanonicalMark ha h jj)))
      = P.rows.mat 0 j * toAdd (c (nFrameCanonicalMark ha h 0))
        + P.rows.mat 1 j * toAdd (c (nFrameCanonicalMark ha h 1))
        + P.rows.mat 2 j * toAdd (c (nFrameCanonicalMark ha h 2))
        + P.rows.mat 3 j * toAdd (c (nFrameCanonicalMark ha h 3)) := by
  have him : nNielsenHdlMap P (nFrameCanonicalMark ha h jj)
      = ofAdd ((P.rows.col j).1, (P.rows.col j).2.1, (P.rows.col j).2.2.1,
          (P.rows.col j).2.2.2, (0 : Fin (2 * h) → ℤ_[2])) := by
    rw [hmark, ← hcol]
    rfl
  rw [him, nNielsenHdl_char_of_core ha c (P.rows.col j)]
  rfl

/-- The extension is the identity on any frame element with trivial core block. -/
theorem nNielsenHdlMap_of_core_trivial (P : NStabParam) {h : ℕ} (g : Fin (2 * h) → ℤ_[2]) :
    nNielsenHdlMap P (ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]), g))
      = ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]), g) := by
  refine congrArg ofAdd (Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))))
  · show (0 : ZMod 2) + nRed 0 * P.tau + nRed 0 * P.tauSigma + nRed 0 * P.tauX2 = 0
    rw [map_zero]; ring
  · show (0 : ℤ_[2]) * P.p + 0 * P.g 0 0 + 0 * P.g 0 1 = 0
    ring
  · show (0 : ℤ_[2]) * P.q + 0 * P.g 1 0 + 0 * P.g 1 1 = 0
    ring

/-- The `u`-mark of the `j`-th handle is fixed. -/
theorem nNielsenHdl_fix_markU {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (P : NStabParam)
    (j : Fin h) :
    nNielsenHdlMap P (nFrameCanonicalMark ha h (handleIdxU j))
      = nFrameCanonicalMark ha h (handleIdxU j) := by
  rw [show nFrameCanonicalMark ha h (handleIdxU j)
      = ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
          Pi.single (nHandleCoordU j) 1) from nPhiHom_U ha j]
  exact nNielsenHdlMap_of_core_trivial P _

/-- The `v`-mark of the `j`-th handle is fixed. -/
theorem nNielsenHdl_fix_markV {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (P : NStabParam)
    (j : Fin h) :
    nNielsenHdlMap P (nFrameCanonicalMark ha h (handleIdxV j))
      = nFrameCanonicalMark ha h (handleIdxV j) := by
  rw [show nFrameCanonicalMark ha h (handleIdxV j)
      = ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
          Pi.single (nHandleCoordV j) 1) from nPhiHom_V ha j]
  exact nNielsenHdlMap_of_core_trivial P _

/-- The head block of the even Gram is preserved by any mod-two matrix satisfying `N.lean`'s
own cup clause. This is `NNielsenGenerators`' `nNielsenGen_cup_core` in the explicit
eight-variable form that the general-`h` `evenCupForm` head presents; that copy is `private`,
so it is restated. -/
theorem nNielsenHdl_cup_head (A : Fin 4 → Fin 4 → ZMod 2)
    (hA : ∀ i j, nCupForm (A i) (A j) = nGram i j) (a0 a1 a2 a3 b0 b1 b2 b3 : ZMod 2) :
    (A 0 0 * a0 + A 1 0 * a1 + A 2 0 * a2 + A 3 0 * a3)
        * (A 0 0 * b0 + A 1 0 * b1 + A 2 0 * b2 + A 3 0 * b3)
      + ((A 0 0 * a0 + A 1 0 * a1 + A 2 0 * a2 + A 3 0 * a3)
          * (A 0 1 * b0 + A 1 1 * b1 + A 2 1 * b2 + A 3 1 * b3)
        + (A 0 1 * a0 + A 1 1 * a1 + A 2 1 * a2 + A 3 1 * a3)
          * (A 0 0 * b0 + A 1 0 * b1 + A 2 0 * b2 + A 3 0 * b3))
      + ((A 0 2 * a0 + A 1 2 * a1 + A 2 2 * a2 + A 3 2 * a3)
          * (A 0 3 * b0 + A 1 3 * b1 + A 2 3 * b2 + A 3 3 * b3)
        + (A 0 3 * a0 + A 1 3 * a1 + A 2 3 * a2 + A 3 3 * a3)
          * (A 0 2 * b0 + A 1 2 * b1 + A 2 2 * b2 + A 3 2 * b3))
      = a0 * b0 + (a0 * b1 + a1 * b0) + (a2 * b3 + a3 * b2) := by
  have h00 : nCupForm (A 0) (A 0) = 1 := hA 0 0
  have h01 : nCupForm (A 0) (A 1) = 1 := hA 0 1
  have h02 : nCupForm (A 0) (A 2) = 0 := hA 0 2
  have h03 : nCupForm (A 0) (A 3) = 0 := hA 0 3
  have h10 : nCupForm (A 1) (A 0) = 1 := hA 1 0
  have h11 : nCupForm (A 1) (A 1) = 0 := hA 1 1
  have h12 : nCupForm (A 1) (A 2) = 0 := hA 1 2
  have h13 : nCupForm (A 1) (A 3) = 0 := hA 1 3
  have h20 : nCupForm (A 2) (A 0) = 0 := hA 2 0
  have h21 : nCupForm (A 2) (A 1) = 0 := hA 2 1
  have h22 : nCupForm (A 2) (A 2) = 0 := hA 2 2
  have h23 : nCupForm (A 2) (A 3) = 1 := hA 2 3
  have h30 : nCupForm (A 3) (A 0) = 0 := hA 3 0
  have h31 : nCupForm (A 3) (A 1) = 0 := hA 3 1
  have h32 : nCupForm (A 3) (A 2) = 1 := hA 3 2
  have h33 : nCupForm (A 3) (A 3) = 0 := hA 3 3
  simp only [nCupForm] at h00 h01 h02 h03 h10 h11 h12 h13 h20 h21 h22 h23 h30 h31 h32 h33
  linear_combination (a0 * b0) * h00 + (a0 * b1) * h01 + (a0 * b2) * h02 +
    (a0 * b3) * h03 + (a1 * b0) * h10 + (a1 * b1) * h11 +
    (a1 * b2) * h12 + (a1 * b3) * h13 + (a2 * b0) * h20 +
    (a2 * b1) * h21 + (a2 * b2) * h22 + (a2 * b3) * h23 +
    (a3 * b0) * h30 + (a3 * b1) * h31 + (a3 * b2) * h32 +
    (a3 * b3) * h33

/-- **T2, cup half, at every handle count.** The identity-handle-tail extension of the frame
action of every *admissible* rank-four `N` stabilizer parameter is a full mod-two cup
isometry of the actual `N` frame at handle count `h`. -/
theorem nNielsenHdl_cupIsometry {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hP : P.Admissible) (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v)
    (h : ℕ) : NFrameCupIsometry ha (nNielsenHdlEquiv P Q hPQ hQP h) := by
  intro c d
  have hc0 := nNielsenHdl_char_coreMark ha P c 0 0 ((1 : ZMod 2), 0, 0, 0)
    (nPhiHom_X0 ha h) (NStabParam.act_t P)
  have hc1 := nNielsenHdl_char_coreMark ha P c 1 1 ((0 : ZMod 2), 1, 0, 0)
    (nPhiHom_X1 ha h) (NStabParam.act_x1 P)
  have hc2 := nNielsenHdl_char_coreMark ha P c 2 2 ((0 : ZMod 2), 0, 1, 0)
    (nPhiHom_Sigma ha h) (NStabParam.act_sigma P)
  have hc3 := nNielsenHdl_char_coreMark ha P c 3 3 ((0 : ZMod 2), 0, 0, 1)
    (nPhiHom_X2 ha h) (NStabParam.act_x2 P)
  have hd0 := nNielsenHdl_char_coreMark ha P d 0 0 ((1 : ZMod 2), 0, 0, 0)
    (nPhiHom_X0 ha h) (NStabParam.act_t P)
  have hd1 := nNielsenHdl_char_coreMark ha P d 1 1 ((0 : ZMod 2), 1, 0, 0)
    (nPhiHom_X1 ha h) (NStabParam.act_x1 P)
  have hd2 := nNielsenHdl_char_coreMark ha P d 2 2 ((0 : ZMod 2), 0, 1, 0)
    (nPhiHom_Sigma ha h) (NStabParam.act_sigma P)
  have hd3 := nNielsenHdl_char_coreMark ha P d 3 3 ((0 : ZMod 2), 0, 0, 1)
    (nPhiHom_X2 ha h) (NStabParam.act_x2 P)
  simp only [nNielsenHdlEquiv_apply, evenCupForm, nNielsenHdl_fix_markU ha P,
    nNielsenHdl_fix_markV ha P, hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3]
  congr 1
  exact nNielsenHdl_cup_head P.rows.mat (fun i j => NStabParam.rows_isCupIsometry hP i j)
    _ _ _ _ _ _ _ _


/-! ## The six families, carried to every handle count -/

/-- Family **N1**, with the identity handle tail. -/
def nNielsenHdlN1 (k : ℤ_[2]) (h : ℕ) : ContinuousMulEquiv (NFrameModel h) (NFrameModel h) :=
  nNielsenHdlEquiv (nFamN1 k) (nFamN1 (-k)) (nNielsenFac_N1_inv k)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N1_inv (-k) v) h

/-- Family **N2**, with the identity handle tail. -/
def nNielsenHdlN2 (k : ℤ_[2]) (h : ℕ) : ContinuousMulEquiv (NFrameModel h) (NFrameModel h) :=
  nNielsenHdlEquiv (nFamN2 k) (nFamN2 (-k)) (nNielsenFac_N2_inv k)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N2_inv (-k) v) h

/-- Family **N3**, with the identity handle tail. -/
def nNielsenHdlN3 (k : ℤ_[2]) (h : ℕ) : ContinuousMulEquiv (NFrameModel h) (NFrameModel h) :=
  nNielsenHdlEquiv (nFamN3 k) (nFamN3 (-k)) (nNielsenFac_N3_inv k)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N3_inv (-k) v) h

/-- Family **N4**, with the identity handle tail. -/
def nNielsenHdlN4 (κ : ℤ_[2]ˣ) (h : ℕ) : ContinuousMulEquiv (NFrameModel h) (NFrameModel h) :=
  nNielsenHdlEquiv (nFamN4 κ) (nFamN4 κ⁻¹) (nNielsenFac_N4_inv κ)
    (fun v => by simpa only [inv_inv] using nNielsenFac_N4_inv κ⁻¹ v) h

/-- Family **N5**, with the identity handle tail. -/
def nNielsenHdlN5 (p : ℤ_[2]) (h : ℕ) : ContinuousMulEquiv (NFrameModel h) (NFrameModel h) :=
  nNielsenHdlEquiv (nFamN5 p) (nFamN5 (-p)) (nNielsenFac_N5_inv p)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N5_inv (-p) v) h

/-- Family **N6**, with the identity handle tail. -/
def nNielsenHdlN6 (q : ℤ_[2]) (h : ℕ) : ContinuousMulEquiv (NFrameModel h) (NFrameModel h) :=
  nNielsenHdlEquiv (nFamN6 q) (nFamN6 (-q)) (nNielsenFac_N6_inv q)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N6_inv (-q) v) h

/-! ## Composition, and the lifts at every handle count -/

/-- `Psi` is an actual `chiN`-preserving continuous automorphism of `D_N` at handle count `h`
inducing `phi` on the full abelian frame. Verbatim the conclusion of `nFullStabilizer_lift`. -/
def NNielsenHdlLifts {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ}
    (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) : Prop :=
  ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
    (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
    (∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x)))

theorem nNielsenHdlLifts_refl {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) :
    NNielsenHdlLifts (alpha := alpha) ha (ContinuousMulEquiv.refl (NFrameModel h)) :=
  ⟨ContinuousMulEquiv.refl _, fun _ => rfl, fun _ => rfl⟩

theorem nNielsenHdlLifts_trans {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ}
    {phi psi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)}
    (h1 : NNielsenHdlLifts (alpha := alpha) ha phi)
    (h2 : NNielsenHdlLifts (alpha := alpha) ha psi) :
    NNielsenHdlLifts (alpha := alpha) ha (phi.trans psi) := by
  obtain ⟨P, hP1, hP2⟩ := h1
  obtain ⟨Q, hQ1, hQ2⟩ := h2
  refine ⟨P.trans Q, fun x => ?_, fun x => ?_⟩
  · exact (hQ1 (P x)).trans (hP1 x)
  · show nPhiHom ha h (abMk (Q (P x))) = psi (phi _)
    rw [hQ2 (P x), hP2 x]

/-- The composite of a finite list of frame automorphisms, leftmost applied first. -/
def nNielsenHdlCompose {h : ℕ}
    (L : List (ContinuousMulEquiv (NFrameModel h) (NFrameModel h))) :
    ContinuousMulEquiv (NFrameModel h) (NFrameModel h) :=
  L.foldr (fun g e => g.trans e) (ContinuousMulEquiv.refl _)

theorem nNielsenHdlLifts_compose {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ}
    (L : List (ContinuousMulEquiv (NFrameModel h) (NFrameModel h)))
    (hL : ∀ g ∈ L, NNielsenHdlLifts (alpha := alpha) ha g) :
    NNielsenHdlLifts (alpha := alpha) ha (nNielsenHdlCompose L) := by
  induction L with
  | nil => exact nNielsenHdlLifts_refl ha h
  | cons g L ih =>
      exact nNielsenHdlLifts_trans ha (hL g (List.mem_cons_self))
        (ih fun x hx => hL x (List.mem_cons_of_mem g hx))

/-- **Every identity-tail extension of an admissible rank-four `N` stabilizer parameter lifts,
at every handle count.** -/
theorem nNielsenHdlLifts_of_param {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hP : P.Admissible) (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v)
    (h : ℕ) : NNielsenHdlLifts (alpha := alpha) ha (nNielsenHdlEquiv P Q hPQ hQP h) :=
  nFullStabilizer_lift ha (nNielsenHdlEquiv P Q hPQ hQP h)
    (nNielsenHdl_orientation ha P Q hPQ hQP h) (nNielsenHdl_cupIsometry ha P Q hP hPQ hQP h)

/-! ## The packet's eight-slot list, at every handle count -/

/-- **The eight-slot Nielsen list at handle count `h`**, in `NNielsenFactorization`'s order,
each slot with the identity handle tail. -/
def nNielsenHdlList (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]) (h : ℕ) :
    List (ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :=
  [nNielsenHdlN2 z h, nNielsenHdlN3 y h, nNielsenHdlN2 x h, nNielsenHdlN4 κ h,
    nNielsenHdlN3 w h, nNielsenHdlN5 p h, nNielsenHdlN6 q h, nNielsenHdlN1 k h]

theorem nNielsenHdlList_length (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]) (h : ℕ) :
    (nNielsenHdlList z y x κ w p q k h).length = 8 := rfl

theorem nNielsenHdlCompose_list (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]) (h : ℕ)
    (v : NFrameModel h) :
    nNielsenHdlCompose (nNielsenHdlList z y x κ w p q k h) v =
      nNielsenHdlLift ((nFamN1 k).act ∘ (nFamN6 q).act ∘ (nFamN5 p).act ∘ (nFamN3 w).act ∘
        (nFamN4 κ).act ∘ (nFamN2 x).act ∘ (nFamN3 y).act ∘ (nFamN2 z).act) v := rfl

/-- Each generator preserves the orientation, is a cup isometry, and lifts, at every `h`. -/
theorem nNielsenHdl_props_of_param {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hP : P.Admissible) (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v)
    (h : ℕ) :
    (∀ z, nFrameOrientation ha h (nNielsenHdlEquiv P Q hPQ hQP h z)
        = nFrameOrientation ha h z) ∧
      NFrameCupIsometry ha (nNielsenHdlEquiv P Q hPQ hQP h) ∧
      NNielsenHdlLifts (alpha := alpha) ha (nNielsenHdlEquiv P Q hPQ hQP h) :=
  ⟨nNielsenHdl_orientation ha P Q hPQ hQP h, nNielsenHdl_cupIsometry ha P Q hP hPQ hQP h,
    nNielsenHdlLifts_of_param ha P Q hP hPQ hQP h⟩

theorem nNielsenHdlList_props {alpha : ℕ} (ha : 2 ≤ alpha) (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ)
    (w p q k : ℤ_[2]) (h : ℕ) :
    ∀ g ∈ nNielsenHdlList z y x κ w p q k h,
      (∀ v, nFrameOrientation ha h (g v) = nFrameOrientation ha h v) ∧
        NFrameCupIsometry ha g ∧ NNielsenHdlLifts (alpha := alpha) ha g := by
  intro g hg
  simp only [nNielsenHdlList, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nNielsenHdl_props_of_param ha _ _ (nFamN2_admissible z) _ _ h
  · exact nNielsenHdl_props_of_param ha _ _ (nFamN3_admissible y) _ _ h
  · exact nNielsenHdl_props_of_param ha _ _ (nFamN2_admissible x) _ _ h
  · exact nNielsenHdl_props_of_param ha _ _ (nFamN4_admissible κ) _ _ h
  · exact nNielsenHdl_props_of_param ha _ _ (nFamN3_admissible w) _ _ h
  · exact nNielsenHdl_props_of_param ha _ _ (nFamN5_admissible p) _ _ h
  · exact nNielsenHdl_props_of_param ha _ _ (nFamN6_admissible q) _ _ h
  · exact nNielsenHdl_props_of_param ha _ _ (nFamN1_admissible k) _ _ h

/-- **The MC-N finite-list artifact at every handle count** (`alpha >= 2`), for the
identity-handle-tail extensions.

For every admissible rank-four parameter `P : NStabParam` and every handle count `h` there is
an explicit list of **eight** frame automorphisms of `NFrameModel h`, each a member of memo
§3.4's six families at an explicit parameter extended by the identity on the `2h` handle
coordinates, each preserving the orientation and the full mod-two cup form and therefore
lifting to an actual `chiN`-preserving continuous automorphism of `D_N α h`, whose composite
is the identity-tail extension of the frame action of `P`, and whose lifts compose to a lift
of that composite.

**This is not a handle-mixing classification.** The parameter `P` is a *rank-four* stabilizer
parameter, and every map produced here is the identity on the handle block. -/
theorem nNielsenHdl_finite_list {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (P : NStabParam)
    (hP : P.Admissible) :
    ∃ (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]),
      (nNielsenHdlList z y x κ w p q k h).length = 8 ∧
      (∀ g ∈ nNielsenHdlList z y x κ w p q k h,
        (∀ v, nFrameOrientation ha h (g v) = nFrameOrientation ha h v) ∧
          NFrameCupIsometry ha g ∧ NNielsenHdlLifts (alpha := alpha) ha g) ∧
      (∀ v, nNielsenHdlCompose (nNielsenHdlList z y x κ w p q k h) v = nNielsenHdlMap P v) ∧
      NNielsenHdlLifts (alpha := alpha) ha
        (nNielsenHdlCompose (nNielsenHdlList z y x κ w p q k h)) := by
  obtain ⟨k, q, p, w, x, y, z, κ, -, -, hfac⟩ := nNielsen_factorization P hP
  refine ⟨z, y, x, κ, w, p, q, k, nNielsenHdlList_length _ _ _ _ _ _ _ _ h,
    nNielsenHdlList_props ha _ _ _ _ _ _ _ _ h, fun v => ?_, ?_⟩
  · rw [nNielsenHdlCompose_list, nNielsenHdlMap_eq_lift, hfac]
  · exact nNielsenHdlLifts_compose ha _
      (fun g hg => (nNielsenHdlList_props ha _ _ _ _ _ _ _ _ h g hg).2.2)

/-- **Every identity-tail extension of an admissible rank-four parameter is realized by an
actual automorphism of `D_N α h`**, as the composite of the eight generators' lifts. -/
theorem nNielsenHdl_param_realized {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (P : NStabParam)
    (hP : P.Admissible) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
      (∀ x, nPhiHom ha h (abMk (Psi x)) = nNielsenHdlMap P (nPhiHom ha h (abMk x))) := by
  obtain ⟨z, y, x, κ, w, p, q, k, -, -, hcomp, Psi, hchi, hsq⟩ :=
    nNielsenHdl_finite_list ha h P hP
  exact ⟨Psi, hchi, fun u => (hsq u).trans (hcomp _)⟩

/-! ## The closure in the identity-tail form -/

/-- The two block conditions pin the map. -/
theorem nNielsenHdl_eq_of_blocks {h : ℕ} (P : NStabParam)
    (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h))
    (hcore : ∀ z, nNielsenHdlCore (phi z) = nNielsenFacMap P (nNielsenHdlCore z))
    (hhandle : ∀ z, (phi z).toAdd.2.2.2.2 = z.toAdd.2.2.2.2) (z : NFrameModel h) :
    phi z = nNielsenHdlMap P z := by
  have h1 := congrArg (fun w : NFrameModel 0 => w.toAdd.1) (hcore z)
  have h2 := congrArg (fun w : NFrameModel 0 => w.toAdd.2.1) (hcore z)
  have h3 := congrArg (fun w : NFrameModel 0 => w.toAdd.2.2.1) (hcore z)
  have h4 := congrArg (fun w : NFrameModel 0 => w.toAdd.2.2.2.1) (hcore z)
  exact Multiplicative.toAdd.injective
    (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 (hhandle z)))))

/-- **T2, the closure at every handle count.** Every continuous automorphism of the full `N`
frame at handle count `h` that acts on the rank-four core block by an admissible Smith-Witt
stabilizer parameter and by the **identity** on the `2h` handle coordinates is induced by an
actual `chiN`-preserving continuous automorphism of `D_N α h`, with the exact all-element
commuting frame square. An automorphism that mixes handles satisfies neither hypothesis and
is not covered. -/
theorem nNielsenHdl_stabilizer_induced {alpha : ℕ} (ha : 2 ≤ alpha) {h : ℕ} (P : NStabParam)
    (hP : P.Admissible) (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h))
    (hcore : ∀ z, nNielsenHdlCore (phi z) = nNielsenFacMap P (nNielsenHdlCore z))
    (hhandle : ∀ z, (phi z).toAdd.2.2.2.2 = z.toAdd.2.2.2.2) :
    ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
      (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
      (∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x))) := by
  obtain ⟨Psi, hchi, hsq⟩ := nNielsenHdl_param_realized ha h P hP
  exact ⟨Psi, hchi, fun x => (hsq x).trans
    (nNielsenHdl_eq_of_blocks P phi hcore hhandle _).symm⟩

#print axioms nNielsenHdlN1
#print axioms nNielsenHdlN2
#print axioms nNielsenHdlN3
#print axioms nNielsenHdlN4
#print axioms nNielsenHdlN5
#print axioms nNielsenHdlN6
#print axioms NNielsenHdlLifts
#print axioms nNielsenHdlLifts_refl
#print axioms nNielsenHdlLifts_trans
#print axioms nNielsenHdlCompose
#print axioms nNielsenHdlLifts_compose
#print axioms nNielsenHdlLifts_of_param
#print axioms nNielsenHdlList
#print axioms nNielsenHdlList_length
#print axioms nNielsenHdlCompose_list
#print axioms nNielsenHdl_props_of_param
#print axioms nNielsenHdlList_props
#print axioms nNielsenHdl_finite_list
#print axioms nNielsenHdl_param_realized
#print axioms nNielsenHdl_eq_of_blocks
#print axioms nNielsenHdl_stabilizer_induced

#print axioms nNielsenHdl_coord_handle
#print axioms nNielsenHdl_char_of_core
#print axioms nNielsenHdl_char_coreMark
#print axioms nNielsenHdlMap_of_core_trivial
#print axioms nNielsenHdl_fix_markU
#print axioms nNielsenHdl_fix_markV
#print axioms nNielsenHdl_cup_head
#print axioms nNielsenHdl_cupIsometry

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
