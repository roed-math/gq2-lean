/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedFiniteCore

/-!
# The torsion row in the neutral relative source

The finite neutral `C` source is defined by vanishing under every continuous `Z_2`-valued
character.  This module identifies that condition on the full Demushkin group: it is exactly
the assertion that the abelianization class has order dividing two.  The only undetected class
is the distinguished order-two torsion class.

Inside the exact handle-forgetting kernel, that torsion class cannot occur.  Consequently the
neutrality condition there is exactly trivial abelianization, and the finite neutral relative
layer is the image of the relative abelianization kernel.  This is the prerequisite for a
coordinate calculation of the W221 finite `ZMod 4` cokernel; no coordinate dimension or
vanishing claim is made here.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityTorsionRow

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Roe.Labute
open scoped GQ2.SectionThree.TopAbInstances

/-- The first handle `U`-coordinate, pulled back to the Demushkin group. -/
def oneHandleHandleUHom :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  (mHHom 2 (mHandleCoordU (0 : Fin 1))).comp (mAbMkHom 2 1)

/-- The first handle `V`-coordinate, pulled back to the Demushkin group. -/
def oneHandleHandleVHom :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  (mHHom 2 (mHandleCoordV (0 : Fin 1))).comp (mAbMkHom 2 1)

private def oneHandleBHom :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  (mBHom 2 1).comp (mAbMkHom 2 1)

private def oneHandleCHom :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  (mCHom (by omega : 1 ≤ 2) 1).comp (mAbMkHom 2 1)

private def oneHandleDHom :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  (mDHom 2 1).comp (mAbMkHom 2 1)

private def oneHandleTorsionHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative (ZMod 2)) :=
  (mTHom 2 h).comp (mAbMkHom 2 h)

private theorem oneHandleTorsionHom_forget (x : DM 2 1) :
    oneHandleTorsionHom 1 x =
      oneHandleTorsionHom 0 (dmForgetHandles 2 1 x) := by
  have heq : oneHandleTorsionHom 1 =
      (oneHandleTorsionHom 0).comp (dmForgetHandles 2 1) := by
    apply dm_hom_ext
    intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · change oneHandleTorsionHom 1 (dmA 2 1) =
        oneHandleTorsionHom 0 (dmForgetHandles 2 1 (dmA 2 1))
      rw [dmForgetHandles_dmA]
      change mTHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 0)) =
        mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 0))
      rw [mTHom, mCoordHom_gen, mTHom, mCoordHom_gen]
      rfl
    · change oneHandleTorsionHom 1 (dmB 2 1) =
        oneHandleTorsionHom 0 (dmForgetHandles 2 1 (dmB 2 1))
      rw [dmForgetHandles_dmB]
      change mTHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 1)) =
        mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 1))
      rw [mTHom, mCoordHom_gen, mTHom, mCoordHom_gen]
      rfl
    · change oneHandleTorsionHom 1 (dmC 2 1) =
        oneHandleTorsionHom 0 (dmForgetHandles 2 1 (dmC 2 1))
      rw [dmForgetHandles_dmC]
      change mTHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 2)) =
        mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 2))
      rw [mTHom, mCoordHom_gen, mTHom, mCoordHom_gen]
      rfl
    · change oneHandleTorsionHom 1 (dmD 2 1) =
        oneHandleTorsionHom 0 (dmForgetHandles 2 1 (dmD 2 1))
      rw [dmForgetHandles_dmD]
      change mTHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 3)) =
        mTHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 3))
      rw [mTHom, mCoordHom_gen, mTHom, mCoordHom_gen]
      rfl
    · rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [mHandleIdx_coordU]
        change oneHandleTorsionHom 1 (dmGen 2 1 (handleIdxU j)) =
          oneHandleTorsionHom 0
            (dmForgetHandles 2 1 (dmGen 2 1 (handleIdxU j)))
        rw [dmForgetHandles_handleU]
        simp [oneHandleTorsionHom, mTHom, mCoordHom_gen]
      · rw [mHandleIdx_coordV]
        change oneHandleTorsionHom 1 (dmGen 2 1 (handleIdxV j)) =
          oneHandleTorsionHom 0
            (dmForgetHandles 2 1 (dmGen 2 1 (handleIdxV j)))
        rw [dmForgetHandles_handleV]
        simp [oneHandleTorsionHom, mTHom, mCoordHom_gen]
  exact DFunLike.congr_fun heq x

private theorem abMk_sq_eq_one_of_rowKer
    {x : DM 2 1} (hx : x ∈ oneHandleRowKer) :
    (GQ2.SectionThree.abMk x) ^ 2 = 1 := by
  have hb := (mem_oneHandleRowKer_iff.mp hx) oneHandleBHom
  have hc := (mem_oneHandleRowKer_iff.mp hx) oneHandleCHom
  have hd := (mem_oneHandleRowKer_iff.mp hx) oneHandleDHom
  have hU := (mem_oneHandleRowKer_iff.mp hx) oneHandleHandleUHom
  have hV := (mem_oneHandleRowKer_iff.mp hx) oneHandleHandleVHom
  apply mPhiHom_injective (by omega : 1 ≤ 2) 1
  rw [map_pow, map_one]
  change (ofAdd
    ((mTHom 2 1 (GQ2.SectionThree.abMk x)).toAdd,
      (mBHom 2 1 (GQ2.SectionThree.abMk x)).toAdd,
      (mCHom (by omega : 1 ≤ 2) 1 (GQ2.SectionThree.abMk x)).toAdd,
      (mDHom 2 1 (GQ2.SectionThree.abMk x)).toAdd,
      fun k => (mHHom 2 k (GQ2.SectionThree.abMk x)).toAdd)) ^ 2 = 1
  rw [← ofAdd_nsmul]
  apply congrArg ofAdd
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · change (2 : ℕ) • (mTHom 2 1 (GQ2.SectionThree.abMk x)).toAdd = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _
  · change (2 : ℕ) • toAdd (oneHandleBHom x) = 0
    rw [hb, toAdd_one, smul_zero]
  · change (2 : ℕ) • toAdd (oneHandleCHom x) = 0
    rw [hc, toAdd_one, smul_zero]
  · change (2 : ℕ) • toAdd (oneHandleDHom x) = 0
    rw [hd, toAdd_one, smul_zero]
  · funext k
    rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · fin_cases j
      change (2 : ℕ) • toAdd (oneHandleHandleUHom x) = 0
      rw [hU, toAdd_one, smul_zero]
    · fin_cases j
      change (2 : ℕ) • toAdd (oneHandleHandleVHom x) = 0
      rw [hV, toAdd_one, smul_zero]

private theorem rowKer_of_abMk_sq_eq_one
    {x : DM 2 1} (hx : (GQ2.SectionThree.abMk x) ^ 2 = 1) :
    x ∈ oneHandleRowKer := by
  apply mem_oneHandleRowKer_iff.mpr
  intro f
  have hf2 : (f x) ^ 2 = 1 := by
    have h := congrArg (GQ2.SectionThree.abLiftG f) hx
    simpa only [map_pow, map_one, GQ2.SectionThree.abLiftG_abMk] using h
  apply Multiplicative.toAdd.injective
  have hzero : (2 : ℤ_[2]) * toAdd (f x) = 0 := by
    have h := congrArg Multiplicative.toAdd hf2
    rw [pow_two, toAdd_mul, toAdd_one] at h
    simpa [two_mul] using h
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- An element is killed by every continuous `ℤ₂`-row exactly when its abelianization has
order dividing two. -/
theorem mem_oneHandleRowKer_iff_abMk_sq_eq_one {x : DM 2 1} :
    x ∈ oneHandleRowKer ↔ (GQ2.SectionThree.abMk x) ^ 2 = 1 := by
  exact ⟨abMk_sq_eq_one_of_rowKer, rowKer_of_abMk_sq_eq_one⟩

private theorem abMk_eq_one_of_rowKer_of_forget
    {x : DM 2 1} (hforget : dmForgetHandles 2 1 x = 1)
    (hx : x ∈ oneHandleRowKer) : GQ2.SectionThree.abMk x = 1 := by
  have hT : oneHandleTorsionHom 1 x = 1 := by
    rw [oneHandleTorsionHom_forget, hforget, map_one]
  have hb := (mem_oneHandleRowKer_iff.mp hx) oneHandleBHom
  have hc := (mem_oneHandleRowKer_iff.mp hx) oneHandleCHom
  have hd := (mem_oneHandleRowKer_iff.mp hx) oneHandleDHom
  have hU := (mem_oneHandleRowKer_iff.mp hx) oneHandleHandleUHom
  have hV := (mem_oneHandleRowKer_iff.mp hx) oneHandleHandleVHom
  apply mPhiHom_injective (by omega : 1 ≤ 2) 1
  rw [map_one]
  change ofAdd
    ((mTHom 2 1 (GQ2.SectionThree.abMk x)).toAdd,
      (mBHom 2 1 (GQ2.SectionThree.abMk x)).toAdd,
      (mCHom (by omega : 1 ≤ 2) 1 (GQ2.SectionThree.abMk x)).toAdd,
      (mDHom 2 1 (GQ2.SectionThree.abMk x)).toAdd,
      fun k => (mHHom 2 k (GQ2.SectionThree.abMk x)).toAdd) = 1
  apply congrArg ofAdd
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · change toAdd (oneHandleTorsionHom 1 x) = 0
    rw [hT, toAdd_one]
  · change toAdd (oneHandleBHom x) = 0
    rw [hb, toAdd_one]
  · change toAdd (oneHandleCHom x) = 0
    rw [hc, toAdd_one]
  · change toAdd (oneHandleDHom x) = 0
    rw [hd, toAdd_one]
  · funext k
    rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · fin_cases j
      change toAdd (oneHandleHandleUHom x) = 0
      rw [hU, toAdd_one]
    · fin_cases j
      change toAdd (oneHandleHandleVHom x) = 0
      rw [hV, toAdd_one]

/-- Inside the handle-forgetting kernel, universal `ℤ₂`-row neutrality is exactly
triviality of the full abelianization.  The extra hypothesis removes the residual order-two
class left invisible by torsion-free `ℤ₂` rows. -/
theorem mem_oneHandleRowKer_iff_abMk_eq_one_of_forget
    {x : DM 2 1} (hforget : dmForgetHandles 2 1 x = 1) :
    x ∈ oneHandleRowKer ↔ GQ2.SectionThree.abMk x = 1 := by
  constructor
  · exact abMk_eq_one_of_rowKer_of_forget hforget
  · intro hx
    rw [mem_oneHandleRowKer_iff_abMk_sq_eq_one, hx]
    exact one_pow 2

/-- After imposing handle-forgetting, the row-neutral exact subgroup is simply the kernel of
abelianization. -/
theorem oneHandleRelativeRowKer_eq_abMkKernel (j : ℕ) :
    (twoCentralSeries (DM 2 1) j ⊓
        (dmForgetHandles 2 1).toMonoidHom.ker) ⊓ oneHandleRowKer =
      (twoCentralSeries (DM 2 1) j ⊓
        (dmForgetHandles 2 1).toMonoidHom.ker) ⊓
          (mAbMkHom 2 1).toMonoidHom.ker := by
  ext x
  constructor
  · rintro ⟨⟨hx, hforget⟩, hrow⟩
    refine ⟨⟨hx, hforget⟩, MonoidHom.mem_ker.mpr ?_⟩
    exact (mem_oneHandleRowKer_iff_abMk_eq_one_of_forget
      (MonoidHom.mem_ker.mp hforget)).mp hrow
  · rintro ⟨⟨hx, hforget⟩, hab⟩
    refine ⟨⟨hx, hforget⟩, ?_⟩
    exact (mem_oneHandleRowKer_iff_abMk_eq_one_of_forget
      (MonoidHom.mem_ker.mp hforget)).mpr (MonoidHom.mem_ker.mp hab)

/-- The finite neutral relative layer is the image of exact relative elements with trivial
abelianization. -/
theorem oneHandleNeutralRelativeLambdaImage_eq_abMkKernel (j n : ℕ) :
    oneHandleNeutralRelativeLambdaImage j n =
      ((twoCentralSeries (DM 2 1) j ⊓
          (dmForgetHandles 2 1).toMonoidHom.ker) ⊓
        (mAbMkHom 2 1).toMonoidHom.ker).map (levelMk (DM 2 1) n) := by
  rw [oneHandleNeutralRelativeLambdaImage,
    oneHandleRelativeRowKer_eq_abMkKernel]

#print axioms oneHandleHandleUHom
#print axioms oneHandleHandleVHom
#print axioms mem_oneHandleRowKer_iff_abMk_sq_eq_one
#print axioms mem_oneHandleRowKer_iff_abMk_eq_one_of_forget
#print axioms oneHandleRelativeRowKer_eq_abMkKernel
#print axioms oneHandleNeutralRelativeLambdaImage_eq_abMkKernel

end

end GQ2.Dyadic.Instances.MpcBalancedNeutralityTorsionRow
