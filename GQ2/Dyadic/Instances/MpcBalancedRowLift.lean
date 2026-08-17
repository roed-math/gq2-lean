import GQ2.Dyadic.Instances.MpcFixedCNeutralBracketObstruction

/-!
# Balanced one-handle row lifts

W198 rules out both unrestricted and abelian-neutral fixed-`C`, one-slot bracket
surjectivity.  The honest remaining route is therefore the balanced multi-slot inverse limit
from `MpcOneHandleBalancedLimit`.

This module separates its routine linear and Frattini clauses from the genuinely nonabelian
finite relator defect.  First, a lift of the compact `C + 2 B` row is corrected inside its
handle-forgetting fibre by clearing both handle coordinates.  Its residual abelianization has
order two, so every `ℤ₂`-valued character kills it.  Second, any index-two quotient killing
the standard handle pair factors through handle-forgetting.  Four lifts of a compact
automorphic basis therefore remain mod-two independent.  Consequently every compact shift
witness has a one-handle balanced seed satisfying every clause of `oneHandleBalancedSet`
except the finite-depth relator-defect condition.

No relator-defect lifting claim is made here.  Per-class nonemptiness of that final condition
is the precise remaining input to the existing compactness theorem.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedRowLift

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open scoped GQ2.SectionThree.TopAbInstances

private abbrev U : DM 2 1 := dmGen 2 1 (handleIdxU (0 : Fin 1))
private abbrev V : DM 2 1 := dmGen 2 1 (handleIdxV (0 : Fin 1))

private def handleUHom :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  (mHHom 2 (mHandleCoordU (0 : Fin 1))).comp (mAbMkHom 2 1)

private def handleVHom :
    ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]) :=
  (mHHom 2 (mHandleCoordV (0 : Fin 1))).comp (mAbMkHom 2 1)

private def handleUCoord (x : DM 2 1) : ℤ_[2] := toAdd (handleUHom x)

private def handleVCoord (x : DM 2 1) : ℤ_[2] := toAdd (handleVHom x)

private def clearHandleRows (x : DM 2 1) : DM 2 1 :=
  zpowZtwo (isProP_DM 2 1) U (-handleUCoord x) *
    zpowZtwo (isProP_DM 2 1) V (-handleVCoord x) * x

private theorem dmForgetHandles_clearHandleRows (x : DM 2 1) :
    dmForgetHandles 2 1 (clearHandleRows x) = dmForgetHandles 2 1 x := by
  rw [clearHandleRows, map_mul, map_mul,
    map_zpowZtwo (isProP_DM 2 1) (isProP_DM 2 0),
    map_zpowZtwo (isProP_DM 2 1) (isProP_DM 2 0),
    dmForgetHandles_handleU, dmForgetHandles_handleV,
    zpowZtwo_one_base, zpowZtwo_one_base, one_mul, one_mul]

private theorem mHHom_U_U :
    toAdd (handleUHom U) = 1 := by
  change toAdd (mHHom 2 (mHandleCoordU (0 : Fin 1))
    (GQ2.SectionThree.abMk U)) = 1
  rw [mHHom, mCoordHom_gen, ← mHandleIdx_coordU, mHandleMark_self, toAdd_ofAdd]

private theorem mHHom_U_V :
    toAdd (handleUHom V) = 0 := by
  change toAdd (mHHom 2 (mHandleCoordU (0 : Fin 1))
    (GQ2.SectionThree.abMk V)) = 0
  rw [mHHom, mCoordHom_gen, ← mHandleIdx_coordV]
  rw [mHandleMark_of_ne]
  · rfl
  · decide

private theorem mHHom_V_U :
    toAdd (handleVHom U) = 0 := by
  change toAdd (mHHom 2 (mHandleCoordV (0 : Fin 1))
    (GQ2.SectionThree.abMk U)) = 0
  rw [mHHom, mCoordHom_gen, ← mHandleIdx_coordU]
  rw [mHandleMark_of_ne]
  · rfl
  · decide

private theorem mHHom_V_V :
    toAdd (handleVHom V) = 1 := by
  change toAdd (mHHom 2 (mHandleCoordV (0 : Fin 1))
    (GQ2.SectionThree.abMk V)) = 1
  rw [mHHom, mCoordHom_gen, ← mHandleIdx_coordV, mHandleMark_self, toAdd_ofAdd]

private theorem handleUCoord_clearHandleRows (x : DM 2 1) :
    handleUCoord (clearHandleRows x) = 0 := by
  rw [handleUCoord, clearHandleRows]
  rw [map_mul handleUHom, map_mul handleUHom]
  change toAdd (handleUHom (zpowZtwo (isProP_DM 2 1) U (-handleUCoord x)) *
    handleUHom (zpowZtwo (isProP_DM 2 1) V (-handleVCoord x)) * handleUHom x) = 0
  rw [toAdd_mul, toAdd_mul,
    toAdd_map_zpowZtwo (isProP_DM 2 1),
    toAdd_map_zpowZtwo (isProP_DM 2 1), mHHom_U_U, mHHom_U_V,
    handleUCoord]
  ring

private theorem handleVCoord_clearHandleRows (x : DM 2 1) :
    handleVCoord (clearHandleRows x) = 0 := by
  rw [handleVCoord, clearHandleRows]
  rw [map_mul handleVHom, map_mul handleVHom]
  change toAdd (handleVHom (zpowZtwo (isProP_DM 2 1) U (-handleUCoord x)) *
    handleVHom (zpowZtwo (isProP_DM 2 1) V (-handleVCoord x)) * handleVHom x) = 0
  rw [toAdd_mul, toAdd_mul,
    toAdd_map_zpowZtwo (isProP_DM 2 1),
    toAdd_map_zpowZtwo (isProP_DM 2 1), mHHom_V_U, mHHom_V_V,
    handleVCoord]
  ring

private def bHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative ℤ_[2]) :=
  (mBHom 2 h).comp (mAbMkHom 2 h)

private def cHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative ℤ_[2]) :=
  (mCHom (by omega : 1 ≤ 2) h).comp (mAbMkHom 2 h)

private def dHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative ℤ_[2]) :=
  (mDHom 2 h).comp (mAbMkHom 2 h)

private theorem bHom_forget (x : DM 2 1) :
    bHom 1 x = bHom 0 (dmForgetHandles 2 1 x) := by
  have heq : bHom 1 = (bHom 0).comp (dmForgetHandles 2 1) := by
    apply dm_hom_ext
    intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · change bHom 1 (dmA 2 1) = bHom 0 (dmForgetHandles 2 1 (dmA 2 1))
      rw [dmForgetHandles_dmA]
      change mBHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 0)) =
        mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 0))
      rw [mBHom, mCoordHom_gen, mBHom, mCoordHom_gen]
      rfl
    · change bHom 1 (dmB 2 1) = bHom 0 (dmForgetHandles 2 1 (dmB 2 1))
      rw [dmForgetHandles_dmB]
      change mBHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 1)) =
        mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 1))
      rw [mBHom, mCoordHom_gen, mBHom, mCoordHom_gen]
      rfl
    · change bHom 1 (dmC 2 1) = bHom 0 (dmForgetHandles 2 1 (dmC 2 1))
      rw [dmForgetHandles_dmC]
      change mBHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 2)) =
        mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 2))
      rw [mBHom, mCoordHom_gen, mBHom, mCoordHom_gen]
      rfl
    · change bHom 1 (dmD 2 1) = bHom 0 (dmForgetHandles 2 1 (dmD 2 1))
      rw [dmForgetHandles_dmD]
      change mBHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 3)) =
        mBHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 3))
      rw [mBHom, mCoordHom_gen, mBHom, mCoordHom_gen]
      rfl
    · rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [mHandleIdx_coordU]
        change bHom 1 (dmGen 2 1 (handleIdxU j)) =
          bHom 0 (dmForgetHandles 2 1 (dmGen 2 1 (handleIdxU j)))
        rw [dmForgetHandles_handleU]
        simp [bHom, mBHom, mCoordHom_gen]
      · rw [mHandleIdx_coordV]
        change bHom 1 (dmGen 2 1 (handleIdxV j)) =
          bHom 0 (dmForgetHandles 2 1 (dmGen 2 1 (handleIdxV j)))
        rw [dmForgetHandles_handleV]
        simp [bHom, mBHom, mCoordHom_gen]
  exact DFunLike.congr_fun heq x

private theorem cHom_forget (x : DM 2 1) :
    cHom 1 x = cHom 0 (dmForgetHandles 2 1 x) := by
  have heq : cHom 1 = (cHom 0).comp (dmForgetHandles 2 1) := by
    apply dm_hom_ext
    intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · change cHom 1 (dmA 2 1) = cHom 0 (dmForgetHandles 2 1 (dmA 2 1))
      rw [dmForgetHandles_dmA]
      change mCHom (by omega : 1 ≤ 2) 1 (GQ2.SectionThree.abMk (dmGen 2 1 0)) =
        mCHom (by omega : 1 ≤ 2) 0 (GQ2.SectionThree.abMk (dmGen 2 0 0))
      rw [mCHom, mCoordHom_gen, mCHom, mCoordHom_gen]
      rfl
    · change cHom 1 (dmB 2 1) = cHom 0 (dmForgetHandles 2 1 (dmB 2 1))
      rw [dmForgetHandles_dmB]
      change mCHom (by omega : 1 ≤ 2) 1 (GQ2.SectionThree.abMk (dmGen 2 1 1)) =
        mCHom (by omega : 1 ≤ 2) 0 (GQ2.SectionThree.abMk (dmGen 2 0 1))
      rw [mCHom, mCoordHom_gen, mCHom, mCoordHom_gen]
      rfl
    · change cHom 1 (dmC 2 1) = cHom 0 (dmForgetHandles 2 1 (dmC 2 1))
      rw [dmForgetHandles_dmC]
      change mCHom (by omega : 1 ≤ 2) 1 (GQ2.SectionThree.abMk (dmGen 2 1 2)) =
        mCHom (by omega : 1 ≤ 2) 0 (GQ2.SectionThree.abMk (dmGen 2 0 2))
      rw [mCHom, mCoordHom_gen, mCHom, mCoordHom_gen]
      rfl
    · change cHom 1 (dmD 2 1) = cHom 0 (dmForgetHandles 2 1 (dmD 2 1))
      rw [dmForgetHandles_dmD]
      change mCHom (by omega : 1 ≤ 2) 1 (GQ2.SectionThree.abMk (dmGen 2 1 3)) =
        mCHom (by omega : 1 ≤ 2) 0 (GQ2.SectionThree.abMk (dmGen 2 0 3))
      rw [mCHom, mCoordHom_gen, mCHom, mCoordHom_gen]
      rfl
    · rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [mHandleIdx_coordU]
        change cHom 1 (dmGen 2 1 (handleIdxU j)) =
          cHom 0 (dmForgetHandles 2 1 (dmGen 2 1 (handleIdxU j)))
        rw [dmForgetHandles_handleU]
        simp [cHom, mCHom, mCoordHom_gen]
      · rw [mHandleIdx_coordV]
        change cHom 1 (dmGen 2 1 (handleIdxV j)) =
          cHom 0 (dmForgetHandles 2 1 (dmGen 2 1 (handleIdxV j)))
        rw [dmForgetHandles_handleV]
        simp [cHom, mCHom, mCoordHom_gen]
  exact DFunLike.congr_fun heq x

private theorem dHom_forget (x : DM 2 1) :
    dHom 1 x = dHom 0 (dmForgetHandles 2 1 x) := by
  have heq : dHom 1 = (dHom 0).comp (dmForgetHandles 2 1) := by
    apply dm_hom_ext
    intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · change dHom 1 (dmA 2 1) = dHom 0 (dmForgetHandles 2 1 (dmA 2 1))
      rw [dmForgetHandles_dmA]
      change mDHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 0)) =
        mDHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 0))
      rw [mDHom, mCoordHom_gen, mDHom, mCoordHom_gen]
      rfl
    · change dHom 1 (dmB 2 1) = dHom 0 (dmForgetHandles 2 1 (dmB 2 1))
      rw [dmForgetHandles_dmB]
      change mDHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 1)) =
        mDHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 1))
      rw [mDHom, mCoordHom_gen, mDHom, mCoordHom_gen]
      rfl
    · change dHom 1 (dmC 2 1) = dHom 0 (dmForgetHandles 2 1 (dmC 2 1))
      rw [dmForgetHandles_dmC]
      change mDHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 2)) =
        mDHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 2))
      rw [mDHom, mCoordHom_gen, mDHom, mCoordHom_gen]
      rfl
    · change dHom 1 (dmD 2 1) = dHom 0 (dmForgetHandles 2 1 (dmD 2 1))
      rw [dmForgetHandles_dmD]
      change mDHom 2 1 (GQ2.SectionThree.abMk (dmGen 2 1 3)) =
        mDHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 3))
      rw [mDHom, mCoordHom_gen, mDHom, mCoordHom_gen]
      rfl
    · rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [mHandleIdx_coordU]
        change dHom 1 (dmGen 2 1 (handleIdxU j)) =
          dHom 0 (dmForgetHandles 2 1 (dmGen 2 1 (handleIdxU j)))
        rw [dmForgetHandles_handleU]
        simp [dHom, mDHom, mCoordHom_gen]
      · rw [mHandleIdx_coordV]
        change dHom 1 (dmGen 2 1 (handleIdxV j)) =
          dHom 0 (dmForgetHandles 2 1 (dmGen 2 1 (handleIdxV j)))
        rw [dmForgetHandles_handleV]
        simp [dHom, mDHom, mCoordHom_gen]
  exact DFunLike.congr_fun heq x

private theorem coreHom_clearHandleRows
    (f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]))
    (hU : f U = 1) (hV : f V = 1) (x : DM 2 1) :
    f (clearHandleRows x) = f x := by
  rw [clearHandleRows, map_mul, map_mul,
    map_zpowZtwo (isProP_DM 2 1) PropOneOne.isProP_two_multPadicInt,
    map_zpowZtwo (isProP_DM 2 1) PropOneOne.isProP_two_multPadicInt,
    hU, hV, zpowZtwo_one_base, zpowZtwo_one_base, one_mul, one_mul]

private theorem bHom_clearHandleRows (x : DM 2 1) :
    bHom 1 (clearHandleRows x) = bHom 1 x := by
  apply coreHom_clearHandleRows
  · simp [bHom, mBHom, mCoordHom_gen]
  · simp [bHom, mBHom, mCoordHom_gen]

private theorem cHom_clearHandleRows (x : DM 2 1) :
    cHom 1 (clearHandleRows x) = cHom 1 x := by
  apply coreHom_clearHandleRows
  · simp [cHom, mCHom, mCoordHom_gen]
  · simp [cHom, mCHom, mCoordHom_gen]

private theorem dHom_clearHandleRows (x : DM 2 1) :
    dHom 1 (clearHandleRows x) = dHom 1 x := by
  apply coreHom_clearHandleRows
  · simp [dHom, mDHom, mCoordHom_gen]
  · simp [dHom, mDHom, mCoordHom_gen]

private def rowTarget : DM 2 1 := dmC 2 1 * dmB 2 1 ^ 2

private theorem rowTarget_apply
    (f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2])) :
    toAdd (f rowTarget) =
      toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1)) := by
  simp [rowTarget, map_mul, map_pow, toAdd_mul]

private theorem bHom_dmB (h : ℕ) : toAdd (bHom h (dmB 2 h)) = 1 := by
  change toAdd (mBHom 2 h (GQ2.SectionThree.abMk (dmGen 2 h 1))) = 1
  rw [mBHom, mCoordHom_gen, coreMark_one, toAdd_ofAdd]

private theorem bHom_dmC (h : ℕ) : toAdd (bHom h (dmC 2 h)) = 0 := by
  change toAdd (mBHom 2 h (GQ2.SectionThree.abMk (dmGen 2 h 2))) = 0
  rw [mBHom, mCoordHom_gen, coreMark_two, toAdd_one]

private theorem cHom_dmB (h : ℕ) : toAdd (cHom h (dmB 2 h)) = 0 := by
  change toAdd (mCHom (by omega : 1 ≤ 2) h
    (GQ2.SectionThree.abMk (dmGen 2 h 1))) = 0
  rw [mCHom, mCoordHom_gen, coreMark_one, toAdd_one]

private theorem cHom_dmC (h : ℕ) : toAdd (cHom h (dmC 2 h)) = 1 := by
  change toAdd (mCHom (by omega : 1 ≤ 2) h
    (GQ2.SectionThree.abMk (dmGen 2 h 2))) = 1
  rw [mCHom, mCoordHom_gen, coreMark_two, toAdd_ofAdd]

private theorem dHom_dmB (h : ℕ) : toAdd (dHom h (dmB 2 h)) = 0 := by
  change toAdd (mDHom 2 h (GQ2.SectionThree.abMk (dmGen 2 h 1))) = 0
  rw [mDHom, mCoordHom_gen, coreMark_one, toAdd_one]

private theorem dHom_dmC (h : ℕ) : toAdd (dHom h (dmC 2 h)) = 0 := by
  change toAdd (mDHom 2 h (GQ2.SectionThree.abMk (dmGen 2 h 2))) = 0
  rw [mDHom, mCoordHom_gen, coreMark_two, toAdd_one]

private theorem bHom_rowTarget : toAdd (bHom 1 rowTarget) = 2 := by
  rw [rowTarget_apply, bHom_dmC, bHom_dmB]
  ring

private theorem cHom_rowTarget : toAdd (cHom 1 rowTarget) = 1 := by
  rw [rowTarget_apply, cHom_dmC, cHom_dmB]
  ring

private theorem dHom_rowTarget : toAdd (dHom 1 rowTarget) = 0 := by
  rw [rowTarget_apply, dHom_dmC, dHom_dmB]
  ring

private theorem clearHandleRows_core_values
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    {x : DM 2 1} (hx : dmForgetHandles 2 1 x = Psi0 (dmC 2 0)) :
    bHom 1 (clearHandleRows x) = bHom 1 rowTarget ∧
      cHom 1 (clearHandleRows x) = cHom 1 rowTarget ∧
      dHom 1 (clearHandleRows x) = dHom 1 rowTarget := by
  constructor
  · apply Multiplicative.toAdd.injective
    rw [bHom_clearHandleRows, bHom_forget, hx, hrow (bHom 0)]
    rw [bHom_dmC, bHom_dmB, bHom_rowTarget]
    ring
  constructor
  · apply Multiplicative.toAdd.injective
    rw [cHom_clearHandleRows, cHom_forget, hx, hrow (cHom 0)]
    rw [cHom_dmC, cHom_dmB, cHom_rowTarget]
    ring
  · apply Multiplicative.toAdd.injective
    rw [dHom_clearHandleRows, dHom_forget, hx, hrow (dHom 0)]
    rw [dHom_dmC, dHom_dmB, dHom_rowTarget]
    ring

private theorem handleUHom_dmB : handleUHom (dmB 2 1) = 1 := by
  change mHHom 2 (mHandleCoordU (0 : Fin 1))
    (GQ2.SectionThree.abMk (dmGen 2 1 1)) = 1
  rw [mHHom, mCoordHom_gen, mHandleMark_core]
  · norm_num [coreRank]

private theorem handleUHom_dmC : handleUHom (dmC 2 1) = 1 := by
  change mHHom 2 (mHandleCoordU (0 : Fin 1))
    (GQ2.SectionThree.abMk (dmGen 2 1 2)) = 1
  rw [mHHom, mCoordHom_gen, mHandleMark_core]
  · norm_num [coreRank]

private theorem handleVHom_dmB : handleVHom (dmB 2 1) = 1 := by
  change mHHom 2 (mHandleCoordV (0 : Fin 1))
    (GQ2.SectionThree.abMk (dmGen 2 1 1)) = 1
  rw [mHHom, mCoordHom_gen, mHandleMark_core]
  · norm_num [coreRank]

private theorem handleVHom_dmC : handleVHom (dmC 2 1) = 1 := by
  change mHHom 2 (mHandleCoordV (0 : Fin 1))
    (GQ2.SectionThree.abMk (dmGen 2 1 2)) = 1
  rw [mHHom, mCoordHom_gen, mHandleMark_core]
  · norm_num [coreRank]

private theorem handleUHom_rowTarget : handleUHom rowTarget = 1 := by
  rw [rowTarget, map_mul, map_pow, handleUHom_dmC, handleUHom_dmB,
    one_pow, mul_one]

private theorem handleVHom_rowTarget : handleVHom rowTarget = 1 := by
  rw [rowTarget, map_mul, map_pow, handleVHom_dmC, handleVHom_dmB,
    one_pow, mul_one]

private theorem handleUHom_clearHandleRows (x : DM 2 1) :
    handleUHom (clearHandleRows x) = 1 := by
  apply Multiplicative.toAdd.injective
  change handleUCoord (clearHandleRows x) = 0
  exact handleUCoord_clearHandleRows x

private theorem handleVHom_clearHandleRows (x : DM 2 1) :
    handleVHom (clearHandleRows x) = 1 := by
  apply Multiplicative.toAdd.injective
  change handleVCoord (clearHandleRows x) = 0
  exact handleVCoord_clearHandleRows x

private theorem abMk_sq_eq_one_of_coordinate_zero (r : DM 2 1)
    (hb : bHom 1 r = 1) (hc : cHom 1 r = 1) (hd : dHom 1 r = 1)
    (hU : handleUHom r = 1) (hV : handleVHom r = 1) :
    (GQ2.SectionThree.abMk r) ^ 2 = 1 := by
  apply mPhiHom_injective (by omega : 1 ≤ 2) 1
  rw [map_pow, map_one]
  change (ofAdd
    ((mTHom 2 1 (GQ2.SectionThree.abMk r)).toAdd,
      (mBHom 2 1 (GQ2.SectionThree.abMk r)).toAdd,
      (mCHom (by omega : 1 ≤ 2) 1 (GQ2.SectionThree.abMk r)).toAdd,
      (mDHom 2 1 (GQ2.SectionThree.abMk r)).toAdd,
      fun k => (mHHom 2 k (GQ2.SectionThree.abMk r)).toAdd)) ^ 2 = 1
  rw [← ofAdd_nsmul]
  apply congrArg ofAdd
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · change (2 : ℕ) • (mTHom 2 1 (GQ2.SectionThree.abMk r)).toAdd = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _
  · change (2 : ℕ) • toAdd (bHom 1 r) = 0
    rw [hb, toAdd_one, smul_zero]
  · change (2 : ℕ) • toAdd (cHom 1 r) = 0
    rw [hc, toAdd_one, smul_zero]
  · change (2 : ℕ) • toAdd (dHom 1 r) = 0
    rw [hd, toAdd_one, smul_zero]
  · funext k
    rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · fin_cases j
      change (2 : ℕ) • toAdd (handleUHom r) = 0
      rw [hU, toAdd_one, smul_zero]
    · fin_cases j
      change (2 : ℕ) • toAdd (handleVHom r) = 0
      rw [hV, toAdd_one, smul_zero]

private theorem clearHandleRows_ratio_sq
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    {x : DM 2 1} (hx : dmForgetHandles 2 1 x = Psi0 (dmC 2 0)) :
    (GQ2.SectionThree.abMk
      (clearHandleRows x * rowTarget⁻¹)) ^ 2 = 1 := by
  obtain ⟨hb0, hc0, hd0⟩ := clearHandleRows_core_values Psi0 hrow hx
  apply abMk_sq_eq_one_of_coordinate_zero
  · rw [map_mul, map_inv, hb0, mul_inv_cancel]
  · rw [map_mul, map_inv, hc0, mul_inv_cancel]
  · rw [map_mul, map_inv, hd0, mul_inv_cancel]
  · rw [map_mul, map_inv, handleUHom_clearHandleRows,
      handleUHom_rowTarget, inv_one, mul_one]
  · rw [map_mul, map_inv, handleVHom_clearHandleRows,
      handleVHom_rowTarget, inv_one, mul_one]

private theorem padicHom_eq_one_of_abMk_sq_eq_one
    (f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]))
    {r : DM 2 1} (hr : (GQ2.SectionThree.abMk r) ^ 2 = 1) : f r = 1 := by
  have hf2 : (f r) ^ 2 = 1 := by
    have h := congrArg (GQ2.SectionThree.abLiftG f) hr
    simpa only [map_pow, map_one, GQ2.SectionThree.abLiftG_abMk] using h
  apply Multiplicative.toAdd.injective
  have hzero : (2 : ℤ_[2]) * toAdd (f r) = 0 := by
    have h := congrArg Multiplicative.toAdd hf2
    rw [pow_two, toAdd_mul, toAdd_one] at h
    simpa [two_mul] using h
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- Every lift of the compact pivot row can be corrected inside its handle-forgetting fibre so
that it has the required universal general-rank `C + 2 B` row. -/
theorem exists_rowCorrectedLift
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0))) :
    ∃ c : DM 2 1,
      dmForgetHandles 2 1 c = Psi0 (dmC 2 0) ∧
      ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
        toAdd (f c) =
          toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1)) := by
  obtain ⟨x, hx⟩ := dmForgetHandles_surjective 2 1 (Psi0 (dmC 2 0))
  refine ⟨clearHandleRows x, dmForgetHandles_clearHandleRows x |>.trans hx, ?_⟩
  intro f
  have hab := clearHandleRows_ratio_sq Psi0 hrow hx
  have hratio : f (clearHandleRows x * rowTarget⁻¹) = 1 :=
    padicHom_eq_one_of_abMk_sq_eq_one f hab
  have heq : f (clearHandleRows x) = f rowTarget := by
    rw [map_mul, map_inv] at hratio
    exact (mul_inv_eq_one.mp hratio)
  rw [heq, rowTarget_apply]

#print axioms exists_rowCorrectedLift

private lemma quotient_discreteTopology
    (M : OpenNormalSubgroup (DM 2 1)) :
    DiscreteTopology (((DM 2 1 : Type) ⧸ M.toSubgroup)) := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  rw [← (QuotientGroup.isQuotientMap_mk M.toSubgroup).isOpen_preimage]
  have hpre : QuotientGroup.mk ⁻¹'
      ({1} : Set (((DM 2 1 : Type) ⧸ M.toSubgroup))) =
      (M.toSubgroup : Set (DM 2 1)) := by
    ext x
    exact QuotientGroup.eq_one_iff x
  rw [hpre]
  exact M.isOpen'

private theorem quotientMap_factor_forget
    (M : OpenNormalSubgroup (DM 2 1)) (hM : M.toSubgroup.index = 2)
    (hU : U ∈ M.toSubgroup) (hV : V ∈ M.toSubgroup) :
    ∃ q0 : ContinuousMonoidHom (DM 2 0) (((DM 2 1 : Type) ⧸ M.toSubgroup)),
      (⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩ :
        ContinuousMonoidHom (DM 2 1) (((DM 2 1 : Type) ⧸ M.toSubgroup))) =
        q0.comp (dmForgetHandles 2 1) := by
  letI := quotient_discreteTopology M
  letI : Finite (((DM 2 1 : Type) ⧸ M.toSubgroup)) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card (((DM 2 1 : Type) ⧸ M.toSubgroup)) = 2 := by
    rwa [← Subgroup.index_eq_card]
  letI : Fact (Nat.Prime (Nat.card (((DM 2 1 : Type) ⧸ M.toSubgroup)))) :=
    ⟨by simpa [hcard] using Nat.prime_two⟩
  let q : ContinuousMonoidHom (DM 2 1) (((DM 2 1 : Type) ⧸ M.toSubgroup)) :=
    ⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩
  have hpro : IsProP 2 (((DM 2 1 : Type) ⧸ M.toSubgroup)) := by
    refine isProP_of_isPGroup (IsPGroup.of_card (n := 1) ?_)
    rw [hcard, pow_one]
  let m0 : Fin (coreRank 0) → ((DM 2 1 : Type) ⧸ M.toSubgroup) :=
    fun i => q (dmGen 2 1 (Fin.castLE (by simp [coreRank]) i))
  have hrel : mRelWord 2 m0 = 1 := by
    have hfull := congrArg q (dm_relation 2 1)
    rw [map_one, map_mRelWord] at hfull
    rw [mRelWord] at hfull ⊢
    have hhandle : handleWord
        (fun j : Fin 1 => q (dmGen 2 1 (handleIdxU j)))
        (fun j : Fin 1 => q (dmGen 2 1 (handleIdxV j))) = 1 := by
      apply handleWord_of_one
      · intro j
        fin_cases j
        exact (QuotientGroup.eq_one_iff _).mpr hU
      · intro j
        fin_cases j
        exact (QuotientGroup.eq_one_iff _).mpr hV
    rw [hhandle, mul_one] at hfull
    dsimp [m0]
    convert hfull using 1
    all_goals rfl
  let q0 := mLiftHom 2 0 hpro m0 hrel
  refine ⟨q0, ?_⟩
  change q = q0.comp (dmForgetHandles 2 1)
  apply dm_hom_ext
  intro i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · change q (dmGen 2 1 0) = q0 (dmForgetHandles 2 1 (dmGen 2 1 0))
    rw [show dmGen 2 1 0 = dmA 2 1 from rfl,
      dmForgetHandles_dmA]
    dsimp [q0]
    rw [show dmA 2 0 = dmGen 2 0 0 from rfl, mLiftHom_gen]
    rfl
  · change q (dmGen 2 1 1) = q0 (dmForgetHandles 2 1 (dmGen 2 1 1))
    rw [show dmGen 2 1 1 = dmB 2 1 from rfl,
      dmForgetHandles_dmB]
    dsimp [q0]
    rw [show dmB 2 0 = dmGen 2 0 1 from rfl, mLiftHom_gen]
    rfl
  · change q (dmGen 2 1 2) = q0 (dmForgetHandles 2 1 (dmGen 2 1 2))
    rw [show dmGen 2 1 2 = dmC 2 1 from rfl,
      dmForgetHandles_dmC]
    dsimp [q0]
    rw [show dmC 2 0 = dmGen 2 0 2 from rfl, mLiftHom_gen]
    rfl
  · change q (dmGen 2 1 3) = q0 (dmForgetHandles 2 1 (dmGen 2 1 3))
    rw [show dmGen 2 1 3 = dmD 2 1 from rfl,
      dmForgetHandles_dmD]
    dsimp [q0]
    rw [show dmD 2 0 = dmGen 2 0 3 from rfl, mLiftHom_gen]
    rfl
  · rcases mHandleCoord_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · fin_cases k
      change q U = q0 (dmForgetHandles 2 1 U)
      rw [dmForgetHandles_handleU, map_one]
      change QuotientGroup.mk' M.toSubgroup U = 1
      exact (QuotientGroup.eq_one_iff _).mpr hU
    · fin_cases k
      change q V = q0 (dmForgetHandles 2 1 V)
      rw [dmForgetHandles_handleV, map_one]
      change QuotientGroup.mk' M.toSubgroup V = 1
      exact (QuotientGroup.eq_one_iff _).mpr hV

/-- Four lifts of a compact automorphic basis, together with the standard handle pair, remain
mod-two independent. -/
theorem oneHandleModTwoIndep_of_fibers
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    {a b c d : DM 2 1}
    (ha : dmForgetHandles 2 1 a = Psi0 (dmA 2 0))
    (hb : dmForgetHandles 2 1 b = Psi0 (dmB 2 0))
    (hc : dmForgetHandles 2 1 c = Psi0 (dmC 2 0))
    (hd : dmForgetHandles 2 1 d = Psi0 (dmD 2 0)) :
    OneHandleModTwoIndep (standardHandleMark a b c d) := by
  intro M hM
  by_contra hall
  push Not at hall
  have hU : U ∈ M.toSubgroup := by
    simpa [U] using hall (handleIdxU (0 : Fin 1))
  have hV : V ∈ M.toSubgroup := by
    simpa [V] using hall (handleIdxV (0 : Fin 1))
  obtain ⟨q0, hfac⟩ := quotientMap_factor_forget M hM hU hV
  let q : ContinuousMonoidHom (DM 2 1) (((DM 2 1 : Type) ⧸ M.toSubgroup)) :=
    ⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩
  change q = q0.comp (dmForgetHandles 2 1) at hfac
  have hqa : q a = 1 := by
    change QuotientGroup.mk' M.toSubgroup a = 1
    exact (QuotientGroup.eq_one_iff _).mpr (by simpa using hall (0 : Fin (coreRank 1)))
  have hqb : q b = 1 := by
    change QuotientGroup.mk' M.toSubgroup b = 1
    exact (QuotientGroup.eq_one_iff _).mpr (by simpa using hall (1 : Fin (coreRank 1)))
  have hqc : q c = 1 := by
    change QuotientGroup.mk' M.toSubgroup c = 1
    exact (QuotientGroup.eq_one_iff _).mpr (by simpa using hall (2 : Fin (coreRank 1)))
  have hqd : q d = 1 := by
    change QuotientGroup.mk' M.toSubgroup d = 1
    exact (QuotientGroup.eq_one_iff _).mpr (by simpa using hall (3 : Fin (coreRank 1)))
  let psiHom : ContinuousMonoidHom (DM 2 0) (DM 2 0) :=
    ⟨Psi0.toMulEquiv.toMonoidHom, Psi0.continuous_toFun⟩
  have hcomp : q0.comp psiHom = 1 := by
    apply dm_hom_ext
    intro i
    fin_cases i
    · change q0 (Psi0 (dmA 2 0)) = 1
      calc
        q0 (Psi0 (dmA 2 0)) = q0 (dmForgetHandles 2 1 a) := congrArg q0 ha.symm
        _ = q a := (DFunLike.congr_fun hfac a).symm
        _ = 1 := hqa
    · change q0 (Psi0 (dmB 2 0)) = 1
      calc
        q0 (Psi0 (dmB 2 0)) = q0 (dmForgetHandles 2 1 b) := congrArg q0 hb.symm
        _ = q b := (DFunLike.congr_fun hfac b).symm
        _ = 1 := hqb
    · change q0 (Psi0 (dmC 2 0)) = 1
      calc
        q0 (Psi0 (dmC 2 0)) = q0 (dmForgetHandles 2 1 c) := congrArg q0 hc.symm
        _ = q c := (DFunLike.congr_fun hfac c).symm
        _ = 1 := hqc
    · change q0 (Psi0 (dmD 2 0)) = 1
      calc
        q0 (Psi0 (dmD 2 0)) = q0 (dmForgetHandles 2 1 d) := congrArg q0 hd.symm
        _ = q d := (DFunLike.congr_fun hfac d).symm
        _ = 1 := hqd
  have hq0 : q0 = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := Psi0.surjective x
    exact DFunLike.congr_fun hcomp y
  have hq : q = 1 := by
    rw [hfac, hq0]
    rfl
  have htop : M.toSubgroup = ⊤ := by
    refine (Subgroup.eq_top_iff' M.toSubgroup).mpr ?_
    intro x
    apply (QuotientGroup.eq_one_iff x).mp
    change q x = 1
    rw [hq]
    rfl
  have hone : M.toSubgroup.index = 1 := Subgroup.index_eq_one.mpr htop
  omega

#print axioms oneHandleModTwoIndep_of_fibers

/-- A compact automorphism with the universal pivot row has a one-handle balanced seed:
all forgetful-fibre, row, and Frattini conditions hold before imposing the finite relator
defect condition. -/
theorem exists_oneHandleBalancedSeed
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0))) :
    ∃ p : OneHandleBalancedPoint,
      dmForgetHandles 2 1 (balancedA p) = Psi0 (dmA 2 0) ∧
      dmForgetHandles 2 1 (balancedB p) = Psi0 (dmB 2 0) ∧
      dmForgetHandles 2 1 (balancedC p) = Psi0 (dmC 2 0) ∧
      dmForgetHandles 2 1 (balancedD p) = Psi0 (dmD 2 0) ∧
      dmForgetHandles 2 1 (balancedZ p) = 1 ∧
      OneHandleModTwoIndep (balancedCorrectedMark p) ∧
      ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
        toAdd (f (balancedC p)) =
          toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1)) := by
  obtain ⟨a, ha⟩ := dmForgetHandles_surjective 2 1 (Psi0 (dmA 2 0))
  obtain ⟨b, hb⟩ := dmForgetHandles_surjective 2 1 (Psi0 (dmB 2 0))
  obtain ⟨c, hc, hcrow⟩ := exists_rowCorrectedLift Psi0 hrow
  obtain ⟨d, hd⟩ := dmForgetHandles_surjective 2 1 (Psi0 (dmD 2 0))
  let p : OneHandleBalancedPoint := (a, b, c, d, 1)
  refine ⟨p, ha, hb, hc, hd, map_one _, ?_, hcrow⟩
  change OneHandleModTwoIndep (standardHandleMark a b c (1 * d))
  simpa using oneHandleModTwoIndep_of_fibers Psi0 ha hb hc hd

#print axioms exists_oneHandleBalancedSeed

end
end GQ2.Dyadic.Instances.MpcBalancedRowLift
