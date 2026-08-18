/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactSupply
import GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleRange

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenPivotLift

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcMk
open GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedNeutralityTorsionRow
open GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleRange
open GQ2.Dyadic.Instances.MpcFixedCRelativeBracketObstruction
open GQ2.Roe.Labute
open scoped GQ2.SectionThree.TopAbInstances

private abbrev H := DM 2 1
private abbrev U : H := dmGen 2 1 (handleIdxU (0 : Fin 1))
private abbrev V : H := dmGen 2 1 (handleIdxV (0 : Fin 1))

private def bHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative ℤ_[2]) :=
  (mBHom 2 h).comp (mAbMkHom 2 h)

private def cHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative ℤ_[2]) :=
  (mCHom (by omega : 1 ≤ 2) h).comp (mAbMkHom 2 h)

private def dHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative ℤ_[2]) :=
  (mDHom 2 h).comp (mAbMkHom 2 h)

private theorem coordinateHom_forget
    {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A]
    (f1 : ContinuousMonoidHom H A)
    (f0 : ContinuousMonoidHom (DM 2 0) A)
    (hA : f1 (dmA 2 1) = f0 (dmA 2 0))
    (hB : f1 (dmB 2 1) = f0 (dmB 2 0))
    (hC : f1 (dmC 2 1) = f0 (dmC 2 0))
    (hD : f1 (dmD 2 1) = f0 (dmD 2 0))
    (hU : f1 U = 1) (hV : f1 V = 1) (x : H) :
    f1 x = f0 (dmForgetHandles 2 1 x) := by
  have heq : f1 = f0.comp (dmForgetHandles 2 1) := by
    apply dm_hom_ext
    intro i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · change f1 (dmA 2 1) = f0 (dmForgetHandles 2 1 (dmA 2 1))
      simpa only [dmForgetHandles_dmA] using hA
    · change f1 (dmB 2 1) = f0 (dmForgetHandles 2 1 (dmB 2 1))
      simpa only [dmForgetHandles_dmB] using hB
    · change f1 (dmC 2 1) = f0 (dmForgetHandles 2 1 (dmC 2 1))
      simpa only [dmForgetHandles_dmC] using hC
    · change f1 (dmD 2 1) = f0 (dmForgetHandles 2 1 (dmD 2 1))
      simpa only [dmForgetHandles_dmD] using hD
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · fin_cases j
        change f1 U = f0 (dmForgetHandles 2 1 U)
        simpa only [dmForgetHandles_handleU, map_one] using hU
      · fin_cases j
        change f1 V = f0 (dmForgetHandles 2 1 V)
        simpa only [dmForgetHandles_handleV, map_one] using hV
  exact DFunLike.congr_fun heq x

private def clearHandleRows (x : H) : H :=
  zpowZtwo (isProP_DM 2 1) U (-toAdd (oneHandleHandleUHom x)) *
    zpowZtwo (isProP_DM 2 1) V (-toAdd (oneHandleHandleVHom x)) * x

private theorem clearHandleRows_forget (x : H) :
    dmForgetHandles 2 1 (clearHandleRows x) = dmForgetHandles 2 1 x := by
  rw [clearHandleRows, map_mul, map_mul,
    map_zpowZtwo (isProP_DM 2 1) (isProP_DM 2 0),
    map_zpowZtwo (isProP_DM 2 1) (isProP_DM 2 0),
    dmForgetHandles_handleU, dmForgetHandles_handleV,
    zpowZtwo_one_base, zpowZtwo_one_base, one_mul, one_mul]

private theorem clearHandleRows_U (x : H) :
    oneHandleHandleUHom (clearHandleRows x) = 1 := by
  apply toAdd.injective
  rw [clearHandleRows, map_mul oneHandleHandleUHom,
    map_mul oneHandleHandleUHom]
  change toAdd (oneHandleHandleUHom
      (zpowZtwo (isProP_DM 2 1) U (-toAdd (oneHandleHandleUHom x))) *
    oneHandleHandleUHom
      (zpowZtwo (isProP_DM 2 1) V (-toAdd (oneHandleHandleVHom x))) *
    oneHandleHandleUHom x) = 0
  rw [toAdd_mul, toAdd_mul,
    toAdd_map_zpowZtwo (isProP_DM 2 1),
    toAdd_map_zpowZtwo (isProP_DM 2 1),
    oneHandleHandleUHom_U, oneHandleHandleUHom_V]
  simp

private theorem clearHandleRows_V (x : H) :
    oneHandleHandleVHom (clearHandleRows x) = 1 := by
  apply toAdd.injective
  rw [clearHandleRows, map_mul oneHandleHandleVHom,
    map_mul oneHandleHandleVHom]
  change toAdd (oneHandleHandleVHom
      (zpowZtwo (isProP_DM 2 1) U (-toAdd (oneHandleHandleUHom x))) *
    oneHandleHandleVHom
      (zpowZtwo (isProP_DM 2 1) V (-toAdd (oneHandleHandleVHom x))) *
    oneHandleHandleVHom x) = 0
  rw [toAdd_mul, toAdd_mul,
    toAdd_map_zpowZtwo (isProP_DM 2 1),
    toAdd_map_zpowZtwo (isProP_DM 2 1),
    oneHandleHandleVHom_U, oneHandleHandleVHom_V]
  simp

private theorem zpowZtwo_sixteen_mul_mem_five
    (g : H) (a : ℤ_[2]) :
    zpowZtwo (isProP_DM 2 1) g ((2 : ℤ_[2]) ^ 4 * a) ∈
      twoCentralSeries H 5 := by
  have hcast : (((2 ^ 4 : ℕ) : ℤ_[2])) = (2 : ℤ_[2]) ^ 4 := by
    norm_num
  have heq : zpowZtwo (isProP_DM 2 1) g ((2 : ℤ_[2]) ^ 4 * a) =
      zpowZtwo (isProP_DM 2 1) g a ^ (2 ^ 4) := by
    rw [← zpowZtwo_natCast (isProP_DM 2 1)
      (zpowZtwo (isProP_DM 2 1) g a) (2 ^ 4),
      zpowZtwo_zpowZtwo, hcast]
    congr 1
    ring
  rw [heq]
  exact pow_two_pow_mem_twoCentralSeries_succ (G := H) _ 4

private theorem handleU_mod_four_eq_one {x : H}
    (hx : x ∈ twoCentralSeries H 5) : oneHandleUMod 4 x = 1 := by
  have hxq : levelMk H 5 x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
  change oneHandleULevel 4 (levelMk H 5 x) = 1
  rw [hxq, map_one]

private theorem handleV_mod_four_eq_one {x : H}
    (hx : x ∈ twoCentralSeries H 5) : oneHandleVMod 4 x = 1 := by
  have hxq : levelMk H 5 x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
  change oneHandleVLevel 4 (levelMk H 5 x) = 1
  rw [hxq, map_one]

private theorem clearHandleRows_mem_five {x : H}
    (hx : x ∈ twoCentralSeries H 5) :
    clearHandleRows x ∈ twoCentralSeries H 5 := by
  have hU := handleU_mod_four_eq_one hx
  have hV := handleV_mod_four_eq_one hx
  have hUzero : PadicInt.toZModPow 4 (toAdd (oneHandleHandleUHom x)) = 0 := by
    change ofAdd (PadicInt.toZModPow 4
      (toAdd (oneHandleHandleUHom x))) = 1 at hU
    exact congrArg Multiplicative.toAdd hU
  have hVzero : PadicInt.toZModPow 4 (toAdd (oneHandleHandleVHom x)) = 0 := by
    change ofAdd (PadicInt.toZModPow 4
      (toAdd (oneHandleHandleVHom x))) = 1 at hV
    exact congrArg Multiplicative.toAdd hV
  obtain ⟨a, ha⟩ := MarkedPair.exists_eq_two_pow_mul hUzero
  obtain ⟨b, hb⟩ := MarkedPair.exists_eq_two_pow_mul hVzero
  apply Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) hx
  · rw [ha]
    simpa only [mul_neg] using zpowZtwo_sixteen_mul_mem_five U (-a)
  · rw [hb]
    simpa only [mul_neg] using zpowZtwo_sixteen_mul_mem_five V (-b)

private theorem coreHom_clearHandleRows (f : ContinuousMonoidHom H (Multiplicative ℤ_[2]))
    (hU : f U = 1) (hV : f V = 1) (x : H) :
    f (clearHandleRows x) = f x := by
  rw [clearHandleRows, map_mul, map_mul,
    map_zpowZtwo (isProP_DM 2 1) PropOneOne.isProP_two_multPadicInt,
    map_zpowZtwo (isProP_DM 2 1) PropOneOne.isProP_two_multPadicInt,
    hU, hV, zpowZtwo_one_base, zpowZtwo_one_base, one_mul, one_mul]

private theorem bHom_forget (x : H) :
    bHom 1 x = bHom 0 (dmForgetHandles 2 1 x) := by
  apply coordinateHom_forget
  all_goals simp [bHom, mBHom, dmA, dmB, dmC, dmD, U, V, mCoordHom_gen]

private theorem cHom_forget (x : H) :
    cHom 1 x = cHom 0 (dmForgetHandles 2 1 x) := by
  apply coordinateHom_forget
  all_goals simp [cHom, mCHom, dmA, dmB, dmC, dmD, U, V, mCoordHom_gen]

private theorem dHom_forget (x : H) :
    dHom 1 x = dHom 0 (dmForgetHandles 2 1 x) := by
  apply coordinateHom_forget
  all_goals simp [dHom, mDHom, dmA, dmB, dmC, dmD, U, V, mCoordHom_gen]

private theorem clearHandleRows_rowKer {x : DM 2 0} {y : H}
    (hx : x ∈ mpcMkDerived) (hy : dmForgetHandles 2 1 y = x) :
    clearHandleRows y ∈ oneHandleRowKer := by
  rw [mem_oneHandleRowKer_iff_abMk_sq_eq_one]
  apply mPhiHom_injective (by omega : 1 ≤ 2) 1
  rw [map_pow, map_one]
  change ofAdd
    ((mTHom 2 1 (GQ2.SectionThree.abMk (clearHandleRows y))).toAdd,
      (mBHom 2 1 (GQ2.SectionThree.abMk (clearHandleRows y))).toAdd,
      (mCHom (by omega : 1 ≤ 2) 1
        (GQ2.SectionThree.abMk (clearHandleRows y))).toAdd,
      (mDHom 2 1 (GQ2.SectionThree.abMk (clearHandleRows y))).toAdd,
      fun k => (mHHom 2 k
        (GQ2.SectionThree.abMk (clearHandleRows y))).toAdd) ^ 2 = 1
  rw [← ofAdd_nsmul]
  apply congrArg ofAdd
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · change (2 : ℕ) • (mTHom 2 1
        (GQ2.SectionThree.abMk (clearHandleRows y))).toAdd = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _
  · change (2 : ℕ) • toAdd (bHom 1 (clearHandleRows y)) = 0
    have hrow := (mpcWord_mem_rowKer.mp (mpcMk_derived_rowKer hx)) (bHom 0)
    have hcore : bHom 1 (clearHandleRows y) = bHom 1 y := by
      apply coreHom_clearHandleRows
      all_goals simp [bHom, U, V, mBHom, mCoordHom_gen]
    rw [hcore, bHom_forget, hy, hrow, toAdd_one, smul_zero]
  · change (2 : ℕ) • toAdd (cHom 1 (clearHandleRows y)) = 0
    have hrow := (mpcWord_mem_rowKer.mp (mpcMk_derived_rowKer hx)) (cHom 0)
    have hcore : cHom 1 (clearHandleRows y) = cHom 1 y := by
      apply coreHom_clearHandleRows
      all_goals simp [cHom, U, V, mCHom, mCoordHom_gen]
    rw [hcore, cHom_forget, hy, hrow, toAdd_one, smul_zero]
  · change (2 : ℕ) • toAdd (dHom 1 (clearHandleRows y)) = 0
    have hrow := (mpcWord_mem_rowKer.mp (mpcMk_derived_rowKer hx)) (dHom 0)
    have hcore : dHom 1 (clearHandleRows y) = dHom 1 y := by
      apply coreHom_clearHandleRows
      all_goals simp [dHom, U, V, mDHom, mCoordHom_gen]
    rw [hcore, dHom_forget, hy, hrow, toAdd_one, smul_zero]
  · funext k
    rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · fin_cases j
      change (2 : ℕ) • toAdd
        (oneHandleHandleUHom (clearHandleRows y)) = 0
      rw [clearHandleRows_U, toAdd_one, smul_zero]
    · fin_cases j
      change (2 : ℕ) • toAdd
        (oneHandleHandleVHom (clearHandleRows y)) = 0
      rw [clearHandleRows_V, toAdd_one, smul_zero]

theorem exists_oneHandlePivotLift {x : DM 2 0}
    (hx : x ∈ mpcMkPivotKill 5) :
    ∃ y : H, y ∈ twoCentralSeries H 5 ∧ chiM 2 1 y = 1 ∧
      (∀ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
        toAdd (f y) = 0) ∧ dmForgetHandles 2 1 y = x := by
  have hmap :
      (twoCentralSeries H 5).map (dmForgetHandles 2 1).toMonoidHom =
        twoCentralSeries (DM 2 0 : Type) 5 :=
    map_twoCentralSeries_eq (dmForgetHandles 2 1).toMonoidHom
      (dmForgetHandles 2 1).continuous_toFun
      (dmForgetHandles_surjective 2 1) 5
  have hxmap : x ∈
      (twoCentralSeries H 5).map (dmForgetHandles 2 1).toMonoidHom := by
    rw [hmap]
    exact hx.2
  obtain ⟨z, hz, hzx⟩ := hxmap
  change dmForgetHandles 2 1 z = x at hzx
  let y := clearHandleRows z
  have hydepth : y ∈ twoCentralSeries H 5 := clearHandleRows_mem_five hz
  have hyforget : dmForgetHandles 2 1 y = x :=
    (clearHandleRows_forget z).trans hzx
  have hyrow : y ∈ oneHandleRowKer := clearHandleRows_rowKer hx.1 hzx
  refine ⟨y, hydepth, ?_, ?_, hyforget⟩
  · rw [← chiM_dmForgetHandles 2 1, hyforget]
    exact mpcMk_derived_chi hx.1
  · intro f
    exact congrArg toAdd ((mem_oneHandleRowKer_iff.mp hyrow) f)

#print axioms exists_oneHandlePivotLift


