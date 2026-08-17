/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralityTorsionRow
import GQ2.Dyadic.Instances.MpcBalancedNeutralitySourceQuotient
import GQ2.Dyadic.Instances.MpcFixedCRelativeBracketObstruction

/-!
# Finite handle coordinates of the neutral relative source

W222 identifies exact row-neutrality in the handle-forgetting kernel with trivial full
abelianization.  This module turns that structural statement into two finite coordinates.
The first `U`- and `V`-handle rows descend modulo `2^k` to the `(k+1)`-st two-central
quotient.  On the ordinary relative source, their common kernel is exactly the image of the
neutral relative source.

Consequently the source modulo neutral representatives is canonically isomorphic to the
intrinsic range of the two handle digits.  This is deliberately a two-stage calculation: no
cardinality or identification of that range with an ambient product is asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleRange

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleDefectObstruction
open GQ2.Dyadic.Instances.MpcFixedCRelativeBracketObstruction
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedNeutralityTorsionRow
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySourceQuotient
open GQ2.Roe.Labute
open scoped GQ2.SectionThree.TopAbInstances

private abbrev U : DM 2 1 := dmGen 2 1 (handleIdxU (0 : Fin 1))
private abbrev V : DM 2 1 := dmGen 2 1 (handleIdxV (0 : Fin 1))

/-- Reduction of the first `V`-handle coordinate modulo `2^k`. -/
def oneHandleVMod (k : ℕ) :
    ContinuousMonoidHom (DM 2 1) (Multiplicative (ZMod (2 ^ k))) where
  toMonoidHom :=
    (AddMonoidHom.toMultiplicative
      (PadicInt.toZModPow (p := 2) k).toAddMonoidHom).comp
        oneHandleHandleVHom.toMonoidHom
  continuous_toFun := by
    have hred : Continuous (PadicInt.toZModPow (p := 2) k) := by
      rw [continuous_def]
      intro T _
      exact isOpen_preimage_toZModPow k T
    exact continuous_ofAdd.comp
      (hred.comp (continuous_toAdd.comp oneHandleHandleVHom.continuous_toFun))

@[simp] theorem oneHandleVMod_handleV (k : ℕ) :
    oneHandleVMod k V = ofAdd (1 : ZMod (2 ^ k)) := by
  change ofAdd (PadicInt.toZModPow k
    (toAdd (oneHandleHandleVHom V))) = _
  change ofAdd (PadicInt.toZModPow k
    (toAdd (mHHom 2 (mHandleCoordV (0 : Fin 1))
      (GQ2.SectionThree.abMk V)))) = _
  rw [mHHom, mCoordHom_gen, ← mHandleIdx_coordV, mHandleMark_self,
    toAdd_ofAdd, map_one]

private theorem oneHandleVMod_pow_exp (k : ℕ)
    (x : Multiplicative (ZMod (2 ^ k))) : x ^ 2 ^ k = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod (2 ^ k), ofAdd a = x := ⟨toAdd x, rfl⟩
  rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

/-- The first `V`-handle digit on the `(k+1)`-st two-central quotient. -/
def oneHandleVLevel (k : ℕ) :
    levelQuot (DM 2 1) (k + 1) →* Multiplicative (ZMod (2 ^ k)) :=
  QuotientGroup.lift (twoCentralSeries (DM 2 1) (k + 1))
    (oneHandleVMod k).toMonoidHom (fun g hg => by
      have him : oneHandleVMod k g ∈
          twoCentralSeries (Multiplicative (ZMod (2 ^ k))) (k + 1) :=
        map_twoCentralSeries_le (oneHandleVMod k).toMonoidHom
          (oneHandleVMod k).continuous_toFun (k + 1) ⟨g, hg, rfl⟩
      obtain ⟨x, hx⟩ := evenStratumShift_twoCentralSeries_le_pow k him
      rw [MonoidHom.mem_ker]
      change oneHandleVMod k g = 1
      rw [← hx]
      exact oneHandleVMod_pow_exp k x)

@[simp] theorem oneHandleVLevel_levelMk (k : ℕ) (g : DM 2 1) :
    oneHandleVLevel k (levelMk (DM 2 1) (k + 1) g) = oneHandleVMod k g :=
  rfl

/-- The pair of finite handle digits. -/
def oneHandleUVLevel (k : ℕ) :
    levelQuot (DM 2 1) (k + 1) →*
      Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod (2 ^ k)) :=
  (oneHandleULevel k).prod (oneHandleVLevel k)

/-- The handle-digit pair restricted to the ordinary relative source. -/
def oneHandleRelativeUVLevel (k : ℕ) :
    oneHandleRelativeLambdaImage (k - 1) (k + 1) →*
      Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod (2 ^ k)) :=
  (oneHandleUVLevel k).comp
    (oneHandleRelativeLambdaImage (k - 1) (k + 1)).subtype

private theorem coordinateHom_forget
    {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A]
    (f1 : ContinuousMonoidHom (DM 2 1) A)
    (f0 : ContinuousMonoidHom (DM 2 0) A)
    (hA : f1 (dmA 2 1) = f0 (dmA 2 0))
    (hB : f1 (dmB 2 1) = f0 (dmB 2 0))
    (hC : f1 (dmC 2 1) = f0 (dmC 2 0))
    (hD : f1 (dmD 2 1) = f0 (dmD 2 0))
    (hU : f1 U = 1) (hV : f1 V = 1) (x : DM 2 1) :
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

private def torsionHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative (ZMod 2)) :=
  (mTHom 2 h).comp (mAbMkHom 2 h)

private def bHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative ℤ_[2]) :=
  (mBHom 2 h).comp (mAbMkHom 2 h)

private def cHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative ℤ_[2]) :=
  (mCHom (by omega : 1 ≤ 2) h).comp (mAbMkHom 2 h)

private def dHom (h : ℕ) :
    ContinuousMonoidHom (DM 2 h) (Multiplicative ℤ_[2]) :=
  (mDHom 2 h).comp (mAbMkHom 2 h)

private theorem torsionHom_forget (x : DM 2 1) :
    torsionHom 1 x = torsionHom 0 (dmForgetHandles 2 1 x) := by
  apply coordinateHom_forget
  all_goals simp [torsionHom, mTHom, dmA, dmB, dmC, dmD, U, V, mCoordHom_gen]

private theorem bHom_forget (x : DM 2 1) :
    bHom 1 x = bHom 0 (dmForgetHandles 2 1 x) := by
  apply coordinateHom_forget
  all_goals simp [bHom, mBHom, dmA, dmB, dmC, dmD, U, V, mCoordHom_gen]

private theorem cHom_forget (x : DM 2 1) :
    cHom 1 x = cHom 0 (dmForgetHandles 2 1 x) := by
  apply coordinateHom_forget
  all_goals simp [cHom, mCHom, dmA, dmB, dmC, dmD, U, V, mCoordHom_gen]

private theorem dHom_forget (x : DM 2 1) :
    dHom 1 x = dHom 0 (dmForgetHandles 2 1 x) := by
  apply coordinateHom_forget
  all_goals simp [dHom, mDHom, dmA, dmB, dmC, dmD, U, V, mCoordHom_gen]

@[simp] theorem oneHandleHandleUHom_U :
    toAdd (oneHandleHandleUHom U) = 1 := by
  change toAdd (mHHom 2 (mHandleCoordU (0 : Fin 1))
    (GQ2.SectionThree.abMk U)) = 1
  rw [mHHom, mCoordHom_gen, ← mHandleIdx_coordU, mHandleMark_self,
    toAdd_ofAdd]

@[simp] theorem oneHandleHandleUHom_V :
    toAdd (oneHandleHandleUHom V) = 0 := by
  change toAdd (mHHom 2 (mHandleCoordU (0 : Fin 1))
    (GQ2.SectionThree.abMk V)) = 0
  rw [mHHom, mCoordHom_gen, ← mHandleIdx_coordV, mHandleMark_of_ne]
  · rfl
  · decide

@[simp] theorem oneHandleHandleVHom_U :
    toAdd (oneHandleHandleVHom U) = 0 := by
  change toAdd (mHHom 2 (mHandleCoordV (0 : Fin 1))
    (GQ2.SectionThree.abMk U)) = 0
  rw [mHHom, mCoordHom_gen, ← mHandleIdx_coordU, mHandleMark_of_ne]
  · rfl
  · decide

@[simp] theorem oneHandleHandleVHom_V :
    toAdd (oneHandleHandleVHom V) = 1 := by
  change toAdd (mHHom 2 (mHandleCoordV (0 : Fin 1))
    (GQ2.SectionThree.abMk V)) = 1
  rw [mHHom, mCoordHom_gen, ← mHandleIdx_coordV, mHandleMark_self,
    toAdd_ofAdd]

private theorem abMk_eq_one_of_forget_of_handleRows
    {x : DM 2 1} (hforget : dmForgetHandles 2 1 x = 1)
    (hU : oneHandleHandleUHom x = 1)
    (hV : oneHandleHandleVHom x = 1) :
    GQ2.SectionThree.abMk x = 1 := by
  have ht : torsionHom 1 x = 1 := by
    rw [torsionHom_forget, hforget, map_one]
  have hb : bHom 1 x = 1 := by
    rw [bHom_forget, hforget, map_one]
  have hc : cHom 1 x = 1 := by
    rw [cHom_forget, hforget, map_one]
  have hd : dHom 1 x = 1 := by
    rw [dHom_forget, hforget, map_one]
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
  · change toAdd (torsionHom 1 x) = 0
    rw [ht, toAdd_one]
  · change toAdd (bHom 1 x) = 0
    rw [hb, toAdd_one]
  · change toAdd (cHom 1 x) = 0
    rw [hc, toAdd_one]
  · change toAdd (dHom 1 x) = 0
    rw [hd, toAdd_one]
  · funext i
    rcases mHandleCoord_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · fin_cases j
      change toAdd (oneHandleHandleUHom x) = 0
      rw [hU, toAdd_one]
    · fin_cases j
      change toAdd (oneHandleHandleVHom x) = 0
      rw [hV, toAdd_one]

private theorem zpowZtwo_two_pow_mul_mem
    (g : DM 2 1) (k : ℕ) (a : ℤ_[2]) :
    zpowZtwo (isProP_DM 2 1) g ((2 : ℤ_[2]) ^ k * a) ∈
      twoCentralSeries (DM 2 1) (k + 1) := by
  have hcast : (((2 ^ k : ℕ) : ℤ_[2])) = (2 : ℤ_[2]) ^ k := by
    push_cast
    ring
  have heq : zpowZtwo (isProP_DM 2 1) g ((2 : ℤ_[2]) ^ k * a) =
      zpowZtwo (isProP_DM 2 1) g a ^ (2 ^ k) := by
    rw [← zpowZtwo_natCast (isProP_DM 2 1)
      (zpowZtwo (isProP_DM 2 1) g a) (2 ^ k),
      zpowZtwo_zpowZtwo, hcast]
    congr 1
    ring
  rw [heq]
  exact pow_two_pow_mem_twoCentralSeries_succ (G := (DM 2 1 : Type)) _ k

private def clearHandleRows (x : DM 2 1) : DM 2 1 :=
  zpowZtwo (isProP_DM 2 1) U (-toAdd (oneHandleHandleUHom x)) *
    zpowZtwo (isProP_DM 2 1) V (-toAdd (oneHandleHandleVHom x)) * x

private theorem dmForgetHandles_clearHandleRows (x : DM 2 1) :
    dmForgetHandles 2 1 (clearHandleRows x) = dmForgetHandles 2 1 x := by
  rw [clearHandleRows, map_mul, map_mul,
    map_zpowZtwo (isProP_DM 2 1) (isProP_DM 2 0),
    map_zpowZtwo (isProP_DM 2 1) (isProP_DM 2 0),
    dmForgetHandles_handleU, dmForgetHandles_handleV,
    zpowZtwo_one_base, zpowZtwo_one_base, one_mul, one_mul]

private theorem oneHandleHandleUHom_clearHandleRows (x : DM 2 1) :
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

private theorem oneHandleHandleVHom_clearHandleRows (x : DM 2 1) :
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

private theorem oneHandleUChar_eq_handleUHom :
    oneHandleUChar = oneHandleHandleUHom := rfl

private theorem clearHandleRows_same_level
    {k : ℕ} {x : DM 2 1}
    (hU : oneHandleUMod k x = 1)
    (hV : oneHandleVMod k x = 1) :
    levelMk (DM 2 1) (k + 1) (clearHandleRows x) =
      levelMk (DM 2 1) (k + 1) x := by
  have hUzero : PadicInt.toZModPow k (toAdd (oneHandleHandleUHom x)) = 0 := by
    change ofAdd (PadicInt.toZModPow k
      (toAdd (oneHandleHandleUHom x))) = 1 at hU
    exact congrArg Multiplicative.toAdd hU
  have hVzero : PadicInt.toZModPow k (toAdd (oneHandleHandleVHom x)) = 0 := by
    change ofAdd (PadicInt.toZModPow k
      (toAdd (oneHandleHandleVHom x))) = 1 at hV
    exact congrArg Multiplicative.toAdd hV
  obtain ⟨a, ha⟩ := MarkedPair.exists_eq_two_pow_mul hUzero
  obtain ⟨b, hb⟩ := MarkedPair.exists_eq_two_pow_mul hVzero
  have hUa : zpowZtwo (isProP_DM 2 1) U
      (-toAdd (oneHandleHandleUHom x)) ∈
      twoCentralSeries (DM 2 1) (k + 1) := by
    rw [ha]
    simpa only [mul_neg] using zpowZtwo_two_pow_mul_mem U k (-a)
  have hVb : zpowZtwo (isProP_DM 2 1) V
      (-toAdd (oneHandleHandleVHom x)) ∈
      twoCentralSeries (DM 2 1) (k + 1) := by
    rw [hb]
    simpa only [mul_neg] using zpowZtwo_two_pow_mul_mem V k (-b)
  have hUa_one : levelMk (DM 2 1) (k + 1)
      (zpowZtwo (isProP_DM 2 1) U
        (-toAdd (oneHandleHandleUHom x))) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hUa
  have hVb_one : levelMk (DM 2 1) (k + 1)
      (zpowZtwo (isProP_DM 2 1) V
        (-toAdd (oneHandleHandleVHom x))) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hVb
  rw [clearHandleRows, map_mul, map_mul, hUa_one, hVb_one,
    one_mul, one_mul]

private theorem neutralRelativeInclusion_mem_uvLevel_ker
    {k : ℕ} (x : oneHandleNeutralRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleNeutralRelativeInclusion (k - 1) (k + 1) (by omega) x ∈
      (oneHandleRelativeUVLevel k).ker := by
  obtain ⟨e, he, hforget, hrow, hex⟩ :=
    (mem_oneHandleNeutralRelativeLambdaImage_iff_exists_exact x.1).mp x.2
  rw [MonoidHom.mem_ker]
  change oneHandleUVLevel k x.1 = 1
  rw [← hex]
  apply Prod.ext
  · change oneHandleUMod k e = 1
    change ofAdd (PadicInt.toZModPow k
      (toAdd (oneHandleHandleUHom e))) = 1
    rw [hrow oneHandleHandleUHom, map_zero]
    rfl
  · change oneHandleVMod k e = 1
    change ofAdd (PadicInt.toZModPow k
      (toAdd (oneHandleHandleVHom e))) = 1
    rw [hrow oneHandleHandleVHom, map_zero]
    rfl

/-- On the ordinary relative source, the two finite handle digits vanish exactly on the
classes admitting a genuinely row-neutral representative. -/
theorem oneHandleRelativeUVLevel_ker_eq_neutralRange
    (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleRelativeUVLevel k).ker =
      (oneHandleNeutralRelativeInclusion
        (k - 1) (k + 1) (by omega)).range := by
  ext x
  constructor
  · intro hx
    obtain ⟨e, he, hforget, hex⟩ :=
      (mem_oneHandleRelativeLambdaImage_iff_exists_exact
        (by omega : k - 1 ≤ k + 1) x.1).mp x.2
    have hpair := MonoidHom.mem_ker.mp hx
    change oneHandleUVLevel k x.1 = 1 at hpair
    rw [← hex] at hpair
    have hU : oneHandleUMod k e = 1 := by
      have h := congrArg Prod.fst hpair
      exact h
    have hV : oneHandleVMod k e = 1 := by
      have h := congrArg Prod.snd hpair
      exact h
    let e' := clearHandleRows e
    have hsame : levelMk (DM 2 1) (k + 1) e' =
        levelMk (DM 2 1) (k + 1) e :=
      clearHandleRows_same_level hU hV
    have hdiff : e' * e⁻¹ ∈ twoCentralSeries (DM 2 1) (k + 1) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change levelMk (DM 2 1) (k + 1) (e' * e⁻¹) = 1
      rw [map_mul, map_inv, hsame, mul_inv_cancel]
    have he' : e' ∈ twoCentralSeries (DM 2 1) (k - 1) := by
      rw [show e' = (e' * e⁻¹) * e by group]
      exact Subgroup.mul_mem _
        (twoCentralSeries_antitone (DM 2 1) (by omega) hdiff) he
    have hforget' : dmForgetHandles 2 1 e' = 1 := by
      rw [dmForgetHandles_clearHandleRows, hforget]
    have hab : GQ2.SectionThree.abMk e' = 1 :=
      abMk_eq_one_of_forget_of_handleRows hforget'
        (oneHandleHandleUHom_clearHandleRows e)
        (oneHandleHandleVHom_clearHandleRows e)
    have hrow' : e' ∈ oneHandleRowKer :=
      (mem_oneHandleRowKer_iff_abMk_eq_one_of_forget hforget').mpr hab
    let y : oneHandleNeutralRelativeLambdaImage (k - 1) (k + 1) :=
      ⟨levelMk (DM 2 1) (k + 1) e', by
        refine (mem_oneHandleNeutralRelativeLambdaImage_iff_exists_exact _).mpr
          ⟨e', he', hforget', ?_, rfl⟩
        intro f
        have hf := (mem_oneHandleRowKer_iff.mp hrow') f
        rw [hf, toAdd_one]⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hsame.trans hex
  · rintro ⟨y, rfl⟩
    exact neutralRelativeInclusion_mem_uvLevel_ker y

/-- The relative source modulo exact neutral representatives is the intrinsic range of its
two finite handle digits.  This is the coordinate-free first stage of the finite quotient
calculation; no claim about the size of that range is folded into this equivalence. -/
noncomputable def oneHandleRelativeCModuloNeutralEquivUVRange
    (k : ℕ) (hk : 3 ≤ k) :
    OneHandleRelativeCModuloNeutral k hk ≃*
      (oneHandleRelativeUVLevel k).range := by
  letI := oneHandleRelativeLambdaImageIsMulCommutative k hk
  exact (QuotientGroup.quotientMulEquivOfEq
    (oneHandleRelativeUVLevel_ker_eq_neutralRange k hk).symm).trans
      (QuotientGroup.quotientKerEquivRange (oneHandleRelativeUVLevel k))

#print axioms oneHandleVMod
#print axioms oneHandleVLevel
#print axioms oneHandleUVLevel
#print axioms oneHandleRelativeUVLevel
#print axioms oneHandleHandleUHom_U
#print axioms oneHandleHandleUHom_V
#print axioms oneHandleHandleVHom_U
#print axioms oneHandleHandleVHom_V
#print axioms oneHandleRelativeUVLevel_ker_eq_neutralRange
#print axioms oneHandleRelativeCModuloNeutralEquivUVRange

end

end GQ2.Dyadic.Instances.MpcBalancedNeutralityHandleRange
