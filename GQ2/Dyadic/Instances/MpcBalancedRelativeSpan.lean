/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedFiniteSpan

/-!
# The relative codomain of the finite four-core shift

Every W208 correction class vanishes under handle-forgetting.  Naturality of the relator word
therefore forces its shift to vanish under the induced level map.  The corrected relator of a
balanced point has the same property because its forgotten marking is the compact shift
automorphism followed by two trivial handle rows.

This file corestricts the finite shift homomorphism to the relative central layer.  The exact
campaign boundary remains target membership in its range.  Surjectivity onto the relative
layer is recorded separately as a clean sufficient finite spanning statement; it is not
asserted or confused with the weaker target-specific claim.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedRelativeSpan

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedCoreShift
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedFiniteSpan
open GQ2.Roe.Labute

/-! ## Relative source and target layers -/

/-- The character-neutral relative layer is contained in the ordinary relative layer. -/
theorem oneHandleNeutralRelativeLambdaImage_le_relative
    (j n : ℕ) (hjn : j ≤ n) :
    oneHandleNeutralRelativeLambdaImage j n ≤ oneHandleRelativeLambdaImage j n := by
  intro x hx
  obtain ⟨e, he, hef, -, hex⟩ :=
    (mem_oneHandleNeutralRelativeLambdaImage_iff_exists_exact x).mp hx
  exact (mem_oneHandleRelativeLambdaImage_iff_exists_exact hjn x).mpr
    ⟨e, he, hef, hex⟩

/-- Every coordinate of the finite correction maps to one after forgetting the handle. -/
theorem oneHandleForgetLevelMap_coreLevelCorrectionMark
    {k : ℕ} (E : OneHandleBalancedCoreLevelCorrection k) :
    (fun i ↦ oneHandleForgetLevelMap (k + 1)
      (oneHandleBalancedCoreLevelCorrectionMark E i)) = fun _ ↦ 1 := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · exact MonoidHom.mem_ker.mp E.corrA.2.2
  · exact MonoidHom.mem_ker.mp E.corrB.2.2
  · exact MonoidHom.mem_ker.mp
      ((oneHandleNeutralRelativeLambdaImage_le_relative _ _ (by omega)) E.corrC.2).2
  · exact MonoidHom.mem_ker.mp E.corrD.2.2
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleBalancedCoreLevelCorrectionMark,
        mHandleIdx_coordU, mHandleIdx_coordV]

/-- The finite shift itself vanishes after forgetting the handle. -/
theorem oneHandleForgetLevelMap_coreLevelShift
    (p : OneHandleBalancedPoint) {k : ℕ}
    (E : OneHandleBalancedCoreLevelCorrection k) :
    oneHandleForgetLevelMap (k + 1)
      (oneHandleBalancedCoreLevelShift p E) = 1 := by
  rw [oneHandleBalancedCoreLevelShift, stageShift]
  change oneHandleForgetLevelMap (k + 1)
    ((mRelWord 2 (fun i ↦ levelMk (DM 2 1) (k + 1)
      (balancedCorrectedMark p i)))⁻¹ *
      mRelWord 2 (fun i ↦
        levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i) *
          oneHandleBalancedCoreLevelCorrectionMark E i)) = 1
  rw [map_mul, map_inv, map_mRelWord, map_mRelWord]
  have hsame :
      (fun i ↦ oneHandleForgetLevelMap (k + 1)
        (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i) *
          oneHandleBalancedCoreLevelCorrectionMark E i)) =
      fun i ↦ oneHandleForgetLevelMap (k + 1)
        (levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i)) := by
    funext i
    rw [map_mul]
    have hi := congrFun (oneHandleForgetLevelMap_coreLevelCorrectionMark E) i
    rw [hi, mul_one]
  rw [hsame]
  exact inv_mul_cancel _

/-- The central layer classes which also vanish after forgetting the handle. -/
def oneHandleRelativeZLayer (k : ℕ) :
    Subgroup (levelQuot (DM 2 1) (k + 1)) :=
  zLayer (DM 2 1) k ⊓ (oneHandleForgetLevelMap (k + 1)).toMonoidHom.ker

theorem oneHandleRelativeZLayer_eq_relativeLambdaImage (k : ℕ) :
    oneHandleRelativeZLayer k = oneHandleRelativeLambdaImage k (k + 1) :=
  rfl

/-! ## The relative shift homomorphism -/

/-- Corestrict the W208 shift homomorphism to the relative central layer. -/
noncomputable def oneHandleBalancedCoreRelativeShiftHom
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    OneHandleBalancedCoreLevelCorrection k →* oneHandleRelativeZLayer k where
  toFun E := ⟨(oneHandleBalancedCoreLevelShiftHom p k hk E).1,
    ⟨(oneHandleBalancedCoreLevelShiftHom p k hk E).2,
      MonoidHom.mem_ker.mpr (by
        rw [oneHandleBalancedCoreLevelShiftHom_apply]
        exact oneHandleForgetLevelMap_coreLevelShift p E)⟩⟩
  map_one' := by
    apply Subtype.ext
    change (oneHandleBalancedCoreLevelShiftHom p k hk
      (1 : OneHandleBalancedCoreLevelCorrection k)).1 = 1
    exact congrArg Subtype.val (map_one (oneHandleBalancedCoreLevelShiftHom p k hk))
  map_mul' E F := by
    apply Subtype.ext
    change (oneHandleBalancedCoreLevelShiftHom p k hk (E * F)).1 =
      (oneHandleBalancedCoreLevelShiftHom p k hk E).1 *
        (oneHandleBalancedCoreLevelShiftHom p k hk F).1
    exact congrArg Subtype.val (map_mul (oneHandleBalancedCoreLevelShiftHom p k hk) E F)

@[simp] theorem oneHandleBalancedCoreRelativeShiftHom_apply
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (E : OneHandleBalancedCoreLevelCorrection k) :
    (oneHandleBalancedCoreRelativeShiftHom p k hk E).1 =
      oneHandleBalancedCoreLevelShift p E :=
  oneHandleBalancedCoreLevelShiftHom_apply p k hk E

/-! ## The balanced target is relative -/

/-- Forgetting a balanced corrected relator gives the compact relator under `Psi0`, hence one. -/
theorem dmForgetHandles_balancedCorrectedRelator
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)} {p : OneHandleBalancedPoint}
    {k : ℕ} (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    dmForgetHandles 2 1 (mRelWord 2 (balancedCorrectedMark p)) = 1 := by
  rcases hp with ⟨ha, hb, hc, hd, hz, -, -, -⟩
  rw [map_mRelWord]
  have hmark :
      (fun i ↦ dmForgetHandles 2 1 (balancedCorrectedMark p i)) =
        fullMark (Psi0 (dmA 2 0)) (Psi0 (dmB 2 0))
          (Psi0 (dmC 2 0)) (Psi0 (dmD 2 0))
          (fun _ ↦ 1) (fun _ ↦ 1) := by
    funext i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · exact ha
    · exact hb
    · exact hc
    · simp only [balancedCorrectedMark, standardHandleMark_three, map_mul, hz, hd,
        one_mul, fullMark_three]
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
        simp [balancedCorrectedMark, mHandleIdx_coordU, mHandleIdx_coordV]
  rw [hmark, mRelWord, fullMark_zero, fullMark_one, fullMark_two,
    fullMark_three]
  simp_rw [fullMark_handleU, fullMark_handleV]
  rw [handleWord_one]
  simp only [commP, inv_one, mul_one]
  rw [← map_mWord Psi0]
  have hrel := dm_relation 2 0
  rw [mRelWord, handleWord_zero, mul_one] at hrel
  have hrel' : mWord 2 (dmA 2 0) (dmB 2 0) (dmC 2 0) (dmD 2 0) = 1 := by
    simpa [dmA, dmB, dmC, dmD] using hrel
  rw [hrel', map_one]

/-- The W208 target, corestricted to the relative central layer. -/
def oneHandleBalancedCoreRelativeTarget
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)} {k : ℕ}
    (p : OneHandleBalancedPoint) (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    oneHandleRelativeZLayer k :=
  ⟨(oneHandleBalancedCoreLevelTarget p hp).1,
    ⟨(oneHandleBalancedCoreLevelTarget p hp).2,
      MonoidHom.mem_ker.mpr (by
        change oneHandleForgetLevelMap (k + 1)
          ((levelMk (DM 2 1) (k + 1)
            (mRelWord 2 (balancedCorrectedMark p)))⁻¹) = 1
        rw [map_inv, oneHandleForgetLevelMap_levelMk,
          dmForgetHandles_balancedCorrectedRelator hp, map_one, inv_one])⟩⟩

/-- The exact W208 range condition is unchanged by corestricting to the relative layer. -/
theorem target_mem_relativeRange_iff_target_mem_range
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    oneHandleBalancedCoreRelativeTarget p hp ∈
        (oneHandleBalancedCoreRelativeShiftHom p k hk).range ↔
      oneHandleBalancedCoreLevelTarget p hp ∈
        (oneHandleBalancedCoreLevelShiftHom p k hk).range := by
  constructor
  · rintro ⟨E, hE⟩
    exact ⟨E, Subtype.ext (congrArg
      (fun x : oneHandleRelativeZLayer k ↦ x.1) hE)⟩
  · rintro ⟨E, hE⟩
    exact ⟨E, Subtype.ext (congrArg (fun x : zLayer (DM 2 1) k ↦ x.1) hE)⟩

/-- Uniform target membership in the corestricted finite range. -/
def OneHandleBalancedCoreRelativeRangeSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint)
    (hp : p ∈ oneHandleBalancedSet Psi0 k),
      oneHandleBalancedCoreRelativeTarget p hp ∈
        (oneHandleBalancedCoreRelativeShiftHom p k hk).range

theorem relativeRangeSupply_iff_rangeSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreRelativeRangeSupply Psi0 ↔
      OneHandleBalancedCoreRangeSupply Psi0 := by
  constructor <;> intro H k hk p hp
  · exact (target_mem_relativeRange_iff_target_mem_range p hk hp).mp (H k hk p hp)
  · exact (target_mem_relativeRange_iff_target_mem_range p hk hp).mpr (H k hk p hp)

/-- Surjectivity of every corestricted finite shift is a sufficient uniform spanning input. -/
def OneHandleBalancedCoreRelativeSurjectiveSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint),
    p ∈ oneHandleBalancedSet Psi0 k →
      Function.Surjective (oneHandleBalancedCoreRelativeShiftHom p k hk)

theorem relativeRangeSupply_of_surjective
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (H : OneHandleBalancedCoreRelativeSurjectiveSupply Psi0) :
    OneHandleBalancedCoreRelativeRangeSupply Psi0 := by
  intro k hk p hp
  obtain ⟨E, hE⟩ := H k hk p hp (oneHandleBalancedCoreRelativeTarget p hp)
  exact ⟨E, hE⟩

/-- Relative finite surjectivity is enough for the one-handle pivot. -/
theorem mpcPivShiftH_two_one_of_balancedRelativeSurjective
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hsurj : OneHandleBalancedCoreRelativeSurjectiveSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedCoreRange Psi0 hchi0 hrow
    ((relativeRangeSupply_iff_rangeSupply Psi0).mp
      (relativeRangeSupply_of_surjective Hsurj))

#print axioms oneHandleNeutralRelativeLambdaImage_le_relative
#print axioms oneHandleForgetLevelMap_coreLevelCorrectionMark
#print axioms oneHandleForgetLevelMap_coreLevelShift
#print axioms oneHandleRelativeZLayer
#print axioms oneHandleRelativeZLayer_eq_relativeLambdaImage
#print axioms oneHandleBalancedCoreRelativeShiftHom
#print axioms oneHandleBalancedCoreRelativeShiftHom_apply
#print axioms dmForgetHandles_balancedCorrectedRelator
#print axioms oneHandleBalancedCoreRelativeTarget
#print axioms target_mem_relativeRange_iff_target_mem_range
#print axioms OneHandleBalancedCoreRelativeRangeSupply
#print axioms relativeRangeSupply_iff_rangeSupply
#print axioms OneHandleBalancedCoreRelativeSurjectiveSupply
#print axioms relativeRangeSupply_of_surjective
#print axioms mpcPivShiftH_two_one_of_balancedRelativeSurjective

end
end GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
