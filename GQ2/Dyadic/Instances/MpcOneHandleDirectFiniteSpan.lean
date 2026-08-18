/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
import GQ2.Dyadic.Instances.MpcBalancedFiniteCore
import GQ2.Dyadic.Instances.StageAbstractionEvenRawSpan

/-!
# The direct one-handle successor as a finite range problem

The direct correction criterion has four nontrivial core coordinates.  At depth `k - 1`,
all four are killed by `chiM`; the `C` coordinate is additionally invisible to every
continuous `Z_2`-valued character.  This file builds their exact finite quotient images and
packages the crossed-derivation shift as a homomorphism into the central layer.

For every direct stage, existence of a group-level correction is equivalent to membership
of the inverse current relator in the range of this finite homomorphism.  Thus the remaining
one-handle problem is a concrete finite spanning problem with no compact-fibre or generation
conditions left inside the correction step.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcOneHandleDirectLimit
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Roe.Labute

private abbrev H := DM 2 1

/-! ## Exact finite coordinate images -/

def oneHandleDirectChiKer : Subgroup H :=
  (chiM 2 1).toMonoidHom.ker

def oneHandleDirectLambdaImage (j n : ℕ) : Subgroup (levelQuot H n) :=
  (twoCentralSeries H j ⊓ oneHandleDirectChiKer).map (levelMk H n)

theorem mem_oneHandleDirectLambdaImage_iff_exists_exact
    {j n : ℕ} (x : levelQuot H n) :
    x ∈ oneHandleDirectLambdaImage j n ↔
      ∃ e : H, e ∈ twoCentralSeries H j ∧ chiM 2 1 e = 1 ∧
        levelMk H n e = x := by
  constructor
  · rintro ⟨e, ⟨he, hechi⟩, rfl⟩
    exact ⟨e, he, MonoidHom.mem_ker.mp hechi, rfl⟩
  · rintro ⟨e, he, hechi, rfl⟩
    exact ⟨e, ⟨he, MonoidHom.mem_ker.mpr hechi⟩, rfl⟩

def oneHandleDirectNeutralLambdaImage (j n : ℕ) :
    Subgroup (levelQuot H n) :=
  ((twoCentralSeries H j ⊓ oneHandleDirectChiKer) ⊓ oneHandleRowKer).map
    (levelMk H n)

theorem mem_oneHandleDirectNeutralLambdaImage_iff_exists_exact
    {j n : ℕ} (x : levelQuot H n) :
    x ∈ oneHandleDirectNeutralLambdaImage j n ↔
      ∃ e : H, e ∈ twoCentralSeries H j ∧ chiM 2 1 e = 1 ∧
        (∀ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
          toAdd (f e) = 0) ∧ levelMk H n e = x := by
  constructor
  · rintro ⟨e, ⟨⟨he, hechi⟩, herow⟩, rfl⟩
    refine ⟨e, he, MonoidHom.mem_ker.mp hechi, ?_, rfl⟩
    intro f
    exact congrArg toAdd ((mem_oneHandleRowKer_iff.mp herow) f)
  · rintro ⟨e, he, hechi, herow, rfl⟩
    refine ⟨e, ⟨⟨he, MonoidHom.mem_ker.mpr hechi⟩, ?_⟩, rfl⟩
    apply mem_oneHandleRowKer_iff.mpr
    intro f
    apply toAdd.injective
    simpa using herow f

theorem oneHandleDirectLambdaImage_le_lambdaImage (j n : ℕ) :
    oneHandleDirectLambdaImage j n ≤ lambdaImage H j n := by
  rintro x ⟨e, ⟨he, -⟩, rfl⟩
  exact ⟨e, he, rfl⟩

theorem oneHandleDirectNeutralLambdaImage_le_lambdaImage (j n : ℕ) :
    oneHandleDirectNeutralLambdaImage j n ≤ lambdaImage H j n := by
  rintro x ⟨e, ⟨⟨he, -⟩, -⟩, rfl⟩
  exact ⟨e, he, rfl⟩

abbrev OneHandleDirectLevelCorrection (k : ℕ) :=
  oneHandleDirectLambdaImage (k - 1) (k + 1) ×
    oneHandleDirectLambdaImage (k - 1) (k + 1) ×
      oneHandleDirectNeutralLambdaImage (k - 1) (k + 1) ×
        oneHandleDirectLambdaImage (k - 1) (k + 1)

noncomputable instance (k : ℕ) : Finite (OneHandleDirectLevelCorrection k) := by
  letI : Finite (levelQuot H (k + 1)) :=
    finite_levelQuot H (dmFinsetTopGen 2 1) (isProP_DM 2 1) (k + 1)
  infer_instance

def oneHandleDirectLevelCorrectionMark {k : ℕ}
    (E : OneHandleDirectLevelCorrection k) :
    Fin (coreRank 1) → levelQuot H (k + 1) :=
  fullMark E.1.1 E.2.1.1 E.2.2.1.1 E.2.2.2.1
    (fun _ ↦ 1) (fun _ ↦ 1)

def oneHandleDirectLevelShift
    (m : Fin (coreRank 1) → H) {k : ℕ}
    (E : OneHandleDirectLevelCorrection k) : levelQuot H (k + 1) :=
  stageShift (mStageWord 2 1 (by omega))
    (fun i ↦ levelMk H (k + 1) (m i))
    (oneHandleDirectLevelCorrectionMark E)

/-! ## Exact representatives and the group-level correction -/

def directCorrectionToLevel
    {m : Fin (coreRank 1) → H} {k : ℕ}
    (E : OneHandleDirectCorrection m k) :
    OneHandleDirectLevelCorrection k :=
  (⟨levelMk H (k + 1) (E.factors 0),
      (mem_oneHandleDirectLambdaImage_iff_exists_exact _).mpr
        ⟨E.factors 0, E.depth 0, E.chi 0, rfl⟩⟩,
    ⟨levelMk H (k + 1) (E.factors 1),
      (mem_oneHandleDirectLambdaImage_iff_exists_exact _).mpr
        ⟨E.factors 1, E.depth 1, E.chi 1, rfl⟩⟩,
    ⟨levelMk H (k + 1) (E.factors 2),
      (mem_oneHandleDirectNeutralLambdaImage_iff_exists_exact _).mpr
        ⟨E.factors 2, E.depth 2, E.chi 2, E.row, rfl⟩⟩,
    ⟨levelMk H (k + 1) (E.factors 3),
      (mem_oneHandleDirectLambdaImage_iff_exists_exact _).mpr
        ⟨E.factors 3, E.depth 3, E.chi 3, rfl⟩⟩)

theorem directLevelCorrectionMark_toLevel
    {m : Fin (coreRank 1) → H} {k : ℕ}
    (E : OneHandleDirectCorrection m k) :
    oneHandleDirectLevelCorrectionMark (directCorrectionToLevel E) =
      fun i ↦ levelMk H (k + 1) (E.factors i) := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [oneHandleDirectLevelCorrectionMark,
        mHandleIdx_coordU, E.handleU]
    · simp [oneHandleDirectLevelCorrectionMark,
        mHandleIdx_coordV, E.handleV]

theorem directLevelShift_toLevel
    {m : Fin (coreRank 1) → H} {k : ℕ}
    (E : OneHandleDirectCorrection m k) :
    oneHandleDirectLevelShift m (directCorrectionToLevel E) =
      oneHandleDirectRelatorShift m E.factors k := by
  rw [oneHandleDirectLevelShift, oneHandleDirectRelatorShift,
    directLevelCorrectionMark_toLevel]

theorem nonempty_directCorrection_iff_exists_levelCorrection
    (m : Fin (coreRank 1) → H) (k : ℕ) :
    Nonempty (OneHandleDirectCorrection m k) ↔
      ∃ E : OneHandleDirectLevelCorrection k,
        oneHandleDirectLevelShift m E =
          (levelMk H (k + 1) (mRelWord 2 m))⁻¹ := by
  constructor
  · rintro ⟨E⟩
    exact ⟨directCorrectionToLevel E, (directLevelShift_toLevel E).trans E.kills⟩
  · rintro ⟨E, hE⟩
    obtain ⟨a, ha, hachi, haQ⟩ :=
      (mem_oneHandleDirectLambdaImage_iff_exists_exact E.1.1).mp E.1.2
    obtain ⟨b, hb, hbchi, hbQ⟩ :=
      (mem_oneHandleDirectLambdaImage_iff_exists_exact E.2.1.1).mp E.2.1.2
    obtain ⟨c, hc, hcchi, hcrow, hcQ⟩ :=
      (mem_oneHandleDirectNeutralLambdaImage_iff_exists_exact E.2.2.1.1).mp
        E.2.2.1.2
    obtain ⟨d, hd, hdchi, hdQ⟩ :=
      (mem_oneHandleDirectLambdaImage_iff_exists_exact E.2.2.2.1).mp E.2.2.2.2
    let e : Fin (coreRank 1) → H :=
      fullMark a b c d (fun _ ↦ 1) (fun _ ↦ 1)
    have heQ : (fun i ↦ levelMk H (k + 1) (e i)) =
        oneHandleDirectLevelCorrectionMark E := by
      funext i
      rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · exact haQ
      · exact hbQ
      · exact hcQ
      · exact hdQ
      · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
          simp [e, oneHandleDirectLevelCorrectionMark,
            mHandleIdx_coordU, mHandleIdx_coordV]
    refine ⟨{
      factors := e
      depth := ?_
      handleU := ?_
      handleV := ?_
      chi := ?_
      row := ?_
      kills := ?_ }⟩
    · intro i
      rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · exact ha
      · exact hb
      · exact hc
      · exact hd
      · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
          simp [e, mHandleIdx_coordU, mHandleIdx_coordV]
    · intro j
      simp [e]
    · intro j
      simp [e]
    · intro i
      rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
      · exact hachi
      · exact hbchi
      · exact hcchi
      · exact hdchi
      · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
          simp [e, mHandleIdx_coordU, mHandleIdx_coordV]
    · simpa [e] using hcrow
    · rw [oneHandleDirectRelatorShift]
      rw [heQ]
      exact hE

/-! ## The finite shift homomorphism and target range -/

def oneHandleDirectLevelToRaw {k : ℕ}
    (E : OneHandleDirectLevelCorrection k) :
    EvenRawDepthCorrection H 1 k where
  correction := oneHandleDirectLevelCorrectionMark E
  depth i := by
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · exact oneHandleDirectLambdaImage_le_lambdaImage _ _ E.1.2
    · exact oneHandleDirectLambdaImage_le_lambdaImage _ _ E.2.1.2
    · exact oneHandleDirectNeutralLambdaImage_le_lambdaImage _ _ E.2.2.1.2
    · exact oneHandleDirectLambdaImage_le_lambdaImage _ _ E.2.2.2.2
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [oneHandleDirectLevelCorrectionMark,
          mHandleIdx_coordU, fullMark_handleU]
        exact Subgroup.one_mem _
      · rw [oneHandleDirectLevelCorrectionMark,
          mHandleIdx_coordV, fullMark_handleV]
        exact Subgroup.one_mem _

noncomputable def oneHandleDirectLevelToRawHom (k : ℕ) :
    OneHandleDirectLevelCorrection k →* EvenRawDepthCorrection H 1 k where
  toFun := oneHandleDirectLevelToRaw
  map_one' := by
    apply EvenRawDepthCorrection.ext
    funext i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · simp [oneHandleDirectLevelToRaw,
          oneHandleDirectLevelCorrectionMark, mHandleIdx_coordU]
      · simp [oneHandleDirectLevelToRaw,
          oneHandleDirectLevelCorrectionMark, mHandleIdx_coordV]
  map_mul' E F := by
    apply EvenRawDepthCorrection.ext
    funext i
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · simp [oneHandleDirectLevelToRaw,
          oneHandleDirectLevelCorrectionMark, mHandleIdx_coordU]
      · simp [oneHandleDirectLevelToRaw,
          oneHandleDirectLevelCorrectionMark, mHandleIdx_coordV]

noncomputable def oneHandleDirectLevelShiftHom
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k) :
    OneHandleDirectLevelCorrection k →* zLayer H k :=
  (evenRawDepthShiftHom
    (fun i ↦ levelMk H (k + 1) (m i)) hk).comp
      (oneHandleDirectLevelToRawHom k)

theorem oneHandleDirectLevelShiftHom_apply
    (m : Fin (coreRank 1) → H) (k : ℕ) (hk : 3 ≤ k)
    (E : OneHandleDirectLevelCorrection k) :
    (oneHandleDirectLevelShiftHom m k hk E).1 =
      oneHandleDirectLevelShift m E := by
  change evenRawDbarWord
      (fun i ↦ levelMk H (k + 1) (m i))
      (oneHandleDirectLevelCorrectionMark E) = _
  symm
  exact evenRawStageShift_m (G := H) (by omega) (by omega) 1 k hk _ _
    (oneHandleDirectLevelToRaw E).depth

def oneHandleDirectLevelTarget
    {m : Fin (coreRank 1) → H} {k : ℕ}
    (hm : m ∈ oneHandleDirectSet k) : zLayer H k :=
  ⟨(levelMk H (k + 1) (mRelWord 2 m))⁻¹,
    ⟨(mRelWord 2 m)⁻¹, Subgroup.inv_mem _ hm.2.2.2.2, by rw [map_inv]⟩⟩

theorem nonempty_directCorrection_iff_target_mem_range
    (m : Fin (coreRank 1) → H) {k : ℕ} (hk : 3 ≤ k)
    (hm : m ∈ oneHandleDirectSet k) :
    Nonempty (OneHandleDirectCorrection m k) ↔
      oneHandleDirectLevelTarget hm ∈
        (oneHandleDirectLevelShiftHom m k hk).range := by
  rw [nonempty_directCorrection_iff_exists_levelCorrection]
  constructor
  · rintro ⟨E, hE⟩
    exact ⟨E, Subtype.ext ((oneHandleDirectLevelShiftHom_apply m k hk E).trans hE)⟩
  · rintro ⟨E, hE⟩
    refine ⟨E, ?_⟩
    have h := congrArg Subtype.val hE
    rw [oneHandleDirectLevelShiftHom_apply] at h
    exact h

def OneHandleDirectFiniteRangeSupply : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (m : Fin (coreRank 1) → H)
    (hm : m ∈ oneHandleDirectSet k),
      oneHandleDirectLevelTarget hm ∈
        (oneHandleDirectLevelShiftHom m k (by omega)).range

theorem directFiniteRangeSupply_iff_correctionSupply :
    OneHandleDirectFiniteRangeSupply ↔ OneHandleDirectCorrectionSupply := by
  constructor <;> intro Hcorr k hk m hm
  · exact (nonempty_directCorrection_iff_target_mem_range m (by omega) hm).mpr
      (Hcorr k hk m hm)
  · exact (nonempty_directCorrection_iff_target_mem_range m (by omega) hm).mp
      (Hcorr k hk m hm)

theorem mpcPivShiftH_two_one_of_directFiniteRange
    (Hrange : OneHandleDirectFiniteRangeSupply) : MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_direct_correctionSupply
    (directFiniteRangeSupply_iff_correctionSupply.mp Hrange)

#print axioms oneHandleDirectChiKer
#print axioms oneHandleDirectLambdaImage
#print axioms mem_oneHandleDirectLambdaImage_iff_exists_exact
#print axioms oneHandleDirectNeutralLambdaImage
#print axioms mem_oneHandleDirectNeutralLambdaImage_iff_exists_exact
#print axioms oneHandleDirectLambdaImage_le_lambdaImage
#print axioms oneHandleDirectNeutralLambdaImage_le_lambdaImage
#print axioms OneHandleDirectLevelCorrection
#print axioms oneHandleDirectLevelCorrectionMark
#print axioms oneHandleDirectLevelShift
#print axioms nonempty_directCorrection_iff_exists_levelCorrection
#print axioms oneHandleDirectLevelShiftHom
#print axioms oneHandleDirectLevelShiftHom_apply
#print axioms oneHandleDirectLevelTarget
#print axioms nonempty_directCorrection_iff_target_mem_range
#print axioms OneHandleDirectFiniteRangeSupply
#print axioms directFiniteRangeSupply_iff_correctionSupply
#print axioms mpcPivShiftH_two_one_of_directFiniteRange

end
end GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
