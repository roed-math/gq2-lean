/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedRelativeLift

/-!
# The finite four-core correction problem

W206 identifies the depth and handle-forgetting conditions with a finite relative layer.  This
file packages all four W205 correction rows at level `k+1` and proves that their finite word
equation is exactly equivalent to the original group-level correction object.

The `A`, `B`, and `D` coordinates use `oneHandleRelativeLambdaImage`.  The `C` coordinate uses
the image of the smaller exact subgroup additionally killed by every continuous `Z_2`-valued
character.  This is intentionally defined as an image of exact representatives: no claim is
made that character-neutrality is determined by an arbitrary finite quotient class.

Thus the remaining one-handle Mpc boundary is a finite, constrained four-coordinate image
problem for the already-computed stage-shift word.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedFiniteCore

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedClimb
open GQ2.Dyadic.Instances.MpcBalancedStageShift
open GQ2.Dyadic.Instances.MpcBalancedCoreShift
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Roe.Labute

/-! ## The character-neutral relative layer -/

/-- The exact elements invisible to every continuous `Z_2`-valued character. -/
def oneHandleRowKer : Subgroup (DM 2 1) :=
  ⨅ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
    f.toMonoidHom.ker

theorem mem_oneHandleRowKer_iff {x : DM 2 1} :
    x ∈ oneHandleRowKer ↔
      ∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]), f x = 1 := by
  simp [oneHandleRowKer, Subgroup.mem_iInf, MonoidHom.mem_ker]

/-- The finite image of exact relative elements satisfying the extra `C`-row condition. -/
def oneHandleNeutralRelativeLambdaImage (j n : ℕ) :
    Subgroup (levelQuot (DM 2 1) n) :=
  ((twoCentralSeries (DM 2 1) j ⊓
      (dmForgetHandles 2 1).toMonoidHom.ker) ⊓ oneHandleRowKer).map
    (levelMk (DM 2 1) n)

/-- Membership in the neutral relative layer is exactly existence of a representative with
all three original group-level properties. -/
theorem mem_oneHandleNeutralRelativeLambdaImage_iff_exists_exact
    {j n : ℕ} (x : levelQuot (DM 2 1) n) :
    x ∈ oneHandleNeutralRelativeLambdaImage j n ↔
      ∃ e : DM 2 1,
        e ∈ twoCentralSeries (DM 2 1) j ∧
        dmForgetHandles 2 1 e = 1 ∧
        (∀ f : ContinuousMonoidHom (DM 2 1) (Multiplicative ℤ_[2]),
          toAdd (f e) = 0) ∧
        levelMk (DM 2 1) n e = x := by
  constructor
  · rintro ⟨e, ⟨⟨he, hef⟩, herow⟩, hex⟩
    refine ⟨e, he, MonoidHom.mem_ker.mp hef, ?_, hex⟩
    intro f
    have hf := (mem_oneHandleRowKer_iff.mp herow) f
    exact congrArg toAdd hf
  · rintro ⟨e, he, hef, herow, hex⟩
    refine ⟨e, ⟨⟨he, MonoidHom.mem_ker.mpr hef⟩, ?_⟩, hex⟩
    apply mem_oneHandleRowKer_iff.mpr
    intro f
    apply toAdd.injective
    simpa using herow f

/-! ## Four finite correction coordinates -/

/-- Four finite correction classes, with the exact relative constraints built into their
types. -/
structure OneHandleBalancedCoreLevelCorrection (k : ℕ) where
  corrA : oneHandleRelativeLambdaImage (k - 1) (k + 1)
  corrB : oneHandleRelativeLambdaImage (k - 1) (k + 1)
  corrC : oneHandleNeutralRelativeLambdaImage (k - 1) (k + 1)
  corrD : oneHandleRelativeLambdaImage (k - 1) (k + 1)

noncomputable instance (k : ℕ) : Finite (OneHandleBalancedCoreLevelCorrection k) := by
  letI : Finite (levelQuot (DM 2 1) (k + 1)) :=
    finite_levelQuot (DM 2 1) (dmFinsetTopGen 2 1) (isProP_DM 2 1) (k + 1)
  exact Finite.of_injective
    (fun E ↦ (E.corrA, E.corrB, E.corrC, E.corrD)) fun E F h ↦ by
      cases E with
      | mk a b c d =>
        cases F with
        | mk a' b' c' d' =>
          simp only [Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl⟩
          rfl

/-- The four finite core corrections followed by two trivial handle corrections. -/
def oneHandleBalancedCoreLevelCorrectionMark {k : ℕ}
    (E : OneHandleBalancedCoreLevelCorrection k) :
    Fin (coreRank 1) → levelQuot (DM 2 1) (k + 1) :=
  fullMark E.corrA.1 E.corrB.1 E.corrC.1 E.corrD.1
    (fun _ ↦ 1) (fun _ ↦ 1)

/-- The finite four-core stage-shift map. -/
def oneHandleBalancedCoreLevelShift
    {k : ℕ} (p : OneHandleBalancedPoint) (E : OneHandleBalancedCoreLevelCorrection k) :
    levelQuot (DM 2 1) (k + 1) :=
  stageShift (mStageWord 2 1 (by omega))
    (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i))
    (oneHandleBalancedCoreLevelCorrectionMark E)

/-- Send a group-level correction to its four constrained finite classes. -/
def coreShiftCorrectionToLevel
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedCoreShiftCorrection p k) :
    OneHandleBalancedCoreLevelCorrection k where
  corrA := ⟨levelMk (DM 2 1) (k + 1) (coreCorrA E.factors),
    (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) _).mpr
      ⟨coreCorrA E.factors, E.depthA, E.forgetA, rfl⟩⟩
  corrB := ⟨levelMk (DM 2 1) (k + 1) (coreCorrB E.factors),
    (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) _).mpr
      ⟨coreCorrB E.factors, E.depthB, E.forgetB, rfl⟩⟩
  corrC := ⟨levelMk (DM 2 1) (k + 1) (coreCorrC E.factors),
    (mem_oneHandleNeutralRelativeLambdaImage_iff_exists_exact _).mpr
      ⟨coreCorrC E.factors, E.depthC, E.forgetC, E.row, rfl⟩⟩
  corrD := ⟨levelMk (DM 2 1) (k + 1) (coreCorrD E.factors),
    (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) _).mpr
      ⟨coreCorrD E.factors, E.depthD, E.forgetD, rfl⟩⟩

/-- Passing a group-level correction to finite classes preserves the shift exactly. -/
theorem coreLevelShift_toLevel
    {p : OneHandleBalancedPoint} {k : ℕ}
    (E : OneHandleBalancedCoreShiftCorrection p k) :
    oneHandleBalancedCoreLevelShift p (coreShiftCorrectionToLevel E) =
      oneHandleBalancedCoreRelatorShift p E.factors k := by
  rw [oneHandleBalancedCoreLevelShift, oneHandleBalancedCoreRelatorShift]
  congr 2
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleBalancedCoreLevelCorrectionMark,
        oneHandleBalancedCoreCorrectionMark, mHandleIdx_coordU, mHandleIdx_coordV]

/-- Chosen representatives of the four finite coordinates induce the same correction
marking after projection. -/
theorem coreLevelCorrectionMark_eq_of_representatives
    {k : ℕ} (E : OneHandleBalancedCoreLevelCorrection k)
    (a b c d : DM 2 1)
    (ha : levelMk (DM 2 1) (k + 1) a = E.corrA.1)
    (hb : levelMk (DM 2 1) (k + 1) b = E.corrB.1)
    (hc : levelMk (DM 2 1) (k + 1) c = E.corrC.1)
    (hd : levelMk (DM 2 1) (k + 1) d = E.corrD.1) :
    (fun i ↦ levelMk (DM 2 1) (k + 1)
      (oneHandleBalancedCoreCorrectionMark (a, b, c, d) i)) =
      oneHandleBalancedCoreLevelCorrectionMark E := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · simpa [oneHandleBalancedCoreCorrectionMark, coreCorrA,
      oneHandleBalancedCoreLevelCorrectionMark] using ha
  · simpa [oneHandleBalancedCoreCorrectionMark, coreCorrB,
      oneHandleBalancedCoreLevelCorrectionMark] using hb
  · simpa [oneHandleBalancedCoreCorrectionMark, coreCorrC,
      oneHandleBalancedCoreLevelCorrectionMark] using hc
  · simpa [oneHandleBalancedCoreCorrectionMark, coreCorrD,
      oneHandleBalancedCoreLevelCorrectionMark] using hd
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleBalancedCoreCorrectionMark,
        oneHandleBalancedCoreLevelCorrectionMark, mHandleIdx_coordU, mHandleIdx_coordV]

/-! ## Exact equivalence with W205 -/

/-- The original correction object exists exactly when the finite constrained four-row word
equation has a solution. -/
theorem nonempty_coreShiftCorrection_iff_exists_levelCorrection
    (p : OneHandleBalancedPoint) (k : ℕ) :
    Nonempty (OneHandleBalancedCoreShiftCorrection p k) ↔
      ∃ E : OneHandleBalancedCoreLevelCorrection k,
        oneHandleBalancedCoreLevelShift p E =
          (levelMk (DM 2 1) (k + 1)
            (mRelWord 2 (balancedCorrectedMark p)))⁻¹ := by
  constructor
  · rintro ⟨E⟩
    exact ⟨coreShiftCorrectionToLevel E, (coreLevelShift_toLevel E).trans E.kills⟩
  · rintro ⟨E, hkill⟩
    obtain ⟨a, ha, hfa, haQ⟩ :=
      (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) E.corrA.1).mp
        E.corrA.2
    obtain ⟨b, hb, hfb, hbQ⟩ :=
      (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) E.corrB.1).mp
        E.corrB.2
    obtain ⟨c, hc, hfc, hcrow, hcQ⟩ :=
      (mem_oneHandleNeutralRelativeLambdaImage_iff_exists_exact E.corrC.1).mp
        E.corrC.2
    obtain ⟨d, hd, hfd, hdQ⟩ :=
      (mem_oneHandleRelativeLambdaImage_iff_exists_exact (by omega) E.corrD.1).mp
        E.corrD.2
    refine ⟨{
      factors := (a, b, c, d)
      depthA := ha
      depthB := hb
      depthC := hc
      depthD := hd
      forgetA := hfa
      forgetB := hfb
      forgetC := hfc
      forgetD := hfd
      row := hcrow
      kills := ?_ }⟩
    unfold oneHandleBalancedCoreRelatorShift
    unfold oneHandleBalancedCoreLevelShift at hkill
    rw [coreLevelCorrectionMark_eq_of_representatives E a b c d haQ hbQ hcQ hdQ]
    exact hkill

/-- Uniform finite constrained four-row reachability. -/
def OneHandleBalancedCoreLevelSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ p ∈ oneHandleBalancedSet Psi0 k,
    ∃ E : OneHandleBalancedCoreLevelCorrection k,
      oneHandleBalancedCoreLevelShift p E =
        (levelMk (DM 2 1) (k + 1)
          (mRelWord 2 (balancedCorrectedMark p)))⁻¹

/-- The finite four-row supply is exactly the W205 group-level supply. -/
theorem coreLevelSupply_iff_coreShiftSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreLevelSupply Psi0 ↔
      OneHandleBalancedCoreShiftSupply Psi0 := by
  constructor <;> intro H k hk p hp
  · exact (nonempty_coreShiftCorrection_iff_exists_levelCorrection p k).mpr
      (H k hk p hp)
  · exact (nonempty_coreShiftCorrection_iff_exists_levelCorrection p k).mp
      (H k hk p hp)

/-- The finite constrained four-row equation is enough for the one-handle pivot. -/
theorem mpcPivShiftH_two_one_of_balancedCoreLevel
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hlevel : OneHandleBalancedCoreLevelSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedCoreShift Psi0 hchi0 hrow
    ((coreLevelSupply_iff_coreShiftSupply Psi0).mp Hlevel)

#print axioms oneHandleRowKer
#print axioms mem_oneHandleRowKer_iff
#print axioms oneHandleNeutralRelativeLambdaImage
#print axioms mem_oneHandleNeutralRelativeLambdaImage_iff_exists_exact
#print axioms OneHandleBalancedCoreLevelCorrection
#print axioms oneHandleBalancedCoreLevelCorrectionMark
#print axioms oneHandleBalancedCoreLevelShift
#print axioms coreShiftCorrectionToLevel
#print axioms coreLevelShift_toLevel
#print axioms coreLevelCorrectionMark_eq_of_representatives
#print axioms nonempty_coreShiftCorrection_iff_exists_levelCorrection
#print axioms OneHandleBalancedCoreLevelSupply
#print axioms coreLevelSupply_iff_coreShiftSupply
#print axioms mpcPivShiftH_two_one_of_balancedCoreLevel

end
end GQ2.Dyadic.Instances.MpcBalancedFiniteCore
