/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedFiniteCore

/-!
# The finite four-core shift as a range problem

The W207 correction type is a finite group under coordinatewise multiplication.  At every
stage `k >= 3`, its shift is a homomorphism into the central layer `zLayer (DM 2 1) k`.

For a balanced point, the inverse of the current relator also belongs to that layer.  The
finite word equation of W207 is therefore exactly membership of this target in the range of
one finite group homomorphism.  This is the form suited to a graded rank, spanning, or checked
finite calculation.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedFiniteSpan

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedLevelThree
open GQ2.Dyadic.Instances.MpcBalancedClimb
open GQ2.Dyadic.Instances.MpcBalancedCoreShift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Roe.Labute

/-! ## Coordinatewise group structure -/

namespace OneHandleBalancedCoreLevelCorrection

variable {k : ℕ}

@[ext] theorem ext {E F : OneHandleBalancedCoreLevelCorrection k}
    (hA : E.corrA = F.corrA) (hB : E.corrB = F.corrB)
    (hC : E.corrC = F.corrC) (hD : E.corrD = F.corrD) : E = F := by
  cases E
  cases F
  simp_all

protected def one : OneHandleBalancedCoreLevelCorrection k where
  corrA := 1
  corrB := 1
  corrC := 1
  corrD := 1

protected def mul (E F : OneHandleBalancedCoreLevelCorrection k) :
    OneHandleBalancedCoreLevelCorrection k where
  corrA := E.corrA * F.corrA
  corrB := E.corrB * F.corrB
  corrC := E.corrC * F.corrC
  corrD := E.corrD * F.corrD

protected def inv (E : OneHandleBalancedCoreLevelCorrection k) :
    OneHandleBalancedCoreLevelCorrection k where
  corrA := E.corrA⁻¹
  corrB := E.corrB⁻¹
  corrC := E.corrC⁻¹
  corrD := E.corrD⁻¹

noncomputable instance : Group (OneHandleBalancedCoreLevelCorrection k) where
  one := OneHandleBalancedCoreLevelCorrection.one
  mul := OneHandleBalancedCoreLevelCorrection.mul
  inv := OneHandleBalancedCoreLevelCorrection.inv
  mul_assoc E F H := by ext <;> exact mul_assoc _ _ _
  one_mul E := by ext <;> exact one_mul _
  mul_one E := by ext <;> exact mul_one _
  inv_mul_cancel E := by ext <;> exact inv_mul_cancel _

@[simp] theorem one_corrA :
    (1 : OneHandleBalancedCoreLevelCorrection k).corrA = 1 := rfl
@[simp] theorem one_corrB :
    (1 : OneHandleBalancedCoreLevelCorrection k).corrB = 1 := rfl
@[simp] theorem one_corrC :
    (1 : OneHandleBalancedCoreLevelCorrection k).corrC = 1 := rfl
@[simp] theorem one_corrD :
    (1 : OneHandleBalancedCoreLevelCorrection k).corrD = 1 := rfl

@[simp] theorem mul_corrA (E F : OneHandleBalancedCoreLevelCorrection k) :
    (E * F).corrA = E.corrA * F.corrA := rfl
@[simp] theorem mul_corrB (E F : OneHandleBalancedCoreLevelCorrection k) :
    (E * F).corrB = E.corrB * F.corrB := rfl
@[simp] theorem mul_corrC (E F : OneHandleBalancedCoreLevelCorrection k) :
    (E * F).corrC = E.corrC * F.corrC := rfl
@[simp] theorem mul_corrD (E F : OneHandleBalancedCoreLevelCorrection k) :
    (E * F).corrD = E.corrD * F.corrD := rfl

end OneHandleBalancedCoreLevelCorrection

/-! ## The finite shift homomorphism -/

/-- The neutral relative layer is contained in the ordinary depth image. -/
theorem oneHandleNeutralRelativeLambdaImage_le_lambdaImage (j n : ℕ) :
    oneHandleNeutralRelativeLambdaImage j n ≤ lambdaImage (DM 2 1) j n := by
  rintro x ⟨e, ⟨⟨he, -⟩, -⟩, rfl⟩
  exact ⟨e, he, rfl⟩

/-- Forget the constrained coordinate types and retain the underlying raw depth correction. -/
def oneHandleBalancedCoreLevelToRaw {k : ℕ}
    (E : OneHandleBalancedCoreLevelCorrection k) :
    EvenRawDepthCorrection (DM 2 1) 1 k where
  correction := oneHandleBalancedCoreLevelCorrectionMark E
  depth i := by
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
    · exact E.corrA.2.1
    · exact E.corrB.2.1
    · exact oneHandleNeutralRelativeLambdaImage_le_lambdaImage _ _ E.corrC.2
    · exact E.corrD.2.1
    · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [oneHandleBalancedCoreLevelCorrectionMark,
          mHandleIdx_coordU, fullMark_handleU]
        exact Subgroup.one_mem _
      · rw [oneHandleBalancedCoreLevelCorrectionMark,
          mHandleIdx_coordV, fullMark_handleV]
        exact Subgroup.one_mem _

@[simp] theorem oneHandleBalancedCoreLevelCorrectionMark_one {k : ℕ} :
    oneHandleBalancedCoreLevelCorrectionMark
      (1 : OneHandleBalancedCoreLevelCorrection k) = fun _ ↦ 1 := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleBalancedCoreLevelCorrectionMark,
        mHandleIdx_coordU, mHandleIdx_coordV]

@[simp] theorem oneHandleBalancedCoreLevelCorrectionMark_mul
    {k : ℕ} (E F : OneHandleBalancedCoreLevelCorrection k) :
    oneHandleBalancedCoreLevelCorrectionMark (E * F) =
      fun i ↦ oneHandleBalancedCoreLevelCorrectionMark E i *
        oneHandleBalancedCoreLevelCorrectionMark F i := by
  funext i
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases mHandleCoord_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleBalancedCoreLevelCorrectionMark,
        mHandleIdx_coordU, mHandleIdx_coordV]

/-- The constrained finite source maps homomorphically into all raw depth corrections. -/
noncomputable def oneHandleBalancedCoreLevelToRawHom (k : ℕ) :
    OneHandleBalancedCoreLevelCorrection k →*
      EvenRawDepthCorrection (DM 2 1) 1 k where
  toFun := oneHandleBalancedCoreLevelToRaw
  map_one' := by
    apply EvenRawDepthCorrection.ext
    exact oneHandleBalancedCoreLevelCorrectionMark_one
  map_mul' E F := by
    apply EvenRawDepthCorrection.ext
    exact oneHandleBalancedCoreLevelCorrectionMark_mul E F

/-- The finite four-core stage shift as a homomorphism into the central layer. -/
noncomputable def oneHandleBalancedCoreLevelShiftHom
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    OneHandleBalancedCoreLevelCorrection k →* zLayer (DM 2 1) k :=
  (evenRawDepthShiftHom
    (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i)) hk).comp
      (oneHandleBalancedCoreLevelToRawHom k)

/-- The homomorphism's value is exactly the W207 finite shift. -/
theorem oneHandleBalancedCoreLevelShiftHom_apply
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (E : OneHandleBalancedCoreLevelCorrection k) :
    (oneHandleBalancedCoreLevelShiftHom p k hk E).1 =
      oneHandleBalancedCoreLevelShift p E := by
  change evenRawDbarWord
      (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i))
      (oneHandleBalancedCoreLevelCorrectionMark E) = _
  symm
  exact evenRawStageShift_m (G := DM 2 1) (by omega) (by omega) 1 k hk
    (fun i ↦ levelMk (DM 2 1) (k + 1) (balancedCorrectedMark p i))
    (oneHandleBalancedCoreLevelCorrectionMark E)
    (oneHandleBalancedCoreLevelToRaw E).depth

/-! ## The current relator as a target in the central layer -/

/-- A balanced point's corrected full relator has the advertised two-central depth. -/
theorem balancedCorrectedRelator_mem_twoCentralSeries
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)} {p : OneHandleBalancedPoint}
    {k : ℕ} (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    mRelWord 2 (balancedCorrectedMark p) ∈ twoCentralSeries (DM 2 1) k := by
  rcases hp with ⟨-, -, -, -, -, -, -, hdef⟩
  let w := mWord 2 (balancedA p) (balancedB p) (balancedC p) (balancedD p)
  have hc := (twoCentralSeries_normal (DM 2 1) k).conj_mem
    (oneHandleDDefect (balancedA p) (balancedB p) (balancedC p)
      (balancedD p) (balancedZ p)) hdef w
  rw [oneHandleDDefect_eq_conj_relWord] at hc
  dsimp [w] at hc
  convert hc using 1
  group

/-- The inverse current relator, regarded as the target central-layer class. -/
def oneHandleBalancedCoreLevelTarget
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)} {k : ℕ}
    (p : OneHandleBalancedPoint) (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    zLayer (DM 2 1) k :=
  ⟨(levelMk (DM 2 1) (k + 1) (mRelWord 2 (balancedCorrectedMark p)))⁻¹,
    ⟨(mRelWord 2 (balancedCorrectedMark p))⁻¹,
      Subgroup.inv_mem _ (balancedCorrectedRelator_mem_twoCentralSeries hp), by
        rw [map_inv]⟩⟩

/-- Solving the W207 word equation is exactly membership of the target in the finite shift
homomorphism's range. -/
theorem exists_levelCorrection_iff_target_mem_range
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k) :
    (∃ E : OneHandleBalancedCoreLevelCorrection k,
      oneHandleBalancedCoreLevelShift p E =
        (levelMk (DM 2 1) (k + 1)
          (mRelWord 2 (balancedCorrectedMark p)))⁻¹) ↔
      oneHandleBalancedCoreLevelTarget p hp ∈
        (oneHandleBalancedCoreLevelShiftHom p k hk).range := by
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨E, Subtype.ext ?_⟩
    rw [oneHandleBalancedCoreLevelShiftHom_apply]
    exact hE
  · rintro ⟨E, hE⟩
    refine ⟨E, ?_⟩
    have := congrArg Subtype.val hE
    rw [oneHandleBalancedCoreLevelShiftHom_apply] at this
    exact this

/-- Uniform membership of every current relator target in the finite shift range. -/
def OneHandleBalancedCoreRangeSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (p : OneHandleBalancedPoint)
    (hp : p ∈ oneHandleBalancedSet Psi0 k),
      oneHandleBalancedCoreLevelTarget p hp ∈
        (oneHandleBalancedCoreLevelShiftHom p k hk).range

/-- The finite range formulation is exactly the W207 finite-equation supply. -/
theorem coreRangeSupply_iff_coreLevelSupply
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)) :
    OneHandleBalancedCoreRangeSupply Psi0 ↔
      OneHandleBalancedCoreLevelSupply Psi0 := by
  constructor <;> intro H k hk p hp
  · exact (exists_levelCorrection_iff_target_mem_range p hk hp).mpr (H k hk p hp)
  · exact (exists_levelCorrection_iff_target_mem_range p hk hp).mp (H k hk p hp)

/-- Finite four-core range membership is enough for the one-handle pivot. -/
theorem mpcPivShiftH_two_one_of_balancedCoreRange
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (hchi0 : ∀ x, chiM 2 0 (Psi0 x) = chiM 2 0 x)
    (hrow : ∀ f : ContinuousMonoidHom (DM 2 0) (Multiplicative ℤ_[2]),
      toAdd (f (Psi0 (dmC 2 0))) =
        toAdd (f (dmC 2 0)) + 2 * toAdd (f (dmB 2 0)))
    (Hrange : OneHandleBalancedCoreRangeSupply Psi0) :
    MpcPivShiftH 2 1 :=
  mpcPivShiftH_two_one_of_balancedCoreLevel Psi0 hchi0 hrow
    ((coreRangeSupply_iff_coreLevelSupply Psi0).mp Hrange)

#print axioms OneHandleBalancedCoreLevelCorrection.ext
#print axioms oneHandleNeutralRelativeLambdaImage_le_lambdaImage
#print axioms oneHandleBalancedCoreLevelToRaw
#print axioms oneHandleBalancedCoreLevelCorrectionMark_one
#print axioms oneHandleBalancedCoreLevelCorrectionMark_mul
#print axioms oneHandleBalancedCoreLevelToRawHom
#print axioms oneHandleBalancedCoreLevelShiftHom
#print axioms oneHandleBalancedCoreLevelShiftHom_apply
#print axioms balancedCorrectedRelator_mem_twoCentralSeries
#print axioms oneHandleBalancedCoreLevelTarget
#print axioms exists_levelCorrection_iff_target_mem_range
#print axioms OneHandleBalancedCoreRangeSupply
#print axioms coreRangeSupply_iff_coreLevelSupply
#print axioms mpcPivShiftH_two_one_of_balancedCoreRange

end
end GQ2.Dyadic.Instances.MpcBalancedFiniteSpan
