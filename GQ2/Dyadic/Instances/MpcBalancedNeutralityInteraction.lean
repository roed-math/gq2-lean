/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedNeutralitySourceQuotient

/-!
# The residual C-versus-ABD interaction

W214 expresses the neutral-`C` cokernel as the relative-`C`-mod-neutral source modulo an
interaction kernel.  This file identifies that kernel without mentioning the neutral `C`
range again: it is exactly the image of ordinary relative `C` classes whose relaxed shift
lies in the span of the constrained `A`, `B`, and `D` rows.

This is still an exact reduction rather than a vanishing result.  The remaining finite
problem is a literal `C`-versus-`ABD` row relation.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeLift
open GQ2.Dyadic.Instances.MpcBalancedFiniteCore
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralitySourceQuotient
open GQ2.Roe.Labute

open scoped IsMulCommutative

/-! ## The three other coordinate rows -/

/-- The span of the constrained `A`, `B`, and `D` rows, omitting `C`. -/
def oneHandleBalancedCoreOtherCoordinateSpan
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Subgroup (oneHandleRelativeZLayer k) :=
  ((oneHandleBalancedCoreRelativeShiftA p k hk).range ⊔
    (oneHandleBalancedCoreRelativeShiftB p k hk).range) ⊔
      (oneHandleBalancedCoreRelativeShiftD p k hk).range

theorem oneHandleBalancedCoreOtherCoordinateSpan_le_coordinateSpan
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreOtherCoordinateSpan p k hk ≤
      oneHandleBalancedCoreCoordinateSpan p k hk := by
  apply sup_le
  · exact le_sup_left
  · exact le_trans le_sup_right le_sup_right

/-- The constrained span is the `ABD` span plus the neutral `C` range. -/
theorem oneHandleBalancedCoreCoordinateSpan_eq_other_sup_C
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreCoordinateSpan p k hk =
      oneHandleBalancedCoreOtherCoordinateSpan p k hk ⊔
        (oneHandleBalancedCoreRelativeShiftC p k hk).range := by
  change
    (((oneHandleBalancedCoreRelativeShiftA p k hk).range ⊔
        (oneHandleBalancedCoreRelativeShiftB p k hk).range) ⊔
      ((oneHandleBalancedCoreRelativeShiftC p k hk).range ⊔
        (oneHandleBalancedCoreRelativeShiftD p k hk).range)) =
    ((((oneHandleBalancedCoreRelativeShiftA p k hk).range ⊔
        (oneHandleBalancedCoreRelativeShiftB p k hk).range) ⊔
      (oneHandleBalancedCoreRelativeShiftD p k hk).range) ⊔
        (oneHandleBalancedCoreRelativeShiftC p k hk).range)
  apply le_antisymm
  · apply sup_le
    · exact le_trans le_sup_left le_sup_left
    · apply sup_le
      · exact le_sup_right
      · exact le_trans le_sup_right le_sup_left
  · apply sup_le
    · apply sup_le
      · exact le_sup_left
      · exact le_trans le_sup_right le_sup_right
    · exact le_trans le_sup_left le_sup_right

/-! ## The interaction source and its image -/

/-- Ordinary relative `C` classes whose relaxed shift can be cancelled by the other three
constrained coordinate rows. -/
def oneHandleBalancedCoreNeutralityInteractionSource
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    Subgroup (oneHandleRelativeLambdaImage (k - 1) (k + 1)) :=
  Subgroup.comap (oneHandleBalancedCoreRelativeShiftCRelaxed p k hk)
    (oneHandleBalancedCoreOtherCoordinateSpan p k hk)

/-- Project the `C`-versus-`ABD` relation source modulo genuinely neutral `C` classes. -/
noncomputable def oneHandleBalancedCoreNeutralityInteractionToSource
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreNeutralityInteractionSource p k hk →*
      OneHandleRelativeCModuloNeutral k hk :=
  (oneHandleRelativeCModuloNeutralMk k hk).comp
    (oneHandleBalancedCoreNeutralityInteractionSource p k hk).subtype

@[simp] theorem oneHandleRelativeCModuloNeutralMk_neutral
    (k : ℕ) (hk : 3 ≤ k)
    (x : oneHandleNeutralRelativeLambdaImage (k - 1) (k + 1)) :
    oneHandleRelativeCModuloNeutralMk k hk
        (oneHandleNeutralRelativeInclusion (k - 1) (k + 1) (by omega) x) = 1 := by
  letI := oneHandleRelativeLambdaImageIsMulCommutative k hk
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨x, rfl⟩

/-- Every explicit `C`-versus-`ABD` relation belongs to the W214 interaction kernel. -/
theorem oneHandleBalancedCoreNeutralityInteractionToSource_range_le
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityInteractionToSource p k hk).range ≤
      oneHandleBalancedCoreNeutralityInteraction p k hk := by
  rintro q ⟨x, rfl⟩
  rw [oneHandleBalancedCoreNeutralityInteraction, MonoidHom.mem_ker]
  change oneHandleBalancedCoreNeutralitySourceFactor p k hk
    (oneHandleRelativeCModuloNeutralMk k hk x.1) = 1
  rw [oneHandleBalancedCoreNeutralitySourceFactor_mk]
  apply (oneHandleBalancedCoreNeutralityClassHom_eq_one_iff p k hk x.1).mpr
  exact oneHandleBalancedCoreOtherCoordinateSpan_le_coordinateSpan p k hk x.2

/-- Conversely, after quotienting neutral representatives, every interaction-kernel class
has a representative whose relaxed `C` shift lies in the `ABD` span. -/
theorem oneHandleBalancedCoreNeutralityInteraction_le_range
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    oneHandleBalancedCoreNeutralityInteraction p k hk ≤
      (oneHandleBalancedCoreNeutralityInteractionToSource p k hk).range := by
  intro q hq
  obtain ⟨x, rfl⟩ := oneHandleRelativeCModuloNeutralMk_surjective k hk q
  have hclass : oneHandleBalancedCoreNeutralityClassHom p k hk x = 1 := by
    rw [← oneHandleBalancedCoreNeutralitySourceFactor_mk]
    exact MonoidHom.mem_ker.mp hq
  have hxspan : oneHandleBalancedCoreRelativeShiftCRelaxed p k hk x ∈
      oneHandleBalancedCoreCoordinateSpan p k hk :=
    (oneHandleBalancedCoreNeutralityClassHom_eq_one_iff p k hk x).mp hclass
  rw [oneHandleBalancedCoreCoordinateSpan_eq_other_sup_C p k hk] at hxspan
  obtain ⟨o, ho, c, hc, hoc⟩ := Subgroup.mem_sup.mp hxspan
  obtain ⟨n, hnc⟩ := hc
  let ni := oneHandleNeutralRelativeInclusion (k - 1) (k + 1) (by omega) n
  let y : oneHandleRelativeLambdaImage (k - 1) (k + 1) := x * ni⁻¹
  have hni : oneHandleBalancedCoreRelativeShiftCRelaxed p k hk ni = c := by
    rw [oneHandleBalancedCoreRelativeShiftCRelaxed_inclusion]
    exact hnc
  have hyshift : oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y = o := by
    change oneHandleBalancedCoreRelativeShiftCRelaxed p k hk (x * ni⁻¹) = o
    rw [map_mul, map_inv, hni]
    rw [← hoc]
    group
  have hy : y ∈ oneHandleBalancedCoreNeutralityInteractionSource p k hk := by
    change oneHandleBalancedCoreRelativeShiftCRelaxed p k hk y ∈
      oneHandleBalancedCoreOtherCoordinateSpan p k hk
    rw [hyshift]
    exact ho
  refine ⟨⟨y, hy⟩, ?_⟩
  change oneHandleRelativeCModuloNeutralMk k hk y =
    oneHandleRelativeCModuloNeutralMk k hk x
  change oneHandleRelativeCModuloNeutralMk k hk (x * ni⁻¹) = _
  rw [map_mul, map_inv, oneHandleRelativeCModuloNeutralMk_neutral,
    inv_one, mul_one]

/-- The W214 interaction kernel is exactly the projected `C`-versus-`ABD` relation source. -/
theorem oneHandleBalancedCoreNeutralityInteraction_range_eq
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityInteractionToSource p k hk).range =
      oneHandleBalancedCoreNeutralityInteraction p k hk := by
  apply le_antisymm
  · exact oneHandleBalancedCoreNeutralityInteractionToSource_range_le p k hk
  · exact oneHandleBalancedCoreNeutralityInteraction_le_range p k hk

@[reducible] noncomputable def oneHandleRelativeCModuloNeutralIsMulCommutative
    (k : ℕ) (hk : 3 ≤ k) : IsMulCommutative (OneHandleRelativeCModuloNeutral k hk) := by
  refine ⟨⟨fun x y ↦ ?_⟩⟩
  obtain ⟨a, rfl⟩ := oneHandleRelativeCModuloNeutralMk_surjective k hk x
  obtain ⟨b, rfl⟩ := oneHandleRelativeCModuloNeutralMk_surjective k hk y
  rw [← map_mul, ← map_mul]
  exact congrArg (oneHandleRelativeCModuloNeutralMk k hk)
    (Subtype.ext (mul_comm_lambdaImage k hk a.2.1 b.2.1))

noncomputable instance oneHandleBalancedCoreNeutralityInteractionToSource_range_normal
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (oneHandleBalancedCoreNeutralityInteractionToSource p k hk).range.Normal := by
  letI := oneHandleRelativeCModuloNeutralIsMulCommutative k hk
  infer_instance

/-- Final exact form: the neutrality cokernel is the relative-`C`-mod-neutral source modulo
the image of literal `C`-versus-`ABD` relations. -/
noncomputable def oneHandleBalancedCoreNeutralityCokernelEquivInteraction
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k) :
    (OneHandleRelativeCModuloNeutral k hk ⧸
        (oneHandleBalancedCoreNeutralityInteractionToSource p k hk).range) ≃*
      OneHandleBalancedCoreNeutralityCokernel p k hk := by
  exact (QuotientGroup.quotientMulEquivOfEq
    (oneHandleBalancedCoreNeutralityInteraction_range_eq p k hk)).trans
      (oneHandleBalancedCoreNeutralityCokernelEquiv p k hk)

#print axioms oneHandleBalancedCoreOtherCoordinateSpan
#print axioms oneHandleBalancedCoreCoordinateSpan_eq_other_sup_C
#print axioms oneHandleBalancedCoreNeutralityInteractionSource
#print axioms oneHandleBalancedCoreNeutralityInteractionToSource
#print axioms oneHandleRelativeCModuloNeutralMk_neutral
#print axioms oneHandleBalancedCoreNeutralityInteractionToSource_range_le
#print axioms oneHandleBalancedCoreNeutralityInteraction_le_range
#print axioms oneHandleBalancedCoreNeutralityInteraction_range_eq
#print axioms oneHandleRelativeCModuloNeutralIsMulCommutative
#print axioms oneHandleBalancedCoreNeutralityInteractionToSource_range_normal
#print axioms oneHandleBalancedCoreNeutralityCokernelEquivInteraction

end
end GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
