/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralRankBound

/-!
# The class-seven neutral target as an exact parity quotient

W290 produced a surjection from the two-bit parity plane to the standard neutral target.
This module computes its kernel: it is exactly the range of the standard balanced parity
interaction row.  Hence the target is the quotient of `(ZMod 2)^2` by that explicit row range.

The target cardinal times the interaction-range cardinal is four.  In particular the target
is trivial exactly when the parity row fills the whole plane.  No spanning claim is made.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralParityQuotient

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralCoordinateBound
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityParity
open scoped IsMulCommutative

private abbrev CoordinatePlane :=
  Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

private abbrev ParityPlane :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

private abbrev StandardInteractionRange : Subgroup CoordinatePlane :=
  (oneHandleBalancedCoreNeutralityCoordinateRow
    oneHandleStandardBalancedPoint 6 (by omega)).range

private abbrev StandardParityInteractionRange : Subgroup ParityPlane :=
  (oneHandleBalancedCoreNeutralityParityRow
    oneHandleStandardBalancedPoint 6 (by omega)).range

@[simp] theorem oneHandleC7StandardNeutralityParityFactor_coordinateParity
    (z : CoordinatePlane) :
    oneHandleC7StandardNeutralityParityFactor (coordinateParity z) =
      oneHandleC7StandardNeutralityCokernelEquivCoordinates
        (QuotientGroup.mk' StandardInteractionRange z) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective coordinateParity
    coordinateParity_surjective
  have he : e (QuotientGroup.mk' coordinateParity.ker z) =
      coordinateParity z := by
    exact QuotientGroup.kerLift_mk coordinateParity z
  have hsymm : e.symm (coordinateParity z) =
      QuotientGroup.mk' coordinateParity.ker z :=
    e.symm_apply_eq.mpr he.symm
  change oneHandleC7StandardNeutralityCokernelEquivCoordinates
    (standardParityQuotientMap (e.symm (coordinateParity z))) = _
  rw [hsymm, standardParityQuotientMap, QuotientGroup.map_mk']
  rfl

private theorem mem_standardInteractionRange_iff_parity_mem
    (z : CoordinatePlane) :
    z ∈ StandardInteractionRange ↔
      coordinateParity z ∈ StandardParityInteractionRange := by
  change z ∈
      (oneHandleBalancedCoreNeutralityCoordinateRow
        oneHandleStandardBalancedPoint 6 (by omega)).range ↔
    coordinateParity z ∈
      (oneHandleBalancedCoreNeutralityParityRow
        oneHandleStandardBalancedPoint 6 (by omega)).range
  rw [oneHandleBalancedCoreNeutralityParityRow_range_eq_map]
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨y, hy, heq⟩
    have hker : y * z⁻¹ ∈ coordinateParity.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    have hdiff : y * z⁻¹ ∈ StandardInteractionRange :=
      coordinateParity_ker_le_standardInteractionRange hker
    have hz_eq : z = (y * z⁻¹)⁻¹ * y := by group
    rw [hz_eq]
    exact StandardInteractionRange.mul_mem
      (StandardInteractionRange.inv_mem hdiff) hy

theorem oneHandleC7StandardNeutralityParityFactor_eq_one_iff
    (p : ParityPlane) :
    oneHandleC7StandardNeutralityParityFactor p = 1 ↔
      p ∈ StandardParityInteractionRange := by
  obtain ⟨z, rfl⟩ := coordinateParity_surjective p
  rw [oneHandleC7StandardNeutralityParityFactor_coordinateParity]
  have heq :
      oneHandleC7StandardNeutralityCokernelEquivCoordinates
          (QuotientGroup.mk' StandardInteractionRange z) = 1 ↔
        QuotientGroup.mk' StandardInteractionRange z = 1 := by
    constructor
    · intro h
      apply oneHandleC7StandardNeutralityCokernelEquivCoordinates.injective
      simpa using h
    · intro h
      rw [h]
      exact map_one _
  rw [heq]
  constructor
  · intro h
    exact (mem_standardInteractionRange_iff_parity_mem z).mp
      ((QuotientGroup.eq_one_iff _).mp h)
  · intro h
    exact (QuotientGroup.eq_one_iff _).mpr
      ((mem_standardInteractionRange_iff_parity_mem z).mpr h)

theorem oneHandleC7StandardNeutralityParityFactor_ker :
    oneHandleC7StandardNeutralityParityFactor.ker =
      StandardParityInteractionRange := by
  ext p
  rw [MonoidHom.mem_ker,
    oneHandleC7StandardNeutralityParityFactor_eq_one_iff]

noncomputable def oneHandleC7StandardNeutralityCokernelEquivParity :
    (ParityPlane ⧸ StandardParityInteractionRange) ≃*
      OneHandleC7StandardNeutralityCokernel :=
  (QuotientGroup.quotientMulEquivOfEq
      oneHandleC7StandardNeutralityParityFactor_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      oneHandleC7StandardNeutralityParityFactor
      oneHandleC7StandardNeutralityParityFactor_surjective)

theorem natCard_standardNeutrality_mul_parityInteraction_eq_four :
    Nat.card OneHandleC7StandardNeutralityCokernel *
        Nat.card StandardParityInteractionRange = 4 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    StandardParityInteractionRange
  rw [Nat.card_congr
    oneHandleC7StandardNeutralityCokernelEquivParity.toEquiv] at h
  simpa [ParityPlane, Nat.card_prod, Nat.card_zmod] using h.symm

theorem oneHandleC7StandardNeutralityCokernel_trivial_iff_parityRow_range_eq_top :
    Subsingleton OneHandleC7StandardNeutralityCokernel ↔
      StandardParityInteractionRange = ⊤ := by
  constructor
  · intro hsub
    apply top_unique
    intro p _
    rw [← oneHandleC7StandardNeutralityParityFactor_eq_one_iff]
    exact Subsingleton.elim _ _
  · intro htop
    constructor
    intro x y
    obtain ⟨px, rfl⟩ :=
      oneHandleC7StandardNeutralityParityFactor_surjective x
    obtain ⟨py, rfl⟩ :=
      oneHandleC7StandardNeutralityParityFactor_surjective y
    have hpx : oneHandleC7StandardNeutralityParityFactor px = 1 :=
      (oneHandleC7StandardNeutralityParityFactor_eq_one_iff px).mpr (by
        rw [htop]
        exact Subgroup.mem_top _)
    have hpy : oneHandleC7StandardNeutralityParityFactor py = 1 :=
      (oneHandleC7StandardNeutralityParityFactor_eq_one_iff py).mpr (by
        rw [htop]
        exact Subgroup.mem_top _)
    rw [hpx, hpy]

#print axioms oneHandleC7StandardNeutralityParityFactor_coordinateParity
#print axioms oneHandleC7StandardNeutralityParityFactor_eq_one_iff
#print axioms oneHandleC7StandardNeutralityParityFactor_ker
#print axioms oneHandleC7StandardNeutralityCokernelEquivParity
#print axioms natCard_standardNeutrality_mul_parityInteraction_eq_four
#print axioms oneHandleC7StandardNeutralityCokernel_trivial_iff_parityRow_range_eq_top

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralParityQuotient
