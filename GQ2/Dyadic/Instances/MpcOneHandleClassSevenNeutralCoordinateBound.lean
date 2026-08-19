/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTargetRank
import GQ2.Dyadic.Instances.MpcBalancedNeutralityParity

/-!
# Coordinate bound for the class-seven neutral target

The standard class-seven neutral cokernel is the generic balanced neutral cokernel at the
standard point.  Its raw model is a quotient of `(ZMod 4)^2`.  Because W288 proved the target
has exponent two, the coordinate factor descends further through parity.  Thus the target is
a quotient of `(ZMod 2)^2`, has at most four elements, and has `F₂`-dimension at most two.

This does not compute the remaining neutral connecting image.  It reduces that computation
from an abstract finite target to at most two parity coordinates.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralCoordinateBound

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralTarget
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateGenerators
open GQ2.Dyadic.Instances.MpcBalancedNeutralityParity
open scoped IsMulCommutative

theorem oneHandleC7StandardNeutralitySubgroup_eq_balanced :
    oneHandleC7StandardNeutralitySubgroup =
      oneHandleBalancedCoreNeutralitySubgroup
        oneHandleStandardBalancedPoint 6 (by omega) := by
  unfold oneHandleC7StandardNeutralitySubgroup
  unfold oneHandleBalancedCoreNeutralitySubgroup
  unfold oneHandleStandardRelativeRelaxedCoordinateSpan
  rw [standardRelativeCoordinateSpan_eq_balanced]

noncomputable def oneHandleC7StandardNeutralityCokernelEquivBalanced :
    OneHandleC7StandardNeutralityCokernel ≃*
      OneHandleBalancedCoreNeutralityCokernel
        oneHandleStandardBalancedPoint 6 (by omega) :=
  QuotientGroup.quotientMulEquivOfEq
    oneHandleC7StandardNeutralitySubgroup_eq_balanced

noncomputable def oneHandleC7StandardNeutralityCokernelEquivCoordinates :
    ((Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ⧸
        (oneHandleBalancedCoreNeutralityCoordinateRow
          oneHandleStandardBalancedPoint 6 (by omega)).range) ≃*
      OneHandleC7StandardNeutralityCokernel :=
  (oneHandleBalancedCoreNeutralityCokernelEquivCoordinates
      oneHandleStandardBalancedPoint 6 (by omega)).trans
    oneHandleC7StandardNeutralityCokernelEquivBalanced.symm

theorem natCard_oneHandleC7StandardNeutralityCokernel_dvd_sixteen :
    Nat.card OneHandleC7StandardNeutralityCokernel ∣ 16 := by
  rw [Nat.card_congr oneHandleC7StandardNeutralityCokernelEquivBalanced.toEquiv]
  exact natCard_oneHandleBalancedCoreNeutralityCokernel_dvd_sixteen
    oneHandleStandardBalancedPoint 6 (by omega)

private abbrev CoordinatePlane :=
  Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

private abbrev ParityPlane :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

private abbrev StandardInteractionRange : Subgroup CoordinatePlane :=
  (oneHandleBalancedCoreNeutralityCoordinateRow
    oneHandleStandardBalancedPoint 6 (by omega)).range

theorem standardInteractionRange_contains_coordinate_square
    (z : CoordinatePlane) : z ^ 2 ∈ StandardInteractionRange := by
  change z ^ 2 ∈
    (oneHandleBalancedCoreNeutralityCoordinateRow
      oneHandleStandardBalancedPoint 6 (by omega)).range
  rw [oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker,
    MonoidHom.mem_ker, map_pow]
  have hsquare := oneHandleC7StandardNeutralityCokernel_sq
    (oneHandleC7StandardNeutralityCokernelEquivBalanced.symm
      (oneHandleBalancedCoreNeutralityCoordinateFactor
        oneHandleStandardBalancedPoint 6 (by omega) z))
  have himage := congrArg
    oneHandleC7StandardNeutralityCokernelEquivBalanced hsquare
  simpa using himage

theorem coordinateParity_ker_le_standardInteractionRange :
    coordinateParity.ker ≤ StandardInteractionRange := by
  intro z hz
  apply coordinate_mem_of_parity_one_of_squares StandardInteractionRange
    (standardInteractionRange_contains_coordinate_square
      oneHandleRelativeCoordinateU)
    (standardInteractionRange_contains_coordinate_square
      oneHandleRelativeCoordinateV)
  exact MonoidHom.mem_ker.mp hz

noncomputable def standardParityQuotientMap :
    (CoordinatePlane ⧸ coordinateParity.ker) →*
      (CoordinatePlane ⧸ StandardInteractionRange) :=
  QuotientGroup.map coordinateParity.ker StandardInteractionRange
    (MonoidHom.id CoordinatePlane) (by
      simpa only [Subgroup.comap_id] using
        coordinateParity_ker_le_standardInteractionRange)

theorem standardParityQuotientMap_surjective :
    Function.Surjective standardParityQuotientMap := by
  intro q
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective StandardInteractionRange q
  refine ⟨QuotientGroup.mk' coordinateParity.ker z, ?_⟩
  exact QuotientGroup.map_mk' _ _ _ _ z

noncomputable def oneHandleC7StandardNeutralityParityFactor :
    ParityPlane →* OneHandleC7StandardNeutralityCokernel :=
  oneHandleC7StandardNeutralityCokernelEquivCoordinates.toMonoidHom.comp
    (standardParityQuotientMap.comp
      (QuotientGroup.quotientKerEquivOfSurjective coordinateParity
        coordinateParity_surjective).symm.toMonoidHom)

theorem oneHandleC7StandardNeutralityParityFactor_surjective :
    Function.Surjective oneHandleC7StandardNeutralityParityFactor := by
  exact oneHandleC7StandardNeutralityCokernelEquivCoordinates.surjective.comp
    (standardParityQuotientMap_surjective.comp
      (QuotientGroup.quotientKerEquivOfSurjective coordinateParity
        coordinateParity_surjective).symm.surjective)

theorem natCard_oneHandleC7StandardNeutralityCokernel_le_four :
    Nat.card OneHandleC7StandardNeutralityCokernel ≤ 4 := by
  have hcard := Nat.card_le_card_of_surjective
    oneHandleC7StandardNeutralityParityFactor
    oneHandleC7StandardNeutralityParityFactor_surjective
  simpa [ParityPlane, Nat.card_prod, Nat.card_zmod] using hcard

private abbrev NeutralTarget := Additive OneHandleC7StandardNeutralityCokernel

noncomputable def oneHandleC7StandardNeutralityFinrank : ℕ := by
  letI : Module (ZMod 2) NeutralTarget :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact oneHandleC7StandardNeutralityCokernel_add_self v)
  exact Module.finrank (ZMod 2) NeutralTarget

theorem natCard_oneHandleC7StandardNeutralityCokernel_eq_pow_finrank :
    Nat.card OneHandleC7StandardNeutralityCokernel =
      2 ^ oneHandleC7StandardNeutralityFinrank := by
  letI : Module (ZMod 2) NeutralTarget :=
    AddCommGroup.zmodModule (fun v ↦ by
      rw [two_nsmul]
      exact oneHandleC7StandardNeutralityCokernel_add_self v)
  letI : FiniteDimensional (ZMod 2) NeutralTarget := Module.Finite.of_finite
  change Nat.card NeutralTarget = 2 ^ Module.finrank (ZMod 2) NeutralTarget
  simpa [ZMod.card] using
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := NeutralTarget))

theorem oneHandleC7StandardNeutralityFinrank_le_two :
    oneHandleC7StandardNeutralityFinrank ≤ 2 := by
  have hle : 2 ^ oneHandleC7StandardNeutralityFinrank ≤ 2 ^ 2 := by
    rw [← natCard_oneHandleC7StandardNeutralityCokernel_eq_pow_finrank]
    norm_num
    exact natCard_oneHandleC7StandardNeutralityCokernel_le_four
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle

#print axioms oneHandleC7StandardNeutralitySubgroup_eq_balanced
#print axioms oneHandleC7StandardNeutralityCokernelEquivBalanced
#print axioms oneHandleC7StandardNeutralityCokernelEquivCoordinates
#print axioms natCard_oneHandleC7StandardNeutralityCokernel_dvd_sixteen
#print axioms standardInteractionRange_contains_coordinate_square
#print axioms coordinateParity_ker_le_standardInteractionRange
#print axioms standardParityQuotientMap
#print axioms standardParityQuotientMap_surjective
#print axioms oneHandleC7StandardNeutralityParityFactor
#print axioms oneHandleC7StandardNeutralityParityFactor_surjective
#print axioms natCard_oneHandleC7StandardNeutralityCokernel_le_four
#print axioms oneHandleC7StandardNeutralityFinrank
#print axioms natCard_oneHandleC7StandardNeutralityCokernel_eq_pow_finrank
#print axioms oneHandleC7StandardNeutralityFinrank_le_two

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutralCoordinateBound
