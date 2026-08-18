/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSearch

/-!
# The neutral connecting homomorphism at class seven

The kernel of the ordinary compact connecting map acts transitively on every nonempty
connecting fiber. Its relative shift lies in the relaxed coordinate span, so it has a second
canonical image in the neutral-C cokernel.

The neutral obstruction transforms by the inverse of this homomorphism. Consequently, once
one ordinary correction is fixed, full W6 correctability is exactly membership of its neutral
obstruction in the finite neutral connecting image. This replaces the filtered finite search
of W286 by a second finite homomorphism image problem; it does not assert membership.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralConnecting

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSearch

abbrev OneHandleCompactConnectingKernel :=
  oneHandleCompactConnectingHom.ker

theorem compactConnectingKernel_shift_mem_relaxed
    (K : OneHandleCompactConnectingKernel) :
    compactKernelRelativeShiftHom K.1 ∈
      oneHandleStandardRelativeRelaxedCoordinateSpan := by
  apply (QuotientGroup.eq_one_iff _).mp
  exact MonoidHom.mem_ker.mp K.2

noncomputable def compactConnectingKernelRelaxedShiftHom :
    OneHandleCompactConnectingKernel →*
      oneHandleStandardRelativeRelaxedCoordinateSpan where
  toFun K := ⟨compactKernelRelativeShiftHom K.1,
    compactConnectingKernel_shift_mem_relaxed K⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' K L := by
    apply Subtype.ext
    simp

noncomputable def oneHandleCompactNeutralConnectingHom :
    OneHandleCompactConnectingKernel →*
      OneHandleC7StandardNeutralityCokernel :=
  (QuotientGroup.mk' oneHandleC7StandardNeutralitySubgroup).comp
    compactConnectingKernelRelaxedShiftHom

theorem compactKernelCorrectionLift_mul_target
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (K : OneHandleCompactConnectingKernel) :
    oneHandleC7RelativeTarget (compactKernelCorrectionLift E (D * K.1)) =
      (compactKernelRelativeShiftHom K.1)⁻¹ *
        oneHandleC7RelativeTarget (compactKernelCorrectionLift E D) := by
  let F := compactKernelCorrectionLift E D
  let G := compactKernelCorrectionLift E (D * K.1)
  have hdiff :
      (realizedCompactKernelDifference F G).1 = K.1.1 := by
    change (relativeLiftToDirect F)⁻¹ * relativeLiftToDirect G = K.1.1
    rw [compactKernelCorrectionLift_toDirect,
      compactKernelCorrectionLift_toDirect]
    simp only [Subgroup.coe_mul]
    group
  have hdiff' : realizedCompactKernelDifference F G = K.1 :=
    Subtype.ext hdiff
  rw [relativeTarget_eq_connectingShift_inv_mul F G]
  rw [hdiff']

theorem compactKernelCorrectionLift_mul_connects
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E)
    (K : OneHandleCompactConnectingKernel) :
    oneHandleCompactConnectingHom (D * K.1) =
      oneHandleC7StandardRelativeObstruction E := by
  rw [map_mul, hD, MonoidHom.mem_ker.mp K.2, mul_one]

theorem neutralityObstruction_mul_connectingKernel
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E)
    (K : OneHandleCompactConnectingKernel) :
    oneHandleC7StandardNeutralityObstruction
        (compactKernelCorrectionLift E (D * K.1))
        (compactKernelCorrectionLift_relaxed E (D * K.1)
          (compactKernelCorrectionLift_mul_connects E D hD K)) =
      (oneHandleCompactNeutralConnectingHom K)⁻¹ *
        oneHandleC7StandardNeutralityObstruction
          (compactKernelCorrectionLift E D)
          (compactKernelCorrectionLift_relaxed E D hD) := by
  let s : oneHandleStandardRelativeRelaxedCoordinateSpan :=
    compactConnectingKernelRelaxedShiftHom K
  let t : oneHandleStandardRelativeRelaxedCoordinateSpan :=
    ⟨oneHandleC7RelativeTarget (compactKernelCorrectionLift E D),
      compactKernelCorrectionLift_relaxed E D hD⟩
  have heq :
      (⟨oneHandleC7RelativeTarget
          (compactKernelCorrectionLift E (D * K.1)),
        compactKernelCorrectionLift_relaxed E (D * K.1)
          (compactKernelCorrectionLift_mul_connects E D hD K)⟩ :
          oneHandleStandardRelativeRelaxedCoordinateSpan) = s⁻¹ * t := by
    apply Subtype.ext
    exact compactKernelCorrectionLift_mul_target E D K
  change QuotientGroup.mk' oneHandleC7StandardNeutralitySubgroup _ = _
  rw [heq]
  rw [map_mul, map_inv]
  rfl

noncomputable def compactNeutralConnectingValues :
    Finset OneHandleC7StandardNeutralityCokernel := by
  classical
  letI := Fintype.ofFinite OneHandleCompactConnectingKernel
  exact Finset.univ.image oneHandleCompactNeutralConnectingHom

theorem mem_compactNeutralConnectingValues_iff
    (x : OneHandleC7StandardNeutralityCokernel) :
    x ∈ compactNeutralConnectingValues ↔
      ∃ K : OneHandleCompactConnectingKernel,
        oneHandleCompactNeutralConnectingHom K = x := by
  classical
  rw [compactNeutralConnectingValues, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]

theorem oneHandleW6Correctable_iff_neutrality_mem_connectingValues
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection)
    (hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E) :
    OneHandleW6Correctable ↔
      oneHandleC7StandardNeutralityObstruction
          (compactKernelCorrectionLift E D)
          (compactKernelCorrectionLift_relaxed E D hD) ∈
        compactNeutralConnectingValues := by
  rw [← nonempty_compactKernelFullSolution_iff_oneHandleW6Correctable E]
  constructor
  · rintro ⟨S⟩
    let K0 : OneHandleCompactKernelCorrection := D⁻¹ * S.correction
    have hK0 : oneHandleCompactConnectingHom K0 = 1 := by
      dsimp [K0]
      rw [map_mul, map_inv, hD, S.connects]
      group
    let K : OneHandleCompactConnectingKernel :=
      ⟨K0, MonoidHom.mem_ker.mpr hK0⟩
    rw [mem_compactNeutralConnectingValues_iff]
    refine ⟨K, ?_⟩
    have hmul : D * K.1 = S.correction := by
      apply Subtype.ext
      dsimp [K, K0]
      change D.1 * (D.1⁻¹ * S.correction.1) = S.correction.1
      group
    have hcoc := neutralityObstruction_mul_connectingKernel E D hD K
    have hleft : oneHandleC7StandardNeutralityObstruction
        (compactKernelCorrectionLift E (D * K.1))
        (compactKernelCorrectionLift_relaxed E (D * K.1)
          (compactKernelCorrectionLift_mul_connects E D hD K)) = 1 := by
      simpa only [hmul] using S.neutral
    rw [hleft] at hcoc
    exact inv_mul_eq_one.mp hcoc.symm
  · intro hmem
    rw [mem_compactNeutralConnectingValues_iff] at hmem
    obtain ⟨K, hK⟩ := hmem
    let hconnect := compactKernelCorrectionLift_mul_connects E D hD K
    refine ⟨⟨D * K.1, hconnect, ?_⟩⟩
    rw [neutralityObstruction_mul_connectingKernel E D hD K, hK]
    group

#print axioms compactConnectingKernel_shift_mem_relaxed
#print axioms compactConnectingKernelRelaxedShiftHom
#print axioms oneHandleCompactNeutralConnectingHom
#print axioms compactKernelCorrectionLift_mul_target
#print axioms compactKernelCorrectionLift_mul_connects
#print axioms neutralityObstruction_mul_connectingKernel
#print axioms compactNeutralConnectingValues
#print axioms mem_compactNeutralConnectingValues_iff
#print axioms oneHandleW6Correctable_iff_neutrality_mem_connectingValues

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactNeutralConnecting
