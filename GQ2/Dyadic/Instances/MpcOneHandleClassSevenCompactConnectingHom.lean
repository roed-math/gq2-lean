/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactCostFiber

/-!
# The compact-kernel connecting homomorphism

The direct class-seven shift has a compact cost obtained by forgetting the one-handle factor.
Its kernel therefore consists exactly of direct corrections whose shift is purely relative.
This module maps that kernel into the ordinary relative cokernel and proves the resulting
connecting-homomorphism formula for the obstruction of any two legal compact lifts.

Consequently, if the connecting homomorphism vanishes, every attained compact packet has the
same ordinary obstruction and the finite obstruction-value set is a singleton.  No vanishing
claim is made here, nor does ordinary relative coverage impose the separate neutral-C condition.
-/
namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleDirectSuccessor
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeFiniteLiftIndependence
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeEquation
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenFinitePacket
open GQ2.Roe.Labute

private abbrev H := DM 2 1

noncomputable def oneHandleCompactCostHom :
    OneHandleDirectLevelCorrection 6 →* levelQuot (DM 2 0 : Type) 7 :=
  (dmForgetHandlesLevelSeven.comp (zLayer H 6).subtype).comp
    (oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega))

abbrev OneHandleCompactKernelCorrection := oneHandleCompactCostHom.ker

noncomputable def compactKernelRelativeShiftHom :
    OneHandleCompactKernelCorrection →* oneHandleRelativeZLayer 6 where
  toFun D := ⟨(oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega) D.1).1,
    (oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega) D.1).2,
    MonoidHom.mem_ker.mpr D.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' D F := by
    apply Subtype.ext
    simp

noncomputable def oneHandleCompactConnectingHom :
    OneHandleCompactKernelCorrection →* OneHandleC7StandardRelativeCokernel :=
  (QuotientGroup.mk' oneHandleStandardRelativeRelaxedCoordinateSpan).comp
    compactKernelRelativeShiftHom

theorem directFiniteLiftDifference_mem_compactKernel
    (E F : OneHandleC7RelativeLift) :
    directFiniteLiftDifference E F ∈ oneHandleCompactCostHom.ker := by
  rw [MonoidHom.mem_ker]
  change dmForgetHandlesLevelSeven
      (oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)
        (directFiniteLiftDifference E F)).1 = 1
  rw [oneHandleDirectLevelShiftHom_apply, directFiniteLiftDifference_shift,
    map_mul, map_inv]
  have hE := MonoidHom.mem_ker.mp E.residual_mem_ker
  have hF := MonoidHom.mem_ker.mp F.residual_mem_ker
  rw [hE, hF, inv_one, one_mul]

noncomputable def realizedCompactKernelDifference
    (E F : OneHandleC7RelativeLift) : OneHandleCompactKernelCorrection :=
  ⟨directFiniteLiftDifference E F,
    directFiniteLiftDifference_mem_compactKernel E F⟩

theorem compactKernelRelativeShift_realized
    (E F : OneHandleC7RelativeLift) :
    (compactKernelRelativeShiftHom (realizedCompactKernelDifference E F)).1 =
      E.residual⁻¹ * F.residual := by
  change (oneHandleDirectLevelShiftHom oneHandleW6Mark 6 (by omega)
      (directFiniteLiftDifference E F)).1 = _
  rw [oneHandleDirectLevelShiftHom_apply,
    directFiniteLiftDifference_shift]

theorem relativeTarget_eq_connectingShift_inv_mul
    (E F : OneHandleC7RelativeLift) :
    oneHandleC7RelativeTarget F =
      (compactKernelRelativeShiftHom
        (realizedCompactKernelDifference E F))⁻¹ *
          oneHandleC7RelativeTarget E := by
  apply Subtype.ext
  change F.residual⁻¹ =
    (compactKernelRelativeShiftHom
      (realizedCompactKernelDifference E F)).1⁻¹ * E.residual⁻¹
  rw [compactKernelRelativeShift_realized]
  group

theorem relativeObstruction_eq_connecting_inv_mul
    (E F : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeObstruction F =
      (oneHandleCompactConnectingHom
        (realizedCompactKernelDifference E F))⁻¹ *
          oneHandleC7StandardRelativeObstruction E := by
  change QuotientGroup.mk' oneHandleStandardRelativeRelaxedCoordinateSpan
      (oneHandleC7RelativeTarget F) = _
  rw [relativeTarget_eq_connectingShift_inv_mul E F, map_mul, map_inv]
  rfl

def OneHandleCompactConnectingTrivial : Prop :=
  ∀ D : OneHandleCompactKernelCorrection, oneHandleCompactConnectingHom D = 1

theorem relativeObstruction_eq_of_connectingTrivial
    (h : OneHandleCompactConnectingTrivial) (E F : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeObstruction E =
      oneHandleC7StandardRelativeObstruction F := by
  rw [relativeObstruction_eq_connecting_inv_mul E F,
    h (realizedCompactKernelDifference E F), inv_one, one_mul]

theorem relativeRowEquation_iff_of_connectingTrivial
    (h : OneHandleCompactConnectingTrivial) (E F : OneHandleC7RelativeLift) :
    OneHandleC7StandardRelativeRowEquation E ↔
      OneHandleC7StandardRelativeRowEquation F := by
  rw [← standardRelativeTarget_mem_relaxed_iff_rowEquation,
    ← standardRelativeObstruction_eq_one_iff,
    ← standardRelativeTarget_mem_relaxed_iff_rowEquation,
    ← standardRelativeObstruction_eq_one_iff,
    relativeObstruction_eq_of_connectingTrivial h E F]

theorem compactPacketObstructionValues_eq_singleton_of_connectingTrivial
    (h : OneHandleCompactConnectingTrivial) (E : OneHandleC7RelativeLift) :
    compactPacketObstructionValues =
      {oneHandleC7StandardRelativeObstruction E} := by
  classical
  ext x
  rw [mem_compactPacketObstructionValues_iff]
  constructor
  · rintro ⟨P, rfl⟩
    simp only [Finset.mem_singleton]
    exact relativeObstruction_eq_of_connectingTrivial h _ E
  · intro hx
    simp only [Finset.mem_singleton] at hx
    let P : OneHandleC7CompactLevelSevenPacket :=
      ⟨compactLevelSevenData E, ⟨E, rfl⟩⟩
    refine ⟨P, ?_⟩
    exact (relativeObstruction_eq_of_connectingTrivial h _ E).trans hx.symm

#print axioms oneHandleCompactCostHom
#print axioms compactKernelRelativeShiftHom
#print axioms oneHandleCompactConnectingHom
#print axioms directFiniteLiftDifference_mem_compactKernel
#print axioms compactKernelRelativeShift_realized
#print axioms relativeObstruction_eq_connecting_inv_mul
#print axioms relativeObstruction_eq_of_connectingTrivial
#print axioms relativeRowEquation_iff_of_connectingTrivial
#print axioms compactPacketObstructionValues_eq_singleton_of_connectingTrivial

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
