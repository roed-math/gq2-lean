/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingCriterion

/-!
# The compact obstruction coset

Changing a legal compact lift changes the ordinary class-seven obstruction by the inverse
of a value of the compact connecting homomorphism.  Thus, relative to any fixed lift, every
attained packet obstruction lies in one coset of the connecting image.

The reverse inclusion is precisely a realization question.  This module records the exact
criterion: the finite packet-obstruction set is the whole coset if and only if every value of
the connecting homomorphism is attained by the difference from the reference lift to another
legal lift.  Neither realization nor vanishing is asserted.
-/
namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactObstructionCoset

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeFiniteLiftIndependence
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenFinitePacket
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingCriterion

def compactConnectingObstructionCoset
    (E : OneHandleC7RelativeLift) : Set OneHandleC7StandardRelativeCokernel :=
  {x | ∃ D : OneHandleCompactKernelCorrection,
    x = (oneHandleCompactConnectingHom D)⁻¹ *
      oneHandleC7StandardRelativeObstruction E}

theorem relativeObstruction_mem_compactConnectingObstructionCoset
    (E F : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeObstruction F ∈
      compactConnectingObstructionCoset E := by
  exact ⟨realizedCompactKernelDifference E F,
    relativeObstruction_eq_connecting_inv_mul E F⟩

theorem compactPacketObstruction_mem_compactConnectingObstructionCoset
    (E : OneHandleC7RelativeLift) (P : OneHandleC7CompactLevelSevenPacket) :
    compactPacketObstruction P ∈ compactConnectingObstructionCoset E := by
  rw [compactPacketObstruction]
  exact relativeObstruction_mem_compactConnectingObstructionCoset E _

theorem compactPacketObstructionValues_subset_connectingCoset
    (E : OneHandleC7RelativeLift) :
    (↑compactPacketObstructionValues :
        Set OneHandleC7StandardRelativeCokernel) ⊆
      compactConnectingObstructionCoset E := by
  intro x hx
  rw [Finset.mem_coe, mem_compactPacketObstructionValues_iff] at hx
  obtain ⟨P, rfl⟩ := hx
  exact compactPacketObstruction_mem_compactConnectingObstructionCoset E P

theorem referenceObstruction_mem_compactConnectingObstructionCoset
    (E : OneHandleC7RelativeLift) :
    oneHandleC7StandardRelativeObstruction E ∈
      compactConnectingObstructionCoset E := by
  refine ⟨1, ?_⟩
  simp

def OneHandleCompactConnectingRealizedAt
    (E : OneHandleC7RelativeLift) : Prop :=
  ∀ D : OneHandleCompactKernelCorrection,
    ∃ F : OneHandleC7RelativeLift,
      oneHandleCompactConnectingHom (realizedCompactKernelDifference E F) =
        oneHandleCompactConnectingHom D

theorem compactPacketObstructionValues_eq_connectingCoset_iff
    (E : OneHandleC7RelativeLift) :
    (↑compactPacketObstructionValues :
        Set OneHandleC7StandardRelativeCokernel) =
      compactConnectingObstructionCoset E ↔
        OneHandleCompactConnectingRealizedAt E := by
  constructor
  · intro hset D
    have hx : (oneHandleCompactConnectingHom D)⁻¹ *
        oneHandleC7StandardRelativeObstruction E ∈
          (↑compactPacketObstructionValues :
            Set OneHandleC7StandardRelativeCokernel) := by
      rw [hset]
      exact ⟨D, rfl⟩
    rw [Finset.mem_coe, mem_compactPacketObstructionValues_iff] at hx
    obtain ⟨P, hP⟩ := hx
    let F := compactPacketRepresentative P
    refine ⟨F, ?_⟩
    have hPF : compactPacketObstruction P =
        oneHandleC7StandardRelativeObstruction F :=
      compactPacketObstruction_eq_lift P F
        (compactPacketRepresentative_data P)
    have hmul :
        (oneHandleCompactConnectingHom
          (realizedCompactKernelDifference E F))⁻¹ *
            oneHandleC7StandardRelativeObstruction E =
          (oneHandleCompactConnectingHom D)⁻¹ *
            oneHandleC7StandardRelativeObstruction E := by
      rw [← relativeObstruction_eq_connecting_inv_mul E F,
        ← hPF, hP]
    exact inv_injective (mul_right_cancel hmul)
  · intro hreal
    apply Set.Subset.antisymm
    · exact compactPacketObstructionValues_subset_connectingCoset E
    · intro x hx
      obtain ⟨D, rfl⟩ := hx
      obtain ⟨F, hF⟩ := hreal D
      rw [← hF, ← relativeObstruction_eq_connecting_inv_mul E F]
      rw [Finset.mem_coe, mem_compactPacketObstructionValues_iff]
      let P : OneHandleC7CompactLevelSevenPacket :=
        ⟨compactLevelSevenData F, ⟨F, rfl⟩⟩
      refine ⟨P, ?_⟩
      exact compactPacketObstruction_eq_lift P F rfl

#print axioms compactConnectingObstructionCoset
#print axioms relativeObstruction_mem_compactConnectingObstructionCoset
#print axioms compactPacketObstruction_mem_compactConnectingObstructionCoset
#print axioms compactPacketObstructionValues_subset_connectingCoset
#print axioms referenceObstruction_mem_compactConnectingObstructionCoset
#print axioms OneHandleCompactConnectingRealizedAt
#print axioms compactPacketObstructionValues_eq_connectingCoset_iff

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactObstructionCoset
