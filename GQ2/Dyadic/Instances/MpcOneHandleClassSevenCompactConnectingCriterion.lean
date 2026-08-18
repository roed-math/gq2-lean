/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom

/-!
# Exact finite criteria for the compact connecting homomorphism

W278 isolated the homomorphism through which legal compact-lift changes alter the ordinary
class-seven obstruction.  This module identifies its vanishing with one concrete range
inclusion: every direct correction of zero compact cost must shift into the four-row relaxed
relative span.

The source is finite, so the image is also recorded as an explicit finite set.  Vanishing is
equivalent to that set being the singleton identity.  These are exact reformulations, not a
proof of the remaining range inclusion.
-/
namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingCriterion

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleDirectFiniteSpan
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom

def OneHandleCompactKernelCovered : Prop :=
  ∀ D : OneHandleCompactKernelCorrection,
    compactKernelRelativeShiftHom D ∈
      oneHandleStandardRelativeRelaxedCoordinateSpan

theorem compactConnectingTrivial_iff_kernelCovered :
    OneHandleCompactConnectingTrivial ↔
      OneHandleCompactKernelCovered := by
  constructor
  · intro h D
    apply (QuotientGroup.eq_one_iff _).mp
    exact h D
  · intro h D
    apply (QuotientGroup.eq_one_iff _).mpr
    exact h D

theorem compactConnectingTrivial_iff_range_le_relaxed :
    OneHandleCompactConnectingTrivial ↔
      compactKernelRelativeShiftHom.range ≤
        oneHandleStandardRelativeRelaxedCoordinateSpan := by
  rw [compactConnectingTrivial_iff_kernelCovered]
  constructor
  · rintro h _ ⟨D, rfl⟩
    exact h D
  · intro h D
    exact h ⟨D, rfl⟩

theorem compactConnectingTrivial_iff_direct_kernel_shift_mem :
    OneHandleCompactConnectingTrivial ↔
      ∀ D : OneHandleDirectLevelCorrection 6,
        ∀ hD : oneHandleCompactCostHom D = 1,
          compactKernelRelativeShiftHom
              ⟨D, MonoidHom.mem_ker.mpr hD⟩ ∈
            oneHandleStandardRelativeRelaxedCoordinateSpan := by
  rw [compactConnectingTrivial_iff_kernelCovered]
  constructor
  · intro h D hD
    exact h ⟨D, MonoidHom.mem_ker.mpr hD⟩
  · intro h D
    exact h D.1 (MonoidHom.mem_ker.mp D.2)

noncomputable def compactConnectingValues :
    Finset OneHandleC7StandardRelativeCokernel := by
  classical
  letI := Fintype.ofFinite OneHandleCompactKernelCorrection
  exact Finset.univ.image oneHandleCompactConnectingHom

theorem mem_compactConnectingValues_iff
    (x : OneHandleC7StandardRelativeCokernel) :
    x ∈ compactConnectingValues ↔
      ∃ D : OneHandleCompactKernelCorrection,
        oneHandleCompactConnectingHom D = x := by
  classical
  rw [compactConnectingValues, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]

theorem compactConnectingValues_nonempty :
    compactConnectingValues.Nonempty := by
  refine ⟨1, (mem_compactConnectingValues_iff 1).mpr ?_⟩
  exact ⟨1, map_one oneHandleCompactConnectingHom⟩

theorem compactConnectingTrivial_iff_values_eq_singleton :
    OneHandleCompactConnectingTrivial ↔ compactConnectingValues = {1} := by
  constructor
  · intro h
    ext x
    rw [mem_compactConnectingValues_iff]
    constructor
    · rintro ⟨D, rfl⟩
      simp [h D]
    · intro hx
      simp only [Finset.mem_singleton] at hx
      refine ⟨1, ?_⟩
      subst x
      exact map_one oneHandleCompactConnectingHom
  · intro h D
    have hmem : oneHandleCompactConnectingHom D ∈
        compactConnectingValues :=
      (mem_compactConnectingValues_iff _).mpr ⟨D, rfl⟩
    rw [h] at hmem
    simp at hmem
    exact hmem

#print axioms OneHandleCompactKernelCovered
#print axioms compactConnectingTrivial_iff_kernelCovered
#print axioms compactConnectingTrivial_iff_range_le_relaxed
#print axioms compactConnectingTrivial_iff_direct_kernel_shift_mem
#print axioms compactConnectingValues
#print axioms mem_compactConnectingValues_iff
#print axioms compactConnectingTrivial_iff_values_eq_singleton

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingCriterion

