/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution

/-!
# Explicit finite search sets for class seven

The connecting fiber is the finite set of compact-kernel corrections whose connecting value
equals a fixed reference obstruction.  Its nonemptiness is exactly ordinary relative
solvability.  Filtering this fiber by the neutral-C obstruction gives the finite set of full
correction candidates, whose nonemptiness is exactly W6 correctability.

This is a search interface, not a computation of either set.  It exposes the exact candidates
without proof-carrying solution records and keeps the ordinary and neutral filters separate.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSearch

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenFinitePacket
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingHom
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingCriterion
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactConnectingRealization
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSolution

noncomputable def compactConnectingFiber
    (E : OneHandleC7RelativeLift) :
    Finset OneHandleCompactKernelCorrection := by
  classical
  letI := Fintype.ofFinite OneHandleCompactKernelCorrection
  exact Finset.univ.filter fun D ↦
    oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E

theorem mem_compactConnectingFiber_iff
    (E : OneHandleC7RelativeLift) (D : OneHandleCompactKernelCorrection) :
    D ∈ compactConnectingFiber E ↔
      oneHandleCompactConnectingHom D =
        oneHandleC7StandardRelativeObstruction E := by
  classical
  simp [compactConnectingFiber]

theorem compactConnectingFiber_nonempty_iff
    (E : OneHandleC7RelativeLift) :
    (compactConnectingFiber E).Nonempty ↔
      OneHandleW6OrdinaryRelativeSolvable := by
  rw [ordinaryRelativeSolvable_iff_obstruction_mem_connectingValues]
  constructor
  · rintro ⟨D, hD⟩
    rw [mem_compactConnectingFiber_iff] at hD
    exact (mem_compactConnectingValues_iff _).mpr ⟨D, hD⟩
  · intro hmem
    rw [mem_compactConnectingValues_iff] at hmem
    obtain ⟨D, hD⟩ := hmem
    exact ⟨D, (mem_compactConnectingFiber_iff E D).mpr hD⟩

def CompactKernelCorrectionFullySolves
    (E : OneHandleC7RelativeLift)
    (D : OneHandleCompactKernelCorrection) : Prop :=
  ∃ hD : oneHandleCompactConnectingHom D =
      oneHandleC7StandardRelativeObstruction E,
    oneHandleC7StandardNeutralityObstruction
      (compactKernelCorrectionLift E D)
      (compactKernelCorrectionLift_relaxed E D hD) = 1

theorem compactKernelFullSolution_iff_correctionFullySolves
    (E : OneHandleC7RelativeLift) (D : OneHandleCompactKernelCorrection) :
    CompactKernelCorrectionFullySolves E D ↔
      ∃ S : OneHandleCompactKernelFullSolution E, S.correction = D := by
  constructor
  · rintro ⟨hD, hneutral⟩
    exact ⟨⟨D, hD, hneutral⟩, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S.connects, S.neutral⟩

noncomputable def compactFullCorrectionCandidates
    (E : OneHandleC7RelativeLift) :
    Finset OneHandleCompactKernelCorrection := by
  classical
  letI := Fintype.ofFinite OneHandleCompactKernelCorrection
  exact Finset.univ.filter (CompactKernelCorrectionFullySolves E)

theorem mem_compactFullCorrectionCandidates_iff
    (E : OneHandleC7RelativeLift) (D : OneHandleCompactKernelCorrection) :
    D ∈ compactFullCorrectionCandidates E ↔
      CompactKernelCorrectionFullySolves E D := by
  classical
  simp [compactFullCorrectionCandidates]

theorem compactFullCorrectionCandidates_subset_connectingFiber
    (E : OneHandleC7RelativeLift) :
    compactFullCorrectionCandidates E ⊆ compactConnectingFiber E := by
  intro D hD
  rw [mem_compactFullCorrectionCandidates_iff] at hD
  obtain ⟨hconnect, -⟩ := hD
  exact (mem_compactConnectingFiber_iff E D).mpr hconnect

theorem compactFullCorrectionCandidates_nonempty_iff
    (E : OneHandleC7RelativeLift) :
    (compactFullCorrectionCandidates E).Nonempty ↔
      OneHandleW6Correctable := by
  rw [← nonempty_compactKernelFullSolution_iff_oneHandleW6Correctable E]
  constructor
  · rintro ⟨D, hD⟩
    rw [mem_compactFullCorrectionCandidates_iff,
      compactKernelFullSolution_iff_correctionFullySolves] at hD
    obtain ⟨S, -⟩ := hD
    exact ⟨S⟩
  · rintro ⟨S⟩
    refine ⟨S.correction,
      (mem_compactFullCorrectionCandidates_iff E S.correction).mpr ?_⟩
    exact (compactKernelFullSolution_iff_correctionFullySolves E _).mpr
      ⟨S, rfl⟩

#print axioms compactConnectingFiber
#print axioms mem_compactConnectingFiber_iff
#print axioms compactConnectingFiber_nonempty_iff
#print axioms CompactKernelCorrectionFullySolves
#print axioms compactKernelFullSolution_iff_correctionFullySolves
#print axioms compactFullCorrectionCandidates
#print axioms mem_compactFullCorrectionCandidates_iff
#print axioms compactFullCorrectionCandidates_subset_connectingFiber
#print axioms compactFullCorrectionCandidates_nonempty_iff

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenCompactFullSearch
