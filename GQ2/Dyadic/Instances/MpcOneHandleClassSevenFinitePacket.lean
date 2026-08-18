/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeFiniteLiftIndependence

/-!
# The finite compact packet controlling the ordinary class-seven obstruction

A compact packet records the four compact correction factors only in `D_M(2,0)/lambda_7` and
is restricted to data attained by a legal one-handle relative lift.  This is a finite type.
W275 makes the relaxed obstruction and literal row equation independent of the representative,
so both descend to this packet type.

The finite set `compactPacketObstructionValues` is the exact ordinary search space.  It contains
the identity precisely when some legal relative lift satisfies the ordinary row equation.  Full
W6-to-W7 correctability implies this condition.  The reverse implication is not claimed: it
still requires the separate character-neutral `C` condition.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassSevenFinitePacket

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeTarget
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeCorrection
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenNeutrality
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeEquation
open GQ2.Dyadic.Instances.MpcOneHandleClassSevenRelativeFiniteLiftIndependence
open GQ2.Roe.Labute

abbrev OneHandleC7CompactLevelSevenData :=
  Fin (coreRank 1) → levelQuot (DM 2 0 : Type) 7

def compactLevelSevenData (E : OneHandleC7RelativeLift) :
    OneHandleC7CompactLevelSevenData :=
  fun i ↦ levelMk (DM 2 0 : Type) 7 (E.compactFactors i)

theorem sameCompactLevelSeven_iff_data_eq (E F : OneHandleC7RelativeLift) :
    SameCompactLevelSeven E F ↔ compactLevelSevenData E = compactLevelSevenData F := by
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

abbrev OneHandleC7CompactLevelSevenPacket := Set.range compactLevelSevenData

noncomputable instance : Finite OneHandleC7CompactLevelSevenData := by
  letI : Finite (levelQuot (DM 2 0 : Type) 7) :=
    finite_levelQuot (DM 2 0 : Type) (dmFinsetTopGen 2 0) (isProP_DM 2 0) 7
  infer_instance

noncomputable instance : Finite OneHandleC7CompactLevelSevenPacket := by
  infer_instance

noncomputable def compactPacketRepresentative
    (P : OneHandleC7CompactLevelSevenPacket) : OneHandleC7RelativeLift :=
  Classical.choose P.2

theorem compactPacketRepresentative_data
    (P : OneHandleC7CompactLevelSevenPacket) :
    compactLevelSevenData (compactPacketRepresentative P) = P.1 :=
  Classical.choose_spec P.2

def compactPacketObstruction (P : OneHandleC7CompactLevelSevenPacket) :
    OneHandleC7StandardRelativeCokernel :=
  oneHandleC7StandardRelativeObstruction (compactPacketRepresentative P)

def CompactPacketRowEquation (P : OneHandleC7CompactLevelSevenPacket) : Prop :=
  OneHandleC7StandardRelativeRowEquation (compactPacketRepresentative P)

theorem compactPacketObstruction_eq_lift
    (P : OneHandleC7CompactLevelSevenPacket) (E : OneHandleC7RelativeLift)
    (hE : compactLevelSevenData E = P.1) :
    compactPacketObstruction P = oneHandleC7StandardRelativeObstruction E := by
  apply relativeObstruction_eq_of_sameCompactLevelSeven
  exact (sameCompactLevelSeven_iff_data_eq _ _).mpr
    (compactPacketRepresentative_data P |>.trans hE.symm)

theorem compactPacketRowEquation_iff_lift
    (P : OneHandleC7CompactLevelSevenPacket) (E : OneHandleC7RelativeLift)
    (hE : compactLevelSevenData E = P.1) :
    CompactPacketRowEquation P ↔ OneHandleC7StandardRelativeRowEquation E := by
  apply relativeRowEquation_iff_of_sameCompactLevelSeven
  exact (sameCompactLevelSeven_iff_data_eq _ _).mpr
    (compactPacketRepresentative_data P |>.trans hE.symm)

theorem compactPacketObstruction_eq_one_iff_rowEquation
    (P : OneHandleC7CompactLevelSevenPacket) :
    compactPacketObstruction P = 1 ↔ CompactPacketRowEquation P := by
  rw [compactPacketObstruction, CompactPacketRowEquation,
    standardRelativeObstruction_eq_one_iff,
    standardRelativeTarget_mem_relaxed_iff_rowEquation]

noncomputable instance : Fintype OneHandleC7CompactLevelSevenPacket :=
  Fintype.ofFinite _

noncomputable def compactPacketObstructionValues :
    Finset OneHandleC7StandardRelativeCokernel := by
  classical
  exact Finset.univ.image compactPacketObstruction

theorem mem_compactPacketObstructionValues_iff
    (x : OneHandleC7StandardRelativeCokernel) :
    x ∈ compactPacketObstructionValues ↔
      ∃ P : OneHandleC7CompactLevelSevenPacket, compactPacketObstruction P = x := by
  simp [compactPacketObstructionValues]

def OneHandleW6OrdinaryRelativeSolvable : Prop :=
  ∃ E : OneHandleC7RelativeLift, OneHandleC7StandardRelativeRowEquation E

theorem one_mem_compactPacketObstructionValues_iff :
    1 ∈ compactPacketObstructionValues ↔ OneHandleW6OrdinaryRelativeSolvable := by
  rw [mem_compactPacketObstructionValues_iff]
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨compactPacketRepresentative P,
      (compactPacketObstruction_eq_one_iff_rowEquation P).mp hP⟩
  · rintro ⟨E, hE⟩
    let P : OneHandleC7CompactLevelSevenPacket :=
      ⟨compactLevelSevenData E, ⟨E, rfl⟩⟩
    refine ⟨P, ?_⟩
    rw [compactPacketObstruction_eq_lift P E rfl]
    exact (standardRelativeObstruction_eq_one_iff E).mpr
      ((standardRelativeTarget_mem_relaxed_iff_rowEquation E).mpr hE)

theorem ordinaryRelativeSolvable_of_oneHandleW6Correctable
    (h : OneHandleW6Correctable) : OneHandleW6OrdinaryRelativeSolvable := by
  obtain ⟨E, hE⟩ := oneHandleW6Correctable_iff_relativeResidual.mp h
  refine ⟨E, (standardRelativeTarget_mem_relaxed_iff_rowEquation E).mp ?_⟩
  have ht : oneHandleC7RelativeTarget E = 1 := by
    apply Subtype.ext
    simp [oneHandleC7RelativeTarget_val, hE]
  rw [ht]
  exact Subgroup.one_mem _

theorem one_mem_compactPacketObstructionValues_of_oneHandleW6Correctable
    (h : OneHandleW6Correctable) : 1 ∈ compactPacketObstructionValues :=
  one_mem_compactPacketObstructionValues_iff.mpr
    (ordinaryRelativeSolvable_of_oneHandleW6Correctable h)

#print axioms sameCompactLevelSeven_iff_data_eq
#print axioms compactPacketRepresentative_data
#print axioms compactPacketObstruction_eq_lift
#print axioms compactPacketRowEquation_iff_lift
#print axioms compactPacketObstruction_eq_one_iff_rowEquation
#print axioms mem_compactPacketObstructionValues_iff
#print axioms one_mem_compactPacketObstructionValues_iff
#print axioms ordinaryRelativeSolvable_of_oneHandleW6Correctable
#print axioms one_mem_compactPacketObstructionValues_of_oneHandleW6Correctable

end
end GQ2.Dyadic.Instances.MpcOneHandleClassSevenFinitePacket
