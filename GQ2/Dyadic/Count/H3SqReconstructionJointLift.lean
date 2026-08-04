/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqReconstructionCoordinateDetector

/-!
# Joint choice of the square one-relator lift and reconstruction map

Reconstruction need not use the particular completed Fox preimages chosen by the canonical
one-relator lift.  This file parameterizes all possible changes of that lift which remain
globally compatible: their coordinate at a finite quotient is precisely the range of the
coordinate map from the kernel of the completed square Fox boundary.

Relative to any base lift, existence of some compatible lift satisfying reconstruction is
equivalent to one finite affine system.  Its first unknown changes each standard input column
inside the reachable completed-Fox-kernel range; its second unknown is the reconstruction
table.  The equations then require the changed one-relator columns to reconstruct the explicit
universal target columns.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh
open GQ2.Dyadic.SqCore

/-! ## Compatible changes of a completed lift -/

/-- Kernel of the completed improved-square Fox boundary. -/
abbrev SqCompletedModTwoFoxKernel (h : ℕ) :=
  LinearMap.ker (sqCompletedModTwoFoxBoundary h).map

/-- Completed regular mod-two modules remain elementary abelian. -/
theorem modTwoCompletedRegularModule_add_self
    {h : ℕ} {J : Type}
    (x : ModTwoCompletedRegularModule (DSq h : Type) J) :
    x + x = 0 := by
  apply ModTwoCompletedRegularModule.ext (DSq h : Type) J
  intro U
  change
    ModTwoCompletedRegularModule.coordinate (DSq h : Type) J U x +
        ModTwoCompletedRegularModule.coordinate (DSq h : Type) J U x = 0
  exact regularModTwoRelationModule_add_self
    ((DSq h : Type) ⧸ U.toSubgroup) J _

/-- Read a completed Fox-kernel element at one finite quotient. -/
def sqCompletedModTwoFoxKernelCoordinate
    (h : ℕ) (W : OpenNormalSubgroup (DSq h : Type)) :
    SqCompletedModTwoFoxKernel h →ₗ[ZMod 2]
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ W.toSubgroup) Unit :=
  (ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit W).comp
    (LinearMap.ker (sqCompletedModTwoFoxBoundary h).map).subtype

/-- Finite-level changes which genuinely arise from a globally compatible completed
Fox-kernel element. -/
abbrev SqCompletedModTwoFoxKernelCoordinateRange
    (h : ℕ) (W : OpenNormalSubgroup (DSq h : Type)) :=
  LinearMap.range (sqCompletedModTwoFoxKernelCoordinate h W)

/-- Add a completed Fox-kernel-valued linear correction to a compatible one-relator lift. -/
noncomputable def SqCompatibleUniversalBarRelationLiftAt.addCompletedFoxKernelCorrection
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    {S : SqCompatibleFiniteUniversalBarSyzygyAt h V}
    (L₀ : SqCompatibleUniversalBarRelationLiftAt S)
    (K : FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
        SqCompletedModTwoFoxKernel h) :
    SqCompatibleUniversalBarRelationLiftAt S := by
  let Rlin :=
    L₀.relationSyzygy.toCompleted.toZModLinearMap 2 +
      (LinearMap.ker (sqCompletedModTwoFoxBoundary h).map).subtype.comp K
  refine {
    relationSyzygy := sqCompatibleFiniteRelationSyzygyAtOfCompleted
      Rlin.toAddMonoidHom
    fox_lift := fun c ↦ ?_
  }
  rw [toCompleted_sqCompatibleFiniteRelationSyzygyAtOfCompleted]
  change (sqCompletedModTwoFoxBoundary h).map (Rlin c) = S.toCompletedFox c
  simp only [Rlin, LinearMap.add_apply, LinearMap.comp_apply]
  rw [map_add]
  have hL₀ :
      (sqCompletedModTwoFoxBoundary h).map
          (L₀.relationSyzygy.toCompleted.toZModLinearMap 2 c) =
        S.toCompletedFox c := by
    exact L₀.fox_lift c
  have hK := (K c).2
  rw [LinearMap.mem_ker] at hK
  have hK' :
      (sqCompletedModTwoFoxBoundary h).map
          ((LinearMap.ker
            (sqCompletedModTwoFoxBoundary h).map).subtype (K c)) = 0 :=
    hK
  rw [hL₀, hK', add_zero]

/-- Coordinate formula for changing a compatible lift by a completed Fox-kernel map. -/
theorem SqCompatibleUniversalBarRelationLiftAt.addCompletedFoxKernelCorrection_coordinate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    {S : SqCompatibleFiniteUniversalBarSyzygyAt h V}
    (L₀ : SqCompatibleUniversalBarRelationLiftAt S)
    (K : FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
        SqCompletedModTwoFoxKernel h)
    (W : OpenNormalSubgroup (DSq h : Type))
    (c : FiniteModTwoBarCochainThree
      ((DSq h : Type) ⧸ V.toSubgroup)) :
    (L₀.addCompletedFoxKernelCorrection K).relationSyzygy.coordinate W c =
      L₀.relationSyzygy.coordinate W c +
        sqCompletedModTwoFoxKernelCoordinate h W (K c) := by
  simp only [
    SqCompatibleUniversalBarRelationLiftAt.addCompletedFoxKernelCorrection]
  change
    ModTwoCompletedRegularModule.coordinate (DSq h : Type) Unit W
        ((L₀.relationSyzygy.toCompleted.toZModLinearMap 2 +
          (LinearMap.ker
            (sqCompletedModTwoFoxBoundary h).map).subtype.comp K) c) =
      L₀.relationSyzygy.coordinate W c +
        sqCompletedModTwoFoxKernelCoordinate h W (K c)
  rw [LinearMap.add_apply, map_add]
  rfl

/-! ## The finite joint affine system -/

/-- A compatible lift satisfying the exact reconstruction transport condition exists. -/
def SqFiniteInputRelationReconstructionCompatibleLiftExistsAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) : Prop :=
  ∃ L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy,
    SqFiniteInputRelationReconstructionTransportAt C L

/-- One finite affine system simultaneously chooses a globally reachable change of the
one-relator lift and the reconstruction table.  The reachability condition is what retains
inverse-limit compatibility; replacing it by the larger finite Fox kernel would not be exact. -/
def SqFiniteInputRelationReconstructionJointLiftSystemAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) : Prop :=
  ∃ delta : SqFiniteInputReconstructionBasisIndex h V →
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ C.W.toSubgroup) Unit,
    (∀ i, delta i ∈ SqCompletedModTwoFoxKernelCoordinateRange h C.W) ∧
      ∃ table : SqFiniteRelationReconstructionBasisIndex h C.W →
          FiniteModTwoBarCochainThree
            ((DSq h : Type) ⧸ C.W.toSubgroup),
        ∀ i : SqFiniteInputReconstructionBasisIndex h V,
          Finsupp.linearCombination (ZMod 2) table
              (sqFiniteInputSingleRelatorReconstructionCoordinate C L₀
                  (Pi.basisFun (ZMod 2)
                    (SqFiniteInputReconstructionBasisIndex h V) i) +
                delta i) =
            sqFiniteInputUniversalReconstructionTerm C
              (Pi.basisFun (ZMod 2)
                (SqFiniteInputReconstructionBasisIndex h V) i)

/-- Every reachable correction is killed by the finite square Fox boundary. -/
theorem sqFiniteLevelModTwoFoxBoundary_eq_zero_of_mem_completedKernelCoordinateRange
    {h : ℕ} (W : OpenNormalSubgroup (DSq h : Type))
    {d : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ W.toSubgroup) Unit}
    (hd : d ∈ SqCompletedModTwoFoxKernelCoordinateRange h W) :
    (sqFiniteLevelModTwoFoxBoundary h
      (sqOpenQuotientMarking h W)).map d = 0 := by
  obtain ⟨k, rfl⟩ := hd
  have hk := k.2
  rw [LinearMap.mem_ker] at hk
  have hcoord := congrArg
    (ModTwoCompletedRegularModule.coordinate
      (DSq h : Type) (Fin (sqRank h)) W) hk
  rw [map_zero, sqCompletedModTwoFoxBoundary_coordinate] at hcoord
  exact hcoord

/-- Therefore the affine columns in the joint system preserve the universal Fox image on every
standard input. -/
theorem SqFiniteInputRelationReconstructionJointLiftSystemAt.fox_preservation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    {C : SqFiniteInputUniversalDegreeThreeComparisonAt h V}
    {L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy}
    (H : SqFiniteInputRelationReconstructionJointLiftSystemAt C L₀) :
    ∃ relationColumn : SqFiniteInputReconstructionBasisIndex h V →
        RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit,
      (∀ i,
        (sqFiniteLevelModTwoFoxBoundary h
          (sqOpenQuotientMarking h C.W)).map (relationColumn i) =
            (finiteUniversalRelationFoxBoundary
              (sqOpenQuotientMarking h C.W)).map
              (C.universalSyzygy.coordinate C.W
                (Pi.basisFun (ZMod 2)
                  (SqFiniteInputReconstructionBasisIndex h V) i))) ∧
      ∃ table : SqFiniteRelationReconstructionBasisIndex h C.W →
          FiniteModTwoBarCochainThree
            ((DSq h : Type) ⧸ C.W.toSubgroup),
        ∀ i,
          Finsupp.linearCombination (ZMod 2) table (relationColumn i) =
            sqFiniteInputUniversalReconstructionTerm C
              (Pi.basisFun (ZMod 2)
                (SqFiniteInputReconstructionBasisIndex h V) i) := by
  rcases H with ⟨delta, hdelta, table, htable⟩
  let relationColumn : SqFiniteInputReconstructionBasisIndex h V →
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ C.W.toSubgroup) Unit :=
    fun i ↦
      sqFiniteInputSingleRelatorReconstructionCoordinate C L₀
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i) +
        delta i
  refine ⟨relationColumn, fun i ↦ ?_, table, fun i ↦ htable i⟩
  simp only [relationColumn, map_add]
  rw [sqFiniteLevelModTwoFoxBoundary_eq_zero_of_mem_completedKernelCoordinateRange
    C.W (hdelta i), add_zero]
  exact L₀.fox_lift_coordinate C.W
    (Pi.basisFun (ZMod 2)
      (SqFiniteInputReconstructionBasisIndex h V) i)

/-! ## Exact equivalence with a reconstruction-compatible lift -/

/-- **Joint-lift theorem.** Relative to any base compatible lift, the finite affine system is
exactly equivalent to existence of some compatible lift satisfying reconstruction. -/
theorem sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_jointLiftSystem
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionCompatibleLiftExistsAt C ↔
      SqFiniteInputRelationReconstructionJointLiftSystemAt C L₀ := by
  classical
  let b := Pi.basisFun (ZMod 2) (SqFiniteInputReconstructionBasisIndex h V)
  constructor
  · rintro ⟨L, htransport⟩
    obtain ⟨table, htable⟩ :=
      (sqFiniteInputRelationReconstructionGeneratorSystemAt_iff C L).2 htransport
    let delta : SqFiniteInputReconstructionBasisIndex h V →
        RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit :=
      fun i ↦
        sqFiniteInputSingleRelatorReconstructionCoordinate C L (b i) +
          sqFiniteInputSingleRelatorReconstructionCoordinate C L₀ (b i)
    refine ⟨delta, ?_, table, ?_⟩
    · intro i
      let k :
          ModTwoCompletedRegularModule (DSq h : Type) Unit :=
        L.relationSyzygy.toCompleted (b i) +
          L₀.relationSyzygy.toCompleted (b i)
      have hk : k ∈ LinearMap.ker (sqCompletedModTwoFoxBoundary h).map := by
        rw [LinearMap.mem_ker]
        change (sqCompletedModTwoFoxBoundary h).map
            (L.relationSyzygy.toCompleted (b i) +
              L₀.relationSyzygy.toCompleted (b i)) = 0
        rw [map_add, L.fox_lift (b i), L₀.fox_lift (b i),
          modTwoCompletedRegularModule_add_self]
      refine ⟨⟨k, hk⟩, ?_⟩
      rfl
    · intro i
      have hcoordinate :
          sqFiniteInputSingleRelatorReconstructionCoordinate C L₀ (b i) +
              delta i =
            sqFiniteInputSingleRelatorReconstructionCoordinate C L (b i) := by
        change
          sqFiniteInputSingleRelatorReconstructionCoordinate C L₀ (b i) +
              (sqFiniteInputSingleRelatorReconstructionCoordinate C L (b i) +
                sqFiniteInputSingleRelatorReconstructionCoordinate C L₀ (b i)) =
            sqFiniteInputSingleRelatorReconstructionCoordinate C L (b i)
        calc
          _ = sqFiniteInputSingleRelatorReconstructionCoordinate C L (b i) +
                (sqFiniteInputSingleRelatorReconstructionCoordinate C L₀ (b i) +
                  sqFiniteInputSingleRelatorReconstructionCoordinate C L₀ (b i)) := by
              abel
          _ = _ := by rw [ZModModule.add_self, add_zero]
      rw [hcoordinate]
      exact htable i
  · rintro ⟨delta, hdelta, table, htable⟩
    choose k hk using hdelta
    let K : FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
        SqCompletedModTwoFoxKernel h :=
      b.constr (ZMod 2) k
    let L := L₀.addCompletedFoxKernelCorrection K
    refine ⟨L, (sqFiniteInputRelationReconstructionGeneratorSystemAt_iff C L).1 ?_⟩
    refine ⟨table, fun i ↦ ?_⟩
    have hK : K (b i) = k i :=
      b.constr_basis (ZMod 2) k i
    have hcoordinate :
        sqFiniteInputSingleRelatorReconstructionCoordinate C L (b i) =
          sqFiniteInputSingleRelatorReconstructionCoordinate C L₀ (b i) +
            delta i := by
      change
        L.relationSyzygy.coordinate C.W (b i) =
          L₀.relationSyzygy.coordinate C.W (b i) + delta i
      rw [L₀.addCompletedFoxKernelCorrection_coordinate, hK, hk i]
    rw [hcoordinate]
    exact htable i

/-- Extract the compatible lift selected by a solution of the finite joint affine system. -/
noncomputable def sqFiniteInputRelationReconstructionCompatibleLiftOfJointSystem
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (H : SqFiniteInputRelationReconstructionJointLiftSystemAt C L₀) :
    SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy :=
  Classical.choose
    ((sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_jointLiftSystem
      C L₀).2 H)

/-- The lift extracted from the joint system satisfies reconstruction transport. -/
theorem sqFiniteInputRelationReconstructionCompatibleLiftOfJointSystem_transport
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (H : SqFiniteInputRelationReconstructionJointLiftSystemAt C L₀) :
    SqFiniteInputRelationReconstructionTransportAt C
      (sqFiniteInputRelationReconstructionCompatibleLiftOfJointSystem C L₀ H) :=
  Classical.choose_spec
    ((sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_jointLiftSystem
      C L₀).2 H)

/-- Generator-table regression for the lift extracted from the joint affine system. -/
theorem sqFiniteInputRelationReconstructionCompatibleLiftOfJointSystem_generators
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (H : SqFiniteInputRelationReconstructionJointLiftSystemAt C L₀) :
    SqFiniteInputRelationReconstructionGeneratorSystemAt C
      (sqFiniteInputRelationReconstructionCompatibleLiftOfJointSystem C L₀ H) :=
  (sqFiniteInputRelationReconstructionGeneratorSystemAt_iff C _).2
    (sqFiniteInputRelationReconstructionCompatibleLiftOfJointSystem_transport
      C L₀ H)

/-! ## Concrete square-presentation specialization -/

/-- The current reconstruction obstruction may choose the lift jointly with the reconstruction
table.  Fixing the canonical square-presentation lift is therefore unnecessary. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.exists_reconstructionCompatibleLift_iff_jointSystem
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :
    SqFiniteInputRelationReconstructionCompatibleLiftExistsAt S.degreeThreeComparison ↔
      SqFiniteInputRelationReconstructionJointLiftSystemAt
        S.degreeThreeComparison
        S.universalSyzygy.relationLiftOfSqPresentation :=
  sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_jointLiftSystem
    S.degreeThreeComparison
    S.universalSyzygy.relationLiftOfSqPresentation

#print axioms sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_jointLiftSystem
#print axioms sqFiniteInputRelationReconstructionCompatibleLiftOfJointSystem_transport
#print axioms SqFiniteInputRelationReconstructionJointLiftSystemAt.fox_preservation
#print axioms SqCompatibleUniversalCocycleCancellingSyzygyAt.exists_reconstructionCompatibleLift_iff_jointSystem

end

end GQ2.Dyadic.Count
