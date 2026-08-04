/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqReconstructionJointLift

/-!
# The affine obstruction for jointly chosen square reconstruction lifts

The reconstruction map and the correction to the one-relator lift occur multiplicatively in
the joint equations.  Consequently, the full joint problem is a finite bilinear incidence
problem, rather than one linear system in all unknowns at once.  After fixing a candidate
reconstruction map `E`, however, the remaining lift-correction equation is affine linear.

This file packages that equation as a finite cokernel class.  It proves that some compatible
lift satisfies reconstruction exactly when one class in the finite family indexed by `E`
vanishes.  Thus this family is the precise affine obstruction without privileging the canonical
Fox-preserving lift.

Every permitted correction comes from the completed Fox kernel.  A final regression proves
that all such corrections are invisible to the finite Fox boundary.  In particular, the
terminal/first-parity Fox detector used for literal relation-transition maps cannot distinguish
the different lifts in this affine family.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh
open GQ2.Dyadic.SqCore

/-! ## The affine family for a fixed reconstruction map -/

/-- Linear changes of the finite relation coordinate which genuinely lift to the completed
Fox kernel. -/
abbrev SqFiniteInputReachableRelationLiftCorrection
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) :=
  FiniteModTwoBarCochainThree
      ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
    SqCompletedModTwoFoxKernelCoordinateRange h C.W

/-- The base finite relation coordinate as a `ZMod 2`-linear map. -/
def sqFiniteInputBaseRelationReconstructionCoordinate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    FiniteModTwoBarCochainThree
        ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ C.W.toSubgroup) Unit :=
  (sqFiniteInputSingleRelatorReconstructionCoordinate C L₀).toZModLinearMap 2

/-- Add a globally reachable correction to the base finite relation coordinate. -/
def sqFiniteInputRelationReconstructionCoordinateWithCorrection
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (K : SqFiniteInputReachableRelationLiftCorrection C) :
    FiniteModTwoBarCochainThree
        ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ C.W.toSubgroup) Unit :=
  sqFiniteInputBaseRelationReconstructionCoordinate C L₀ +
    (SqCompletedModTwoFoxKernelCoordinateRange h C.W).subtype.comp K

/-- For a fixed reconstruction map `E`, this is the linear variation obtained by changing the
relation lift inside the reachable completed-Fox-kernel range. -/
def sqFiniteInputRelationReconstructionAffineVariation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (E : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup)) :
    SqFiniteInputReachableRelationLiftCorrection C →ₗ[ZMod 2]
      (FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup)) where
  toFun K := E.comp
    ((SqCompletedModTwoFoxKernelCoordinateRange h C.W).subtype.comp K)
  map_add' K K' := by
    apply LinearMap.ext
    intro c
    simp
  map_smul' a K := by
    apply LinearMap.ext
    intro c
    simp

/-- The affine residual for a fixed reconstruction map: target minus the value on the base
relation coordinate. -/
def sqFiniteInputRelationReconstructionAffineResidual
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (E : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup)) :
    FiniteModTwoBarCochainThree
        ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree
        ((DSq h : Type) ⧸ C.W.toSubgroup) :=
  (sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2 -
    E.comp (sqFiniteInputBaseRelationReconstructionCoordinate C L₀)

/-- The finite affine cokernel for reachable lift corrections at a fixed reconstruction map. -/
abbrev SqFiniteInputRelationReconstructionAffineCokernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (E : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup)) :=
  (FiniteModTwoBarCochainThree
      ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
    FiniteModTwoBarCochainThree
      ((DSq h : Type) ⧸ C.W.toSubgroup)) ⧸
    LinearMap.range (sqFiniteInputRelationReconstructionAffineVariation C E)

/-- Every fixed-map affine obstruction lives in a finite cokernel. -/
noncomputable instance instFintypeSqFiniteInputRelationReconstructionAffineCokernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (E : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup)) :
    Fintype (SqFiniteInputRelationReconstructionAffineCokernel C E) := by
  let A := FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)
  let B := FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup)
  letI : Finite (A →ₗ[ZMod 2] B) :=
    Finite.of_injective (fun f : A →ₗ[ZMod 2] B ↦ (f : A → B)) <| by
      intro f g hfg
      apply LinearMap.ext
      intro x
      exact congrFun hfg x
  let P := LinearMap.range
    (sqFiniteInputRelationReconstructionAffineVariation C E)
  letI : Finite (SqFiniteInputRelationReconstructionAffineCokernel C E) :=
    Finite.of_surjective P.mkQ P.mkQ_surjective
  exact Fintype.ofFinite _

/-- The affine obstruction class for a fixed candidate reconstruction map. -/
def sqFiniteInputRelationReconstructionAffineCokernelClass
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (E : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup)) :
    SqFiniteInputRelationReconstructionAffineCokernel C E :=
  (LinearMap.range
    (sqFiniteInputRelationReconstructionAffineVariation C E)).mkQ
      (sqFiniteInputRelationReconstructionAffineResidual C L₀ E)

/-- Vanishing of the fixed-map affine class is exactly existence of a reachable correction
which makes that reconstruction map work. -/
theorem sqFiniteInputRelationReconstructionAffineCokernelClass_eq_zero_iff
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (E : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup)) :
    sqFiniteInputRelationReconstructionAffineCokernelClass C L₀ E = 0 ↔
      ∃ K : SqFiniteInputReachableRelationLiftCorrection C,
        E.comp (sqFiniteInputRelationReconstructionCoordinateWithCorrection C L₀ K) =
          (sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2 := by
  rw [sqFiniteInputRelationReconstructionAffineCokernelClass,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    apply LinearMap.ext
    intro c
    have hc := LinearMap.congr_fun hK c
    change
      E ((sqFiniteInputBaseRelationReconstructionCoordinate C L₀) c +
          (SqCompletedModTwoFoxKernelCoordinateRange h C.W).subtype (K c)) =
        sqFiniteInputUniversalReconstructionTerm C c
    rw [map_add]
    change
      E ((SqCompletedModTwoFoxKernelCoordinateRange h C.W).subtype (K c)) =
        sqFiniteInputUniversalReconstructionTerm C c -
          E ((sqFiniteInputBaseRelationReconstructionCoordinate C L₀) c) at hc
    rw [hc]
    abel
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    apply LinearMap.ext
    intro c
    have hc := LinearMap.congr_fun hK c
    change
      E ((sqFiniteInputBaseRelationReconstructionCoordinate C L₀) c +
          (SqCompletedModTwoFoxKernelCoordinateRange h C.W).subtype (K c)) =
        sqFiniteInputUniversalReconstructionTerm C c at hc
    rw [map_add] at hc
    change
      E ((sqFiniteInputBaseRelationReconstructionCoordinate C L₀) c) +
          E ((SqCompletedModTwoFoxKernelCoordinateRange h C.W).subtype (K c)) =
        sqFiniteInputUniversalReconstructionTerm C c at hc
    change
      E ((SqCompletedModTwoFoxKernelCoordinateRange h C.W).subtype (K c)) =
        sqFiniteInputUniversalReconstructionTerm C c -
          E ((sqFiniteInputBaseRelationReconstructionCoordinate C L₀) c)
    rw [← hc]
    abel

/-! ## Exact joint obstruction -/

set_option maxHeartbeats 800000 in
/-- **Affine-cokernel theorem.**  The finite joint lift system is solvable exactly when one
member of the finite family of fixed-reconstruction-map affine classes vanishes. -/
theorem sqFiniteInputRelationReconstructionJointLiftSystemAt_iff_affineCokernelClass
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionJointLiftSystemAt C L₀ ↔
      ∃ E : RegularModTwoRelationModule
            ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
          FiniteModTwoBarCochainThree
            ((DSq h : Type) ⧸ C.W.toSubgroup),
        sqFiniteInputRelationReconstructionAffineCokernelClass C L₀ E = 0 := by
  classical
  let b := Pi.basisFun (ZMod 2) (SqFiniteInputReconstructionBasisIndex h V)
  constructor
  · rintro ⟨delta, hdelta, table, htable⟩
    choose k hk using hdelta
    let E : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup) :=
      Finsupp.linearCombination (ZMod 2) table
    let Kcompleted : FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
        SqCompletedModTwoFoxKernel h :=
      b.constr (ZMod 2) k
    let K : SqFiniteInputReachableRelationLiftCorrection C :=
      (sqCompletedModTwoFoxKernelCoordinate h C.W).rangeRestrict.comp Kcompleted
    refine ⟨E,
      (sqFiniteInputRelationReconstructionAffineCokernelClass_eq_zero_iff
        C L₀ E).2 ⟨K, ?_⟩⟩
    apply b.ext
    intro i
    change E
        (sqFiniteInputSingleRelatorReconstructionCoordinate C L₀ (b i) +
          (K (b i)).1) =
      sqFiniteInputUniversalReconstructionTerm C (b i)
    have hKcompleted : Kcompleted (b i) = k i :=
      b.constr_basis (ZMod 2) k i
    have hKi : (K (b i)).1 = delta i := by
      change sqCompletedModTwoFoxKernelCoordinate h C.W
          (Kcompleted (b i)) = delta i
      rw [hKcompleted, hk i]
    rw [hKi]
    exact htable i
  · rintro ⟨E, hE⟩
    obtain ⟨K, hK⟩ :=
      (sqFiniteInputRelationReconstructionAffineCokernelClass_eq_zero_iff
        C L₀ E).1 hE
    let table : SqFiniteRelationReconstructionBasisIndex h C.W →
        FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ C.W.toSubgroup) :=
      fun j ↦ E (Finsupp.single j 1)
    have htableE : E = Finsupp.linearCombination (ZMod 2) table := by
      apply Finsupp.basisSingleOne.ext
      intro j
      simp [table]
    refine ⟨fun i ↦ (K (b i)).1, fun i ↦ (K (b i)).2, table, fun i ↦ ?_⟩
    rw [← htableE]
    exact LinearMap.congr_fun hK (b i)

/-- A compatible reconstruction lift exists exactly when the affine obstruction vanishes for
some finite reconstruction map. -/
theorem sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_affineCokernelClass
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionCompatibleLiftExistsAt C ↔
      ∃ E : RegularModTwoRelationModule
            ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
          FiniteModTwoBarCochainThree
            ((DSq h : Type) ⧸ C.W.toSubgroup),
        sqFiniteInputRelationReconstructionAffineCokernelClass C L₀ E = 0 := by
  rw [sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_jointLiftSystem,
    sqFiniteInputRelationReconstructionJointLiftSystemAt_iff_affineCokernelClass]

/-! ## Fox and parity audit -/

/-- Reachable corrections are invisible to the finite Fox boundary, on every input and before
any reconstruction map is chosen. -/
theorem sqFiniteInputReachableRelationLiftCorrection_fox_invisible
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (K : SqFiniteInputReachableRelationLiftCorrection C)
    (c : FiniteModTwoBarCochainThree
      ((DSq h : Type) ⧸ V.toSubgroup)) :
    (sqFiniteLevelModTwoFoxBoundary h
      (sqOpenQuotientMarking h C.W)).map
        ((SqCompletedModTwoFoxKernelCoordinateRange h C.W).subtype (K c)) = 0 :=
  sqFiniteLevelModTwoFoxBoundary_eq_zero_of_mem_completedKernelCoordinateRange
    C.W (K c).2

/-- Consequently the finite Fox image of every corrected relation coordinate is exactly the
image of the base coordinate.  Any detector depending only on this Fox image, including the
existing terminal/first-parity detector, is blind to the joint-lift correction. -/
theorem sqFiniteInputRelationReconstructionCoordinateWithCorrection_fox_eq_base
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L₀ : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (K : SqFiniteInputReachableRelationLiftCorrection C)
    (c : FiniteModTwoBarCochainThree
      ((DSq h : Type) ⧸ V.toSubgroup)) :
    (sqFiniteLevelModTwoFoxBoundary h
      (sqOpenQuotientMarking h C.W)).map
        (sqFiniteInputRelationReconstructionCoordinateWithCorrection C L₀ K c) =
      (sqFiniteLevelModTwoFoxBoundary h
        (sqOpenQuotientMarking h C.W)).map
          (sqFiniteInputBaseRelationReconstructionCoordinate C L₀ c) := by
  have hc := sqFiniteInputReachableRelationLiftCorrection_fox_invisible C K c
  change
    (sqFiniteLevelModTwoFoxBoundary h
        (sqOpenQuotientMarking h C.W)).map
          ((sqFiniteInputBaseRelationReconstructionCoordinate C L₀) c +
            (SqCompletedModTwoFoxKernelCoordinateRange h C.W).subtype (K c)) =
      (sqFiniteLevelModTwoFoxBoundary h
        (sqOpenQuotientMarking h C.W)).map
          (sqFiniteInputBaseRelationReconstructionCoordinate C L₀ c)
  rw [map_add, hc, add_zero]

#print axioms sqFiniteInputRelationReconstructionAffineCokernelClass_eq_zero_iff
#print axioms sqFiniteInputRelationReconstructionJointLiftSystemAt_iff_affineCokernelClass
#print axioms sqFiniteInputRelationReconstructionCompatibleLiftExistsAt_iff_affineCokernelClass
#print axioms sqFiniteInputRelationReconstructionCoordinateWithCorrection_fox_eq_base

end

end GQ2.Dyadic.Count
