/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqAdjointReconstructionDefect
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# A finite detector for square-presentation reconstruction transport

The remaining reconstruction obstruction at an input quotient is finite-dimensional.  This
file presents it in two detector-friendly forms.

* Its cokernel class is the class of the finite-support reconstruction map modulo maps which
  factor through the chosen single-relator coordinate.
* Its generator system asks for one output cochain for each standard basis vector of the finite
  one-relator module, followed by one explicit equation on every standard bar-three cochain.

The cokernel class vanishes exactly when the finite-support transport defect vanishes, and this
is equivalent to solvability of the generator system.  Thus no decomposition into cocycles and
coboundaries is hidden in the interface: cocycle cancellation controls only the cocycle
subspace, while the finite system detects the complementary directions as well.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh
open GQ2.Dyadic.SqCore

/-! ## The finite cokernel obstruction -/

/-- Precomposition with the chosen single-relator coordinate, as a linear map between finite
spaces of linear maps. -/
def sqFiniteInputRelationReconstructionPrecomposition
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    (RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup)) →ₗ[ZMod 2]
      (FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup)) where
  toFun E := E.comp
    ((sqFiniteInputSingleRelatorReconstructionCoordinate C L).toZModLinearMap 2 :
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
        RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit)
  map_add' E F := by
    apply LinearMap.ext
    intro c
    rfl
  map_smul' a E := by
    apply LinearMap.ext
    intro c
    rfl

/-- The finite cokernel in which failure of reconstruction factorization lives. -/
abbrev SqFiniteInputRelationReconstructionCokernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :=
  (FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup)) ⧸
    LinearMap.range (sqFiniteInputRelationReconstructionPrecomposition C L)

/-- The reconstruction cokernel is genuinely finite at every finite input quotient. -/
noncomputable instance instFintypeSqFiniteInputRelationReconstructionCokernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    Fintype (SqFiniteInputRelationReconstructionCokernel C L) := by
  let A := FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)
  let B := FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup)
  letI : Finite (A →ₗ[ZMod 2] B) :=
    Finite.of_injective (fun f : A →ₗ[ZMod 2] B ↦ (f : A → B)) <| by
      intro f g hfg
      apply LinearMap.ext
      intro x
      exact congrFun hfg x
  let P := LinearMap.range (sqFiniteInputRelationReconstructionPrecomposition C L)
  letI : Finite (SqFiniteInputRelationReconstructionCokernel C L) :=
    Finite.of_surjective P.mkQ P.mkQ_surjective
  exact Fintype.ofFinite _

/-- The reconstruction obstruction class: the universal reconstruction term modulo maps which
factor through the chosen single-relator coordinate. -/
def sqFiniteInputRelationReconstructionCokernelClass
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionCokernel C L :=
  (LinearMap.range
    (sqFiniteInputRelationReconstructionPrecomposition C L)).mkQ
      ((sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2 :
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →ₗ[ZMod 2]
          FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup))

/-- The cokernel class vanishes exactly when the reconstruction term factors through the chosen
single-relator coordinate. -/
theorem sqFiniteInputRelationReconstructionCokernelClass_eq_zero_iff
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    sqFiniteInputRelationReconstructionCokernelClass C L = 0 ↔
      SqFiniteInputRelationReconstructionTransportAt C L := by
  rw [sqFiniteInputRelationReconstructionCokernelClass,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨E.toAddMonoidHom, ?_⟩
    apply AddMonoidHom.ext
    intro c
    exact DFunLike.congr_fun hE c
  · rintro ⟨E, hE⟩
    refine ⟨E.toZModLinearMap 2, ?_⟩
    apply LinearMap.ext
    intro c
    exact congrArg (fun f ↦ f c) hE

/-! ## A standard-basis generator system -/

/-- Standard basis index for finite bar-three cochains at the input quotient. -/
abbrev SqFiniteInputReconstructionBasisIndex
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) :=
  ((DSq h : Type) ⧸ V.toSubgroup) ×
    ((DSq h : Type) ⧸ V.toSubgroup) ×
      ((DSq h : Type) ⧸ V.toSubgroup)

/-- A finite generator table for reconstruction transport.  The unknown `table j` is the image
of the one-relator basis vector `j`; the displayed equations are indexed by the standard basis
of the finite input bar-three cochains. -/
def SqFiniteInputRelationReconstructionGeneratorSystemAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) : Prop :=
  ∃ table : (((DSq h : Type) ⧸ C.W.toSubgroup) × Unit) →
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup),
    ∀ i : SqFiniteInputReconstructionBasisIndex h V,
      Finsupp.linearCombination (ZMod 2) table
          (sqFiniteInputSingleRelatorReconstructionCoordinate C L
            (Pi.basisFun (ZMod 2)
              (SqFiniteInputReconstructionBasisIndex h V) i)) =
        sqFiniteInputUniversalReconstructionTerm C
          (Pi.basisFun (ZMod 2)
            (SqFiniteInputReconstructionBasisIndex h V) i)

/-- Solvability of the finite generator table is exactly additive reconstruction
factorization. -/
theorem sqFiniteInputRelationReconstructionGeneratorSystemAt_iff
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionGeneratorSystemAt C L ↔
      SqFiniteInputRelationReconstructionTransportAt C L := by
  classical
  let b := Pi.basisFun (ZMod 2) (SqFiniteInputReconstructionBasisIndex h V)
  let R :=
    (sqFiniteInputSingleRelatorReconstructionCoordinate C L).toZModLinearMap 2
  let T := (sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2
  constructor
  · rintro ⟨table, htable⟩
    let E : RegularModTwoRelationModule
          ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) :=
      Finsupp.linearCombination (ZMod 2) table
    have hlinear : E.comp R = T := by
      apply b.ext
      intro i
      exact htable i
    refine ⟨E.toAddMonoidHom, ?_⟩
    apply AddMonoidHom.ext
    intro c
    exact LinearMap.congr_fun hlinear c
  · rintro ⟨Eadd, hEadd⟩
    let E := Eadd.toZModLinearMap 2
    let table : (((DSq h : Type) ⧸ C.W.toSubgroup) × Unit) →
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) :=
      fun j ↦ E (Finsupp.single j 1)
    have hE : E = Finsupp.linearCombination (ZMod 2) table := by
      apply Finsupp.basisSingleOne.ext
      intro j
      simp [table]
    refine ⟨table, fun i ↦ ?_⟩
    change Finsupp.linearCombination (ZMod 2) table (R (b i)) = T (b i)
    rw [← hE]
    have hi := congrArg (fun f ↦ f (b i)) hEadd
    exact hi

/-- Hence the detector has three interchangeable forms: generator-table solvability,
cokernel-class vanishing, and the reconstruction kernel inclusion. -/
theorem sqFiniteInputRelationReconstructionGeneratorSystemAt_iff_cokernelClass_eq_zero
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionGeneratorSystemAt C L ↔
      sqFiniteInputRelationReconstructionCokernelClass C L = 0 := by
  rw [sqFiniteInputRelationReconstructionGeneratorSystemAt_iff,
    sqFiniteInputRelationReconstructionCokernelClass_eq_zero_iff]

/-! ## Specialization to the concrete compactness output -/

/-- The finite cokernel obstruction for the named unconditional square-presentation lift of a
concrete cocycle-cancelling compactness output. -/
def SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationReconstructionCokernelClass
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :=
  sqFiniteInputRelationReconstructionCokernelClass S.degreeThreeComparison
    S.universalSyzygy.relationLiftOfSqPresentation

/-- The previously isolated finite-support defect vanishes exactly when its finite cokernel
class vanishes. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationFiniteSupportTransportDefect_eq_zero_iff_cokernelClass
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :
    S.sqPresentationFiniteSupportTransportDefect = 0 ↔
      S.sqPresentationReconstructionCokernelClass = 0 := by
  let L := S.universalSyzygy.relationLiftOfSqPresentation
  have hiff := (S.reconstructionKernel_iff_defect_eq_zero L).symm |>.trans
    (sqFiniteInputRelationReconstructionTransportAt_iff_kernel
      S.degreeThreeComparison L).symm |>.trans
    (sqFiniteInputRelationReconstructionCokernelClass_eq_zero_iff
      S.degreeThreeComparison L).symm
  simpa only [SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationFiniteSupportTransportDefect,
    SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationReconstructionCokernelClass,
    L] using hiff

/-- **Finite detector endpoint.**  Vanishing of the concrete finite-support defect is exactly
solvability of the standard-basis generator system at the finite input quotient. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationFiniteSupportTransportDefect_eq_zero_iff_generators
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :
    S.sqPresentationFiniteSupportTransportDefect = 0 ↔
      SqFiniteInputRelationReconstructionGeneratorSystemAt S.degreeThreeComparison
        S.universalSyzygy.relationLiftOfSqPresentation := by
  let L := S.universalSyzygy.relationLiftOfSqPresentation
  have hiff := (S.reconstructionKernel_iff_defect_eq_zero L).symm |>.trans
    (sqFiniteInputRelationReconstructionTransportAt_iff_kernel
      S.degreeThreeComparison L).symm |>.trans
    (sqFiniteInputRelationReconstructionGeneratorSystemAt_iff
      S.degreeThreeComparison L).symm
  simpa only [SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationFiniteSupportTransportDefect,
    L] using hiff

end

end GQ2.Dyadic.Count
