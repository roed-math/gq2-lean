/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqUnconditionalDegreeThree
import GQ2.Dyadic.Count.H3CompletedMagnusKernelIdentity
import GQ2.Dyadic.Count.FiniteTwoGroupAugmentationNilpotence

/-!
# Transporting universal reconstruction through the improved square relator

The universal degree-three comparison reconstructs its relation contribution from coefficients
in the free relation kernel.  The now-unconditional square-presentation lift replaces those
coefficients by a compatible coefficient of the single improved relator while preserving their
Fox boundary.  To reach the existing finite bar--Fox assembly, one final fact is needed: the
universal reconstruction contribution must depend only on that chosen single-relator
coefficient.

This file isolates that fact exactly.  For a fixed compatible lift it is equivalent to inclusion
of the kernel of the single-relator coordinate map in the kernel of the universal reconstruction
map.  Ordinary linear extension then constructs the required relation-error map.  We package the
criterion globally and prove the end-to-end capstone: this reconstruction transport together
with the all-degree completed Magnus--PBW kernel identity supplies finite elementary `H²`
right-exactness for the improved square core.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh
open GQ2.Dyadic.SqCore

/-! ## The unconditional compatible lift -/

/-- The square presentation unconditionally supplies a compatible coefficient of its single
improved relator for every compatible universal bar syzygy. -/
noncomputable def
    SqCompatibleFiniteUniversalBarSyzygyAt.relationLiftOfSqPresentation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) :
    SqCompatibleUniversalBarRelationLiftAt S :=
  sqCompatibleUniversalBarRelationLiftAtOfEventualRange S
    (sqUniversalBarFoxEventualRange S)

/-- Regression form of the unconditional compatible-lift result. -/
theorem nonempty_sqCompatibleUniversalBarRelationLiftAt_unconditional
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleFiniteUniversalBarSyzygyAt h V) :
    Nonempty (SqCompatibleUniversalBarRelationLiftAt S) :=
  ⟨S.relationLiftOfSqPresentation⟩

/-! ## The exact reconstruction-transport criterion -/

/-- The finite single-relator coordinate selected by a fixed compatible lift. -/
def sqFiniteInputSingleRelatorReconstructionCoordinate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →+
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ C.W.toSubgroup) Unit :=
  L.relationSyzygy.coordinate C.W

/-- The reconstruction term produced by the universal relation-kernel comparison. -/
def sqFiniteInputUniversalReconstructionTerm
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) :
    FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) :=
  C.universalRelationError.comp (C.universalSyzygy.coordinate C.W)

/-- Direct factorization formulation: the universal reconstruction term factors through the
chosen single-relator coordinate. -/
def SqFiniteInputRelationReconstructionTransportAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) : Prop :=
  ∃ E : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ C.W.toSubgroup) Unit →+
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup),
    E.comp (sqFiniteInputSingleRelatorReconstructionCoordinate C L) =
      sqFiniteInputUniversalReconstructionTerm C

/-- Kernel formulation of reconstruction transport.  It says precisely that two inputs with
the same chosen single-relator coordinate have the same universal reconstruction term. -/
def SqFiniteInputRelationReconstructionKernelAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) : Prop :=
  LinearMap.ker
      ((sqFiniteInputSingleRelatorReconstructionCoordinate C L).toZModLinearMap 2) ≤
    LinearMap.ker
      ((sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2)

/-- Over `F₂`, the kernel criterion is exactly equivalent to existence of the reconstruction
map.  The reverse implication descends through `C³ / ker R ≃ range R` and extends linearly
from `range R` to the whole single-relator module. -/
theorem sqFiniteInputRelationReconstructionTransportAt_iff_kernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy) :
    SqFiniteInputRelationReconstructionTransportAt C L ↔
      SqFiniteInputRelationReconstructionKernelAt C L := by
  constructor
  · rintro ⟨E, hE⟩ c hc
    rw [LinearMap.mem_ker] at hc ⊢
    change sqFiniteInputSingleRelatorReconstructionCoordinate C L c = 0 at hc
    change sqFiniteInputUniversalReconstructionTerm C c = 0
    have hEc := congrArg
      (fun f : FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ V.toSubgroup) →+
            FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) ↦ f c)
      hE
    change E (sqFiniteInputSingleRelatorReconstructionCoordinate C L c) =
      sqFiniteInputUniversalReconstructionTerm C c at hEc
    rw [hc, map_zero] at hEc
    exact hEc.symm
  · intro hker
    let R :=
      (sqFiniteInputSingleRelatorReconstructionCoordinate C L).toZModLinearMap 2
    let T := (sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2
    let onRange : LinearMap.range R →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) :=
      ((LinearMap.ker R).liftQ T hker).comp
        R.quotKerEquivRange.symm.toLinearMap
    let hExtend := LinearMap.exists_extend onRange
    let E := Classical.choose hExtend
    have hE := Classical.choose_spec hExtend
    refine ⟨E.toAddMonoidHom, ?_⟩
    apply AddMonoidHom.ext
    intro c
    change E (R c) = T c
    let Rc : LinearMap.range R := ⟨R c, ⟨c, rfl⟩⟩
    calc
      E (R c) = E ((LinearMap.range R).subtype Rc) := rfl
      _ = onRange Rc := LinearMap.congr_fun hE Rc
      _ = T c := by simp [onRange, Rc]

/-! ## Constructors for the existing bar--Fox assembly -/

/-- A universal comparison, a chosen compatible single-relator lift, and reconstruction
transport fill every field of the eventual finite-coordinate bar--Fox correction. -/
noncomputable def
    SqFiniteInputUniversalDegreeThreeComparisonAt.eventualBarFoxCorrectionOfRelationLift
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (htransport : SqFiniteInputRelationReconstructionTransportAt C L) :
    SqFiniteInputEventualBarFoxCorrectionAt h V := by
  let E := Classical.choose htransport
  let hE := Classical.choose_spec htransport
  refine {
    W := C.W
    le := C.le
    homotopyTwo := C.homotopyTwo
    relationSyzygy := L.relationSyzygy
    relationError := E
    boundaryDefect := C.boundaryDefect
    barDefect := C.barDefect
    boundary_relationSyzygy := fun c ↦
      (L.fox_lift c).trans (C.boundary_universalSyzygy c)
    reconstruct := fun c ↦ ?_
  }
  have hEc := congrArg
    (fun f : FiniteModTwoBarCochainThree
        ((DSq h : Type) ⧸ V.toSubgroup) →+
          FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) ↦ f c)
    hE
  change E (L.relationSyzygy.coordinate C.W c) =
    C.universalRelationError (C.universalSyzygy.coordinate C.W c) at hEc
  rw [hEc]
  exact C.reconstruct c

/-- Kernel-inclusion form of the preceding constructor. -/
noncomputable def
    SqFiniteInputUniversalDegreeThreeComparisonAt.eventualBarFoxCorrectionOfRelationLiftKernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (hkernel : SqFiniteInputRelationReconstructionKernelAt C L) :
    SqFiniteInputEventualBarFoxCorrectionAt h V :=
  C.eventualBarFoxCorrectionOfRelationLift L
    ((sqFiniteInputRelationReconstructionTransportAt_iff_kernel C L).2 hkernel)

/-- For the unconditional square-presentation lift, the reconstruction kernel inclusion is the
sole premise needed to construct the eventual bar--Fox correction. -/
noncomputable def
    SqFiniteInputUniversalDegreeThreeComparisonAt.eventualBarFoxCorrectionOfSqPresentationKernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (hkernel : SqFiniteInputRelationReconstructionKernelAt C
      C.universalSyzygy.relationLiftOfSqPresentation) :
    SqFiniteInputEventualBarFoxCorrectionAt h V :=
  C.eventualBarFoxCorrectionOfRelationLiftKernel
    C.universalSyzygy.relationLiftOfSqPresentation hkernel

/-- The remaining local condition after relation generation: there is a compatible
single-relator lift for which the reconstruction kernel inclusion holds.  Existence of a lift
alone is unconditional for the square presentation; the displayed kernel inclusion is the
additional mathematical assertion. -/
def SqFiniteInputRelationReconstructionTransportableAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) : Prop :=
  ∃ L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy,
    SqFiniteInputRelationReconstructionKernelAt C L

/-- The local transportability condition constructs the eventual bar--Fox correction. -/
noncomputable def
    SqFiniteInputUniversalDegreeThreeComparisonAt.eventualBarFoxCorrection
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (htransport : SqFiniteInputRelationReconstructionTransportableAt C) :
    SqFiniteInputEventualBarFoxCorrectionAt h V := by
  let L := Classical.choose htransport
  let hkernel := Classical.choose_spec htransport
  exact C.eventualBarFoxCorrectionOfRelationLiftKernel L hkernel

/-! ## Global assembly and capstone -/

/-- Universal degree-three comparisons at every finite input quotient, together with exactly the
remaining reconstruction-transport condition. -/
structure SqFiniteInputUniversalDegreeThreeTransportAssembly (h : ℕ) where
  comparison : ∀ V : OpenNormalSubgroup (DSq h : Type),
    SqFiniteInputUniversalDegreeThreeComparisonAt h V
  reconstructionTransport : ∀ V : OpenNormalSubgroup (DSq h : Type),
    SqFiniteInputRelationReconstructionTransportableAt (comparison V)

/-- Using the named unconditional square-presentation lift, a family of universal comparisons
and the corresponding kernel inclusions construct the global transport package. -/
noncomputable def sqFiniteInputUniversalDegreeThreeTransportAssemblyOfSqPresentationKernel
    (h : ℕ)
    (C : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (hkernel : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionKernelAt (C V)
        (C V).universalSyzygy.relationLiftOfSqPresentation) :
    SqFiniteInputUniversalDegreeThreeTransportAssembly h where
  comparison := C
  reconstructionTransport V :=
    ⟨(C V).universalSyzygy.relationLiftOfSqPresentation, hkernel V⟩

/-- The universal comparisons and reconstruction transport give the eventual finite-coordinate
assembly, with no further relation-generation premise. -/
noncomputable def
    SqFiniteInputUniversalDegreeThreeTransportAssembly.toEventualBarFoxAssembly
    {h : ℕ} (S : SqFiniteInputUniversalDegreeThreeTransportAssembly h) :
    SqFiniteInputEventualBarFoxAssembly h :=
  fun V ↦ (S.comparison V).eventualBarFoxCorrection
    (S.reconstructionTransport V)

/-- Hence the same data gives the completed bar--Fox assembly used by the cohomological
capstone. -/
noncomputable def
    SqFiniteInputUniversalDegreeThreeTransportAssembly.toCompletedBarFoxAssembly
    {h : ℕ} (S : SqFiniteInputUniversalDegreeThreeTransportAssembly h) :
    SqFiniteToCompletedBarFoxAssembly h :=
  sqFiniteToCompletedBarFoxAssembly_of_eventual h S.toEventualBarFoxAssembly

end

end GQ2.Dyadic.Count

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

/-- **End-to-end square-core capstone.**  The all-degree completed Magnus--PBW kernel identity
and reconstruction transport for universal degree-three comparisons are the only remaining
inputs to finite elementary `H²` right-exactness. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_kernelIdentity_reconstructionTransport
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (S : SqFiniteInputUniversalDegreeThreeTransportAssembly h) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_barFox h
    (SqCompletedMagnusNormalCoefficientSystem.completedRowAugmentationInitialRegular
      (sqCompletedMagnusNormalCoefficientSystem_of_kernelIdentity h H))
    S.toCompletedBarFoxAssembly

/-- Explicit regression form: after the universal degree-three comparisons, the only additional
local hypothesis is the kernel inclusion for the unconditional square-presentation lift. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_kernelIdentity_universalComparisonKernel
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (C : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (hkernel : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionKernelAt (C V)
        (C V).universalSyzygy.relationLiftOfSqPresentation) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_kernelIdentity_reconstructionTransport h H
    (sqFiniteInputUniversalDegreeThreeTransportAssemblyOfSqPresentationKernel
      h C hkernel)

end


end GQ2.ContCoh
