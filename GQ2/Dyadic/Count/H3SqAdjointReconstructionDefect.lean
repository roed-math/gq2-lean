/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqRelationReconstructionTransport

/-!
# The finite-support obstruction to adjoint reconstruction transport

The concrete universal degree-three comparison uses
`finiteUniversalRelationThreeFiniteSupportCorrection` as its reconstruction map.  The
unconditional single-relator lift preserves the universal Fox boundary, but the finite-support
correction is the adjoint of the degree-three reverse comparison, not a function of that Fox
boundary in the current API.

This file makes the distinction exact.  First, factorization of the reconstruction term through
the universal Fox output is characterized by a kernel inclusion and shown to imply transport
through every compatible single-relator lift.  Then, for the comparisons produced by adjoint
cocycle cancellation, we isolate the strictly smaller obstruction: the restriction of the
finite-support correction to the kernel of the chosen single-relator coordinate.  Its vanishing
is equivalent to the exact reconstruction-kernel condition, and hence constructs the existing
eventual bar--Fox correction.  A final endpoint appends this one obstruction to the fully
concrete cofiltered-coherence hypotheses.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh
open GQ2.Dyadic.SqCore

/-! ## The stronger universal-Fox factorization route -/

/-- The universal Fox boundary of the compatible relation output at the reconstruction
quotient. -/
def sqFiniteInputUniversalFoxReconstructionCoordinate
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) :
    FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup) →+
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ C.W.toSubgroup) (Fin (sqRank h)) :=
  (finiteUniversalRelationFoxBoundary
      (sqOpenQuotientMarking h C.W)).map.toAddMonoidHom.comp
    (C.universalSyzygy.coordinate C.W)

/-- The restricted reconstruction term factors through the universal Fox output.  This is the
natural route by which Fox-preservation of a compatible single-relator lift would imply
reconstruction transport. -/
def SqFiniteInputUniversalReconstructionFactorsThroughFoxAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) : Prop :=
  ∃ E : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ C.W.toSubgroup) (Fin (sqRank h)) →+
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup),
    E.comp (sqFiniteInputUniversalFoxReconstructionCoordinate C) =
      sqFiniteInputUniversalReconstructionTerm C

/-- Exact kernel criterion for factorization of the compatible reconstruction output through
its universal Fox boundary. -/
def SqFiniteInputUniversalReconstructionFoxKernelAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) : Prop :=
  LinearMap.ker
      ((sqFiniteInputUniversalFoxReconstructionCoordinate C).toZModLinearMap 2) ≤
    LinearMap.ker
      ((sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2)

/-- Universal-Fox factorization is equivalent to its kernel criterion. -/
theorem sqFiniteInputUniversalReconstructionFactorsThroughFoxAt_iff_kernel
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V) :
    SqFiniteInputUniversalReconstructionFactorsThroughFoxAt C ↔
      SqFiniteInputUniversalReconstructionFoxKernelAt C := by
  constructor
  · rintro ⟨E, hE⟩ c hc
    rw [LinearMap.mem_ker] at hc ⊢
    change sqFiniteInputUniversalFoxReconstructionCoordinate C c = 0 at hc
    change sqFiniteInputUniversalReconstructionTerm C c = 0
    have hEc := congrArg
      (fun f : FiniteModTwoBarCochainThree
          ((DSq h : Type) ⧸ V.toSubgroup) →+
            FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) ↦ f c)
      hE
    change E (sqFiniteInputUniversalFoxReconstructionCoordinate C c) =
      sqFiniteInputUniversalReconstructionTerm C c at hEc
    rw [hc, map_zero] at hEc
    exact hEc.symm
  · intro hker
    let J :=
      (sqFiniteInputUniversalFoxReconstructionCoordinate C).toZModLinearMap 2
    let T := (sqFiniteInputUniversalReconstructionTerm C).toZModLinearMap 2
    let onRange : LinearMap.range J →ₗ[ZMod 2]
        FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) :=
      ((LinearMap.ker J).liftQ T hker).comp
        J.quotKerEquivRange.symm.toLinearMap
    let hExtend := LinearMap.exists_extend onRange
    let E := Classical.choose hExtend
    have hE := Classical.choose_spec hExtend
    refine ⟨E.toAddMonoidHom, ?_⟩
    apply AddMonoidHom.ext
    intro c
    change E (J c) = T c
    let Jc : LinearMap.range J := ⟨J c, ⟨c, rfl⟩⟩
    calc
      E (J c) = E ((LinearMap.range J).subtype Jc) := rfl
      _ = onRange Jc := LinearMap.congr_fun hE Jc
      _ = T c := by simp [onRange, Jc]

/-- If reconstruction depends only on the universal Fox output, Fox-preservation of any
compatible single-relator lift gives the exact reconstruction transport condition. -/
theorem sqFiniteInputRelationReconstructionKernelAt_of_factorsThroughUniversalFox
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqFiniteInputUniversalDegreeThreeComparisonAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt C.universalSyzygy)
    (hfactor : SqFiniteInputUniversalReconstructionFactorsThroughFoxAt C) :
    SqFiniteInputRelationReconstructionKernelAt C L := by
  rw [← sqFiniteInputRelationReconstructionTransportAt_iff_kernel]
  let E := Classical.choose hfactor
  have hE := Classical.choose_spec hfactor
  refine ⟨E.comp
      (sqFiniteLevelModTwoFoxBoundary h
        (sqOpenQuotientMarking h C.W)).map.toAddMonoidHom, ?_⟩
  apply AddMonoidHom.ext
  intro c
  have hfactorC := congrArg
    (fun f : FiniteModTwoBarCochainThree
        ((DSq h : Type) ⧸ V.toSubgroup) →+
          FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ C.W.toSubgroup) ↦ f c)
    hE
  change E ((finiteUniversalRelationFoxBoundary
      (sqOpenQuotientMarking h C.W)).map
        (C.universalSyzygy.coordinate C.W c)) =
    sqFiniteInputUniversalReconstructionTerm C c at hfactorC
  change E ((sqFiniteLevelModTwoFoxBoundary h
      (sqOpenQuotientMarking h C.W)).map
        (L.relationSyzygy.coordinate C.W c)) =
    sqFiniteInputUniversalReconstructionTerm C c
  rw [L.fox_lift_coordinate]
  exact hfactorC

/-! ## The exact finite-support defect for the concrete adjoint comparison -/

/-- The smallest transport defect for the concrete comparison produced by a cocycle-cancelling
compatible universal syzygy.  It is the reconstruction term restricted to inputs whose chosen
single-relator coordinate is zero. -/
def SqCompatibleUniversalCocycleCancellingSyzygyAt.finiteSupportTransportDefect
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt S.universalSyzygy) :
    LinearMap.ker
        ((sqFiniteInputSingleRelatorReconstructionCoordinate
          S.degreeThreeComparison L).toZModLinearMap 2) →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree
        ((DSq h : Type) ⧸ S.degreeThreeComparison.W.toSubgroup) :=
  ((sqFiniteInputUniversalReconstructionTerm
    S.degreeThreeComparison).toZModLinearMap 2).domRestrict
      (LinearMap.ker
        ((sqFiniteInputSingleRelatorReconstructionCoordinate
          S.degreeThreeComparison L).toZModLinearMap 2))

/-- On the concrete adjoint comparison, the preceding abstract defect is literally the
finite-support correction applied to the compatible universal output. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.finiteSupportTransportDefect_apply
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt S.universalSyzygy)
    (c : LinearMap.ker
      ((sqFiniteInputSingleRelatorReconstructionCoordinate
        S.degreeThreeComparison L).toZModLinearMap 2)) :
    S.finiteSupportTransportDefect L c =
      finiteUniversalRelationThreeFiniteSupportCorrection
        (sqOpenQuotientMarking h V)
        (sqOpenQuotientFreeEvaluation_surjective h V)
        (S.universalSyzygy.coordinate V c.1) :=
  rfl

/-- On cocycles, existing adjoint cancellation identifies the finite-support transport defect
with the sum of the two raw adjoint corrections.  Thus cancellation controls the *coupled* sum;
it does not make the finite-support term vanish. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.finiteSupportTransportDefect_apply_of_cocycle
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt S.universalSyzygy)
    (c : LinearMap.ker
      ((sqFiniteInputSingleRelatorReconstructionCoordinate
        S.degreeThreeComparison L).toZModLinearMap 2))
    (hc : finiteModTwoBarDThree
      ((DSq h : Type) ⧸ V.toSubgroup) c.1 = 0) :
    S.finiteSupportTransportDefect L c =
      finiteBarHomotopyTwoAdjointBarDefect
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V)
          (sqFiniteModTwoBarRefineThree h (le_refl V.toSubgroup) c.1) +
        finiteUniversalForwardReverseThreeCochainCorrection
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V)
          (sqFiniteModTwoBarRefineThree h (le_refl V.toSubgroup) c.1) := by
  rw [S.finiteSupportTransportDefect_apply L c]
  have hcancel := S.cancels_at_input c.1 hc
  funext a
  have ha := congrFun hcancel a
  simp only [finiteUniversalThreeAdjointFiniteSupportDefect,
    Pi.add_apply] at ha
  let B : ZMod 2 := finiteBarHomotopyTwoAdjointBarDefect
    (sqOpenQuotientMarking h V)
    (sqOpenQuotientFreeEvaluation_surjective h V)
    (sqFiniteModTwoBarRefineThree h (le_refl V.toSubgroup) c.1) a
  let U : ZMod 2 := finiteUniversalForwardReverseThreeCochainCorrection
    (sqOpenQuotientMarking h V)
    (sqOpenQuotientFreeEvaluation_surjective h V)
    (sqFiniteModTwoBarRefineThree h (le_refl V.toSubgroup) c.1) a
  let T : ZMod 2 := finiteUniversalRelationThreeFiniteSupportCorrection
    (sqOpenQuotientMarking h V)
    (sqOpenQuotientFreeEvaluation_surjective h V)
    (S.universalSyzygy.coordinate V c.1) a
  change T = B + U
  change B + (U + T) = 0 at ha
  calc
    T = (B + B) + (U + U) + T := by
      rw [ZModModule.add_self, ZModModule.add_self]
      simp
    _ = (B + (U + T)) + (B + U) := by abel
    _ = B + U := by rw [ha, zero_add]

/-- Vanishing of the finite-support defect is exactly, not merely sufficiently, the remaining
reconstruction kernel inclusion for the concrete comparison. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.reconstructionKernel_iff_defect_eq_zero
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt S.universalSyzygy) :
    SqFiniteInputRelationReconstructionKernelAt S.degreeThreeComparison L ↔
      S.finiteSupportTransportDefect L = 0 := by
  constructor
  · intro hkernel
    apply LinearMap.ext
    intro c
    change sqFiniteInputUniversalReconstructionTerm S.degreeThreeComparison c.1 = 0
    exact (LinearMap.mem_ker.mp (hkernel c.2))
  · intro hzero c hc
    rw [LinearMap.mem_ker] at hc ⊢
    change sqFiniteInputSingleRelatorReconstructionCoordinate
      S.degreeThreeComparison L c = 0 at hc
    change sqFiniteInputUniversalReconstructionTerm S.degreeThreeComparison c = 0
    let cz : LinearMap.ker
        ((sqFiniteInputSingleRelatorReconstructionCoordinate
          S.degreeThreeComparison L).toZModLinearMap 2) := ⟨c, hc⟩
    have hz := LinearMap.congr_fun hzero cz
    simpa [SqCompatibleUniversalCocycleCancellingSyzygyAt.finiteSupportTransportDefect]
      using hz

/-- The stronger universal-Fox factorization kills the exact finite-support transport defect
for every compatible single-relator lift. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.finiteSupportTransportDefect_eq_zero_of_factorsThroughFox
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (L : SqCompatibleUniversalBarRelationLiftAt S.universalSyzygy)
    (hfactor : SqFiniteInputUniversalReconstructionFactorsThroughFoxAt
      S.degreeThreeComparison) :
    S.finiteSupportTransportDefect L = 0 :=
  (S.reconstructionKernel_iff_defect_eq_zero L).1
    (sqFiniteInputRelationReconstructionKernelAt_of_factorsThroughUniversalFox
      S.degreeThreeComparison L hfactor)

/-- The exact defect for the named unconditional square-presentation lift. -/
def SqCompatibleUniversalCocycleCancellingSyzygyAt.sqPresentationFiniteSupportTransportDefect
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :=
  S.finiteSupportTransportDefect
    S.universalSyzygy.relationLiftOfSqPresentation

/-- Defect vanishing closes the concrete compactness output all the way to the eventual
single-relator bar--Fox correction. -/
noncomputable def
    SqCompatibleUniversalCocycleCancellingSyzygyAt.eventualBarFoxCorrectionOfDefectZero
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (hzero : S.sqPresentationFiniteSupportTransportDefect = 0) :
    SqFiniteInputEventualBarFoxCorrectionAt h V :=
  S.degreeThreeComparison.eventualBarFoxCorrectionOfSqPresentationKernel
    ((S.reconstructionKernel_iff_defect_eq_zero
      S.universalSyzygy.relationLiftOfSqPresentation).2 hzero)

/-! ## Concrete-coherence endpoint -/

/-- The concrete local and transition-coherence hypotheses produce a compatible
cocycle-cancelling universal syzygy before asking about finite-support transport. -/
theorem nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_concreteCoherence
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V)
    (hbar : SqUniversalBarInputTransitionRange h)
    (hcancel : SqUniversalBarInputCocycleCancellationTransitionKernel h V) :
    Nonempty (SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :=
  nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_eventuallyNonempty
    h V
      (sqUniversalCocycleOutputTransitionClosed_of_barInputKernelCoherence
        h V hbar hcancel)
      (sqUniversalCocycleOutputEventuallyNonempty_of_syzygyBarCofinalRange hlocal)

/-- A named compactness output from the fully concrete coherence hypotheses. -/
noncomputable def sqCompatibleUniversalCocycleCancellingSyzygyAtOfConcreteCoherence
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V)
    (hbar : SqUniversalBarInputTransitionRange h)
    (hcancel : SqUniversalBarInputCocycleCancellationTransitionKernel h V) :
    SqCompatibleUniversalCocycleCancellingSyzygyAt h V :=
  Classical.choice
    (nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_concreteCoherence
      h V hlocal hbar hcancel)

/-- For the named compactness output, its one finite-support defect is the sole additional
condition needed to reach the eventual bar--Fox correction. -/
theorem nonempty_sqFiniteInputEventualBarFoxCorrectionAt_of_concreteCoherence_chosenDefectZero
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V)
    (hbar : SqUniversalBarInputTransitionRange h)
    (hcancel : SqUniversalBarInputCocycleCancellationTransitionKernel h V)
    (hdefect :
      (sqCompatibleUniversalCocycleCancellingSyzygyAtOfConcreteCoherence
        h V hlocal hbar hcancel).sqPresentationFiniteSupportTransportDefect = 0) :
    Nonempty (SqFiniteInputEventualBarFoxCorrectionAt h V) :=
  ⟨(sqCompatibleUniversalCocycleCancellingSyzygyAtOfConcreteCoherence
      h V hlocal hbar hcancel).eventualBarFoxCorrectionOfDefectZero hdefect⟩

/-- Fully concrete transition coherence reaches the eventual bar--Fox endpoint once the exact
finite-support transport defect is known to vanish for the compactness output.  No relation-
generation or further assembly premise remains. -/
theorem nonempty_sqFiniteInputEventualBarFoxCorrectionAt_of_concreteCoherence_defectZero
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V)
    (hbar : SqUniversalBarInputTransitionRange h)
    (hcancel : SqUniversalBarInputCocycleCancellationTransitionKernel h V)
    (hdefect : ∀ S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V,
      S.sqPresentationFiniteSupportTransportDefect = 0) :
    Nonempty (SqFiniteInputEventualBarFoxCorrectionAt h V) := by
  have hclosed : SqUniversalCocycleOutputTransitionClosed h V :=
    sqUniversalCocycleOutputTransitionClosed_of_barInputKernelCoherence
      h V hbar hcancel
  have heventual : SqUniversalCocycleOutputEventuallyNonempty h V :=
    sqUniversalCocycleOutputEventuallyNonempty_of_syzygyBarCofinalRange hlocal
  obtain ⟨S⟩ :=
    nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_eventuallyNonempty
      h V hclosed heventual
  exact ⟨S.eventualBarFoxCorrectionOfDefectZero (hdefect S)⟩

end

end GQ2.Dyadic.Count
