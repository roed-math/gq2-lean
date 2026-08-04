/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteBarFoxAdjoint
import GQ2.Dyadic.Count.H3UniversalRelationLift
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# From the finite adjoint identity to the universal degree-three interface

The canonical bar contraction is not equivariant, so its raw adjoint bar defect need not vanish
on three-cocycles.  The correct object to factor through `d³` is the combined reconstruction
residual after choosing the universal relation coefficient.  This file defines that residual,
identifies it with the three explicit terms in the transposed chain identity, and constructs
`SqFiniteInputUniversalDegreeThreeComparisonAt` from precisely its `d³`-factorization.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore
open CategoryTheory

private abbrev SqAdjointInputThree (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :=
  FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)

private abbrev SqAdjointInputFour (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :=
  FiniteModTwoBarCochainFour ((DSq h : Type) ⧸ V.toSubgroup)

/-! ## The finite-quotient cocycle lifting problem -/

/-- Apply the degree-three relation correction to an actual universal output `R₂(b)`.  This is
the correction map available to a `SqCompatibleFiniteUniversalBarSyzygyAt`, whose coordinates
are required to arise from bar two-chains. -/
def finiteUniversalThreeBarInputCorrection
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarChainTwo Q →ₗ[ZMod 2] FiniteModTwoBarCochainThree Q :=
  (finiteUniversalRelationThreeFiniteSupportCorrection m heval).comp
    (finiteBarToUniversalRelationTwo m heval)

/-- The coupled relation correction required on cocycles: raw universal adjoint plus the raw
bar non-invariance defect. -/
def finiteUniversalThreeAdjointCocycleTarget
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainThree Q →+ FiniteModTwoBarCochainThree Q :=
  (finiteUniversalForwardReverseThreeCochainCorrection m heval).toAddMonoidHom +
    finiteBarHomotopyTwoAdjointBarDefect m heval

/-- Exact finite-level range condition: on the cocycle subspace, the coupled target is in the
range of the correction attached to a genuine bar-two input. -/
def FiniteUniversalThreeAdjointCocycleBarRange
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) : Prop :=
  let d := (finiteModTwoBarDThree Q).toZModLinearMap 2
  let T := (finiteUniversalThreeAdjointCocycleTarget m heval).toZModLinearMap 2
  let L := finiteUniversalThreeBarInputCorrection m heval
  LinearMap.range (T.domRestrict (LinearMap.ker d)) ≤ LinearMap.range L

/-- Fox boundary of a universal relation output arising from a bar-two input. -/
def finiteUniversalThreeBarInputFoxBoundary
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarChainTwo Q →ₗ[ZMod 2]
      RegularModTwoRelationModule Q I :=
  (finiteUniversalRelationFoxBoundary m).map.comp
    (finiteBarToUniversalRelationTwo m heval)

/-- The proved reverse degree-two chain identity identifies the new Fox-zero condition with
vanishing of the reverse marked boundary of the bar-two input. -/
theorem finiteUniversalThreeBarInputFoxBoundary_eq_reverseBoundary
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (b : FiniteModTwoBarChainTwo Q) :
    finiteUniversalThreeBarInputFoxBoundary m heval b =
      finiteBarToMarkedOne m heval (finiteModTwoBarBoundaryTwo b) := by
  exact (finiteBarToMarkedOne_boundaryTwo m heval b).symm

/-- Exact local existence statement: one linear bar-two lift simultaneously realizes the
coupled adjoint target and has Fox-zero universal output on every three-cocycle. -/
def FiniteUniversalThreeAdjointCocycleSyzygyBarLiftExists
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) : Prop :=
  ∃ B : FiniteModTwoBarCochainThree Q →ₗ[ZMod 2]
      FiniteModTwoBarChainTwo Q,
    ∀ c : FiniteModTwoBarCochainThree Q,
      finiteModTwoBarDThree Q c = 0 →
        finiteUniversalThreeBarInputCorrection m heval (B c) =
            finiteUniversalThreeAdjointCocycleTarget m heval c ∧
          finiteUniversalThreeBarInputFoxBoundary m heval (B c) = 0

/-- The smallest linear range condition which imposes both requirements: the coupled target on
cocycles must lie in the range of the correction map restricted to bar-two inputs whose
universal Fox boundary is zero. -/
def FiniteUniversalThreeAdjointCocycleSyzygyBarRange
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) : Prop :=
  let d := (finiteModTwoBarDThree Q).toZModLinearMap 2
  let T := (finiteUniversalThreeAdjointCocycleTarget m heval).toZModLinearMap 2
  let L := finiteUniversalThreeBarInputCorrection m heval
  let J := finiteUniversalThreeBarInputFoxBoundary m heval
  LinearMap.range (T.domRestrict (LinearMap.ker d)) ≤
    LinearMap.range (L.domRestrict (LinearMap.ker J))

/-- The syzygy range condition is exact: it is equivalent to existence of a linear local lift
with both adjoint cancellation and Fox-zero on cocycles. -/
theorem finiteUniversalThreeAdjointCocycleSyzygyBarRange_iff
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteUniversalThreeAdjointCocycleSyzygyBarRange m heval ↔
      FiniteUniversalThreeAdjointCocycleSyzygyBarLiftExists m heval := by
  let d := (finiteModTwoBarDThree Q).toZModLinearMap 2
  let T := (finiteUniversalThreeAdjointCocycleTarget m heval).toZModLinearMap 2
  let L := finiteUniversalThreeBarInputCorrection m heval
  let J := finiteUniversalThreeBarInputFoxBoundary m heval
  constructor
  · intro hrange
    let Tker := T.domRestrict (LinearMap.ker d)
    let Lker := L.domRestrict (LinearMap.ker J)
    let intoRange : LinearMap.ker d →ₗ[ZMod 2] LinearMap.range Lker :=
      Tker.codRestrict (LinearMap.range Lker) fun c =>
        hrange (LinearMap.mem_range_self Tker c)
    let hRight := Lker.rangeRestrict.exists_rightInverse_of_surjective
      Lker.range_rangeRestrict
    let right := Classical.choose hRight
    have hright := Classical.choose_spec hRight
    let onKer : LinearMap.ker d →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q :=
      (LinearMap.ker J).subtype.comp (right.comp intoRange)
    let hExtend := LinearMap.exists_extend onKer
    let B := Classical.choose hExtend
    have hB := Classical.choose_spec hExtend
    refine ⟨B, fun c hc => ?_⟩
    have hc' : c ∈ LinearMap.ker d := by
      rw [LinearMap.mem_ker]
      simpa [d] using hc
    let cz : LinearMap.ker d := ⟨c, hc'⟩
    have hBc : B c = onKer cz := LinearMap.congr_fun hB cz
    have hright_c := LinearMap.congr_fun hright (intoRange cz)
    constructor
    · change L (B c) = T c
      rw [hBc]
      exact congrArg Subtype.val hright_c
    · change J (B c) = 0
      rw [hBc]
      exact (right (intoRange cz)).2
  · rintro ⟨B, hB⟩
    intro z hz
    obtain ⟨c, rfl⟩ := hz
    have hc : finiteModTwoBarDThree Q c.1 = 0 := by
      exact c.2
    let b : LinearMap.ker J := ⟨B c.1, (hB c.1 hc).2⟩
    refine ⟨b, ?_⟩
    exact (hB c.1 hc).1

/-- The strengthened syzygy range condition implies the earlier cancellation-only range
condition, by forgetting that the chosen bar input lies in the Fox kernel. -/
theorem FiniteUniversalThreeAdjointCocycleSyzygyBarRange.toBarRange
    {Q I : Type} [Group Q]
    {m : I → Q} {heval : Function.Surjective (FreeGroup.lift m)}
    (hrange : FiniteUniversalThreeAdjointCocycleSyzygyBarRange m heval) :
    FiniteUniversalThreeAdjointCocycleBarRange m heval := by
  let d := (finiteModTwoBarDThree Q).toZModLinearMap 2
  let T := (finiteUniversalThreeAdjointCocycleTarget m heval).toZModLinearMap 2
  let L := finiteUniversalThreeBarInputCorrection m heval
  let J := finiteUniversalThreeBarInputFoxBoundary m heval
  intro z hz
  obtain ⟨b, hb⟩ := hrange hz
  exact ⟨b.1, hb⟩

/-- Any bar input realizing the coupled target gives the desired defect cancellation.  The
Fox-zero requirement is deliberately absent from this lemma and remains the second, independent
half of the syzygy range condition. -/
theorem finiteUniversalThreeAdjointBarInput_cancels_of_spec
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainThree Q) (b : FiniteModTwoBarChainTwo Q)
    (hspec : finiteUniversalThreeBarInputCorrection m heval b =
      finiteUniversalThreeAdjointCocycleTarget m heval c) :
    finiteBarHomotopyTwoAdjointBarDefect m heval c +
      finiteUniversalThreeAdjointFiniteSupportDefect m heval c
        (finiteBarToUniversalRelationTwo m heval b) = 0 := by
  funext a
  have ha := congrFun hspec a
  simp only [finiteUniversalThreeAdjointFiniteSupportDefect,
    finiteUniversalThreeBarInputCorrection,
    finiteUniversalThreeAdjointCocycleTarget,
    LinearMap.comp_apply, AddMonoidHom.add_apply] at ha ⊢
  let B : ZMod 2 := finiteBarHomotopyTwoAdjointBarDefect m heval c a
  let U : ZMod 2 := finiteUniversalForwardReverseThreeCochainCorrection m heval c a
  let F : ZMod 2 := finiteUniversalRelationThreeFiniteSupportCorrection m heval
    (finiteBarToUniversalRelationTwo m heval b) a
  change B + (U + F) = 0
  change F = U + B at ha
  rw [ha]
  calc
    B + (U + (U + B)) = (B + B) + (U + U) := by abel
    _ = 0 := by
      rw [ZModModule.add_self, ZModModule.add_self]
      simp

/-! ### Refined-input version for the square quotient system -/

/-- The coupled target at `U`, pulled back from an input cochain at `V`. -/
def sqFiniteUniversalThreeAdjointCocycleTargetAt
    (h : ℕ) {V U : OpenNormalSubgroup (DSq h : Type)}
    (hUV : U.toSubgroup ≤ V.toSubgroup) :
    SqAdjointInputThree h V →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ U.toSubgroup) :=
  ((finiteUniversalThreeAdjointCocycleTarget
    (sqOpenQuotientMarking h U)
    (sqOpenQuotientFreeEvaluation_surjective h U)).toZModLinearMap 2).comp
      ((sqFiniteModTwoBarRefineThree h hUV).toZModLinearMap 2)

/-- Refined local existence of a linear bar lift which realizes the coupled target and has
Fox-zero universal output on input cocycles. -/
def SqFiniteUniversalThreeAdjointCocycleSyzygyBarLiftExistsAt
    (h : ℕ) (V U : OpenNormalSubgroup (DSq h : Type))
    (hUV : U.toSubgroup ≤ V.toSubgroup) : Prop :=
  ∃ B : SqAdjointInputThree h V →ₗ[ZMod 2]
      FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup),
    ∀ c : SqAdjointInputThree h V,
      finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0 →
        finiteUniversalThreeBarInputCorrection
            (sqOpenQuotientMarking h U)
            (sqOpenQuotientFreeEvaluation_surjective h U) (B c) =
            sqFiniteUniversalThreeAdjointCocycleTargetAt h hUV c ∧
          finiteUniversalThreeBarInputFoxBoundary
            (sqOpenQuotientMarking h U)
            (sqOpenQuotientFreeEvaluation_surjective h U) (B c) = 0

/-- Minimal refined range condition: the coupled target on input cocycles is lifted through the
correction map restricted to the Fox kernel at the refining quotient. -/
def SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeAt
    (h : ℕ) (V U : OpenNormalSubgroup (DSq h : Type))
    (hUV : U.toSubgroup ≤ V.toSubgroup) : Prop :=
  let d := (finiteModTwoBarDThree
    ((DSq h : Type) ⧸ V.toSubgroup)).toZModLinearMap 2
  let T := sqFiniteUniversalThreeAdjointCocycleTargetAt h hUV
  let L := finiteUniversalThreeBarInputCorrection
    (sqOpenQuotientMarking h U)
    (sqOpenQuotientFreeEvaluation_surjective h U)
  let J := finiteUniversalThreeBarInputFoxBoundary
    (sqOpenQuotientMarking h U)
    (sqOpenQuotientFreeEvaluation_surjective h U)
  LinearMap.range (T.domRestrict (LinearMap.ker d)) ≤
    LinearMap.range (L.domRestrict (LinearMap.ker J))

/-- The refined range premise is again exactly equivalent to existence of the desired linear
local lift. -/
theorem sqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeAt_iff
    (h : ℕ) (V U : OpenNormalSubgroup (DSq h : Type))
    (hUV : U.toSubgroup ≤ V.toSubgroup) :
    SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeAt h V U hUV ↔
      SqFiniteUniversalThreeAdjointCocycleSyzygyBarLiftExistsAt h V U hUV := by
  let d := (finiteModTwoBarDThree
    ((DSq h : Type) ⧸ V.toSubgroup)).toZModLinearMap 2
  let T := sqFiniteUniversalThreeAdjointCocycleTargetAt h hUV
  let L := finiteUniversalThreeBarInputCorrection
    (sqOpenQuotientMarking h U)
    (sqOpenQuotientFreeEvaluation_surjective h U)
  let J := finiteUniversalThreeBarInputFoxBoundary
    (sqOpenQuotientMarking h U)
    (sqOpenQuotientFreeEvaluation_surjective h U)
  constructor
  · intro hrange
    let Tker := T.domRestrict (LinearMap.ker d)
    let Lker := L.domRestrict (LinearMap.ker J)
    let intoRange : LinearMap.ker d →ₗ[ZMod 2] LinearMap.range Lker :=
      Tker.codRestrict (LinearMap.range Lker) fun c =>
        hrange (LinearMap.mem_range_self Tker c)
    let hRight := Lker.rangeRestrict.exists_rightInverse_of_surjective
      Lker.range_rangeRestrict
    let right := Classical.choose hRight
    have hright := Classical.choose_spec hRight
    let onKer : LinearMap.ker d →ₗ[ZMod 2]
        FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup) :=
      (LinearMap.ker J).subtype.comp (right.comp intoRange)
    let hExtend := LinearMap.exists_extend onKer
    let B := Classical.choose hExtend
    have hB := Classical.choose_spec hExtend
    refine ⟨B, fun c hc => ?_⟩
    have hc' : c ∈ LinearMap.ker d := by
      rw [LinearMap.mem_ker]
      simpa [d] using hc
    let cz : LinearMap.ker d := ⟨c, hc'⟩
    have hBc : B c = onKer cz := LinearMap.congr_fun hB cz
    have hright_c := LinearMap.congr_fun hright (intoRange cz)
    constructor
    · change L (B c) = T c
      rw [hBc]
      exact congrArg Subtype.val hright_c
    · change J (B c) = 0
      rw [hBc]
      exact (right (intoRange cz)).2
  · rintro ⟨B, hB⟩
    intro z hz
    obtain ⟨c, rfl⟩ := hz
    have hc : finiteModTwoBarDThree
        ((DSq h : Type) ⧸ V.toSubgroup) c.1 = 0 := by
      exact c.2
    let b : LinearMap.ker J := ⟨B c.1, (hB c.1 hc).2⟩
    exact ⟨b, (hB c.1 hc).1⟩

/-- Finite-dimensional linear algebra turns the cocycle range condition into an additive
bar-two input map.  The lift is first chosen through `L.rangeRestrict` on `ker d³`, then extended
from the cocycle subspace to all three-cochains. -/
noncomputable def finiteUniversalThreeAdjointBarChainLiftOfCocycleRange
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (hrange : FiniteUniversalThreeAdjointCocycleBarRange m heval) :
    FiniteModTwoBarCochainThree Q →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q := by
  let d := (finiteModTwoBarDThree Q).toZModLinearMap 2
  let T := (finiteUniversalThreeAdjointCocycleTarget m heval).toZModLinearMap 2
  let L := finiteUniversalThreeBarInputCorrection m heval
  let Tker := T.domRestrict (LinearMap.ker d)
  let intoRange : LinearMap.ker d →ₗ[ZMod 2] LinearMap.range L :=
    Tker.codRestrict (LinearMap.range L) fun c =>
      hrange (LinearMap.mem_range_self Tker c)
  let hRight := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  let right := Classical.choose hRight
  have hright := Classical.choose_spec hRight
  let onKer : LinearMap.ker d →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q :=
    right.comp intoRange
  let hExtend := LinearMap.exists_extend onKer
  exact Classical.choose hExtend

/-- The finite-level bar-chain lift realizes the coupled target on every three-cocycle. -/
theorem finiteUniversalThreeAdjointBarChainLiftOfCocycleRange_spec
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (hrange : FiniteUniversalThreeAdjointCocycleBarRange m heval)
    (c : FiniteModTwoBarCochainThree Q)
    (hc : finiteModTwoBarDThree Q c = 0) :
    finiteUniversalThreeBarInputCorrection m heval
        (finiteUniversalThreeAdjointBarChainLiftOfCocycleRange m heval hrange c) =
      finiteUniversalThreeAdjointCocycleTarget m heval c := by
  let d := (finiteModTwoBarDThree Q).toZModLinearMap 2
  let T := (finiteUniversalThreeAdjointCocycleTarget m heval).toZModLinearMap 2
  let L := finiteUniversalThreeBarInputCorrection m heval
  let Tker := T.domRestrict (LinearMap.ker d)
  let intoRange : LinearMap.ker d →ₗ[ZMod 2] LinearMap.range L :=
    Tker.codRestrict (LinearMap.range L) fun z =>
      hrange (LinearMap.mem_range_self Tker z)
  let hRight := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  let right := Classical.choose hRight
  have hright := Classical.choose_spec hRight
  let onKer : LinearMap.ker d →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q :=
    right.comp intoRange
  let hExtend := LinearMap.exists_extend onKer
  let lift := Classical.choose hExtend
  have hlift := Classical.choose_spec hExtend
  have hc' : c ∈ LinearMap.ker d := by
    rw [LinearMap.mem_ker]
    simpa [d] using hc
  let cz : LinearMap.ker d := ⟨c, hc'⟩
  change L (lift c) = T c
  have hlift_c : lift c = onKer cz := by
    have h := LinearMap.congr_fun hlift cz
    exact h
  rw [hlift_c]
  have hright_c := LinearMap.congr_fun hright (intoRange cz)
  change L (right (intoRange cz)) = T c
  exact congrArg Subtype.val hright_c

/-- Consequently, the universal coefficient `R₂(barChainLift c)` cancels the raw bar defect on
cocycles.  This is the exact local condition later required of a compatible inverse-system
family. -/
theorem finiteUniversalThreeAdjointBarChainLiftOfCocycleRange_cancels
    {Q I : Type} [Group Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (hrange : FiniteUniversalThreeAdjointCocycleBarRange m heval)
    (c : FiniteModTwoBarCochainThree Q)
    (hc : finiteModTwoBarDThree Q c = 0) :
    finiteBarHomotopyTwoAdjointBarDefect m heval c +
      finiteUniversalThreeAdjointFiniteSupportDefect m heval c
        (finiteBarToUniversalRelationTwo m heval
          (finiteUniversalThreeAdjointBarChainLiftOfCocycleRange
            m heval hrange c)) = 0 := by
  have hspec := finiteUniversalThreeAdjointBarChainLiftOfCocycleRange_spec
    m heval hrange c hc
  funext a
  have ha := congrFun hspec a
  simp only [finiteUniversalThreeAdjointFiniteSupportDefect,
    finiteUniversalThreeBarInputCorrection,
    finiteUniversalThreeAdjointCocycleTarget,
    LinearMap.comp_apply, AddMonoidHom.add_apply] at ha ⊢
  let B : ZMod 2 := finiteBarHomotopyTwoAdjointBarDefect m heval c a
  let U : ZMod 2 := finiteUniversalForwardReverseThreeCochainCorrection m heval c a
  let F : ZMod 2 := finiteUniversalRelationThreeFiniteSupportCorrection m heval
    (finiteBarToUniversalRelationTwo m heval
      (finiteUniversalThreeAdjointBarChainLiftOfCocycleRange m heval hrange c)) a
  change B + (U + F) = 0
  change F = U + B at ha
  rw [ha]
  calc
    B + (U + (U + B)) = (B + B) + (U + U) := by abel
    _ = 0 := by
      rw [ZModModule.add_self, ZModModule.add_self]
      simp

/-- Quotientwise form of the exact finite-dimensional range premise for the actual improved
square marking.  This is a new universal-comparison input; it is not implied merely by
finiteness of the quotient. -/
def SqUniversalThreeAdjointCocycleBarRange (h : ℕ) : Prop :=
  ∀ U : OpenNormalSubgroup (DSq h : Type),
    FiniteUniversalThreeAdjointCocycleBarRange
      (sqOpenQuotientMarking h U)
      (sqOpenQuotientFreeEvaluation_surjective h U)

/-- The additive local bar-chain lift supplied by the quotientwise range premise. -/
noncomputable def sqOpenQuotientUniversalThreeAdjointBarChainLift
    (h : ℕ) (U : OpenNormalSubgroup (DSq h : Type))
    (hrange : SqUniversalThreeAdjointCocycleBarRange h) :
    FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ U.toSubgroup) →ₗ[ZMod 2]
      FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup) :=
  finiteUniversalThreeAdjointBarChainLiftOfCocycleRange
    (sqOpenQuotientMarking h U)
    (sqOpenQuotientFreeEvaluation_surjective h U)
    (hrange U)

/-- Each local actual-quotient lift cancels the raw bar defect on cocycles.  Coherence of these
local choices under quotient transition remains a separate inverse-system condition. -/
theorem sqOpenQuotientUniversalThreeAdjointBarChainLift_cancels
    (h : ℕ) (U : OpenNormalSubgroup (DSq h : Type))
    (hrange : SqUniversalThreeAdjointCocycleBarRange h)
    (c : FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ U.toSubgroup))
    (hc : finiteModTwoBarDThree ((DSq h : Type) ⧸ U.toSubgroup) c = 0) :
    finiteBarHomotopyTwoAdjointBarDefect
        (sqOpenQuotientMarking h U)
        (sqOpenQuotientFreeEvaluation_surjective h U) c +
      finiteUniversalThreeAdjointFiniteSupportDefect
        (sqOpenQuotientMarking h U)
        (sqOpenQuotientFreeEvaluation_surjective h U) c
        (sqOpenQuotientBarToUniversalRelationTwo h U
          (sqOpenQuotientUniversalThreeAdjointBarChainLift h U hrange c)) = 0 :=
  finiteUniversalThreeAdjointBarChainLiftOfCocycleRange_cancels
    (sqOpenQuotientMarking h U)
    (sqOpenQuotientFreeEvaluation_surjective h U)
    (hrange U) c hc

/-! ## Finite fibers for quotient-compatible cocycle-cancelling outputs -/

/-- A finite-level candidate is recorded by its universal relation output.  It must admit an
actual bar-two representative, have zero universal Fox boundary on input cocycles, and satisfy
the reconstruction cancellation whenever its quotient refines the input quotient. -/
structure SqUniversalCocycleOutputFiber
    (h : ℕ) (V U : OpenNormalSubgroup (DSq h : Type)) where
  output : SqAdjointInputThree h V →ₗ[ZMod 2]
    RegularModTwoRelationModule
      ((DSq h : Type) ⧸ U.toSubgroup)
      (FreeRelationKernel (sqOpenQuotientMarking h U))
  bar_representable : ∃ B : SqAdjointInputThree h V →ₗ[ZMod 2]
      FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup),
    output = (finiteBarToUniversalRelationTwo
      (sqOpenQuotientMarking h U)
      (sqOpenQuotientFreeEvaluation_surjective h U)).comp B
  fox_zero_on_cocycles : ∀ c,
    finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0 →
      (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U)).map (output c) = 0
  cancels_on_refinements : ∀
    (hUV : U.toSubgroup ≤ V.toSubgroup) (c : SqAdjointInputThree h V),
    finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0 →
      finiteBarHomotopyTwoAdjointBarDefect
          (sqOpenQuotientMarking h U)
          (sqOpenQuotientFreeEvaluation_surjective h U)
          (sqFiniteModTwoBarRefineThree h hUV c) +
        finiteUniversalThreeAdjointFiniteSupportDefect
          (sqOpenQuotientMarking h U)
          (sqOpenQuotientFreeEvaluation_surjective h U)
          (sqFiniteModTwoBarRefineThree h hUV c) (output c) = 0

@[ext] theorem SqUniversalCocycleOutputFiber.ext
    {h : ℕ} {V U : OpenNormalSubgroup (DSq h : Type)}
    {x y : SqUniversalCocycleOutputFiber h V U}
    (hout : x.output = y.output) : x = y := by
  cases x
  cases y
  cases hout
  rfl

/-- A solution of the strengthened refined range condition supplies an actual local fiber.
Bar representability is built into the output; the two conclusions of the exact lift theorem
give Fox-zero and cocycle cancellation respectively. -/
noncomputable def sqUniversalCocycleOutputFiberOfSyzygyBarRangeAt
    (h : ℕ) (V U : OpenNormalSubgroup (DSq h : Type))
    (hUV : U.toSubgroup ≤ V.toSubgroup)
    (hrange : SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeAt h V U hUV) :
    SqUniversalCocycleOutputFiber h V U := by
  let hexists := (sqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeAt_iff
    h V U hUV).mp hrange
  let B := Classical.choose hexists
  have hB := Classical.choose_spec hexists
  refine {
    output := (finiteBarToUniversalRelationTwo
      (sqOpenQuotientMarking h U)
      (sqOpenQuotientFreeEvaluation_surjective h U)).comp B
    bar_representable := ⟨B, rfl⟩
    fox_zero_on_cocycles := fun c hc => ?_
    cancels_on_refinements := fun hUV' c hc => ?_
  }
  · change finiteUniversalThreeBarInputFoxBoundary
      (sqOpenQuotientMarking h U)
      (sqOpenQuotientFreeEvaluation_surjective h U) (B c) = 0
    exact (hB c hc).2
  · have hproof : hUV' = hUV := Subsingleton.elim _ _
    cases hproof
    have hspec : finiteUniversalThreeBarInputCorrection
        (sqOpenQuotientMarking h U)
        (sqOpenQuotientFreeEvaluation_surjective h U) (B c) =
      finiteUniversalThreeAdjointCocycleTarget
        (sqOpenQuotientMarking h U)
        (sqOpenQuotientFreeEvaluation_surjective h U)
        (sqFiniteModTwoBarRefineThree h hUV c) := by
      simpa [B, sqFiniteUniversalThreeAdjointCocycleTargetAt] using (hB c hc).1
    exact finiteUniversalThreeAdjointBarInput_cancels_of_spec
      (sqOpenQuotientMarking h U)
      (sqOpenQuotientFreeEvaluation_surjective h U)
      (sqFiniteModTwoBarRefineThree h hUV c) (B c) hspec

/-- Each output fiber is finite: choose one bar-two representative of every output and inject
the fiber into the finite type of linear maps between the two finite quotient spaces. -/
noncomputable instance SqUniversalCocycleOutputFiber.instFinite
    (h : ℕ) (V U : OpenNormalSubgroup (DSq h : Type)) :
    Finite (SqUniversalCocycleOutputFiber h V U) := by
  classical
  letI : Finite ((DSq h : Type) ⧸ V.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen V.toSubgroup V.isOpen'
  letI : Finite ((DSq h : Type) ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
  letI : Fintype ((DSq h : Type) ⧸ V.toSubgroup) := Fintype.ofFinite _
  letI : Fintype ((DSq h : Type) ⧸ U.toSubgroup) := Fintype.ofFinite _
  letI : Fintype (SqAdjointInputThree h V) := Fintype.ofFinite _
  letI : Fintype
      (FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :=
    Finsupp.fintype
  letI : Finite (SqAdjointInputThree h V →ₗ[ZMod 2]
      FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :=
    Finite.of_injective
      (fun f : SqAdjointInputThree h V →ₗ[ZMod 2]
        FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup) =>
          (f : SqAdjointInputThree h V →
            FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)))
      LinearMap.coe_injective
  let representative (x : SqUniversalCocycleOutputFiber h V U) :
      SqAdjointInputThree h V →ₗ[ZMod 2]
        FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup) :=
    Classical.choose x.bar_representable
  apply Finite.of_injective representative
  intro x y hxy
  apply SqUniversalCocycleOutputFiber.ext
  have hx := Classical.choose_spec x.bar_representable
  have hy := Classical.choose_spec y.bar_representable
  rw [hx, hy]
  apply congrArg
  simpa [representative] using hxy

/-- The exact transition-closure premise.  Pushforward of a candidate universal output is
required to remain bar-representable and to retain cocycle cancellation at the coarser level.
Fox-zero preservation is automatic from naturality of the universal Fox boundary. -/
def SqUniversalCocycleOutputTransitionClosed
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) : Prop :=
  ∀ {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (x : SqUniversalCocycleOutputFiber h V U),
    (∃ B' : SqAdjointInputThree h V →ₗ[ZMod 2]
        FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U'.toSubgroup),
      (sqUniversalRelationModuleTransition h hUU').comp x.output =
        (finiteBarToUniversalRelationTwo
          (sqOpenQuotientMarking h U')
          (sqOpenQuotientFreeEvaluation_surjective h U')).comp B') ∧
    (∀ (hU'V : U'.toSubgroup ≤ V.toSubgroup)
      (c : SqAdjointInputThree h V),
      finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0 →
        finiteBarHomotopyTwoAdjointBarDefect
            (sqOpenQuotientMarking h U')
            (sqOpenQuotientFreeEvaluation_surjective h U')
            (sqFiniteModTwoBarRefineThree h hU'V c) +
          finiteUniversalThreeAdjointFiniteSupportDefect
            (sqOpenQuotientMarking h U')
            (sqOpenQuotientFreeEvaluation_surjective h U')
            (sqFiniteModTwoBarRefineThree h hU'V c)
            (sqUniversalRelationModuleTransition h hUU' (x.output c)) = 0)

/-- Push a candidate fiber point to a coarser quotient under the exact closure premise. -/
noncomputable def sqUniversalCocycleOutputFiberTransition
    {h : ℕ} {V U U' : OpenNormalSubgroup (DSq h : Type)}
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (hUU' : U ≤ U') :
    SqUniversalCocycleOutputFiber h V U →
      SqUniversalCocycleOutputFiber h V U' := fun x => by
  let output' := (sqUniversalRelationModuleTransition h hUU').comp x.output
  refine {
    output := output'
    bar_representable := (hclosed hUU' x).1
    fox_zero_on_cocycles := fun c hc => ?_
    cancels_on_refinements := (hclosed hUU' x).2
  }
  have hfox := sqUniversalRelationFoxBoundary_natural h hUU' (x.output c)
  rw [x.fox_zero_on_cocycles c hc, map_zero] at hfox
  exact hfox.symm

@[simp] theorem sqUniversalCocycleOutputFiberTransition_output
    {h : ℕ} {V U U' : OpenNormalSubgroup (DSq h : Type)}
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (hUU' : U ≤ U') (x : SqUniversalCocycleOutputFiber h V U) :
    (sqUniversalCocycleOutputFiberTransition hclosed hUU' x).output =
      (sqUniversalRelationModuleTransition h hUU').comp x.output := by
  rfl

/-- Universal relation-module transition is the identity at an identity refinement. -/
theorem sqUniversalRelationModuleTransition_id
    (h : ℕ) (U : OpenNormalSubgroup (DSq h : Type))
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ U.toSubgroup)
      (FreeRelationKernel (sqOpenQuotientMarking h U))) :
    sqUniversalRelationModuleTransition h (le_refl U) c = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, r⟩
      simp only [map_add, ih, sqUniversalRelationModuleTransition_single]
      congr 2
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup g
      rfl

/-- Universal relation-module transitions compose along refinement towers. -/
theorem sqUniversalRelationModuleTransition_comp
    (h : ℕ) {U U' U'' : OpenNormalSubgroup (DSq h : Type)}
    (hUU' : U ≤ U') (hU'U'' : U' ≤ U'')
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ U.toSubgroup)
      (FreeRelationKernel (sqOpenQuotientMarking h U))) :
    sqUniversalRelationModuleTransition h hU'U''
        (sqUniversalRelationModuleTransition h hUU' c) =
      sqUniversalRelationModuleTransition h (hUU'.trans hU'U'') c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, r⟩
      simp only [map_add, ih, sqUniversalRelationModuleTransition_single]
      congr 2
      apply Prod.ext
      · exact DFunLike.congr_fun
          (modTwoQuotientTransition_comp (DSq h : Type) hUU' hU'U'') g
      · apply Subtype.ext
        rfl

/-- The finite cocycle-output fibers form a cofiltered functor once the exact transition-closure
equations are supplied. -/
noncomputable def sqUniversalCocycleOutputFiberFunctor
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V) :
    OpenNormalSubgroup (DSq h : Type) ⥤ Type where
  obj U := SqUniversalCocycleOutputFiber h V U
  map f := ↾(sqUniversalCocycleOutputFiberTransition hclosed (leOfHom f))
  map_id U := by
    ext x c z
    exact congrArg (fun y => y z)
      (sqUniversalRelationModuleTransition_id h U (x.output c))
  map_comp f g := by
    ext x c z
    exact congrArg (fun y => y z)
      (sqUniversalRelationModuleTransition_comp h
        (leOfHom f) (leOfHom g) (x.output c)).symm

/-- Output of the finite compactness argument: a literally compatible universal bar syzygy,
with completed Fox boundary zero on input cocycles and with the required cancellation at the
input quotient. -/
structure SqCompatibleUniversalCocycleCancellingSyzygyAt
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) where
  universalSyzygy : SqCompatibleFiniteUniversalBarSyzygyAt h V
  fox_zero_on_cocycles : ∀ c,
    finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0 →
      universalSyzygy.toCompletedFox c = 0
  cancels_at_input : ∀ c,
    finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0 →
      finiteBarHomotopyTwoAdjointBarDefect
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V)
          (sqFiniteModTwoBarRefineThree h (le_refl V.toSubgroup) c) +
        finiteUniversalThreeAdjointFiniteSupportDefect
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V)
          (sqFiniteModTwoBarRefineThree h (le_refl V.toSubgroup) c)
          (universalSyzygy.coordinate V c) = 0

/-- **Finite cofiltered compactness for the corrected universal outputs.** Transition closure
and nonemptiness of every finite fiber produce a compatible universal syzygy.  No surjectivity
of transition maps is assumed. -/
theorem nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_fibers
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (hnonempty : ∀ U : OpenNormalSubgroup (DSq h : Type),
      Nonempty (SqUniversalCocycleOutputFiber h V U)) :
    Nonempty (SqCompatibleUniversalCocycleCancellingSyzygyAt h V) := by
  classical
  let F := sqUniversalCocycleOutputFiberFunctor h V hclosed
  letI (U : OpenNormalSubgroup (DSq h : Type)) : Nonempty (F.obj U) :=
    hnonempty U
  letI (U : OpenNormalSubgroup (DSq h : Type)) : Finite (F.obj U) :=
    SqUniversalCocycleOutputFiber.instFinite h V U
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_cofiltered_system F
  let barRepresentative (U : OpenNormalSubgroup (DSq h : Type)) :
      SqAdjointInputThree h V →ₗ[ZMod 2]
        FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup) :=
    Classical.choose (sec U).bar_representable
  have hbarRepresentative (U : OpenNormalSubgroup (DSq h : Type)) :
      (sec U).output =
        (finiteBarToUniversalRelationTwo
          (sqOpenQuotientMarking h U)
          (sqOpenQuotientFreeEvaluation_surjective h U)).comp
            (barRepresentative U) :=
    Classical.choose_spec (sec U).bar_representable
  let S : SqCompatibleFiniteUniversalBarSyzygyAt h V := {
    barChain := fun U => (barRepresentative U).toAddMonoidHom
    compatible := by
      intro U U' hUU' c
      have hs := hsec (homOfLE hUU')
      have hsout := congrArg
        (fun z : SqUniversalCocycleOutputFiber h V U' => z.output c) hs
      have hsout' :
          (sqUniversalCocycleOutputFiberTransition hclosed hUU' (sec U)).output c =
            (sec U').output c := hsout
      have hbarU := DFunLike.congr_fun (hbarRepresentative U) c
      have hbarU' := DFunLike.congr_fun (hbarRepresentative U') c
      change sqUniversalRelationModuleTransition h hUU'
          (finiteBarToUniversalRelationTwo
            (sqOpenQuotientMarking h U)
            (sqOpenQuotientFreeEvaluation_surjective h U)
            (barRepresentative U c)) =
        finiteBarToUniversalRelationTwo
          (sqOpenQuotientMarking h U')
          (sqOpenQuotientFreeEvaluation_surjective h U')
          (barRepresentative U' c)
      calc
        _ = sqUniversalRelationModuleTransition h hUU' ((sec U).output c) :=
          congrArg (sqUniversalRelationModuleTransition h hUU') hbarU.symm
        _ = (sqUniversalCocycleOutputFiberTransition hclosed hUU' (sec U)).output c :=
          (DFunLike.congr_fun
            (sqUniversalCocycleOutputFiberTransition_output hclosed hUU' (sec U)) c).symm
        _ = (sec U').output c := hsout'
        _ = _ := hbarU'
  }
  refine ⟨{
    universalSyzygy := S
    fox_zero_on_cocycles := fun c hc => ?_
    cancels_at_input := fun c hc => ?_
  }⟩
  · apply ModTwoCompletedRegularModule.ext (DSq h : Type) (Fin (sqRank h))
    intro U
    rw [SqCompatibleFiniteUniversalBarSyzygyAt.coordinate_toCompletedFox]
    change (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U)).map
      (finiteBarToUniversalRelationTwo
        (sqOpenQuotientMarking h U)
        (sqOpenQuotientFreeEvaluation_surjective h U)
        (barRepresentative U c)) = 0
    have hbarU := DFunLike.congr_fun (hbarRepresentative U) c
    calc
      _ = (finiteUniversalRelationFoxBoundary
          (sqOpenQuotientMarking h U)).map ((sec U).output c) :=
        congrArg (finiteUniversalRelationFoxBoundary
          (sqOpenQuotientMarking h U)).map hbarU.symm
      _ = 0 := (sec U).fox_zero_on_cocycles c hc
  · change finiteBarHomotopyTwoAdjointBarDefect
        (sqOpenQuotientMarking h V)
        (sqOpenQuotientFreeEvaluation_surjective h V)
        (sqFiniteModTwoBarRefineThree h (le_refl V.toSubgroup) c) +
      finiteUniversalThreeAdjointFiniteSupportDefect
        (sqOpenQuotientMarking h V)
        (sqOpenQuotientFreeEvaluation_surjective h V)
        (sqFiniteModTwoBarRefineThree h (le_refl V.toSubgroup) c)
        (finiteBarToUniversalRelationTwo
          (sqOpenQuotientMarking h V)
          (sqOpenQuotientFreeEvaluation_surjective h V)
          (barRepresentative V c)) = 0
    have hbarV := DFunLike.congr_fun (hbarRepresentative V) c
    simp only [LinearMap.comp_apply] at hbarV
    rw [← hbarV]
    exact (sec V).cancels_on_refinements (le_refl V.toSubgroup) c hc

/-- The cofinal version of local existence.  It is enough to find a candidate below every
finite quotient: transition closure then pushes that candidate to the requested quotient.
This is the exact refinement condition needed when literal nonemptiness of every fiber is not
available directly. -/
def SqUniversalCocycleOutputEventuallyNonempty
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) : Prop :=
  ∀ U : OpenNormalSubgroup (DSq h : Type),
    ∃ W : OpenNormalSubgroup (DSq h : Type), ∃ _hWU : W ≤ U,
      Nonempty (SqUniversalCocycleOutputFiber h V W)

/-- Concrete cofinal local obligation which implies eventual fiber nonemptiness: below every
requested quotient, find a common refinement of it and the input quotient where the coupled
target lifts through the correction map restricted to the Fox kernel. -/
def SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) : Prop :=
  ∀ U : OpenNormalSubgroup (DSq h : Type),
    ∃ W : OpenNormalSubgroup (DSq h : Type), ∃ _hWU : W ≤ U,
      ∃ hWV : W ≤ V,
        SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeAt h V W hWV

/-- The cofinal strengthened range premise produces the exact eventual nonemptiness premise
used by finite cofiltered compactness. -/
theorem sqUniversalCocycleOutputEventuallyNonempty_of_syzygyBarCofinalRange
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (hrange : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V) :
    SqUniversalCocycleOutputEventuallyNonempty h V := by
  intro U
  obtain ⟨W, hWU, hWV, hrangeW⟩ := hrange U
  exact ⟨W, hWU,
    ⟨sqUniversalCocycleOutputFiberOfSyzygyBarRangeAt h V W hWV hrangeW⟩⟩

theorem sqUniversalCocycleOutputFiber_nonempty_of_eventuallyNonempty
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (heventual : SqUniversalCocycleOutputEventuallyNonempty h V)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    Nonempty (SqUniversalCocycleOutputFiber h V U) := by
  obtain ⟨W, hWU, ⟨x⟩⟩ := heventual U
  exact ⟨sqUniversalCocycleOutputFiberTransition hclosed hWU x⟩

/-- Cofinal local existence plus transition closure gives the same compatible global package.
No transition-surjectivity hypothesis is needed. -/
theorem nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_eventuallyNonempty
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (heventual : SqUniversalCocycleOutputEventuallyNonempty h V) :
    Nonempty (SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :=
  nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_fibers h V hclosed
    (sqUniversalCocycleOutputFiber_nonempty_of_eventuallyNonempty hclosed heventual)

/-- Fox-zero on cocycles is exactly the kernel condition needed to factor the completed
universal Fox output through `d³`.  The factorization is independent of the later adjoint
reconstruction factorization. -/
noncomputable def SqCompatibleUniversalCocycleCancellingSyzygyAt.syzygyBoundary
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :
    SqFiniteInputUniversalSyzygyBoundaryAt h V := by
  let d := (finiteModTwoBarDThree
    ((DSq h : Type) ⧸ V.toSubgroup)).toZModLinearMap 2
  let T := S.universalSyzygy.toCompletedFox.toZModLinearMap 2
  have hker : LinearMap.ker d ≤ LinearMap.ker T := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    apply S.fox_zero_on_cocycles c
    simpa [d] using hc
  let onRange : LinearMap.range d →ₗ[ZMod 2]
      ModTwoCompletedRegularModule (DSq h : Type) (Fin (sqRank h)) :=
    ((LinearMap.ker d).liftQ T hker).comp
      d.quotKerEquivRange.symm.toLinearMap
  let hExtend := LinearMap.exists_extend onRange
  let D := Classical.choose hExtend
  have hD := Classical.choose_spec hExtend
  refine {
    universalSyzygy := S.universalSyzygy
    boundaryDefect := D.toAddMonoidHom
    boundary_universalSyzygy := fun c => ?_
  }
  change T c = D (d c)
  let dc : LinearMap.range d := ⟨d c, ⟨c, rfl⟩⟩
  symm
  calc
    D (d c) = D ((LinearMap.range d).subtype dc) := rfl
    _ = onRange dc := LinearMap.congr_fun hD dc
    _ = T c := by simp [onRange, dc]

/-- The combined fixed-quotient residual that must factor through `d³`.  It contains the
refined input, the `d²H₂†` term, and the finite-support universal correction chosen by the
compatible universal syzygy. -/
def sqFiniteInputUniversalAdjointReconstructionResidual
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup) :
    SqAdjointInputThree h V →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup) :=
  let m := sqOpenQuotientMarking h W
  let heval := sqOpenQuotientFreeEvaluation_surjective h W
  sqFiniteModTwoBarRefineThree h hWV +
    (finiteModTwoBarDTwo ((DSq h : Type) ⧸ W.toSubgroup)).comp
      ((finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval).toAddMonoidHom.comp
        (sqFiniteModTwoBarRefineThree h hWV)) +
    (finiteUniversalRelationThreeFiniteSupportCorrection m heval).toAddMonoidHom.comp
      (U.universalSyzygy.coordinate W)

/-- The combined residual is exactly the sum of the `H₃†d³` term, the raw non-invariance
defect, and the universal finite-support defect.  In particular, truncating the unrestricted
universal adjoint kills only the last term; it does not make the raw bar defect factor through
`d³`. -/
theorem sqFiniteInputUniversalAdjointReconstructionResidual_eq_explicitDefects
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : SqAdjointInputThree h V) :
    sqFiniteInputUniversalAdjointReconstructionResidual U W hWV c =
      finiteBarForwardReverseHomotopyThreeCochainAdjoint
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (finiteModTwoBarDThree ((DSq h : Type) ⧸ W.toSubgroup)
            (sqFiniteModTwoBarRefineThree h hWV c)) +
        finiteBarHomotopyTwoAdjointBarDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c) +
        finiteUniversalThreeAdjointFiniteSupportDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c)
          (U.universalSyzygy.coordinate W c) := by
  let m := sqOpenQuotientMarking h W
  let heval := sqOpenQuotientFreeEvaluation_surjective h W
  let cW := sqFiniteModTwoBarRefineThree h hWV c
  let u := U.universalSyzygy.coordinate W c
  have hid := finiteBarForwardReverseHomotopyThree_cochain_identity_with_defects
    m heval cW u
  funext a
  have ha := congrFun hid a
  simp only [sqFiniteInputUniversalAdjointReconstructionResidual,
    AddMonoidHom.add_apply, AddMonoidHom.comp_apply]
  let A : ZMod 2 := finiteBarForwardReverseHomotopyThreeCochainAdjoint m heval
    (finiteModTwoBarDThree ((DSq h : Type) ⧸ W.toSubgroup) cW) a
  let D : ZMod 2 := finiteModTwoBarDTwo ((DSq h : Type) ⧸ W.toSubgroup)
    (finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval cW) a
  let F : ZMod 2 := finiteUniversalRelationThreeFiniteSupportCorrection m heval u a
  let B : ZMod 2 := finiteBarHomotopyTwoAdjointBarDefect m heval cW a
  let T : ZMod 2 := finiteUniversalThreeAdjointFiniteSupportDefect m heval cW u a
  let C : ZMod 2 := cW a
  change C + D + F = A + B + T
  change A + D + F + B + T = C at ha
  calc
    C + D + F = (A + D + F + B + T) + D + F := by rw [ha]
    _ = A + B + T + (D + D) + (F + F) := by abel
    _ = A + B + T := by
      rw [ZModModule.add_self, ZModModule.add_self]
      simp

/-- On an input three-cocycle, the `H₃†d³` term vanishes after refinement.  The combined
residual is therefore exactly the raw bar defect plus the universal finite-support defect. -/
theorem sqFiniteInputUniversalAdjointReconstructionResidual_of_cocycle
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : SqAdjointInputThree h V)
    (hc : finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0) :
    sqFiniteInputUniversalAdjointReconstructionResidual U W hWV c =
      finiteBarHomotopyTwoAdjointBarDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c) +
        finiteUniversalThreeAdjointFiniteSupportDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c)
          (U.universalSyzygy.coordinate W c) := by
  rw [sqFiniteInputUniversalAdjointReconstructionResidual_eq_explicitDefects]
  have hrefine := DFunLike.congr_fun (finiteModTwoBarDThree_refine h hWV) c
  simp only [AddMonoidHom.comp_apply] at hrefine
  rw [hc, map_zero] at hrefine
  rw [hrefine, map_zero, zero_add]

/-- The exact quotient-coordinate condition needed from a compatible universal syzygy: on
three-cocycles, its universal defect cancels the raw non-invariance defect.  Requiring the
universal defect itself to vanish would be too strong in the wrong direction unless the raw bar
defect also vanished. -/
def SqFiniteInputUniversalAdjointCocycleCancellationAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup) : Prop :=
  ∀ c : SqAdjointInputThree h V,
    finiteModTwoBarDThree ((DSq h : Type) ⧸ V.toSubgroup) c = 0 →
      finiteBarHomotopyTwoAdjointBarDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c) +
        finiteUniversalThreeAdjointFiniteSupportDefect
          (sqOpenQuotientMarking h W)
          (sqOpenQuotientFreeEvaluation_surjective h W)
          (sqFiniteModTwoBarRefineThree h hWV c)
          (U.universalSyzygy.coordinate W c) = 0

/-- The compactness output satisfies the exact fixed-input cancellation premise for its
induced universal syzygy boundary. -/
theorem SqCompatibleUniversalCocycleCancellingSyzygyAt.cocycleCancellation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :
    SqFiniteInputUniversalAdjointCocycleCancellationAt
      S.syzygyBoundary V (le_refl V.toSubgroup) := by
  intro c hc
  exact S.cancels_at_input c hc

/-- Cocycle cancellation is precisely enough for the kernel inclusion required by the linear
factorization constructor. -/
theorem sqFiniteInputUniversalAdjoint_ker_le_ker_of_cocycleCancellation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (hcancel : SqFiniteInputUniversalAdjointCocycleCancellationAt U W hWV) :
    LinearMap.ker
        ((finiteModTwoBarDThree
          ((DSq h : Type) ⧸ V.toSubgroup)).toZModLinearMap 2) ≤
      LinearMap.ker
        ((sqFiniteInputUniversalAdjointReconstructionResidual U W hWV).toZModLinearMap 2) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have hc' : finiteModTwoBarDThree
      ((DSq h : Type) ⧸ V.toSubgroup) c = 0 := by
    simpa using hc
  simpa using (sqFiniteInputUniversalAdjointReconstructionResidual_of_cocycle
    U W hWV c hc').trans (hcancel c hc')

/-- The exact residual factorization needed by the existing universal degree-three comparison
interface.  The field is deliberately named for its role in that interface; it need not equal
the raw non-invariance defect of `H₂†`. -/
structure SqFiniteInputUniversalAdjointResidualFactorizationAt
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup) where
  barDefect :
    SqAdjointInputFour h V →+
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup)
  factor : ∀ c,
    barDefect (finiteModTwoBarDThree _ c) =
      sqFiniteInputUniversalAdjointReconstructionResidual U W hWV c

/-- Linear algebra turns the kernel criterion for the combined residual into the required
factorization.  First descend through `C³ / ker d³ ≃ range d³`, then extend the resulting map
from `range d³` to all of `C⁴`. -/
noncomputable def
    SqFiniteInputUniversalAdjointResidualFactorizationAt.of_ker_le_ker
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (hker :
      LinearMap.ker
          ((finiteModTwoBarDThree
            ((DSq h : Type) ⧸ V.toSubgroup)).toZModLinearMap 2) ≤
        LinearMap.ker
          ((sqFiniteInputUniversalAdjointReconstructionResidual U W hWV).toZModLinearMap 2)) :
    SqFiniteInputUniversalAdjointResidualFactorizationAt U W hWV := by
  let d := (finiteModTwoBarDThree
    ((DSq h : Type) ⧸ V.toSubgroup)).toZModLinearMap 2
  let E :=
    (sqFiniteInputUniversalAdjointReconstructionResidual U W hWV).toZModLinearMap 2
  let onRange : LinearMap.range d →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ W.toSubgroup) :=
    ((LinearMap.ker d).liftQ E hker).comp
      d.quotKerEquivRange.symm.toLinearMap
  let hExtend := LinearMap.exists_extend onRange
  let D := Classical.choose hExtend
  have hD := Classical.choose_spec hExtend
  refine {
    barDefect := D.toAddMonoidHom
    factor := fun c => ?_
  }
  change D (d c) = E c
  let dc : LinearMap.range d := ⟨d c, ⟨c, rfl⟩⟩
  calc
    D (d c) = D ((LinearMap.range d).subtype dc) := rfl
    _ = onRange dc := LinearMap.congr_fun hD dc
    _ = E c := by
      simp [onRange, dc]

/-- A factorization of the combined residual through `d³` fills all fields of
`SqFiniteInputUniversalDegreeThreeComparisonAt` at the chosen finite quotient. -/
def SqFiniteInputUniversalDegreeThreeComparisonAt.ofAdjointResidualFactorization
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (F : SqFiniteInputUniversalAdjointResidualFactorizationAt U W hWV) :
    SqFiniteInputUniversalDegreeThreeComparisonAt h V where
  W := W
  le := hWV
  homotopyTwo :=
    (finiteBarForwardReverseHomotopyTwoCochainAdjoint
      (sqOpenQuotientMarking h W)
      (sqOpenQuotientFreeEvaluation_surjective h W)).toAddMonoidHom.comp
        (sqFiniteModTwoBarRefineThree h hWV)
  universalSyzygy := U.universalSyzygy
  universalRelationError :=
    (finiteUniversalRelationThreeFiniteSupportCorrection
      (sqOpenQuotientMarking h W)
      (sqOpenQuotientFreeEvaluation_surjective h W)).toAddMonoidHom
  boundaryDefect := U.boundaryDefect
  barDefect := F.barDefect
  boundary_universalSyzygy := U.boundary_universalSyzygy
  reconstruct c := by
    rw [F.factor]
    funext a
    simp only [sqFiniteInputUniversalAdjointReconstructionResidual,
      AddMonoidHom.add_apply, AddMonoidHom.comp_apply]
    let C : ZMod 2 := sqFiniteModTwoBarRefineThree h hWV c a
    let D : ZMod 2 := finiteModTwoBarDTwo ((DSq h : Type) ⧸ W.toSubgroup)
      (finiteBarForwardReverseHomotopyTwoCochainAdjoint
        (sqOpenQuotientMarking h W)
        (sqOpenQuotientFreeEvaluation_surjective h W)
        (sqFiniteModTwoBarRefineThree h hWV c)) a
    let R : ZMod 2 := finiteUniversalRelationThreeFiniteSupportCorrection
      (sqOpenQuotientMarking h W)
      (sqOpenQuotientFreeEvaluation_surjective h W)
      (U.universalSyzygy.coordinate W c) a
    change D + R + (C + D + R) = C
    calc
      D + R + (C + D + R) = C + (D + D) + (R + R) := by abel
      _ = C := by
        rw [ZModModule.add_self, ZModModule.add_self]
        simp

/-- Final fixed-quotient constructor: a compatible universal syzygy whose coordinate cancels
the raw bar defect on cocycles automatically supplies the residual factorization and hence the
full existing degree-three comparison interface. -/
noncomputable def
    SqFiniteInputUniversalDegreeThreeComparisonAt.ofAdjointCocycleCancellation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (hcancel : SqFiniteInputUniversalAdjointCocycleCancellationAt U W hWV) :
    SqFiniteInputUniversalDegreeThreeComparisonAt h V :=
  .ofAdjointResidualFactorization U W hWV
    (.of_ker_le_ker U W hWV
      (sqFiniteInputUniversalAdjoint_ker_le_ker_of_cocycleCancellation
        U W hWV hcancel))

/-- Once universal cocycle cancellation has produced the genuine comparison interface, the
existing eventual relation-generation theorem performs the logically separate lift from the
universal relation kernel to the single improved relator. -/
noncomputable def
    SqFiniteInputCompletedSyzygyBoundaryAt.ofAdjointCocycleCancellation
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (U : SqFiniteInputUniversalSyzygyBoundaryAt h V)
    (W : OpenNormalSubgroup (DSq h : Type))
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (hcancel : SqFiniteInputUniversalAdjointCocycleCancellationAt U W hWV)
    (hgen : SqEventualRelationFoxGeneration h) :
    SqFiniteInputCompletedSyzygyBoundaryAt h V :=
  (SqFiniteInputUniversalDegreeThreeComparisonAt.ofAdjointCocycleCancellation
    U W hWV hcancel).completedSyzygyBoundaryOfEventualGeneration hgen

/-- End-to-end constructor from the compactness output to the genuine universal
degree-three comparison. -/
noncomputable def
    SqCompatibleUniversalCocycleCancellingSyzygyAt.degreeThreeComparison
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V) :
    SqFiniteInputUniversalDegreeThreeComparisonAt h V :=
  .ofAdjointCocycleCancellation S.syzygyBoundary V (le_refl V.toSubgroup)
    S.cocycleCancellation

/-- Finite cofiltered compactness, stated directly at the genuine comparison endpoint. -/
theorem nonempty_sqFiniteInputUniversalDegreeThreeComparisonAt_of_fibers
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (hnonempty : ∀ U : OpenNormalSubgroup (DSq h : Type),
      Nonempty (SqUniversalCocycleOutputFiber h V U)) :
    Nonempty (SqFiniteInputUniversalDegreeThreeComparisonAt h V) :=
  (nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_fibers
    h V hclosed hnonempty).map
      SqCompatibleUniversalCocycleCancellingSyzygyAt.degreeThreeComparison

/-- The cofinal/refinement form of the compactness endpoint. -/
theorem nonempty_sqFiniteInputUniversalDegreeThreeComparisonAt_of_eventuallyNonempty
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (heventual : SqUniversalCocycleOutputEventuallyNonempty h V) :
    Nonempty (SqFiniteInputUniversalDegreeThreeComparisonAt h V) :=
  (nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_eventuallyNonempty
    h V hclosed heventual).map
      SqCompatibleUniversalCocycleCancellingSyzygyAt.degreeThreeComparison

/-- After the separate eventual relation-generation theorem, the same compactness output
reaches the completed single-relator syzygy boundary used by the counting theorem. -/
noncomputable def
    SqCompatibleUniversalCocycleCancellingSyzygyAt.completedSyzygyBoundary
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (S : SqCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (hgen : SqEventualRelationFoxGeneration h) :
    SqFiniteInputCompletedSyzygyBoundaryAt h V :=
  S.degreeThreeComparison.completedSyzygyBoundaryOfEventualGeneration hgen

/-- Cofinal local solvability, transition closure, and the independent eventual
single-relator generation premise give the completed comparison package. -/
theorem nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_eventuallyNonempty
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (heventual : SqUniversalCocycleOutputEventuallyNonempty h V)
    (hgen : SqEventualRelationFoxGeneration h) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  (nonempty_sqCompatibleUniversalCocycleCancellingSyzygyAt_of_eventuallyNonempty
    h V hclosed heventual).map fun S => S.completedSyzygyBoundary hgen

/-- Strongest honest endpoint from the local calculation: the Fox-kernel range condition is
required only cofinally, while quotient-transition closure remains a separate premise. -/
theorem nonempty_sqFiniteInputUniversalDegreeThreeComparisonAt_of_syzygyBarCofinalRange
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (hrange : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V) :
    Nonempty (SqFiniteInputUniversalDegreeThreeComparisonAt h V) :=
  nonempty_sqFiniteInputUniversalDegreeThreeComparisonAt_of_eventuallyNonempty
    h V hclosed
      (sqUniversalCocycleOutputEventuallyNonempty_of_syzygyBarCofinalRange hrange)

/-- Adding the independent eventual generation of the improved relator reaches the completed
single-relator syzygy boundary. -/
theorem nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_syzygyBarCofinalRange
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hclosed : SqUniversalCocycleOutputTransitionClosed h V)
    (hrange : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V)
    (hgen : SqEventualRelationFoxGeneration h) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_eventuallyNonempty
    h V hclosed
      (sqUniversalCocycleOutputEventuallyNonempty_of_syzygyBarCofinalRange hrange) hgen

end

end GQ2.Dyadic.Count
