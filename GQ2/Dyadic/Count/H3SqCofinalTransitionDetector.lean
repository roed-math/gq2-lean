/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqUnconditionalDegreeThree

/-!
# Cofinal transition detectors for the square presentation

This file first discharges the relation-generation input in the new range-good cofinal
degree-three endpoints.  It then packages the two transition obstructions attached to a common
source into one finite detector.  The resulting reduction makes precise what remains beyond
the already proved pro-two detector argument: the universal-relation basis is not presently
equipped with a group-valued detector compatible with refinement.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

/-! ## Unconditional range-good cofinal wrappers -/

/-- The minimal range-good cofinal hypotheses reach the completed square-presentation
endpoint, with eventual improved-relator generation discharged unconditionally. -/
theorem
    nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_rangeGoodCofinal_unconditional
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeGoodCofinalAt h V)
    (hcommon : SqUniversalBarInputTransitionCommonRefinementRange h)
    (hkernel : SqUniversalBarInputCocycleCancellationTransitionKernel h V) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_rangeGoodCofinal
    h V hlocal hcommon hkernel (sqEventualRelationFoxGeneration h)

/-- Pairwise eventual transition range plus downward stability is a convenient sufficient
form of the unconditional completed square-presentation endpoint. -/
theorem
    nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_eventualTransitionRange_unconditional
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarCofinalRangeAt h V)
    (heventual : SqUniversalBarInputTransitionEventuallyRange h)
    (hstable : SqUniversalBarInputTransitionRangeDownwardStable h)
    (hkernel : SqUniversalBarInputCocycleCancellationTransitionKernel h V) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_eventualTransitionRange
    h V hlocal heventual hstable hkernel (sqEventualRelationFoxGeneration h)

/-- Regression endpoint for the weakest current transition hypotheses. -/
theorem sqCompletedDegreeThree_rangeGoodCofinal_regression
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeGoodCofinalAt h V)
    (hcommon : SqUniversalBarInputTransitionCommonRefinementRange h)
    (hkernel : SqUniversalBarInputCocycleCancellationTransitionKernel h V) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_rangeGoodCofinal_unconditional
    h V hlocal hcommon hkernel

/-! ## The simultaneous finite detector -/

/-- Cokernel which detects failure of bar-input representability at one target quotient. -/
abbrev SqUniversalBarInputTransitionCokernel (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) :=
  RegularModTwoRelationModule
      ((DSq h : Type) ⧸ U.toSubgroup)
      (FreeRelationKernel (sqOpenQuotientMarking h U)) ⧸
    LinearMap.range (sqOpenQuotientBarToUniversalRelationTwo h U)

/-- One linear map records both target obstructions from a specified common source. -/
def sqUniversalBarInputTransitionPairObstruction
    (h : ℕ) {W U U' : OpenNormalSubgroup (DSq h : Type)}
    (hWU : W ≤ U) (hWU' : W ≤ U') :
    FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ W.toSubgroup) →ₗ[ZMod 2]
      SqUniversalBarInputTransitionCokernel h U ×
        SqUniversalBarInputTransitionCokernel h U' :=
  (sqUniversalBarInputTransitionCokernelObstruction h hWU).prod
    (sqUniversalBarInputTransitionCokernelObstruction h hWU')

/-- The minimal simultaneous detector is the image of the paired obstruction.  Its ambient
cokernels can be infinite, but this image is finite because its bar-two source is finite. -/
abbrev SqUniversalBarInputTransitionPairDetector
    (h : ℕ) {W U U' : OpenNormalSubgroup (DSq h : Type)}
    (hWU : W ≤ U) (hWU' : W ≤ U') :=
  LinearMap.range (sqUniversalBarInputTransitionPairObstruction h hWU hWU')

noncomputable instance sqUniversalBarInputTransitionPairDetector_finite
    (h : ℕ) {W U U' : OpenNormalSubgroup (DSq h : Type)}
    (hWU : W ≤ U) (hWU' : W ≤ U') :
    Finite (SqUniversalBarInputTransitionPairDetector h hWU hWU') := by
  classical
  letI : Finite ((DSq h : Type) ⧸ W.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen W.toSubgroup W.isOpen'
  letI : Fintype ((DSq h : Type) ⧸ W.toSubgroup) := Fintype.ofFinite _
  letI : Fintype (FiniteModTwoBarChainTwo
      ((DSq h : Type) ⧸ W.toSubgroup)) := Finsupp.fintype
  let f := sqUniversalBarInputTransitionPairObstruction h hWU hWU'
  refine Finite.of_surjective
    (fun b => (⟨f b, LinearMap.mem_range_self f b⟩ : LinearMap.range f)) ?_
  rintro ⟨z, b, rfl⟩
  exact ⟨b, rfl⟩

/-- The paired detector is an elementary abelian two-group, hence a finite two-group after
switching from additive to multiplicative notation. -/
theorem sqUniversalBarInputTransitionPairDetector_isPGroup
    (h : ℕ) {W U U' : OpenNormalSubgroup (DSq h : Type)}
    (hWU : W ≤ U) (hWU' : W ≤ U') :
    IsPGroup 2
      (Multiplicative (SqUniversalBarInputTransitionPairDetector h hWU hWU')) := by
  intro x
  refine ⟨1, ?_⟩
  show x ^ 2 = 1
  rw [pow_two, ← ofAdd_toAdd x, ← ofAdd_add, ZModModule.add_self, ofAdd_zero]

/-- The paired obstruction vanishes exactly when its finite image detector is trivial. -/
theorem sqUniversalBarInputTransitionPairObstruction_eq_zero_iff_subsingleton
    (h : ℕ) {W U U' : OpenNormalSubgroup (DSq h : Type)}
    (hWU : W ≤ U) (hWU' : W ≤ U') :
    sqUniversalBarInputTransitionPairObstruction h hWU hWU' = 0 ↔
      Subsingleton (SqUniversalBarInputTransitionPairDetector h hWU hWU') := by
  let f := sqUniversalBarInputTransitionPairObstruction h hWU hWU'
  constructor
  · intro hf
    constructor
    intro x y
    apply Subtype.ext
    obtain ⟨bx, hbx⟩ := x.property
    obtain ⟨b_y, hby⟩ := y.property
    rw [← hbx, ← hby, hf]
    rfl
  · intro hsub
    apply LinearMap.ext
    intro b
    have heq :
        (⟨f b, LinearMap.mem_range_self f b⟩ : LinearMap.range f) =
          ⟨0, Submodule.zero_mem _⟩ := hsub.elim _ _
    exact congrArg Subtype.val heq

theorem sqUniversalBarInputTransitionPairObstruction_eq_zero_iff
    (h : ℕ) {W U U' : OpenNormalSubgroup (DSq h : Type)}
    (hWU : W ≤ U) (hWU' : W ≤ U') :
    sqUniversalBarInputTransitionPairObstruction h hWU hWU' = 0 ↔
      sqUniversalBarInputTransitionCokernelObstruction h hWU = 0 ∧
        sqUniversalBarInputTransitionCokernelObstruction h hWU' = 0 := by
  constructor
  · intro hpair
    constructor
    · apply LinearMap.ext
      intro b
      have hb := DFunLike.congr_fun hpair b
      exact congrArg Prod.fst hb
    · apply LinearMap.ext
      intro b
      have hb := DFunLike.congr_fun hpair b
      exact congrArg Prod.snd hb
  · rintro ⟨hleft, hright⟩
    apply LinearMap.ext
    intro b
    apply Prod.ext
    · exact DFunLike.congr_fun hleft b
    · exact DFunLike.congr_fun hright b

/-- Exact cofinal detector statement: after one common refinement, the single finite paired
detector is trivial. -/
def SqUniversalBarInputTransitionPairDetectorCofinallyTrivial (h : ℕ) : Prop :=
  ∀ U U' : OpenNormalSubgroup (DSq h : Type),
    ∃ W : OpenNormalSubgroup (DSq h : Type), ∃ hWZ : W ≤ U ⊓ U',
      Subsingleton (SqUniversalBarInputTransitionPairDetector h
        (hWZ.trans inf_le_left) (hWZ.trans inf_le_right))

/-- The simultaneous range condition is precisely cofinal triviality of one finite
elementary-abelian detector for each pair of targets. -/
theorem sqUniversalBarInputTransitionCommonRefinementRange_iff_pairDetector
    (h : ℕ) :
    SqUniversalBarInputTransitionCommonRefinementRange h ↔
      SqUniversalBarInputTransitionPairDetectorCofinallyTrivial h := by
  constructor
  · intro hcommon U U'
    obtain ⟨W, hWU, hWU', hgoodU, hgoodU'⟩ := hcommon U U'
    let hWZ : W ≤ U ⊓ U' := le_inf hWU hWU'
    have hleft : sqUniversalBarInputTransitionCokernelObstruction h
        (hWZ.trans inf_le_left) = 0 := by
      convert (sqUniversalBarInputTransitionRangeAt_iff_obstruction_eq_zero
        h hWU).mp hgoodU
    have hright : sqUniversalBarInputTransitionCokernelObstruction h
        (hWZ.trans inf_le_right) = 0 := by
      convert (sqUniversalBarInputTransitionRangeAt_iff_obstruction_eq_zero
        h hWU').mp hgoodU'
    refine ⟨W, hWZ, ?_⟩
    exact (sqUniversalBarInputTransitionPairObstruction_eq_zero_iff_subsingleton
      h (hWZ.trans inf_le_left) (hWZ.trans inf_le_right)).mp
        ((sqUniversalBarInputTransitionPairObstruction_eq_zero_iff
          h (hWZ.trans inf_le_left) (hWZ.trans inf_le_right)).mpr ⟨hleft, hright⟩)
  · intro hdet U U'
    obtain ⟨W, hWZ, htrivial⟩ := hdet U U'
    have hpair := (sqUniversalBarInputTransitionPairObstruction_eq_zero_iff_subsingleton
      h (hWZ.trans inf_le_left) (hWZ.trans inf_le_right)).mpr htrivial
    obtain ⟨hleft, hright⟩ :=
      (sqUniversalBarInputTransitionPairObstruction_eq_zero_iff
        h (hWZ.trans inf_le_left) (hWZ.trans inf_le_right)).mp hpair
    exact ⟨W, hWZ.trans inf_le_left, hWZ.trans inf_le_right,
      (sqUniversalBarInputTransitionRangeAt_iff_obstruction_eq_zero
        h (hWZ.trans inf_le_left)).mpr hleft,
      (sqUniversalBarInputTransitionRangeAt_iff_obstruction_eq_zero
        h (hWZ.trans inf_le_right)).mpr hright⟩

/-! ## The missing universal-property bridge -/

/-- An *effective marking* of the finite paired detector.  Besides killing the defining square
relator, it must detect every refined Schreier relation defect: if that word vanishes under the
marking, then its paired universal-relation cokernel class vanishes.  This compatibility is the
extra ingredient not supplied merely by finiteness and the two-group property of the detector. -/
def SqUniversalBarInputTransitionPairDetectorEffectiveMarkingAt
    (h : ℕ) (U U' : OpenNormalSubgroup (DSq h : Type)) : Prop :=
  let Z := U ⊓ U'
  let hZU : Z ≤ U := inf_le_left
  let hZU' : Z ≤ U' := inf_le_right
  let D := Multiplicative
    (SqUniversalBarInputTransitionPairDetector h hZU hZU')
  ∃ m : Fin (sqRank h) → D,
    sqRelWord m = 1 ∧
      ∀ (W : OpenNormalSubgroup (DSq h : Type)) (hWZ : W ≤ Z)
        (g q r : (DSq h : Type) ⧸ W.toSubgroup),
        FreeGroup.lift m
            (relationDefect
              (sqOpenQuotientFreeEvaluation_surjective h W) q r).1 = 1 →
          sqUniversalBarInputTransitionPairObstruction h
              (hWZ.trans hZU) (hWZ.trans hZU')
            (Finsupp.single (g, (q, r)) 1) = 0

/-- Precise remaining detector lemma, uniformly over pairs of target quotients. -/
def SqUniversalBarInputTransitionPairDetectorEffectiveMarking (h : ℕ) : Prop :=
  ∀ U U' : OpenNormalSubgroup (DSq h : Type),
    SqUniversalBarInputTransitionPairDetectorEffectiveMarkingAt h U U'

/-- Effective detector markings let the pro-two universal property choose one common
refinement which kills both transition obstructions. -/
theorem sqUniversalBarInputTransitionCommonRefinementRange_of_effectivePairDetectorMarking
    (h : ℕ) (heffective : SqUniversalBarInputTransitionPairDetectorEffectiveMarking h) :
    SqUniversalBarInputTransitionCommonRefinementRange h := by
  intro U U'
  let Z := U ⊓ U'
  let hZU : Z ≤ U := inf_le_left
  let hZU' : Z ≤ U' := inf_le_right
  let D := Multiplicative
    (SqUniversalBarInputTransitionPairDetector h hZU hZU')
  obtain ⟨m, hmrel, hdetect⟩ := heffective U U'
  letI : Finite D := sqUniversalBarInputTransitionPairDetector_finite
    h hZU hZU'
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  have hD : IsPGroup 2 D :=
    sqUniversalBarInputTransitionPairDetector_isPGroup h hZU hZU'
  let F : ContinuousMonoidHom (DSq h : Type) D :=
    sqLiftHom h (isProP_of_isPGroup hD) m hmrel
  let W₀ : OpenNormalSubgroup (DSq h : Type) := {
    toSubgroup := F.toMonoidHom.ker
    isOpen' := by
      change IsOpen (F ⁻¹' {1})
      exact (isOpen_discrete ({1} : Set D)).preimage F.continuous_toFun
  }
  let W : OpenNormalSubgroup (DSq h : Type) := W₀ ⊓ Z
  have hWZ : W ≤ Z := inf_le_right
  have hWU : W ≤ U := hWZ.trans hZU
  have hWU' : W ≤ U' := hWZ.trans hZU'
  refine ⟨W, hWU, hWU', ?_, ?_⟩
  · apply (sqUniversalBarInputTransitionRangeAt_iff_generators h hWU).mpr
    intro g q r
    let δ := relationDefect
      (sqOpenQuotientFreeEvaluation_surjective h W) q r
    have hwordW : FreeGroup.lift (sqGen h) δ.1 ∈ W.toSubgroup := by
      rw [← QuotientGroup.eq_one_iff]
      calc
        QuotientGroup.mk' W.toSubgroup (FreeGroup.lift (sqGen h) δ.1) =
            FreeGroup.lift (sqOpenQuotientMarking h W) δ.1 :=
          map_freeGroup_lift (QuotientGroup.mk' W.toSubgroup) (sqGen h) δ.1
        _ = 1 := δ.2
    have hFword : F (FreeGroup.lift (sqGen h) δ.1) = 1 :=
      MonoidHom.mem_ker.mp ((show W ≤ W₀ from inf_le_left) hwordW)
    have hmword : FreeGroup.lift m δ.1 = 1 := by
      calc
        FreeGroup.lift m δ.1 =
            FreeGroup.lift (fun i ↦ F (sqGen h i)) δ.1 := by
          apply congrArg
            (fun φ : FreeGroup (Fin (sqRank h)) →* D ↦ φ δ.1)
          apply FreeGroup.ext_hom
          intro i
          simp only [FreeGroup.lift_apply_of]
          exact (sqLiftHom_gen h (isProP_of_isPGroup hD) m hmrel i).symm
        _ = F (FreeGroup.lift (sqGen h) δ.1) :=
          (map_freeGroup_lift F.toMonoidHom (sqGen h) δ.1).symm
        _ = 1 := hFword
    have hp := hdetect W hWZ g q r hmword
    exact congrArg Prod.fst hp
  · apply (sqUniversalBarInputTransitionRangeAt_iff_generators h hWU').mpr
    intro g q r
    let δ := relationDefect
      (sqOpenQuotientFreeEvaluation_surjective h W) q r
    have hwordW : FreeGroup.lift (sqGen h) δ.1 ∈ W.toSubgroup := by
      rw [← QuotientGroup.eq_one_iff]
      calc
        QuotientGroup.mk' W.toSubgroup (FreeGroup.lift (sqGen h) δ.1) =
            FreeGroup.lift (sqOpenQuotientMarking h W) δ.1 :=
          map_freeGroup_lift (QuotientGroup.mk' W.toSubgroup) (sqGen h) δ.1
        _ = 1 := δ.2
    have hFword : F (FreeGroup.lift (sqGen h) δ.1) = 1 :=
      MonoidHom.mem_ker.mp ((show W ≤ W₀ from inf_le_left) hwordW)
    have hmword : FreeGroup.lift m δ.1 = 1 := by
      calc
        FreeGroup.lift m δ.1 =
            FreeGroup.lift (fun i ↦ F (sqGen h i)) δ.1 := by
          apply congrArg
            (fun φ : FreeGroup (Fin (sqRank h)) →* D ↦ φ δ.1)
          apply FreeGroup.ext_hom
          intro i
          simp only [FreeGroup.lift_apply_of]
          exact (sqLiftHom_gen h (isProP_of_isPGroup hD) m hmrel i).symm
        _ = F (FreeGroup.lift (sqGen h) δ.1) :=
          (map_freeGroup_lift F.toMonoidHom (sqGen h) δ.1).symm
        _ = 1 := hFword
    have hp := hdetect W hWZ g q r hmword
    exact congrArg Prod.snd hp

/-- With range-good cofinal local solvability fixed, the effective finite-detector marking is
the sole remaining transition input for the unconditional completed endpoint. -/
theorem
    nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_effectivePairDetectorMarking_unconditional
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (hlocal : SqFiniteUniversalThreeAdjointCocycleSyzygyBarRangeGoodCofinalAt h V)
    (heffective : SqUniversalBarInputTransitionPairDetectorEffectiveMarking h)
    (hkernel : SqUniversalBarInputCocycleCancellationTransitionKernel h V) :
    Nonempty (SqFiniteInputCompletedSyzygyBoundaryAt h V) :=
  nonempty_sqFiniteInputCompletedSyzygyBoundaryAt_of_rangeGoodCofinal_unconditional
    h V hlocal
      (sqUniversalBarInputTransitionCommonRefinementRange_of_effectivePairDetectorMarking
        h heffective)
      hkernel

end

end GQ2.Dyadic.Count
