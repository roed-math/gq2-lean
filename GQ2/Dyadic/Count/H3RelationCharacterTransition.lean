/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqCofinalTransitionNoGo
import GQ2.Dyadic.Count.HTwoRelationModule

/-!
# Corrected transition law in the relation module

The literal transition condition for the free alphabet of relation words is false: a Schreier
factor at a finer quotient need not itself be the Schreier factor selected at a coarser quotient.
This file records the replacement identity before making any new degree-three construction.

For a quotient map `phi : Q → Q'`, let `d(q) = s'(phi q) s(q)⁻¹` be the normalized-section
refinement defect.  Then the target Schreier factor is

`d(q) · (s(q) d(r) s(q)⁻¹) · phi_*(factor(q,r)) · d(qr)⁻¹`.

Consequently every relation-module character sees the two factor sets as differing by the
explicit coboundary of `q ↦ chi(d(q))`.  This is exactly the multiplicative/Peiffer quotient
and relation-cell correction which the literal no-go theorem leaves available.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.FoxH
open GQ2.ContCoh
open GQ2.Dyadic.SqCore

variable {I Q Q' A : Type} [Group Q] [Group Q']
  [AddCommGroup A] [DistribMulAction Q' A]

/-! ## Mapping relation kernels along a quotient -/

/-- A relation word remains a relation word after postcomposing its marking. -/
def freeRelationKernelMap (phi : Q →* Q') (m : I → Q) :
    FreeRelationKernel m → FreeRelationKernel (fun i ↦ phi (m i)) :=
  fun r ↦ ⟨r.1, by
    rw [MonoidHom.mem_ker]
    calc
      FreeGroup.lift (fun i ↦ phi (m i)) r.1 =
          phi (FreeGroup.lift m r.1) :=
        (map_freeGroup_lift phi m r.1).symm
      _ = 1 := by rw [r.2, map_one]⟩

@[simp] theorem freeRelationKernelMap_coe
    (phi : Q →* Q') (m : I → Q) (r : FreeRelationKernel m) :
    (freeRelationKernelMap phi m r).1 = r.1 :=
  rfl

/-! ## The corrected Schreier-factor identity -/

/-- Exact word-level comparison of the two normalized Schreier factor sets.  The three extra
terms are the two section-refinement cells and the conjugate of the middle one. -/
theorem relationDefect_refinement
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (q r : Q) :
    relationDefect heval' (phi q) (phi r) =
      relationSectionRefinementDefect phi m heval heval' q *
        relationKernelConj (fun i ↦ phi (m i)) (relationSection heval q)
          (relationSectionRefinementDefect phi m heval heval' r) *
        freeRelationKernelMap phi m (relationDefect heval q r) *
        (relationSectionRefinementDefect phi m heval heval' (q * r))⁻¹ := by
  apply Subtype.ext
  simp only [relationDefect, relationSectionRefinementDefect,
    relationKernelConj, freeRelationKernelMap, Subgroup.coe_mul,
    Subgroup.coe_inv, Subgroup.coe_mk]
  rw [map_mul]
  group

/-- A relation character sends inverses to additive negatives. -/
theorem FreeRelationCharacter.val_inv
    {m' : I → Q'} (chi : FreeRelationCharacter m' A)
    (s : FreeRelationKernel m') :
    chi.val (s⁻¹) = -chi.val s := by
  change Multiplicative.toAdd (chi.toMonoidHom s⁻¹) =
    -Multiplicative.toAdd (chi.toMonoidHom s)
  rw [map_inv]
  rfl

/-- A relation character turns the corrected word identity into the usual inhomogeneous
coboundary formula.  This statement works over arbitrary additive coefficients. -/
theorem FreeRelationCharacter.val_relationDefect_refinement
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (chi : FreeRelationCharacter (fun i ↦ phi (m i)) A)
    (q r : Q) :
    chi.val (relationDefect heval' (phi q) (phi r)) =
      chi.val (relationSectionRefinementDefect phi m heval heval' q) +
        phi q • chi.val (relationSectionRefinementDefect phi m heval heval' r) +
        chi.val (freeRelationKernelMap phi m (relationDefect heval q r)) -
        chi.val (relationSectionRefinementDefect phi m heval heval' (q * r)) := by
  rw [relationDefect_refinement phi m heval heval' q r,
    chi.val_mul, chi.val_mul, chi.val_mul,
    FreeRelationCharacter.val_inv chi, chi.val_conjugation]
  rw [← map_freeGroup_lift phi m, relationSection_spec]
  abel

/-- In exponent two, solve the preceding formula for the transported finer Schreier factor.
This is the precise replacement for literal equality of raw relation-word basis vectors. -/
theorem FreeRelationCharacter.val_mappedRelationDefect_eq_target_add_coboundary
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (chi : FreeRelationCharacter (fun i ↦ phi (m i)) A)
    (hA₂ : ∀ a : A, a + a = 0) (q r : Q) :
    chi.val (freeRelationKernelMap phi m (relationDefect heval q r)) =
      chi.val (relationDefect heval' (phi q) (phi r)) +
        chi.val (relationSectionRefinementDefect phi m heval heval' q) +
        phi q • chi.val (relationSectionRefinementDefect phi m heval heval' r) +
        chi.val (relationSectionRefinementDefect phi m heval heval' (q * r)) := by
  have h := chi.val_relationDefect_refinement phi m heval heval' q r
  have hneg : ∀ a : A, -a = a := by
    intro a
    rw [neg_eq_iff_add_eq_zero]
    exact hA₂ a
  simp only [sub_eq_add_neg, hneg] at h
  let t := chi.val (relationDefect heval' (phi q) (phi r))
  let a := chi.val (relationSectionRefinementDefect phi m heval heval' q)
  let b := phi q •
    chi.val (relationSectionRefinementDefect phi m heval heval' r)
  let s := chi.val (freeRelationKernelMap phi m (relationDefect heval q r))
  let d := chi.val
    (relationSectionRefinementDefect phi m heval heval' (q * r))
  change s = t + a + b + d
  change t = a + b + s + d at h
  rw [h]
  symm
  calc
    (a + b + s + d) + a + b + d =
        (a + a) + (b + b) + s + (d + d) := by abel
    _ = s := by rw [hA₂ a, hA₂ b, hA₂ d]; simp

/-! ## Unconditional universal relation-cell corrections -/

/-- The section-refinement defect always has coordinates in the *universal* relation module:
it is simply its own basis vector.  The terminal obstruction arose only when this coordinate was
required to lie in the single displayed-relator module. -/
def finiteUniversalSectionRefinementRelatorCoordinates
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i)))) :
    FiniteSectionRefinementRelatorCoordinates
      phi m heval heval'
      (FreeRelationKernel (fun i ↦ phi (m i))) (fun r ↦ r.1) where
  coordinate q := Finsupp.single
    (1, relationSectionRefinementDefect phi m heval heval' q) 1
  fox q := by
    simp

/-- The explicit universal relation-cell correction on bar one-chains. -/
def finiteUniversalSectionRefinementCorrection
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i)))) :
    FiniteModTwoBarChainOne Q →ₗ[ZMod 2]
      RegularModTwoRelationModule Q'
        (FreeRelationKernel (fun i ↦ phi (m i))) :=
  finiteBarSectionRefinementRelatorCorrection
    (finiteUniversalSectionRefinementRelatorCoordinates phi m heval heval')

/-- Unconditional corrected naturality: the reverse degree-one maps commute after adding the
Fox boundary of the explicit universal relation-cell correction. -/
theorem finiteBarToMarkedOne_refinement_up_to_universalRelation
    (phi : Q →* Q') (m : I → Q)
    (heval : Function.Surjective (FreeGroup.lift m))
    (heval' : Function.Surjective (FreeGroup.lift (fun i ↦ phi (m i))))
    (c : FiniteModTwoBarChainOne Q) :
    regularModTwoPushforward phi I (finiteBarToMarkedOne m heval c) +
        finiteBarToMarkedOne (fun i ↦ phi (m i)) heval'
          (finiteModTwoBarMapOne phi c) =
      (finiteUniversalRelationFoxBoundary (fun i ↦ phi (m i))).map
        (finiteUniversalSectionRefinementCorrection phi m heval heval' c) := by
  simpa [finiteUniversalRelationFoxBoundary,
    finiteUniversalSectionRefinementCorrection] using
    finiteBarToMarkedOne_refinement_up_to_fox phi m heval heval'
      (finiteUniversalSectionRefinementRelatorCoordinates phi m heval heval') c

/-! ## Corrected transitions for square quotients -/

/-- The canonical universal relation-cell correction along one square-quotient transition. -/
def sqUniversalSectionRefinementCorrection
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U') :
    FiniteModTwoBarChainOne ((DSq h : Type) ⧸ U.toSubgroup) →ₗ[ZMod 2]
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ U'.toSubgroup)
        (FreeRelationKernel (sqOpenQuotientMarking h U')) :=
  finiteUniversalSectionRefinementCorrection
    (openNormalQuotientProj hUU') (sqOpenQuotientMarking h U)
    (sqOpenQuotientFreeEvaluation_surjective h U)
    (sqOpenQuotientProjectedFreeEvaluation_surjective h hUU')

/-- The reverse-two discrepancy is exactly the Fox boundary of the explicit relation-cell
correction.  This is unconditional and replaces literal raw-word range transport. -/
theorem sqUniversalBarInput_correctedTransition_fox
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U')).map
          (sqUniversalRelationModuleTransition h hUU'
            (sqOpenQuotientBarToUniversalRelationTwo h U b)) +
      (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U')).map
          (sqOpenQuotientBarToUniversalRelationTwo h U'
            (finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b)) =
      (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U')).map
          (sqUniversalSectionRefinementCorrection h hUU'
            (finiteModTwoBarBoundaryTwo b)) := by
  rw [← sqUniversalRelationFoxBoundary_natural h hUU',
    ← sqOpenQuotientBarToMarkedOne_boundaryTwo,
    ← sqOpenQuotientBarToMarkedOne_boundaryTwo,
    finiteModTwoBarBoundaryTwo_map]
  have hproj : modTwoQuotientTransition (DSq h : Type) hUU' =
      openNormalQuotientProj hUU' := by
    apply MonoidHom.ext
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup q
    rfl
  rw [modTwoRegularModuleTransition, hproj]
  have hmark : (fun i ↦ openNormalQuotientProj hUU'
      (sqOpenQuotientMarking h U i)) = sqOpenQuotientMarking h U' := by
    funext i
    exact openNormalQuotientProj_sqOpenQuotientMarking h hUU' i
  have H := finiteBarToMarkedOne_refinement_up_to_universalRelation
      (openNormalQuotientProj hUU') (sqOpenQuotientMarking h U)
      (sqOpenQuotientFreeEvaluation_surjective h U)
      (sqOpenQuotientProjectedFreeEvaluation_surjective h hUU')
      (finiteModTwoBarBoundaryTwo b)
  change
    regularModTwoPushforward (openNormalQuotientProj hUU') (Fin (sqRank h))
          (finiteBarToMarkedOne (sqOpenQuotientMarking h U)
            (sqOpenQuotientFreeEvaluation_surjective h U)
            (finiteModTwoBarBoundaryTwo b)) +
        finiteBarToMarkedOne (sqOpenQuotientMarking h U')
          (sqOpenQuotientFreeEvaluation_surjective h U')
          (finiteModTwoBarMapOne (openNormalQuotientProj hUU')
            (finiteModTwoBarBoundaryTwo b)) = _
  convert H using 1
  all_goals congr 2

/-- A finite corrected transition stores an ordinary target bar input together with the
universal relation cell whose Fox boundary accounts for the section change. -/
structure SqFiniteCorrectedUniversalBarTransition
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) where
  targetBar : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U'.toSubgroup)
  relationCellCorrection : RegularModTwoRelationModule
    ((DSq h : Type) ⧸ U'.toSubgroup)
    (FreeRelationKernel (sqOpenQuotientMarking h U'))
  corrected_fox :
    (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U')).map
          (sqUniversalRelationModuleTransition h hUU'
            (sqOpenQuotientBarToUniversalRelationTwo h U b)) +
      (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U')).map
          (sqOpenQuotientBarToUniversalRelationTwo h U' targetBar) =
      (finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U')).map relationCellCorrection

/-- Every quotient map and every bar-two input has a canonical corrected transition. -/
noncomputable def sqFiniteCorrectedUniversalBarTransition
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    SqFiniteCorrectedUniversalBarTransition h hUU' b where
  targetBar := finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b
  relationCellCorrection := sqUniversalSectionRefinementCorrection h hUU'
    (finiteModTwoBarBoundaryTwo b)
  corrected_fox := sqUniversalBarInput_correctedTransition_fox h hUU' b

/-- Nonemptiness form used by finite-fiber compactness arguments. -/
theorem nonempty_sqFiniteCorrectedUniversalBarTransition
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    Nonempty (SqFiniteCorrectedUniversalBarTransition h hUU' b) :=
  ⟨sqFiniteCorrectedUniversalBarTransition h hUU' b⟩

end

end GQ2.Dyadic.Count
