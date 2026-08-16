/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactMBoundary
import GQ2.Dyadic.Instances.WordPhaseCompactMFinalBase

/-!
# The corrected compact-M endpoints

The branch-free compact-`M` boundary supply closes the determinant certificate at the two
handle-free tied rows.  This file packages that supply through the corrected residual API and
feeds the canonical `sqrt(5)` and `sqrt(2)` branches to the general assembly theorem.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactMFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseCompactMBoundary
open GQ2.Dyadic.Instances.WordPhaseCompactMFinalBase
open GQ2.Dyadic.Instances.CanonicalRecords
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.MCompact GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Fields TameSpec MarkedCore

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity}

/-! ## The tied `sqrt(5)` row -/

/-- The tied `sqrt(5)` branch supplies the corrected compact-`M` residual with no additional
hypotheses. -/
theorem wPcM_rowResidualRN_sqrtFive [T2Space (GalK KSqrtFive)]
    (B : MarkedRecip R KSqrtFive) {FF : DyadicUnitFiltration KSqrtFive} :
    ∃ G : GenAsmBranch KSqrtFive B, G.pres = .M0 2 0 ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨G, hp, hnu⟩ := canRec_branch_sqrtFive B
  refine ⟨G, hp, ?_⟩
  exact wPcM_rowResidualRN_of_tied B G (le_refl 2) hp hnu
    (by
      apply wPcM_branchFreeSupply
      · simp
      · simp
      · intro i
        simp
      · exact le_refl 2)

/-- The corrected compact-`M` endpoint at `sqrt(5)`. -/
theorem wPcM_candidate_equiv_galKRN_sqrtFive [T2Space (GalK KSqrtFive)]
    (B : MarkedRecip R KSqrtFive) {FF : DyadicUnitFiltration KSqrtFive}
    (F : GenAsmFieldInputs KSqrtFive B FF (SelectedPresentation.M0 2 0).degree) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.M0 2 0).degree (qOf KSqrtFive FF)
        (SelectedPresentation.M0 2 0).word : ProfiniteGrp) : Type) (GalK KSqrtFive)) := by
  obtain ⟨G, hp, ⟨S⟩⟩ := wPcM_rowResidualRN_sqrtFive (B := B) (FF := FF)
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  exact genAsm_candidate_equiv_galKRN
    { pres := .M0 2 0
      hdeg := hdeg
      nuP := nu
      hnuP := hnuP
      realization := realization }
    F S

/-! ## The tied `sqrt(2)` row -/

/-- The tied `sqrt(2)` branch supplies the corrected compact-`M` residual with no additional
hypotheses. -/
theorem wPcM_rowResidualRN_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (B : MarkedRecip R KSqrtTwo) {FF : DyadicUnitFiltration KSqrtTwo} :
    ∃ G : GenAsmBranch KSqrtTwo B, G.pres = .M0 3 0 ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨G, hp, hnu⟩ := canRec_branch_sqrtTwo B
  refine ⟨G, hp, ?_⟩
  exact wPcM_rowResidualRN_of_tied B G (by omega) hp hnu
    (by
      apply wPcM_branchFreeSupply
      · simp
      · simp
      · intro i
        simp
      · omega)

/-- The corrected compact-`M` endpoint at `sqrt(2)`. -/
theorem wPcM_candidate_equiv_galKRN_sqrtTwo [T2Space (GalK KSqrtTwo)]
    (B : MarkedRecip R KSqrtTwo) {FF : DyadicUnitFiltration KSqrtTwo}
    (F : GenAsmFieldInputs KSqrtTwo B FF (SelectedPresentation.M0 3 0).degree) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.M0 3 0).degree (qOf KSqrtTwo FF)
        (SelectedPresentation.M0 3 0).word : ProfiniteGrp) : Type) (GalK KSqrtTwo)) := by
  obtain ⟨G, hp, ⟨S⟩⟩ := wPcM_rowResidualRN_sqrtTwo (B := B) (FF := FF)
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  exact genAsm_candidate_equiv_galKRN
    { pres := .M0 3 0
      hdeg := hdeg
      nuP := nu
      hnuP := hnuP
      realization := realization }
    F S

/-! ## Axiom audit -/

#print axioms wPcM_rowResidualRN_sqrtFive
#print axioms wPcM_candidate_equiv_galKRN_sqrtFive
#print axioms wPcM_rowResidualRN_sqrtTwo
#print axioms wPcM_candidate_equiv_galKRN_sqrtTwo

end

end GQ2.Dyadic.Instances.WordPhaseCompactMFinal
