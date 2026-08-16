/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseCompactNData

/-!
# The corrected compact-N endpoint

The compact-`N` determinant supply closes both action branches.  This file packages it with
the already unconditional corrected lifting, Stokes, and scalar certificates into the active
`WordCertificateRN` API, then feeds the tied `N0 2 0` branch directly to the corrected general
assembly theorem.  In particular the final `sqrt(-2)` statement has no frozen
`askCStageVanishing` hypotheses.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactNFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseCompactNData
open GQ2.Dyadic.Instances.CanonicalRecords
open GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Fields TameSpec MarkedCore

/-! ## The corrected compact-N certificate -/

/-- The compact-`N` determinant certificate, with both action branches supplied by the
branch-free phase comparison. -/
theorem wPcN_affineDeterminantCertificate {alpha h q : Nat} (halpha : 2 ≤ alpha)
    (hq0 : q ≠ 0) (hqe : Even q) :
    AffineDeterminantCertificate (GammaR (2 + 2 * h) q (nCompactW alpha h)) (2 + 2 * h) q
      (DN alpha h) (nNuZtwo alpha h) (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (nCompactW alpha h)
        (genCertNTameSpecializes alpha h q hq0 hqe))
      (genCertNPro2 alpha h q hq0 hqe)
      (genCertNCompat alpha h q hq0 hqe (genCertNTameSpecializes alpha h q hq0 hqe)
        (nNuZtwo alpha h) (nNuZtwo_sigma alpha h) (nNuZtwo_wild alpha h))
      (scalarActionZmodTwo _) := by
  apply RecordBlocks.recBl_determinant_standard_congr
    (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
  apply wPh_nCand_determinant_of_wordPhaseSupply (h := h) (q := q) halpha
  apply wPh_wordPhaseSupplyN_of_branchFree
  apply wPcN_branchFreeSupply
  · simp
  · simp
  · intro i
    simp
  · exact halpha

/-- The canonical compact-`N` corrected word certificate.  Every analytic field is a theorem;
the obsolete frozen coefficient-stage premise does not enter this record. -/
noncomputable def wPcNWordCertificateRN (alpha h q : Nat) (halpha : 2 ≤ alpha)
    (hq0 : q ≠ 0) (hqe : Even q) :
    WordCertificateRN (2 + 2 * h) q (nCompactW alpha h) (DN alpha h) (isProP_DN alpha h)
      (nNuZtwo alpha h) (standardNumerics (2 + 2 * h)) where
  tameSpecialization := genCertNTameSpecializes alpha h q hq0 hqe
  coreRel := genCertNCoreRel alpha h
  proTwoWord := fun G _ _ _ _ _ t ↦ genCertNProTwoWord alpha h G t
  pro2 := genCertNPro2 alpha h q hq0 hqe
  ker_pro2 := genCertN_ker_pro2 alpha h q hq0 hqe
  hpro2 := genCertNPro2_surjective alpha h q hq0 hqe
  compat := genCertNCompat alpha h q hq0 hqe (genCertNTameSpecializes alpha h q hq0 hqe)
    (nNuZtwo alpha h) (nNuZtwo_sigma alpha h) (nNuZtwo_wild alpha h)
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := RowClauses.rowCl_nCand_exactLiftingRN halpha hq0 hqe (nNuZtwo alpha h)
  stokes := wPh_nCand_stokes halpha hq0 hqe
  scalar := RowClauses.rowCl_nCand_scalar halpha hq0 hqe
  determinant := wPcN_affineDeterminantCertificate halpha hq0 hqe
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_nCompact _

/-! ## The tied frozen row and the corrected final theorem -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity}

/-- The tied `sqrt(-2)` row supplies the corrected residual record with no additional
hypotheses. -/
theorem wPcN_rowResidualRN_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) {FF : DyadicUnitFiltration KSqrtNegTwo} :
    ∃ G : GenAsmBranch KSqrtNegTwo B, G.pres = .N0 2 0 ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨G, hp, hnu⟩ := canRec_branch_sqrtNegTwo B
  refine ⟨G, hp, ?_⟩
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  obtain rfl : nu = nNuZtwo 2 0 := eq_of_heq hnu
  exact ⟨⟨wPcNWordCertificateRN 2 0 (qOf KSqrtNegTwo FF) (le_refl 2)
    (qOf_ne_zero KSqrtNegTwo FF) (even_qOf KSqrtNegTwo FF)⟩⟩

/-- The corrected compact-`N` endpoint at `sqrt(-2)`.  Unlike the frozen compatibility
endpoint, this statement has no `askCStageVanishing` binders. -/
theorem wPcN_candidate_equiv_galKRN_sqrtNegTwo [T2Space (GalK KSqrtNegTwo)]
    (B : MarkedRecip R KSqrtNegTwo) {FF : DyadicUnitFiltration KSqrtNegTwo}
    (F : GenAsmFieldInputs KSqrtNegTwo B FF (SelectedPresentation.N0 2 0).degree) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.N0 2 0).degree (qOf KSqrtNegTwo FF)
        (SelectedPresentation.N0 2 0).word : ProfiniteGrp) : Type) (GalK KSqrtNegTwo)) := by
  obtain ⟨G, hp, ⟨S⟩⟩ := wPcN_rowResidualRN_sqrtNegTwo (B := B) (FF := FF)
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  exact genAsm_candidate_equiv_galKRN
    { pres := .N0 2 0
      hdeg := hdeg
      nuP := nu
      hnuP := hnuP
      realization := realization }
    F S

/-! ## Axiom audit -/

#print axioms wPcN_affineDeterminantCertificate
#print axioms wPcNWordCertificateRN
#print axioms wPcN_rowResidualRN_sqrtNegTwo
#print axioms wPcN_candidate_equiv_galKRN_sqrtNegTwo

end

end GQ2.Dyadic.Instances.WordPhaseCompactNFinal
