/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhase

/-!
# The corrected compact-M record base

This file packages the corrected compact-M determinant and word-certificate records from an
abstract branch-free phase supply.  It deliberately does not import or assume a concrete
compact-M boundary theorem, so the record layer is reusable while that theorem is completed.
-/

namespace GQ2.Dyadic.Instances.WordPhaseCompactMFinalBase

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.CanonicalRecords
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.MCompact GQ2.Dyadic.Words.MCompact
open TameSpec MarkedCore

/-- The compact-M determinant certificate obtained from an abstract branch-free phase supply. -/
theorem wPcM_affineDeterminantCertificate_of_supply
    {alpha h q : Nat} (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (Sdet : wPhBranchFreeSupply (2 * h + 2) (fieldId_mNuZtwo alpha h (by omega))
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe))
      (mPro2 alpha h q (by omega) hq0 hqe)
      (mCompat alpha h q (by omega) hq0 hqe
        (mTameSpecializes alpha h q hq0 hqe)
        (fieldId_mNuZtwo alpha h (by omega))
        (canRec_mNuZtwo_sigma alpha h (by omega))
        (canRec_mNuZtwo_wild alpha h (by omega)))) :
    AffineDeterminantCertificate
      (GammaR (2 + 2 * h) q (mCompactW alpha h)) (2 + 2 * h) q (DM alpha h)
      (fieldId_mNuZtwo alpha h (by omega)) (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe))
      (mPro2 alpha h q (by omega) hq0 hqe)
      (mCompat alpha h q (by omega) hq0 hqe
        (mTameSpecializes alpha h q hq0 hqe)
        (fieldId_mNuZtwo alpha h (by omega))
        (canRec_mNuZtwo_sigma alpha h (by omega))
        (canRec_mNuZtwo_wild alpha h (by omega)))
      (scalarActionZmodTwo _) := by
  apply RecordBlocks.recBl_determinant_standard_congr
    (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
  apply RecordBlocks.recBl_mCand_determinant_of_wordPhaseSupply halpha
  exact wPh_recBlWordPhaseSupply_of_branchFree _ _ _ _ Sdet

/-- The corrected compact-M word certificate, parameterized only by its branch-free phase
supply. -/
noncomputable def wPcMWordCertificateRN_of_supply
    (alpha h q : Nat) (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    (Sdet : wPhBranchFreeSupply (2 * h + 2) (fieldId_mNuZtwo alpha h (by omega))
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe))
      (mPro2 alpha h q (by omega) hq0 hqe)
      (mCompat alpha h q (by omega) hq0 hqe
        (mTameSpecializes alpha h q hq0 hqe)
        (fieldId_mNuZtwo alpha h (by omega))
        (canRec_mNuZtwo_sigma alpha h (by omega))
        (canRec_mNuZtwo_wild alpha h (by omega)))) :
    WordCertificateRN (2 + 2 * h) q (mCompactW alpha h) (DM alpha h)
      (isProP_DM alpha h) (fieldId_mNuZtwo alpha h (by omega))
      (standardNumerics (2 + 2 * h)) where
  tameSpecialization := mTameSpecializes alpha h q hq0 hqe
  coreRel := mCoreRel alpha h
  proTwoWord := fun G _ _ _ _ _ t ↦ mProTwoWord alpha h (by omega) G t
  pro2 := mPro2 alpha h q (by omega) hq0 hqe
  ker_pro2 := ker_mPro2 alpha h q (by omega) hq0 hqe
  hpro2 := mPro2_surjective alpha h q (by omega) hq0 hqe
  compat := mCompat alpha h q (by omega) hq0 hqe
    (mTameSpecializes alpha h q hq0 hqe) (fieldId_mNuZtwo alpha h (by omega))
    (canRec_mNuZtwo_sigma alpha h (by omega))
    (canRec_mNuZtwo_wild alpha h (by omega))
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := RowClauses.rowCl_mCand_exactLiftingRN halpha hq0 hqe
    (fieldId_mNuZtwo alpha h (by omega))
  stokes := RecordBlocks.recBl_mCand_stokes halpha hq0 hqe
  scalar := RowClauses.rowCl_mCand_scalar halpha hq0 hqe
  determinant := wPcM_affineDeterminantCertificate_of_supply halpha hq0 hqe Sdet
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_mCompact _

/-! ## Generic tied-row wrappers -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity}

/-- A branch tied to a compact-M presentation and its canonical marking acquires the corrected
row residual from the same abstract branch-free supply. -/
theorem wPcM_rowResidualRN_of_tied
    {alpha h : Nat}
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K) {FF : DyadicUnitFiltration K} (G : GenAsmBranch K B)
    (halpha : 2 ≤ alpha) (hp : G.pres = .M0 alpha h)
    (hnu : HEq G.nuP (fieldId_mNuZtwo alpha h (by omega)))
    (Sdet : wPhBranchFreeSupply (2 * h + 2)
      (fieldId_mNuZtwo alpha h (by omega))
      (tameOfSpec (2 + 2 * h) (qOf K FF) (mCompactW alpha h)
        (mTameSpecializes alpha h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)))
      (mPro2 alpha h (qOf K FF) (by omega) (qOf_ne_zero K FF) (even_qOf K FF))
      (mCompat alpha h (qOf K FF) (by omega) (qOf_ne_zero K FF) (even_qOf K FF)
        (mTameSpecializes alpha h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF))
        (fieldId_mNuZtwo alpha h (by omega))
        (canRec_mNuZtwo_sigma alpha h (by omega))
        (canRec_mNuZtwo_wild alpha h (by omega)))) :
    Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  obtain rfl : nu = fieldId_mNuZtwo alpha h (by omega) := eq_of_heq hnu
  exact ⟨⟨wPcMWordCertificateRN_of_supply alpha h (qOf K FF) halpha
    (qOf_ne_zero K FF) (even_qOf K FF) Sdet⟩⟩

/-- The corrected general assembly consumes the supply-parameterized compact-M residual at any
tied branch. -/
theorem wPcM_candidate_equiv_galKRN_of_tied
    {alpha h : Nat}
    {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
    [T2Space (GalK K)] (B : MarkedRecip R K) {FF : DyadicUnitFiltration K}
    (G : GenAsmBranch K B) (halpha : 2 ≤ alpha) (hp : G.pres = .M0 alpha h)
    (hnu : HEq G.nuP (fieldId_mNuZtwo alpha h (by omega)))
    (F : GenAsmFieldInputs K B FF G.degree)
    (Sdet : wPhBranchFreeSupply (2 * h + 2)
      (fieldId_mNuZtwo alpha h (by omega))
      (tameOfSpec (2 + 2 * h) (qOf K FF) (mCompactW alpha h)
        (mTameSpecializes alpha h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)))
      (mPro2 alpha h (qOf K FF) (by omega) (qOf_ne_zero K FF) (even_qOf K FF))
      (mCompat alpha h (qOf K FF) (by omega) (qOf_ne_zero K FF) (even_qOf K FF)
        (mTameSpecializes alpha h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF))
        (fieldId_mNuZtwo alpha h (by omega))
        (canRec_mNuZtwo_sigma alpha h (by omega))
        (canRec_mNuZtwo_wild alpha h (by omega)))) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) := by
  obtain ⟨S⟩ := wPcM_rowResidualRN_of_tied B G halpha hp hnu Sdet
  exact genAsm_candidate_equiv_galKRN G F S

#print axioms wPcM_affineDeterminantCertificate_of_supply
#print axioms wPcMWordCertificateRN_of_supply
#print axioms wPcM_rowResidualRN_of_tied
#print axioms wPcM_candidate_equiv_galKRN_of_tied

end

end GQ2.Dyadic.Instances.WordPhaseCompactMFinalBase
