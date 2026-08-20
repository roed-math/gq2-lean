/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilyPlacementDefectExact
import GQ2.Dyadic.Instances.GammaLOddCompatibleRamified

/-!
# The exact general selected-family assembly boundary

The selected-family campaign now has a single final statement.  Fix the corrected
row-independent field packet.  Then the selected candidate carries both its corrected residual
and its candidate/Galois equivalence exactly when the intrinsic mobile M pivot has no canonical
placement defect.

The packet retains only compatibility-aware ramified data for the selected tame quotient.  In
particular it drops the legacy quantification over unrelated actions and the unused
all-square-roots ramified-i premise.  The theorem is uniform in the degree and in all five
presentation families.
-/

namespace GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.FieldFamilyPlacementDefectExact

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

variable {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- The corrected row-independent field packet, retaining only compatible ramified data. -/
structure GenAsmCompatibleFieldInputs (B : MarkedRecip R K)
    (FF : DyadicUnitFiltration K) (n : ℕ) where
  T : OrientedTameQuotientK B FF
  params : FieldParameters
  params_n : params.n = n
  params_qK : params.qK = qOf K FF
  ramifiedData : CompatibleRamifiedDataAt params (GalKsub K)
    (tameAtParams params params_qK T.tameFK)

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- The corrected general assembly from compatibility-aware ramified data. -/
theorem genAsm_candidate_equiv_galKRN_compatible
    (G : GenAsmBranch K B)
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    (S : GenAsmRowResidualRN (FF := FF) G) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) := by
  let KS : KExactSupplyRN F.T G.degree G.core G.coreIsProP G.nuP :=
    kExactSupplyRN_of_markedCore G.hdeg G.pro2
      G.realization.pro2_surjective G.realization.ker_pro2 G.realization.nu_compat
  let source : SourceDataRN G.degree (qOf K FF) G.core G.coreIsProP G.nuP
      (standardNumerics G.degree) :=
    KS.toSourceRN_compatible F.params F.params_n F.params_qK F.ramifiedData
  let A : GalKArithmeticSourceRN G.degree (qOf K FF) G.core G.coreIsProP G.nuP
      (standardNumerics G.degree) K :=
    { source := source
      equivGalK := ContinuousMulEquiv.refl (GalK K)
      tame_surjective := F.T.tameFK_surjective
      wild_isProP := F.T.ker_tameFK ▸ F.T.isProP }
  exact candidate_equiv_galK_of_supplyRN S.cand A
    (two_le_qOf K FF) (even_qOf K FF) G.hnuP

/-- The corrected selected row, together with its final candidate/Galois equivalence. -/
def HasSelectedAssemblyRN (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  ∃ G : GenAsmBranch K B,
    G.pres = selectedPresentation S ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) ∧
      Nonempty (ContinuousMulEquiv
        ((candidateGroup (selectedPresentation S).degree (qOf K FF)
          (selectedPresentation S).word : ProfiniteGrp) : Type) (GalK K))

/-- With the row-independent field packet fixed, the full selected corrected assembly exists
exactly when the intrinsic mobile pivot has no canonical placement defect. -/
theorem hasSelectedAssemblyRN_fieldSelectionFromRange_iff_not_placementDefect
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (F : GenAsmCompatibleFieldInputs B FF
      (selectedPresentation (selectFieldBranchFamilyFromRange B FF D RI)).degree) :
    HasSelectedAssemblyRN B FF
        (selectFieldBranchFamilyFromRange B FF D RI) ↔
      ¬ CanonicalPivotPlacementDefectBoundary B
        (selectFieldBranchFamilyFromRange B FF D RI) := by
  let S := selectFieldBranchFamilyFromRange B FF D RI
  constructor
  · rintro ⟨G, hG, hR, _⟩
    apply (hasSelectedRowResidualRN_fieldSelectionFromRange_iff_not_placementDefect
      B FF D RI).mp
    exact ⟨G, hG, hR⟩
  · intro hdefect
    obtain ⟨G, hG, hR⟩ :=
      (hasSelectedRowResidualRN_fieldSelectionFromRange_iff_not_placementDefect
        B FF D RI).mpr hdefect
    have hdegree : G.degree = (selectedPresentation S).degree :=
      congrArg SelectedPresentation.degree hG
    let FG : GenAsmCompatibleFieldInputs B FF G.degree := hdegree.symm ▸ F
    have hequiv := genAsm_candidate_equiv_galKRN_compatible G FG hR.some
    refine ⟨G, hG, hR, ?_⟩
    change Nonempty (ContinuousMulEquiv
      ((candidateGroup (selectedPresentation S).degree (qOf K FF)
        (selectedPresentation S).word : ProfiniteGrp) : Type) (GalK K))
    rw [← hG]
    exact hequiv

#print axioms GenAsmCompatibleFieldInputs
#print axioms genAsm_candidate_equiv_galKRN_compatible
#print axioms HasSelectedAssemblyRN
#print axioms hasSelectedAssemblyRN_fieldSelectionFromRange_iff_not_placementDefect

end

end GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact
