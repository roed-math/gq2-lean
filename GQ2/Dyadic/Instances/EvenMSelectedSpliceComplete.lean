/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMSelectedSpliceCoverage
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceBoundary
import GQ2.Dyadic.Instances.MpcMobileSpliceBoundary


/-!
# Complete selected even-M changed-source certificates

The strict level-zero M0 route and every positive-level Mpc route now carry all
word-dependent leaves, including the affine determinant. The source word may change:
no theorem here asserts a residual at the old frozen word. Ordinary field orientation
and the existing canonical-or-strict M0 boundary remain explicit inputs. The inherited
canonical certificate producer is likewise explicit, preserving the standard-three
axiom footprint. Final field identification still belongs to the separate compatible
field assembly, whose ramified field packet and existing arithmetic axioms are not
silently consumed here.
-/

namespace GQ2.Dyadic.Instances.EvenMSelectedSpliceComplete
noncomputable section
open GQ2 GQ2.Dyadic Count MarkedCore Multiplicative
open Instances.EvenMSelectedSpliceCoverage
open Instances.EvenMHeadHandlePairSpliceSupply
open Instances.MpcMobileSpliceSupply Instances.MpcMobileNuSource
open Instances.MFieldStrictHandleNormalForm Instances.MFieldCanonicalMarkingTransitivity
open Instances.MpcGeneralHandleFamily Instances.M0FamilyField
open Instances.FieldFamilyCampaignBoundary Instances.FieldFamilyFlexibleCertificate
open Instances.FieldFamilyFlexibleAssembly Instances.SourceBoundaryReplacementRN
open Instances.EvenMHeadHandleSource
open Instances.EvenMHeadHandlePairSpliceBoundary Instances.MpcMobileSpliceBoundary

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- A field-tied changed source with every word-dependent certificate, including determinant.
The field realization is the explicitly supplied ordinary oriented pro-2 equivalence. -/
structure MFieldSpliceCompleteData (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (alpha h : ℕ) extends MFieldSpliceData B FF alpha h where
  certificate : FlexibleCertificateLeavesRN (2 + 2 * h) (qOf K FF) word
    (DM alpha h) (isProP_DM alpha h) nuP (standardNumerics (2 + 2 * h))
    (by have := two_le_qOf K FF; omega) (even_qOf K FF)

/-- Complete splice data supply the corrected residual for their actual changed word. -/
def MFieldSpliceCompleteData.rowResidual
    {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K} {alpha h : ℕ}
    (D : MFieldSpliceCompleteData B FF alpha h)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    GenAsmFlexibleRowResidualRN FF (D.toMFieldSpliceData.flexibleBranch hdeg) :=
  GenAsmFlexibleRowResidualRN.ofFlexibleLeaves _ D.certificate

/-- A complete field-tied source at the selected degree. Unlike `HasSelectedRowResidualRN`,
this intentionally does not equate the source word with the old frozen presentation. -/
def HasSelectedFlexibleRowResidualRN (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  ∃ G : GenAsmFlexibleBranch K B, G.degree = S.semantic.degree ∧
    Nonempty (GenAsmFlexibleRowResidualRN FF G)

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- A frozen-word certificate is one possible flexible certificate; no field axiom is invoked. -/
theorem hasSelectedFlexibleRowResidualRN_of_canonical
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (H : HasSelectedRowResidualRN B FF S) : HasSelectedFlexibleRowResidualRN B FF S := by
  obtain ⟨G, _, ⟨hG⟩⟩ := H
  refine ⟨GenAsmFlexibleBranch.ofCanonical G, ?_,
    ⟨GenAsmFlexibleRowResidualRN.ofCanonical G hG⟩⟩
  exact G.hdeg.symm.trans S.degree_eq_field.symm

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- Complete changed-source data at the selected degree supply the selected flexible residual. -/
theorem hasSelectedFlexibleRowResidualRN_of_completeData
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha h : ℕ} (D : MFieldSpliceCompleteData B FF alpha h)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h) :
    HasSelectedFlexibleRowResidualRN B FF S := by
  refine ⟨D.toMFieldSpliceData.flexibleBranch hdeg, ?_, ⟨D.rowResidual hdeg⟩⟩
  exact hdeg.symm.trans S.degree_eq_field.symm

omit [T2Space (GalK K)] in
/-- The strict M0 level-zero row gives a complete changed-source certificate, with no
remaining analytic or determinant input. -/
theorem exists_completeData_of_strict_m0
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {alpha h : ℕ}
    (hα : 2 ≤ alpha) (H : MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 h) :
    Nonempty (MFieldSpliceCompleteData B FF alpha h) := by
  obtain ⟨e, j, hU, _hV, _hC⟩ := H
  let nuP := mFieldTransportZ B e.1
  have hu : nuP (dmGen alpha h (handleIdxU j)) = ztwoOne := by
    apply ztwoIota.injective
    rw [ztwoIota_ztwoOne]
    change ztwoIota (mFieldTransportZ B e.1 _) = _
    rw [ztwoIota_mFieldTransportZ]
    apply Multiplicative.toAdd.injective
    change toAdd (nuUrKTwo B (e.1 (dmGen alpha h (handleIdxU j)))) = 2 ^ 0 at hU
    simpa only [pow_zero, toAdd_ofAdd] using hU
  have hq0 : qOf K FF ≠ 0 := by have := two_le_qOf K FF; omega
  let halpha : 1 ≤ alpha := by omega
  refine ⟨{
    word := headHandlePairSpliceW alpha h (qOf K FF) halpha hq0 (even_qOf K FF) j nuP
    nuP := nuP
    hnuP := mFieldTransportZ_surjective B FF e.1
    realization := { equiv := e.1, nu_equiv := fun x => ztwoIota_mFieldTransportZ B e.1 x }
    core := flexibleCore_headHandlePairSplice halpha hq0 (even_qOf K FF) j nuP hu
    specializes := headHandlePairSpliceW_specializes halpha hq0 (even_qOf K FF) j nuP
    supply := uniformStokesSupply_headHandlePairSplice halpha hα hq0 (even_qOf K FF) j nuP
    certificate := headHandlePairSplice_flexibleCertificateLeaves
      halpha hα hq0 (even_qOf K FF) j nuP hu }⟩

omit [T2Space (GalK K)] in
/-- Every positive selected Mpc row supplies all changed-source certificate leaves. The unit
is the actual D-coordinate, not the originally displayed representative. -/
theorem exists_completeData_of_selected_mpc_oriented
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount P (.Mpc alpha r epsilon eta))) (chiCycKTwo (K := K))) :
    Nonempty (MFieldSpliceCompleteData B FF alpha (handleCount P (.Mpc alpha r epsilon eta))) := by
  let h := handleCount P (.Mpc alpha r epsilon eta)
  let nuP := mFieldTransportZ B e.1
  have hunit := isUnit_D_of_familySelection B FF S hbranch e
  let etaD : ℤ_[2]ˣ := hunit.unit
  have hd : ztwoIota (nuP (dmD alpha h)) = ofAdd (etaD : ℤ_[2]) := by
    rw [show (etaD : ℤ_[2]) = toAdd (ztwoIota (nuP (dmD alpha h))) from hunit.unit_spec]
    rfl
  have hα : 2 ≤ alpha := by have hv := S.valid; rw [hbranch] at hv; exact hv.1
  have hq0 : qOf K FF ≠ 0 := by have := two_le_qOf K FF; omega
  let halpha : 1 ≤ alpha := by omega
  let R := mpcMobileTameCorrectedW hq0 (even_qOf K FF) alpha r (p epsilon r) h etaD halpha nuP
  refine ⟨{
    word := tameSplice R (Words.MCompact.mCompactW alpha h)
    nuP := nuP
    hnuP := mFieldTransportZ_surjective B FF e.1
    realization := { equiv := e.1, nu_equiv := fun x => ztwoIota_mFieldTransportZ B e.1 x }
    core := mpcMobileTameSplice_core hq0 (even_qOf K FF) alpha r (p epsilon r) h etaD halpha nuP hd
    specializes := tameSpecializes_tameSplice
      (mpcMobileTameCorrectedW_specializes hq0 (even_qOf K FF) etaD halpha nuP)
      (tameSpecializes_mCompact hq0 (even_qOf K FF) alpha h)
    supply := mpcMobileTameSplice_uniformStokesSupply hq0 (even_qOf K FF) etaD halpha hα nuP
    certificate := mpcMobileTameSplice_flexibleCertificateLeaves
      hq0 (even_qOf K FF) etaD halpha hα nuP hd }⟩

omit [T2Space (GalK K)] in
/-- Complete selected M0 coverage on the strict-handle alternative. -/
theorem hasSelectedFlexibleRowResidualRN_m0_strict
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (H : MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha))) :
    HasSelectedFlexibleRowResidualRN B FF S := by
  have hα : 2 ≤ alpha := by have hv := S.valid; rw [hbranch] at hv; exact hv
  obtain ⟨D⟩ := exists_completeData_of_strict_m0 B FF hα H
  apply hasSelectedFlexibleRowResidualRN_of_completeData B FF S D
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  exact hdeg.symm

omit [T2Space (GalK K)] in
/-- Complete selected Mpc coverage for both epsilon values and every handle count. -/
theorem hasSelectedFlexibleRowResidualRN_mpc_oriented
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount P (.Mpc alpha r epsilon eta))) (chiCycKTwo (K := K))) :
    HasSelectedFlexibleRowResidualRN B FF S := by
  obtain ⟨D⟩ := exists_completeData_of_selected_mpc_oriented B FF S hbranch e
  apply hasSelectedFlexibleRowResidualRN_of_completeData B FF S D
  have hdeg := S.degree_eq_field
  rw [hbranch] at hdeg
  exact hdeg.symm

omit [T2Space (GalK K)] in
/-- M0 dispatch keeps the inherited canonical certificate producer explicit. This includes
the zero-handle case, where the strict alternative is impossible. -/
theorem hasSelectedFlexibleRowResidualRN_m0_of_boundary
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (H : MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) ∨
      MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha)))
    (hcanonical : MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) →
      HasSelectedRowResidualRN B FF S) :
    HasSelectedFlexibleRowResidualRN B FF S := by
  rcases H with hc | hs
  · exact hasSelectedFlexibleRowResidualRN_of_canonical B FF S (hcanonical hc)
  · exact hasSelectedFlexibleRowResidualRN_m0_strict B FF S hbranch hs

/-- The only field-side inputs for the selected even-M flexible dispatcher. The ordinary
orientation and strict boundary are explicit; the old canonical branch is not re-proved. -/
def SelectedEvenMCompleteInputs (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  match S.branch with
  | .M0 alpha =>
      (MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) ∨
        MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha))) ∧
      (MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) →
        HasSelectedRowResidualRN B FF S)
  | .Mpc alpha r epsilon eta => Nonempty (OrientedContinuousMulEquiv
      (chiM alpha (handleCount P (.Mpc alpha r epsilon eta))) (chiCycKTwo (K := K)))
  | _ => False

omit [T2Space (GalK K)] in
/-- Rank-uniform selected even-M dispatch to complete actual changed-word residuals. -/
theorem hasSelectedFlexibleRowResidualRN_of_evenMInputs
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (H : SelectedEvenMCompleteInputs B FF S) : HasSelectedFlexibleRowResidualRN B FF S := by
  cases hb : S.branch with
  | L => simp [SelectedEvenMCompleteInputs, hb] at H
  | N0 alpha => simp [SelectedEvenMCompleteInputs, hb] at H
  | Npc alpha r eta => simp [SelectedEvenMCompleteInputs, hb] at H
  | M0 alpha =>
      simp only [SelectedEvenMCompleteInputs, hb] at H
      exact hasSelectedFlexibleRowResidualRN_m0_of_boundary B FF S hb H.1 H.2
  | Mpc alpha r epsilon eta =>
      simp only [SelectedEvenMCompleteInputs, hb] at H
      obtain ⟨e⟩ := H
      exact hasSelectedFlexibleRowResidualRN_mpc_oriented B FF S hb e

#print axioms MFieldSpliceCompleteData
#print axioms MFieldSpliceCompleteData.rowResidual
#print axioms HasSelectedFlexibleRowResidualRN
#print axioms hasSelectedFlexibleRowResidualRN_of_canonical
#print axioms hasSelectedFlexibleRowResidualRN_of_completeData
#print axioms exists_completeData_of_strict_m0
#print axioms exists_completeData_of_selected_mpc_oriented
#print axioms hasSelectedFlexibleRowResidualRN_m0_strict
#print axioms hasSelectedFlexibleRowResidualRN_mpc_oriented
#print axioms hasSelectedFlexibleRowResidualRN_m0_of_boundary
#print axioms SelectedEvenMCompleteInputs
#print axioms hasSelectedFlexibleRowResidualRN_of_evenMInputs

end
end GQ2.Dyadic.Instances.EvenMSelectedSpliceComplete
