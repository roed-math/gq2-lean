/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
import GQ2.Dyadic.Instances.MpcMobileSpliceSupply
import GQ2.Dyadic.Instances.GammaRUniformAnalyticCore
import GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm
import GQ2.Dyadic.Instances.MFieldCanonicalMarkingTransitivity

/-!
# Selected even-M coverage by genuine changed-word analytic sources

The field's actual unramified character is pulled back along the supplied oriented
pro-2 equivalence. At selected positive Mpc level its D-coordinate is a unit, so the
mobile splice applies at every handle count and for either epsilon value. At M0 level
zero, the existing strict handle normal form has U-coordinate exactly one and supplies
the pair splice. If there are no handles, that strict alternative is impossible and the
existing canonical C-pivot alternative remains.

The ordinary field orientation and canonical-or-strict boundary are explicit inputs.
Their existing field-theoretic producers are not silently imported into the axiom
footprint of these bridges. The output includes a complete normalized structural core
and all boundary-independent analytic certificates. It does not assert an affine
determinant, final field identification, or a corrected residual at the frozen word.
-/

namespace GQ2.Dyadic.Instances.EvenMSelectedSpliceCoverage
noncomputable section
open GQ2 GQ2.Dyadic Count MarkedCore Multiplicative
open Instances.EvenMHeadHandlePairSpliceSupply
open Instances.MpcMobileSpliceSupply Instances.MpcMobileNuSource
open Instances.MFieldStrictHandleNormalForm Instances.MFieldCanonicalMarkingTransitivity
open Instances.MpcGeneralHandleFamily Instances.M0FamilyField
open Instances.FieldFamilyCampaignBoundary Instances.FieldFamilyFlexibleCertificate
open Instances.FieldFamilyFlexibleAssembly Instances.SourceBoundaryReplacementRN
open Instances.EvenMHeadHandleSource

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- A changed-word analytic presentation tied to the field's actual unramified marking.
No affine determinant or final field identification is included. -/
structure MFieldSpliceData (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (alpha h : ℕ) where
  word : PWord (Generator (2 + 2 * h))
  nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo
  hnuP : Function.Surjective nuP
  realization : MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP
  core : FlexibleCoreLeavesRN (2 + 2 * h) word (DM alpha h) nuP
  specializes : TameSpec.TameSpecializes (2 + 2 * h) (qOf K FF) word
  supply : UniformStokesSupply (2 + 2 * h) (qOf K FF) word
    (pinnedResolvedFamily (2 + 2 * h) (qOf K FF) word)

def MFieldSpliceData.analyticCore {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {alpha h : ℕ} (D : MFieldSpliceData B FF alpha h) :
    SourceAnalyticCoreRN (2 + 2 * h) (qOf K FF) (DM alpha h) (isProP_DM alpha h)
      D.nuP (standardNumerics (2 + 2 * h)) :=
  D.supply.analyticCore D.specializes (DM alpha h) (isProP_DM alpha h) D.nuP

def MFieldSpliceData.flexibleBranch {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {alpha h : ℕ} (D : MFieldSpliceData B FF alpha h)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h) : GenAsmFlexibleBranch K B where
  degree := 2 + 2 * h
  word := D.word
  core := DM alpha h
  coreIsProP := isProP_DM alpha h
  hdeg := hdeg
  nuP := D.nuP
  hnuP := D.hnuP
  realization := D.realization

omit [T2Space (GalK K)] in
theorem exists_spliceData_of_strict_m0
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {alpha h : ℕ}
    (hα : 2 ≤ alpha) (H : MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 h) :
    Nonempty (MFieldSpliceData B FF alpha h) := by
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
    supply := uniformStokesSupply_headHandlePairSplice halpha hα hq0 (even_qOf K FF) j nuP }⟩

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Every selected positive-level M row has an actual unit D-coordinate. This uses the
selected lambda residue, not a canonical C-placement premise. -/
theorem isUnit_D_of_familySelection
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount P (.Mpc alpha r epsilon eta))) (chiCycKTwo (K := K))) :
    IsUnit (toAdd (ztwoIota (mFieldTransportZ B e.1
      (dmD alpha (handleCount P (.Mpc alpha r epsilon eta)))))) := by
  obtain ⟨_hlev, hD, _hB⟩ := level_and_residues_of_familySelection B FF S hbranch e
  obtain ⟨w, hw⟩ := hD
  rw [ztwoIota_mFieldTransportZ]
  change toAdd (nuUrKTwo B (e.1 _)) = (eta : ℤ_[2]) + 2 ^ r * w at hw
  rw [hw]
  apply isUnit_of_unit_add_positive_two_pow _ eta w
  have hv := S.valid
  rw [hbranch] at hv
  exact hv.2

omit [T2Space (GalK K)] in
/-- Both epsilon choices and every handle count, including zero, have a field-tied new
splice source at positive selected level. -/
theorem exists_spliceData_of_selected_mpc_oriented
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount P (.Mpc alpha r epsilon eta))) (chiCycKTwo (K := K))) :
    Nonempty (MFieldSpliceData B FF alpha (handleCount P (.Mpc alpha r epsilon eta))) := by
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
    supply := mpcMobileTameSplice_uniformStokesSupply hq0 (even_qOf K FF) etaD halpha hα nuP }⟩

omit [T2Space (GalK K)] in
/-- The existing strict M0 normal form supplies a field-tied analytic splice. -/
theorem exists_spliceData_of_selected_m0_strict
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (H : MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha))) :
    Nonempty (MFieldSpliceData B FF alpha (handleCount P (.M0 alpha))) := by
  apply exists_spliceData_of_strict_m0 B FF _ H
  have hv := S.valid
  rw [hbranch] at hv
  exact hv

omit [T2Space (GalK K)] in
/-- Exposing the already-proved canonical-or-strict boundary requires no new arithmetic
assumption: its strict alternative is now an analytic splice. -/
theorem canonicalPivot_or_spliceData_of_boundary
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {alpha h : ℕ}
    (hα : 2 ≤ alpha)
    (H : MFieldCPivotAtLevel B alpha 0 h ∨
      MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 h) :
    MFieldCPivotAtLevel B alpha 0 h ∨ Nonempty (MFieldSpliceData B FF alpha h) :=
  H.imp_right (exists_spliceData_of_strict_m0 B FF hα)

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- At zero handle count the strict branch is impossible, so the existing canonical pivot
theorem already covers the selected M0 row. -/
theorem cPivot_of_strict_boundary_zero_handles
    (B : MarkedRecip Rec K) {alpha h : ℕ}
    (H : MFieldCPivotAtLevel B alpha 0 h ∨
      MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 h)
    (hh : h = 0) : MFieldCPivotAtLevel B alpha 0 h := by
  rcases H with hC | ⟨e, j, _⟩
  · exact hC
  · exact (hh ▸ j).elim0

#print axioms MFieldSpliceData
#print axioms MFieldSpliceData.analyticCore
#print axioms MFieldSpliceData.flexibleBranch
#print axioms exists_spliceData_of_strict_m0
#print axioms isUnit_D_of_familySelection
#print axioms exists_spliceData_of_selected_mpc_oriented
#print axioms exists_spliceData_of_selected_m0_strict
#print axioms canonicalPivot_or_spliceData_of_boundary
#print axioms cPivot_of_strict_boundary_zero_handles
end
end GQ2.Dyadic.Instances.EvenMSelectedSpliceCoverage

