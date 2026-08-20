/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MOrientationCharacteristicFinal
import GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm

/-!
# The strict compact-M handle alternative is not a residual supply

Characteristic orientation makes the canonical C-pivot necessary for every realized
compact-M word certificate.  Therefore the strict handle alternative, whose C row is
one level too deep, cannot carry the existing corrected RN residual.  On a selected
M0 row the residual exists exactly when the canonical C pivot exists.

This rules out a circular completion of the campaign by postulating a strict-handle
supply for the unchanged compact-M presentation.  A genuine solution must prove the
field pivot or replace that presentation by a new mobile-pivot normal form.
-/

namespace GQ2.Dyadic.Instances.MStrictHandleResidualNoGo

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MOrientationCharacteristicFinal
open GQ2.Dyadic.Instances.MFieldStrictHandleNormalForm
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.EvenFamilyRangeBridge
open GQ2.Dyadic.Instances.M0FamilyField
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Words.Mpc

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [T2Space (GalK K)] in
theorem mFieldCPivotAtLevel_m0_of_genAsmRowResidualRN
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (G : GenAsmBranch K B) (hpres : G.pres = .M0 alpha h)
    (R : GenAsmRowResidualRN (FF := FF) G) :
    MFieldCPivotAtLevel B alpha 0 h := by
  cases G with
  | mk pres hdeg nuP hnuP realization =>
      dsimp only at hpres R
      subst pres
      exact mFieldCPivotAtLevel_zero_of_wordCertificateRN_general
        B e0 halpha (qOf_ne_zero K FF) (even_qOf K FF)
          nuP realization R.cand

omit [T2Space (GalK K)] in
theorem no_genAsmRowResidualRN_m0_of_strictHandle
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (Hstrict : StrictNormalizedMHandlePivotAtLevel (r := 0) (m0Transport B e0))
    (G : GenAsmBranch K B) (hpres : G.pres = .M0 alpha h) :
    ¬ Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  intro hR
  obtain ⟨R⟩ := hR
  cases G with
  | mk pres hdeg nuP hnuP realization =>
      dsimp only at hpres R
      subst pres
      exact no_mCompact_realizedWordCertificateRN_of_strictHandle_general
        B e0 halpha (qOf_ne_zero K FF) (even_qOf K FF) Hstrict
          nuP realization ⟨R.cand⟩

omit [T2Space (GalK K)] in
theorem no_hasSelectedRowResidualRN_m0_of_strictHandle
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (Hstrict : MFieldStrictNormalizedHandlePivotAtLevel B alpha 0
      (handleCount P (.M0 alpha))) :
    ¬ HasSelectedRowResidualRN B FF S := by
  rintro ⟨G, hG, hR⟩
  obtain ⟨e0, he0⟩ := Hstrict
  have halpha : 2 ≤ alpha := by
    have hv := S.valid
    rw [hbranch] at hv
    exact hv
  apply no_genAsmRowResidualRN_m0_of_strictHandle
    B FF halpha e0 he0 G (hG.trans (selectedPresentation_eq_m0 S hbranch))
  exact hR

omit [T2Space (GalK K)] in
theorem mFieldCPivotAtLevel_m0_of_hasSelectedRowResidualRN
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (H : HasSelectedRowResidualRN B FF S) :
    MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) := by
  obtain ⟨e0⟩ := orientedEquivM_of_familySelection_of_matchesRange_m0
    B FF S hmatch hbranch
  obtain ⟨G, hG, ⟨R⟩⟩ := H
  cases G with
  | mk pres hdeg nuP hnuP realization =>
      dsimp only at hG R
      rw [selectedPresentation_eq_m0 S hbranch] at hG
      subst pres
      exact mFieldCPivotAtLevel_zero_of_wordCertificateRN_general
        B e0 (by
          have hv := S.valid
          rw [hbranch] at hv
          exact hv) (qOf_ne_zero K FF) (even_qOf K FF)
            nuP realization R.cand

omit [T2Space (GalK K)] in
theorem hasSelectedRowResidualRN_m0_iff_cPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha) :
    HasSelectedRowResidualRN B FF S ↔
      MFieldCPivotAtLevel B alpha 0 (handleCount P (.M0 alpha)) := by
  constructor
  · exact mFieldCPivotAtLevel_m0_of_hasSelectedRowResidualRN
      B FF S hmatch hbranch
  · exact hasSelectedRowResidualRN_m0_of_cPivot B FF S hbranch

omit [T2Space (GalK K)] in
theorem mFieldCPivotAtLevel_mpc_of_genAsmRowResidualRN
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (e0 : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)))
    (G : GenAsmBranch K B)
    (hpres : G.pres = .Mpc alpha r epsilon d.display h)
    (R : GenAsmRowResidualRN (FF := FF) G) :
    MFieldCPivotAtLevel B alpha r h := by
  cases G with
  | mk pres hdeg nuP hnuP realization =>
      dsimp only at hpres R
      subst pres
      exact mFieldCPivotAtLevel_of_mpcWordCertificateRN_general
        B d e0 halpha hr (qOf_ne_zero K FF) (even_qOf K FF)
          nuP realization R.cand

omit [T2Space (GalK K)] in
theorem mFieldCPivotAtLevel_mpc_of_hasSelectedRowResidualRN
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (H : HasSelectedRowResidualRN B FF S) :
    MFieldCPivotAtLevel B alpha r
      (handleCount P (.Mpc alpha r epsilon eta)) := by
  let d : MpcDisplayFor eta :=
    Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
  obtain ⟨e0⟩ := orientedEquivM_of_familySelection_of_matchesRange_mpc
    B FF S hmatch hbranch
  obtain ⟨G, hG, ⟨R⟩⟩ := H
  have hpres : G.pres = .Mpc alpha r epsilon d.display
      (handleCount P (.Mpc alpha r epsilon eta)) := by
    exact hG.trans (selectedPresentation_eq_mpc S hbranch)
  have halpha : 2 ≤ alpha := by
    have hv := S.valid
    rw [hbranch] at hv
    exact hv.1
  have hr : 1 ≤ r := by
    have hv := S.valid
    rw [hbranch] at hv
    exact hv.2
  exact mFieldCPivotAtLevel_mpc_of_genAsmRowResidualRN
    B FF d halpha hr e0 G hpres R

omit [T2Space (GalK K)] in
theorem hasSelectedRowResidualRN_mpc_iff_cPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta) :
    HasSelectedRowResidualRN B FF S ↔
      MFieldCPivotAtLevel B alpha r
        (handleCount P (.Mpc alpha r epsilon eta)) := by
  constructor
  · exact mFieldCPivotAtLevel_mpc_of_hasSelectedRowResidualRN
      B FF S hmatch hbranch
  · exact hasSelectedRowResidualRN_mpc_of_cPivot B FF S hbranch

#print axioms no_genAsmRowResidualRN_m0_of_strictHandle
#print axioms mFieldCPivotAtLevel_m0_of_genAsmRowResidualRN
#print axioms no_hasSelectedRowResidualRN_m0_of_strictHandle
#print axioms mFieldCPivotAtLevel_m0_of_hasSelectedRowResidualRN
#print axioms hasSelectedRowResidualRN_m0_iff_cPivot
#print axioms mFieldCPivotAtLevel_mpc_of_genAsmRowResidualRN
#print axioms mFieldCPivotAtLevel_mpc_of_hasSelectedRowResidualRN
#print axioms hasSelectedRowResidualRN_mpc_iff_cPivot

end

end GQ2.Dyadic.Instances.MStrictHandleResidualNoGo
