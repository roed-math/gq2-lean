/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldMobilePivotBoundary
import GQ2.Dyadic.Instances.MpcGeneralHandleFamilyClosed
import GQ2.Dyadic.Instances.M0FamilyFinal

/-!
# The canonical marked-core realization boundary

The corrected M-row certificates do not intrinsically require an oriented equivalence whose
distinguished `C` coordinate is a pivot.  They require a realization of the canonical marked
M core.  This module packages that weaker and coordinate-free field datum for both compact and
procyclic M rows and feeds it directly into corrected assembly.

The resulting all-degree dispatcher supersedes the exact-`C` boundary as the sharp public
interface.  Exact-`C` normalization remains a sufficient construction of the realization, but
it is no longer confused with the object consumed by the campaign endpoint.  The remaining
general problem is therefore canonical marked-core realization, equivalently a full marking
normalization or a proof that a different canonical M normal form is required.
-/

namespace GQ2.Dyadic.Instances.MFieldCanonicalRealizationBoundary

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.FieldBranchId
open GQ2.Dyadic.Instances.FieldFamilyCampaignBoundary
open GQ2.Dyadic.Instances.MpcGeneralHandleFamilyClosed
open GQ2.Dyadic.Instances.M0FamilyFinal

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The actual field-facing compact-M datum needed by corrected assembly. -/
def M0CanonicalMarkedCoreRealization (B : MarkedRecip R K)
    (alpha h : ℕ) : Prop :=
  ∃ halpha : 1 ≤ alpha,
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DM alpha h)
      (fieldId_mNuZtwo alpha h halpha))

/-- The actual field-facing procyclic-M datum needed by corrected assembly. -/
def MpcCanonicalMarkedCoreRealization (B : MarkedRecip R K)
    (alpha r h : ℕ) (epsilon : Bool) (eta : ℤ_[2]ˣ) : Prop :=
  ∃ halpha : 1 ≤ alpha,
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DM alpha h)
      (mpcNu alpha r (p epsilon r) h eta halpha))

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- A selected compact-M realization is enough for its corrected row, without an oriented
`C`-pivot hypothesis. -/
theorem hasSelectedRowResidualRN_m0_of_realization
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (H : M0CanonicalMarkedCoreRealization B alpha
      (handleCount P (.M0 alpha))) :
    HasSelectedRowResidualRN B FF S := by
  have hvalid := S.valid
  rw [hbranch] at hvalid
  have hdeg : Module.finrank ℚ_[2] K =
      (SelectedPresentation.M0 alpha (handleCount P (.M0 alpha))).degree := by
    have hd := S.degree_eq_field
    rw [hbranch] at hd
    exact hd.symm
  obtain ⟨halpha, ⟨M⟩⟩ := H
  let G : GenAsmBranch K B :=
    { pres := .M0 alpha (handleCount P (.M0 alpha))
      hdeg := hdeg
      nuP := fieldId_mNuZtwo alpha (handleCount P (.M0 alpha)) halpha
      hnuP := fieldId_mNuZtwo_surjective alpha (handleCount P (.M0 alpha)) halpha
      realization := M }
  refine ⟨G, ?_, ?_⟩
  · rw [selectedPresentation_eq_m0 S hbranch]
  · dsimp only [G, GenAsmBranch.degree, GenAsmBranch.word, GenAsmBranch.core]
    exact ⟨⟨wPcMWordCertificateRN_handles alpha (handleCount P (.M0 alpha))
      (qOf K FF) hvalid (qOf_ne_zero K FF) (even_qOf K FF)⟩⟩

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- A selected procyclic-M realization is enough for its corrected row, without an oriented
`C`-pivot hypothesis. -/
theorem hasSelectedRowResidualRN_mpc_of_realization
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (H : MpcCanonicalMarkedCoreRealization B alpha r
      (handleCount P (.Mpc alpha r epsilon eta)) epsilon eta) :
    HasSelectedRowResidualRN B FF S := by
  let d : MpcDisplayFor eta :=
    Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
  have hvalid := S.valid
  rw [hbranch] at hvalid
  have hdeg : Module.finrank ℚ_[2] K =
      (SelectedPresentation.Mpc alpha r epsilon d.display
        (handleCount P (.Mpc alpha r epsilon eta))).degree := by
    have hd := S.degree_eq_field
    rw [hbranch] at hd
    exact hd.symm
  obtain ⟨halpha, ⟨M⟩⟩ := H
  let G : GenAsmBranch K B :=
    { pres := .Mpc alpha r epsilon d.display
        (handleCount P (.Mpc alpha r epsilon eta))
      hdeg := hdeg
      nuP := mpcNu alpha r (p epsilon r)
        (handleCount P (.Mpc alpha r epsilon eta)) eta halpha
      hnuP := MpcGeneralHandleRealization.mpcNu_surjective alpha r (p epsilon r)
        (handleCount P (.Mpc alpha r epsilon eta)) eta halpha
      realization := M }
  refine ⟨G, ?_, ?_⟩
  · rw [selectedPresentation_eq_mpc S hbranch]
  · dsimp only [G, GenAsmBranch.degree, GenAsmBranch.word, GenAsmBranch.core]
    exact ⟨⟨mpcWordCertificateRN_of_display alpha r (qOf K FF) epsilon
      (handleCount P (.Mpc alpha r epsilon eta)) d hvalid.1 hvalid.2
      (qOf_ne_zero K FF) (even_qOf K FF)⟩⟩

/-- The weaker canonical-realization boundary on the two unresolved selected M rows. -/
def EvenCanonicalRealizationBoundary (B : MarkedRecip R K)
    {P : FieldParameters} {FF : DyadicUnitFiltration K}
    {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  match S.branch with
  | .M0 alpha =>
      M0CanonicalMarkedCoreRealization B alpha (handleCount P (.M0 alpha))
  | .Mpc alpha r false eta =>
      MpcCanonicalMarkedCoreRealization B alpha r
        (handleCount P (.Mpc alpha r false eta)) false eta
  | _ => True

theorem hasSelectedRowResidualRN_of_evenRealizationBoundary
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange)
    (hnotL : S.branch ≠ .L)
    (hboundary : EvenCanonicalRealizationBoundary B S) :
    HasSelectedRowResidualRN B FF S := by
  generalize hbranch : S.branch = branch
  cases branch with
  | L => exact (hnotL hbranch).elim
  | N0 alpha => exact hasSelectedRowResidualRN_n0 B FF S hmatch hbranch
  | Npc alpha r eta => exact hasSelectedRowResidualRN_npc B FF S hmatch hbranch
  | M0 alpha =>
      rw [EvenCanonicalRealizationBoundary, hbranch] at hboundary
      exact hasSelectedRowResidualRN_m0_of_realization B FF S hbranch hboundary
  | Mpc alpha r epsilon eta =>
      cases epsilon with
      | false =>
          rw [EvenCanonicalRealizationBoundary, hbranch] at hboundary
          exact hasSelectedRowResidualRN_mpc_of_realization B FF S hbranch hboundary
      | true =>
          exact hasSelectedRowResidualRN_mpc_of_cPivot B FF S hbranch
            (mFieldCPivotAtLevel_mpc_true B FF S hmatch hbranch)

/-- The all-degree corrected-family dispatcher over the sharp canonical-realization boundary. -/
theorem hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_realizationBoundary
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K)
    (hboundary : EvenCanonicalRealizationBoundary B
      (selectFieldBranchFamilyFromRange B FF D RI)) :
    HasSelectedRowResidualRN B FF
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  let S := selectFieldBranchFamilyFromRange B FF D RI
  have hmatch := fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI
  generalize hbranch : S.branch = branch
  cases branch with
  | L => exact hasSelectedRowResidualRN_l B FF D S hbranch
  | N0 alpha =>
      exact hasSelectedRowResidualRN_of_evenRealizationBoundary B FF S hmatch
        (by rw [hbranch]; intro h; cases h) hboundary
  | Npc alpha r eta =>
      exact hasSelectedRowResidualRN_of_evenRealizationBoundary B FF S hmatch
        (by rw [hbranch]; intro h; cases h) hboundary
  | M0 alpha =>
      exact hasSelectedRowResidualRN_of_evenRealizationBoundary B FF S hmatch
        (by rw [hbranch]; intro h; cases h) hboundary
  | Mpc alpha r epsilon eta =>
      exact hasSelectedRowResidualRN_of_evenRealizationBoundary B FF S hmatch
        (by rw [hbranch]; intro h; cases h) hboundary

#print axioms M0CanonicalMarkedCoreRealization
#print axioms MpcCanonicalMarkedCoreRealization
#print axioms hasSelectedRowResidualRN_m0_of_realization
#print axioms hasSelectedRowResidualRN_mpc_of_realization
#print axioms EvenCanonicalRealizationBoundary
#print axioms hasSelectedRowResidualRN_of_evenRealizationBoundary
#print axioms hasSelectedRowResidualRN_of_fieldSelectionFromRange_of_realizationBoundary

end

end GQ2.Dyadic.Instances.MFieldCanonicalRealizationBoundary
