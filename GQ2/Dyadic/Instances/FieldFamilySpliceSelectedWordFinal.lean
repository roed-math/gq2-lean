/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWord
import GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical

/-!
# Fully marked field equivalence with the exact selected source constructor

The source profile survives existential realization calibration definitionally. The record
below retains it alongside the actual word certificate and all four marking equations.
The canonical endpoint requires only a finite dyadic field in the standing ramified-i scope.
No frozen-word equality is asserted for either changed M-source branch.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWordFinal
noncomputable section
open GQ2 GQ2.Dyadic
open Instances.FieldFamilyFlexibleAssembly Instances.FieldFamilyGeneralAssemblyExact
open Instances.FieldFamilySpliceFinal Instances.FieldFamilySpliceSelectedWord
open Instances.FieldFamilySpliceAlignedFinal Instances.FieldFamilySpliceMarkedFinal
open Instances.FieldCyclotomicCharacteristic
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section FieldInputs
variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
  {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}

omit [T2Space (GalK K)] in
/-- Calibration changes no component used by the exact selected-word profile. -/
theorem selectedWordProfile_alignedBranch
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (G : GenAsmFlexibleBranch K B)
    (C : WordCertificateRN G.degree (qOf K FF) G.word G.core G.coreIsProP G.nuP
      (standardNumerics G.degree))
    (e : ContinuousMulEquiv (GammaR G.degree (qOf K FF) G.word) (GalK K))
    (hnu : ∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (C.pro2 g))) :
    SelectedWordProfile FF S (alignedBranch G C e hnu) ↔ SelectedWordProfile FF S G :=
  Iff.rfl

/-- A selected actual word, not just a degree, with its certified fully marked field
equivalence. The carried realization is the new existentially aligned realization. -/
structure SelectedWordMarkedFieldData
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) where
  branch : GenAsmFlexibleBranch K B
  degree_eq : branch.degree = S.semantic.degree
  profile : SelectedWordProfile FF S branch
  certificate : GenAsmFlexibleRowResidualRN FF branch
  equiv : ContinuousMulEquiv (GammaR branch.degree (qOf K FF) branch.word) (GalK K)
  tame : ∀ g, T.tameFK (equiv g) =
    TameSpec.tameOfSpec branch.degree (qOf K FF) branch.word
      certificate.cand.tameSpecialization g
  pro2 : ∀ g, branch.realization.pro2 (equiv g) = certificate.cand.pro2 g
  maxPro2 : ∀ g, maxProPMk 2 (GalK K) (equiv g) =
    branch.realization.equiv (certificate.cand.pro2 g)
  cyclotomic : ∀ g, chiCycK K (equiv g) =
    chiCycKTwo (K := K) (branch.realization.equiv (certificate.cand.pro2 g))
  nu : ∀ g, B.nu_ur (toAbK K (equiv g)) = ztwoIota (branch.nuP (certificate.cand.pro2 g))

omit [T2Space (GalK K)] in
/-- The selected alphabet has exactly the field degree, without an unstated reindexing. -/
theorem SelectedWordMarkedFieldData.degree_eq_field
    {T : OrientedTameQuotientK B FF}
    {S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W}
    (D : SelectedWordMarkedFieldData B FF T S) :
    D.branch.degree = Module.finrank ℚ_[2] K :=
  D.degree_eq.trans (FamilyFieldBranchSelection.semantic_degree_field S)

/-- Exact word provenance and all marking equations hold simultaneously for every selected
family. Characteristicness preserves the pre-reconstruction core character during calibration. -/
theorem nonempty_selectedWordMarkedFieldData_of_matchesRange
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    (RI : RamifiedIData K)
    {W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange) : Nonempty (SelectedWordMarkedFieldData B FF T S) := by
  obtain ⟨G, hdegree, hp, ⟨cert⟩⟩ := hasSelectedWordCertificate_of_matchesRange B FF D S hmatch
  let F := genAsmCompatibleFieldInputs_of_norm_reciprocity B FF T D G.hdeg
  obtain ⟨M⟩ := nonempty_alignedMarkedFieldEquiv G cert.cand F D RI
  refine ⟨{
    branch := M.branch G cert.cand
    degree_eq := hdegree
    profile := (selectedWordProfile_alignedBranch S G cert.cand M.equiv M.nu).mpr hp
    certificate := M.certificate G cert.cand
    equiv := M.equiv
    tame := M.tame
    pro2 := M.pro2
    maxPro2 := M.maxPro2
    cyclotomic := ?_
    nu := M.nu }⟩
  intro g
  exact (M.cyclotomic g).trans
    (alignedRealization_chi_eq_original G cert.cand
      (chiCycKTwo_characteristic_ramifiedI B FF D RI) M.equiv M.nu (cert.cand.pro2 g)).symm

/-- Range-based selection removes all family-coverage premises. -/
theorem nonempty_selectedWordMarkedFieldData_fieldSelectionFromRange
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    (RI : RamifiedIData K) :
    Nonempty (SelectedWordMarkedFieldData B FF T (selectFieldBranchFamilyFromRange B FF D RI)) :=
  nonempty_selectedWordMarkedFieldData_of_matchesRange B FF T D RI _
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI)

end FieldInputs

section Canonical
private instance compact_abs : CompactSpace AbsGalQ2 := by
  change CompactSpace (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)
  infer_instance
private instance td_abs : TotallyDisconnectedSpace AbsGalQ2 := by
  change TotallyDisconnectedSpace (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)
  infer_instance
private instance t2_abs : T2Space AbsGalQ2 := by
  change T2Space (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)
  infer_instance

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
private instance compact_galK : CompactSpace (GalK K) :=
  isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_of_isOpen _ (isOpen_fixingSubgroup K)).isCompact
private instance t2_galK : T2Space (GalK K) := inferInstanceAs (T2Space ↥(K.fixingSubgroup))
private instance td_galK : TotallyDisconnectedSpace (GalK K) :=
  inferInstanceAs (TotallyDisconnectedSpace ↥(K.fixingSubgroup))

/-- Bare finite-field endpoint retaining the exact selected word/core/marking profile,
certificate, field-degree equality, and every literal marking equation. -/
theorem nonempty_selectedWordMarkedFieldData_ramifiedI
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (RI : RamifiedIData K) :
    Nonempty (SelectedWordMarkedFieldData (markedRecipAt K) (dyadicUnitFiltration K)
      (orientedTameQuotientAt K (dyadicUnitFiltration K))
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) RI)) :=
  nonempty_selectedWordMarkedFieldData_fieldSelectionFromRange (markedRecipAt K)
    (dyadicUnitFiltration K) (orientedTameQuotientAt K (dyadicUnitFiltration K))
    (canonicalFiniteDyadicParameters K) RI

/-- Odd degree supplies the ramified-i condition without restricting the source constructor. -/
theorem nonempty_selectedWordMarkedFieldData_oddDegree
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    Nonempty (SelectedWordMarkedFieldData (markedRecipAt K) (dyadicUnitFiltration K)
      (orientedTameQuotientAt K (dyadicUnitFiltration K))
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) (ramifiedIData_of_odd_finrank K hodd))) :=
  nonempty_selectedWordMarkedFieldData_ramifiedI K (ramifiedIData_of_odd_finrank K hodd)
end Canonical

#print axioms selectedWordProfile_alignedBranch
#print axioms nonempty_selectedWordMarkedFieldData_of_matchesRange
#print axioms nonempty_selectedWordMarkedFieldData_ramifiedI
#print axioms nonempty_selectedWordMarkedFieldData_oddDegree

end
end GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWordFinal
