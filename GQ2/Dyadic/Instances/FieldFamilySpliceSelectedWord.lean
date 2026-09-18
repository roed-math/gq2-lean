/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceSourceComplete
import GQ2.Dyadic.Instances.FieldFamilySpliceMarkedFinal

/-!
# The actual constructor and parameters of the selected splice source

The earlier flexible existential intentionally forgot its source constructor. This module
retains exact word, core, and marking provenance. L and N use the selected canonical display;
M0 uses either its canonical word or the pair splice; positive Mpc uses the mobile splice.
The mobile unit is the actual D-coordinate and is congruent to the selected unit modulo 2^r.
No equality with the frozen Mpc word, or with a frozen M0 word on the strict branch, is asserted.

Heterogeneous equality is used only to express literal word/marking equality across the degree
and core indices; the degree and core equalities are included alongside it.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWord
noncomputable section
open GQ2 GQ2.Dyadic Count MarkedCore Multiplicative
open Instances.FieldFamilyFlexibleAssembly Instances.FieldFamilyCampaignBoundary
open Instances.FieldFamilyGeneralAssemblyExact Instances.FieldFamilySpliceFinal
open Instances.EvenMSelectedSpliceComplete Instances.EvenMSelectedSpliceCoverage
open Instances.EvenMHeadHandlePairSpliceSupply Instances.EvenMHeadHandlePairSpliceBoundary
open Instances.MpcMobileSpliceSupply Instances.MpcMobileSpliceBoundary
open Instances.MpcMobileNuSource Instances.EvenMHeadHandleSource
open Instances.MFieldStrictHandleNormalForm Instances.MFieldCanonicalMarkingTransitivity
open Instances.MpcGeneralHandleFamily Instances.M0FamilyField
open Instances.FieldFamilySpliceMarkedFinal Instances.FieldFamilySpliceAlignedFinal
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Literal source data, with index equalities exposed and realization deliberately absent. -/
def MatchesSource {B : MarkedRecip Rec K} (G : GenAsmFlexibleBranch K B)
    (n : ℕ) (word : PWord (Generator n)) (core : ProfiniteGrp)
    (nuP : ContinuousMonoidHom core Ztwo) : Prop :=
  G.degree = n ∧ HEq G.word word ∧ G.core = core ∧ HEq G.nuP nuP

/-- Exact selected canonical word and core. The displayed Npc parameters are retained. -/
def CanonicalSelectedWordCore {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (G : GenAsmFlexibleBranch K B) : Prop :=
  G.degree = (selectedPresentation S).degree ∧
    HEq G.word (selectedPresentation S).word ∧ G.core = genAsmCore (selectedPresentation S)

/-- The exact source constructors admitted by the selected branch. -/
def SelectedWordProfile {B : MarkedRecip Rec K} (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (G : GenAsmFlexibleBranch K B) : Prop :=
  match S.branch with
  | .L | .N0 _ | .Npc _ _ _ => CanonicalSelectedWordCore S G
  | .M0 alpha => CanonicalSelectedWordCore S G ∨
      ∃ (halpha : 1 ≤ alpha) (hq0 : qOf K FF ≠ 0)
        (j : Fin (handleCount P (.M0 alpha)))
        (nuP : ContinuousMonoidHom (DM alpha (handleCount P (.M0 alpha))) Ztwo),
        MatchesSource G (2 + 2 * handleCount P (.M0 alpha))
          (headHandlePairSpliceW alpha (handleCount P (.M0 alpha)) (qOf K FF)
            halpha hq0 (even_qOf K FF) j nuP)
          (DM alpha (handleCount P (.M0 alpha))) nuP ∧
        nuP (dmGen alpha _ (handleIdxU j)) = ztwoOne
  | .Mpc alpha r epsilon eta =>
      ∃ (halpha : 1 ≤ alpha) (hq0 : qOf K FF ≠ 0) (etaD : ℤ_[2]ˣ)
        (nuP : ContinuousMonoidHom (DM alpha (handleCount P (.Mpc alpha r epsilon eta))) Ztwo),
        MatchesSource G (2 + 2 * handleCount P (.Mpc alpha r epsilon eta))
          (tameSplice
            (mpcMobileTameCorrectedW hq0 (even_qOf K FF) alpha r (p epsilon r)
              (handleCount P (.Mpc alpha r epsilon eta)) etaD halpha nuP)
            (Words.MCompact.mCompactW alpha (handleCount P (.Mpc alpha r epsilon eta))))
          (DM alpha (handleCount P (.Mpc alpha r epsilon eta))) nuP ∧
        ztwoIota (nuP (dmD alpha _)) = ofAdd (etaD : ℤ_[2]) ∧
        ∃ w : ℤ_[2], (etaD : ℤ_[2]) = (eta : ℤ_[2]) + 2 ^ r * w

/-- A certificate together with exact constructor provenance, at the selected degree. -/
def HasSelectedWordCertificate (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  ∃ G : GenAsmFlexibleBranch K B, G.degree = S.semantic.degree ∧
    SelectedWordProfile FF S G ∧ Nonempty (GenAsmFlexibleRowResidualRN FF G)

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
private theorem canonical_profile
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (H : HasSelectedRowResidualRN B FF S) :
    ∃ G : GenAsmFlexibleBranch K B, G.degree = S.semantic.degree ∧
      CanonicalSelectedWordCore S G ∧ Nonempty (GenAsmFlexibleRowResidualRN FF G) := by
  obtain ⟨G, hp, ⟨cert⟩⟩ := H
  refine ⟨GenAsmFlexibleBranch.ofCanonical G,
    G.hdeg.symm.trans S.degree_eq_field.symm, ?_,
    ⟨GenAsmFlexibleRowResidualRN.ofCanonical G cert⟩⟩
  change G.pres.degree = (selectedPresentation S).degree ∧
    HEq G.pres.word (selectedPresentation S).word ∧
    genAsmCore G.pres = genAsmCore (selectedPresentation S)
  rw [hp]
  exact ⟨rfl, HEq.rfl, rfl⟩

omit [T2Space (GalK K)] in
private theorem selectedWordCertificate_m0_strict
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hb : S.branch = .M0 alpha)
    (H : MFieldStrictNormalizedHandlePivotAtLevel B alpha 0 (handleCount P (.M0 alpha))) :
    HasSelectedWordCertificate B FF S := by
  let h := handleCount P (.M0 alpha)
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
  have hα : 2 ≤ alpha := by have hv := S.valid; rw [hb] at hv; exact hv
  have hq0 : qOf K FF ≠ 0 := by have := two_le_qOf K FF; omega
  let halpha : 1 ≤ alpha := by omega
  let C : MFieldSpliceCompleteData B FF alpha h := {
    word := headHandlePairSpliceW alpha h (qOf K FF) halpha hq0 (even_qOf K FF) j nuP
    nuP := nuP
    hnuP := mFieldTransportZ_surjective B FF e.1
    realization := { equiv := e.1, nu_equiv := fun x => ztwoIota_mFieldTransportZ B e.1 x }
    core := flexibleCore_headHandlePairSplice halpha hq0 (even_qOf K FF) j nuP hu
    specializes := headHandlePairSpliceW_specializes halpha hq0 (even_qOf K FF) j nuP
    supply := uniformStokesSupply_headHandlePairSplice halpha hα hq0 (even_qOf K FF) j nuP
    certificate := headHandlePairSplice_flexibleCertificateLeaves
      halpha hα hq0 (even_qOf K FF) j nuP hu }
  have hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h := by
    have hd := S.degree_eq_field
    rw [hb] at hd
    exact hd.symm
  refine ⟨C.toMFieldSpliceData.flexibleBranch hdeg,
    hdeg.symm.trans S.degree_eq_field.symm, ?_, ⟨C.rowResidual hdeg⟩⟩
  rw [SelectedWordProfile, hb]
  exact Or.inr ⟨halpha, hq0, j, nuP, ⟨rfl, HEq.rfl, rfl, HEq.rfl⟩, hu⟩

omit [T2Space (GalK K)] in
private theorem selectedWordCertificate_mpc
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hb : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount P (.Mpc alpha r epsilon eta))) (chiCycKTwo (K := K))) :
    HasSelectedWordCertificate B FF S := by
  let h := handleCount P (.Mpc alpha r epsilon eta)
  let nuP := mFieldTransportZ B e.1
  have hunit := isUnit_D_of_familySelection B FF S hb e
  let etaD : ℤ_[2]ˣ := hunit.unit
  have hd : ztwoIota (nuP (dmD alpha h)) = ofAdd (etaD : ℤ_[2]) := by
    rw [show (etaD : ℤ_[2]) = toAdd (ztwoIota (nuP (dmD alpha h))) from hunit.unit_spec]
    rfl
  have heta : ∃ w : ℤ_[2], (etaD : ℤ_[2]) = (eta : ℤ_[2]) + 2 ^ r * w := by
    obtain ⟨_, ⟨w, hw⟩, _⟩ := level_and_residues_of_familySelection B FF S hb e
    refine ⟨w, ?_⟩
    rw [show (etaD : ℤ_[2]) = toAdd (ztwoIota (nuP (dmD alpha h))) from hunit.unit_spec]
    rw [ztwoIota_mFieldTransportZ]
    exact hw
  have hα : 2 ≤ alpha := by have hv := S.valid; rw [hb] at hv; exact hv.1
  have hq0 : qOf K FF ≠ 0 := by have := two_le_qOf K FF; omega
  let halpha : 1 ≤ alpha := by omega
  let coreWord := mpcMobileTameCorrectedW hq0 (even_qOf K FF)
    alpha r (p epsilon r) h etaD halpha nuP
  let C : MFieldSpliceCompleteData B FF alpha h := {
    word := tameSplice coreWord (Words.MCompact.mCompactW alpha h)
    nuP := nuP
    hnuP := mFieldTransportZ_surjective B FF e.1
    realization := { equiv := e.1, nu_equiv := fun x => ztwoIota_mFieldTransportZ B e.1 x }
    core := mpcMobileTameSplice_core hq0 (even_qOf K FF) alpha r (p epsilon r) h etaD halpha nuP hd
    specializes := tameSpecializes_tameSplice
      (mpcMobileTameCorrectedW_specializes hq0 (even_qOf K FF) etaD halpha nuP)
      (tameSpecializes_mCompact hq0 (even_qOf K FF) alpha h)
    supply := mpcMobileTameSplice_uniformStokesSupply hq0 (even_qOf K FF) etaD halpha hα nuP
    certificate := mpcMobileTameSplice_flexibleCertificateLeaves
      hq0 (even_qOf K FF) etaD halpha hα nuP hd }
  have hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h := by
    have hd := S.degree_eq_field
    rw [hb] at hd
    exact hd.symm
  refine ⟨C.toMFieldSpliceData.flexibleBranch hdeg,
    hdeg.symm.trans S.degree_eq_field.symm, ?_, ⟨C.rowResidual hdeg⟩⟩
  rw [SelectedWordProfile, hb]
  exact ⟨halpha, hq0, etaD, nuP, ⟨rfl, HEq.rfl, rfl, HEq.rfl⟩, hd, heta⟩

/-- Every selected family has a certificate retaining its exact actual source constructor. -/
theorem hasSelectedWordCertificate_of_matchesRange
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF)
    {W : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF) W)
    (hmatch : W.MatchesCyclotomicRange) : HasSelectedWordCertificate B FF S := by
  cases hb : S.branch with
  | L =>
      obtain ⟨G, hdeg, hp, hc⟩ := canonical_profile B FF S (hasSelectedRowResidualRN_l B FF D S hb)
      exact ⟨G, hdeg, by simpa only [SelectedWordProfile, hb] using hp, hc⟩
  | N0 alpha =>
      obtain ⟨G, hdeg, hp, hc⟩ := canonical_profile B FF S
        (hasSelectedRowResidualRN_n0 B FF S hmatch hb)
      exact ⟨G, hdeg, by simpa only [SelectedWordProfile, hb] using hp, hc⟩
  | Npc alpha r eta =>
      obtain ⟨G, hdeg, hp, hc⟩ := canonical_profile B FF S
        (hasSelectedRowResidualRN_npc B FF S hmatch hb)
      exact ⟨G, hdeg, by simpa only [SelectedWordProfile, hb] using hp, hc⟩
  | M0 alpha =>
      have H := evenCanonicalOrStrictHandleBoundary_of_familySelection B FF S hmatch
      rw [EvenCanonicalOrStrictHandleBoundary, hb] at H
      rcases H with hc | hs
      · obtain ⟨G, hdeg, hp, hcert⟩ := canonical_profile B FF S
          (hasSelectedRowResidualRN_m0_of_cPivot B FF S hb hc)
        exact ⟨G, hdeg, by rw [SelectedWordProfile, hb]; exact Or.inl hp, hcert⟩
      · exact selectedWordCertificate_m0_strict B FF S hb hs
  | Mpc alpha r epsilon eta =>
      obtain ⟨e⟩ := orientedEquivM_of_familySelection_of_matchesRange_mpc B FF S hmatch hb
      exact selectedWordCertificate_mpc B FF S hb e

/-- Range-based selection discharges the profile producer uniformly in all ranks. -/
theorem hasSelectedWordCertificate_fieldSelectionFromRange
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    HasSelectedWordCertificate B FF (selectFieldBranchFamilyFromRange B FF D RI) :=
  hasSelectedWordCertificate_of_matchesRange B FF D _
    (fieldFamilyWitnessFromRange_matchesCyclotomicRange B FF D RI)

#print axioms hasSelectedWordCertificate_of_matchesRange
#print axioms hasSelectedWordCertificate_fieldSelectionFromRange

end
end GQ2.Dyadic.Instances.FieldFamilySpliceSelectedWord
