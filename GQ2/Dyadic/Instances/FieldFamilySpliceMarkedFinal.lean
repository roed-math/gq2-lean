/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceAlignedFinal
import GQ2.Dyadic.Instances.FieldCyclotomicCharacteristic

/-!
# Tame, pro-two, cyclotomic, and full unramified field compatibility

The cyclotomic character below is fixed using the ORIGINAL supplied core realization, before
choosing a reconstructed field equivalence. Characteristicness of the actual field pro-two
orientation shows that existential alignment does not change this character. Thus the aligned
realization gives all four marking equations on the same actual certified source word.

Only the existential realization is calibrated. No claim is made that reconstruction preserves
an arbitrary previously supplied realization pointwise.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceMarkedFinal
noncomputable section
open GQ2 GQ2.Dyadic
open Instances.FieldFamilyFlexibleAssembly Instances.FieldFamilyGeneralAssemblyExact
open Instances.FieldFamilySpliceFinal Instances.FieldFamilySpliceSourceComplete
open Instances.FieldFamilySpliceTameFinal Instances.FieldFamilySpliceAlignedFinal
open Instances.FieldCyclotomicCharacteristic
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

variable (G : GenAsmFlexibleBranch K B)
  (W : WordCertificateRN G.degree (qOf K FF) G.word G.core G.coreIsProP G.nuP
    (standardNumerics G.degree))

omit [T2Space (GalK K)] in
/-- Characteristic orientation makes the OLD core character independent of the subsequently
chosen aligned realization. -/
theorem alignedRealization_chi_eq_original
    (Hchar : IsCharacteristicCharacter (chiCycKTwo (K := K)))
    (e : ContinuousMulEquiv (GammaR G.degree (qOf K FF) G.word) (GalK K))
    (hnu : ∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g)))
    (p : G.core) :
    chiCycKTwo (K := K) ((alignedRealization G W e hnu).equiv p) =
      chiCycKTwo (K := K) (G.realization.equiv p) := by
  have h := Hchar
    (G.realization.equiv.symm.trans (alignedRealization G W e hnu).equiv)
    (G.realization.equiv p)
  simpa only [ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.symm_apply_apply] using h

omit [T2Space (GalK K)] in
/-- The reconstructed equivalence respects the original core's cyclotomic character, not a
character defined after reconstruction by pulling back along `e`. -/
theorem cyclotomic_eq_original_of_aligned
    (Hchar : IsCharacteristicCharacter (chiCycKTwo (K := K)))
    (e : ContinuousMulEquiv (GammaR G.degree (qOf K FF) G.word) (GalK K))
    (hnu : ∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g)))
    (g : GammaR G.degree (qOf K FF) G.word) :
    chiCycK K (e g) = chiCycKTwo (K := K) (G.realization.equiv (W.pro2 g)) := by
  rw [← chiCycKTwo_maxProPMk, alignedRealization_maxPro2 G W e hnu]
  exact alignedRealization_chi_eq_original G W Hchar e hnu (W.pro2 g)

/-- A field equivalence with all marking equations. Its pro-two realization is the calibrated
one, while its cyclotomic character is fixed by the ORIGINAL supplied branch `G`. -/
structure AlignedMarkedFieldEquiv (T : OrientedTameQuotientK B FF) where
  equiv : ContinuousMulEquiv (GammaR G.degree (qOf K FF) G.word) (GalK K)
  nu : ∀ g, B.nu_ur (toAbK K (equiv g)) = ztwoIota (G.nuP (W.pro2 g))
  tame : ∀ g, T.tameFK (equiv g) =
    TameSpec.tameOfSpec G.degree (qOf K FF) G.word W.tameSpecialization g
  pro2 : ∀ g, (alignedRealization G W equiv nu).pro2 (equiv g) = W.pro2 g
  maxPro2 : ∀ g, maxProPMk 2 (GalK K) (equiv g) =
    (alignedRealization G W equiv nu).equiv (W.pro2 g)
  cyclotomic : ∀ g, chiCycK K (equiv g) =
    chiCycKTwo (K := K) (G.realization.equiv (W.pro2 g))

/-- The genuinely new existential branch, with only its realization replaced. -/
def AlignedMarkedFieldEquiv.branch {T : OrientedTameQuotientK B FF}
    (M : AlignedMarkedFieldEquiv G W T) : GenAsmFlexibleBranch K B :=
  alignedBranch G W M.equiv M.nu

/-- The actual corrected word certificate survives alignment definitionally. -/
def AlignedMarkedFieldEquiv.certificate {T : OrientedTameQuotientK B FF}
    (M : AlignedMarkedFieldEquiv G W T) :
    GenAsmFlexibleRowResidualRN FF (M.branch G W) :=
  alignedBranch_certificate G W M.equiv M.nu

/-- Any supplied certified source over a ramified-i field admits all four marking equations
after calibrating its existential realization. Its original core character is preserved. -/
theorem nonempty_alignedMarkedFieldEquiv
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    (D : FiniteDyadicParameters K FF) (RI : RamifiedIData K) :
    Nonempty (AlignedMarkedFieldEquiv G W F.T) := by
  obtain ⟨e, ht, hnu⟩ := genAsmFlexible_exists_tameNuCompatible_equiv G F W
  exact ⟨{
    equiv := e
    nu := hnu
    tame := ht
    pro2 := alignedRealization_pro2 G W e hnu
    maxPro2 := alignedRealization_maxPro2 G W e hnu
    cyclotomic := cyclotomic_eq_original_of_aligned G W
      (chiCycKTwo_characteristic_ramifiedI B FF D RI) e hnu }⟩

omit G W in
/-- A selected source and certificate, followed by a field equivalence whose aligned branch
has all marking equations. The original core character remains explicit in the witness. -/
def HasSelectedFullyMarkedFlexibleAssemblyRN
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  ∃ G : GenAsmFlexibleBranch K B, G.degree = S.semantic.degree ∧
    ∃ cert : GenAsmFlexibleRowResidualRN FF G,
      Nonempty (AlignedMarkedFieldEquiv G cert.cand T)

omit G W in
/-- All degrees and all five selected families have a complete marked field presentation
within the original ramified-i scope, with no additional marking hypothesis. -/
theorem hasSelectedFullyMarkedFlexibleAssemblyRN_fieldSelectionFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    (RI : RamifiedIData K) :
    HasSelectedFullyMarkedFlexibleAssemblyRN B FF T
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  obtain ⟨G, hdegree, ⟨cert⟩⟩ :=
    hasSelectedFlexibleRowResidualRN_fieldSelectionFromRange B FF D RI
  let F := genAsmCompatibleFieldInputs_of_norm_reciprocity B FF T D G.hdeg
  exact ⟨G, hdegree, cert, nonempty_alignedMarkedFieldEquiv G cert.cand F D RI⟩

#print axioms alignedRealization_chi_eq_original
#print axioms cyclotomic_eq_original_of_aligned
#print axioms nonempty_alignedMarkedFieldEquiv
#print axioms hasSelectedFullyMarkedFlexibleAssemblyRN_fieldSelectionFromRange

end
end GQ2.Dyadic.Instances.FieldFamilySpliceMarkedFinal
