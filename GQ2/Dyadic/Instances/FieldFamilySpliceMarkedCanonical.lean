/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceMarkedFinal
import GQ2.Dyadic.Instances.FieldCanonicalParameters
import GQ2.Dyadic.OddDegreeRamifiedI

/-!
# Canonical fully marked field presentation in the ramified-i scope

Canonical field bundles discharge all auxiliary choices. The final existential witness carries
the actual certified source word, at the exact field degree, with literal tame, maximal-pro-two,
cyclotomic, and full unramified equations. Its realization is calibrated to the reconstructed
equivalence; this does not assert preservation of an arbitrary previously fixed realization.

The stronger record-valued endpoint also retains the ORIGINAL core character chosen before
reconstruction. Characteristicness proves that calibration leaves that character unchanged.
No new arithmetic axiom is introduced; the established field-constructor baseline is inherited.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical
noncomputable section
open GQ2 GQ2.Dyadic
open Instances.FieldFamilyFlexibleAssembly Instances.FieldFamilySpliceMarkedFinal
open Instances.FieldFamilySpliceAlignedFinal Instances.FieldCyclotomicCharacteristic
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

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

/-- Canonical filtration and numerical parameters retain the supplied reciprocity and tame
bundles, with no residual marked-reconstruction hypothesis. -/
theorem hasSelectedFullyMarkedFlexibleAssemblyRN_canonicalParameters
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (T : OrientedTameQuotientK B (dyadicUnitFiltration K)) (RI : RamifiedIData K) :
    HasSelectedFullyMarkedFlexibleAssemblyRN B (dyadicUnitFiltration K) T
      (selectFieldBranchFamilyFromRange B (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) RI) :=
  hasSelectedFullyMarkedFlexibleAssemblyRN_fieldSelectionFromRange B
    (dyadicUnitFiltration K) T (canonicalFiniteDyadicParameters K) RI

/-- Every finite dyadic field in the standing ramified-i scope has a selected fully marked
presentation, with the pre-reconstruction core character retained explicitly. -/
theorem hasSelectedFullyMarkedFlexibleAssemblyRN_ramifiedI
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (RI : RamifiedIData K) :
    HasSelectedFullyMarkedFlexibleAssemblyRN (markedRecipAt K) (dyadicUnitFiltration K)
      (orientedTameQuotientAt K (dyadicUnitFiltration K))
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) RI) :=
  hasSelectedFullyMarkedFlexibleAssemblyRN_canonicalParameters (markedRecipAt K)
    (orientedTameQuotientAt K (dyadicUnitFiltration K)) RI

/-- Odd degree supplies the ramified-i hypothesis by the established norm obstruction. -/
theorem hasSelectedFullyMarkedFlexibleAssemblyRN_oddDegree
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    HasSelectedFullyMarkedFlexibleAssemblyRN (markedRecipAt K) (dyadicUnitFiltration K)
      (orientedTameQuotientAt K (dyadicUnitFiltration K))
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) (ramifiedIData_of_odd_finrank K hodd)) :=
  hasSelectedFullyMarkedFlexibleAssemblyRN_ramifiedI K (ramifiedIData_of_odd_finrank K hodd)

/-- Bare field-facing existence with every literal marking equation on the new existential
realization. The source word, core, full nu, and certificate are unchanged by calibration. -/
theorem exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (RI : RamifiedIData K) :
    ∃ G : GenAsmFlexibleBranch K (markedRecipAt K),
      G.degree = Module.finrank ℚ_[2] K ∧
      ∃ cert : GenAsmFlexibleRowResidualRN (dyadicUnitFiltration K) G,
      ∃ e : ContinuousMulEquiv
        (GammaR G.degree (qOf K (dyadicUnitFiltration K)) G.word) (GalK K),
        (∀ g, (orientedTameQuotientAt K (dyadicUnitFiltration K)).tameFK (e g) =
          TameSpec.tameOfSpec G.degree (qOf K (dyadicUnitFiltration K)) G.word
            cert.cand.tameSpecialization g) ∧
        (∀ g, G.realization.pro2 (e g) = cert.cand.pro2 g) ∧
        (∀ g, maxProPMk 2 (GalK K) (e g) = G.realization.equiv (cert.cand.pro2 g)) ∧
        (∀ g, chiCycK K (e g) = chiCycKTwo (K := K)
          (G.realization.equiv (cert.cand.pro2 g))) ∧
        (∀ g, (markedRecipAt K).nu_ur (toAbK K (e g)) =
          ztwoIota (G.nuP (cert.cand.pro2 g))) := by
  obtain ⟨G, hdegree, cert, ⟨M⟩⟩ :=
    hasSelectedFullyMarkedFlexibleAssemblyRN_ramifiedI K RI
  refine ⟨M.branch G cert.cand, hdegree.trans ?_, M.certificate G cert.cand,
    M.equiv, M.tame, M.pro2, M.maxPro2, ?_, M.nu⟩
  · exact FamilyFieldBranchSelection.semantic_degree_field _
  · intro g
    exact (M.cyclotomic g).trans
      (alignedRealization_chi_eq_original G cert.cand
        (chiCycKTwo_characteristic_ramifiedI (markedRecipAt K)
          (dyadicUnitFiltration K) (canonicalFiniteDyadicParameters K) RI)
        M.equiv M.nu (cert.cand.pro2 g)).symm

#print axioms hasSelectedFullyMarkedFlexibleAssemblyRN_canonicalParameters
#print axioms hasSelectedFullyMarkedFlexibleAssemblyRN_ramifiedI
#print axioms hasSelectedFullyMarkedFlexibleAssemblyRN_oddDegree
#print axioms exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI

end
end GQ2.Dyadic.Instances.FieldFamilySpliceMarkedCanonical
