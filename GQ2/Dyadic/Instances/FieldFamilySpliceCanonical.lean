/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceFinal
import GQ2.Dyadic.Instances.FieldCanonicalParameters
import GQ2.Dyadic.OddDegreeRamifiedI
import GQ2.Foundations.Axioms

/-!
# Canonical field-facing ramified-i presentation endpoint

The proved unit filtration and fundamental identity discharge the numerical field inputs.
Concrete Krull-topology instances discharge all topology binders. Specialization to the
standing localReciprocity, markedRecipAt, and orientedTameQuotientAt constructors therefore
leaves only a finite dyadic field and its original RamifiedIData scope condition. Odd degree
discharges that condition by the proved norm obstruction.

The conclusion retains the actual carried source word and its complete corrected certificate;
it does not identify a changed M source with the old frozen canonical M word.

The generic-bundle result uses the standard axioms plus the established Hilbert norm criterion,
peripheral cyclotomic action, relative Stiefel-Whitney comparison, local Tate duality, absolute
Galois finite generation, and local Euler characteristic inputs. The bare field results add the
three standing reciprocity/marked-reciprocity/oriented-tame constructors. No new axiom is added.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceCanonical
noncomputable section
open GQ2 GQ2.Dyadic
open Instances.FieldFamilySpliceSourceComplete
open Instances.FieldFamilyFlexibleAssembly
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

/-- Canonical filtration and numerical parameters remove all auxiliary field-parameter choices.
The supplied reciprocity and tame bundles remain explicit. -/
theorem hasSelectedFlexibleAssemblyRN_canonicalParameters
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (T : OrientedTameQuotientK B (dyadicUnitFiltration K)) (RI : RamifiedIData K) :
    HasSelectedFlexibleAssemblyRN B (dyadicUnitFiltration K)
      (selectFieldBranchFamilyFromRange B (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) RI) :=
  FieldFamilySpliceFinal.hasSelectedFlexibleAssemblyRN_fieldSelectionFromRange B
    (dyadicUnitFiltration K) T (canonicalFiniteDyadicParameters K) RI

/-- Every finite dyadic field in the campaign's ramified-i scope has a complete selected
flexible presentation, using the standing reciprocity/tame constructors. -/
theorem hasSelectedFlexibleAssemblyRN_ramifiedI
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (RI : RamifiedIData K) :
    HasSelectedFlexibleAssemblyRN (markedRecipAt K) (dyadicUnitFiltration K)
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) RI) :=
  hasSelectedFlexibleAssemblyRN_canonicalParameters (markedRecipAt K)
    (orientedTameQuotientAt K (dyadicUnitFiltration K)) RI

/-- Odd degree discharges the ramified-i hypothesis by the proved norm obstruction. -/
theorem hasSelectedFlexibleAssemblyRN_oddDegree
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    HasSelectedFlexibleAssemblyRN (markedRecipAt K) (dyadicUnitFiltration K)
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) (ramifiedIData_of_odd_finrank K hodd)) :=
  hasSelectedFlexibleAssemblyRN_ramifiedI K (ramifiedIData_of_odd_finrank K hodd)

/-- Bare field-facing existence: the carried word, its full corrected certificate, and its
actual candidate/Galois equivalence are retained at the field's exact degree. -/
theorem exists_certifiedFlexiblePresentation_ramifiedI
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (RI : RamifiedIData K) :
    ∃ G : GenAsmFlexibleBranch K (markedRecipAt K),
      G.degree = Module.finrank ℚ_[2] K ∧
      Nonempty (GenAsmFlexibleRowResidualRN (dyadicUnitFiltration K) G) ∧
      Nonempty (ContinuousMulEquiv
        ((candidateGroup G.degree (qOf K (dyadicUnitFiltration K)) G.word : ProfiniteGrp) : Type)
        (GalK K)) := by
  obtain ⟨G, hdegree, hcert, hequiv⟩ := hasSelectedFlexibleAssemblyRN_ramifiedI K RI
  refine ⟨G, hdegree.trans ?_, hcert, hequiv⟩
  exact FamilyFieldBranchSelection.semantic_degree_field _

#print axioms hasSelectedFlexibleAssemblyRN_canonicalParameters
#print axioms hasSelectedFlexibleAssemblyRN_ramifiedI
#print axioms hasSelectedFlexibleAssemblyRN_oddDegree
#print axioms exists_certifiedFlexiblePresentation_ramifiedI
end
end GQ2.Dyadic.Instances.FieldFamilySpliceCanonical

