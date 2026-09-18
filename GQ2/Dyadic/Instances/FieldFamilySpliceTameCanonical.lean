/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceTameFinal
import GQ2.Dyadic.Instances.FieldCanonicalParameters
import GQ2.Dyadic.OddDegreeRamifiedI

/-!
# Canonical field-facing tame-marked ramified-i presentation

Canonical filtration, numerical parameters, and Krull-topology instances discharge the
auxiliary inputs. The standing reciprocity and tame constructors leave only a finite dyadic
field and its ramified-i scope condition. The actual source word, certificate, tame equation,
and full two-adic unramified equation remain in the conclusion.

No equality of the two prescribed pro-two maps or cyclotomic character equation is asserted.
The field-facing theorem inherits the established arithmetic constructors and analytic axiom
baseline; it introduces no new axiom.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceTameCanonical
noncomputable section
open GQ2 GQ2.Dyadic
open Instances.FieldFamilyFlexibleAssembly Instances.FieldFamilySpliceTameFinal
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

/-- Canonical numerical parameters remove auxiliary field choices while retaining the
supplied reciprocity and oriented tame bundles. -/
theorem hasSelectedTameMarkedFlexibleAssemblyRN_canonicalParameters
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (T : OrientedTameQuotientK B (dyadicUnitFiltration K)) (RI : RamifiedIData K) :
    HasSelectedTameMarkedFlexibleAssemblyRN B (dyadicUnitFiltration K) T
      (selectFieldBranchFamilyFromRange B (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) RI) :=
  hasSelectedTameMarkedFlexibleAssemblyRN_fieldSelectionFromRange B
    (dyadicUnitFiltration K) T (canonicalFiniteDyadicParameters K) RI

/-- Every finite dyadic field in the standing ramified-i scope admits a selected tame-marked
presentation using the canonical reciprocity and tame constructors. -/
theorem hasSelectedTameMarkedFlexibleAssemblyRN_ramifiedI
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (RI : RamifiedIData K) :
    HasSelectedTameMarkedFlexibleAssemblyRN (markedRecipAt K) (dyadicUnitFiltration K)
      (orientedTameQuotientAt K (dyadicUnitFiltration K))
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) RI) :=
  hasSelectedTameMarkedFlexibleAssemblyRN_canonicalParameters (markedRecipAt K)
    (orientedTameQuotientAt K (dyadicUnitFiltration K)) RI

/-- Odd field degree discharges ramified-i by the proved norm obstruction. -/
theorem hasSelectedTameMarkedFlexibleAssemblyRN_oddDegree
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    HasSelectedTameMarkedFlexibleAssemblyRN (markedRecipAt K) (dyadicUnitFiltration K)
      (orientedTameQuotientAt K (dyadicUnitFiltration K))
      (selectFieldBranchFamilyFromRange (markedRecipAt K) (dyadicUnitFiltration K)
        (canonicalFiniteDyadicParameters K) (ramifiedIData_of_odd_finrank K hodd)) :=
  hasSelectedTameMarkedFlexibleAssemblyRN_ramifiedI K (ramifiedIData_of_odd_finrank K hodd)

/-- Bare field-facing existence retaining the actual word, corrected certificate, and the
literal tame and full two-adic unramified equations at the exact field degree. -/
theorem exists_certifiedTameMarkedFlexiblePresentation_ramifiedI
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
        (∀ g, (markedRecipAt K).nu_ur (toAbK K (e g)) =
          ztwoIota (G.nuP (cert.cand.pro2 g))) := by
  obtain ⟨G, hdegree, cert, e, ht, hnu⟩ :=
    hasSelectedTameMarkedFlexibleAssemblyRN_ramifiedI K RI
  refine ⟨G, hdegree.trans ?_, cert, e, ht, hnu⟩
  exact FamilyFieldBranchSelection.semantic_degree_field _

#print axioms hasSelectedTameMarkedFlexibleAssemblyRN_canonicalParameters
#print axioms hasSelectedTameMarkedFlexibleAssemblyRN_ramifiedI
#print axioms hasSelectedTameMarkedFlexibleAssemblyRN_oddDegree
#print axioms exists_certifiedTameMarkedFlexiblePresentation_ramifiedI

end
end GQ2.Dyadic.Instances.FieldFamilySpliceTameCanonical
