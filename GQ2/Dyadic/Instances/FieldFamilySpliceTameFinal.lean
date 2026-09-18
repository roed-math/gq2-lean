/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceFinal
import GQ2.Dyadic.TameMarkedReconstruction

/-!
# The selected ramified-i presentation over the actual tame quotient

The general selected source admits a field equivalence preserving its canonical tame map and
the full two-adic unramified character. Relative reconstruction, not the previously available
abstract equivalence, proves the marking equations. The source word and its certificate remain
part of the witness, including changed M-family splice words.

This theorem does not identify the two prescribed pro-two maps pointwise and does not assert
cyclotomic compatibility of the reconstructed equivalence. Those stronger marking claims are
not consequences of the tame equation alone.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceTameFinal
noncomputable section
open GQ2 GQ2.Dyadic
open Instances.FieldFamilyFlexibleAssembly Instances.FieldFamilyGeneralAssemblyExact
open Instances.FieldFamilySpliceSourceComplete Instances.FieldFamilySpliceFinal

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- General certified flexible assembly preserving the chosen tame quotient and full
unramified character. The output keeps the actual certificate's pro-two map visible. -/
theorem genAsmFlexible_exists_tameNuCompatible_equiv
    (G : GenAsmFlexibleBranch K B) (F : GenAsmCompatibleFieldInputs B FF G.degree)
    (W : WordCertificateRN G.degree (qOf K FF) G.word G.core G.coreIsProP G.nuP
      (standardNumerics G.degree)) :
    ∃ e : ContinuousMulEquiv (GammaR G.degree (qOf K FF) G.word) (GalK K),
      (∀ g, F.T.tameFK (e g) =
        TameSpec.tameOfSpec G.degree (qOf K FF) G.word W.tameSpecialization g) ∧
      (∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g))) := by
  let KS : KExactSupplyRN F.T G.degree G.core G.coreIsProP G.nuP :=
    kExactSupplyRN_of_markedCore G.hdeg G.realization.pro2
      G.realization.pro2_surjective G.realization.ker_pro2 G.realization.nu_compat
  let S₂ := KS.toSourceRN_compatible F.params F.params_n F.params_qK F.ramifiedData
  let S₁ := W.toSourceRN (two_le_qOf K FF) (even_qOf K FF)
  obtain ⟨e⟩ := nonempty_tameMarkedEquiv_of_sourcesRN S₁ S₂
    (qOf_ne_zero K FF) (even_qOf K FF) G.hnuP W.htame W.hwild
    F.T.tameFK_surjective (F.T.ker_tameFK ▸ F.T.isProP)
  let e' : ContinuousMulEquiv (GammaR G.degree (qOf K FF) G.word) (GalK K) := e.equiv
  have ht : ∀ g, F.T.tameFK (e' g) =
      TameSpec.tameOfSpec G.degree (qOf K FF) G.word W.tameSpecialization g := e.boundary_eq
  refine ⟨e', ht, fun g => ?_⟩
  rw [← F.T.tame_reciprocity_K, ht, W.compat]

/-- A selected-degree certified source together with a field equivalence carrying its tame
map and full two-adic unramified character. No prescribed core square is included. -/
def HasSelectedTameMarkedFlexibleAssemblyRN
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  ∃ G : GenAsmFlexibleBranch K B, G.degree = S.semantic.degree ∧
    ∃ cert : GenAsmFlexibleRowResidualRN FF G,
    ∃ e : ContinuousMulEquiv (GammaR G.degree (qOf K FF) G.word) (GalK K),
      (∀ g, T.tameFK (e g) = TameSpec.tameOfSpec G.degree (qOf K FF) G.word
        cert.cand.tameSpecialization g) ∧
      (∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (cert.cand.pro2 g)))

/-- Every range-selected ramified-i source has a marked field equivalence over its actual
tame quotient, in every degree and all five families, without additional arithmetic inputs. -/
theorem hasSelectedTameMarkedFlexibleAssemblyRN_fieldSelectionFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    (RI : RamifiedIData K) :
    HasSelectedTameMarkedFlexibleAssemblyRN B FF T
      (selectFieldBranchFamilyFromRange B FF D RI) := by
  obtain ⟨G, hdegree, ⟨cert⟩⟩ :=
    hasSelectedFlexibleRowResidualRN_fieldSelectionFromRange B FF D RI
  let F := genAsmCompatibleFieldInputs_of_norm_reciprocity B FF T D G.hdeg
  obtain ⟨e, ht, hnu⟩ := genAsmFlexible_exists_tameNuCompatible_equiv G F cert.cand
  exact ⟨G, hdegree, cert, e, ht, hnu⟩

#print axioms genAsmFlexible_exists_tameNuCompatible_equiv
#print axioms HasSelectedTameMarkedFlexibleAssemblyRN
#print axioms hasSelectedTameMarkedFlexibleAssemblyRN_fieldSelectionFromRange

end
end GQ2.Dyadic.Instances.FieldFamilySpliceTameFinal
