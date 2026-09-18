/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilySpliceTameFinal
import GQ2.Dyadic.SourceBoundaryMarkingRN

/-!
# Existential alignment of the carried field realization

A tame-compatible equivalence determines its own maximal-pro-two identification. Replacing
only the existential branch's realization by this identification leaves its degree, word,
core, full unramified marking, and word certificate unchanged. The resulting NEW witness has
the literal prescribed pro-two square, in addition to its tame and full unramified equations.

This is not a theorem that an arbitrary previously fixed realization is preserved. It does
not assert a cyclotomic equation; that requires orientation compatibility separately.
-/

namespace GQ2.Dyadic.Instances.FieldFamilySpliceAlignedFinal
noncomputable section
open GQ2 GQ2.Dyadic
open Instances.FieldFamilyFlexibleAssembly Instances.FieldFamilySpliceTameFinal
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

variable (G : GenAsmFlexibleBranch K B)
  (W : WordCertificateRN G.degree (qOf K FF) G.word G.core G.coreIsProP G.nuP
    (standardNumerics G.degree))
  (e : ContinuousMulEquiv (GammaR G.degree (qOf K FF) G.word) (GalK K))

/-- Pull the actual certificate's pro-two map across the chosen field equivalence. -/
def alignedFieldPro2 : ContinuousMonoidHom (galKProfinite K) G.core :=
  W.pro2.comp ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous_toFun⟩

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
private theorem alignedFieldPro2_surjective :
    Function.Surjective (alignedFieldPro2 G W e) := W.hpro2.comp e.symm.surjective

omit [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
private theorem alignedFieldPro2_ker :
    (alignedFieldPro2 G W e).toMonoidHom.ker = proPKernel 2 (galKProfinite K) :=
  ker_comp_continuousMulEquiv e.symm W.pro2 W.ker_pro2

private def alignedCoreIso : ContinuousMulEquiv
    (maxProPQuotient 2 (GalK K)) G.core :=
  pro2IsoK G.coreIsProP (alignedFieldPro2 G W e)
    (alignedFieldPro2_surjective G W e) (alignedFieldPro2_ker G W e)

omit [T2Space (GalK K)] in
private theorem alignedCoreIso_mk (g : GalK K) :
    alignedCoreIso G W e (maxProPMk 2 (GalK K) g) = alignedFieldPro2 G W e g :=
  DFunLike.congr_fun ((maxProPHomEquiv G.coreIsProP).apply_symm_apply
    (alignedFieldPro2 G W e)) g

/-- The realization induced by the actual field equivalence is correctly marked by full
`nuP`. Only the already-proved unramified equation is used. -/
def alignedRealization
    (hnu : ∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g))) :
    MarkedCoreRealization (K := K) (B := B) G.core G.nuP where
  equiv := (alignedCoreIso G W e).symm
  nu_equiv p := by
    obtain ⟨g, rfl⟩ := W.hpro2 p
    have heq : (alignedCoreIso G W e).symm (W.pro2 g) =
        maxProPMk 2 (GalK K) (e g) := by
      apply (alignedCoreIso G W e).injective
      rw [ContinuousMulEquiv.apply_symm_apply, alignedCoreIso_mk]
      change W.pro2 g = W.pro2 (e.symm (e g))
      rw [e.symm_apply_apply]
    rw [heq, nuUrKTwo_maxProPMk]
    exact (hnu g).symm

omit [T2Space (GalK K)] in
/-- The newly aligned field projection is exactly the certificate projection under `e`. -/
theorem alignedRealization_pro2
    (hnu : ∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g)))
    (g : GammaR G.degree (qOf K FF) G.word) :
    (alignedRealization G W e hnu).pro2 (e g) = W.pro2 g := by
  change alignedCoreIso G W e (maxProPMk 2 (GalK K) (e g)) = W.pro2 g
  rw [alignedCoreIso_mk]
  change W.pro2 (e.symm (e g)) = W.pro2 g
  rw [e.symm_apply_apply]

omit [T2Space (GalK K)] in
/-- The induced realization identifies the certificate quotient with the field's actual
maximal-pro-two projection on the nose. -/
theorem alignedRealization_maxPro2
    (hnu : ∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g)))
    (g : GammaR G.degree (qOf K FF) G.word) :
    maxProPMk 2 (GalK K) (e g) = (alignedRealization G W e hnu).equiv (W.pro2 g) := by
  rw [← alignedRealization_pro2 G W e hnu g]
  exact ((alignedRealization G W e hnu).equiv.apply_symm_apply _).symm

/-- Replace ONLY the realization. All word- and certificate-dependent data remain
definitionally the same. -/
def alignedBranch
    (hnu : ∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g))) :
    GenAsmFlexibleBranch K B :=
  { G with realization := alignedRealization G W e hnu }

/-- Alignment does not alter the corrected source certificate. -/
def alignedBranch_certificate
    (hnu : ∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g))) :
    GenAsmFlexibleRowResidualRN FF (alignedBranch G W e hnu) := ⟨W⟩

omit G W e in
/-- The new existential branch carries a realization aligned to its actual field equivalence.
The chosen word certificate remains visible. This is not preservation of an old realization. -/
def HasSelectedAlignedFlexibleAssemblyRN
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W) : Prop :=
  ∃ G : GenAsmFlexibleBranch K B, G.degree = S.semantic.degree ∧
    ∃ cert : GenAsmFlexibleRowResidualRN FF G,
    ∃ e : ContinuousMulEquiv (GammaR G.degree (qOf K FF) G.word) (GalK K),
      (∀ g, T.tameFK (e g) = TameSpec.tameOfSpec G.degree (qOf K FF) G.word
        cert.cand.tameSpecialization g) ∧
      (∀ g, G.realization.pro2 (e g) = cert.cand.pro2 g) ∧
      (∀ g, maxProPMk 2 (GalK K) (e g) = G.realization.equiv (cert.cand.pro2 g)) ∧
      (∀ g, B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (cert.cand.pro2 g)))

omit G W e [T2Space (GalK K)] in
/-- A tame-marked existential witness can be calibrated without changing its source word,
core, unramified marking, or word certificate. Only the carried realization is replaced. -/
theorem hasSelectedAlignedFlexibleAssemblyRN_of_tame
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    {P : FieldParameters} {W : FamilyFieldBranchWitness P (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K P (B.fieldMarkedPair FF) W)
    (H : HasSelectedTameMarkedFlexibleAssemblyRN B FF T S) :
    HasSelectedAlignedFlexibleAssemblyRN B FF T S := by
  obtain ⟨G, hdegree, cert, e, ht, hnu⟩ := H
  refine ⟨alignedBranch G cert.cand e hnu, hdegree,
    alignedBranch_certificate G cert.cand e hnu, e, ht, ?_, ?_, hnu⟩
  · exact alignedRealization_pro2 G cert.cand e hnu
  · exact alignedRealization_maxPro2 G cert.cand e hnu

omit G W e in
/-- Every selected ramified-i source has a field equivalence identifying the tame quotient,
the NEW carried maximal-pro-two realization, and full unramified character. -/
theorem hasSelectedAlignedFlexibleAssemblyRN_fieldSelectionFromRange
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF)
    (RI : RamifiedIData K) :
    HasSelectedAlignedFlexibleAssemblyRN B FF T
      (selectFieldBranchFamilyFromRange B FF D RI) :=
  hasSelectedAlignedFlexibleAssemblyRN_of_tame B FF T _
    (hasSelectedTameMarkedFlexibleAssemblyRN_fieldSelectionFromRange B FF T D RI)

#print axioms alignedRealization
#print axioms alignedRealization_pro2
#print axioms alignedRealization_maxPro2
#print axioms alignedBranch
#print axioms alignedBranch_certificate
#print axioms hasSelectedAlignedFlexibleAssemblyRN_of_tame
#print axioms hasSelectedAlignedFlexibleAssemblyRN_fieldSelectionFromRange

end
end GQ2.Dyadic.Instances.FieldFamilySpliceAlignedFinal
