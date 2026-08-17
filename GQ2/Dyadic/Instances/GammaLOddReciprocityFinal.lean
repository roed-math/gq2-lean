/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbstractTameReciprocityLaw
import GQ2.Dyadic.Instances.RamifiedCertificateResidueCompatibleOrientedTame

/-!
# The odd-L endpoint from the two reciprocity laws

W195 and W196 replace all residue/tame unit and uniformizer plumbing by two natural laws on
`K×`: the actual absolute-residue action law and the abstract full-tame-quotient law.  This
module threads their signed comparison through the compatible ramified-certificate constructor.

After the two reciprocity laws, the only remaining ramified analytic input is equality of norm
value groups for the canonical anchored involution fields.  The final theorem feeds those three
arithmetic statements directly into the uniform odd-degree `L` reconstruction.  It exposes no
residue-lift, full-inertia, normalization, marked-core, or determinant premise.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K}
  {FF : DyadicUnitFiltration K}

/-- The two reciprocity laws and anchored equal norm-value groups produce the complete
compatible ramified-data packet. -/
theorem compatibleRamifiedDataAt_of_reciprocityLaws
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (T : OrientedTameQuotientK B FF)
    (Habs : AbsoluteResidueLocalReciprocityLaw B FF)
    (Htame : AbstractTameLocalReciprocityLaw T)
    (P : FieldParameters) (hq : P.qK = qOf K FF)
    (hNorm : AnchoredInvolutionEqualNormValueGroupsAt P (GalKsub K)
      (tameAtParams P hq T.tameFK)) :
    CompatibleRamifiedDataAt P (GalKsub K)
      (tameAtParams P hq T.tameFK) := by
  let C : OrientedAbsoluteResidueFrobeniusCompatibility T :=
    orientedAbsoluteResidueFrobeniusCompatibility_of_reciprocityLaws
      T Habs Htame
  letI : (GalKsub K).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _
      (finite_quotient_of_isOpen _ (isOpen_fixingSubgroup K))
  let tame : ContinuousMonoidHom (GalK K) (Tq P.qK) :=
    tameAtParams P hq T.tameFK
  have hLift : CompatibleResidueLiftAt P (GalKsub K) tame :=
    C.compatibleResidueLiftAt P hq
  have hInv : AnchoredInvolutionFieldDataAt P (GalKsub K) tame :=
    anchoredInvolutionFieldDataAt_of_equalNormValueGroups P (GalKsub K)
      (isOpen_fixingSubgroup K) tame hNorm
  exact @compatibleRamifiedDataAt_of_residuals P (GalKsub K)
    (inferInstance : DistribMulAction (GalK K) (MuN 2))
    (inferInstance : ContinuousSMul (GalK K) (MuN 2))
    (isOpen_fixingSubgroup K) inferInstance tame hLift hInv

namespace LSquare

open GQ2.Dyadic.SqCore

variable [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2]

/-- Uniform odd-degree reconstruction from the two reciprocity laws and anchored equal norms. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_reciprocityLaws
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (Habs : AbsoluteResidueLocalReciprocityLaw B FF)
    (Htame : AbstractTameLocalReciprocityLaw T)
    (hNorm : AnchoredInvolutionEqualNormValueGroupsAt D.params (GalKsub K)
      (tameAtParams D.params D.qK_eq_qOf T.tameFK)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_compatible B FF T D hdeg
    (compatibleRamifiedDataAt_of_reciprocityLaws T Habs Htame
      D.params D.qK_eq_qOf hNorm)

end LSquare

#print axioms compatibleRamifiedDataAt_of_reciprocityLaws
#print axioms LSquare.gammaR_lSq_equiv_galK_oddDegree_of_reciprocityLaws

end
end GQ2.Dyadic
