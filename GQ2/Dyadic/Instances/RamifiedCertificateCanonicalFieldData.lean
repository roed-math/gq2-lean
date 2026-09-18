/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateCanonicalResidueLift
import GQ2.Dyadic.Instances.RamifiedCertificateInertiaFixedNorm
import GQ2.Dyadic.Instances.RamifiedCertificateTameInertiaExact
import GQ2.Dyadic.Instances.AnchoredInvolutionRelativeNorm

/-!
# Canonical compatible field data over arbitrary finite dyadic bases

The actual/full tame inertia comparison and odd cyclotomic unramifiedness give the prescribed
anchored tame-inertia fields their relative ramification index one. This construction uses only
the existing reciprocity and oriented tame quotient bundles; it does not assume a signed
Frobenius comparison or any additional relative norm-reciprocity law.

The relative involution argument then gives the norm-value matching field package in every
degree. Combining it with the canonical residue lift produces the full compatibility-aware
ramified packet. Its only additional axiom dependency is the existing local Tate-duality
baseline used by the certificate constructor.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

private instance compact_galK : CompactSpace (GalK K) :=
  isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_of_isOpen _ (isOpen_fixingSubgroup K)).isCompact
private instance t2_galK : T2Space (GalK K) := inferInstanceAs (T2Space ↥(K.fixingSubgroup))
private instance td_galK : TotallyDisconnectedSpace (GalK K) :=
  inferInstanceAs (TotallyDisconnectedSpace ↥(K.fixingSubgroup))

omit [FiniteDimensional ℚ_[2] K] in
private theorem actualInertia_tameAtParams {q : ℕ}
    (tame : ContinuousMonoidHom (GalK K) (Tq q))
    (params : FieldParameters) (params_qK : params.qK = q)
    (hI : ∀ g : GalK K, subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup →
      tame g ∈ inertiaPartQ q) :
    ∀ g : GalK K, subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup →
      tameAtParams params params_qK tame g ∈ inertiaPartQ params.qK := by
  subst q
  exact hI

/-- Every compatible canonical tame-inertia fixed field is relatively unramified, over any
finite dyadic base, with no relative reciprocity premise. -/
theorem anchoredTameInertiaRelativeUnramifiedDataAt_of_norm_reciprocity
    (T : OrientedTameQuotientK B FF) (params : FieldParameters)
    (params_qK : params.qK = qOf K FF) :
    AnchoredTameInertiaRelativeUnramifiedDataAt params K FF
      (tameAtParams params params_qK T.tameFK) :=
  anchoredTameInertiaRelativeUnramifiedDataAt_of_actualInertia params K FF
    (tameAtParams params params_qK T.tameFK)
    (actualInertia_tameAtParams T.tameFK params params_qK
      (actualInertia_mem_fullTameInertia T))

/-- Compatible anchored involution fields have the same value groups in every finite dyadic
degree. The ramification argument is relative to the base, so no absolute odd-degree condition
is required. -/
theorem anchoredInvolutionEqualNormValueGroupsAt_of_norm_reciprocity
    (T : OrientedTameQuotientK B FF) (params : FieldParameters)
    (params_qK : params.qK = qOf K FF) :
    AnchoredInvolutionEqualNormValueGroupsAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) :=
  anchoredInvolutionEqualNormValueGroupsAt_of_prescribedTameUnramified_general
    params K FF (tameAtParams params params_qK T.tameFK)
    (tameAtParams_surjective params params_qK T.tameFK T.tameFK_surjective)
    (anchoredTameInertiaRelativeUnramifiedDataAt_of_norm_reciprocity T params params_qK)

/-- The canonical involution field package for every compatible ramified action, with its
analytic norm-value clause discharged and no extra field-arithmetic premise. -/
theorem anchoredInvolutionFieldDataAt_of_norm_reciprocity
    (T : OrientedTameQuotientK B FF) (params : FieldParameters)
    (params_qK : params.qK = qOf K FF) :
    AnchoredInvolutionFieldDataAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) :=
  anchoredInvolutionFieldDataAt_of_equalNormValueGroups params (GalKsub K)
    (isOpen_fixingSubgroup K) (tameAtParams params params_qK T.tameFK)
    (anchoredInvolutionEqualNormValueGroupsAt_of_norm_reciprocity T params params_qK)

/-- The shared compatibility-aware ramified field packet follows from the existing field
bundles in every degree. The caller's `MuN 2` action is retained explicitly; no signed full
Frobenius law, tame unit law, or relative norm-reciprocity premise is added. -/
theorem compatibleRamifiedDataAt_of_norm_reciprocity
    [instDMA : DistribMulAction (GalK K) (MuN 2)]
    [instCS : ContinuousSMul (GalK K) (MuN 2)]
    (T : OrientedTameQuotientK B FF) (params : FieldParameters)
    (params_qK : params.qK = qOf K FF) :
    CompatibleRamifiedDataAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) := by
  letI : (GalKsub K).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _
      (finite_quotient_of_isOpen _ (isOpen_fixingSubgroup K))
  exact @compatibleRamifiedDataAt_of_residuals params (GalKsub K) instDMA instCS
    (isOpen_fixingSubgroup K) inferInstance (tameAtParams params params_qK T.tameFK)
    (compatibleResidueLiftAt_of_norm_reciprocity T params params_qK)
    (anchoredInvolutionFieldDataAt_of_norm_reciprocity T params params_qK)

#print axioms anchoredTameInertiaRelativeUnramifiedDataAt_of_norm_reciprocity
#print axioms anchoredInvolutionEqualNormValueGroupsAt_of_norm_reciprocity
#print axioms anchoredInvolutionFieldDataAt_of_norm_reciprocity
#print axioms compatibleRamifiedDataAt_of_norm_reciprocity

end
end GQ2.Dyadic
