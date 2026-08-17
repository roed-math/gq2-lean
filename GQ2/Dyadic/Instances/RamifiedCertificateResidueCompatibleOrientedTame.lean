/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueAction
import GQ2.Dyadic.Instances.AnchoredInvolutionFieldNorm

/-!
# Residue-compatible oriented tame quotients

An `OrientedTameQuotientK` contains the abstract maximal normal pro-`2` subgroup `W`, an
abstract quotient equivalence with `Tq`, and the orientation of the `2`-primary unramified
coordinate.  These data do not compare the preimage of `inertiaPartQ` with the kernel of the
canonical absolute residue action: `qMkQ` identifies the former group-theoretically, while the
orientation clauses only control `nuTq` on reciprocity elements.  In particular, neither the
existing unit clause nor density of reciprocity supplies the missing prime-to-`2` residue-field
comparison.

`AbsoluteResidueCompatibleOrientedTameQuotientK` is the minimal enhancement: it adds exactly
the assertion that full tame inertia lies in `absoluteInertiaSubgroup`.  The field is deliberately
stated using `OrientedFullTameInertiaLiesInAbsoluteInertiaAt`, so it can be supplied directly by a
future comparison between the canonical tame quotient and the valuation-theoretic residue
action.

The remaining results are endpoint adapters.  They turn the enhanced quotient into
`CompatibleResidueLiftAt`, combine it with anchored involution-field data to produce
`CompatibleRamifiedDataAt`, and feed that packet into the compatible odd-degree gamma theorem.
The last adapter retains only the already-isolated equality of norm-value groups as an analytic
premise.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- An oriented tame quotient equipped with the exact comparison between its full inertia
preimage and the kernel of the canonical absolute residue action. -/
structure AbsoluteResidueCompatibleOrientedTameQuotientK
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    extends OrientedTameQuotientK B FF where
  fullInertia_le_absoluteInertia :
    OrientedFullTameInertiaLiesInAbsoluteInertiaAt toOrientedTameQuotientK

namespace AbsoluteResidueCompatibleOrientedTameQuotientK

/-- Package an oriented tame quotient once its canonical absolute-inertia comparison is known. -/
def ofOriented (T : OrientedTameQuotientK B FF)
    (hI : OrientedFullTameInertiaLiesInAbsoluteInertiaAt T) :
    AbsoluteResidueCompatibleOrientedTameQuotientK B FF :=
  { toOrientedTameQuotientK := T
    fullInertia_le_absoluteInertia := hI }

variable (T : AbsoluteResidueCompatibleOrientedTameQuotientK B FF)

/-- A residue-compatible oriented tame quotient supplies the compatible residue-lift packet at
every equality-transported parameter set. -/
theorem compatibleResidueLiftAt (P : FieldParameters)
    (hq : P.qK = qOf K FF) :
    CompatibleResidueLiftAt P (GalKsub K)
      (tameAtParams P hq T.toOrientedTameQuotientK.tameFK) :=
  compatibleResidueLiftAt_of_orientedFullTameInertiaInAbsoluteInertia
    T.toOrientedTameQuotientK P hq T.fullInertia_le_absoluteInertia

/-- Combine the canonical residue comparison with anchored involution-field data. -/
theorem compatibleRamifiedDataAt [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2]
    (P : FieldParameters) (hq : P.qK = qOf K FF)
    (hInv : AnchoredInvolutionFieldDataAt P (GalKsub K)
      (tameAtParams P hq T.toOrientedTameQuotientK.tameFK)) :
    CompatibleRamifiedDataAt P (GalKsub K)
      (tameAtParams P hq T.toOrientedTameQuotientK.tameFK) := by
  letI : (GalKsub K).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _
      (finite_quotient_of_isOpen _ (isOpen_fixingSubgroup K))
  let tame : ContinuousMonoidHom (GalK K) (Tq P.qK) :=
    tameAtParams P hq T.toOrientedTameQuotientK.tameFK
  have hLift : CompatibleResidueLiftAt P (GalKsub K) tame :=
    T.compatibleResidueLiftAt P hq
  exact @compatibleRamifiedDataAt_of_residuals P (GalKsub K)
    (inferInstance : DistribMulAction (GalK K) (MuN 2))
    (inferInstance : ContinuousSMul (GalK K) (MuN 2))
    (isOpen_fixingSubgroup K) inferInstance tame hLift hInv

/-- Equality of norm-value groups is the sole remaining field-side analytic premise after the
canonical residue comparison has been packaged. -/
theorem compatibleRamifiedDataAt_of_equalNormValueGroups
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (P : FieldParameters) (hq : P.qK = qOf K FF)
    (hNorm : AnchoredInvolutionEqualNormValueGroupsAt P (GalKsub K)
      (tameAtParams P hq T.toOrientedTameQuotientK.tameFK)) :
    CompatibleRamifiedDataAt P (GalKsub K)
      (tameAtParams P hq T.toOrientedTameQuotientK.tameFK) :=
  T.compatibleRamifiedDataAt P hq
    (anchoredInvolutionFieldDataAt_of_equalNormValueGroups P (GalKsub K)
      (isOpen_fixingSubgroup K)
      (tameAtParams P hq T.toOrientedTameQuotientK.tameFK) hNorm)

end AbsoluteResidueCompatibleOrientedTameQuotientK

namespace LSquare

open GQ2.Dyadic.SqCore

variable [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2]

/-- The compatible odd-degree gamma endpoint from a residue-compatible oriented tame quotient
and the remaining anchored involution-field packet. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_absoluteResidueCompatible
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : AbsoluteResidueCompatibleOrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hInv : AnchoredInvolutionFieldDataAt D.params (GalKsub K)
      (tameAtParams D.params D.qK_eq_qOf T.toOrientedTameQuotientK.tameFK)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_compatible B FF T.toOrientedTameQuotientK D hdeg
    (T.compatibleRamifiedDataAt D.params D.qK_eq_qOf hInv)

/-- The compatible odd-degree gamma endpoint from the enhanced tame quotient and equality of
norm-value groups at every compatible anchored involution field. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_absoluteResidueCompatible_of_equalNormValueGroups
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : AbsoluteResidueCompatibleOrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hNorm : AnchoredInvolutionEqualNormValueGroupsAt D.params (GalKsub K)
      (tameAtParams D.params D.qK_eq_qOf T.toOrientedTameQuotientK.tameFK)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_compatible B FF T.toOrientedTameQuotientK D hdeg
    (T.compatibleRamifiedDataAt_of_equalNormValueGroups D.params D.qK_eq_qOf hNorm)

end LSquare

#print axioms AbsoluteResidueCompatibleOrientedTameQuotientK
#print axioms AbsoluteResidueCompatibleOrientedTameQuotientK.ofOriented
#print axioms AbsoluteResidueCompatibleOrientedTameQuotientK.compatibleResidueLiftAt
#print axioms AbsoluteResidueCompatibleOrientedTameQuotientK.compatibleRamifiedDataAt
#print axioms
  AbsoluteResidueCompatibleOrientedTameQuotientK.compatibleRamifiedDataAt_of_equalNormValueGroups
#print axioms LSquare.gammaR_lSq_equiv_galK_oddDegree_of_absoluteResidueCompatible
#print axioms
  LSquare.gammaR_lSq_equiv_galK_oddDegree_of_absoluteResidueCompatible_of_equalNormValueGroups

end
end GQ2.Dyadic
