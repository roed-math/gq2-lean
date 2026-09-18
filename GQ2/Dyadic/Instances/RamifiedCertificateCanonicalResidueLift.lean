/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateTameInertiaContainment

/-!
# Canonical compatible residue lifts from the existing field bundles

The full tame-inertia containment needed by the general residue-lift construction now follows
from finite-layer norm reciprocity. This producer introduces no Frobenius normalization or
additional arithmetic compatibility premise, and applies to every finite dyadic field.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The general compatible residue-lift packet is determined by the existing reciprocity and
oriented tame quotient bundles; no signed full residue law is assumed. -/
theorem compatibleResidueLiftAt_of_norm_reciprocity
    (T : OrientedTameQuotientK B FF) (params : FieldParameters)
    (params_qK : params.qK = qOf K FF) :
    CompatibleResidueLiftAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) :=
  compatibleResidueLiftAt_of_orientedFullTameInertiaInAbsoluteInertia T params params_qK
    (orientedFullTameInertiaLiesInAbsoluteInertiaAt_of_norm_reciprocity T)

#print axioms compatibleResidueLiftAt_of_norm_reciprocity

end
end GQ2.Dyadic
