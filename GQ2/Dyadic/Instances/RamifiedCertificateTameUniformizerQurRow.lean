/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateZhatFiniteRows

/-!
# The geometric uniformizer row in the abstract tame quotient

W192 expresses the missing abstract uniformizer normalization as non-pro-`2` finite rows in
`Zhat`.  This module translates the same residual back to its natural source.  For every Galois
lift of the reciprocity uniformizer, its image in the full unramified tame quotient `QurQ` must be
the inverse of the distinguished generator `qSigmaQ`.

The condition is independent of the chosen Galois lift because the `QurQ` coordinate descends
through abelianization.  The normalized equivalence `qurQEquivZhat` identifies this quotient row
with `Zhat.ofInt (-1)`, so it is equivalent both to `AbstractTameUniformizerNormalization` and to
W192's finite non-pro-`2` rows.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K}
  {FF : DyadicUnitFiltration K}

/-- Every lift of the reciprocity uniformizer is geometric Frobenius in `QurQ`. -/
def AbstractTameUniformizerQurRow
    (T : OrientedTameQuotientK B FF) : Prop :=
  ∀ g : GalK K,
    toAbK K g = B.recip (uniformizerK K FF) →
      qMkQ (qOf K FF) (T.tameFK g) =
        (qSigmaQ (qOf K FF))⁻¹

/-- The natural tame quotient row is exactly the full abstract `Zhat` normalization. -/
theorem abstractTameUniformizerNormalization_iff_qurRow
    (T : OrientedTameQuotientK B FF) :
    AbstractTameUniformizerNormalization T ↔
      AbstractTameUniformizerQurRow T := by
  constructor
  · intro hnorm g hg
    apply (qurQEquivZhat (qOf K FF)).injective
    rw [map_inv, qurQEquivZhat_qSigmaQ]
    change orientedTameQurCoordinateKAb T (toAbK K g) = _
    rw [hg, hnorm]
    rw [← Zhat.ofInt_one_zpow]
    rfl
  · intro hrow
    rw [AbstractTameUniformizerNormalization]
    obtain ⟨g, hg⟩ := surjective_toAbK K
      (B.recip (uniformizerK K FF))
    rw [← hg, orientedTameQurCoordinateKAb_toAbK, hrow g hg]
    rw [map_inv, qurQEquivZhat_qSigmaQ]
    simpa using Zhat.ofInt_one_zpow (-1)

/-- The quotient row and W192's non-pro-`2` finite rows are the same residual. -/
theorem abstractTameUniformizerQurRow_iff_nonProTwoRows
    (T : OrientedTameQuotientK B FF) :
    AbstractTameUniformizerQurRow T ↔
      AbstractTameUniformizerNonProTwoRows T :=
  (abstractTameUniformizerNormalization_iff_qurRow T).symm.trans
    (abstractTameUniformizerNormalization_iff_nonProTwoRows T)

#print axioms AbstractTameUniformizerQurRow
#print axioms abstractTameUniformizerNormalization_iff_qurRow
#print axioms abstractTameUniformizerQurRow_iff_nonProTwoRows

end
end GQ2.Dyadic
