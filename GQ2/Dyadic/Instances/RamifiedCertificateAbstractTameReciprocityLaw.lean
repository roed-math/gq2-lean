/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueReciprocityLaw

/-!
# The abstract tame local reciprocity law

W195 packages the actual absolute-residue action into one local-reciprocity law on every
`x : K×`.  This module proves the exact abstract analogue.  The full unramified quotient of an
oriented tame image sends `rec_K(x)` to the `-v_K(x)`-th power of its distinguished geometric
Frobenius generator.

`abstractTameLocalReciprocityLaw_iff_rows` proves that this law is exactly the conjunction of
the full-inertia unit refinement and W193's geometric uniformizer row.  The decomposition
`K× = O_K× * pi^Z` again proves the reverse implication.  Consequently the field and abstract
all-elements laws alone imply `OrientedAbsoluteResidueFrobeniusCompatibility`; the earlier
unit, inertia, and coordinate-normalization premises disappear from the public consumer.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K}
  {FF : DyadicUnitFiltration K}

/-- The natural local-reciprocity law in the full abstract unramified tame quotient. -/
def AbstractTameLocalReciprocityLaw
    (T : OrientedTameQuotientK B FF) : Prop :=
  ∀ (x : (↥K)ˣ) (g : GalK K),
    toAbK K g = B.recip x →
      qMkQ (qOf K FF) (T.tameFK g) =
        qSigmaQ (qOf K FF) ^ (-dyadicValuation FF x)

/-- The full abstract reciprocity law is exactly its unit and uniformizer rows. -/
theorem abstractTameLocalReciprocityLaw_iff_rows
    (T : OrientedTameQuotientK B FF) :
    AbstractTameLocalReciprocityLaw T ↔
      TameUnitInertiaRefinement B FF T ∧
        AbstractTameUniformizerQurRow T := by
  constructor
  · intro H
    constructor
    · rw [tameUnitInertiaRefinement_iff_qMkQ_recip_unit]
      intro u g hu hg
      have h := H u g hg
      rw [dyadicValuation_eq_zero_of_norm_eq_one u hu, neg_zero, zpow_zero] at h
      exact h
    · intro g hg
      simpa [dyadicValuation_uniformizerK] using
        H (uniformizerK K FF) g hg
  · rintro ⟨Hunit, Hpi⟩ x g hg
    apply (qurQEquivZhat (qOf K FF)).injective
    change orientedTameQurCoordinateKRaw T g = _
    rw [orientedTameQurCoordinateKRaw_apply]
    rw [← orientedTameQurCoordinateKAb_toAbK, hg]
    obtain ⟨u, n, hx, hu⟩ := exists_unit_zpow_decomp K FF x
    have hval : dyadicValuation FF x = n := by
      apply dyadicValuation_eq_of_norm_eq_zpow FF x n
      rw [hx]
      simp only [Units.val_mul]
      push_cast
      rw [uniformizerK_val_zpow_coe, norm_mul, norm_zpow, hu, one_mul]
    rw [hval, hx, map_mul, map_zpow, map_zpow, qurQEquivZhat_qSigmaQ]
    rw [map_mul, map_zpow]
    have Hu := orientedTameQurCoordinateKAb_recip_unit_eq_one T Hunit u hu
    have Hpi' :=
      (abstractTameUniformizerNormalization_iff_qurRow T).mpr Hpi
    rw [Hu, Hpi', one_mul]
    rw [← Zhat.ofInt_one_zpow, ← zpow_mul]
    congr 1
    ring

/-- The actual and abstract all-elements reciprocity laws imply the signed comparison directly. -/
theorem orientedAbsoluteResidueFrobeniusCompatibility_of_reciprocityLaws
    (T : OrientedTameQuotientK B FF)
    (Habs : AbsoluteResidueLocalReciprocityLaw B FF)
    (Htame : AbstractTameLocalReciprocityLaw T) :
    OrientedAbsoluteResidueFrobeniusCompatibility T :=
  orientedAbsoluteResidueFrobeniusCompatibility_of_localReciprocityLaw
    T (abstractTameLocalReciprocityLaw_iff_rows T |>.mp Htame).1
      Habs (abstractTameLocalReciprocityLaw_iff_rows T |>.mp Htame).2

#print axioms AbstractTameLocalReciprocityLaw
#print axioms abstractTameLocalReciprocityLaw_iff_rows
#print axioms orientedAbsoluteResidueFrobeniusCompatibility_of_reciprocityLaws

end
end GQ2.Dyadic
