/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateZhatProTwoAmbiguity

/-!
# Finite rows for the missing prime-to-two Frobenius coordinate

W191 proves that the maximal pro-`2` image does not determine an element of `Zhat`.  This module
identifies exactly what must be added: equality in every finite quotient of `Zhat` that is not a
`2`-group.  The pro-`2` kernel handles the complementary finite quotients by definition, and the
intersection of all open normal subgroups is trivial.

For the abstract geometric uniformizer coordinate, AX4 already supplies the maximal pro-`2`
equality.  Consequently `AbstractTameUniformizerNormalization` is equivalent to the remaining
non-pro-`2` finite rows.  The explicit W191 pair fails one such row, so this is a genuine residual
rather than a vacuous reformulation.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

/-- Agreement in every finite quotient of `Zhat` which is not a `2`-group. -/
def ZhatNonProTwoRows (gamma delta : Zhat) : Prop :=
  ∀ U : OpenNormalSubgroup Zhat,
    ¬ IsPGroup 2 (Zhat ⧸ U.toSubgroup) →
      QuotientGroup.mk' U.toSubgroup gamma =
        QuotientGroup.mk' U.toSubgroup delta

/-- A `Zhat` equality is exactly its pro-`2` equality plus all non-pro-`2` finite rows. -/
theorem zhat_eq_iff_maxProTwo_and_nonProTwoRows
    (gamma delta : Zhat) :
    gamma = delta ↔
      maxProPMk 2 Zhat gamma = maxProPMk 2 Zhat delta ∧
      ZhatNonProTwoRows gamma delta := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩
  · rintro ⟨hpro, hrows⟩
    have hdiv : gamma / delta = 1 :=
      eq_one_of_forall_mem_openNormalSubgroup fun U => by
        by_cases hP : IsPGroup 2 (Zhat ⧸ U.toSubgroup)
        · exact proPKernel_le U hP
            (QuotientGroup.eq_iff_div_mem.mp hpro)
        · exact QuotientGroup.eq_iff_div_mem.mp (hrows U hP)
    exact div_eq_one.mp hdiv

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2]
    (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- The exact non-pro-`2` finite rows missing from the abstract uniformizer normalization. -/
def AbstractTameUniformizerNonProTwoRows
    (T : OrientedTameQuotientK B FF) : Prop :=
  ZhatNonProTwoRows
    (orientedTameQurCoordinateKAb T
      (B.recip (uniformizerK K FF)))
    (Zhat.ofInt (-1))

/-- Since AX4 supplies the pro-`2` row, full normalization is exactly the remaining rows. -/
theorem abstractTameUniformizerNormalization_iff_nonProTwoRows
    (T : OrientedTameQuotientK B FF) :
    AbstractTameUniformizerNormalization T ↔
      AbstractTameUniformizerNonProTwoRows T := by
  rw [AbstractTameUniformizerNormalization,
    zhat_eq_iff_maxProTwo_and_nonProTwoRows]
  exact and_iff_right
    (maxProPMk_orientedTameQurCoordinateKAb_recip_uniformizer T |>.trans
      maxProPMk_ofInt_neg_one.symm)

/-- The two explicit W191 lifts cannot agree on every non-pro-`2` finite row. -/
theorem not_zhatNonProTwoRows_omega2_inv :
    ¬ ZhatNonProTwoRows omega2⁻¹ (Zhat.ofInt (-1)) := by
  intro hrows
  exact omega2_inv_ne_ofInt_neg_one
    ((zhat_eq_iff_maxProTwo_and_nonProTwoRows _ _).mpr
      ⟨maxProPMk_omega2_inv.trans maxProPMk_ofInt_neg_one.symm,
        hrows⟩)

/-- Some finite non-pro-`2` quotient explicitly separates the two W191 lifts. -/
theorem exists_nonProTwo_row_distinguishing_omega2_inv :
    ∃ U : OpenNormalSubgroup Zhat,
      ¬ IsPGroup 2 (Zhat ⧸ U.toSubgroup) ∧
      QuotientGroup.mk' U.toSubgroup omega2⁻¹ ≠
        QuotientGroup.mk' U.toSubgroup (Zhat.ofInt (-1)) := by
  simpa [ZhatNonProTwoRows] using
    not_zhatNonProTwoRows_omega2_inv

#print axioms ZhatNonProTwoRows
#print axioms zhat_eq_iff_maxProTwo_and_nonProTwoRows
#print axioms AbstractTameUniformizerNonProTwoRows
#print axioms abstractTameUniformizerNormalization_iff_nonProTwoRows
#print axioms not_zhatNonProTwoRows_omega2_inv
#print axioms exists_nonProTwo_row_distinguishing_omega2_inv

end
end GQ2.Dyadic
