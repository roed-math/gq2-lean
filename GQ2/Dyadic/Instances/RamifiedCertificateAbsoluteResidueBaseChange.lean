/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLOddReciprocityFinal
import GQ2.Dyadic.Instances.GammaLNuKummerIdentification

/-!
# Base change for the absolute-residue reciprocity law

The actual absolute-residue law in the odd reconstruction was previously stated separately at
every finite dyadic field `K`.  Norm functoriality in `MarkedRecip` shows that this is redundant.
It is enough to know the corresponding law once over `Q_2`: the absolute Galois element underlying
a lift from `G_K` represents reciprocity of `N_{K/Q_2}(x)`, and

`v_2(N_{K/Q_2}(x)) = f_K * v_K(x)`.

This module proves that valuation identity without a Galois hypothesis and transports the base
law to every finite `K`.  The final odd-degree wrapper consequently retains one base-field law,
the abstract tame law, and the anchored norm-value statement.  It does not add a nilpotency class,
presentation family, or handle-count hypothesis.

The base law is deliberately not inferred from the present `LocalReciprocity` structure.  Its
pro-`2` normalization does not determine the odd-primary components of the full unramified
`Zhat` coordinate; the finite-quotient ambiguity is recorded elsewhere in the campaign.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The absolute-residue normalization of local reciprocity, stated once over `Q_2`. -/
def AbsoluteResidueBaseReciprocityLaw (R : LocalReciprocity) : Prop :=
  ∀ (x : ℚ_[2]ˣ) (g : AbsGalQ2),
    toAb g = R.recip x →
      absoluteResidueAlgAction g = absoluteResidueFrobenius ^ v2 x

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-- Norm valuation is residue degree times the filtration valuation.  No normality or Galois
hypothesis on `K/Q_2` is needed. -/
theorem v2_normUnitsK_eq_f_mul_dyadicValuation
    (FF : DyadicUnitFiltration K) (x : (↥K)ˣ) :
    v2 (normUnitsK K x) = (FF.f : ℤ) * dyadicValuation FF x := by
  have hkey := LSquare.NuKummer.e_mul_val_norm_of_finrank FF
    (x : ↥K) (Units.ne_zero x) (dyadicValuation FF x)
      (norm_eq_zpow_dyadicValuation FF x)
  have hef : (Module.finrank ℚ_[2] K : ℤ) = (FF.e : ℤ) * (FF.f : ℤ) := by
    rw [SpectralLocalField.field_finrank_eq_e_mul_f (K := K) (FF := FF)]
    push_cast
    rfl
  have hene : (FF.e : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp FF.he_pos)
  have hv2 : v2 (normUnitsK K x) =
      (Algebra.norm ℚ_[2] ((x : ↥K))).valuation := rfl
  rw [hv2]
  refine mul_left_cancel₀ hene ?_
  rw [hkey, hef]
  ring

/-- The single base-field absolute-residue law transports to every finite dyadic field through
the norm-compatibility clause of its marked reciprocity bundle. -/
theorem absoluteResidueLocalReciprocityLaw_of_base
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (Hbase : AbsoluteResidueBaseReciprocityLaw R) :
    AbsoluteResidueLocalReciprocityLaw B FF := by
  intro x g hg
  have hab : toAb (subtypeAnc (GalKsub K) g) =
      R.recip (normUnitsK K x) := by
    calc
      toAb (subtypeAnc (GalKsub K) g) = inclAbK K (toAbK K g) :=
        (inclAbK_toAbK K g).symm
      _ = inclAbK K (B.recip x) := congrArg (inclAbK K) hg
      _ = R.recip (normUnitsK K x) := B.norm_compat x
  rw [Hbase (normUnitsK K x) (subtypeAnc (GalKsub K) g) hab,
    v2_normUnitsK_eq_f_mul_dyadicValuation FF x]

/-- Uniform odd-degree reconstruction with the actual residue law paid only once over `Q_2`. -/
theorem LSquare.gammaR_lSq_equiv_galK_oddDegree_of_baseReciprocity
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2]
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (Hbase : AbsoluteResidueBaseReciprocityLaw R)
    (Htame : AbstractTameLocalReciprocityLaw T)
    (hNorm : AnchoredInvolutionEqualNormValueGroupsAt D.params (GalKsub K)
      (tameAtParams D.params D.qK_eq_qOf T.tameFK)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_reciprocityLaws B FF T D hdeg
    (absoluteResidueLocalReciprocityLaw_of_base B FF Hbase) Htame hNorm

#print axioms AbsoluteResidueBaseReciprocityLaw
#print axioms v2_normUnitsK_eq_f_mul_dyadicValuation
#print axioms absoluteResidueLocalReciprocityLaw_of_base
#print axioms LSquare.gammaR_lSq_equiv_galK_oddDegree_of_baseReciprocity

end
end GQ2.Dyadic
