/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateRelativeFrobeniusRows
import GQ2.Dyadic.Instances.AnchoredTameInertiaPrescribedUnramified

/-!
# Splitting the relative Frobenius rows into units and a uniformizer

The W188 comparison consists of a row on every norm-one unit and one row on a chosen
uniformizer.  Under `TameUnitInertiaRefinement`, the abstract full tame coordinate already kills
all reciprocity units.  This module therefore identifies the unit row exactly with the field-side
statement that every reciprocity lift of a norm-one unit lies in canonical absolute inertia.

The full signed Frobenius comparison is then equivalent to two independent residuals:

* `AbsoluteResidueUnitInertia`, the actual residue-action unit theorem;
* `RelativeFrobeniusUniformizerRow`, the signed normalization at one uniformizer.

This separates the unit/inertia compatibility needed by the anchored norm lane from the
geometric-versus-arithmetic Frobenius normalization.  Neither residual is inferred from the
maximal pro-`2` coordinate supplied by the current marked-reciprocity interface.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K}
  {FF : DyadicUnitFiltration K}

/-- Actual absolute inertia contains every reciprocity lift of a norm-one unit. -/
def AbsoluteResidueUnitInertia (B : MarkedRecip R K) : Prop :=
  ∀ (u : (↥K)ˣ) (g : GalK K), ‖((u : ↥K) : ℚ̄₂)‖ = 1 →
    toAbK K g = B.recip u → g ∈ absoluteInertiaK (K := K)

/-- The absolute residue coordinate kills every norm-one reciprocity unit. -/
def AbsoluteResidueUnitReciprocity (B : MarkedRecip R K) : Prop :=
  ∀ u : (↥K)ˣ, ‖((u : ↥K) : ℚ̄₂)‖ = 1 →
    absoluteResidueCoordinateKAb (K := K) (B.recip u) = 1

/-- The remaining signed row at one chosen filtration uniformizer. -/
def RelativeFrobeniusUniformizerRow
    (T : OrientedTameQuotientK B FF) : Prop :=
  absoluteResidueCoordinateKAb (K := K)
      (B.recip (uniformizerK K FF)) =
    (orientedTameQurCoordinateKAb T
      (B.recip (uniformizerK K FF))) ^ (-(FF.f : ℤ))

theorem absoluteResidueUnitInertia_iff_reciprocity :
    AbsoluteResidueUnitInertia B ↔ AbsoluteResidueUnitReciprocity B := by
  constructor
  · intro H u hu
    obtain ⟨g, hg⟩ := surjective_toAbK K (B.recip u)
    rw [← hg, absoluteResidueCoordinateKAb_toAbK]
    have hmem : g ∈
        (absoluteResidueCoordinateK (K := K)).toMonoidHom.ker := by
      rw [absoluteResidueCoordinateK_ker]
      exact H u g hu hg
    exact hmem
  · intro H u g hu hg
    rw [← absoluteResidueCoordinateK_ker]
    change absoluteResidueCoordinateK (K := K) g = 1
    rw [← absoluteResidueCoordinateKAb_toAbK, hg]
    exact H u hu

theorem orientedTameQurCoordinateKAb_recip_unit_eq_one
    (T : OrientedTameQuotientK B FF)
    (Hunit : TameUnitInertiaRefinement B FF T)
    (u : (↥K)ˣ) (hu : ‖((u : ↥K) : ℚ̄₂)‖ = 1) :
    orientedTameQurCoordinateKAb T (B.recip u) = 1 := by
  obtain ⟨g, hg⟩ := surjective_toAbK K (B.recip u)
  rw [← hg, orientedTameQurCoordinateKAb_toAbK]
  have hq := (tameUnitInertiaRefinement_iff_qMkQ_recip_unit B FF T).mp
    Hunit u g hu hg
  rw [hq, map_one]

theorem relativeFrobeniusReciprocityRows_iff_unit_uniformizer
    (T : OrientedTameQuotientK B FF)
    (Hunit : TameUnitInertiaRefinement B FF T) :
    RelativeFrobeniusReciprocityRows T ↔
      AbsoluteResidueUnitReciprocity B ∧
        RelativeFrobeniusUniformizerRow T := by
  constructor
  · intro H
    refine ⟨?_, H.2⟩
    intro u hu
    rw [H.1 u hu, orientedTameQurCoordinateKAb_recip_unit_eq_one T Hunit u hu,
      one_zpow]
  · rintro ⟨Hu, Hpi⟩
    refine ⟨?_, Hpi⟩
    intro u hu
    rw [Hu u hu, orientedTameQurCoordinateKAb_recip_unit_eq_one T Hunit u hu,
      one_zpow]

theorem orientedAbsoluteResidueFrobeniusCompatibility_iff_unit_uniformizer
    (T : OrientedTameQuotientK B FF)
    (Hunit : TameUnitInertiaRefinement B FF T) :
    OrientedAbsoluteResidueFrobeniusCompatibility T ↔
      AbsoluteResidueUnitInertia B ∧
        RelativeFrobeniusUniformizerRow T :=
  (orientedAbsoluteResidueFrobeniusCompatibility_iff_rows T).trans <|
    (relativeFrobeniusReciprocityRows_iff_unit_uniformizer T Hunit).trans <|
      and_congr absoluteResidueUnitInertia_iff_reciprocity.symm Iff.rfl

#print axioms AbsoluteResidueUnitInertia
#print axioms AbsoluteResidueUnitReciprocity
#print axioms RelativeFrobeniusUniformizerRow
#print axioms absoluteResidueUnitInertia_iff_reciprocity
#print axioms orientedTameQurCoordinateKAb_recip_unit_eq_one
#print axioms relativeFrobeniusReciprocityRows_iff_unit_uniformizer
#print axioms orientedAbsoluteResidueFrobeniusCompatibility_iff_unit_uniformizer

end
end GQ2.Dyadic
