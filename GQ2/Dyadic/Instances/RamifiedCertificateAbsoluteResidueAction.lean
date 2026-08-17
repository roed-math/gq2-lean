/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateResidueQurCompatibility
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# The canonical absolute residue action and full tame inertia

`RamifiedCertificateResidueQurCompatibility` isolates the missing field statement as
factorization of the odd-root action through the full unramified quotient `QurQ`.  This module
gives that statement a standard valuation-theoretic form.

The norm valuation on `AlgebraicClosure ℚ_[2]` defines the valuation subring
`absoluteNormInteger`.  Every absolute Galois automorphism preserves it, so Mathlib's
`ValuationSubring.decompositionSubgroup` and residue-field action give a canonical homomorphism

`absoluteResidueAction : Gal(ℚ̄₂/ℚ₂) →* Aut(k_ℚ̄₂)`.

Its kernel `absoluteInertiaSubgroup` is exactly the repository's spectral predicate
`IsResidueTrivial ⊥`: equality after reduction is equivalent to the norm of the difference
being less than one.  Consequently the conventional field statement

`preimage(full tame inertia) ≤ absoluteInertiaSubgroup`

is equivalent to `OddRootActionFactorsThroughQurAt`.  The equivalence is stable under the
`tameAtParams` equality transport and supplies `CompatibleResidueLiftAt`.

The present `OrientedTameQuotientK` interface does not prove this last inclusion.  Its `W` is an
abstract maximal normal pro-`2` subgroup and its `equiv : GalK/W ≃ Tq`; neither field identifies
`W`, or the preimage of `inertiaPartQ`, with the kernel of the canonical residue action.  Thus
`OrientedFullTameInertiaLiesInAbsoluteInertiaAt` is the narrow standard field premise still
required from the tame-ramification construction.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open scoped NNReal Pointwise

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The canonical absolute residue action -/

/-- The norm valuation subring of the algebraic closure of `ℚ₂`. -/
abbrev absoluteNormInteger : ValuationSubring ℚ̄₂ :=
  (NormedField.valuation (K := ℚ̄₂)).valuationSubring

/-- Every absolute Galois automorphism preserves the norm valuation subring. -/
theorem absGal_mem_absoluteNormInteger_decomposition (g : Kummer.GaloisGroup ℚ_[2]) :
    g ∈ absoluteNormInteger.decompositionSubgroup ℚ_[2] := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  change ‖g⁻¹ • x‖₊ ≤ 1 ↔ ‖x‖₊ ≤ 1
  rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simp only [NNReal.coe_one, coe_nnnorm, norm_galois]

/-- The absolute Galois group lifted to the decomposition subgroup of the norm valuation
subring. -/
def absoluteDecomposition :
    Kummer.GaloisGroup ℚ_[2] →* absoluteNormInteger.decompositionSubgroup ℚ_[2] where
  toFun g := ⟨g, absGal_mem_absoluteNormInteger_decomposition g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical action of the absolute Galois group on the residue field of the norm
valuation subring of `ℚ̄₂`. -/
def absoluteResidueAction :
    Kummer.GaloisGroup ℚ_[2] →* RingAut (IsLocalRing.ResidueField absoluteNormInteger) :=
  (MulSemiringAction.toRingAut
    (absoluteNormInteger.decompositionSubgroup ℚ_[2])
    (IsLocalRing.ResidueField absoluteNormInteger)).comp absoluteDecomposition

/-- The actual absolute inertia subgroup: the kernel of the canonical absolute residue
action. -/
abbrev absoluteInertiaSubgroup : Subgroup (Kummer.GaloisGroup ℚ_[2]) :=
  absoluteResidueAction.ker

/-- The canonical residue action evaluated on the reduction of an integral element. -/
theorem absoluteResidueAction_residue (g : Kummer.GaloisGroup ℚ_[2])
    (x : absoluteNormInteger) :
    absoluteResidueAction g (IsLocalRing.residue absoluteNormInteger x) =
      IsLocalRing.residue absoluteNormInteger (absoluteDecomposition g • x) := by
  exact (IsLocalRing.ResidueField.residue_smul
    (absoluteNormInteger.decompositionSubgroup ℚ_[2]) (absoluteDecomposition g) x).symm

/-- An integral algebraic `2`-adic number reduces to zero exactly when its norm is less than
one. -/
theorem absoluteResidue_zero_iff_norm_lt_one (x : absoluteNormInteger) :
    IsLocalRing.residue absoluteNormInteger x = 0 ↔ ‖(x : ℚ̄₂)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change ‖(x : ℚ̄₂)‖₊ < 1 ↔ ‖(x : ℚ̄₂)‖ < 1
  exact_mod_cast Iff.rfl

/-- Membership in the canonical absolute inertia subgroup is exactly the repository's
spectral absolute-residue-triviality predicate. -/
theorem mem_absoluteInertiaSubgroup_iff_isResidueTrivial_bot
    (g : Kummer.GaloisGroup ℚ_[2]) :
    g ∈ absoluteInertiaSubgroup ↔
      IsResidueTrivial (⊥ : Subgroup AbsGalQ2) g := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg x _ hx
    have hxA : x ∈ absoluteNormInteger := by
      change ‖x‖₊ ≤ 1
      exact_mod_cast hx
    let xA : absoluteNormInteger := ⟨x, hxA⟩
    have hres : IsLocalRing.residue absoluteNormInteger (absoluteDecomposition g • xA) =
        IsLocalRing.residue absoluteNormInteger xA := by
      rw [← absoluteResidueAction_residue, hg]
      rfl
    have hz : IsLocalRing.residue absoluteNormInteger
        (absoluteDecomposition g • xA - xA) = 0 := by
      rw [map_sub, hres, sub_self]
    have hlt := (absoluteResidue_zero_iff_norm_lt_one _).mp hz
    change ‖g • x - x‖ < 1
    exact hlt
  · intro hres
    apply MonoidHom.mem_ker.mpr
    ext z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    rw [absoluteResidueAction_residue]
    change IsLocalRing.residue absoluteNormInteger (absoluteDecomposition g • x) =
      IsLocalRing.residue absoluteNormInteger x
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (absoluteResidue_zero_iff_norm_lt_one _).mpr
    have hxnorm : ‖(x : ℚ̄₂)‖ ≤ 1 := by
      have hxval := x.property
      change ‖(x : ℚ̄₂)‖₊ ≤ 1 at hxval
      exact_mod_cast hxval
    have hlt := hres (x : ℚ̄₂) (by
      intro m hm
      have hm1 : m = 1 := Subgroup.mem_bot.mp hm
      subst m
      exact one_smul _ _) hxnorm
    change ‖g • (x : ℚ̄₂) - x‖ < 1 at hlt
    exact hlt

/-! ## Full tame inertia and the canonical absolute inertia subgroup -/

/-- The preimage of full tame inertia lies in the kernel of the actual absolute residue
action. -/
def TameFullInertiaLiesInAbsoluteInertiaAt (P : FieldParameters)
    (U : Subgroup AbsGalQ2) (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ g : ↑U, tame g ∈ inertiaPartQ P.qK →
    subtypeAnc U g ∈ absoluteInertiaSubgroup

/-- The actual-inertia inclusion is exactly corrected full-inertia absolute residue
triviality. -/
theorem tameFullInertiaLiesInAbsoluteInertiaAt_iff_residueTrivial
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) :
    TameFullInertiaLiesInAbsoluteInertiaAt P U tame ↔
      TameFullInertiaAbsoluteResidueTrivialAt P U tame := by
  constructor
  · intro h g hg
    exact (mem_absoluteInertiaSubgroup_iff_isResidueTrivial_bot _).mp (h g hg)
  · intro h g hg
    exact (mem_absoluteInertiaSubgroup_iff_isResidueTrivial_bot _).mpr (h g hg)

/-- The actual-inertia inclusion is exactly factorization of the odd-root action through the
full unramified quotient. -/
theorem tameFullInertiaLiesInAbsoluteInertiaAt_iff_oddRootFactorization
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) :
    TameFullInertiaLiesInAbsoluteInertiaAt P U tame ↔
      OddRootActionFactorsThroughQurAt P U tame :=
  (tameFullInertiaLiesInAbsoluteInertiaAt_iff_residueTrivial P U tame).trans
    (oddRootActionFactorsThroughQurAt_iff_fullInertia P U tame).symm

/-- Full tame inertia lying in actual absolute inertia produces the compatible residue-lift
packet. -/
theorem compatibleResidueLiftAt_of_fullTameInertiaInAbsoluteInertia
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) (htame : Function.Surjective tame)
    (hI : TameFullInertiaLiesInAbsoluteInertiaAt P U tame) :
    CompatibleResidueLiftAt P U tame :=
  compatibleResidueLiftAt_of_oddRootActionFactorsThroughQur P U tame htame
    ((tameFullInertiaLiesInAbsoluteInertiaAt_iff_oddRootFactorization P U tame).mp hI)

/-! ## The concrete AX4 quotient and `tameAtParams` -/

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- Equality transport of the tame modulus preserves the actual-inertia inclusion. -/
theorem tameAtParams_fullTameInertiaInAbsoluteInertia {q : ℕ}
    (tame : ContinuousMonoidHom (GalK K) (Tq q))
    (params : FieldParameters) (params_qK : params.qK = q)
    (hI : ∀ g : GalK K, tame g ∈ inertiaPartQ q →
      subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup) :
    TameFullInertiaLiesInAbsoluteInertiaAt params (GalKsub K)
      (tameAtParams params params_qK tame) := by
  subst q
  exact hI

variable {R : LocalReciprocity} [FiniteDimensional ℚ_[2] K]
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- The narrow standard field statement still required of the concrete AX4 tame quotient: the
preimage of its full tame inertia subgroup acts trivially on the actual absolute residue field. -/
def OrientedFullTameInertiaLiesInAbsoluteInertiaAt
    (T : OrientedTameQuotientK B FF) : Prop :=
  ∀ g : GalK K, T.tameFK g ∈ inertiaPartQ (qOf K FF) →
    subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup

/-- The standard AX4 full-inertia inclusion supplies odd-root factorization after reindexing by
`tameAtParams`. -/
theorem oddRootActionFactorsThroughQurAt_tameAtParams
    (T : OrientedTameQuotientK B FF) (params : FieldParameters)
    (params_qK : params.qK = qOf K FF)
    (hI : OrientedFullTameInertiaLiesInAbsoluteInertiaAt T) :
    OddRootActionFactorsThroughQurAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) :=
  (tameFullInertiaLiesInAbsoluteInertiaAt_iff_oddRootFactorization params
    (GalKsub K) (tameAtParams params params_qK T.tameFK)).mp
      (tameAtParams_fullTameInertiaInAbsoluteInertia T.tameFK params params_qK hI)

/-- The standard AX4 full-inertia inclusion is the concrete field adapter producing the
compatible residue-lift packet. -/
theorem compatibleResidueLiftAt_of_orientedFullTameInertiaInAbsoluteInertia
    (T : OrientedTameQuotientK B FF) (params : FieldParameters)
    (params_qK : params.qK = qOf K FF)
    (hI : OrientedFullTameInertiaLiesInAbsoluteInertiaAt T) :
    CompatibleResidueLiftAt params (GalKsub K)
      (tameAtParams params params_qK T.tameFK) :=
  compatibleResidueLiftAt_of_oddRootActionFactorsThroughQur params (GalKsub K)
    (tameAtParams params params_qK T.tameFK)
    (tameAtParams_surjective params params_qK T.tameFK T.tameFK_surjective)
    (oddRootActionFactorsThroughQurAt_tameAtParams T params params_qK hI)

#print axioms absGal_mem_absoluteNormInteger_decomposition
#print axioms absoluteDecomposition
#print axioms absoluteResidueAction
#print axioms absoluteResidueAction_residue
#print axioms absoluteResidue_zero_iff_norm_lt_one
#print axioms mem_absoluteInertiaSubgroup_iff_isResidueTrivial_bot
#print axioms TameFullInertiaLiesInAbsoluteInertiaAt
#print axioms tameFullInertiaLiesInAbsoluteInertiaAt_iff_residueTrivial
#print axioms tameFullInertiaLiesInAbsoluteInertiaAt_iff_oddRootFactorization
#print axioms compatibleResidueLiftAt_of_fullTameInertiaInAbsoluteInertia
#print axioms tameAtParams_fullTameInertiaInAbsoluteInertia
#print axioms OrientedFullTameInertiaLiesInAbsoluteInertiaAt
#print axioms oddRootActionFactorsThroughQurAt_tameAtParams
#print axioms compatibleResidueLiftAt_of_orientedFullTameInertiaInAbsoluteInertia

end
end GQ2.Dyadic
