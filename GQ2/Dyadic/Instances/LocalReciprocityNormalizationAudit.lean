/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.LocalReciprocityOddReflection
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueBaseChange

/-!
# The current reciprocity bundle does not force full signed Frobenius normalization

Odd reflection preserves every clause of `LocalReciprocity`.  This module checks
that a bundle and its reflection cannot both satisfy the full absolute-residue
Frobenius law: the arithmetic generator changes sign in the quotient of order
three.  The weaker inertia-kernel comparison is deliberately not refuted.
-/

namespace GQ2.Dyadic

open GQ2 SpectralLocalField

noncomputable section

local notation "k₀" => IsLocalRing.ResidueField BaseInteger
local notation "k̄₂" => IsLocalRing.ResidueField absoluteNormInteger

local instance : Algebra k₀ k̄₂ := absoluteResidueFieldAlgebra
local instance : Algebra.IsAlgebraic k₀ k̄₂ := absoluteResidueField_isAlgebraic
local instance : Finite k₀ := baseResidueField_finite
local instance : Fintype k₀ := Fintype.ofFinite k₀
local instance : IsAlgClosed k̄₂ := absoluteResidueField_isAlgClosed
local instance : Normal k₀ k̄₂ := absoluteResidueField_normal
local instance : Algebra.IsSeparable k₀ k̄₂ := inferInstance
local instance : IsGalois k₀ k̄₂ where
local instance : CommGroup Zhat :=
  { (inferInstance : Group Zhat) with mul_comm := Words.Mpc.zhat_mul_comm }

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

local instance : IsClosed (commClosure : Set AbsGalQ2) := isClosed_closure
local instance : T2Space AbsGalQ2ab :=
  inferInstanceAs (T2Space (AbsGalQ2 ⧸ commClosure))
local instance : TotallyDisconnectedSpace AbsGalQ2ab :=
  inferInstanceAs (TotallyDisconnectedSpace (AbsGalQ2 ⧸ commClosure))

/-- The canonical actual square-Frobenius coordinate on the base absolute Galois group. -/
def baseAbsoluteResidueCoordinate : ContinuousMonoidHom AbsGalQ2 Zhat :=
  (⟨absoluteResidueGalEquivZhat.toMulEquiv.toMonoidHom,
    absoluteResidueGalEquivZhat.continuous_toFun⟩ :
    ContinuousMonoidHom Gal(k̄₂/k₀) Zhat).comp absoluteResidueAlgActionContinuous

/-- Its descent to the genuine topological abelianization. -/
def baseAbsoluteResidueCoordinateAb : ContinuousMonoidHom AbsGalQ2ab Zhat :=
  quotientLift commClosure baseAbsoluteResidueCoordinate (by
    apply Subgroup.topologicalClosure_minimal
    · exact Abelianization.commutator_subset_ker baseAbsoluteResidueCoordinate.toMonoidHom
    · exact isClosed_singleton.preimage baseAbsoluteResidueCoordinate.continuous_toFun)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
@[simp] theorem baseAbsoluteResidueCoordinateAb_toAb (g : AbsGalQ2) :
    baseAbsoluteResidueCoordinateAb (toAb g) =
      absoluteResidueGalEquivZhat (absoluteResidueAlgAction g) := rfl

/-- The full signed law pins this coordinate at the uniformizer to the integer one. -/
theorem baseAbsoluteResidueCoordinateAb_uniformizer_of_law
    (R : LocalReciprocity) (H : AbsoluteResidueBaseReciprocityLaw R) :
    baseAbsoluteResidueCoordinateAb (R.recip uniformizer) = Zhat.ofInt 1 := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective commClosure (R.recip uniformizer)
  change toAb g = R.recip uniformizer at hg
  rw [← hg, baseAbsoluteResidueCoordinateAb_toAb, H uniformizer g hg]
  have hv : v2 uniformizer = 1 := by
    norm_num [v2, uniformizer, Padic.valuation_p]
  rw [hv, zpow_one, absoluteResidueGalEquivZhat_frobenius]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The difference from the integer generator is already visible modulo three. -/
theorem oddReflection_ofInt_one_ne : oddReflection (Zhat.ofInt 1) ≠ Zhat.ofInt 1 := by
  intro h
  let f : ContinuousMonoidHom Zhat (Multiplicative (ZMod 3)) :=
    (zpowHatHom (Multiplicative.ofAdd (1 : ZMod 3))).hom
  have hm := congrArg f h
  rw [map_oddReflection] at hm
  have hf : f (Zhat.ofInt 1) = Multiplicative.ofAdd (1 : ZMod 3) := by
    change (Multiplicative.ofAdd (1 : ZMod 3)) ^ᶻ Zhat.ofInt 1 = _
    rw [zpowHat_ofInt, zpow_one]
  rw [hf, oddReflection_apply, zpowHat_omega2] at hm
  have homega : omega2Exp 3 = 0 := by
    have hfac : (3 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [omega2Exp, hfac]
  have hp : powOmega2 (Multiplicative.ofAdd (1 : ZMod 3)) = 1 := by
    simp [powOmega2, homega]
  rw [hp, one_pow, one_mul] at hm
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ ≠
    Multiplicative.ofAdd (1 : ZMod 3)) hm

/-- No bundle and its odd reflection can both have the signed actual Frobenius law. -/
theorem LocalReciprocity.not_base_law_and_oddReflected_base_law (R : LocalReciprocity) :
    ¬ (AbsoluteResidueBaseReciprocityLaw R ∧
      AbsoluteResidueBaseReciprocityLaw R.oddReflected) := by
  rintro ⟨hR, hF⟩
  have h := baseAbsoluteResidueCoordinateAb_uniformizer_of_law R.oddReflected hF
  rw [GQ2.LocalReciprocity.oddReflected_recip, map_oddReflection,
    baseAbsoluteResidueCoordinateAb_uniformizer_of_law R hR] at h
  exact oddReflection_ofInt_one_ne h

/-- Consequently there is no uniform derivation of the full signed law from this bundle. -/
theorem LocalReciprocity.not_every_bundle_has_base_law (R : LocalReciprocity) :
    ¬ (∀ S : LocalReciprocity, AbsoluteResidueBaseReciprocityLaw S) := by
  intro h
  exact LocalReciprocity.not_base_law_and_oddReflected_base_law R ⟨h R, h R.oddReflected⟩

#print axioms baseAbsoluteResidueCoordinateAb_uniformizer_of_law
#print axioms oddReflection_ofInt_one_ne
#print axioms LocalReciprocity.not_base_law_and_oddReflected_base_law
#print axioms LocalReciprocity.not_every_bundle_has_base_law

end
end GQ2.Dyadic
