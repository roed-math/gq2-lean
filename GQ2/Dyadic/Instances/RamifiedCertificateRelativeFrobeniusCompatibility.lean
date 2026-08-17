/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueZhat

/-!
# The relative Frobenius comparison boundary

The absolute residue Galois group now has a canonical square-Frobenius coordinate in Zhat.  This
module restricts it to GalK K.  Its kernel is exactly the pullback of canonical absolute inertia,
so the actual unramified quotient embeds continuously into Zhat and is continuously equivalent to
its closed image.  In particular, closedness of absoluteInertiaK no longer requires a hypothetical
field-side Frobenius coordinate.

The remaining comparison with an oriented abstract tame quotient is isolated as
OrientedAbsoluteResidueFrobeniusCompatibility.  If f is the residue degree, its equation is

  absolute square-Frobenius coordinate = (abstract tame coordinate)^(-f).

The minus sign records the repository convention: the abstract tame generator is geometric,
whereas square Frobenius on the residue field is arithmetic.  This one equation implies the full
tame-inertia containment in canonical absolute inertia and therefore produces the compatible
residue-lift packet.  No relative residue/Frobenius compatibility theorem in the current field
interfaces proves the equation, so it remains an explicit arithmetic boundary rather than being
silently inferred from the pro-two nuTq projection.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
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

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- The canonical absolute square-Frobenius coordinate restricted to `GalK K`. -/
def absoluteResidueCoordinateK : ContinuousMonoidHom (GalK K) Zhat :=
  let residueCoordinate : ContinuousMonoidHom Gal(k̄₂/k₀) Zhat :=
    ⟨absoluteResidueGalEquivZhat.toMulEquiv.toMonoidHom,
      absoluteResidueGalEquivZhat.continuous_toFun⟩
  residueCoordinate.comp
    (absoluteResidueAlgActionContinuous.comp (subtypeAnc (GalKsub K)))

@[simp] theorem absoluteResidueCoordinateK_apply (g : GalK K) :
    absoluteResidueCoordinateK (K := K) g =
      absoluteResidueGalEquivZhat
        (absoluteResidueAlgAction (subtypeAnc (GalKsub K) g)) := rfl

/-- The kernel of the restricted absolute Frobenius coordinate is exactly canonical inertia. -/
theorem absoluteResidueCoordinateK_ker :
    (absoluteResidueCoordinateK (K := K)).toMonoidHom.ker =
      absoluteInertiaK (K := K) := by
  ext g
  change absoluteResidueGalEquivZhat
      (absoluteResidueAlgAction (subtypeAnc (GalKsub K) g)) = 1 ↔
    subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup
  constructor
  · intro h
    have ha : absoluteResidueAlgAction
        (subtypeAnc (GalKsub K) g) = 1 := by
      apply absoluteResidueGalEquivZhat.injective
      simpa using h
    have hker : subtypeAnc (GalKsub K) g ∈
        absoluteResidueAlgAction.ker := ha
    rwa [absoluteResidueAlgAction_ker] at hker
  · intro h
    have hker : subtypeAnc (GalKsub K) g ∈
        absoluteResidueAlgAction.ker := by
      rwa [absoluteResidueAlgAction_ker]
    have ha : absoluteResidueAlgAction
        (subtypeAnc (GalKsub K) g) = 1 := hker
    rw [ha, map_one]

instance absoluteInertiaK_isClosed_unconditional :
    IsClosed ((absoluteInertiaK (K := K) : Subgroup (GalK K)) : Set (GalK K)) := by
  rw [← absoluteResidueCoordinateK_ker, MonoidHom.coe_ker]
  exact isClosed_singleton.preimage
    (absoluteResidueCoordinateK (K := K)).continuous_toFun

/-- The canonical absolute coordinate descended to the quotient by actual inertia. -/
def absoluteUnramifiedCoordinateK :
    ContinuousMonoidHom (AbsoluteUnramifiedQuotientK (K := K)) Zhat :=
  quotientLift (absoluteInertiaK (K := K))
    (absoluteResidueCoordinateK (K := K)) (by
      rw [absoluteResidueCoordinateK_ker])

@[simp] theorem absoluteUnramifiedCoordinateK_mk (g : GalK K) :
    absoluteUnramifiedCoordinateK (K := K)
        (absoluteUnramifiedMkK (K := K) g) =
      absoluteResidueCoordinateK (K := K) g := rfl

theorem absoluteUnramifiedCoordinateK_injective :
    Function.Injective (absoluteUnramifiedCoordinateK (K := K)) := by
  change Function.Injective
    (absoluteUnramifiedCoordinateK (K := K)).toMonoidHom
  rw [← (absoluteUnramifiedCoordinateK (K := K)).toMonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    change absoluteResidueCoordinateK (K := K) g = 1 at hx
    have hg : g ∈ absoluteInertiaK (K := K) := by
      rw [← absoluteResidueCoordinateK_ker]
      exact hx
    exact (QuotientGroup.eq_one_iff g).mpr hg
  · rintro rfl
    exact map_one _

section FiniteK

variable [FiniteDimensional ℚ_[2] K]

private noncomputable instance galK_compactSpace : CompactSpace (GalK K) :=
  isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_of_isOpen _ (isOpen_fixingSubgroup K)).isCompact

/-- The image of the restricted absolute Frobenius coordinate is closed in `Zhat`. -/
theorem absoluteUnramifiedCoordinateK_range_isClosed :
    IsClosed (Set.range (absoluteUnramifiedCoordinateK (K := K))) :=
  (isCompact_range
    (absoluteUnramifiedCoordinateK (K := K)).continuous_toFun).isClosed

/-- The actual unramified quotient is continuously equivalent to its closed image in the
canonical absolute `Zhat` coordinate. -/
noncomputable def absoluteUnramifiedCoordinateKEquivRange :
    ContinuousMulEquiv (AbsoluteUnramifiedQuotientK (K := K))
      (absoluteUnramifiedCoordinateK (K := K)).toMonoidHom.range := by
  let f := (absoluteUnramifiedCoordinateK (K := K)).toMonoidHom
  let e : AbsoluteUnramifiedQuotientK (K := K) ≃* f.range :=
    MulEquiv.ofBijective f.rangeRestrict
      ⟨fun _ _ h => absoluteUnramifiedCoordinateK_injective
          (congrArg Subtype.val h),
        f.rangeRestrict_surjective⟩
  have he_cont : Continuous e :=
    (absoluteUnramifiedCoordinateK (K := K)).continuous_toFun.subtype_mk _
  have he_home : IsHomeomorph e :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨he_cont, e.bijective⟩
  have he_inv_cont : Continuous e.symm :=
    (Equiv.isHomeomorph_iff e.toEquiv).mp he_home |>.2
  exact
    { e with
      continuous_toFun := he_cont
      continuous_invFun := he_inv_cont }

end FiniteK

variable {R : LocalReciprocity} [FiniteDimensional ℚ_[2] K]
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- The exact signed residue-degree Frobenius square.  The abstract tame generator is geometric,
whereas square Frobenius on the absolute residue field is arithmetic, accounting for the minus
sign. -/
def OrientedAbsoluteResidueFrobeniusCompatibility
    (T : OrientedTameQuotientK B FF) : Prop :=
  ∀ g : GalK K,
    absoluteResidueCoordinateK (K := K) g =
      (qurQEquivZhat (qOf K FF)
        (qMkQ (qOf K FF) (T.tameFK g))) ^ (-(FF.f : ℤ))

namespace OrientedAbsoluteResidueFrobeniusCompatibility

variable {T : OrientedTameQuotientK B FF}
  (C : OrientedAbsoluteResidueFrobeniusCompatibility T)

include C in
theorem orientedFullTameInertiaLiesInAbsoluteInertiaAt :
    OrientedFullTameInertiaLiesInAbsoluteInertiaAt T := by
  intro g hg
  have hq : qMkQ (qOf K FF) (T.tameFK g) = 1 :=
    (mem_inertiaPartQ_iff_qMkQ_eq_one _ _).mp hg
  have hc : absoluteResidueCoordinateK (K := K) g = 1 := by
    rw [C g, hq, map_one, one_zpow]
  have hmem : g ∈ absoluteInertiaK (K := K) := by
    rw [← absoluteResidueCoordinateK_ker]
    exact hc
  exact hmem

include C in
def toAbsoluteResidueCompatible :
    AbsoluteResidueCompatibleOrientedTameQuotientK B FF :=
  AbsoluteResidueCompatibleOrientedTameQuotientK.ofOriented T
    C.orientedFullTameInertiaLiesInAbsoluteInertiaAt

include C in
theorem compatibleResidueLiftAt (P : FieldParameters)
    (hq : P.qK = qOf K FF) :
    CompatibleResidueLiftAt P (GalKsub K) (tameAtParams P hq T.tameFK) :=
  C.toAbsoluteResidueCompatible.compatibleResidueLiftAt P hq

end OrientedAbsoluteResidueFrobeniusCompatibility

#print axioms absoluteResidueCoordinateK
#print axioms absoluteResidueCoordinateK_apply
#print axioms absoluteResidueCoordinateK_ker
#print axioms absoluteInertiaK_isClosed_unconditional
#print axioms absoluteUnramifiedCoordinateK
#print axioms absoluteUnramifiedCoordinateK_mk
#print axioms absoluteUnramifiedCoordinateK_injective
#print axioms absoluteUnramifiedCoordinateK_range_isClosed
#print axioms absoluteUnramifiedCoordinateKEquivRange
#print axioms OrientedAbsoluteResidueFrobeniusCompatibility
#print axioms
  OrientedAbsoluteResidueFrobeniusCompatibility.orientedFullTameInertiaLiesInAbsoluteInertiaAt
#print axioms OrientedAbsoluteResidueFrobeniusCompatibility.toAbsoluteResidueCompatible
#print axioms OrientedAbsoluteResidueFrobeniusCompatibility.compatibleResidueLiftAt

end
end GQ2.Dyadic

