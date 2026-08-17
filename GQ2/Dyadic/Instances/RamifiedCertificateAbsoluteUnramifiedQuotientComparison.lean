/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateResidueCompatibleOrientedTame

/-!
# Comparing the tame and canonical absolute unramified quotients

The full unramified quotient attached to AX4 is the abstract group `QurQ (qOf K FF)`, obtained
from `Tq` by killing `inertiaPartQ`.  Independently, the canonical residue action gives the
actual inertia subgroup of `GalK K`, namely the pullback of `absoluteInertiaSubgroup`.  Its
algebraic quotient is `AbsoluteUnramifiedQuotientK`.

The existing interfaces do not compare these two quotients.  The AX4 orientation and density of
reciprocity determine `nuTq`, but `nuTq` sees only the `2`-primary unramified coordinate.  The
map `qMkQ` retains the entire unramified quotient.  Mathlib defines the residue action and its
inertia kernel, but supplies no theorem identifying that quotient with `QurQ`.

`OrientedAbsoluteUnramifiedQuotientComparison` is the standard missing field statement in an
exact quotient form: a commuting equivalence from `QurQ` to the quotient by the canonical
residue-action kernel.  Unlike a direct containment wrapper, it proves equality of the pullback
of `inertiaPartQ` with actual absolute inertia.  The containment required by
`OrientedFullTameInertiaLiesInAbsoluteInertiaAt`, and hence the compatible residue-lift packet,
are immediate consequences.

The equivalence is algebraic rather than topological because the current residue-action API does
not equip its infinite automorphism target with a topology or prove that its kernel is closed.
This is sufficient for the exact kernel comparison and records no substitute continuity claim.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- The actual inertia subgroup of `GalK K`, obtained by restricting the canonical absolute
residue action. -/
def absoluteInertiaK : Subgroup (GalK K) :=
  absoluteInertiaSubgroup.comap (subtypeAnc (GalKsub K)).toMonoidHom

instance absoluteInertiaK_normal : (absoluteInertiaK (K := K)).Normal :=
  Subgroup.Normal.comap absoluteResidueAction.normal_ker
    (subtypeAnc (GalKsub K)).toMonoidHom

/-- The algebraic unramified quotient of `GalK K` by the kernel of its actual residue action. -/
abbrev AbsoluteUnramifiedQuotientK := GalK K ⧸ absoluteInertiaK (K := K)

/-- The canonical projection to the quotient by actual inertia. -/
def absoluteUnramifiedMkK : GalK K →* AbsoluteUnramifiedQuotientK (K := K) :=
  QuotientGroup.mk' (absoluteInertiaK (K := K))

/-- Vanishing in the canonical unramified quotient is exactly triviality of the absolute
residue action. -/
@[simp] theorem absoluteUnramifiedMkK_eq_one_iff (g : GalK K) :
    absoluteUnramifiedMkK (K := K) g = 1 ↔
      subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup := by
  constructor
  · intro hg
    have hmem : g ∈ absoluteInertiaK (K := K) :=
      (QuotientGroup.eq_one_iff g).mp hg
    exact hmem
  · intro hg
    exact (QuotientGroup.eq_one_iff g).mpr hg

variable {R : LocalReciprocity} [FiniteDimensional ℚ_[2] K]
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- The exact comparison between the abstract full unramified quotient of AX4 and the quotient
by the canonical absolute residue-action kernel.  The commuting square pins the equivalence to
the two quotient maps rather than allowing an arbitrary abstract group equivalence. -/
structure OrientedAbsoluteUnramifiedQuotientComparison
    (T : OrientedTameQuotientK B FF) where
  equiv : QurQ (qOf K FF) ≃* AbsoluteUnramifiedQuotientK (K := K)
  equiv_qMkQ_tameFK : ∀ g : GalK K,
    equiv (qMkQ (qOf K FF) (T.tameFK g)) = absoluteUnramifiedMkK (K := K) g

/-- Membership in full tame inertia is vanishing in `qMkQ`. -/
theorem mem_inertiaPartQ_iff_qMkQ_eq_one (q : ℕ) (x : Tq q) :
    x ∈ inertiaPartQ q ↔ qMkQ q x = 1 :=
  (quotientMk_eq_one_iff (N := inertiaPartQ q)).symm

namespace OrientedAbsoluteUnramifiedQuotientComparison

variable {T : OrientedTameQuotientK B FF}
  (C : OrientedAbsoluteUnramifiedQuotientComparison T)

include C in
/-- A commuting comparison identifies full tame inertia exactly with actual absolute inertia. -/
theorem tameFK_mem_inertiaPartQ_iff_absoluteInertia (g : GalK K) :
    T.tameFK g ∈ inertiaPartQ (qOf K FF) ↔
      subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup := by
  rw [← absoluteUnramifiedMkK_eq_one_iff]
  constructor
  · intro hg
    have hq : qMkQ (qOf K FF) (T.tameFK g) = 1 :=
      (mem_inertiaPartQ_iff_qMkQ_eq_one _ _).mp hg
    calc
      absoluteUnramifiedMkK (K := K) g =
          (equiv C) (qMkQ (qOf K FF) (T.tameFK g)) :=
        (equiv_qMkQ_tameFK C g).symm
      _ = (equiv C) 1 := congrArg (equiv C) hq
      _ = 1 := map_one (equiv C)
  · intro hg
    apply (mem_inertiaPartQ_iff_qMkQ_eq_one _ _).mpr
    apply (equiv C).injective
    calc
      (equiv C) (qMkQ (qOf K FF) (T.tameFK g)) =
          absoluteUnramifiedMkK (K := K) g := equiv_qMkQ_tameFK C g
      _ = 1 := hg
      _ = (equiv C) 1 := (map_one (equiv C)).symm

include C in
/-- The full tame-inertia preimage is the canonical absolute inertia subgroup, as subgroups of
`GalK K`. -/
theorem fullTameInertia_comap_eq_absoluteInertiaK :
    (inertiaPartQ (qOf K FF)).comap T.tameFK.toMonoidHom =
      absoluteInertiaK (K := K) := by
  ext g
  exact tameFK_mem_inertiaPartQ_iff_absoluteInertia C g

include C in
/-- The exact quotient comparison produces the full-inertia containment required by the residue
certificate route. -/
theorem orientedFullTameInertiaLiesInAbsoluteInertiaAt :
    OrientedFullTameInertiaLiesInAbsoluteInertiaAt T :=
  fun g hg => (tameFK_mem_inertiaPartQ_iff_absoluteInertia C g).mp hg

include C in
/-- Package the exact quotient comparison as a residue-compatible oriented tame quotient. -/
def toAbsoluteResidueCompatible :
    AbsoluteResidueCompatibleOrientedTameQuotientK B FF :=
  AbsoluteResidueCompatibleOrientedTameQuotientK.ofOriented T
    (orientedFullTameInertiaLiesInAbsoluteInertiaAt C)

include C in
/-- The exact quotient comparison supplies the compatible residue-lift packet after equality
transport of the residue cardinality. -/
theorem compatibleResidueLiftAt (P : FieldParameters) (hq : P.qK = qOf K FF) :
    CompatibleResidueLiftAt P (GalKsub K) (tameAtParams P hq T.tameFK) :=
  AbsoluteResidueCompatibleOrientedTameQuotientK.compatibleResidueLiftAt
    (toAbsoluteResidueCompatible C) P hq

end OrientedAbsoluteUnramifiedQuotientComparison

#print axioms absoluteInertiaK
#print axioms absoluteUnramifiedMkK
#print axioms absoluteUnramifiedMkK_eq_one_iff
#print axioms OrientedAbsoluteUnramifiedQuotientComparison
#print axioms mem_inertiaPartQ_iff_qMkQ_eq_one
#print axioms
  OrientedAbsoluteUnramifiedQuotientComparison.tameFK_mem_inertiaPartQ_iff_absoluteInertia
#print axioms
  OrientedAbsoluteUnramifiedQuotientComparison.fullTameInertia_comap_eq_absoluteInertiaK
#print axioms
  OrientedAbsoluteUnramifiedQuotientComparison.orientedFullTameInertiaLiesInAbsoluteInertiaAt
#print axioms OrientedAbsoluteUnramifiedQuotientComparison.toAbsoluteResidueCompatible
#print axioms OrientedAbsoluteUnramifiedQuotientComparison.compatibleResidueLiftAt

end
end GQ2.Dyadic
