/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteUnramifiedQuotientComparison

/-!
# The full unramified tame quotient and its Frobenius coordinate

The abstract full unramified quotient `QurQ q` is canonically the profinite completion `Zhat`.
This module constructs the equivalence directly from the presentation of `Tq q`: the forward
map sends `tqSigma` to `Zhat.ofInt 1` and kills `tqTau`, while the inverse raises `qSigmaQ` to a
profinite exponent.  Density of the integers and topological generation by `qSigmaQ` prove that
the two maps are inverse.

The maximal pro-`2` projection of this full coordinate is exactly `nuTq`.  Consequently AX4's
orientation and reciprocity-density theorem determine only this pro-`2` projection; they cannot
recover the prime-to-`2` coordinates of `Zhat`.

On the field side, `AbsoluteUnramifiedFrobeniusCoordinate` states the remaining standard theorem:
the quotient by the canonical absolute residue-action kernel is continuously equivalent to
`Zhat`, and its coordinate agrees with the constructed tame coordinate.  This single commuting
square constructs `OrientedAbsoluteUnramifiedQuotientComparison`, hence the exact full-inertia
comparison and compatible residue-lift packet.  It also proves that the canonical inertia kernel
is closed, a fact not available from Mathlib's current infinite residue-action API alone.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

private theorem tameToZhat_of_zero_for_qur :
    tameToZhat (FreeProfiniteGroup.of 0) = Zhat.ofInt 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

private theorem tameToZhat_of_one_for_qur :
    tameToZhat (FreeProfiniteGroup.of 1) = 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

private theorem tameToZhat_tameWordQ_for_qur (q : ℕ) :
    tameToZhat (tameWordQ q) = 1 := by
  simp only [tameWordQ, conjP, map_mul, map_inv, map_pow,
    tameToZhat_of_zero_for_qur, tameToZhat_of_one_for_qur]
  group

/-- The full profinite unramified coordinate on `Tq q`, before quotienting by tame inertia. -/
def tqToZhat (q : ℕ) : ContinuousMonoidHom (Tq q) Zhat :=
  presentationLift {tameWordQ q} tameToZhat (by
    rintro r rfl
    exact tameToZhat_tameWordQ_for_qur q)

@[simp] theorem tqToZhat_tqSigma (q : ℕ) :
    tqToZhat q (tqSigma q) = Zhat.ofInt 1 :=
  (presentationLift_mk {tameWordQ q} tameToZhat
    (by rintro r rfl; exact tameToZhat_tameWordQ_for_qur q)
    (FreeProfiniteGroup.of 0)).trans tameToZhat_of_zero_for_qur

@[simp] theorem tqToZhat_tqTau (q : ℕ) : tqToZhat q (tqTau q) = 1 :=
  (presentationLift_mk {tameWordQ q} tameToZhat
    (by rintro r rfl; exact tameToZhat_tameWordQ_for_qur q)
    (FreeProfiniteGroup.of 1)).trans tameToZhat_of_one_for_qur

/-- Full tame inertia lies in the kernel of the profinite unramified coordinate. -/
theorem inertiaPartQ_le_tqToZhat_ker (q : ℕ) :
    inertiaPartQ q ≤ (tqToZhat q).toMonoidHom.ker := by
  have hclosed : IsClosed (((tqToZhat q).toMonoidHom.ker : Subgroup (Tq q)) : Set (Tq q)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (tqToZhat q).continuous_toFun
  refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
  refine Subgroup.normalClosure_le_normal ?_
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact MonoidHom.mem_ker.mpr (tqToZhat_tqTau q)

/-- The full profinite unramified coordinate descended to `QurQ q`. -/
def qurQToZhat (q : ℕ) : ContinuousMonoidHom (QurQ q) Zhat :=
  quotientLift (inertiaPartQ q) (tqToZhat q) (inertiaPartQ_le_tqToZhat_ker q)

@[simp] theorem qurQToZhat_qMkQ (q : ℕ) (x : Tq q) :
    qurQToZhat q (qMkQ q x) = tqToZhat q x := by
  exact quotientLift_quotientMk (inertiaPartQ q) (tqToZhat q)
    (inertiaPartQ_le_tqToZhat_ker q) x

@[simp] theorem qurQToZhat_qSigmaQ (q : ℕ) :
    qurQToZhat q (qSigmaQ q) = Zhat.ofInt 1 := by
  exact (qurQToZhat_qMkQ q (tqSigma q)).trans (tqToZhat_tqSigma q)

/-- The inverse coordinate sends a profinite exponent to the corresponding power of Frobenius. -/
def zhatToQurQ (q : ℕ) : ContinuousMonoidHom Zhat (QurQ q) :=
  (zpowHatHom (qSigmaQ q)).hom

@[simp] theorem zhatToQurQ_ofInt (q : ℕ) (n : ℤ) :
    zhatToQurQ q (Zhat.ofInt n) = qSigmaQ q ^ n :=
  zpowHat_ofInt (qSigmaQ q) n

theorem qurQToZhat_zhatToQurQ (q : ℕ) (z : Zhat) :
    qurQToZhat q (zhatToQurQ q z) = z := by
  have hfun : (fun w : Zhat => qurQToZhat q (zhatToQurQ q w)) = fun w => w := by
    apply Zhat.funext_ofInt
    · exact (qurQToZhat q).continuous_toFun.comp (zhatToQurQ q).continuous_toFun
    · exact continuous_id
    · intro n
      rw [zhatToQurQ_ofInt, map_zpow, qurQToZhat_qSigmaQ, Zhat.ofInt_one_zpow]
  exact congrFun hfun z

theorem zhatToQurQ_qurQToZhat (q : ℕ) (x : QurQ q) :
    zhatToQurQ q (qurQToZhat q x) = x := by
  apply TopGen.monoidHom_eq
    (f := (zhatToQurQ q).toMonoidHom.comp (qurQToZhat q).toMonoidHom)
    (g := MonoidHom.id (QurQ q))
    ((zhatToQurQ q).continuous_toFun.comp (qurQToZhat q).continuous_toFun)
    continuous_id (topGen_qurQ q)
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  change zhatToQurQ q (qurQToZhat q (qSigmaQ q)) = qSigmaQ q
  rw [qurQToZhat_qSigmaQ, zhatToQurQ_ofInt, zpow_one]

/-- The canonical continuous equivalence `QurQ q ≃ Zhat`, normalized at geometric Frobenius. -/
def qurQEquivZhat (q : ℕ) : ContinuousMulEquiv (QurQ q) Zhat where
  toFun := qurQToZhat q
  invFun := zhatToQurQ q
  left_inv := zhatToQurQ_qurQToZhat q
  right_inv := qurQToZhat_zhatToQurQ q
  map_mul' := map_mul (qurQToZhat q)
  continuous_toFun := (qurQToZhat q).continuous_toFun
  continuous_invFun := (zhatToQurQ q).continuous_toFun

@[simp] theorem qurQEquivZhat_qSigmaQ (q : ℕ) :
    qurQEquivZhat q (qSigmaQ q) = Zhat.ofInt 1 :=
  qurQToZhat_qSigmaQ q

/-- The `2`-primary character `nuTq` is exactly the maximal pro-`2` projection of the full
`Zhat` coordinate. -/
theorem maxProPMk_qurQEquivZhat_qMkQ (q : ℕ) (x : Tq q) :
    maxProPMk 2 Zhat (qurQEquivZhat q (qMkQ q x)) = nuTq q x := by
  let f : ContinuousMonoidHom (Tq q) Ztwo :=
    (maxProPMk 2 Zhat).comp (tqToZhat q)
  have hcomp : ∀ y : Tq q, f y = nuTq q y := by
    apply contMonoidHom_eq_of_gens
    · change maxProPMk 2 Zhat (tqToZhat q (tqSigma q)) = nuTq q (tqSigma q)
      rw [tqToZhat_tqSigma, nuTq_tqSigma]
      rfl
    · change maxProPMk 2 Zhat (tqToZhat q (tqTau q)) = nuTq q (tqTau q)
      rw [tqToZhat_tqTau, nuTq_tqTau, map_one]
      rfl
  exact (congrArg (maxProPMk 2 Zhat) (qurQToZhat_qMkQ q x)).trans (hcomp x)

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] K] {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- The missing field-side Frobenius coordinate: the actual residue-action quotient is
continuously `Zhat`, and its coordinate agrees with the canonical coordinate constructed from
the oriented tame quotient. -/
structure AbsoluteUnramifiedFrobeniusCoordinate
    (T : OrientedTameQuotientK B FF) where
  equiv : ContinuousMulEquiv (AbsoluteUnramifiedQuotientK (K := K)) Zhat
  equiv_absoluteUnramifiedMkK : ∀ g : GalK K,
    equiv (absoluteUnramifiedMkK (K := K) g) =
      qurQEquivZhat (qOf K FF) (qMkQ (qOf K FF) (T.tameFK g))

namespace AbsoluteUnramifiedFrobeniusCoordinate

variable {T : OrientedTameQuotientK B FF}
  (C : AbsoluteUnramifiedFrobeniusCoordinate T)

include C in
/-- A continuous Frobenius coordinate proves that the canonical absolute inertia kernel is
closed. -/
theorem absoluteInertiaK_isClosed :
    IsClosed ((absoluteInertiaK (K := K) : Subgroup (GalK K)) : Set (GalK K)) := by
  letI : T2Space (AbsoluteUnramifiedQuotientK (K := K)) :=
    C.equiv.symm.toHomeomorph.t2Space
  have heq : absoluteInertiaK (K := K) =
      (absoluteUnramifiedMkK (K := K)).ker := by
    ext g
    rw [MonoidHom.mem_ker, absoluteUnramifiedMkK_eq_one_iff]
    rfl
  rw [heq, MonoidHom.coe_ker]
  exact isClosed_singleton.preimage QuotientGroup.continuous_mk

include C in
/-- Compose the two `Zhat` coordinates to construct the exact quotient comparison of W176. -/
def toOrientedAbsoluteUnramifiedQuotientComparison :
    OrientedAbsoluteUnramifiedQuotientComparison T where
  equiv := (qurQEquivZhat (qOf K FF)).toMulEquiv.trans C.equiv.symm.toMulEquiv
  equiv_qMkQ_tameFK g := by
    apply C.equiv.injective
    rw [C.equiv_absoluteUnramifiedMkK]
    exact C.equiv.apply_symm_apply _

include C in
/-- The field-side Frobenius coordinate supplies the exact full-inertia containment. -/
theorem orientedFullTameInertiaLiesInAbsoluteInertiaAt :
    OrientedFullTameInertiaLiesInAbsoluteInertiaAt T :=
  OrientedAbsoluteUnramifiedQuotientComparison.orientedFullTameInertiaLiesInAbsoluteInertiaAt
    C.toOrientedAbsoluteUnramifiedQuotientComparison

include C in
/-- The field-side Frobenius coordinate supplies the compatible residue-lift packet after
equality transport of the residue cardinality. -/
theorem compatibleResidueLiftAt (P : FieldParameters) (hq : P.qK = qOf K FF) :
    CompatibleResidueLiftAt P (GalKsub K) (tameAtParams P hq T.tameFK) :=
  OrientedAbsoluteUnramifiedQuotientComparison.compatibleResidueLiftAt
    C.toOrientedAbsoluteUnramifiedQuotientComparison P hq

end AbsoluteUnramifiedFrobeniusCoordinate

#print axioms tqToZhat
#print axioms tqToZhat_tqSigma
#print axioms tqToZhat_tqTau
#print axioms inertiaPartQ_le_tqToZhat_ker
#print axioms qurQToZhat
#print axioms qurQToZhat_qMkQ
#print axioms qurQToZhat_qSigmaQ
#print axioms zhatToQurQ
#print axioms zhatToQurQ_ofInt
#print axioms qurQToZhat_zhatToQurQ
#print axioms zhatToQurQ_qurQToZhat
#print axioms qurQEquivZhat
#print axioms qurQEquivZhat_qSigmaQ
#print axioms maxProPMk_qurQEquivZhat_qMkQ
#print axioms AbsoluteUnramifiedFrobeniusCoordinate
#print axioms AbsoluteUnramifiedFrobeniusCoordinate.absoluteInertiaK_isClosed
#print axioms
  AbsoluteUnramifiedFrobeniusCoordinate.toOrientedAbsoluteUnramifiedQuotientComparison
#print axioms
  AbsoluteUnramifiedFrobeniusCoordinate.orientedFullTameInertiaLiesInAbsoluteInertiaAt
#print axioms AbsoluteUnramifiedFrobeniusCoordinate.compatibleResidueLiftAt

end
end GQ2.Dyadic
