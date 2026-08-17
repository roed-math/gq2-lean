/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateRelativeFrobeniusCompatibility

/-!
# The relative Frobenius comparison on reciprocity rows

The relative Frobenius comparison from the preceding module is an equality of two continuous
`Zhat`-valued coordinates on `GalK K`.  This module descends both coordinates to `GalKab K` and
uses the dense reciprocity image to reduce that global equality to local-class-field rows.

Every nonzero field element is a norm-one unit times an integral power of the chosen filtration
uniformizer.  Consequently the entire comparison is equivalent to two conditions: the signed
coordinate equality on all norm-one units and the equality on that one uniformizer.  This is the
smallest boundary exposed by the current reciprocity API.  The existing marked-reciprocity
packet controls only the pro-`2` unramified coordinate, so it does not prove these full `Zhat`
rows, especially their prime-to-`2` components.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂}

/-- A continuous `Zhat` coordinate descends through the field-side abelianization. -/
private def zhatAbLift (f : ContinuousMonoidHom (GalK K) Zhat) :
    ContinuousMonoidHom (GalKab K) Zhat :=
  quotientLift (commClosureK K) f (by
    show (commutator (GalK K)).topologicalClosure ≤ f.toMonoidHom.ker
    refine Subgroup.topologicalClosure_minimal (commutator (GalK K)) ?_ ?_
    · rw [show commutator (GalK K) = ⁅(⊤ : Subgroup (GalK K)), ⊤⁆ from rfl,
        Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_commute]
      exact GQ2.Dyadic.Words.Mpc.zhat_mul_comm _ _
    · have hset : (f.toMonoidHom.ker : Set (GalK K)) = f ⁻¹' {1} := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
          Set.mem_singleton_iff]
        rfl
      rw [hset]
      exact isClosed_singleton.preimage f.continuous_toFun)

/-- The canonical absolute residue coordinate descended to `GalK K`'s abelianization. -/
def absoluteResidueCoordinateKAb : ContinuousMonoidHom (GalKab K) Zhat :=
  zhatAbLift (absoluteResidueCoordinateK (K := K))

@[simp] theorem absoluteResidueCoordinateKAb_toAbK (g : GalK K) :
    absoluteResidueCoordinateKAb (K := K) (toAbK K g) =
      absoluteResidueCoordinateK (K := K) g := rfl

variable {R : LocalReciprocity} [FiniteDimensional ℚ_[2] K]
  {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- The full abstract unramified `Zhat` coordinate pulled back to `GalK K`. -/
def orientedTameQurCoordinateKRaw (T : OrientedTameQuotientK B FF) :
    ContinuousMonoidHom (GalK K) Zhat :=
  let qcoord : ContinuousMonoidHom (Tq (qOf K FF)) Zhat :=
    ⟨(qurQEquivZhat (qOf K FF)).toMulEquiv.toMonoidHom.comp
        (qMkQ (qOf K FF)).toMonoidHom,
      (qurQEquivZhat (qOf K FF)).continuous_toFun.comp
        (qMkQ (qOf K FF)).continuous_toFun⟩
  qcoord.comp T.tameFK

@[simp] theorem orientedTameQurCoordinateKRaw_apply
    (T : OrientedTameQuotientK B FF) (g : GalK K) :
    orientedTameQurCoordinateKRaw T g =
      qurQEquivZhat (qOf K FF)
        (qMkQ (qOf K FF) (T.tameFK g)) := rfl

/-- The full abstract unramified coordinate descended to `GalK K`'s abelianization. -/
def orientedTameQurCoordinateKAb (T : OrientedTameQuotientK B FF) :
    ContinuousMonoidHom (GalKab K) Zhat :=
  zhatAbLift (orientedTameQurCoordinateKRaw T)

@[simp] theorem orientedTameQurCoordinateKAb_toAbK
    (T : OrientedTameQuotientK B FF) (g : GalK K) :
    orientedTameQurCoordinateKAb T (toAbK K g) =
      qurQEquivZhat (qOf K FF)
        (qMkQ (qOf K FF) (T.tameFK g)) := rfl

/-- The signed comparison checked only on the dense reciprocity image. -/
def RelativeFrobeniusReciprocity
    (T : OrientedTameQuotientK B FF) : Prop :=
  ∀ x : (↥K)ˣ,
    absoluteResidueCoordinateKAb (K := K) (B.recip x) =
      (orientedTameQurCoordinateKAb T (B.recip x)) ^ (-(FF.f : ℤ))

/-- The dense reciprocity comparison reduces to units and one filtration uniformizer. -/
def RelativeFrobeniusReciprocityRows
    (T : OrientedTameQuotientK B FF) : Prop :=
  (∀ u : (↥K)ˣ, ‖((u : ↥K) : ℚ̄₂)‖ = 1 →
    absoluteResidueCoordinateKAb (K := K) (B.recip u) =
      (orientedTameQurCoordinateKAb T (B.recip u)) ^ (-(FF.f : ℤ))) ∧
  absoluteResidueCoordinateKAb (K := K)
      (B.recip (uniformizerK K FF)) =
    (orientedTameQurCoordinateKAb T
      (B.recip (uniformizerK K FF))) ^ (-(FF.f : ℤ))

theorem relativeFrobeniusReciprocity_of_rows
    (T : OrientedTameQuotientK B FF)
    (H : RelativeFrobeniusReciprocityRows T) :
    RelativeFrobeniusReciprocity T := by
  intro x
  obtain ⟨u, n, hx, hu⟩ := exists_unit_zpow_decomp K FF x
  rw [hx]
  simp only [map_mul, map_zpow]
  rw [H.1 u hu, H.2]
  have hcomm : Commute
      (orientedTameQurCoordinateKAb T (B.recip u))
      ((orientedTameQurCoordinateKAb T
        (B.recip (uniformizerK K FF))) ^ n) :=
    GQ2.Dyadic.Words.Mpc.zhat_mul_comm _ _
  rw [hcomm.mul_zpow, ← zpow_mul, ← zpow_mul,
    Int.mul_comm n (-(FF.f : ℤ))]

theorem relativeFrobeniusReciprocity_iff_rows
    (T : OrientedTameQuotientK B FF) :
    RelativeFrobeniusReciprocity T ↔
      RelativeFrobeniusReciprocityRows T := by
  constructor
  · intro H
    exact ⟨fun u _ => H u, H (uniformizerK K FF)⟩
  · exact relativeFrobeniusReciprocity_of_rows T

theorem orientedAbsoluteResidueFrobeniusCompatibility_iff_reciprocity
    (T : OrientedTameQuotientK B FF) :
    OrientedAbsoluteResidueFrobeniusCompatibility T ↔
      RelativeFrobeniusReciprocity T := by
  constructor
  · intro C x
    obtain ⟨g, hg⟩ := surjective_toAbK K (B.recip x)
    rw [← hg, absoluteResidueCoordinateKAb_toAbK,
      orientedTameQurCoordinateKAb_toAbK]
    exact C g
  · intro H g
    have hext :
        (fun x : GalKab K => absoluteResidueCoordinateKAb (K := K) x) =
          fun x : GalKab K =>
            (orientedTameQurCoordinateKAb T x) ^ (-(FF.f : ℤ)) := by
      refine Continuous.ext_on B.denseRange_recip
        (absoluteResidueCoordinateKAb (K := K)).continuous_toFun
        ((continuous_zpow (-(FF.f : ℤ))).comp
          (orientedTameQurCoordinateKAb T).continuous_toFun) ?_
      rintro _ ⟨x, rfl⟩
      exact H x
    simpa only [absoluteResidueCoordinateKAb_toAbK,
      orientedTameQurCoordinateKAb_toAbK] using congrFun hext (toAbK K g)

theorem orientedAbsoluteResidueFrobeniusCompatibility_iff_rows
    (T : OrientedTameQuotientK B FF) :
    OrientedAbsoluteResidueFrobeniusCompatibility T ↔
      RelativeFrobeniusReciprocityRows T :=
  (orientedAbsoluteResidueFrobeniusCompatibility_iff_reciprocity T).trans
    (relativeFrobeniusReciprocity_iff_rows T)

#print axioms absoluteResidueCoordinateKAb
#print axioms absoluteResidueCoordinateKAb_toAbK
#print axioms orientedTameQurCoordinateKRaw
#print axioms orientedTameQurCoordinateKAb
#print axioms RelativeFrobeniusReciprocity
#print axioms RelativeFrobeniusReciprocityRows
#print axioms relativeFrobeniusReciprocity_of_rows
#print axioms orientedAbsoluteResidueFrobeniusCompatibility_iff_reciprocity
#print axioms orientedAbsoluteResidueFrobeniusCompatibility_iff_rows

end
end GQ2.Dyadic
