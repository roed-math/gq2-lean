/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Word.NpcBridge

namespace GQ2.Dyadic

open GQ2 GQ2.WordCoh2 GQ2.SectionSix GQ2.SectionEight.AffineTLift
open GQ2.Dyadic.Certificates.MProcyclic

/-- A surjection onto the semidirect base transports the source exponent to a
constant `omega2` resolver for the associated `κ₀` central extension. -/
theorem kappaResolverLifts_of_surjective
    {L0 C V : Type} [Group L0] [Finite L0] [Group C] [Finite C]
    [AddCommGroup V] [Finite V] [DistribMulAction C V] {q : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (phi : L0 →* SemiProd C V) (hphi : Function.Surjective phi) :
    ResolverLifts
      (fun _ ↦ ((omega2Exp (4 * Monoid.exponent L0) : ℕ) : ℤ))
      (GQ2.WordCoh2.CentExt
        (GQ2.SectionEight.AffineTLift.kappa0Cocycle dat hdat)) := by
  have hexp : Monoid.exponent (SemiProd C V) ∣ Monoid.exponent L0 :=
    MonoidHom.exponent_dvd hphi
  have hN : 4 * Monoid.exponent L0 ≠ 0 := by
    exact Nat.mul_ne_zero (by norm_num) Monoid.exponent_ne_zero_of_finite
  intro y
  rw [zpow_natCast]
  apply powOmega2_pow_eq y
  · have hbase : y.base ^ Monoid.exponent L0 = 1 := by
      apply NpcBridge.sdEquiv.injective
      rw [map_pow, map_one]
      obtain ⟨k, hk⟩ := hexp
      rw [hk, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
    exact (nc3_orderOf_dvd_two_mul dat hdat hbase).trans ⟨2, by ring⟩
  · exact hN

#print axioms kappaResolverLifts_of_surjective

end GQ2.Dyadic
