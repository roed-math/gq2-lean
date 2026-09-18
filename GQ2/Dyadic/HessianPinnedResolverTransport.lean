/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.Hessian
import GQ2.Dyadic.Instances.OmegaPinnedLevelResolver

/-!
# Pinned phase resolvers after a surjective lower-level projection

The graph trace is resolved at the original lower group's level. A surjective
projection to the phase head must transport that level to the full central
extension, not merely to its action image. Every F2 central extension doubles
the lower exponent, so the existing four-times-exponent level resolves every
word, including genuine profinite and 2-adic powers.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH GQ2.SectionSix Count Certificates.MProcyclic

/-- A finite source surjecting onto the lower group bounds the entire central lift. -/
theorem orderOf_centExt_dvd_two_mul_exponent_of_surjective
    {L0 L : Type} [Group L0] [Finite L0] [Group L]
    (phi : L0 →* L) (hphi : Function.Surjective phi)
    (c : WordCoh.TwoCocycle L) (p : WordCoh.CentExt c) :
    orderOf p ∣ 2*Monoid.exponent L0 := by
  rw [orderOf_dvd_iff_pow_eq_one]
  apply centExt_pow_eq_one_of_base_pow
  obtain ⟨g, hg⟩ := hphi p.base
  rw [← hg, ← map_pow, Monoid.pow_exponent_eq_one, map_one]

/-- The pinned source level resolves omega powers in the projected central extension. -/
theorem omegaPinnedLevelZhatResolver_centExt_of_surjective
    {L0 L : Type} [Group L0] [Finite L0] [Group L]
    (phi : L0 →* L) (hphi : Function.Surjective phi)
    (c : WordCoh.TwoCocycle L) :
    ResolverLifts (omegaPinnedLevelZhatResolver (4*Monoid.exponent L0)) (WordCoh.CentExt c) := by
  intro p
  rw [omegaPinnedLevelZhatResolver_omega2, zpow_natCast]
  exact powOmega2_pow_eq p
    ((orderOf_centExt_dvd_two_mul_exponent_of_surjective phi hphi c p).trans ⟨2, by ring⟩)
    (fourMulExponent_ne_zero_and_even L0).1

/-- All word powers resolve in the projected phase extension at the original level. -/
theorem resolvedAt_omegaPinnedLevelResolvers_centExt_of_surjective
    {X L0 L : Type} [Group L0] [Finite L0] [Group L] [Finite L]
    (phi : L0 →* L) (hphi : Function.Surjective phi)
    (c : WordCoh.TwoCocycle L) (mu : X → WordCoh.CentExt c) (R : PWord X) :
    PWord.ResolvedAt mu (omegaPinnedLevelZhatResolver (4*Monoid.exponent L0))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent L0)) R :=
  resolvedAt_omegaPinnedLevelResolvers (fourMulExponent_ne_zero_and_even L0).1
    (fun p ↦ (orderOf_centExt_dvd_two_mul_exponent_of_surjective phi hphi c p).trans ⟨2, by ring⟩)
    mu R

/-- The semidirect graph group is the first-jet group. -/
def semiProdToWordLift {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V] :
    SemiProd C V →* WordLift V C where
  toFun p := ⟨p.1, p.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Every first jet is represented by a graph-group element. -/
theorem semiProdToWordLift_surjective
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V] :
    Function.Surjective (semiProdToWordLift (C := C) (V := V)) := by
  intro p
  exact ⟨(p.u,p.g), WordLift.ext rfl rfl⟩

/-- A surjective graph projection also transports the first-jet resolver. -/
theorem omegaPinnedLevelZhatResolver_wordLift_of_surjective
    {L0 C V : Type} [Group L0] [Finite L0] [Group C] [AddCommGroup V]
    [DistribMulAction C V]
    (phi : L0 →* SemiProd C V) (hphi : Function.Surjective phi) :
    ResolverLifts (omegaPinnedLevelZhatResolver (4*Monoid.exponent L0)) (WordLift V C) := by
  have hsurj : Function.Surjective (semiProdToWordLift.comp phi) :=
    semiProdToWordLift_surjective.comp hphi
  have hdiv : Monoid.exponent (WordLift V C) ∣ Monoid.exponent L0 :=
    MonoidHom.exponent_dvd hsurj
  intro p
  rw [omegaPinnedLevelZhatResolver_omega2, zpow_natCast]
  exact powOmega2_pow_eq p
    (((Monoid.order_dvd_exponent p).trans hdiv).trans ⟨4, by ring⟩)
    (fourMulExponent_ne_zero_and_even L0).1

#print axioms orderOf_centExt_dvd_two_mul_exponent_of_surjective
#print axioms omegaPinnedLevelZhatResolver_centExt_of_surjective
#print axioms resolvedAt_omegaPinnedLevelResolvers_centExt_of_surjective
#print axioms semiProdToWordLift
#print axioms semiProdToWordLift_surjective
#print axioms omegaPinnedLevelZhatResolver_wordLift_of_surjective

end
end GQ2.Dyadic

