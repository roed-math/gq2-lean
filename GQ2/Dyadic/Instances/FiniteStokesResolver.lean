/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FiniteProfiniteResolver
import GQ2.Dyadic.Instances.StokesEndpointSubstitution
import GQ2.Dyadic.Instances.TameInertiaPrimeToTwoCorrection

/-!
# Finite resolvers carrying the Stokes parity test

Resolve a finite target `Q` together with the multiplicative group of `ZMod 2`.  Projection to
`Q` gives a resolver for every reflected word, while projection to the scalar factor records
the parity of every selected integer exponent.  In particular, a profinite exponent with
trivial maximal pro-`2` component resolves to a power which is invisible to every `heisEps`.

Consequently prime-to-two tame correction preserves the Stokes endpoint for an arbitrary word.
This is a word- and rank-generic construction.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates

/-- The finite target enlarged by the scalar parity detector. -/
abbrev StokesResolverTarget (Q : Type) := Multiplicative (ZMod 2) × Q

section FiniteTarget

variable (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]

noncomputable def stokesZhatResolver : Zhat → ℤ :=
  finiteZhatResolver (StokesResolverTarget Q)

noncomputable def stokesZtwoResolver : ℤ_[2] → ℤ :=
  finiteZtwoResolver (StokesResolverTarget Q)

theorem stokesZhatResolver_spec (gamma : Zhat) (x : Q) :
    x ^ stokesZhatResolver Q gamma = x ^ᶻ gamma := by
  let sndHom : ContinuousMonoidHom (StokesResolverTarget Q) Q :=
    ⟨{ toFun := Prod.snd, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }, continuous_snd⟩
  have H := finiteZhatResolver_spec (StokesResolverTarget Q) gamma
    ((1 : Multiplicative (ZMod 2)), x)
  calc
    x ^ stokesZhatResolver Q gamma =
        sndHom (((1 : Multiplicative (ZMod 2)), x) ^
          stokesZhatResolver Q gamma) := by rfl
    _ = sndHom (((1 : Multiplicative (ZMod 2)), x) ^ᶻ gamma) :=
      congrArg sndHom H
    _ = x ^ᶻ gamma := map_zpowHat sndHom _ _

theorem stokesZhatResolver_zmod2_spec (gamma : Zhat)
    (x : Multiplicative (ZMod 2)) :
    x ^ stokesZhatResolver Q gamma = x ^ᶻ gamma := by
  let fstHom : ContinuousMonoidHom (StokesResolverTarget Q)
      (Multiplicative (ZMod 2)) :=
    ⟨{ toFun := Prod.fst, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }, continuous_fst⟩
  have H := finiteZhatResolver_spec (StokesResolverTarget Q) gamma (x, 1)
  calc
    x ^ stokesZhatResolver Q gamma =
        fstHom ((x, (1 : Q)) ^ stokesZhatResolver Q gamma) := by rfl
    _ = fstHom ((x, (1 : Q)) ^ᶻ gamma) := congrArg fstHom H
    _ = x ^ᶻ gamma := map_zpowHat fstHom _ _

theorem resolvedAt_stokesResolvers {X : Type} (mu : X → Q) (w : PWord X) :
    PWord.ResolvedAt mu (stokesZhatResolver Q) (stokesZtwoResolver Q) w := by
  induction w with
  | one => trivial
  | gen g => trivial
  | mul u v ihu ihv => exact ⟨ihu, ihv⟩
  | inv u ih => exact ih
  | conj u g ihu ihg => exact ⟨ihu, ihg⟩
  | comm u v ihu ihv => exact ⟨ihu, ihv⟩
  | zpow u k ih => exact ih
  | z2pow u z ih =>
      refine ⟨ih, ?_⟩
      exact (stokesZhatResolver_spec Q (padicOmega2 z) (PWord.eval mu u)).symm
  | profPow u gamma ih =>
      refine ⟨ih, ?_⟩
      exact (stokesZhatResolver_spec Q gamma (PWord.eval mu u)).symm

theorem resolvesAt_stokesResolvers {X rho : Type} (W : rho → PWord X) :
    ResolvesAt W
      (fun k ↦ heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q) (W k)) Q :=
  resolvesAt_of_resolvedAt fun f k ↦ resolvedAt_stokesResolvers Q f (W k)

/-- Prime-to-two exponents are invisible to the scalar component of the resolver. -/
theorem stokesZhatResolver_pow_eq_one_of_maxProPMk_eq_one
    (x : Multiplicative (ZMod 2)) {z : Zhat}
    (hz : maxProPMk 2 Zhat z = 1) :
    x ^ stokesZhatResolver Q z = 1 := by
  rw [stokesZhatResolver_zmod2_spec]
  exact zpowHat_eq_one_of_maxProPMk_eq_one
    GQ2.SectionThree.isProP_two_multZMod2 x hz

/-- The scalar factor forces the selected representative of `omega2` to be odd. -/
theorem stokesZhatResolver_omega2_odd : Odd (stokesZhatResolver Q omega2) := by
  apply Int.not_even_iff_odd.mp
  intro heven
  let a : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  have H := stokesZhatResolver_zmod2_spec Q omega2 a
  have hsem : a ^ᶻ omega2 = a :=
    zpowHat_omega2_eq_self_of_isProP
      GQ2.SectionThree.isProP_two_multZMod2 a
  rw [GQ2.Dyadic.Certificates.MProcyclic.mult_zmod2_even_zpow a heven,
    hsem] at H
  exact GQ2.Dyadic.SqCore.ofAdd_one_ne_one_multZMod2 H.symm

/-- The prime-to-two correction contributes no mod-two exponent in any letter slot. -/
theorem heisEps_tamePrimeToTwoCorrectedWord_eq
    {n q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q)
    (i : Generator n) :
    heisEps i (heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q)
      (tamePrimeToTwoCorrectedWord hq0 hqe R hR)) =
    heisEps i (heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q) R) := by
  rw [tamePrimeToTwoCorrectedWord, heisToFree, PWord.evalZ_mul,
    PWord.evalZ_inv, PWord.evalZ_profPow, PWord.evalZ_gen,
    map_mul, map_inv, map_zpow]
  rw [stokesZhatResolver_pow_eq_one_of_maxProPMk_eq_one]
  · simp
  · exact maxProPMk_tamePrimeToTwoCorrectionExponent hq0 hqe R hR

/-- Prime-to-two tame correction preserves the endpoint of a two-relator family. -/
theorem isStokesEndpoint_primeToTwoCorrection
    {n q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q)
    (hend : IsStokesEndpoint (fun k : Fin 2 ↦
      heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q)
        (gammaFam n q R k))) :
    IsStokesEndpoint (fun k : Fin 2 ↦
      heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q)
        (gammaFam n q (tamePrimeToTwoCorrectedWord hq0 hqe R hR) k)) := by
  intro i
  have H := hend i
  rw [Fin.sum_univ_two] at H ⊢
  change Multiplicative.toAdd (heisEps i
      (heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q)
        (tameRelW n q))) +
    Multiplicative.toAdd (heisEps i
      (heisToFree (stokesZhatResolver Q) (stokesZtwoResolver Q)
        (tamePrimeToTwoCorrectedWord hq0 hqe R hR))) = 0
  rw [heisEps_tamePrimeToTwoCorrectedWord_eq]
  exact H

#print axioms stokesZhatResolver_spec
#print axioms resolvedAt_stokesResolvers
#print axioms resolvesAt_stokesResolvers
#print axioms stokesZhatResolver_pow_eq_one_of_maxProPMk_eq_one
#print axioms stokesZhatResolver_omega2_odd
#print axioms heisEps_tamePrimeToTwoCorrectedWord_eq
#print axioms isStokesEndpoint_primeToTwoCorrection

end FiniteTarget

end

end GQ2.Dyadic
