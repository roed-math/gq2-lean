/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.LUniformHeisenbergResolver

/-!
# Coefficient-independent Heisenberg resolvers for the two compact even rows

`LUniformHeisenbergResolver` supplies the uniform level `4 * Monoid.exponent C` for the `L`
row: every element of `HeisLift A C` has order dividing that level whenever the elementary
coefficient module `A` is killed by two, so the `L` word at `omega2Exp (4 * Monoid.exponent C)`
resolves the whole Heisenberg target while the coefficient module varies.

The level fact `orderOf_heisLift_dvd_four_mul` is about the Heisenberg target alone, not about
any branch word, and `resolvesAt_and_endpoint_nCompactFam` / `resolvesAt_and_endpoint_mCompactFam`
are already generic in the level.  This file therefore records the same matched
`(resolver, endpoint)` pair for the compact-`N` and compact-`M` rows, which is what a fixed-word
simple devissage on those rows needs.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Certificates

local instance compactUniformHeisTopology
    {C A : Type} [Group C] [AddCommGroup A] : TopologicalSpace (HeisLift A C) := ⊥

local instance compactUniformHeisDiscrete
    {C A : Type} [Group C] [AddCommGroup A] : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

/-- The compact-`N` word at the uniform level resolves `HeisLift A C` for every elementary
finite coefficient module `A`.  Its exponent parameter mentions only `C`. -/
theorem resolvesAt_nCompactFam_uniformHeis
    {C A : Type} [Group C] [Finite C] [AddCommGroup A]
    [DistribMulAction C A] [Finite A] (hA₂ : ∀ a : A, a + a = 0) (α h q : ℕ) :
    ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.nCompactW α h))
      (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
      (HeisLift A C) :=
  resolvesAt_nCompactFam (fourMulExponent_ne_zero_and_even C).1
    (orderOf_heisLift_dvd_four_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g)) α h q

/-- At even `q` the uniform compact-`N` word is simultaneously a Heisenberg resolver and a
Stokes endpoint: the matched pair a fixed-word simple devissage consumes. -/
theorem resolvesAt_and_endpoint_nCompactFam_uniformHeis
    {C A : Type} [Group C] [Finite C] [AddCommGroup A]
    [DistribMulAction C A] [Finite A] (hA₂ : ∀ a : A, a + a = 0)
    {α h q : ℕ} (hα : 1 ≤ α) (hq : Even q) :
    ResolvesAt
        (gammaFam (2 + 2 * h) q (Words.nCompactW α h))
        (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
        (HeisLift A C) ∧
      IsStokesEndpoint (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) :=
  resolvesAt_and_endpoint_nCompactFam (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
    (orderOf_heisLift_dvd_four_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g)) hα hq

/-- At the uniform level, the resolver is `1` modulo `4`, not merely odd.

The compact-`M` second-order row is assembled only at the honest resolver class `e % 4 = 1`
(its `𝓔`-correction block is not exact in `e`, unlike the compact-`N` row), so this is the
side condition that lets that row be read at the uniform word.  It holds because
`v₂ (4 * Monoid.exponent C) ≥ 2` and `ω₂` is `1` modulo the whole two-part. -/
theorem omega2Exp_fourMulExponent_mod_four (C : Type*) [Group C] [Finite C] :
    omega2Exp (4 * Monoid.exponent C) % 4 = 1 := by
  have he : Monoid.exponent C ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have hN : 4 * Monoid.exponent C ≠ 0 := Nat.mul_ne_zero (by norm_num) he
  have hfac : (4 * Monoid.exponent C).factorization 2
      = 2 + (Monoid.exponent C).factorization 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
      Nat.factorization_mul (by norm_num) he, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hle : 2 ≤ (4 * Monoid.exponent C).factorization 2 := by omega
  have hv : (4 * Monoid.exponent C).factorization 2 ≠ 0 := by omega
  have hdvd : (4 : ℕ) ∣ 2 ^ (4 * Monoid.exponent C).factorization 2 := by
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [← h4]
    exact pow_dvd_pow 2 hle
  have hmod := (omega2Exp_modEq_one hN hv).of_dvd hdvd
  simpa [Nat.ModEq] using hmod

/-- The compact-`M` word at the uniform level resolves `HeisLift A C` for every elementary
finite coefficient module `A`. -/
theorem resolvesAt_mCompactFam_uniformHeis
    {C A : Type} [Group C] [Finite C] [AddCommGroup A]
    [DistribMulAction C A] [Finite A] (hA₂ : ∀ a : A, a + a = 0) (α h q : ℕ) :
    ResolvesAt
      (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h))
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
      (HeisLift A C) :=
  resolvesAt_mCompactFam (fourMulExponent_ne_zero_and_even C).1
    (orderOf_heisLift_dvd_four_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g)) α h q

/-- At even `q` the uniform compact-`M` word is simultaneously a Heisenberg resolver and a
Stokes endpoint. -/
theorem resolvesAt_and_endpoint_mCompactFam_uniformHeis
    {C A : Type} [Group C] [Finite C] [AddCommGroup A]
    [DistribMulAction C A] [Finite A] (hA₂ : ∀ a : A, a + a = 0)
    {α h q : ℕ} (hq : Even q) :
    ResolvesAt
        (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h))
        (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
        (HeisLift A C) ∧
      IsStokesEndpoint (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C))) :=
  resolvesAt_and_endpoint_mCompactFam (fourMulExponent_ne_zero_and_even C).1
    (fourMulExponent_ne_zero_and_even C).2
    (orderOf_heisLift_dvd_four_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g)) hq

end

end GQ2.Dyadic.Count
