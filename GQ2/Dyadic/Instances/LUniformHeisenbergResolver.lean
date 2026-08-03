/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.Frozen
import GQ2.FoxHeisenberg.Traced

/-!
# A coefficient-independent L Heisenberg resolver

The target-local resolver in `LHeisenbergResolver` uses the exact exponent of
`HeisLift A C`.  That is optimal for a single coefficient module, but its displayed word changes
with `A`.  Simple devissage instead needs one fixed word while the elementary coefficient module
varies.

This file supplies the uniform level `4 * Monoid.exponent C`.  Every element of
`HeisLift A C` has order dividing this level when `A` is killed by two: its primal and dual
projections are killed by `2 * Monoid.exponent C`, and squaring once more kills the remaining
central `ZMod 2` coordinate.  Consequently the L word at
`omega2Exp (4 * Monoid.exponent C)` resolves every such Heisenberg target.  The level depends
only on the fixed finite quotient `C`, so the same word can be used for all simple constituents
in a coefficient devissage.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2 GQ2.FoxH

/-- If the elementary coefficient group `A` is killed by two and all element orders in `C`
divide `N`, then every element of `HeisLift A C` has order dividing `4 * N`.

The extra factor two beyond the split-lift bound kills the central Heisenberg coordinate. -/
theorem orderOf_heisLift_dvd_four_mul
    {C A : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]
    (hA₂ : ∀ a : A, a + a = 0) {N : ℕ}
    (hbase : ∀ g : C, orderOf g ∣ N) (p : HeisLift A C) :
    orderOf p ∣ 4 * N := by
  apply orderOf_dvd_of_pow_eq_one
  let m := 2 * N
  have hag : (agHom p) ^ m = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      (WordLift.orderOf_dvd_two_mul hA₂ hbase (agHom p))
  have hlg : (lgHom p) ^ m = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      (WordLift.orderOf_dvd_two_mul
        (fun lam : ElemDual A ↦ lam.add_self_eq_zero) hbase (lgHom p))
  have ha : (p ^ m).a = 0 := by
    have hag' : agHom (p ^ m) = 1 := by simpa only [map_pow] using hag
    exact congrArg WordLift.u hag'
  have hl : (p ^ m).l = 0 := by
    have hlg' : lgHom (p ^ m) = 1 := by simpa only [map_pow] using hlg
    exact congrArg WordLift.u hlg'
  have hg : (p ^ m).g = 1 := by
    have hag' : agHom (p ^ m) = 1 := by simpa only [map_pow] using hag
    exact congrArg WordLift.g hag'
  have hsq : (p ^ m) * (p ^ m) = 1 := by
    ext
    · simp [ha, hg, hA₂]
    · simp [hl, hg]
    · simp [ha, hl, hg, CharTwo.add_self_eq_zero]
    · simp [hg]
  calc
    p ^ (4 * N) = p ^ (m + m) := by congr 1; omega
    _ = (p ^ m) * (p ^ m) := pow_add p m m
    _ = 1 := hsq

/-- The uniform level `4 * exponent C` is nonzero and even for every finite group `C`. -/
theorem fourMulExponent_ne_zero_and_even
    (C : Type*) [Group C] [Finite C] :
    4 * Monoid.exponent C ≠ 0 ∧
      (4 * Monoid.exponent C).factorization 2 ≠ 0 := by
  have he : Monoid.exponent C ≠ 0 := Monoid.exponent_ne_zero_of_finite
  refine ⟨Nat.mul_ne_zero (by norm_num) he, ?_⟩
  have hdvd : 2 ∣ 4 * Monoid.exponent C := by omega
  exact (Nat.Prime.factorization_pos_of_dvd Nat.prime_two
    (Nat.mul_ne_zero (by norm_num) he) hdvd).ne'

local instance uniformHeisTopology
    {C A : Type} [Group C] [AddCommGroup A] : TopologicalSpace (HeisLift A C) := ⊥

local instance uniformHeisDiscrete
    {C A : Type} [Group C] [AddCommGroup A] : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

/-- The L word at the uniform level resolves `HeisLift A C` for every elementary finite
coefficient module `A`.  Its exponent parameter mentions only `C`, which lets a devissage keep
the presentation word fixed while changing coefficients. -/
theorem resolvesAt_lSqFam_uniformHeis
    {C A : Type} [Group C] [Finite C] [AddCommGroup A]
    [DistribMulAction C A] [Finite A] (hA₂ : ∀ a : A, a + a = 0) (h q : ℕ) :
    ResolvesAt
      (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q
        (omega2Exp (4 * Monoid.exponent C)))
      (HeisLift A C) :=
  resolvesAt_lSqFam (fourMulExponent_ne_zero_and_even C).1
    (orderOf_heisLift_dvd_four_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g)) h q

/-- At even `q`, the uniform L word is simultaneously a resolver for the Heisenberg target and
a Stokes endpoint.  This is the matched pair needed by fixed-word simple devissage. -/
theorem resolvesAt_and_endpoint_lSqFam_uniformHeis
    {C A : Type} [Group C] [Finite C] [AddCommGroup A]
    [DistribMulAction C A] [Finite A] (hA₂ : ∀ a : A, a + a = 0)
    {h q : ℕ} (hq : Even q) :
    ResolvesAt
        (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (4 * Monoid.exponent C)))
        (HeisLift A C) ∧
      IsStokesEndpoint
        (Certificates.LSqStokes.lSqFam h q
          (omega2Exp (4 * Monoid.exponent C))) :=
  ⟨resolvesAt_lSqFam_uniformHeis hA₂ h q,
    Certificates.LSqStokes.lSq_isStokesEndpoint hq
      (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
        (fourMulExponent_ne_zero_and_even C).2)⟩

end

end GQ2.Dyadic.Count
