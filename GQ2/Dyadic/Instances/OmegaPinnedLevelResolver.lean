/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FiniteLevelProfiniteResolver
import GQ2.Dyadic.Instances.N0M0UniformHeisenbergResolver
import GQ2.Dyadic.Instances.NpcUnramifiedScalar
import GQ2.Dyadic.SelectedEta

/-!
# A level resolver with the positive omega representative pinned

The generic finite-level resolver computes every exponent, but its representative at omega2
need not be a nonnegative integer. Second-order M rows use the natural representative
`omega2Exp N`, which is 1 modulo 4 at the coefficient-independent level `4 * exponent C`.
Pin just that exponent, retaining the generic level resolver elsewhere. The Z2 resolver is
obtained from the same pinned function, so coincident profinite nodes remain consistent.

All words resolve at every finite target killed by N. In particular the Heisenberg targets
are uniformly resolved at `4 * exponent C`, independently of the coefficient module. The
semantic eta exponent of any 2-adic unit has an odd resolved integer representative.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Certificates.MProcyclic

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

def omegaPinnedLevelZhatResolver (N : ℕ) (gamma : Zhat) : ℤ := by
  classical
  exact if gamma = omega2 then (omega2Exp N : ℤ) else levelStokesZhatResolver N gamma

def omegaPinnedLevelZtwoResolver (N : ℕ) (z : ℤ_[2]) : ℤ :=
  omegaPinnedLevelZhatResolver N (padicOmega2 z)

@[simp] theorem omegaPinnedLevelZhatResolver_omega2 (N : ℕ) :
    omegaPinnedLevelZhatResolver N omega2 = (omega2Exp N : ℤ) := by
  simp [omegaPinnedLevelZhatResolver]

theorem omegaPinnedLevelZhatResolver_spec
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N)
    (gamma : Zhat) (x : Q) :
    x ^ omegaPinnedLevelZhatResolver N gamma = x ^ᶻ gamma := by
  by_cases hgamma : gamma = omega2
  · subst gamma
    rw [omegaPinnedLevelZhatResolver_omega2]
    exact (PWord.zpowHat_omega2_zpow hN (hord x)).symm
  · rw [omegaPinnedLevelZhatResolver, if_neg hgamma]
    exact levelStokesZhatResolver_spec hN hord gamma x

theorem resolvedAt_omegaPinnedLevelResolvers
    {X Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N)
    (mu : X → Q) (w : PWord X) :
    PWord.ResolvedAt mu (omegaPinnedLevelZhatResolver N)
      (omegaPinnedLevelZtwoResolver N) w := by
  induction w with
  | one => trivial
  | gen g => trivial
  | mul u v ihu ihv => exact ⟨ihu, ihv⟩
  | inv u ih => exact ih
  | conj u g ihu ihg => exact ⟨ihu, ihg⟩
  | comm u v ihu ihv => exact ⟨ihu, ihv⟩
  | zpow u k ih => exact ih
  | z2pow u z ih =>
      exact ⟨ih, (omegaPinnedLevelZhatResolver_spec hN hord (padicOmega2 z)
        (PWord.eval mu u)).symm⟩
  | profPow u gamma ih =>
      exact ⟨ih, (omegaPinnedLevelZhatResolver_spec hN hord gamma (PWord.eval mu u)).symm⟩

theorem resolvesAt_omegaPinnedLevelResolvers
    {X rho Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N)
    (W : rho → PWord X) :
    ResolvesAt W
      (fun k ↦ heisToFree (omegaPinnedLevelZhatResolver N)
        (omegaPinnedLevelZtwoResolver N) (W k)) Q :=
  resolvesAt_of_resolvedAt fun f k ↦ resolvedAt_omegaPinnedLevelResolvers hN hord f (W k)

theorem omegaPinnedLevelZhatResolver_fourMulExponent_wordLift
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [DistribMulAction C A]
    (hA₂ : ∀ a : A, a + a = 0) :
    ResolverLifts (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C)) (WordLift A C) := by
  intro x
  rw [omegaPinnedLevelZhatResolver_omega2, zpow_natCast]
  exact powOmega2_pow_eq x
    ((WordLift.orderOf_dvd_two_mul hA₂ (fun c : C ↦ Monoid.order_dvd_exponent c) x).trans
      ⟨2, by ring⟩) (fourMulExponent_ne_zero_and_even C).1

theorem omegaPinnedLevelZhatResolver_fourMulExponent_base
    (C : Type*) [Group C] [Finite C] :
    ResolverLifts (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C)) C := by
  intro x
  rw [omegaPinnedLevelZhatResolver_omega2, zpow_natCast]
  exact powOmega2_pow_eq x ((Monoid.order_dvd_exponent x).trans ⟨4, by ring⟩)
    (fourMulExponent_ne_zero_and_even C).1

theorem resolvesAt_omegaPinnedLevelResolvers_heis
    {X rho C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] (hA₂ : ∀ a : A, a + a = 0)
    (W : rho → PWord X) :
    ResolvesAt W
      (fun k ↦ heisToFree (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)) (W k)) (HeisLift A C) :=
  resolvesAt_omegaPinnedLevelResolvers (fourMulExponent_ne_zero_and_even C).1
    (orderOf_heisLift_dvd_four_mul hA₂ (fun c : C ↦ Monoid.order_dvd_exponent c)) W

theorem omegaPinnedLevelZhatResolver_etaHatZ_odd
    {N : ℕ} (hN : N ≠ 0) (eta : ℤ_[2]ˣ) :
    Odd (omegaPinnedLevelZhatResolver N (etaHatZ (eta : ℤ_[2]))) := by
  letI : NeZero N := ⟨hN⟩
  let x : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  have hcorrect : x ^ omegaPinnedLevelZhatResolver N (etaHatZ (eta : ℤ_[2])) =
      x ^ᶻ etaHatZ (eta : ℤ_[2]) := by
    rw [omegaPinnedLevelZhatResolver, if_neg (Words.Npc.etaHatZ_ne_omega2 _)]
    simpa [levelStokesZhatResolver, hN] using
      stokesZhatResolver_zmod2_spec (CycTest N) (etaHatZ (eta : ℤ_[2])) x
  obtain ⟨z, hz⟩ := exists_padicUnit_eq_one_add_two_mul eta
  obtain ⟨c, hc⟩ := NProcyclicUnram.even_padicOmega2Exp_of_oneUnit z hz (orderOf x)
  have hx2 : x ^ 2 = 1 := by decide
  have hsem : x ^ᶻ etaHatZ (eta : ℤ_[2]) = x := by
    rw [zpowHat_etaHatZ, hc, ← two_mul, pow_mul, hx2, one_pow, mul_one]
  rw [hsem] at hcorrect
  apply Int.not_even_iff_odd.mp
  intro heven
  rw [mult_zmod2_even_zpow x heven] at hcorrect
  exact GQ2.Dyadic.SqCore.ofAdd_one_ne_one_multZMod2 hcorrect.symm

#print axioms omegaPinnedLevelZhatResolver_spec
#print axioms resolvesAt_omegaPinnedLevelResolvers
#print axioms omegaPinnedLevelZhatResolver_fourMulExponent_wordLift
#print axioms omegaPinnedLevelZhatResolver_fourMulExponent_base
#print axioms resolvesAt_omegaPinnedLevelResolvers_heis
#print axioms omegaPinnedLevelZhatResolver_etaHatZ_odd

end
end GQ2.Dyadic
