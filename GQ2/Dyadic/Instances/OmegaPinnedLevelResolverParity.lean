/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.OmegaPinnedLevelResolver

/-!
# Prime-to-two exponent divisibility at a pinned finite level

The cyclic group of order `2^a` detects the entire `2^a`-divisibility of a resolved exponent,
not just its parity. If `2^a` divides the chosen level, a profinite exponent with trivial
maximal pro-2 component resolves to an integer divisible by `2^a`. In particular the
prime-to-two tame correction resolves to a multiple of four at every level divisible by four.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.Dyadic.Count

theorem omegaPinnedLevelZhatResolver_twoPow_dvd_of_primeToTwo
    {N a : ℕ} (hN : N ≠ 0) (ha : 2 ^ a ∣ N) {gamma : Zhat}
    (hgamma : maxProPMk 2 Zhat gamma = 1) :
    ((2 ^ a : ℕ) : ℤ) ∣ omegaPinnedLevelZhatResolver N gamma := by
  let x := CycTest.gen (2 ^ a)
  have hpro : IsProP 2 (CycTest (2 ^ a)) := by
    apply isProP_of_isPGroup
    intro y
    exact ⟨a, orderOf_dvd_iff_pow_eq_one.mp (CycTest.orderOf_dvd (2 ^ a) y)⟩
  have H := omegaPinnedLevelZhatResolver_spec hN
    (fun y : CycTest (2 ^ a) ↦ (CycTest.orderOf_dvd (2 ^ a) y).trans ha) gamma x
  rw [zpowHat_eq_one_of_maxProPMk_eq_one hpro x hgamma] at H
  change Multiplicative.ofAdd ((omegaPinnedLevelZhatResolver N gamma : ℤ) •
    (1 : ZMod (2 ^ a))) = Multiplicative.ofAdd 0 at H
  have Hz : (omegaPinnedLevelZhatResolver N gamma : ZMod (2 ^ a)) = 0 := by
    simpa using Multiplicative.ofAdd.injective H
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp Hz

theorem omegaPinnedLevelZhatResolver_four_dvd_primeToTwo
    {N : ℕ} (hN : N ≠ 0) (hfour : 4 ∣ N) {gamma : Zhat}
    (hgamma : maxProPMk 2 Zhat gamma = 1) :
    (4 : ℤ) ∣ omegaPinnedLevelZhatResolver N gamma := by
  exact omegaPinnedLevelZhatResolver_twoPow_dvd_of_primeToTwo (a := 2) hN hfour hgamma

theorem omegaPinnedLevelZhatResolver_four_dvd_tameCorrection
    {n q N : ℕ} (hN : N ≠ 0) (hfour : 4 ∣ N)
    (hq0 : q ≠ 0) (hqe : Even q) (R : PWord (Generator n))
    (hR : (tameMarking n q).eval R ∈ inertiaPartQ q) :
    (4 : ℤ) ∣ omegaPinnedLevelZhatResolver N
      (tamePrimeToTwoCorrectionExponent hq0 hqe R hR) :=
  omegaPinnedLevelZhatResolver_four_dvd_primeToTwo hN hfour
    (maxProPMk_tamePrimeToTwoCorrectionExponent hq0 hqe R hR)

#print axioms omegaPinnedLevelZhatResolver_twoPow_dvd_of_primeToTwo
#print axioms omegaPinnedLevelZhatResolver_four_dvd_primeToTwo
#print axioms omegaPinnedLevelZhatResolver_four_dvd_tameCorrection

end
end GQ2.Dyadic
