/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Count.ProTwo

/-!
# The canonical two-adic exponent on pro-two groups

The semantic exponent `padicOmega2 u : Zhat` acts on every pro-`2` profinite group by
ordinary `Z_2`-powering by `u`.  The proof is quotientwise and independent of every dyadic
presentation branch.
-/

namespace GQ2.Dyadic.PadicOmegaProTwo

open GQ2

noncomputable section

private theorem zpowZtwo_eq_pow_toZModPow {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) (k : ℕ) (hx : x ^ (2 ^ k) = 1) (u : ℤ_[2]) :
    zpowZtwo hP x u = x ^ (PadicInt.toZModPow k u).val := by
  have h := zpowZtwoHom_unique hP (φ := powZModTwoHom x k hx)
    (continuous_powZModTwoHom x k hx) u
  have hone : powZModTwoHom x k hx (Multiplicative.ofAdd (1 : ℤ_[2])) = x := by
    show x ^ (PadicInt.toZModPow k
      (Multiplicative.ofAdd (1 : ℤ_[2])).toAdd).val = x
    rw [show (Multiplicative.ofAdd (1 : ℤ_[2])).toAdd = (1 : ℤ_[2]) from rfl,
      map_one]
    by_cases hk : k = 0
    · have hx1 : x = 1 := by simpa [hk] using hx
      simp [hx1]
    · rw [ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (Nat.one_lt_two_pow_iff.mpr hk), pow_one]
  rw [hone] at h
  exact h.symm

/-- The semantic lift `padicOmega2 u` acts on a pro-`2` group by `Z_2`-powering. -/
theorem zpowHat_padicOmega2_eq_zpowZtwo {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) (u : ℤ_[2]) :
    x ^ᶻ padicOmega2 u = zpowZtwo hP x u := by
  apply mul_inv_eq_one.mp
  refine eq_one_of_forall_mem_openNormalSubgroup fun U => ?_
  let q : ContinuousMonoidHom P (P ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩
  haveI : DiscreteTopology (P ⧸ U.toSubgroup) := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hpre : (QuotientGroup.mk : P → P ⧸ U.toSubgroup) ⁻¹' {1} =
        (U.toSubgroup : Set P) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
        QuotientGroup.eq_one_iff]
    rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
    exact U.isOpen'
  haveI : Finite (P ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ U.isOpen'
  have hQU : IsProP 2 (P ⧸ U.toSubgroup) := isProP_of_isPGroup (hP U)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (hP U)) (q x)
  have heq : q (x ^ᶻ padicOmega2 u) = q (zpowZtwo hP x u) := by
    by_cases hk0 : k = 0
    · have hqx : q x = 1 := orderOf_eq_one_iff.mp (by simpa [hk0] using hk)
      rw [map_zpowHat, zpowHat_padicOmega2, hqx, one_pow,
        map_zpowZtwo hP hQU, hqx, zpowZtwo_one_base]
    · have hpow : (q x) ^ (2 ^ k) = 1 := by rw [← hk, pow_orderOf_eq_one]
      have homega : omega2Exp (2 ^ k) = 1 := by
        have hfac : (2 ^ k).factorization 2 = k := by
          rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
        have hpos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
        have hlt : (1 : ℕ) < 2 ^ k := Nat.one_lt_two_pow_iff.mpr hk0
        rw [omega2Exp]
        simp only [hfac, if_neg hk0, Nat.div_self hpos, one_pow,
          Nat.mod_eq_of_lt hlt]
      have hleft : q (x ^ᶻ padicOmega2 u) =
          (q x) ^ (PadicInt.toZModPow k u).val := by
        rw [map_zpowHat, zpowHat_padicOmega2, hk, padicOmega2Exp,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
          homega, mul_one]
      have hright : q (zpowZtwo hP x u) =
          (q x) ^ (PadicInt.toZModPow k u).val := by
        rw [map_zpowZtwo hP hQU]
        exact zpowZtwo_eq_pow_toZModPow hQU (q x) k hpow u
      exact hleft.trans hright.symm
  have hone : q ((x ^ᶻ padicOmega2 u) * (zpowZtwo hP x u)⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  have hone' : (((x ^ᶻ padicOmega2 u) * (zpowZtwo hP x u)⁻¹ : P) :
      P ⧸ U.toSubgroup) = 1 := by
    change q ((x ^ᶻ padicOmega2 u) * (zpowZtwo hP x u)⁻¹) = 1
    exact hone
  exact (QuotientGroup.eq_one_iff _).mp hone'

#print axioms zpowHat_padicOmega2_eq_zpowZtwo

end


end GQ2.Dyadic.PadicOmegaProTwo
