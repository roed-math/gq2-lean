/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateRelativeFrobeniusUniformizer

/-!
# The pro-two Frobenius coordinate does not determine the full profinite coordinate

W190 isolates the abstract uniformizer normalization in `Zhat`.  AX4 already fixes its maximal
pro-`2` image, but that fact alone cannot determine the full value.  This module makes the gap
formal: `omega2⁻¹` and `Zhat.ofInt (-1)` are distinct lifts of `ztwoOne⁻¹`.

The equality after pro-`2` projection is the defining property of `omega2`.  Distinctness is
detected in the odd quotient `Multiplicative (ZMod 3)`, where `omega2` acts by the zeroth power
while `Zhat.ofInt 1` acts by the first power.  Thus the remaining W190 normalization really
requires odd-primary Frobenius/reciprocity information; it cannot be recovered from AX4's
pro-`2` coordinate.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open Multiplicative

/-- `omega2` and the integer exponent `1` have the same `2`-adic projection. -/
theorem zhatProjTwo_omega2_eq_ofInt_one :
    zhatProjTwo omega2 = zhatProjTwo (Zhat.ofInt 1) := by
  change (ofAdd (1 : ℤ_[2])) ^ᶻ omega2 =
    (ofAdd (1 : ℤ_[2])) ^ᶻ Zhat.ofInt 1
  rw [zpowHat_omega2_eq_self PropOneOne.isProP_two_multPadicInt,
    zpowHat_ofInt, zpow_one]

/-- The maximal pro-`2` quotient identifies `omega2` with the integer exponent `1`. -/
theorem maxProPMk_omega2_eq_ofInt_one :
    maxProPMk 2 Zhat omega2 = maxProPMk 2 Zhat (Zhat.ofInt 1) := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  rw [← ker_zhatProjTwo]
  apply MonoidHom.mem_ker.mpr
  rw [map_div]
  change zhatProjTwo omega2 / zhatProjTwo (Zhat.ofInt 1) = 1
  rw [zhatProjTwo_omega2_eq_ofInt_one, div_eq_mul_inv]
  exact mul_inv_cancel _

/-- The odd component distinguishes `omega2` from the integer exponent `1`. -/
theorem omega2_ne_ofInt_one : omega2 ≠ Zhat.ofInt 1 := by
  intro h
  have hh := congrArg
    (fun γ : Zhat => (ofAdd (1 : ZMod 3)) ^ᶻ γ) h
  rw [zpowHat_omega2, zpowHat_ofInt, zpow_one] at hh
  have homega : omega2Exp 3 = 0 := by
    have hfac : (3 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [omega2Exp, hfac]
  rw [show powOmega2 (ofAdd (1 : ZMod 3)) = 1 by
    simp [powOmega2, homega]] at hh
  exact (by decide : (1 : Multiplicative (ZMod 3)) ≠ ofAdd 1) hh

/-- The two lifts relevant to the geometric uniformizer value are distinct. -/
theorem omega2_inv_ne_ofInt_neg_one :
    omega2⁻¹ ≠ Zhat.ofInt (-1) := by
  intro h
  apply omega2_ne_ofInt_one
  have hi := congrArg Inv.inv h
  rw [← Zhat.ofInt_one_zpow] at hi
  simpa using hi

/-- The inverse of `omega2` lifts AX4's geometric pro-`2` generator. -/
theorem maxProPMk_omega2_inv :
    maxProPMk 2 Zhat omega2⁻¹ = ztwoOne⁻¹ := by
  rw [map_inv, maxProPMk_omega2_eq_ofInt_one]
  rfl

/-- The desired integer exponent `-1` lifts the same pro-`2` generator. -/
theorem maxProPMk_ofInt_neg_one :
    maxProPMk 2 Zhat (Zhat.ofInt (-1)) = ztwoOne⁻¹ := by
  rw [← Zhat.ofInt_one_zpow, map_zpow]
  rfl

/-- The maximal pro-`2` projection of `Zhat` is not injective. -/
theorem maxProPMk_zhat_not_injective :
    ¬ Function.Injective (maxProPMk 2 Zhat) := by
  intro hinj
  exact omega2_inv_ne_ofInt_neg_one
    (hinj (maxProPMk_omega2_inv.trans
      maxProPMk_ofInt_neg_one.symm))

/-- AX4's known target `ztwoOne⁻¹` has two explicit distinct lifts in `Zhat`. -/
theorem exists_distinct_lifts_ztwoOne_inv :
    ∃ γ δ : Zhat,
      γ ≠ δ ∧
      maxProPMk 2 Zhat γ = ztwoOne⁻¹ ∧
      maxProPMk 2 Zhat δ = ztwoOne⁻¹ := by
  exact ⟨omega2⁻¹, Zhat.ofInt (-1),
    omega2_inv_ne_ofInt_neg_one,
    maxProPMk_omega2_inv,
    maxProPMk_ofInt_neg_one⟩

#print axioms zhatProjTwo_omega2_eq_ofInt_one
#print axioms maxProPMk_omega2_eq_ofInt_one
#print axioms omega2_ne_ofInt_one
#print axioms omega2_inv_ne_ofInt_neg_one
#print axioms maxProPMk_omega2_inv
#print axioms maxProPMk_ofInt_neg_one
#print axioms maxProPMk_zhat_not_injective
#print axioms exists_distinct_lifts_ztwoOne_inv

end
end GQ2.Dyadic
