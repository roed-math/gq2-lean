/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import GQ2.Words

@[expose] public section

/-!
# The `ω₂` exponent: specification and Appendix-B cross-check

`GQ2.omega2Exp n` is our concrete integer representative of the profinite idempotent `ω₂` modulo
`n`. This file proves it satisfies the two congruences that *define* `ω₂` — `≡ 1` on the 2-part and
`≡ 0` on the odd part — and cross-checks it against the paper's Appendix B serialization.
-/

namespace GQ2

open scoped Classical

/-- The odd part of `n` divides `omega2Exp n` (the "`ω₂ ≡ 0` on the odd part" condition). -/
theorem oddPart_dvd_omega2Exp (n : ℕ) :
    (n / 2 ^ n.factorization 2) ∣ omega2Exp n := by
  unfold omega2Exp
  by_cases haz : n.factorization 2 = 0
  · simp [haz]
  · simp only [haz, if_false]
    rw [Nat.dvd_mod_iff (Nat.div_dvd_of_dvd (Nat.ordProj_dvd n 2))]
    exact dvd_pow_self _ (by positivity)

/-- `omega2Exp n ≡ 1` modulo the 2-part `2 ^ v₂(n)` (the "`ω₂ ≡ 1` on the 2-part" condition),
for `n` with a nontrivial 2-part.  Uses Euler's theorem: the odd part is a unit mod `2^a`, and
`2^(a-1) = φ(2^a)`. -/
theorem omega2Exp_modEq_one {n : ℕ} (hn : n ≠ 0) (ha : n.factorization 2 ≠ 0) :
    omega2Exp n ≡ 1 [MOD 2 ^ n.factorization 2] := by
  set a := n.factorization 2 with hadef
  have h2a : 2 ^ a ∣ n := Nat.ordProj_dvd n 2
  -- `x % n ≡ x` modulo `2^a` since `2^a ∣ n`.
  have hmodn : omega2Exp n ≡ (n / 2 ^ a) ^ (2 ^ (a - 1)) [MOD 2 ^ a] := by
    unfold omega2Exp
    simp only [← hadef, ha, if_false]
    exact (Nat.mod_modEq _ _).of_dvd h2a
  -- The odd part is coprime to `2^a`, so Euler applies with `φ(2^a) = 2^(a-1)`.
  have hnd : ¬ (2 : ℕ) ∣ (n / 2 ^ a) := Nat.not_dvd_ordCompl Nat.prime_two hn
  have hcop : Nat.Coprime (n / 2 ^ a) (2 ^ a) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hnd).symm).pow_right a
  have htot : Nat.totient (2 ^ a) = 2 ^ (a - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.pos_of_ne_zero ha)]; simp
  exact hmodn.trans (htot ▸ Nat.ModEq.pow_totient hcop)

/-- **Compatibility of the `ω₂` exponents across levels.**  For `N ∣ M` (`M ≠ 0`), the exponents
at levels `M` and `N` agree modulo `N`: `omega2Exp M ≡ omega2Exp N [MOD N]`.  This is the
coherence making the family `(omega2Exp N)_N` a well-defined element `ω₂` of `ℤ̂ = lim ℤ/N`
(see `GQ2.omega2`): both sides are `≡ 1` on the 2-part of `N` and `≡ 0` on its odd part, and CRT
combines the two congruences over the coprime factorisation `N = 2^{v₂ N} · (N / 2^{v₂ N})`. -/
theorem omega2Exp_modEq {N M : ℕ} (hdvd : N ∣ M) (hM : M ≠ 0) :
    omega2Exp M ≡ omega2Exp N [MOD N] := by
  have hN : N ≠ 0 := ne_zero_of_dvd_ne_zero hM hdvd
  -- Congruent modulo the 2-part `2 ^ v₂(N)` (both `≡ 1`).
  have h2 : omega2Exp M ≡ omega2Exp N [MOD 2 ^ N.factorization 2] := by
    by_cases hα : N.factorization 2 = 0
    · rw [hα, pow_zero]; exact Nat.modEq_one
    · have hle : N.factorization 2 ≤ M.factorization 2 :=
        (Nat.factorization_le_iff_dvd hN hM).mpr hdvd 2
      exact ((omega2Exp_modEq_one hM (by lia)).of_dvd (pow_dvd_pow 2 hle)).trans
        (omega2Exp_modEq_one hN hα).symm
  -- Congruent modulo the odd part `N / 2 ^ v₂(N)` (both `≡ 0`).
  have hodd : omega2Exp M ≡ omega2Exp N [MOD N / 2 ^ N.factorization 2] := by
    have e1 : (N / 2 ^ N.factorization 2) ∣ omega2Exp N := oddPart_dvd_omega2Exp N
    have e2 : (N / 2 ^ N.factorization 2) ∣ omega2Exp M :=
      (Nat.ordCompl_dvd_ordCompl_of_dvd hdvd 2).trans (oddPart_dvd_omega2Exp M)
    exact (Nat.modEq_zero_iff_dvd.mpr e2).trans (Nat.modEq_zero_iff_dvd.mpr e1).symm
  -- CRT: combine over the coprime factorisation `N = 2^{v₂ N} · (N / 2^{v₂ N})`.
  have hcop : Nat.Coprime (2 ^ N.factorization 2) (N / 2 ^ N.factorization 2) :=
    Nat.Coprime.pow_left _
      ((Nat.prime_two.coprime_iff_not_dvd).mpr (Nat.not_dvd_ordCompl Nat.prime_two hN))
  have hcrt := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, hodd⟩
  rwa [Nat.ordProj_mul_ordCompl_eq_self N 2] at hcrt

/-- **`ω₂` is well-defined via any exponent multiple.**  For `x` of finite order dividing `N`
(`N ≠ 0`), `x ^ (omega2Exp N) = powOmega2 x`.  So `powOmega2` really is *the* 2-primary
projection: the choice of modulus `orderOf x` in its definition is immaterial, as long as the
modulus is a multiple of `orderOf x`.  (This is what makes `powOmega2` behave coordinatewise on
products, cf. `powOmega2_prod`.) -/
theorem powOmega2_pow_eq {G : Type*} [Group G] (x : G) {N : ℕ}
    (hdvd : orderOf x ∣ N) (hN : N ≠ 0) : x ^ omega2Exp N = powOmega2 x :=
  pow_eq_pow_iff_modEq.mpr (omega2Exp_modEq hdvd hN)

/-- **Naturality of `ω₂`.** The 2-primary projection commutes with every group homomorphism (out
of a finite group): `f (x ^ ω₂) = (f x) ^ ω₂`.  This is the structural fact underlying the fact
that the paper's auxiliary words are preserved by quotient maps (needed for Lemma 2.1). -/
theorem powOmega2_map {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H) (x : G) :
    f (powOmega2 x) = powOmega2 (f x) := by
  rw [powOmega2, map_pow]
  exact powOmega2_pow_eq (f x) (orderOf_map_dvd f x) (orderOf_pos x).ne'


/-- **Appendix B, exact match.**  Our *computable* representative `omega2Exp`, evaluated at the
paper's modulus `M = 85667662080 = 2⁸·3²·5·7·11·13·17·19·23`, reproduces the Appendix-B
serialization `40491355905` **exactly** (not merely up to the defining congruences).  This certifies
that the definition `omega2Exp`, and not just the hard-coded residue of `omega2_appendixB`, agrees
with the paper.  Proved with only the standard axioms: the 2-adic valuation `v₂(M) = 8` is pinned by
`p^k ∣ M` bounds, and the remaining `334639305 ^ 2⁷ % M` is closed by kernel `Nat` arithmetic. -/
theorem omega2Exp_appendixB_value : omega2Exp 85667662080 = 40491355905 := by
  have hn : (85667662080 : ℕ) ≠ 0 := by norm_num
  have hfac : (85667662080 : ℕ).factorization 2 = 8 := by
    have h8 : 8 ≤ (85667662080 : ℕ).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).mp (by decide)
    have h9 : ¬ 9 ≤ (85667662080 : ℕ).factorization 2 := fun h =>
      absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).mpr h) (by decide)
    lia
  norm_num [omega2Exp, hfac]

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 2.1 = ⟦lem-subdirect⟧
-/
