import GQ2.Words

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
  set a := n.factorization 2 with ha
  by_cases hn : n = 0
  · subst hn; simp
  by_cases haz : a = 0
  · simp [haz]
  · simp only [haz, if_false]
    have h2a : 2 ^ a ∣ n := ha ▸ Nat.ordProj_dvd n 2
    have hdvd_n : (n / 2 ^ a) ∣ n := Nat.div_dvd_of_dvd h2a
    rw [Nat.dvd_mod_iff hdvd_n]
    exact dvd_pow_self _ (by positivity)

/-- `omega2Exp n ≡ 1` modulo the 2-part `2 ^ v₂(n)` (the "`ω₂ ≡ 1` on the 2-part" condition),
for `n` with a nontrivial 2-part.  Uses Euler's theorem: the odd part is a unit mod `2^a`, and
`2^(a-1) = φ(2^a)`. -/
theorem omega2Exp_modEq_one {n : ℕ} (hn : n ≠ 0) (ha : n.factorization 2 ≠ 0) :
    omega2Exp n ≡ 1 [MOD 2 ^ n.factorization 2] := by
  set a := n.factorization 2 with hadef
  have h2a : 2 ^ a ∣ n := hadef ▸ Nat.ordProj_dvd n 2
  -- `x % n ≡ x` modulo `2^a` since `2^a ∣ n`.
  have hmodn : omega2Exp n ≡ (n / 2 ^ a) ^ (2 ^ (a - 1)) [MOD 2 ^ a] := by
    unfold omega2Exp
    simp only [← hadef, ha, if_false]
    exact (Nat.mod_modEq _ _).of_dvd h2a
  -- The odd part is coprime to `2^a`, so Euler applies with `φ(2^a) = 2^(a-1)`.
  have hnd : ¬ (2 : ℕ) ∣ (n / 2 ^ a) := by
    have h := Nat.not_dvd_ordCompl (p := 2) Nat.prime_two hn
    simpa [hadef] using h
  have hcop : Nat.Coprime (n / 2 ^ a) (2 ^ a) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hnd).symm).pow_right a
  have htot : Nat.totient (2 ^ a) = 2 ^ (a - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.pos_of_ne_zero ha)]; simp
  have heuler : (n / 2 ^ a) ^ (2 ^ (a - 1)) ≡ 1 [MOD 2 ^ a] := by
    rw [← htot]; exact Nat.ModEq.pow_totient hcop
  exact hmodn.trans heuler

/-- **Appendix B cross-check.** For the paper's finite modulus `M = 85667662080 =
2⁸·3²·5·7·11·13·17·19·23`, the idempotent `ω₂` is serialized as `40491355905`.  We confirm this
residue satisfies the two defining congruences of `ω₂` — `≡ 1` on the 2-part `2⁸ = 256`, `≡ 0` on
the odd part `M/256 = 334639305` — and is a reduced residue.  These two congruences pin down `ω₂`
modulo `M` uniquely, so this certifies the paper's serialized value. -/
theorem omega2_appendixB :
    (85667662080 : ℕ) = 2 ^ 8 * 334639305 ∧
    ¬ (2 : ℕ) ∣ 334639305 ∧
    (40491355905 : ℕ) % 256 = 1 ∧
    (334639305 : ℕ) ∣ 40491355905 ∧
    (40491355905 : ℕ) < 85667662080 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end GQ2
