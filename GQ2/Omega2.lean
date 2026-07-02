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

/-- **`ω₂` is well-defined via any exponent multiple.**  For `x` of finite order dividing `N`
(`N ≠ 0`), `x ^ (omega2Exp N) = powOmega2 x`.  So `powOmega2` really is *the* 2-primary
projection: the choice of modulus `orderOf x` in its definition is immaterial, as long as the
modulus is a multiple of `orderOf x`.  (This is what makes `powOmega2` behave coordinatewise on
products, cf. `powOmega2_prod`.) -/
theorem powOmega2_pow_eq {G : Type*} [Group G] (x : G) {N : ℕ}
    (hdvd : orderOf x ∣ N) (hN : N ≠ 0) : x ^ omega2Exp N = powOmega2 x := by
  show x ^ omega2Exp N = x ^ omega2Exp (orderOf x)
  apply pow_eq_pow_iff_modEq.mpr
  set d := orderOf x with hddef
  have hd0 : d ≠ 0 := by intro h0; rw [h0, Nat.zero_dvd] at hdvd; exact hN hdvd
  -- Congruent modulo the 2-part `2 ^ v₂(d)` (both `≡ 1`).
  have h2 : omega2Exp N ≡ omega2Exp d [MOD 2 ^ d.factorization 2] := by
    by_cases hα : d.factorization 2 = 0
    · rw [hα, pow_zero]; exact Nat.modEq_one
    · have hle : d.factorization 2 ≤ N.factorization 2 :=
        (Nat.factorization_le_iff_dvd hd0 hN).mpr hdvd 2
      have e2 : omega2Exp N ≡ 1 [MOD 2 ^ d.factorization 2] :=
        (omega2Exp_modEq_one hN (by omega)).of_dvd (pow_dvd_pow 2 hle)
      exact e2.trans (omega2Exp_modEq_one hd0 hα).symm
  -- Congruent modulo the odd part `d / 2 ^ v₂(d)` (both `≡ 0`).
  have hodd : omega2Exp N ≡ omega2Exp d [MOD d / 2 ^ d.factorization 2] := by
    have e1 : (d / 2 ^ d.factorization 2) ∣ omega2Exp d := oddPart_dvd_omega2Exp d
    have e2 : (d / 2 ^ d.factorization 2) ∣ omega2Exp N :=
      (Nat.ordCompl_dvd_ordCompl_of_dvd hdvd 2).trans (oddPart_dvd_omega2Exp N)
    exact (Nat.modEq_zero_iff_dvd.mpr e2).trans (Nat.modEq_zero_iff_dvd.mpr e1).symm
  -- CRT: combine over the coprime factorisation `d = 2^{v₂ d} · (d / 2^{v₂ d})`.
  have hcop : Nat.Coprime (2 ^ d.factorization 2) (d / 2 ^ d.factorization 2) :=
    Nat.Coprime.pow_left _
      ((Nat.prime_two.coprime_iff_not_dvd).mpr (Nat.not_dvd_ordCompl Nat.prime_two hd0))
  have hcrt := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, hodd⟩
  rwa [Nat.ordProj_mul_ordCompl_eq_self d 2] at hcrt

/-- **Naturality of `ω₂`.** The 2-primary projection commutes with every group homomorphism (out
of a finite group): `f (x ^ ω₂) = (f x) ^ ω₂`.  This is the structural fact underlying the fact
that the paper's auxiliary words are preserved by quotient maps (needed for Lemma 2.1). -/
theorem powOmega2_map {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H) (x : G) :
    f (powOmega2 x) = powOmega2 (f x) := by
  rw [powOmega2, map_pow]
  have hdvd : orderOf (f x) ∣ orderOf x :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  exact powOmega2_pow_eq (f x) hdvd (orderOf_pos x).ne'

/-- `powOmega2` is computed coordinatewise on a product of finite groups. -/
theorem powOmega2_prod {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (a : G) (b : H) :
    powOmega2 ((a, b) : G × H) = (powOmega2 a, powOmega2 b) := by
  have hne : orderOf ((a, b) : G × H) ≠ 0 := (orderOf_pos _).ne'
  have hpow := pow_orderOf_eq_one ((a, b) : G × H)
  rw [Prod.pow_mk, Prod.ext_iff] at hpow
  have hda : orderOf a ∣ orderOf ((a, b) : G × H) := orderOf_dvd_of_pow_eq_one hpow.1
  have hdb : orderOf b ∣ orderOf ((a, b) : G × H) := orderOf_dvd_of_pow_eq_one hpow.2
  have hLHS : powOmega2 ((a, b) : G × H)
      = (a ^ omega2Exp (orderOf ((a, b) : G × H)), b ^ omega2Exp (orderOf ((a, b) : G × H))) := by
    rw [powOmega2, Prod.pow_mk]
  rw [hLHS, powOmega2_pow_eq a hda hne, powOmega2_pow_eq b hdb hne]

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
