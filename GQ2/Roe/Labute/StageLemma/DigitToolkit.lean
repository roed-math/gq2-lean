/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.StageLemma.Defect

/-!
# The digit calculus, the χ-plumbing, and the kernel witnesses

Piece 3/6 of `GQ2.Roe.Labute.StageLemma` (see that module for the mathematical overview
and the statement freeze).  The `2`-adic digit facts driving SL2 (lifting the exponent,
the dichotomy, the automatic digit), the translation between `χ`-values and divisibility,
and the explicit `ker d̄` witnesses.  Consumed by both SL1 and SL2.
-/

namespace GQ2.Roe.Labute

/-! ## The digit calculus (SL2's internal mechanism; spike §2.4, memo §1)

A level-`k` triple carries character values `χ(Tᵢ) = targetᵢ·ρᵢ` with `ρᵢ ≡ 1 mod 2^k`
(the invariant `P`); SL2 must kill the fresh level-`k` digits of the `ρᵢ`.  Three `2`-adic
facts do it, all proved here from scratch over `ℤ₂` (parity steps run through the residue
field `𝔽₂ = ZMod (2^1)`):

* **lifting the exponent** (`sharp_pow_two_pow`): `v₂(u − 1) = 2` forces
  `v₂(u^{2^m} − 1) = m + 2`.  All three relevant orientation units are `≡ 5 (mod 8)`
  (`η`, `X`, `S` — `chiTargetR0_three`, `chiTargetR2_three`), so their `2^{k-2}`-powers
  have a *sharp* digit at level `k` — and the `1 mod 2^k` deviation carried along by the
  actual triple is invisible there (`sharp_move`: its junk enters at `2^{2k-2}`, and
  `2k − 2 ≥ k + 1` exactly when `k ≥ 3`);
* **the dichotomy** (`dvd_or_dvd_mul`): against such a move, one of `ρ`, `ρ·μ` is
  `≡ 1 mod 2^{k+1}` — one move per free slot suffices;
* **the automatic digit** (`dvd_succ_of_sq`, memo §1.1): the slot carrying the relator's
  *square* needs no move at all.  Its level-`(k+1)` clause follows from the level-`(k+1)`
  relator clause itself: the corrected word lies in `λ_{k+1}`, so its χ-value lies in
  `1 + 2^{k+2}ℤ₂` (`twoCentralSeries_units_le` at index `k+1`), and with the `⁴`-slot
  contributing only at `2^{k+2}` this reads `ρ² ≡ 1 mod 2^{k+2}`, forcing
  `ρ ≡ 1 mod 2^{k+1}`.  Both exact target relations hold in `ℤ₂ˣ` on the nose:
  `(−1)²·1⁴ = 1` and `X⁻⁴·Y² = 1` (`YvalUnit_sq_eq`). -/

section DigitCalculus

open PadicInt

/-- `2^n ∣ x` read off the mod-`2^n` reduction. -/
theorem two_pow_dvd_iff {n : ℕ} {x : ℤ_[2]} :
    (2 : ℤ_[2]) ^ n ∣ x ↔ toZModPow n x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  norm_num

/-- `2 ∣ x` read off the residue field. -/
private theorem two_dvd_iff {x : ℤ_[2]} : (2 : ℤ_[2]) ∣ x ↔ toZModPow 1 x = 0 := by
  rw [show ((2 : ℤ_[2])) = 2 ^ 1 by ring]
  exact two_pow_dvd_iff

/-- Two odd `2`-adic integers have even sum. -/
private theorem two_dvd_add_of_not_dvd {r m : ℤ_[2]} (hr : ¬ (2 : ℤ_[2]) ∣ r)
    (hm : ¬ (2 : ℤ_[2]) ∣ m) : (2 : ℤ_[2]) ∣ r + m := by
  rw [two_dvd_iff] at hr hm ⊢
  rw [map_add]
  revert hr hm
  generalize toZModPow 1 r = a
  generalize toZModPow 1 m = b
  revert a b
  decide

/-- A product of odd `2`-adic integers is odd. -/
theorem two_not_dvd_mul {r m : ℤ_[2]} (hr : ¬ (2 : ℤ_[2]) ∣ r)
    (hm : ¬ (2 : ℤ_[2]) ∣ m) : ¬ (2 : ℤ_[2]) ∣ r * m := by
  rw [two_dvd_iff] at hr hm ⊢
  rw [map_mul]
  revert hr hm
  generalize toZModPow 1 r = a
  generalize toZModPow 1 m = b
  revert a b
  decide

/-- `1 + 2x` is odd. -/
theorem two_not_dvd_one_add_two_mul (x : ℤ_[2]) : ¬ (2 : ℤ_[2]) ∣ 1 + 2 * x := by
  rw [two_dvd_iff, map_add, map_one, map_mul, map_ofNat]
  generalize toZModPow 1 x = a
  revert a
  decide

/-- Adding an even number preserves oddness. -/
private theorem two_not_dvd_add_two_mul {r : ℤ_[2]} (hr : ¬ (2 : ℤ_[2]) ∣ r) (x : ℤ_[2]) :
    ¬ (2 : ℤ_[2]) ∣ r + 2 * x := fun h => hr (by simpa using dvd_sub h (Dvd.intro x rfl))

/-- Congruences to `1` multiply. -/
theorem dvd_mul_sub_one {A B : ℤ_[2]} {n : ℕ} (hA : (2 : ℤ_[2]) ^ n ∣ A - 1)
    (hB : (2 : ℤ_[2]) ^ n ∣ B - 1) : (2 : ℤ_[2]) ^ n ∣ A * B - 1 := by
  obtain ⟨s, hs⟩ := hA
  obtain ⟨t, ht⟩ := hB
  exact ⟨s * B + t, by linear_combination B * hs + ht⟩

/-- Congruences to `1` cancel. -/
theorem dvd_sub_one_of_mul {A B : ℤ_[2]} {n : ℕ} (h : (2 : ℤ_[2]) ^ n ∣ A * B - 1)
    (hB : (2 : ℤ_[2]) ^ n ∣ B - 1) : (2 : ℤ_[2]) ^ n ∣ A - 1 := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := hB
  exact ⟨s - A * t, by linear_combination hs - A * ht⟩

/-- Congruences to `1` are inherited by powers. -/
theorem dvd_pow_sub_one {A : ℤ_[2]} {n : ℕ} (hA : (2 : ℤ_[2]) ^ n ∣ A - 1) (b : ℕ) :
    (2 : ℤ_[2]) ^ n ∣ A ^ b - 1 := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ]; exact dvd_mul_sub_one ih hA

/-- **Lifting the exponent**: `v₂(u − 1) = 2` forces `v₂(u^{2^m} − 1) = m + 2`. -/
private theorem sharp_pow_two_pow {u c : ℤ_[2]} (hc : u - 1 = 2 ^ 2 * c)
    (hc2 : ¬ (2 : ℤ_[2]) ∣ c) (m : ℕ) :
    ∃ d : ℤ_[2], u ^ 2 ^ m - 1 = 2 ^ (m + 2) * d ∧ ¬ (2 : ℤ_[2]) ∣ d := by
  induction m with
  | zero => exact ⟨c, by simpa using hc, hc2⟩
  | succ m ih =>
    obtain ⟨d, hd, hd2⟩ := ih
    refine ⟨d * (1 + 2 ^ (m + 1) * d), ?_, ?_⟩
    · have hu : u ^ 2 ^ m = 1 + 2 ^ (m + 2) * d := by linear_combination hd
      have h : u ^ 2 ^ (m + 1) = (u ^ 2 ^ m) ^ 2 := by rw [← pow_mul, ← pow_succ]
      rw [h, hu]
      ring
    · refine two_not_dvd_mul hd2 ?_
      rw [show (2 : ℤ_[2]) ^ (m + 1) * d = 2 * (2 ^ m * d) by ring]
      exact two_not_dvd_one_add_two_mul _

/-- Squaring deepens a congruence: `ρ ≡ 1 mod 2^k` gives `ρ^{2^n} ≡ 1 mod 2^{k+n}`. -/
theorem dvd_pow_two_pow_sub_one {ρ : ℤ_[2]} {k : ℕ} (hk : 1 ≤ k)
    (h : (2 : ℤ_[2]) ^ k ∣ ρ - 1) (n : ℕ) : (2 : ℤ_[2]) ^ (k + n) ∣ ρ ^ 2 ^ n - 1 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hfac : ρ ^ 2 ^ (n + 1) - 1 = (ρ ^ 2 ^ n - 1) * (ρ ^ 2 ^ n + 1) := by
      rw [show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 by ring, pow_mul]; ring
    have h2 : (2 : ℤ_[2]) ∣ ρ ^ 2 ^ n + 1 := by
      obtain ⟨c, hc⟩ := ih
      refine ⟨2 ^ (k + n - 1) * c + 1, ?_⟩
      have hρ : ρ ^ 2 ^ n = 1 + 2 ^ (k + n) * c := by linear_combination hc
      rw [hρ, show (2 : ℤ_[2]) ^ (k + n) = 2 * 2 ^ (k + n - 1) by
        rw [← pow_succ']; congr 1; omega]
      ring
    rw [hfac, show k + (n + 1) = k + n + 1 by ring, pow_succ]
    exact mul_dvd_mul ih h2

/-- A deeper factor does not disturb a sharp digit. -/
private theorem sharp_mul_of_dvd {μ ρ d : ℤ_[2]} {k : ℕ} (hμ : μ - 1 = 2 ^ k * d)
    (hd : ¬ (2 : ℤ_[2]) ∣ d) (hρ : (2 : ℤ_[2]) ^ (k + 1) ∣ ρ - 1) :
    ∃ d' : ℤ_[2], μ * ρ - 1 = 2 ^ k * d' ∧ ¬ (2 : ℤ_[2]) ∣ d' := by
  obtain ⟨e, he⟩ := hρ
  have hρ' : ρ = 1 + 2 * (2 ^ k * e) := by rw [pow_succ'] at he; linear_combination he
  have hμ' : μ = 1 + 2 ^ k * d := by linear_combination hμ
  refine ⟨d * ρ + 2 * e, by rw [hμ', hρ']; ring, ?_⟩
  exact two_not_dvd_add_two_mul (two_not_dvd_mul hd (hρ' ▸ two_not_dvd_one_add_two_mul _)) e

/-- **The digit dichotomy**: a sharp level-`k` move fixes the level-`k` digit of `ρ`. -/
theorem dvd_or_dvd_mul {ρ μ d : ℤ_[2]} {k : ℕ} (hk : 1 ≤ k)
    (hρ : (2 : ℤ_[2]) ^ k ∣ ρ - 1) (hμ : μ - 1 = 2 ^ k * d) (hd : ¬ (2 : ℤ_[2]) ∣ d) :
    (2 : ℤ_[2]) ^ (k + 1) ∣ ρ - 1 ∨ (2 : ℤ_[2]) ^ (k + 1) ∣ ρ * μ - 1 := by
  obtain ⟨r, hr⟩ := hρ
  by_cases hr2 : (2 : ℤ_[2]) ∣ r
  · obtain ⟨c, rfl⟩ := hr2
    exact Or.inl ⟨c, by rw [hr, pow_succ]; ring⟩
  · refine Or.inr ?_
    obtain ⟨c, hc⟩ := two_dvd_add_of_not_dvd hr2 hd
    refine ⟨c + 2 ^ (k - 1) * (r * d), ?_⟩
    have hρ' : ρ = 1 + 2 ^ k * r := by linear_combination hr
    have hμ' : μ = 1 + 2 ^ k * d := by linear_combination hμ
    have hpow : (2 : ℤ_[2]) ^ k * 2 ^ k = 2 ^ (k + 1) * 2 ^ (k - 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hρ', hμ']
    linear_combination (2 : ℤ_[2]) ^ k * hc + (r * d) * hpow

/-- **The automatic digit** (memo §1.1): `ρ ≡ 1 mod 2^k` together with
`ρ² ≡ 1 mod 2^{k+2}` already gives `ρ ≡ 1 mod 2^{k+1}` (`k ≥ 2`). -/
theorem dvd_succ_of_sq {ρ : ℤ_[2]} {k : ℕ} (hk : 2 ≤ k)
    (hρ : (2 : ℤ_[2]) ^ k ∣ ρ - 1) (hsq : (2 : ℤ_[2]) ^ (k + 2) ∣ ρ ^ 2 - 1) :
    (2 : ℤ_[2]) ^ (k + 1) ∣ ρ - 1 := by
  obtain ⟨r, hr⟩ := hρ
  obtain ⟨t, ht⟩ := hsq
  have hρ' : ρ = 1 + 2 ^ k * r := by linear_combination hr
  have hpow : (2 : ℤ_[2]) ^ k * 2 ^ k = 2 ^ (k + 1) * 2 ^ (k - 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have key : (2 : ℤ_[2]) ^ (k + 1) * (r * (1 + 2 ^ (k - 1) * r)) = 2 ^ (k + 1) * (2 * t) := by
    rw [hρ'] at ht
    linear_combination ht - (r * r) * hpow
  have hcancel : r * (1 + 2 ^ (k - 1) * r) = 2 * t :=
    mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) key
  have hodd : ¬ (2 : ℤ_[2]) ∣ 1 + 2 ^ (k - 1) * r := by
    rw [show (2 : ℤ_[2]) ^ (k - 1) * r = 2 * (2 ^ (k - 2) * r) by
      rw [← mul_assoc, ← pow_succ']; congr 2; omega]
    exact two_not_dvd_one_add_two_mul _
  have h2r : (2 : ℤ_[2]) ∣ r := by
    by_contra hr2
    exact two_not_dvd_mul hr2 hodd ⟨t, hcancel⟩
  obtain ⟨c, rfl⟩ := h2r
  exact ⟨c, by rw [hr, pow_succ]; ring⟩

/-- A `2`-adic integer that is `5 mod 8` has a sharp digit at level `2`. -/
private theorem sharp_two_of_toZModPow_three {u : ℤ_[2]} (h : toZModPow 3 u = 5) :
    ∃ c : ℤ_[2], u - 1 = 2 ^ 2 * c ∧ ¬ (2 : ℤ_[2]) ∣ c := by
  have h8 : (2 : ℤ_[2]) ^ 3 ∣ u - 1 - 4 := by
    rw [two_pow_dvd_iff, map_sub, map_sub, h, map_one, map_ofNat]
    decide
  obtain ⟨e, he⟩ := h8
  exact ⟨1 + 2 * e, by linear_combination he, two_not_dvd_one_add_two_mul e⟩

/-- **The move digit** (memo §1.2): the `2^{k-2}`-power of a unit whose target is `5 mod 8`
has a sharp level-`k` digit — the `1 mod 2^k` deviation of the actual triple slot only
enters at `2^{2k-2}`, and `2k − 2 ≥ k + 1` exactly at the calculus threshold `k ≥ 3`. -/
theorem sharp_move {base c : ℤ_[2]ˣ} {k : ℕ} (hk : 3 ≤ k)
    (hbase : toZModPow 3 ((base : ℤ_[2]ˣ) : ℤ_[2]) = 5)
    (hc : (2 : ℤ_[2]) ^ k ∣ ((c * base⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    ∃ d : ℤ_[2], ((c ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ k * d ∧
      ¬ (2 : ℤ_[2]) ∣ d := by
  obtain ⟨e, he, he2⟩ := sharp_two_of_toZModPow_three hbase
  obtain ⟨d, hd, hd2⟩ := sharp_pow_two_pow he he2 (k - 2)
  rw [show k - 2 + 2 = k by omega] at hd
  have hjunk : (2 : ℤ_[2]) ^ (k + 1) ∣ ((c * base⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 ^ (k - 2) - 1 :=
    dvd_trans (pow_dvd_pow 2 (by omega : k + 1 ≤ k + (k - 2)))
      (dvd_pow_two_pow_sub_one (by omega) hc (k - 2))
  obtain ⟨d', hd', hd'2⟩ := sharp_mul_of_dvd hd hd2 hjunk
  refine ⟨d', ?_, hd'2⟩
  rw [← hd']
  have hbc : base * (c * base⁻¹) = c := by
    rw [mul_comm c base⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← mul_pow, ← Units.val_mul, hbc, Units.val_pow_eq_pow_val]

end DigitCalculus

/-! ### The χ-plumbing and the kernel witnesses (SL2 fill helpers) -/

/-- Two `2`-adic units agree mod `2^n` exactly when their ratio is `1 mod 2^n`. -/
private theorem units_map_eq_iff_dvd {n : ℕ} {x y : ℤ_[2]ˣ} :
    Units.map (PadicInt.toZModPow n).toMonoidHom x =
        Units.map (PadicInt.toZModPow n).toMonoidHom y ↔
      (2 : ℤ_[2]) ^ n ∣ ((x * y⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  have h : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
  rw [← h, ← mem_ker_units_toZModPow_iff, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]

section ChiPlumbing

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The χ-clause of the levelwise sets, read as a `2`-adic congruence at a chosen lift. -/
theorem dvd_of_chiLevel_eq (χ : ContinuousMonoidHom G ℤ_[2]ˣ) (target : ℤ_[2]ˣ)
    {n : ℕ} {q : levelQuot G n} {a : G} (haq : levelMk G n a = q)
    (h : chiLevel χ n q = Units.map (PadicInt.toZModPow n).toMonoidHom target) :
    (2 : ℤ_[2]) ^ n ∣ ((χ a * target⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
  units_map_eq_iff_dvd.mp (by rwa [← haq, chiLevel_levelMk] at h)

/-- The converse direction: a `2`-adic congruence certifies the χ-clause. -/
theorem chiLevel_eq_of_dvd (χ : ContinuousMonoidHom G ℤ_[2]ˣ) (target : ℤ_[2]ˣ)
    {n : ℕ} {q : levelQuot G n} {a : G} (haq : levelMk G n a = q)
    (h : (2 : ℤ_[2]) ^ n ∣ ((χ a * target⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    chiLevel χ n q = Units.map (PadicInt.toZModPow n).toMonoidHom target := by
  rw [← haq, chiLevel_levelMk]
  exact units_map_eq_iff_dvd.mpr h

/-- **The χ-depth bound at index `k`** (`twoCentralSeries_units_le`): a word that dies in
`Qₖ` has χ-value in `1 + 2^{k+1}ℤ₂`.  This is the mechanism of `chiLevel_lambdaImage_pred`,
re-instantiated one digit deeper than the generic layer bound. -/
theorem dvd_chi_of_mem_twoCentralSeries (χ : ContinuousMonoidHom G ℤ_[2]ˣ) {k : ℕ}
    (hk : 2 ≤ k) {r : G} (hr : r ∈ twoCentralSeries G k) :
    (2 : ℤ_[2]) ^ (k + 1) ∣ ((χ r : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  have h1 : χ r ∈ twoCentralSeries ℤ_[2]ˣ k :=
    map_twoCentralSeries_le χ.toMonoidHom χ.continuous_toFun k ⟨r, hr, rfl⟩
  simpa using mem_ker_units_toZModPow_iff.mp (twoCentralSeries_units_le k hk h1)

/-- `2`-power powers of any element sink into the λ-tower (`λ₁ = ⊤` plus `λⱼ² ⊆ λ_{j+1}`). -/
private theorem pow_two_pow_mem_twoCentralSeries (g : G) (n : ℕ) :
    g ^ 2 ^ n ∈ twoCentralSeries G (1 + n) := by
  induction n with
  | zero => simp [twoCentralSeries_one]
  | succ n ih =>
    have h : g ^ 2 ^ (n + 1) = (g ^ 2 ^ n) ^ 2 := by rw [← pow_mul, ← pow_succ]
    rw [h, show 1 + (n + 1) = 1 + n + 1 from rfl]
    exact sq_mem_twoCentralSeries_succ G ih

/-- The level-quotient form of the previous lemma. -/
theorem pow_two_pow_mem_lambdaImage {m : ℕ} (q : levelQuot G m) (n : ℕ) :
    q ^ 2 ^ n ∈ lambdaImage G (1 + n) m := by
  obtain ⟨g, rfl⟩ := levelMk_surjective G m q
  exact ⟨g ^ 2 ^ n, pow_two_pow_mem_twoCentralSeries g n, map_pow _ _ _⟩

end ChiPlumbing

/-- **The `r₀` kernel witnesses** (memo §1.2): the `s`-slot moves by `p` and the `y`-slot by
`q`, where `p` commutes with `y` and `q` commutes with `s·y`.  Then `d̄` dies: the `p`-bracket
vanishes outright, and the two `q`-brackets recombine into `[q, s·y] = 1` (centrality lets
them be collected).  Both free digit moves of `ker d̄` have this shape — `p` a power of `y`,
`q` a power of `s·y`. -/
theorem dbarWordR0_kernel_witness {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (k : ℕ) (hk : 3 ≤ k) (a s y p q : levelQuot G (k + 1))
    (hq : q ∈ lambdaImage G (k - 1) (k + 1)) (hp : commP p y = 1)
    (hqsy : commP q (s * y) = 1) :
    dbarWordR0 a s y ![1, p * q, q] = 1 := by
  have hone : ∀ z : levelQuot G (k + 1), commP (1 : levelQuot G (k + 1)) z = 1 := by
    intro z; simp only [commP]; group
  have hzs : commP q s ∈ zLayer G k := commP_mem_zLayer k hk hq s
  have hleft : commP (p * q) y = commP q y := by
    rw [commP_mul_left, hp, mul_one, inv_mul_cancel, one_mul]
  have hsplit : commP q y * commP q s = 1 := by
    rw [← hqsy, commP_mul_right, conj_eq_self_of_commP_eq_one
      (commP_eq_one_of_mul_comm (zLayer_commute hzs y).eq)]
  simp only [dbarWordR0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, one_pow, hone, one_mul, hleft]
  exact hsplit

/-- **The `r₂` kernel witnesses** (memo §1.2): the `s`-slot moves by a power of `x` and the
`x`-slot by a power of `s`; each move kills its own bracket definitionally, and the `y`-slot
— the only one entering `d̄` through a square — is left alone.  No hypotheses at all. -/
theorem dbarWordR2_kernel_witness {H : Type*} [Group H] (s x y p q : H)
    (hp : commP p x = 1) (hq : commP q s = 1) : dbarWordR2 s x y ![p, q, 1] = 1 := by
  have hone : ∀ z : H, commP (1 : H) z = 1 := by intro z; simp only [commP]; group
  simp only [dbarWordR2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, one_pow, hone, hp, hq, mul_one]

/-- **Generation lifts along the tower**: a subgroup of `Q_{k+1}` surjecting onto `Qₖ` is
everything — the kernel `Zₖ ≤ λ₂` is Frattini (`lambdaImage_two_le_frattiniLike`), so
non-generation applies. -/
theorem eq_top_of_map_levelProj_eq_top (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) {k : ℕ} (hk : 2 ≤ k) {H : Subgroup (levelQuot G (k + 1))}
    (h : H.map (levelProj G k) = ⊤) : H = ⊤ := by
  haveI := finite_levelQuot G hfg hpro (k + 1)
  have h2 : IsPGroup 2 ↥(⊤ : Subgroup (levelQuot G (k + 1))) :=
    (isPGroup_levelQuot G hfg hpro (k + 1)).of_equiv Subgroup.topEquiv.symm
  have hΦ := lambdaImage_two_le_frattiniLike G hfg hpro (k + 1)
  refine frattiniLike_nongen h2 le_top (le_antisymm le_top ?_)
  intro q _
  obtain ⟨x, hx, hxq⟩ : levelProj G k q ∈ H.map (levelProj G k) := by rw [h]; trivial
  have hz : x⁻¹ * q ∈ zLayer G k := by
    rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, map_mul, map_inv, hxq, inv_mul_cancel]
  have hker : x⁻¹ * q ∈ lambdaImage G 2 (k + 1) := lambdaImage_le_of_le (by omega) hz
  rw [show q = x * (x⁻¹ * q) by group]
  exact Subgroup.mul_mem_sup hx (hΦ hker)

end GQ2.Roe.Labute
