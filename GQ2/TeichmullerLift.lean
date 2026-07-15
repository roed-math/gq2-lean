/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section


set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Teichmüller units, odd-root separation, and successive approximation

The three **σ-free ingredients** of the residue-field proof of
`unramifiedQuadratic_units_are_norms` are:

* `exists_teichmuller` — §1(R)1: in a finite (hence complete) subextension `L/ℚ₂`, a norm-one
  `w` with `‖w^q − w‖ < 1` (`q` of norm `< 1`, e.g. any even `q`) has a **Teichmüller
  representative**: `ω ∈ L` with `ω^q = ω`, `‖ω‖ = 1`, `‖ω − w‖ < 1`.  The sequence `w^{qⁿ}`
  is Cauchy (`cauchySeq_of_le_geometric`, the `HilbertLedger.sq_of_near_one` template — run in
  `↥L`, since `ℚ̄₂` itself is not complete) because `x ↦ x^q` contracts differences on the unit
  ball: `‖a^q − b^q‖ ≤ max(‖q‖, ‖a−b‖)·‖a−b‖` (`norm_pow_sub_pow_le`, via the geometric-sum
  factorization — one step for any `q` of norm `< 1`, no iterated squaring needed).
* `norm_sub_eq_one_of_pow_eq_one` — §1(R)2: distinct `m`-th roots of unity (`m` **odd**) are
  at distance `1`.  Route (simpler than the plan's derivative product, no enumeration of the
  root set): `η := ζ⁻¹ζ' ≠ 1` has `∑_{i<m} η^i = 0`, so `m = ∑_{i<m}(1 − η^i)` with every term
  of norm `≤ ‖1 − η‖`; hence `1 = ‖m‖ ≤ ‖1 − η‖ ≤ 1` (`‖m‖ = 1` because `m` is odd —
  `norm_natCast_eq_one_of_odd`, the only 2-adic input).
* `le_of_shared_uniformizer` — §1(R)4: if `π ∈ k` is a shared uniformizer for `k ≤ L`
  (max-property over `L`) and every integral `z ∈ L` is congruent mod `𝔪_L` to an element of
  `k` (the "`l = k̄`" hypothesis, in norm form), then `L ≤ k` — `π`-adic successive
  approximation with `k`-coefficients, plus closedness of the finite-dimensional `k`.

**Interface note.**  These lemmas need **no** filtration interface
— every B13 input is abstracted into an explicit norm hypothesis (`hwq`, `hπmax`, `hres`), so
the file imports Mathlib only.  `GQ2/UnramifiedQuadraticNorms.lean` supplies the concrete
filtration data at the call sites.  This keeps the elementary approximation layer independent
of the filtration implementation.

Axioms: **∅** (std-3 target).  Paper: §6.3 via Serre LF Ch. V §2 (see the plan).
-/

namespace GQ2.TeichmullerLift

open Filter Finset

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Ultrametric power-difference estimates -/

section Ultrametric

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- An ultrametric bound for finite sums: if every summand has norm `≤ C`, so does the sum. -/
private lemma norm_finset_sum_le {ι : Type*} {s : Finset ι} {f : ι → K} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C := by
  induction s using Finset.cons_induction with
  | empty => simpa using hC
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (h _ (Finset.mem_cons_self _ _)) (ih fun i hi => h i (Finset.mem_cons_of_mem hi)))

/-- In an ultrametric field, `x ↦ xᵐ` is `1`-Lipschitz on the unit ball. -/
lemma norm_pow_sub_pow_le_norm_sub {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ ‖a - b‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by ring
    rw [hsplit]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ m - b ^ m‖ ≤ 1 * ‖a - b‖ :=
            mul_le_mul ha ih (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ m ≤ ‖a - b‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _

/-- On the unit ball of an ultrametric field, `x ↦ x^q` contracts differences by the factor
`max(‖q‖, ‖a − b‖)` — the quantitative "raising to an even power deepens congruences", in one
step for any `q` (the geometric sum `∑ aⁱb^{q−1−i}` is `q·a^{q−1}` up to a multiple of
`a − b`). -/
lemma norm_pow_sub_pow_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (q : ℕ) :
    ‖a ^ q - b ^ q‖ ≤ max ‖(q : K)‖ ‖a - b‖ * ‖a - b‖ := by
  have hfac : a ^ q - b ^ q = (∑ i ∈ range q, a ^ i * b ^ (q - 1 - i)) * (a - b) :=
    (geom_sum₂_mul a b q).symm
  rw [hfac, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hterm : ∀ i ∈ range q, ‖a ^ i * b ^ (q - 1 - i) - a ^ (q - 1)‖ ≤ ‖a - b‖ := by
    intro i hi
    have hexp : a ^ i * a ^ (q - 1 - i) = a ^ (q - 1) := by
      rw [← pow_add]; congr 1; have := mem_range.mp hi; omega
    calc ‖a ^ i * b ^ (q - 1 - i) - a ^ (q - 1)‖
        = ‖a ^ i‖ * ‖b ^ (q - 1 - i) - a ^ (q - 1 - i)‖ := by
          rw [← hexp, ← mul_sub, norm_mul]
      _ ≤ 1 * ‖b - a‖ := by
          refine mul_le_mul ?_ (norm_pow_sub_pow_le_norm_sub hb ha _) (norm_nonneg _)
            zero_le_one
          rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
      _ = ‖a - b‖ := by rw [one_mul, norm_sub_rev]
  have hsum : ∑ i ∈ range q, a ^ i * b ^ (q - 1 - i)
      = (q : K) * a ^ (q - 1) + ∑ i ∈ range q, (a ^ i * b ^ (q - 1 - i) - a ^ (q - 1)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
    ring
  rw [hsum]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
  · refine le_max_of_le_left ?_
    rw [norm_mul]
    calc ‖(q : K)‖ * ‖a ^ (q - 1)‖ ≤ ‖(q : K)‖ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
      _ = ‖(q : K)‖ := mul_one _
  · exact le_max_of_le_right (norm_finset_sum_le (norm_nonneg _) hterm)

end Ultrametric

/-! ## The 2-adic input: odd integers are units -/

/-- Odd naturals have norm `1` in `ℚ̄₂` (the spectral norm extends the 2-adic norm, where odd
integers are units). -/
lemma norm_natCast_eq_one_of_odd {m : ℕ} (hm : Odd m) : ‖(m : ℚ̄₂)‖ = 1 := by
  have h1 : (m : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ (m : ℚ_[2]) := (map_natCast _ m).symm
  rw [h1, norm_algebraMap' (𝕜' := ℚ̄₂) ((m : ℚ_[2])), Padic.norm_natCast_eq_one_iff]
  exact Nat.coprime_two_left.mpr hm

/-! ## Brick 2: odd-root separation -/

/-- A root of unity has norm `1`. -/
private lemma norm_eq_one_of_pow_eq_one {x : ℚ̄₂} {m : ℕ} (hm : m ≠ 0) (hx : x ^ m = 1) :
    ‖x‖ = 1 := by
  have h : ‖x‖ ^ m = 1 := by rw [← norm_pow, hx, norm_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd h (ne_of_lt (pow_lt_one₀ (norm_nonneg x) hlt hm))
  · exact absurd h (ne_of_gt ((one_lt_pow_iff_of_nonneg (norm_nonneg x) hm).mpr hgt))

/-- `1` is at distance exactly `1` from every *other* root of unity of **odd** order:
`m = ∑_{i<m}(1 − ηⁱ)` once `∑ ηⁱ = 0`, every summand has norm `≤ ‖1 − η‖`, and `‖m‖ = 1`. -/
lemma norm_one_sub_eq_one_of_pow_eq_one {m : ℕ} (hm : Odd m) {η : ℚ̄₂}
    (hη : η ^ m = 1) (hne : η ≠ 1) : ‖1 - η‖ = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hηn : ‖η‖ ≤ 1 := (norm_eq_one_of_pow_eq_one hm0 hη).le
  have hgeom : ∑ i ∈ range m, η ^ i = 0 := by
    have h := geom_sum_mul η m
    rw [hη, sub_self] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') hne
  have hmsum : (m : ℚ̄₂) = ∑ i ∈ range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero, Finset.sum_const, card_range, nsmul_eq_mul,
      mul_one]
  have hterm : ∀ i ∈ range m, ‖1 - η ^ i‖ ≤ ‖1 - η‖ := by
    intro i _
    have h := norm_pow_sub_pow_le_norm_sub (K := ℚ̄₂) (a := 1) (b := η) norm_one.le hηn i
    rwa [one_pow] at h
  have hge : (1 : ℝ) ≤ ‖1 - η‖ := by
    calc (1 : ℝ) = ‖(m : ℚ̄₂)‖ := (norm_natCast_eq_one_of_odd hm).symm
      _ = ‖∑ i ∈ range m, (1 - η ^ i)‖ := by rw [← hmsum]
      _ ≤ ‖1 - η‖ := norm_finset_sum_le (norm_nonneg _) hterm
  have hle : ‖1 - η‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
    rw [norm_one, norm_neg]
    exact max_le le_rfl hηn
  exact le_antisymm hle hge

/-- **Odd-root separation** (plan §1(R)2): distinct roots of unity of odd order `m` in `ℚ̄₂`
are at norm-distance exactly `1` — they stay distinct in every residue field of odd
characteristic-avoiding depth.  (Applied at `m = 2^F − 1` in the residue layer.) -/
theorem norm_sub_eq_one_of_pow_eq_one {m : ℕ} (hm : Odd m) {ζ ζ' : ℚ̄₂}
    (hζ : ζ ^ m = 1) (hζ' : ζ' ^ m = 1) (hne : ζ ≠ ζ') : ‖ζ - ζ'‖ = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0] at hζ
    exact zero_ne_one hζ
  have hζn : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hm0 hζ
  have hηm : (ζ⁻¹ * ζ') ^ m = 1 := by
    rw [mul_pow, inv_pow, hζ, hζ', inv_one, one_mul]
  have hηne : ζ⁻¹ * ζ' ≠ 1 := fun h ↦ hne (by field_simp at h; exact h.symm)
  have hkey : ζ - ζ' = ζ * (1 - ζ⁻¹ * ζ') := by
    field_simp
  rw [hkey, norm_mul, hζn, one_mul]
  exact norm_one_sub_eq_one_of_pow_eq_one hm hηm hηne

/-! ## Brick 1: Teichmüller representatives -/

/-- **Teichmüller representative** (plan §1(R)1).  In a finite (hence complete) subextension
`L/ℚ₂`, every norm-one `w ∈ L` with `‖w^q − w‖ < 1` (for an exponent `q` of norm `< 1` — in
application `q = #l`, a power of `2`, and the congruence is Lagrange in the residue field) is
congruent mod `𝔪_L` to a genuine `(q−1)`-st root of unity `ω ∈ L`: the `π`-adic limit of the
sequence `w^{qⁿ}`. -/
theorem exists_teichmuller (L : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] L]
    {q : ℕ} (hqn : ‖(q : ℚ̄₂)‖ < 1)
    {w : ℚ̄₂} (hwL : w ∈ L) (hw1 : ‖w‖ = 1) (hwq : ‖w ^ q - w‖ < 1) :
    ∃ ω : ℚ̄₂, ω ∈ L ∧ ω ^ q = ω ∧ ‖ω‖ = 1 ∧ ‖ω - w‖ < 1 := by
  haveI : CompleteSpace ↥L := FiniteDimensional.complete ℚ_[2] ↥L
  set w' : ↥L := ⟨w, hwL⟩ with hw'def
  have hw'1 : ‖w'‖ = 1 := hw1
  -- the contraction ratio
  set ρ : ℝ := max ‖(q : ℚ̄₂)‖ ‖w ^ q - w‖ with hρdef
  have hρ0 : (0 : ℝ) ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρ1 : ρ < 1 := max_lt hqn hwq
  -- the iteration `n ↦ w^{qⁿ}`, run inside the complete `↥L`
  set v : ℕ → ↥L := fun n => w' ^ q ^ n with hvdef
  have hv0 : v 0 = w' := by simp [hvdef]
  have hvS : ∀ n, v (n + 1) = (v n) ^ q := by
    intro n
    show w' ^ q ^ (n + 1) = (w' ^ q ^ n) ^ q
    rw [← pow_mul, ← pow_succ]
  have hnorm : ∀ n, ‖v n‖ = 1 := by
    intro n
    show ‖w' ^ q ^ n‖ = 1
    rw [norm_pow, hw'1, one_pow]
  have hqL : ‖((q : ℕ) : ↥L)‖ = ‖((q : ℕ) : ℚ̄₂)‖ := by
    have h : (((q : ℕ) : ↥L) : ℚ̄₂) = ((q : ℕ) : ℚ̄₂) := by push_cast; rfl
    calc ‖((q : ℕ) : ↥L)‖ = ‖(((q : ℕ) : ↥L) : ℚ̄₂)‖ := rfl
      _ = ‖((q : ℕ) : ℚ̄₂)‖ := by rw [h]
  -- geometric decay of the jumps
  have hjump : ∀ n, ‖v (n + 1) - v n‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      have h : v 1 - v 0 = w' ^ q - w' := by rw [hv0, hvS 0, hv0]
      rw [h, pow_one]
      exact le_max_of_le_right le_rfl
    | succ n ih =>
      have hstep : v (n + 1 + 1) - v (n + 1) = (v (n + 1)) ^ q - (v n) ^ q := by
        rw [hvS (n + 1), hvS n]
      rw [hstep]
      calc ‖(v (n + 1)) ^ q - (v n) ^ q‖
          ≤ max ‖((q : ℕ) : ↥L)‖ ‖v (n + 1) - v n‖ * ‖v (n + 1) - v n‖ :=
            norm_pow_sub_pow_le (hnorm (n + 1)).le (hnorm n).le q
        _ ≤ ρ * ρ ^ (n + 1) := by
            refine mul_le_mul ?_ ih (norm_nonneg _) hρ0
            refine max_le ?_ ?_
            · rw [hqL]; exact le_max_left _ _
            · exact le_trans ih (pow_le_of_le_one hρ0 hρ1.le (Nat.succ_ne_zero n))
        _ = ρ ^ (n + 1 + 1) := (pow_succ' ρ (n + 1)).symm
  -- Cauchy, hence convergent in the complete `↥L`
  have hcauchy : CauchySeq v := by
    refine cauchySeq_of_le_geometric ρ ρ hρ1 fun n => ?_
    rw [dist_eq_norm, norm_sub_rev]
    calc ‖v (n + 1) - v n‖ ≤ ρ ^ (n + 1) := hjump n
      _ = ρ * ρ ^ n := pow_succ' ρ n
  obtain ⟨ω', hω'⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limit is fixed by `x ↦ x^q`
  have hfix : ω' ^ q = ω' := by
    have h1 : Tendsto (fun n => v (n + 1)) atTop (nhds ω') :=
      hω'.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => (v n) ^ q) atTop (nhds (ω' ^ q)) := hω'.pow q
    have h3 : (fun n => v (n + 1)) = fun n => (v n) ^ q := funext hvS
    rw [h3] at h1
    exact (tendsto_nhds_unique h1 h2).symm
  -- the limit stays in the residue class of `w`
  have hdist : ∀ n, ‖v n - w'‖ ≤ ρ := by
    intro n
    induction n with
    | zero => rw [hv0, sub_self, norm_zero]; exact hρ0
    | succ n ih =>
      have h : v (n + 1) - w' = (v (n + 1) - v n) + (v n - w') := by ring
      rw [h]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ih)
      exact le_trans (hjump n) (pow_le_of_le_one hρ0 hρ1.le (Nat.succ_ne_zero n))
  have hlim_dist : ‖ω' - w'‖ ≤ ρ :=
    le_of_tendsto ((hω'.sub tendsto_const_nhds).norm) (Eventually.of_forall hdist)
  -- and is therefore itself norm-one
  have hω'1 : ‖ω'‖ = 1 := by
    have hne : ‖ω' - w'‖ ≠ ‖w'‖ := by
      rw [hw'1]
      exact ne_of_lt (lt_of_le_of_lt hlim_dist hρ1)
    calc ‖ω'‖ = ‖(ω' - w') + w'‖ := by rw [sub_add_cancel]
      _ = max ‖ω' - w'‖ ‖w'‖ := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      _ = 1 := by rw [hw'1]; exact max_eq_right (le_trans hlim_dist hρ1.le)
  refine ⟨(ω' : ℚ̄₂), ω'.2, ?_, hω'1, ?_⟩
  · have h := congrArg (Subtype.val : ↥L → ℚ̄₂) hfix
    push_cast at h
    exact h
  · calc ‖(ω' : ℚ̄₂) - w‖ = ‖ω' - w'‖ := rfl
      _ ≤ ρ := hlim_dist
      _ < 1 := hρ1

/-! ## Brick 3: successive approximation -/

/-- **Successive approximation** (plan §1(R)4).  If `π ∈ k` is a shared uniformizer for the
pair `k ≤ L` (`‖π‖` dominates every sub-unit norm of `L`) and every integral element of `L` is
congruent mod `𝔪_L` to an element of `k` (the residue fields agree), then `L ≤ k`: every
`z ∈ O_L` is the limit of its `π`-adic partial sums with `k`-coefficients, and the
finite-dimensional `k` is closed; a `π`-power scaling handles general `z`. -/
theorem le_of_shared_uniformizer (k L : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] k] (hkL : k ≤ L)
    {π : ℚ̄₂} (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ z ∈ L, ‖z‖ < 1 → ‖z‖ ≤ ‖π‖)
    (hres : ∀ z ∈ L, ‖z‖ ≤ 1 → ∃ x ∈ k, ‖z - x‖ < 1) :
    L ≤ k := by
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  haveI : CompleteSpace ↥k := FiniteDimensional.complete ℚ_[2] ↥k
  have hclosed : IsClosed (k : Set ℚ̄₂) :=
    (completeSpace_coe_iff_isComplete.mp ‹CompleteSpace ↥k›).isClosed
  -- integral elements of `L` lie in `k`
  have hO : ∀ z, z ∈ L → ‖z‖ ≤ 1 → z ∈ k := by
    intro z hzL hz1
    have happrox : ∀ n : ℕ, ∃ s ∈ k, ‖z - s‖ ≤ ‖π‖ ^ n := by
      intro n
      induction n with
      | zero => exact ⟨0, k.zero_mem, by simpa using hz1⟩
      | succ n ih =>
        obtain ⟨s, hsk, hs⟩ := ih
        have hπn0 : π ^ n ≠ 0 := pow_ne_zero n hπ0
        have hyL : (z - s) / π ^ n ∈ L :=
          L.div_mem (L.sub_mem hzL (hkL hsk)) (pow_mem (hkL hπk) n)
        have hy1 : ‖(z - s) / π ^ n‖ ≤ 1 := by
          rw [norm_div, norm_pow, div_le_one (by positivity)]
          exact hs
        obtain ⟨x, hxk, hx⟩ := hres _ hyL hy1
        have hyxπ : ‖(z - s) / π ^ n - x‖ ≤ ‖π‖ :=
          hπmax _ (L.sub_mem hyL (hkL hxk)) hx
        refine ⟨s + π ^ n * x, k.add_mem hsk (k.mul_mem (pow_mem hπk n) hxk), ?_⟩
        have hrw : z - (s + π ^ n * x) = π ^ n * ((z - s) / π ^ n - x) := by
          field_simp; ring
        rw [hrw, norm_mul, norm_pow, pow_succ]
        exact mul_le_mul_of_nonneg_left hyxπ (by positivity)
    choose s hsk hsb using happrox
    have hlim : Tendsto s atTop (nhds z) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hπpos.le hπ1)
      rw [norm_sub_rev]
      exact hsb n
    exact hclosed.mem_of_tendsto hlim (Eventually.of_forall hsk)
  -- scale a general element into the unit ball
  intro z hzL
  rcases eq_or_ne z 0 with rfl | hz0
  · exact k.zero_mem
  have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ‖π‖ ^ j < ‖z‖⁻¹ := exists_pow_lt_of_lt_one (by positivity) hπ1
  have hint : ‖π ^ j * z‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    calc ‖π‖ ^ j * ‖z‖ ≤ ‖z‖⁻¹ * ‖z‖ := mul_le_mul_of_nonneg_right hj.le hzpos.le
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hzpos)
  have hmem : π ^ j * z ∈ k := hO _ (L.mul_mem (pow_mem (hkL hπk) j) hzL) hint
  have hz : z = (π ^ j)⁻¹ * (π ^ j * z) := by
    field_simp
  rw [hz]
  exact k.mul_mem (k.inv_mem (pow_mem hπk j)) hmem

end GQ2.TeichmullerLift
