/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.DeepCount.Filtration

@[expose] public section

/-!
# Head, tail, and assembly bounds for the deep count

The tail survivor, the head bound, and their assembly into the structural inequality.

See `GQ2.DeepCount` for the paper-facing overview, source citations, and deviations.
-/

namespace GQ2

open ContCoh LocalKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The tail survivor: `#Dc_{2e} ≥ 2`

The graded squaring at `i = e` kills `[−1] ≠ [1]` (`‖−1 − 1‖ = ‖2‖ = ‖π‖^e` exactly), so it
is NOT injective; on equal-card grs it is then not surjective, and any unit class outside
its range is a NONZERO element of `Dc_{2e}`: were it zero, the Kummer kernel would make the
unit a square `w²` with `w ∈ U_e` (the dichotomy), putting it back in the range. -/

section TailSurvivor

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)

/-- `−1` is a depth-`e` unit: `‖−1 − 1‖ = ‖2‖ = ‖π‖^e`. -/
theorem neg_one_mem_depthUnits {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) :
    (-1 : (↥k)ˣ) ∈ depthUnits k π e := by
  have hcast : (((-1 : (↥k)ˣ) : ↥k) : ℚ̄₂) = -1 := by
    push_cast; ring
  constructor
  · show ‖(((-1 : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ = 1
    rw [hcast, norm_neg, norm_one]
  · show ‖(((-1 : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ e
    rw [hcast, show (-1 : ℚ̄₂) - 1 = -2 by ring, norm_neg, he]

/-- `−1` is NOT a depth-`(e+1)` unit (`‖π‖^e > ‖π‖^{e+1}`). -/
theorem neg_one_not_mem_depthUnits_succ (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) :
    (-1 : (↥k)ˣ) ∉ depthUnits k π (e + 1) := by
  intro h
  have hd := h.2
  have hcast : (((-1 : (↥k)ˣ) : ↥k) : ℚ̄₂) = -1 := by
    push_cast; ring
  rw [hcast, show (-1 : ℚ̄₂) - 1 = -2 by ring, norm_neg, he] at hd
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  have : ‖π‖ ^ (e + 1) < ‖π‖ ^ e := by
    rw [pow_succ]
    calc ‖π‖ ^ e * ‖π‖ < ‖π‖ ^ e * 1 := mul_lt_mul_of_pos_left hπ1 (pow_pos hπpos e)
      _ = ‖π‖ ^ e := mul_one _
  exact absurd hd (not_le.mpr this)

/-- **The tail survivor**: some depth-`2e` Kummer class is nonzero.  The graded squaring at
`i = e` has `[−1]` in its kernel but `[−1] ≠ [1]`, so it is not injective, hence (equal-card
grs) not surjective; a unit class `[a]` outside the range gives `kummerClassK a ≠ 0` — were
it zero, the Kummer kernel would write `a = w²` with `w ∈ U_e` (norm-one by taking norms;
depth-`e` by the dichotomy), and `[a] = grSq [w]`. -/
theorem exists_kummerDepth_ne_zero [FiniteDimensional ℚ_[2] k]
    (_ : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (_ : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) {f : ℕ}
    (hcard_e : Nat.card (↥(depthUnits k π e) ⧸
      (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e)) = 2 ^ f)
    (hcard_2e : Nat.card (↥(depthUnits k π (2 * e)) ⧸
      (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e))) = 2 ^ f) :
    ∃ ξ ∈ kummerDepth k π (2 * e), ξ ≠ 0 := by
  haveI hfin1 : Finite (↥(depthUnits k π e) ⧸
      (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e)) :=
    (Nat.card_pos_iff.mp (by rw [hcard_e]; positivity)).2
  haveI hfin2 : Finite (↥(depthUnits k π (2 * e)) ⧸
      (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e))) :=
    (Nat.card_pos_iff.mp (by rw [hcard_2e]; positivity)).2
  -- `grSq` at `i = e` is not injective: `[−1] ≠ [1]` squares to `1`
  have hker : grSq k π hπ1.le he (le_refl e)
      (QuotientGroup.mk ⟨(-1 : (↥k)ˣ), neg_one_mem_depthUnits k π he⟩) = 1 := by
    have h1 : (QuotientGroup.mk (sqHom k π hπ1.le he (le_refl e)
        ⟨(-1 : (↥k)ˣ), neg_one_mem_depthUnits k π he⟩)
        : ↥(depthUnits k π (2 * e)) ⧸
          (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e))) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hval : ((sqHom k π hπ1.le he (le_refl e)
          ⟨(-1 : (↥k)ˣ), neg_one_mem_depthUnits k π he⟩
          : ↥(depthUnits k π (2 * e))) : (↥k)ˣ) = 1 := by
        show ((-1 : (↥k)ˣ)) ^ 2 = 1
        rw [neg_one_sq]
      rw [hval]
      exact one_mem _
    exact h1
  have hne : (QuotientGroup.mk (⟨(-1 : (↥k)ˣ), neg_one_mem_depthUnits k π he⟩
      : ↥(depthUnits k π e)) : ↥(depthUnits k π e) ⧸
        (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e)) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact neg_one_not_mem_depthUnits_succ k π hπ0 hπ1 he
  have hnotinj : ¬ Function.Injective (grSq k π hπ1.le he (le_refl e)) := by
    intro hinj
    exact hne ((injective_iff_map_eq_one _).mp hinj _ hker)
  -- not injective + equal finite cards ⟹ not surjective
  have hnotsurj : ¬ Function.Surjective (grSq k π hπ1.le he (le_refl e)) := by
    intro hsurj
    haveI := Fintype.ofFinite (↥(depthUnits k π e) ⧸
      (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e))
    haveI := Fintype.ofFinite (↥(depthUnits k π (2 * e)) ⧸
      (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e)))
    have hcards : Fintype.card (↥(depthUnits k π (2 * e)) ⧸
          (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e)))
        = Fintype.card (↥(depthUnits k π e) ⧸
          (depthUnits k π (e + 1)).subgroupOf (depthUnits k π e)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard_e, hcard_2e]
    exact hnotinj ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcards.symm⟩).1
  obtain ⟨yq, hyq⟩ := not_forall.mp hnotsurj
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective yq
  -- the survivor
  refine ⟨kummerClassK k (a : (↥k)ˣ),
    (mem_kummerDepth_iff k π).mpr ⟨(a : (↥k)ˣ), a.2, rfl⟩, ?_⟩
  intro h0
  obtain ⟨w, hw⟩ := exists_sq_of_kummerClassK_eq_zero k _ h0
  -- `w` is a norm-one unit
  have hw0 : w ≠ 0 := by
    intro hz
    have := unitCoe_ne_zero k (a : (↥k)ˣ)
    rw [← hw, hz] at this
    exact this (by push_cast; ring)
  have hwn1 : ‖(w : ℚ̄₂)‖ = 1 := by
    have hsq : ‖(w : ℚ̄₂)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← SubmonoidClass.coe_pow, hw]
      exact a.2.1
    nlinarith [norm_nonneg (w : ℚ̄₂), sq_nonneg (‖(w : ℚ̄₂)‖ - 1)]
  -- `w` has depth `e` (the dichotomy)
  have hwd : ‖(w : ℚ̄₂) - 1‖ ≤ ‖π‖ ^ e := by
    rcases norm_sq_sub_one' ((w : ℚ̄₂)) with hcase | hcase
    · rwa [he] at hcase
    · have h2e : ‖(w : ℚ̄₂) - 1‖ ^ 2 ≤ (‖π‖ ^ e) ^ 2 := by
        calc ‖(w : ℚ̄₂) - 1‖ ^ 2 = ‖((w : ℚ̄₂)) ^ 2 - 1‖ := hcase.symm
          _ ≤ ‖π‖ ^ (2 * e) := by
              rw [← SubmonoidClass.coe_pow, hw]
              exact a.2.2
          _ = (‖π‖ ^ e) ^ 2 := by rw [← pow_mul, mul_comm]
      exact le_of_pow_le_pow_left₀ (by omega) (le_of_lt (pow_pos (norm_pos_iff.mpr hπ0) e)) h2e
  have hwmem : Units.mk0 w hw0 ∈ depthUnits k π e := ⟨hwn1, hwd⟩
  -- `grSq [w] = [a]` since `w² = a` on the nose — contradicting the escape
  refine hyq ⟨QuotientGroup.mk ⟨Units.mk0 w hw0, hwmem⟩, ?_⟩
  have hunit : (Units.mk0 w hw0) ^ 2 = (a : (↥k)ˣ) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hw
  have hval : (QuotientGroup.mk (sqHom k π hπ1.le he (le_refl e) ⟨Units.mk0 w hw0, hwmem⟩)
      : ↥(depthUnits k π (2 * e)) ⧸
        (depthUnits k π (2 * e + 1)).subgroupOf (depthUnits k π (2 * e)))
      = QuotientGroup.mk a := by
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show (Units.mk0 w hw0) ^ 2 = (a : (↥k)ˣ)
    exact hunit
  exact hval

end TailSurvivor

/-! ## The head: `#(M ⧸ Dc_1) ≤ 2`

Two inputs: the level-`0` collapse `Dc_0 ≤ Dc_1` (the residue group `U⁰/U¹` has ODD order
`2^f − 1`, so squaring is bijective on it — `grSq` at `i = 0` is the squaring map of the
gr-group itself), and the `π`-parity decomposition (every `a ∈ k^×` is `u·π^m` with `u`
norm-one, by discreteness), which makes `M ⧸ Dc_1` generated by the single 2-torsion class
`mk [π]`. -/

section Head

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)

/-- **The ℕ-valuation** from discreteness: a nonzero integral `k`-element has norm an exact
power of `‖π‖`.  Take the least `m` with `‖π‖^{m+1} < ‖x‖`; then `x/π^m` is integral of norm
`> ‖π‖`, hence norm one by `hπ_max`. -/
theorem exists_nat_val (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {x : ℚ̄₂} (hx : x ∈ k) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, ‖x‖ = ‖π‖ ^ m := by
  have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  -- the least `m` with `‖π‖^{m+1} < ‖x‖`
  have hex : ∃ m : ℕ, ‖π‖ ^ (m + 1) < ‖x‖ := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hxpos hπ1
    exact ⟨m, lt_of_le_of_lt (pow_le_pow_of_le_one (norm_nonneg π) hπ1.le (Nat.le_succ m)) hm⟩
  classical
  refine ⟨Nat.find hex, ?_⟩
  have hfound : ‖π‖ ^ (Nat.find hex + 1) < ‖x‖ := Nat.find_spec hex
  have hupper : ‖x‖ ≤ ‖π‖ ^ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero]
      exact hx1
    · have hnot := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      rw [not_lt] at hnot
      have harith : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rwa [harith] at hnot
  -- `y := x / π^m` is integral (norm ≤ 1) with `‖y‖ > ‖π‖`, hence `‖y‖ = 1`
  have hπmpos : (0 : ℝ) < ‖π‖ ^ Nat.find hex := pow_pos hπpos _
  have hy1 : ‖x / π ^ Nat.find hex‖ ≤ 1 := by
    rw [norm_div, norm_pow, div_le_one hπmpos]
    exact hupper
  have hygt : ‖π‖ < ‖x / π ^ Nat.find hex‖ := by
    rw [norm_div, norm_pow, lt_div_iff₀ hπmpos, ← pow_succ']
    exact hfound
  have hyeq : ‖x / π ^ Nat.find hex‖ = 1 := by
    by_contra hne
    have hlt : ‖x / π ^ Nat.find hex‖ < 1 := lt_of_le_of_ne hy1 hne
    exact absurd (hπmax _ (div_mem hx (pow_mem hπk _)) hlt) (not_le.mpr hygt)
  calc ‖x‖ = ‖x / π ^ Nat.find hex‖ * ‖π‖ ^ Nat.find hex := by
        rw [norm_div, norm_pow, div_mul_cancel₀ _ (ne_of_gt hπmpos)]
    _ = ‖π‖ ^ Nat.find hex := by rw [hyeq, one_mul]

/-- **The level-`0` collapse** `Dc_0 ≤ Dc_1`: the residue group `U⁰/U¹` has odd order
`2^f − 1` (B13 `card_gr_zero`, as a hypothesis over the `depthUnits 0`-form), so squaring is
bijective on it and every norm-one unit is a square times a principal unit. -/
theorem kummerDepth_zero_collapse (hπle : ‖π‖ ≤ 1) {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e)
    {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_0 : Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) = 2 ^ f - 1) :
    kummerDepth k π 0 ≤ kummerDepth k π 1 := by
  -- `grSq` at `i = 0` is the squaring map of the gr-group itself; injective by odd order
  have hcardpos : 0 < Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) := by
    rw [hcard_0]
    have : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) hf_pos
    omega
  haveI hfin : Finite (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) :=
    (Nat.card_pos_iff.mp hcardpos).2
  have hodd : Odd (Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0))) := by
    rw [hcard_0]
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) hf_pos
    have heven : Even (2 ^ f) := by
      rcases f with _ | f'
      · omega
      · exact ⟨2 ^ f', by rw [pow_succ, mul_two]⟩
    rcases heven with ⟨r, hr⟩
    exact ⟨r - 1, by omega⟩
  -- the squaring map on the gr is injective (no 2-torsion in odd order), hence surjective
  have hinj : Function.Injective (grSq k π hπle he (Nat.zero_le e)) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H v =>
      -- `grSq (mk v) = (mk v)²` at `i = 0`
      have hq' : ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
          (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ^ 2 = 1 := by
        have hval : (QuotientGroup.mk (sqHom k π hπle he (Nat.zero_le e) v)
            : ↥(depthUnits k π (2 * 0)) ⧸
              (depthUnits k π (2 * 0 + 1)).subgroupOf (depthUnits k π (2 * 0))) = 1 := hq
        have hmk : (QuotientGroup.mk (sqHom k π hπle he (Nat.zero_le e) v)
            : ↥(depthUnits k π (2 * 0)) ⧸
              (depthUnits k π (2 * 0 + 1)).subgroupOf (depthUnits k π (2 * 0)))
            = ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
              (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ^ 2 := by
          have : (QuotientGroup.mk (v ^ 2) : ↥(depthUnits k π 0) ⧸
              (depthUnits k π 1).subgroupOf (depthUnits k π 0))
              = ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
                (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ^ 2 := by
            rw [← QuotientGroup.mk_pow]
          exact this
        rw [← hmk]
        exact hval
      -- odd order kills the 2-torsion element `mk v`
      have hdvd2 : orderOf ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
          (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hq'
      have hdvdcard : orderOf ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
          (depthUnits k π 1).subgroupOf (depthUnits k π 0))) ∣ Nat.card _ :=
        orderOf_dvd_natCard _
      have hone : orderOf ((QuotientGroup.mk v : ↥(depthUnits k π 0) ⧸
          (depthUnits k π 1).subgroupOf (depthUnits k π 0))) = 1 := by
        have hd := Nat.dvd_gcd hdvd2 hdvdcard
        have hgcd : Nat.gcd 2 (Nat.card (↥(depthUnits k π 0) ⧸
            (depthUnits k π 1).subgroupOf (depthUnits k π 0))) = 1 := by
          rw [Nat.gcd_rec, Nat.odd_iff.mp hodd, Nat.gcd_one_left]
        rw [hgcd] at hd
        exact Nat.dvd_one.mp hd
      rw [← orderOf_eq_one_iff]
      exact hone
  have hsurj : Function.Surjective (grSq k π hπle he (Nat.zero_le e)) := by
    haveI := Fintype.ofFinite (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0))
    exact Finite.surjective_of_injective hinj
  -- consume exactly as in the even collapse
  rintro ξ ⟨a, ha, rfl⟩
  obtain ⟨wq, hwq⟩ := hsurj (QuotientGroup.mk (⟨a, ha⟩ : ↥(depthUnits k π 0)))
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective wq
  have hco : (QuotientGroup.mk (sqHom k π hπle he (Nat.zero_le e) w)
      : ↥(depthUnits k π (2 * 0)) ⧸
        (depthUnits k π (2 * 0 + 1)).subgroupOf (depthUnits k π (2 * 0)))
      = QuotientGroup.mk ⟨a, ha⟩ := hwq
  rw [QuotientGroup.eq] at hco
  rw [Subgroup.mem_subgroupOf] at hco
  set b : (↥k)ˣ := ((w : (↥k)ˣ) ^ 2)⁻¹ * a with hbdef
  have hb : b ∈ depthUnits k π 1 := hco
  have hdecomp : a = (w : (↥k)ˣ) ^ 2 * b := by
    rw [hbdef, mul_inv_cancel_left]
  rw [show kummerClassK k a = kummerClassK k ((w : (↥k)ˣ) ^ 2) + kummerClassK k b from by
    rw [← kummerClassK_mul, ← hdecomp]]
  rw [kummerClassK_eq_zero_of_sq k ((w : (↥k)ˣ) ^ 2) ((w : (↥k)ˣ) : ↥k)
    (by rw [Units.val_pow_eq_pow_val]), zero_add]
  exact ⟨b, hb, rfl⟩

/-- `kummerClassK` of a power: `[a^m] = m • [a]`. -/
theorem kummerClassK_pow (a : (↥k)ˣ) (m : ℕ) :
    kummerClassK k (a ^ m) = m • kummerClassK k a := by
  induction m with
  | zero => rw [pow_zero, kummerClassK_one, zero_nsmul]
  | succ n ih => rw [pow_succ, kummerClassK_mul, ih, succ_nsmul]

/-- 2-torsion `nsmul` reduction: `m • ξ = (m % 2) • ξ`. -/
theorem nsmul_mod_two {G : Type*} [AddCommGroup G] (ξ : G) (hξ : ξ + ξ = 0) (m : ℕ) :
    m • ξ = (m % 2) • ξ := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  rw [add_nsmul, mul_comm, mul_nsmul, two_nsmul, ← nsmul_add, hξ, smul_zero, zero_add]

/-- The uniformizer as a unit of `k`. -/
noncomputable def piUnit (hπk : π ∈ k) (hπ0 : π ≠ 0) : (↥k)ˣ :=
  Units.mk0 ⟨π, hπk⟩ (fun h => hπ0 (by simpa using congrArg Subtype.val h))


/-- **The head bound**: `M ⧸ Dc_1` is generated by the single 2-torsion class of the
uniformizer (`π`-parity via the ℕ-valuation, unit part into `Dc_1` by the level-`0`
collapse), so it has at most `2` elements. -/
theorem card_quot_kummerDepth_one_le_two [FiniteDimensional ℚ_[2] k]
    [Finite (H1 k.fixingSubgroup (ZMod 2))]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_0 : Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) = 2 ^ f - 1) :
    Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1) ≤ 2 := by
  -- the classification: every element of the quotient is `0` or `mk [π₀]`
  have hkey : ∀ b : (↥k)ˣ, ‖((b : ↥k) : ℚ̄₂)‖ ≤ 1 →
      (QuotientAddGroup.mk (kummerClassK k b)
          : H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1) = 0
        ∨ (QuotientAddGroup.mk (kummerClassK k b)
          : H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1)
          = QuotientAddGroup.mk (kummerClassK k (piUnit k π hπk hπ0)) := by
    intro b hb1
    obtain ⟨m, hm⟩ := exists_nat_val k π hπk hπ0 hπ1 hπmax
      (by exact_mod_cast ((b : ↥k)).2) (unitCoe_ne_zero k b) hb1
    -- the norm-one part `u := b · π₀⁻ᵐ`
    have hval : (((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂)
        = (((b : ↥k) : ℚ̄₂)) * ((π : ℚ̄₂) ^ m)⁻¹ := by
      push_cast; rfl
    have hπpos : (0 : ℝ) < ‖π‖ := norm_pos_iff.mpr hπ0
    have hu1 : ‖(((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ = 1 := by
      rw [hval, norm_mul, norm_inv, norm_pow, hm]
      field_simp
    -- its class lies in `Dc_1` (level-`0` collapse)
    have humem : kummerClassK k (b * (piUnit k π hπk hπ0 ^ m)⁻¹)
        ∈ kummerDepth k π 1 := by
      refine kummerDepth_zero_collapse k π hπ1.le he hf_pos hcard_0 ?_
      refine (mem_kummerDepth_iff k π).mpr ⟨_, ⟨hu1, ?_⟩, rfl⟩
      rw [pow_zero]
      calc ‖(((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1‖
          ≤ max ‖(((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ ‖(1 : ℚ̄₂)‖ := by
            rw [show (((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) - 1
                = (((b * (piUnit k π hπk hπ0 ^ m)⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) + (-1) by ring]
            refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
            rw [norm_neg]
        _ = 1 := by rw [hu1, norm_one, max_self]
    -- decompose the class and reduce the multiplicity mod 2
    have hcls : kummerClassK k b
        = kummerClassK k (b * (piUnit k π hπk hπ0 ^ m)⁻¹)
          + m • kummerClassK k (piUnit k π hπk hπ0) := by
      rw [← kummerClassK_pow, ← kummerClassK_mul]
      congr 1
      group
    have hmk : (QuotientAddGroup.mk (kummerClassK k b)
        : H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1)
        = QuotientAddGroup.mk ((m % 2) • kummerClassK k (piUnit k π hπk hπ0)) := by
      rw [hcls, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr humem,
        zero_add, nsmul_mod_two _ (h1_add_self _) m]
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · left
      rw [hmk, h0, zero_nsmul, QuotientAddGroup.mk_zero]
    · right
      rw [hmk, h1, one_nsmul]
  -- surjection from `Fin 2`
  set g : Fin 2 → H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1 :=
    fun i => if i = 0 then 0
      else QuotientAddGroup.mk (kummerClassK k (piUnit k π hπk hπ0)) with hg
  have hg0 : g 0 = 0 := by rw [hg]; simp
  have hg1 : g 1 = QuotientAddGroup.mk (kummerClassK k (piUnit k π hπk hπ0)) := by
    rw [hg]; simp
  have hsurj : Function.Surjective g := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H ξ =>
      obtain ⟨a, rfl⟩ := kummerClassK_surjective k ξ
      rcases le_or_gt ‖((a : ↥k) : ℚ̄₂)‖ 1 with hle | hgt
      · rcases hkey a hle with h | h
        · exact ⟨0, by rw [hg0]; exact h.symm⟩
        · exact ⟨1, by rw [hg1]; exact h.symm⟩
      · have hinv1 : ‖(((a⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂)‖ ≤ 1 := by
          rw [show (((a⁻¹ : (↥k)ˣ) : ↥k) : ℚ̄₂) = (((a : ↥k) : ℚ̄₂))⁻¹ from by
            rw [Units.val_inv_eq_inv_val]; push_cast; ring, norm_inv]
          exact inv_le_one_of_one_le₀ hgt.le
        have hswap : kummerClassK k a⁻¹ = kummerClassK k a := kummerClassK_inv k a
        rcases hkey a⁻¹ hinv1 with h | h
        · refine ⟨0, by rw [hg0]; rw [hswap] at h; exact h.symm⟩
        · refine ⟨1, by rw [hg1]; rw [hswap] at h; exact h.symm⟩
  calc Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1)
      ≤ Nat.card (Fin 2) := Nat.card_le_card_of_surjective g hsurj
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]

end Head

/-! ## The assembly: `#(M ⧸ Dc_{e+1}) ≤ #Dc_e`

The paired descent: `R(s) : #(M⧸Dc_{e+1})·#Dc_{e+1+s} ≤ #Dc_e·#(M⧸Dc_{e−s})` holds at
`s = 0` with equality (double Lagrange), and each step trades the level `e−s−1` on the right
for the level `e+1+s` on the left — same-parity levels summing to `2e`, where the class-gr
counts compare (`= 2^f` odd / `= 1 ≤` even).  At `s = e−1` the head (`≤ 2`) and the tail
survivor (`≥ 2`) close the inequality. -/

section Assembly

variable (k : IntermediateField ℚ_[2] ℚ̄₂) (π : ℚ̄₂)
variable [Finite (H1 k.fixingSubgroup (ZMod 2))]

omit [Finite (H1 k.fixingSubgroup (ZMod 2))] in
/-- Lagrange step-down for the class filtration:
`#Dc_j = #(Dc_j/Dc_{j+1}) · #Dc_{j+1}`. -/
theorem card_kummerDepth_step (hπ1 : ‖π‖ ≤ 1) (j : ℕ) :
    Nat.card ↥(kummerDepth k π j)
      = Nat.card (↥(kummerDepth k π j) ⧸
          (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j))
        * Nat.card ↥(kummerDepth k π (j + 1)) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j))]
  congr 1
  exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe
    (kummerDepth_antitone k π hπ1 (Nat.le_succ j))).toEquiv

/-- Lagrange step-up for the ambient quotients:
`#(M⧸Dc_{j+1}) = #(M⧸Dc_j) · #(Dc_j/Dc_{j+1})`. -/
theorem card_quot_kummerDepth_step (hπ1 : ‖π‖ ≤ 1) (j : ℕ) :
    Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (j + 1))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π j)
        * Nat.card (↥(kummerDepth k π j) ⧸
          (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j)) := by
  haveI : Nonempty ↥(kummerDepth k π (j + 1)) := ⟨⟨0, zero_mem _⟩⟩
  have h1 : Nat.card (H1 k.fixingSubgroup (ZMod 2))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (j + 1))
        * Nat.card ↥(kummerDepth k π (j + 1)) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h2 : Nat.card (H1 k.fixingSubgroup (ZMod 2))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π j)
        * Nat.card ↥(kummerDepth k π j) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h3 := card_kummerDepth_step k π hπ1 j
  have h4 : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (j + 1))
        * Nat.card ↥(kummerDepth k π (j + 1))
      = (Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π j)
        * Nat.card (↥(kummerDepth k π j) ⧸
          (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j)))
        * Nat.card ↥(kummerDepth k π (j + 1)) := by
    rw [← h1, h2, h3]
    ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h4

/-- **The paired level comparison**: for `1 ≤ j ≤ e − 1`, the class-gr at `j` is at most the
class-gr at `2e − j` (same parity: odd levels are both `2^f`, even levels collapse to `1`). -/
theorem card_classGr_pair_le [FiniteDimensional ℚ_[2] k]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_gr : ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f)
    {j : ℕ} (hj1 : 1 ≤ j) (hje : j ≤ e - 1) :
    Nat.card (↥(kummerDepth k π j) ⧸
        (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j))
      ≤ Nat.card (↥(kummerDepth k π (2 * e - j)) ⧸
        (kummerDepth k π (2 * e - j + 1)).addSubgroupOf (kummerDepth k π (2 * e - j))) := by
  haveI : Nonempty (↥(kummerDepth k π (2 * e - j)) ⧸
      (kummerDepth k π (2 * e - j + 1)).addSubgroupOf (kummerDepth k π (2 * e - j))) :=
    ⟨0⟩
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨t, ht⟩
  · -- even level: the left side collapses to `1`
    have hji : j = 2 * i := by omega
    have hi1 : 1 ≤ i := by omega
    have hie : i + 1 ≤ e := by omega
    have hLHS : Nat.card (↥(kummerDepth k π j) ⧸
        (kummerDepth k π (j + 1)).addSubgroupOf (kummerDepth k π j)) = 1 := by
      rw [hji]
      exact card_classGr_even k π hπk hπ0 hπ1 hπmax he hf_pos hie
        (hcard_gr i hi1) (hcard_gr (2 * i) (by omega))
    rw [hLHS]
    exact Nat.card_pos
  · -- odd level: both sides are `2^f`
    subst ht
    rw [show 2 * e - (2 * t + 1) = 2 * (e - t - 1) + 1 from by omega]
    rw [card_classGr_odd k π hπk hπ0 hπ1 hπmax he he_pos (by omega)
        (hcard_gr (2 * t + 1) (by omega)),
      card_classGr_odd k π hπk hπ0 hπ1 hπmax he he_pos (by omega)
        (hcard_gr (2 * (e - t - 1) + 1) (by omega))]

/-- **THE STRUCTURAL COUNT** — the single remaining input of (H4)'s sharpness:
`#(M ⧸ Dc_{e+1}) ≤ #Dc_e`, by the paired descent between the double-Lagrange identity at
`s = 0` and the head/tail comparison at `s = e − 1`. -/
theorem card_quot_deep_le_card_mid [FiniteDimensional ℚ_[2] k]
    (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_zero : Nat.card (↥(normUnits k) ⧸
      (depthUnits k π 1).subgroupOf (normUnits k)) = 2 ^ f - 1)
    (hcard_gr : ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f) :
    Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
      ≤ Nat.card ↥(kummerDepth k π e) := by
  have hcard_0 : Nat.card (↥(depthUnits k π 0) ⧸
      (depthUnits k π 1).subgroupOf (depthUnits k π 0)) = 2 ^ f - 1 := by
    rw [depthUnits_zero]
    exact hcard_zero
  -- the paired descent
  have hR : ∀ s : ℕ, s ≤ e - 1 →
      Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (e + 1 + s))
        ≤ Nat.card ↥(kummerDepth k π e)
          * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s)) := by
    intro s
    induction s with
    | zero =>
      intro _
      show Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (e + 1))
        ≤ Nat.card ↥(kummerDepth k π e)
          * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π e)
      have h1 : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (e + 1))
          = Nat.card (H1 k.fixingSubgroup (ZMod 2)) :=
        (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm
      have h2 : Nat.card (H1 k.fixingSubgroup (ZMod 2))
          = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π e)
            * Nat.card ↥(kummerDepth k π e) :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
      refine le_of_eq ?_
      rw [h1, h2, mul_comm]
    | succ s ih =>
      intro hs
      have hR_s := ih (by omega)
      -- step the two sides
      have hAstep := card_kummerDepth_step k π hπ1.le (e + 1 + s)
      have hidx : e - s - 1 + 1 = e - s := by omega
      have hBstep : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s))
          = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s - 1))
            * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
              (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := by
        rw [← hidx]
        exact card_quot_kummerDepth_step k π hπ1.le (e - s - 1)
      -- the paired comparison at `j := e − s − 1`
      have hidx2 : 2 * e - (e - s - 1) = e + 1 + s := by omega
      have hpair : Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
            (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1)))
          ≤ Nat.card (↥(kummerDepth k π (e + 1 + s)) ⧸
            (kummerDepth k π (e + 1 + s + 1)).addSubgroupOf (kummerDepth k π (e + 1 + s))) := by
        have := card_classGr_pair_le k π hπk hπ0 hπ1 hπmax he he_pos hf_pos hcard_gr
          (j := e - s - 1) (by omega) (by omega)
        rwa [hidx2] at this
      have hg'pos : 0 < Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
          (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := by
        haveI : Nonempty (↥(kummerDepth k π (e - s - 1)) ⧸
            (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := ⟨0⟩
        exact Nat.card_pos
      -- the multiplicative bookkeeping, then cancel the small gr
      have hchain : (Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
            * Nat.card ↥(kummerDepth k π (e + 1 + (s + 1))))
            * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
              (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1)))
          ≤ (Nat.card ↥(kummerDepth k π e)
            * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - (s + 1))))
            * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
              (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := by
        have hidx3 : e + 1 + (s + 1) = e + 1 + s + 1 := by omega
        have hidx4 : e - (s + 1) = e - s - 1 := by omega
        rw [hidx3, hidx4]
        calc (Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
              * Nat.card ↥(kummerDepth k π (e + 1 + s + 1)))
              * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
                (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1)))
            ≤ (Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
              * Nat.card ↥(kummerDepth k π (e + 1 + s + 1)))
              * Nat.card (↥(kummerDepth k π (e + 1 + s)) ⧸
                (kummerDepth k π (e + 1 + s + 1)).addSubgroupOf (kummerDepth k π (e + 1 + s))) := by
              exact Nat.mul_le_mul_left _ hpair
          _ = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
              * Nat.card ↥(kummerDepth k π (e + 1 + s)) := by
              rw [hAstep]
              ring
          _ ≤ Nat.card ↥(kummerDepth k π e)
              * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s)) := hR_s
          _ = (Nat.card ↥(kummerDepth k π e)
              * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e - s - 1)))
              * Nat.card (↥(kummerDepth k π (e - s - 1)) ⧸
                (kummerDepth k π (e - s - 1 + 1)).addSubgroupOf (kummerDepth k π (e - s - 1))) := by
              rw [hBstep]
              ring
      exact Nat.le_of_mul_le_mul_right hchain hg'pos
  -- endpoint at `s = e − 1`
  have hend := hR (e - 1) (le_refl _)
  have hidx1 : e + 1 + (e - 1) = 2 * e := by omega
  have hidx2 : e - (e - 1) = 1 := by omega
  rw [hidx1, hidx2] at hend
  -- head and tail
  have hhead := card_quot_kummerDepth_one_le_two k π hπk hπ0 hπ1 hπmax he hf_pos hcard_0
  have htail : 2 ≤ Nat.card ↥(kummerDepth k π (2 * e)) := by
    obtain ⟨ξ, hξ, hne⟩ := exists_kummerDepth_ne_zero k π hπk hπ0 hπ1 hπmax he
      (hcard_gr e he_pos) (hcard_gr (2 * e) (by omega))
    haveI : Nontrivial ↥(kummerDepth k π (2 * e)) :=
      ⟨⟨⟨ξ, hξ⟩, 0, fun h => hne (by simpa using congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hchain : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
        * Nat.card ↥(kummerDepth k π (2 * e))
      ≤ Nat.card ↥(kummerDepth k π e) * Nat.card ↥(kummerDepth k π (2 * e)) := by
    calc Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (2 * e))
        ≤ Nat.card ↥(kummerDepth k π e)
          * Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π 1) := hend
      _ ≤ Nat.card ↥(kummerDepth k π e) * 2 := Nat.mul_le_mul_left _ hhead
      _ ≤ Nat.card ↥(kummerDepth k π e) * Nat.card ↥(kummerDepth k π (2 * e)) :=
          Nat.mul_le_mul_left _ htail
  exact Nat.le_of_mul_le_mul_right hchain (by omega)

end Assembly

end GQ2
