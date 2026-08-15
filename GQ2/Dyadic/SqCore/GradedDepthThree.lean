/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedAbsorption

/-!
# W79-DEPTH3: the depth-3 base by absorption

Wave 78 formalized Labute's Theorem 5 absorption at depth 2 and re-seeded the odd-route
reduction so that its sole remaining layer-side input is the depth-3 base
`GDecideBaseThree h`: at every selected marking, every exactly row-trivial `γ₄`-element
reaches at depth 3.  This file attempts that base by the same absorption one level up:

* the depth-3 leftover normal form (reach times explicit coker classes with
  `𝔽₂`-coefficients), and
* the coefficient kill on the handle-corrected rows.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The target, unfolded -/

section Target

variable {h : ℕ}

/-- The depth-3 base, unfolded: at every selected marking, every exactly row-trivial
`γ₄`-element's level-5 class lies in the depth-3 reach. -/
theorem gDeep_baseThree_iff :
    GDecideBaseThree h ↔
      ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
        nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
          ∀ g ∈ twoCentralSeries (DSq h : Type) 4, nuLam h g = 1 → nu' g = 1 →
            levelMk (DSq h : Type) 5 g ∈ gTowerReach h nu' 3 :=
  Iff.rfl

end Target

/-! ## §2 The reach kernel at every depth

Wave 78's §2, depth-general: at correction depth `k + 2` the whole admissible reach lies in
the layer kernel `gJoinLayerDvd (k + 2)` (readings `2^{k+3}`-divisible) of any row that kills
the Eichler-cleared letters.  Knobs and bundles are wave 75's bounds at the general index; the
Eichler towers read exactly zero; the `x̃₁`-tower gains one bit per depth because each
squaring multiplies the reading by `1 + χ` with `χ` an odd unit. -/

section ReachKernel

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- The `x̃₁`-power reading gains one bit per squaring: `2^{k+4}` divides the reading of
`x̃₁^{2^{k+2}}` at every row. -/
theorem gDeep_xOne_pow_dvd (c : Fin (sqRank h) → ℤ_[2]) (k : ℕ) :
    (2 : ℤ_[2]) ^ (k + 4) ∣ gDelta h c (gTowerXOne h ^ 2 ^ (k + 2)) := by
  induction k with
  | zero =>
    have h4 := gAbs_xOne_pow_four_dvd (h := h) c
    rwa [show (4 : ℕ) = 2 ^ (0 + 2) from by norm_num] at h4
  | succ k ih =>
    have hsq : gTowerXOne h ^ 2 ^ (k + 1 + 2) = (gTowerXOne h ^ 2 ^ (k + 2)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    have hodd : (2 : ℤ_[2]) ∣
        1 + ((chiSq h (gTowerXOne h ^ 2 ^ (k + 2)) : ℤ_[2]ˣ) : ℤ_[2]) := by
      obtain ⟨t, ht⟩ := two_dvd_sub_of_isUnit
        (Units.isUnit (chiSq h (gTowerXOne h ^ 2 ^ (k + 2)))) isUnit_one
      exact ⟨t + 1, by linear_combination ht⟩
    obtain ⟨s, hs⟩ := ih
    obtain ⟨t, ht⟩ := hodd
    refine ⟨t * s, ?_⟩
    rw [hsq, gDelta_pow, normSum_two, hs]
    linear_combination (2 ^ (k + 4) * s) * ht

/-- **The `x̃₁`-tower at depth `k + 2` reads `2^{k+3}`-divisibly at every row** (in fact
`2^{k+4}`-divisibly): the `ℤ₂`-exponent statement, by density of `ℕ`. -/
theorem gDeep_xOne_tower_dvd (c : Fin (sqRank h) → ℤ_[2]) (k : ℕ) (a : ℤ_[2]) :
    (2 : ℤ_[2]) ^ (k + 3) ∣
      gDelta h c (zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ (k + 2) * a)) := by
  have hall : ∀ b : ℤ_[2], (2 : ℤ_[2]) ^ (k + 4) ∣
      gDelta h c (zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ (k + 2) * b)) := by
    intro b
    have hclosed : IsClosed {b : ℤ_[2] | (2 : ℤ_[2]) ^ (k + 4) ∣
        gDelta h c (zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ (k + 2) * b))} := by
      refine (gDelta_isClosed_dvd_set (k + 4)).preimage ?_
      exact (gDelta_continuous c).comp
        ((continuous_zpowZtwo (isProP_DSq h) (gTowerXOne h)).comp
          (continuous_const.mul continuous_id))
    refine PadicInt.denseRange_natCast.induction_on b hclosed ?_
    intro n
    have hcast : (2 : ℤ_[2]) ^ (k + 2) * (n : ℤ_[2]) = ((2 ^ (k + 2) * n : ℕ) : ℤ_[2]) := by
      push_cast; ring
    rw [hcast, zpowZtwo_natCast, pow_mul]
    obtain ⟨s, hs⟩ := gDeep_xOne_pow_dvd (h := h) c k
    rw [gDelta_pow, hs]
    exact ⟨normSum ((chiSq h (gTowerXOne h ^ 2 ^ (k + 2)) : ℤ_[2]ˣ) : ℤ_[2]) n * s, by ring⟩
  exact (pow_dvd_pow (2 : ℤ_[2]) (by omega : k + 3 ≤ k + 4)).trans (hall a)

/-- ⭐⭐ **The depth-`(k+2)` reach lies in the layer kernel of any row that kills the cleared
letters**, at every depth: wave 78's §2 with the depth generalized. -/
theorem gDeep_reach_le_layerDvd {k : ℕ} {c : Fin (sqRank h) → ℤ_[2]}
    (hU : ∀ j, gDelta h c (sqEichU h nu' j) = 0)
    (hV : ∀ j, gDelta h c (sqEichV h nu' j) = 0) :
    gTowerReach h nu' (k + 2) ≤ gJoinLayerDvd h c (k + 2) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z (hz | ⟨x, hx, a, rfl⟩)
  · rcases hz with ⟨t, q, ht, hq, rfl⟩ | ⟨t, ht, rfl⟩
    · exact gJoin_mem_layerDvd.2 (gJoin_knob_dvd (k := k) ht hq c)
    · exact gJoin_mem_layerDvd.2 (gJoin_bundle_dvd (k := k) ht c)
  · simp only [gTowerXLetters, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hx
    obtain (rfl | ⟨j, rfl⟩) | ⟨j, rfl⟩ := hx
    · exact gJoin_mem_layerDvd.2 (gDeep_xOne_tower_dvd c k a)
    · refine gJoin_mem_layerDvd.2 ?_
      rw [gJoin_zpow_vanish (hU j)]
      exact dvd_zero _
    · refine gJoin_mem_layerDvd.2 ?_
      rw [gJoin_zpow_vanish (hV j)]
      exact dvd_zero _

theorem gDeep_reach_le_layerDvd_rowS {k : ℕ} :
    gTowerReach h nu' (k + 2) ≤ gJoinLayerDvd h (gAbsRowS h nu') (k + 2) :=
  gDeep_reach_le_layerDvd (fun j => gAbs_rowS_eichU j) (fun j => gAbs_rowS_eichV j)

theorem gDeep_reach_le_layerDvd_rowX {k : ℕ} :
    gTowerReach h nu' (k + 2) ≤ gJoinLayerDvd h (gAbsRowX h nu') (k + 2) :=
  gDeep_reach_le_layerDvd (fun j => gAbs_rowX_eichU j) (fun j => gAbs_rowX_eichV j)

end ReachKernel

/-! ## §3 The ladder is false at every depth

The `2^k`-th power of wave 78's `σ`-coker class `B = ⁅⁅x₁,σ⁆,x₁⁆` is an exactly row-trivial
`γ_{k+3}`-element whose corrected-`σ`-row reading is `2^{k+2}·unit`: each squaring doubles the
reading exactly, because `χ(B) = 1` makes the norm sum collapse to the exponent.  The
depth-`(k+2)` reach reads `2^{k+3}`-divisibly (§2), so the class never reaches:
`GTowerLayerReach h ν' k` is FALSE for every `k ≥ 2`, at every marking, selected or not.  In
particular the depth-3 base `GDecideBaseThree h` - the sole remaining layer-side input of the
wave-78 reduction - is REFUTED, and so is every deeper re-seed of the same shape. -/

section Refutation

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- Iterated squaring climbs the series: `x ∈ γ_m` gives `x^{2^j} ∈ γ_{m+j}`. -/
theorem gDeep_pow_two_pow_mem {m : ℕ} {x : (DSq h : Type)}
    (hx : x ∈ twoCentralSeries (DSq h : Type) m) (j : ℕ) :
    x ^ 2 ^ j ∈ twoCentralSeries (DSq h : Type) (m + j) := by
  induction j with
  | zero => rwa [pow_zero, pow_one]
  | succ j ih =>
    have hsq : x ^ 2 ^ (j + 1) = (x ^ 2 ^ j) ^ 2 := by rw [← pow_mul, pow_succ]
    rw [hsq]
    exact sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) ih

/-- The reading of a `2^j`-th power of a `χ`-trivial element is `2^j` times the reading. -/
theorem gDeep_delta_pow_two_pow (c : Fin (sqRank h) → ℤ_[2]) {x : (DSq h : Type)}
    (hchi : chiSq h x = 1) (j : ℕ) :
    gDelta h c (x ^ 2 ^ j) = 2 ^ j * gDelta h c x := by
  rw [gDelta_pow, hchi, Units.val_one, normSum_one_base]
  push_cast
  ring

/-- A `2^m·unit` value is not `2^{m+1}`-divisible. -/
theorem gDeep_pow_unit_not_dvd {m : ℕ} {t : ℤ_[2]} {u : ℤ_[2]ˣ}
    (ht : t = 2 ^ m * (u : ℤ_[2])) : ¬ (2 : ℤ_[2]) ^ (m + 1) ∣ t := by
  intro hdvd
  obtain ⟨s, hs⟩ := hdvd
  rw [ht, pow_succ] at hs
  refine gDelta_not_two_dvd_unit u ⟨s, ?_⟩
  have hm : ((2 : ℤ_[2]) ^ m) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine mul_left_cancel₀ hm ?_
  linear_combination hs

/-- The corrected-`σ`-row reading of `B^{2^k}` is exactly `2^{k+2}·unit`. -/
theorem gDeep_delta_B_pow_rowS (k : ℕ) :
    ∃ u : ℤ_[2]ˣ, gDelta h (gAbsRowS h nu') (gAbsB h ^ 2 ^ k) = 2 ^ (k + 2) * (u : ℤ_[2]) := by
  obtain ⟨u, hu⟩ := gAbs_delta_B_rowS (h := h) (nu' := nu')
  refine ⟨u, ?_⟩
  rw [gDeep_delta_pow_two_pow _ gAbs_chiSq_B, hu]
  ring

/-- ⭐⭐⭐ **The layer statement is FALSE at every depth `k ≥ 2` and every marking**: the class
`B^{2^{k}}` is exactly row-trivial in `γ_{k+3}` and reads `2^{k+2}·unit` at the corrected
`σ`-row, while the depth-`(k+2)` reach reads `2^{k+3}`-divisibly.  No marking selection is
needed: the corrected rows exist at every `ν'`. -/
theorem gDeep_not_layerReach (k : ℕ)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    ¬ GTowerLayerReach h nu' (k + 2) := by
  intro H
  have hmem : gAbsB h ^ 2 ^ k ∈ twoCentralSeries (DSq h : Type) (k + 2 + 1) := by
    have h3 := gDeep_pow_two_pow_mem (gAbs_B_mem_three (h := h)) k
    rwa [show 3 + k = k + 2 + 1 from by omega] at h3
  have hl : nuLam h (gAbsB h ^ 2 ^ k) = 1 := by
    rw [gAbsB, map_pow, gTower_row_commP, one_pow]
  have hn : nu' (gAbsB h ^ 2 ^ k) = 1 := by
    rw [gAbsB, map_pow, gTower_row_commP, one_pow]
  have hreach := H _ hmem hl hn
  obtain ⟨u, hu⟩ := gDeep_delta_B_pow_rowS (h := h) (nu' := nu') k
  have hdvd : (2 : ℤ_[2]) ^ (k + 2 + 1) ∣ gDelta h (gAbsRowS h nu') (gAbsB h ^ 2 ^ k) :=
    (gJoin_mem_layerDvd (k := k + 2)).1 (gDeep_reach_le_layerDvd_rowS hreach)
  exact gDeep_pow_unit_not_dvd hu (by rwa [show k + 2 + 1 = k + 2 + 1 from rfl] at hdvd)

/-- The depth-3 instance, in the form the base names. -/
theorem gDeep_not_layerReach_three
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    ¬ GTowerLayerReach h nu' 3 :=
  gDeep_not_layerReach 1 nu'

/-- ⭐⭐⭐ **`GDecideBaseThree h` is FALSE, at every `h`**: the sole remaining layer-side input
of the wave-78 re-seeded reduction fails outright, by the same functional mechanism that
refuted the depth-2 base, one bit deeper. -/
theorem gDeep_not_baseThree : ¬ GDecideBaseThree h := fun H =>
  gDeep_not_layerReach_three (gDecideNu h)
    (H (gDecideNu h) (gDecideNu_sigma h) (gDecideNu_x0 h))

end Refutation

/-! ## §4 The depth-3 coker and the widened spans

The refutation identifies the depth-3 coker candidates: the SQUARES of wave 78's two classes.
This section adjoins them and builds the absorption mechanism one level up: for an exactly
row-trivial `γ₃`-element `c`, wave 78's normal form `c = p·B^{e₁}·C^{e₂}` squares at level 5
into the reach image of `p²` (the engine step, from the depth-2 reach membership of `p`) times
`(B²)^{e₁}(C²)^{e₂}`, all cross-terms dying in `γ₆`.  The `x₁`-defect of `c` follows by the
bundle split.  This is the depth-3 analogue of waves 76-78's `x₁`-bracket supply, with the
coker carrying the two squared classes. -/

section Wide

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

variable (h) in
/-- **The depth-3 coker span**: the subgroup of `Q₅` generated by the squares of the two
wave-77/78 classes. -/
noncomputable def gDeepCoker : Subgroup (levelQuot (DSq h : Type) 5) :=
  Subgroup.closure
    {levelMk (DSq h : Type) 5 (gAbsB h ^ 2), levelMk (DSq h : Type) 5 (gAbsC h ^ 2)}

variable (h) in
/-- **The widened depth-3 reach**: the admissible reach with the squared coker adjoined. -/
noncomputable def gDeepWide
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    Subgroup (levelQuot (DSq h : Type) 5) :=
  gTowerReach h nu' 3 ⊔ gDeepCoker h

variable (h) in
/-- **The widened depth-3 full reach**: the widened reach with the two complement towers. -/
noncomputable def gDeepWideFull
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    Subgroup (levelQuot (DSq h : Type) 5) :=
  gDeepWide h nu' ⊔ gTowerTowXW h 3

theorem gDeep_reach_le_wide : gTowerReach h nu' 3 ≤ gDeepWide h nu' := le_sup_left

theorem gDeep_wide_le_wideFull : gDeepWide h nu' ≤ gDeepWideFull h nu' := le_sup_left

/-- The widened full reach is the full reach with the coker adjoined. -/
theorem gDeep_wideFull_eq :
    gDeepWideFull h nu' = gTowerFullReach h nu' 3 ⊔ gDeepCoker h := by
  rw [gDeepWideFull, gDeepWide, gTowerFullReach, sup_right_comm]

theorem gDeep_B_sq_mem_four : gAbsB h ^ 2 ∈ twoCentralSeries (DSq h : Type) 4 :=
  sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) gAbs_B_mem_three

theorem gDeep_C_sq_mem_four : gAbsC h ^ 2 ∈ twoCentralSeries (DSq h : Type) 4 :=
  sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) gAbs_C_mem_three

/-- The coker is central: both generators are `γ₄`-images. -/
theorem gDeep_coker_central :
    gDeepCoker h ≤ Subgroup.center (levelQuot (DSq h : Type) 5) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact Subgroup.mem_center_iff.2 fun g => gTower_img_central (k := 3) gDeep_B_sq_mem_four g
  · exact Subgroup.mem_center_iff.2 fun g => gTower_img_central (k := 3) gDeep_C_sq_mem_four g

theorem gDeep_coker_normal : (gDeepCoker h).Normal := by
  constructor
  intro n hn g
  have hc : g * n = n * g := Subgroup.mem_center_iff.1 (gDeep_coker_central hn) g
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact hn

/-- The coker generators are involutions in `Q₅`: squares of `γ₄`-elements die at level 5. -/
theorem gDeep_B_img_sq : levelMk (DSq h : Type) 5 (gAbsB h ^ 2) ^ 2 = 1 := by
  rw [← map_pow]
  exact (lim_mem_twoCentralSeries_iff_levelMk 5 _).mp
    (sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) gDeep_B_sq_mem_four)

theorem gDeep_C_img_sq : levelMk (DSq h : Type) 5 (gAbsC h ^ 2) ^ 2 = 1 := by
  rw [← map_pow]
  exact (lim_mem_twoCentralSeries_iff_levelMk 5 _).mp
    (sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) gDeep_C_sq_mem_four)

/-- **Every coker element is `(B²)^{e₁}·(C²)^{e₂}` with `𝔽₂`-exponents**: the span of two
central commuting involutions, wave 78's `gAbs_coker_form` one level up. -/
theorem gDeep_coker_form {n : levelQuot (DSq h : Type) 5} (hn : n ∈ gDeepCoker h) :
    ∃ e₁ e₂ : ℕ, e₁ ≤ 1 ∧ e₂ ≤ 1 ∧
      n = levelMk (DSq h : Type) 5 (gAbsB h ^ 2) ^ e₁ *
        levelMk (DSq h : Type) 5 (gAbsC h ^ 2) ^ e₂ := by
  set Bc := levelMk (DSq h : Type) 5 (gAbsB h ^ 2) with hBc
  set Cc := levelMk (DSq h : Type) 5 (gAbsC h ^ 2) with hCc
  have hcommute : Commute Cc Bc := by
    show Cc * Bc = Bc * Cc
    exact Subgroup.mem_center_iff.1
      (gDeep_coker_central (Subgroup.subset_closure (Set.mem_insert _ _))) Cc
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hn
  · rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨1, 0, le_refl 1, by omega, by rw [pow_one, pow_zero, mul_one]⟩
    · exact ⟨0, 1, by omega, le_refl 1, by rw [pow_one, pow_zero, one_mul]⟩
  · exact ⟨0, 0, by omega, by omega, by rw [pow_zero, pow_zero, mul_one]⟩
  · rintro y z - - ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨f₁, f₂, hf₁, hf₂, rfl⟩
    obtain ⟨g₁, hg₁, hB⟩ := gAbs_pow_combine gDeep_B_img_sq e₁ f₁ he₁ hf₁
    obtain ⟨g₂, hg₂, hC⟩ := gAbs_pow_combine gDeep_C_img_sq e₂ f₂ he₂ hf₂
    refine ⟨g₁, g₂, hg₁, hg₂, ?_⟩
    have hmid : Cc ^ e₂ * Bc ^ f₁ = Bc ^ f₁ * Cc ^ e₂ := (hcommute.pow_pow e₂ f₁).eq
    calc Bc ^ e₁ * Cc ^ e₂ * (Bc ^ f₁ * Cc ^ f₂)
        = Bc ^ e₁ * (Cc ^ e₂ * Bc ^ f₁) * Cc ^ f₂ := by simp only [mul_assoc]
      _ = Bc ^ e₁ * (Bc ^ f₁ * Cc ^ e₂) * Cc ^ f₂ := by rw [hmid]
      _ = (Bc ^ e₁ * Bc ^ f₁) * (Cc ^ e₂ * Cc ^ f₂) := by simp only [mul_assoc]
      _ = Bc ^ g₁ * Cc ^ g₂ := by rw [hB, hC]
  · rintro z - ⟨e₁, e₂, he₁, he₂, rfl⟩
    refine ⟨e₁, e₂, he₁, he₂, ?_⟩
    refine inv_eq_of_mul_eq_one_left ?_
    have hmid : Cc ^ e₂ * Bc ^ e₁ = Bc ^ e₁ * Cc ^ e₂ := (hcommute.pow_pow e₂ e₁).eq
    have hBsq : Bc ^ e₁ * Bc ^ e₁ = 1 := by
      match e₁, he₁ with
      | 0, _ => rw [pow_zero, mul_one]
      | 1, _ => rw [pow_one, ← pow_two]; exact gDeep_B_img_sq
    have hCsq : Cc ^ e₂ * Cc ^ e₂ = 1 := by
      match e₂, he₂ with
      | 0, _ => rw [pow_zero, mul_one]
      | 1, _ => rw [pow_one, ← pow_two]; exact gDeep_C_img_sq
    calc Bc ^ e₁ * Cc ^ e₂ * (Bc ^ e₁ * Cc ^ e₂)
        = Bc ^ e₁ * (Cc ^ e₂ * Bc ^ e₁) * Cc ^ e₂ := by simp only [mul_assoc]
      _ = Bc ^ e₁ * (Bc ^ e₁ * Cc ^ e₂) * Cc ^ e₂ := by rw [hmid]
      _ = (Bc ^ e₁ * Bc ^ e₁) * (Cc ^ e₂ * Cc ^ e₂) := by simp only [mul_assoc]
      _ = 1 := by rw [hBsq, hCsq, one_mul]

/-- ⭐⭐ **The square supply**: the square of an exactly row-trivial `γ₃`-element lands in the
widened depth-3 reach.  Wave 78's T1 normal form squared: the reach part rides the engine
step, the coker part is the two squared classes, and the cross-terms die in `γ₆`. -/
theorem gDeep_sq_rowTrivial (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {c : (DSq h : Type)}
    (hc : c ∈ twoCentralSeries (DSq h : Type) 3) (hcl : nuLam h c = 1) (hcn : nu' c = 1) :
    levelMk (DSq h : Type) 5 (c ^ 2) ∈ gDeepWide h nu' := by
  obtain ⟨p, e₁, e₂, hpm, hpR, he₁, he₂, hceq⟩ := gAbs_leftover_decomp hsigma hx0 hc hcl hcn
  have hBe : gAbsB h ^ e₁ ∈ twoCentralSeries (DSq h : Type) 3 :=
    Subgroup.pow_mem _ gAbs_B_mem_three e₁
  have hCe : gAbsC h ^ e₂ ∈ twoCentralSeries (DSq h : Type) 3 :=
    Subgroup.pow_mem _ gAbs_C_mem_three e₂
  have hpBe : p * gAbsB h ^ e₁ ∈ twoCentralSeries (DSq h : Type) 3 :=
    Subgroup.mul_mem _ hpm hBe
  have h1 : levelMk (DSq h : Type) 5 (c ^ 2)
      = levelMk (DSq h : Type) 5 ((p * gAbsB h ^ e₁) ^ 2) *
        levelMk (DSq h : Type) 5 ((gAbsC h ^ e₂) ^ 2) := by
    rw [hceq]
    exact gTower_sq_congr (by norm_num) hpBe hCe
  have h2 : levelMk (DSq h : Type) 5 ((p * gAbsB h ^ e₁) ^ 2)
      = levelMk (DSq h : Type) 5 (p ^ 2) * levelMk (DSq h : Type) 5 ((gAbsB h ^ e₁) ^ 2) :=
    gTower_sq_congr (by norm_num) hpm hBe
  have hp2 : levelMk (DSq h : Type) 5 (p ^ 2) ∈ gTowerReach h nu' 3 :=
    gTower_reach_step (le_refl 2) hpm hpR
  rw [h1, h2, pow_right_comm (gAbsB h), pow_right_comm (gAbsC h)]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (gDeep_reach_le_wide hp2) ?_) ?_
  · exact Subgroup.mem_sup_right
      ((gDeepCoker h).pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) e₁)
  · exact Subgroup.mem_sup_right
      ((gDeepCoker h).pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) e₂)

/-- ⭐⭐ **The `x₁`-defect supply**: the `x₁`-bracket of an exactly row-trivial `γ₃`-element
lands in the widened depth-3 reach, by the bundle split against the square supply. -/
theorem gDeep_defect_rowTrivial (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {c : (DSq h : Type)}
    (hc : c ∈ twoCentralSeries (DSq h : Type) 3) (hcl : nuLam h c = 1) (hcn : nu' c = 1) :
    levelMk (DSq h : Type) 5 (commP c (dsqX1 h)) ∈ gDeepWide h nu' := by
  have hbundle : levelMk (DSq h : Type) 5 (c ^ 2 * commP c (dsqX1 h))
      ∈ gTowerReach h nu' 3 :=
    Subgroup.subset_closure (Or.inl (Or.inr ⟨c, ⟨hc, hcl, hcn⟩, rfl⟩))
  have hsplit : levelMk (DSq h : Type) 5 (commP c (dsqX1 h))
      = (levelMk (DSq h : Type) 5 (c ^ 2))⁻¹ *
        levelMk (DSq h : Type) 5 (c ^ 2 * commP c (dsqX1 h)) := by
    rw [map_mul, inv_mul_cancel_left]
  rw [hsplit]
  exact Subgroup.mul_mem _
    (Subgroup.inv_mem _ (gDeep_sq_rowTrivial hsigma hx0 hc hcl hcn))
    (gDeep_reach_le_wide hbundle)

end Wide

/-! ## §5 The wide chain: the depth-3 layer lands in the widened full reach

Wave 72's six-family generation record for `γ₄/γ₅` (`cfiveSpan_zLayer_le_gens_dsq`), joined to
the widened reach.  The four square families are instances of the square supply; the two
bracket families reduce over the letters, far slots to depth-3 knobs and the `x₁`-slot to the
defect supply; the eighth powers and bracket fourth powers ride the two-tower decomposition of
`γ₂`-squares, exactly as at depth 2. -/

section WideChain

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- The fourth power of any `γ₂`-element lands in the widened full reach. -/
theorem gDeep_pow_four_gammaTwo (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {v : (DSq h : Type)}
    (hv : v ∈ twoCentralSeries (DSq h : Type) 2) :
    levelMk (DSq h : Type) 5 (v ^ 4) ∈ gDeepWideFull h nu' := by
  have hw : v ^ 2 ∈ twoCentralSeries (DSq h : Type) 3 :=
    sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) hv
  obtain ⟨d, hdmem, hdl, hdn, hdec⟩ := gTower_decomp nu' hsigma hx0 (by omega) hw
  set a := toAdd (nuLam h (v ^ 2)) with ha
  set b := toAdd (nu' (v ^ 2)) with hb
  have hda : (2 ^ 2 : ℤ_[2]) ∣ a := by
    have hd := gTower_row_dvd (nuLam h) hw
    rwa [show (3 : ℕ) - 1 = 2 from rfl] at hd
  have hdb : (2 ^ 2 : ℤ_[2]) ∣ b := by
    have hd := gTower_row_dvd nu' hw
    rwa [show (3 : ℕ) - 1 = 2 from rfl] at hd
  have hxa : zpowZtwo (isProP_DSq h) (dsqX0 h) a ∈ twoCentralSeries (DSq h : Type) 3 :=
    gTower_zpow_dvd_mem (by omega) (by rw [show (3 : ℕ) - 1 = 2 from rfl]; exact hda) _
  have hwb : zpowZtwo (isProP_DSq h) (sqPivot h) b ∈ twoCentralSeries (DSq h : Type) 3 :=
    gTower_zpow_dvd_mem (by omega) (by rw [show (3 : ℕ) - 1 = 2 from rfl]; exact hdb) _
  have htow : gTowerTower h a b ∈ twoCentralSeries (DSq h : Type) 3 :=
    Subgroup.mul_mem _ hxa hwb
  have hfour : v ^ 4 = (v ^ 2) ^ 2 := by rw [← pow_mul]
  rw [hfour, hdec, gTower_sq_congr (by norm_num) hdmem htow]
  refine Subgroup.mul_mem _ ?_ ?_
  · exact gDeep_wide_le_wideFull (gDeep_sq_rowTrivial hsigma hx0 hdmem hdl hdn)
  · rw [gTowerTower, gTower_sq_congr (by norm_num) hxa hwb, gTower_zpow_sq, gTower_zpow_sq,
      ← map_mul]
    refine le_sup_right (α := Subgroup _) ?_
    refine Subgroup.subset_closure ⟨2 * a, 2 * b, ?_, ?_, ?_⟩
    · obtain ⟨t, htx⟩ := hda
      exact ⟨t, by rw [htx]; ring⟩
    · obtain ⟨t, htx⟩ := hdb
      exact ⟨t, by rw [htx]; ring⟩
    · rw [gTowerTower]

/-- Family one: eighth powers. -/
theorem gDeep_family_pow (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (g : levelQuot (DSq h : Type) 5) :
    ((g ^ 2) ^ 2) ^ 2 ∈ gDeepWideFull h nu' := by
  obtain ⟨v, hv, hveq⟩ := cfiveSpan_sq_mem_lambdaTwo g
  have heq : ((g ^ 2) ^ 2) ^ 2 = levelMk (DSq h : Type) 5 (v ^ 4) := by
    rw [← hveq, ← map_pow, ← map_pow, ← pow_mul]
  rw [heq]
  exact gDeep_pow_four_gammaTwo hsigma hx0 hv

/-- Family two: bracket fourth powers. -/
theorem gDeep_family_brPow (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (p q : levelQuot (DSq h : Type) 5) :
    ((commP p q) ^ 2) ^ 2 ∈ gDeepWideFull h nu' := by
  obtain ⟨v, hv, hveq⟩ := gFourFive_commP_mem_lambdaTwo p q
  have heq : ((commP p q) ^ 2) ^ 2 = levelMk (DSq h : Type) 5 (v ^ 4) := by
    rw [← hveq, ← map_pow, ← map_pow, ← pow_mul]
  rw [heq]
  exact gDeep_pow_four_gammaTwo hsigma hx0 hv

/-- The two `γ₃`-membership certificates the bracket families need. -/
theorem gDeep_sqBr_mem_three (g r : (DSq h : Type)) :
    commP (g ^ 2) r ∈ twoCentralSeries (DSq h : Type) 3 :=
  cfive_commP_mem_succ (sq_mem_twoCentralSeries_succ (G := (DSq h : Type))
    (gAbs_mem_one g)) r

theorem gDeep_trBr_mem_three (a b r : (DSq h : Type)) :
    commP (commP a b) r ∈ twoCentralSeries (DSq h : Type) 3 :=
  cfive_commP_mem_succ (cfour_commP_mem_two a b) r

/-- The slot reduction: the bracket of a row-trivial `γ₃`-element against ANY class lands in
the widened full reach, far slots through the depth-3 knobs and the `x₁`-slot through the
defect supply. -/
theorem gDeep_bracket_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {c : (DSq h : Type)}
    (hc : c ∈ twoCentralSeries (DSq h : Type) 3) (hcl : nuLam h c = 1) (hcn : nu' c = 1)
    (q : (DSq h : Type)) :
    levelMk (DSq h : Type) 5 (commP c q) ∈ gDeepWideFull h nu' := by
  have hspan := gTower_commHom_span (h := h) (k := 3) hc q
  refine Subgroup.closure_le (K := gDeepWideFull h nu') |>.2 ?_ hspan
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = 2
  · subst hi
    exact gDeep_wide_le_wideFull (gDeep_defect_rowTrivial hsigma hx0 hc hcl hcn)
  · refine gDeep_wide_le_wideFull (gDeep_reach_le_wide (Subgroup.subset_closure
      (Or.inl (Or.inl ⟨c, sqGen h i, ⟨hc, hcl, hcn⟩, gTower_letters_mem_far i hi, rfl⟩))))

/-- ⭐⭐⭐ **The depth-3 layer lands in the widened full reach**, unconditionally: the six
families of the `γ₄/γ₅` generation record, absorbed. -/
theorem gDeep_zLayer_le_wideFull (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    zLayer (DSq h : Type) 4 ≤ gDeepWideFull h nu' := by
  refine cfiveSpan_zLayer_le_gens_dsq (gDeep_family_pow hsigma hx0)
    (gDeep_family_brPow hsigma hx0) ?_ ?_ ?_ ?_
  · intro g r
    obtain ⟨g', rfl⟩ := levelMk_surjective (DSq h : Type) 5 g
    obtain ⟨r', rfl⟩ := levelMk_surjective (DSq h : Type) 5 r
    have heq : (commP (levelMk (DSq h : Type) 5 g' ^ 2) (levelMk (DSq h : Type) 5 r')) ^ 2
        = levelMk (DSq h : Type) 5 ((commP (g' ^ 2) r') ^ 2) := by
      simp only [commP, map_mul, map_inv, map_pow]
    rw [heq]
    exact gDeep_wide_le_wideFull (gDeep_sq_rowTrivial hsigma hx0 (gDeep_sqBr_mem_three g' r')
      (gTower_row_commP _ _ _) (gTower_row_commP nu' _ _))
  · intro a b r
    obtain ⟨a', rfl⟩ := levelMk_surjective (DSq h : Type) 5 a
    obtain ⟨b', rfl⟩ := levelMk_surjective (DSq h : Type) 5 b
    obtain ⟨r', rfl⟩ := levelMk_surjective (DSq h : Type) 5 r
    have heq : (commP (commP (levelMk (DSq h : Type) 5 a') (levelMk (DSq h : Type) 5 b'))
        (levelMk (DSq h : Type) 5 r')) ^ 2
        = levelMk (DSq h : Type) 5 ((commP (commP a' b') r') ^ 2) := by
      simp only [commP, map_mul, map_inv, map_pow]
    rw [heq]
    exact gDeep_wide_le_wideFull (gDeep_sq_rowTrivial hsigma hx0
      (gDeep_trBr_mem_three a' b' r') (gTower_row_commP _ _ _) (gTower_row_commP nu' _ _))
  · intro g r q
    obtain ⟨g', rfl⟩ := levelMk_surjective (DSq h : Type) 5 g
    obtain ⟨r', rfl⟩ := levelMk_surjective (DSq h : Type) 5 r
    obtain ⟨q', rfl⟩ := levelMk_surjective (DSq h : Type) 5 q
    have heq : commP (commP (levelMk (DSq h : Type) 5 g' ^ 2) (levelMk (DSq h : Type) 5 r'))
        (levelMk (DSq h : Type) 5 q')
        = levelMk (DSq h : Type) 5 (commP (commP (g' ^ 2) r') q') := by
      simp only [commP, map_mul, map_inv, map_pow]
    rw [heq]
    exact gDeep_bracket_wide hsigma hx0 (gDeep_sqBr_mem_three g' r')
      (gTower_row_commP _ _ _) (gTower_row_commP nu' _ _) q'
  · intro a b r q
    obtain ⟨a', rfl⟩ := levelMk_surjective (DSq h : Type) 5 a
    obtain ⟨b', rfl⟩ := levelMk_surjective (DSq h : Type) 5 b
    obtain ⟨r', rfl⟩ := levelMk_surjective (DSq h : Type) 5 r
    obtain ⟨q', rfl⟩ := levelMk_surjective (DSq h : Type) 5 q
    have heq : commP (commP (commP (levelMk (DSq h : Type) 5 a') (levelMk (DSq h : Type) 5 b'))
        (levelMk (DSq h : Type) 5 r')) (levelMk (DSq h : Type) 5 q')
        = levelMk (DSq h : Type) 5 (commP (commP (commP a' b') r') q') := by
      simp only [commP, map_mul, map_inv]
    rw [heq]
    exact gDeep_bracket_wide hsigma hx0 (gDeep_trBr_mem_three a' b' r')
      (gTower_row_commP _ _ _) (gTower_row_commP nu' _ _) q'

end WideChain

/-! ## Axiom pins -/

section AxiomPins

#print axioms gDeep_baseThree_iff
#print axioms gDeep_xOne_pow_dvd
#print axioms gDeep_xOne_tower_dvd
#print axioms gDeep_reach_le_layerDvd
#print axioms gDeep_reach_le_layerDvd_rowS
#print axioms gDeep_reach_le_layerDvd_rowX
#print axioms gDeep_pow_two_pow_mem
#print axioms gDeep_delta_pow_two_pow
#print axioms gDeep_pow_unit_not_dvd
#print axioms gDeep_delta_B_pow_rowS
#print axioms gDeep_not_layerReach
#print axioms gDeep_not_layerReach_three
#print axioms gDeep_not_baseThree

end AxiomPins

end SqCore

end Dyadic

end GQ2
