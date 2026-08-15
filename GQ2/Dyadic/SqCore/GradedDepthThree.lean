/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedAbsorption

/-!
# W79-DEPTH3: the depth-3 base refuted; the absorption transported; the ladder re-cut

Wave 78 re-seeded the odd-route reduction so that its sole remaining layer-side input was
the depth-3 base `GDecideBaseThree h`: at every selected marking, every exactly row-trivial
`γ₄`-element reaches at depth 3.  This file settles that input and repairs the route:

* **The refutation (§3)**: `GDecideBaseThree h` is FALSE at every `h`, and so is
  `GTowerLayerReach h ν' k` at EVERY depth `k ≥ 2` and every marking: the `2^{k-2}`-th power
  of wave 78's coker class `B = ⁅⁅x₁,σ⁆,x₁⁆` is row-trivial in `γ_{k+1}` and reads
  `2^k·unit` at the corrected `σ`-row, while the depth-`k` reach reads `2^{k+1}`-divisibly
  (§2).  No deeper re-seed of the same shape can ever work.
* **T1 at depth 3 (§4-§6)**: the absorption transports.  The depth-3 coker is the SQUARES
  `B², C²` (Labute's `π^{j-1}ξ`-towers of the two excluded classes), and every exactly
  row-trivial `γ₄`-element is a depth-3 reach element times `(B²)^{e₁}(C²)^{e₂}` with
  `𝔽₂`-exponents (`gDeep_leftover_decomp`).
* **T2 at depth 3 (§7)**: the corrected rows read `B², C²` as `2³·unit` at their own slots,
  zero at the other's, so all-rows-zero elements have both exponents killed and reach
  (`gDeep_zero_reader_reach`).
* **The re-cut (§8)**: the route's proofs only ever applied the layer statement to the
  relator word, which reads zero everywhere; the honest layer-side input is therefore the
  defect-restricted KILL LADDER `GDeepKillAt h k`, whose rungs `k = 2, 3` are now theorems.
  The vanishing interface and `SqLamMarkTransitivity h` follow from the ladder plus the two
  wave-75 interfaces, and the recursion seeded through the proved rungs yields the class-5
  supply from separation and extraction alone (`gDeep_supply_five`).
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
`2^{k+4}`-divisibly): the `ℤ₂`-exponent statement, by density of `ℕ`.

⚠ **[W80-HOUSE, as of `4f30776b`: the parenthetical is about the PROOF, not the statement.**
The conclusion is `2^{k+3} ∣ …`; the `2^{k+4}` bound lives in the local `hall` and is weakened
by `pow_dvd_pow` on the last line.  A caller who cites this lemma for `2^{k+4}` will not get
it; the sharp form has to be re-extracted.]** -/
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

/-! ## §6 The cut and the depth-3 leftover normal form (T1)

Wave 78's §6 one level up: the realization of the widened full reach factors through wave
74's `gTower_fullReach_realize` at depth 3 because the coker is central; the cut is verbatim,
one index deeper; and the result is the depth-3 leftover normal form: every exactly
row-trivial `γ₄`-element is a depth-3 reach element times `(B²)^{e₁}(C²)^{e₂}` with
`𝔽₂`-exponents. -/

section Cut

open scoped Pointwise

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- The row-triviality of the squared coker classes. -/
theorem gDeep_B_sq_nuLam : nuLam h (gAbsB h ^ 2) = 1 := by
  rw [gAbsB, map_pow, gTower_row_commP, one_pow]

theorem gDeep_B_sq_nu : nu' (gAbsB h ^ 2) = 1 := by
  rw [gAbsB, map_pow, gTower_row_commP, one_pow]

theorem gDeep_C_sq_nuLam : nuLam h (gAbsC h ^ 2) = 1 := by
  rw [gAbsC, map_pow, gTower_row_commP, one_pow]

theorem gDeep_C_sq_nu : nu' (gAbsC h ^ 2) = 1 := by
  rw [gAbsC, map_pow, gTower_row_commP, one_pow]

/-- The realization of the widened full reach at depth 3: a row-trivial `γ₄`-element whose
class lies in the widened reach, times a two-tower image with `8`-divisible exponents. -/
theorem gDeep_wideFull_realize (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {z : levelQuot (DSq h : Type) 5}
    (hz : z ∈ gDeepWideFull h nu') :
    ∃ r A B, r ∈ twoCentralSeries (DSq h : Type) 4 ∧ nuLam h r = 1 ∧ nu' r = 1 ∧
      levelMk (DSq h : Type) 5 r ∈ gDeepWide h nu' ∧
        (2 ^ 3 : ℤ_[2]) ∣ A ∧ (2 ^ 3 : ℤ_[2]) ∣ B ∧
          z = levelMk (DSq h : Type) 5 r * levelMk (DSq h : Type) 5 (gTowerTower h A B) := by
  rw [gDeep_wideFull_eq] at hz
  haveI := gDeep_coker_normal (h := h)
  have hmem : z ∈ ((gTowerFullReach h nu' 3 : Subgroup (levelQuot (DSq h : Type) 5)) :
      Set (levelQuot (DSq h : Type) 5)) *
      ((gDeepCoker h : Subgroup (levelQuot (DSq h : Type) 5)) :
        Set (levelQuot (DSq h : Type) 5)) := by
    rw [← Subgroup.mul_normal]
    exact hz
  obtain ⟨f, hf, n, hn, heq⟩ := hmem
  obtain ⟨r, A, B, hrm, hrl, hrn, hrR, hA, hB, hfeq⟩ := gTower_fullReach_realize hsigma hx0 hf
  obtain ⟨e₁, e₂, he₁, he₂, hneq⟩ := gDeep_coker_form hn
  refine ⟨r * (gAbsB h ^ 2) ^ e₁ * (gAbsC h ^ 2) ^ e₂, A, B, ?_, ?_, ?_, ?_, hA, hB, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hrm
      (Subgroup.pow_mem _ gDeep_B_sq_mem_four e₁)) (Subgroup.pow_mem _ gDeep_C_sq_mem_four e₂)
  · have hB1 : nuLam h (gAbsB h) = 1 := by rw [gAbsB]; exact gTower_row_commP _ _ _
    have hC1 : nuLam h (gAbsC h) = 1 := by rw [gAbsC]; exact gTower_row_commP _ _ _
    simp only [map_mul, map_pow, hrl, hB1, hC1, one_pow, one_mul]
  · have hB1 : nu' (gAbsB h) = 1 := by rw [gAbsB]; exact gTower_row_commP _ _ _
    have hC1 : nu' (gAbsC h) = 1 := by rw [gAbsC]; exact gTower_row_commP _ _ _
    simp only [map_mul, map_pow, hrn, hB1, hC1, one_pow, one_mul]
  · have hBcMem : levelMk (DSq h : Type) 5 (gAbsB h ^ 2) ∈ gDeepCoker h :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hCcMem : levelMk (DSq h : Type) 5 (gAbsC h ^ 2) ∈ gDeepCoker h :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rw [map_mul, map_mul, map_pow, map_pow]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (gDeep_reach_le_wide hrR) ?_) ?_
    · exact Subgroup.mem_sup_right ((gDeepCoker h).pow_mem hBcMem e₁)
    · exact Subgroup.mem_sup_right ((gDeepCoker h).pow_mem hCcMem e₂)
  · have hcen : ∀ g : levelQuot (DSq h : Type) 5, g * n = n * g :=
      fun g => Subgroup.mem_center_iff.1 (gDeep_coker_central hn) g
    calc z = f * n := heq.symm
      _ = levelMk (DSq h : Type) 5 r * levelMk (DSq h : Type) 5 (gTowerTower h A B) * n := by
          rw [hfeq]
      _ = levelMk (DSq h : Type) 5 r *
          (levelMk (DSq h : Type) 5 (gTowerTower h A B) * n) := by rw [mul_assoc]
      _ = levelMk (DSq h : Type) 5 r *
          (n * levelMk (DSq h : Type) 5 (gTowerTower h A B)) := by rw [hcen]
      _ = levelMk (DSq h : Type) 5 r * n * levelMk (DSq h : Type) 5 (gTowerTower h A B) := by
          rw [mul_assoc]
      _ = levelMk (DSq h : Type) 5 (r * (gAbsB h ^ 2) ^ e₁ * (gAbsC h ^ 2) ^ e₂) *
          levelMk (DSq h : Type) 5 (gTowerTower h A B) := by
          rw [hneq]
          simp only [map_mul, map_pow, mul_assoc]

/-- ⭐⭐ **The cut for the widened depth-3 reach**: an exactly row-trivial element whose class
lies in the widened full reach already lies in the widened reach. -/
theorem gDeep_wide_cut (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)} (hgl : nuLam h g = 1)
    (hgn : nu' g = 1)
    (hfull : levelMk (DSq h : Type) 5 g ∈ gDeepWideFull h nu') :
    levelMk (DSq h : Type) 5 g ∈ gDeepWide h nu' := by
  obtain ⟨r, A, B, hrmem, hrl, hrn, hrW, hA, hB, heq⟩ :=
    gDeep_wideFull_realize hsigma hx0 hfull
  have hAmem : zpowZtwo (isProP_DSq h) (dsqX0 h) A ∈ twoCentralSeries (DSq h : Type) 4 :=
    gTower_zpow_dvd_mem (by omega) (by simpa using hA) _
  have hBmem : zpowZtwo (isProP_DSq h) (sqPivot h) B ∈ twoCentralSeries (DSq h : Type) 4 :=
    gTower_zpow_dvd_mem (by omega) (by simpa using hB) _
  have htmem : gTowerTower h A B ∈ twoCentralSeries (DSq h : Type) 4 :=
    Subgroup.mul_mem _ hAmem hBmem
  set u := (r * gTowerTower h A B)⁻¹ * g with hu
  have humem : u ∈ twoCentralSeries (DSq h : Type) 5 := by
    rw [lim_mem_twoCentralSeries_iff_levelMk]
    show levelMk (DSq h : Type) 5 ((r * gTowerTower h A B)⁻¹ * g) = 1
    rw [map_mul, map_inv, map_mul, heq]
    group
  have hgform : g = r * gTowerTower h A B * u := by
    rw [hu, mul_inv_cancel_left]
  have hrowA : toAdd (nuLam h g) = A + toAdd (nuLam h u) := by
    rw [hgform, map_mul, toAdd_mul, map_mul, toAdd_mul, hrl, toAdd_one, gTower_tower_nuLam,
      zero_add]
  have hrowB : toAdd (nu' g) = B + toAdd (nu' u) := by
    rw [hgform, map_mul, toAdd_mul, map_mul, toAdd_mul, hrn, toAdd_one,
      gTower_tower_nu nu' hsigma hx0, zero_add]
  have hAdeep : (2 ^ 4 : ℤ_[2]) ∣ A := by
    have hud := gTower_row_dvd (nuLam h) humem
    rw [show (5 : ℕ) - 1 = 4 from rfl] at hud
    have hAeq : A = -toAdd (nuLam h u) := by
      have h0 := hrowA
      rw [hgl, toAdd_one] at h0
      exact eq_neg_of_add_eq_zero_left h0.symm
    rw [hAeq]
    exact hud.neg_right
  have hBdeep : (2 ^ 4 : ℤ_[2]) ∣ B := by
    have hud := gTower_row_dvd nu' humem
    rw [show (5 : ℕ) - 1 = 4 from rfl] at hud
    have hBeq : B = -toAdd (nu' u) := by
      have h0 := hrowB
      rw [hgn, toAdd_one] at h0
      exact eq_neg_of_add_eq_zero_left h0.symm
    rw [hBeq]
    exact hud.neg_right
  have htdeep : gTowerTower h A B ∈ twoCentralSeries (DSq h : Type) 5 :=
    gTower_tower_mem (by omega)
      (by rw [show (5 : ℕ) - 1 = 4 from rfl]; exact hAdeep)
      (by rw [show (5 : ℕ) - 1 = 4 from rfl]; exact hBdeep)
  have htimg : levelMk (DSq h : Type) 5 (gTowerTower h A B) = 1 :=
    (lim_mem_twoCentralSeries_iff_levelMk 5 _).mp htdeep
  rw [heq, htimg, mul_one]
  exact hrW

/-- ⭐⭐⭐ **The wide layer statement at depth 3**: every exactly row-trivial `γ₄`-element
reaches the widened span, unconditionally.  This is the REFUTED `GTowerLayerReach h ν' 3`
with the squared two-class coker adjoined: the exact unconditional content of the depth-3
base.

⚠ **[W80-HOUSE, as of `4f30776b`: two scope corrections to the headline.**  (i) "Unconditionally"
means "with no layer-statement input"; the theorem does carry the marking selection `hsigma`,
`hx0`, whereas `GTowerLayerReach h ν' 3` (`GradedUniformTower.lean`) carries none.  So what is
widened here is the body of `GDecideBaseThree h` (the layer statement AT A SELECTED MARKING),
not `GTowerLayerReach` itself.  (ii) "The exact content" overstates a containment: what is
proved is a membership in the join `gDeepWide h nu'`, an upper bound on the defect.  The two
generators are each shown to be outside the reach (`gDeep_B_sq_notMem_reach`,
`gDeep_C_sq_notMem_reach`), which is minimality generator by generator, not of the span.]** -/
theorem gDeep_layer_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)}
    (hg : g ∈ twoCentralSeries (DSq h : Type) 4) (hgl : nuLam h g = 1) (hgn : nu' g = 1) :
    levelMk (DSq h : Type) 5 g ∈ gDeepWide h nu' := by
  refine gDeep_wide_cut hsigma hx0 hgl hgn ?_
  exact gDeep_zLayer_le_wideFull hsigma hx0 ⟨g, hg, rfl⟩

/-- ⭐⭐⭐ **T1 at depth 3: the leftover normal form.**  Every exactly row-trivial
`γ₄`-element is an element whose class lies in the admissible depth-3 reach, times the two
SQUARED coker classes with explicit `𝔽₂`-exponents: Labute's Theorem 5 leftover
decomposition at level 3, with the `π^{j-1}ξ`-towers appearing exactly as predicted. -/
theorem gDeep_leftover_decomp (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)}
    (hg : g ∈ twoCentralSeries (DSq h : Type) 4) (hgl : nuLam h g = 1) (hgn : nu' g = 1) :
    ∃ p e₁ e₂, p ∈ twoCentralSeries (DSq h : Type) 4 ∧
      levelMk (DSq h : Type) 5 p ∈ gTowerReach h nu' 3 ∧ e₁ ≤ 1 ∧ e₂ ≤ 1 ∧
        g = p * (gAbsB h ^ 2) ^ e₁ * (gAbsC h ^ 2) ^ e₂ := by
  have hw := gDeep_layer_wide hsigma hx0 hg hgl hgn
  haveI := gDeep_coker_normal (h := h)
  have hmem : levelMk (DSq h : Type) 5 g ∈
      ((gTowerReach h nu' 3 : Subgroup (levelQuot (DSq h : Type) 5)) :
        Set (levelQuot (DSq h : Type) 5)) *
      ((gDeepCoker h : Subgroup (levelQuot (DSq h : Type) 5)) :
        Set (levelQuot (DSq h : Type) 5)) := by
    rw [← Subgroup.mul_normal]
    exact hw
  obtain ⟨ρ, hρ, n, hn, heq⟩ := hmem
  obtain ⟨e₁, e₂, he₁, he₂, hneq⟩ := gDeep_coker_form hn
  refine ⟨g * ((gAbsB h ^ 2) ^ e₁ * (gAbsC h ^ 2) ^ e₂)⁻¹, e₁, e₂, ?_, ?_, he₁, he₂,
    by group⟩
  · exact Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ gDeep_B_sq_mem_four e₁)
      (Subgroup.pow_mem _ gDeep_C_sq_mem_four e₂)))
  · have hn' : n = (levelMk (DSq h : Type) 5 (gAbsB h) ^ 2) ^ e₁ *
        (levelMk (DSq h : Type) 5 (gAbsC h) ^ 2) ^ e₂ := by
      rw [hneq]
      simp only [map_pow]
    have hzeq : ρ * n = levelMk (DSq h : Type) 5 g := heq
    have himg : levelMk (DSq h : Type) 5
        (g * ((gAbsB h ^ 2) ^ e₁ * (gAbsC h ^ 2) ^ e₂)⁻¹) = ρ := by
      simp only [map_mul, map_inv, map_pow]
      rw [← hn', ← hzeq, mul_inv_cancel_right]
    rw [himg]
    exact hρ

end Cut

/-! ## §7 T2 at depth 3: the coefficient kill

The corrected rows read the squared coker classes one bit deeper but still at the depth-3
layer bit: `B²` reads `2·4·unit = 2³·unit` at the corrected `σ`-row and `0` at the `x₀`-row,
`C²` conversely, while the whole depth-3 reach reads `2⁴`-divisibly (§2).  A defect reads
zero at every row, so both `𝔽₂`-exponents die and the class lies in the admissible reach:
the refuted depth-3 layer statement is recovered exactly on the all-rows-zero elements,
which is all the tower recursion ever consumes. -/

section Kill

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- Units do not absorb powers of two, at any exponent. -/
theorem gDeep_unit_mul_dvd {m : ℕ} {w : ℤ_[2]ˣ} {t : ℤ_[2]}
    (hd : (2 : ℤ_[2]) ^ m ∣ (w : ℤ_[2]) * t) : (2 : ℤ_[2]) ^ m ∣ t := by
  obtain ⟨s, hs⟩ := hd
  have hcanc : ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (w : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * s, ?_⟩
  linear_combination ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hs - t * hcanc

/-- The reading of the square of a `χ`-trivial element doubles the reading. -/
theorem gDeep_delta_sq (c : Fin (sqRank h) → ℤ_[2]) {x : (DSq h : Type)}
    (hchi : chiSq h x = 1) : gDelta h c (x ^ 2) = 2 * gDelta h c x := by
  rw [gDelta_pow, hchi, Units.val_one, normSum_one_base]
  norm_num

theorem gDeep_chiSq_B_sq : chiSq h (gAbsB h ^ 2) = 1 := by
  rw [map_pow, gAbs_chiSq_B, one_pow]

theorem gDeep_chiSq_C_sq : chiSq h (gAbsC h ^ 2) = 1 := by
  rw [map_pow, gAbs_chiSq_C, one_pow]

/-- ⭐ **`B²` reads `2³·unit` at the corrected `σ`-row**: one bit deeper than `B`, still
visible at the depth-3 layer bit. -/
theorem gDeep_delta_B_sq_rowS :
    ∃ u : ℤ_[2]ˣ, gDelta h (gAbsRowS h nu') (gAbsB h ^ 2) = 2 ^ 3 * (u : ℤ_[2]) := by
  obtain ⟨u, hu⟩ := gAbs_delta_B_rowS (h := h) (nu' := nu')
  refine ⟨u, ?_⟩
  rw [gDeep_delta_sq _ gAbs_chiSq_B, hu]
  ring

theorem gDeep_delta_B_sq_rowX : gDelta h (gAbsRowX h nu') (gAbsB h ^ 2) = 0 := by
  rw [gDeep_delta_sq _ gAbs_chiSq_B, gAbs_delta_B_rowX, mul_zero]

/-- ⭐ **`C²` reads `2³·unit` at the corrected `x₀`-row.** -/
theorem gDeep_delta_C_sq_rowX :
    ∃ u : ℤ_[2]ˣ, gDelta h (gAbsRowX h nu') (gAbsC h ^ 2) = 2 ^ 3 * (u : ℤ_[2]) := by
  obtain ⟨u, hu⟩ := gAbs_delta_C_rowX (h := h) (nu' := nu')
  refine ⟨u, ?_⟩
  rw [gDeep_delta_sq _ gAbs_chiSq_C, hu]
  ring

theorem gDeep_delta_C_sq_rowS : gDelta h (gAbsRowS h nu') (gAbsC h ^ 2) = 0 := by
  rw [gDeep_delta_sq _ gAbs_chiSq_C, gAbs_delta_C_rowS, mul_zero]

/-- **The middle-exponent kill at depth 3**: head `2⁴`-divisible, middle base `2³·unit`, tail
base zero, product zero: the middle `𝔽₂`-exponent vanishes. -/
theorem gDeep_kill_mid {p x y : (DSq h : Type)} {c : Fin (sqRank h) → ℤ_[2]} {e f : ℕ}
    (he : e ≤ 1) (h16p : (2 : ℤ_[2]) ^ 4 ∣ gDelta h c p)
    (hx8 : ∃ u : ℤ_[2]ˣ, gDelta h c x = 2 ^ 3 * (u : ℤ_[2]))
    (hy0 : gDelta h c y = 0) (hchiX : chiSq h x = 1) (hchiY : chiSq h y = 1)
    (hzero : gDelta h c (p * x ^ e * y ^ f) = 0) : e = 0 := by
  rw [gDelta_mul, gDelta_mul, gDelta_pow, gDelta_pow, hchiX, hchiY, hy0, mul_zero, mul_zero,
    add_zero, Units.val_one, normSum_one_base] at hzero
  match e, he with
  | 0, _ => rfl
  | 1, _ =>
    exfalso
    have h16 : (2 : ℤ_[2]) ^ 4 ∣ ((chiSq h p : ℤ_[2]ˣ) : ℤ_[2]) * gDelta h c x := by
      have hneg : ((chiSq h p : ℤ_[2]ˣ) : ℤ_[2]) * gDelta h c x = -gDelta h c p := by
        push_cast at hzero
        linear_combination hzero
      rw [hneg]
      exact h16p.neg_right
    obtain ⟨u, hu⟩ := hx8
    exact gDeep_pow_unit_not_dvd hu (gDeep_unit_mul_dvd h16)

/-- **The tail-exponent kill at depth 3.** -/
theorem gDeep_kill_last {p x y : (DSq h : Type)} {c : Fin (sqRank h) → ℤ_[2]} {e f : ℕ}
    (hf : f ≤ 1) (h16p : (2 : ℤ_[2]) ^ 4 ∣ gDelta h c p)
    (hx0 : gDelta h c x = 0)
    (hy8 : ∃ u : ℤ_[2]ˣ, gDelta h c y = 2 ^ 3 * (u : ℤ_[2]))
    (hchiX : chiSq h x = 1) (hchiY : chiSq h y = 1)
    (hzero : gDelta h c (p * x ^ e * y ^ f) = 0) : f = 0 := by
  rw [gDelta_mul, gDelta_mul, gDelta_pow, gDelta_pow, hchiX, hchiY, hx0, mul_zero, mul_zero,
    add_zero, Units.val_one, normSum_one_base, map_mul, map_pow, hchiX, one_pow, mul_one]
    at hzero
  match f, hf with
  | 0, _ => rfl
  | 1, _ =>
    exfalso
    have h16 : (2 : ℤ_[2]) ^ 4 ∣ ((chiSq h p : ℤ_[2]ˣ) : ℤ_[2]) * gDelta h c y := by
      have hneg : ((chiSq h p : ℤ_[2]ˣ) : ℤ_[2]) * gDelta h c y = -gDelta h c p := by
        push_cast at hzero
        linear_combination hzero
      rw [hneg]
      exact h16p.neg_right
    obtain ⟨u, hu⟩ := hy8
    exact gDeep_pow_unit_not_dvd hu (gDeep_unit_mul_dvd h16)

/-- ⭐⭐⭐ **T2 at depth 3: the coefficient kill.**  An exactly row-trivial `γ₄`-element all
of whose functional readings vanish has zero coker coefficients: its class lies in the
admissible depth-3 reach.  The REFUTED depth-3 base is recovered exactly on the
all-rows-zero elements, which is all the recursion ever needed of it. -/
theorem gDeep_zero_reader_reach (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)}
    (hg : g ∈ twoCentralSeries (DSq h : Type) 4) (hgl : nuLam h g = 1) (hgn : nu' g = 1)
    (hzero : ∀ c : Fin (sqRank h) → ℤ_[2], gDelta h c g = 0) :
    levelMk (DSq h : Type) 5 g ∈ gTowerReach h nu' 3 := by
  obtain ⟨p, e₁, e₂, hpm, hpR, he₁, he₂, hgeq⟩ := gDeep_leftover_decomp hsigma hx0 hg hgl hgn
  have h16pS : (2 : ℤ_[2]) ^ 4 ∣ gDelta h (gAbsRowS h nu') p :=
    (gJoin_mem_layerDvd (c := gAbsRowS h nu') (k := 3) (x := p)).1
      (gDeep_reach_le_layerDvd_rowS hpR)
  have h16pX : (2 : ℤ_[2]) ^ 4 ∣ gDelta h (gAbsRowX h nu') p :=
    (gJoin_mem_layerDvd (c := gAbsRowX h nu') (k := 3) (x := p)).1
      (gDeep_reach_le_layerDvd_rowX hpR)
  have h0S := hzero (gAbsRowS h nu')
  rw [hgeq] at h0S
  have h0X := hzero (gAbsRowX h nu')
  rw [hgeq] at h0X
  have hBkill : e₁ = 0 :=
    gDeep_kill_mid he₁ h16pS gDeep_delta_B_sq_rowS gDeep_delta_C_sq_rowS gDeep_chiSq_B_sq
      gDeep_chiSq_C_sq h0S
  have hCkill : e₂ = 0 :=
    gDeep_kill_last he₂ h16pX gDeep_delta_B_sq_rowX gDeep_delta_C_sq_rowX gDeep_chiSq_B_sq
      gDeep_chiSq_C_sq h0X
  rw [hgeq, hBkill, hCkill, pow_zero, pow_zero, mul_one, mul_one]
  exact hpR

/-- The squared `σ`-coker class is outside the depth-3 reach at every marking: the refutation
core, stated as wave 78 stated its depth-2 twin. -/
theorem gDeep_B_sq_notMem_reach :
    levelMk (DSq h : Type) 5 (gAbsB h ^ 2) ∉ gTowerReach h nu' 3 := by
  intro hmem
  obtain ⟨u, hu⟩ := gDeep_delta_B_sq_rowS (h := h) (nu' := nu')
  exact gDeep_pow_unit_not_dvd hu
    ((gJoin_mem_layerDvd (c := gAbsRowS h nu') (k := 3) (x := gAbsB h ^ 2)).1
      (gDeep_reach_le_layerDvd_rowS hmem))

theorem gDeep_C_sq_notMem_reach :
    levelMk (DSq h : Type) 5 (gAbsC h ^ 2) ∉ gTowerReach h nu' 3 := by
  intro hmem
  obtain ⟨u, hu⟩ := gDeep_delta_C_sq_rowX (h := h) (nu' := nu')
  exact gDeep_pow_unit_not_dvd hu
    ((gJoin_mem_layerDvd (c := gAbsRowX h nu') (k := 3) (x := gAbsC h ^ 2)).1
      (gDeep_reach_le_layerDvd_rowX hmem))

end Kill

/-! ## §8 The re-cut: the kill ladder replaces the refuted base

`gAbs_markTransitivity_of_baseThree` is vacuous: its named input is false (§3).  But its
proof only ever applied the layer statement to the RELATOR WORD, which reads zero at every
functional.  So the honest layer-side input of the repaired route is the defect-restricted
ladder `GDeepKillAt h k`: all-rows-zero row-trivial `γ_{k+1}`-elements reach.  Its `k = 2`
instance is wave 78's T2, its `k = 3` instance is §7, and the whole odd-route residual
re-cuts onto the ladder at `k ≥ 4` plus the two wave-75 interfaces.  The recursion seeded
through `k = 2, 3` already yields the class-5 supply outright. -/

section Reseed

variable {h : ℕ}

variable (h) in
/-- ⭐⭐⭐ **The kill ladder at depth `k`**: the defect-restricted layer statement.  All the
recursion ever consumes; TRUE at `k = 2, 3`, open at `k ≥ 4`, while the unrestricted
statement is FALSE at every `k ≥ 2` (§3). -/
def GDeepKillAt (k : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
    ∀ g ∈ twoCentralSeries (DSq h : Type) (k + 1), nuLam h g = 1 → nu' g = 1 →
      (∀ c : Fin (sqRank h) → ℤ_[2], gDelta h c g = 0) →
      levelMk (DSq h : Type) (k + 2) g ∈ gTowerReach h nu' k

/-- The depth-2 rung: wave 78's T2. -/
theorem gDeep_killAt_two : GDeepKillAt h 2 :=
  fun _ hsigma hx0 _ hg hgl hgn hzero => gAbs_zero_reader_reach hsigma hx0 hg hgl hgn hzero

/-- ⭐⭐⭐ The depth-3 rung: this file's T2. -/
theorem gDeep_killAt_three : GDeepKillAt h 3 :=
  fun _ hsigma hx0 _ hg hgl hgn hzero => gDeep_zero_reader_reach hsigma hx0 hg hgl hgn hzero

/-- ⭐⭐⭐ **The vanishing interface from the kill ladder plus separation**: the honest
re-cut of `gAbs_defectVanishing_of_baseThree`, with the FALSE base replaced by the
defect-restricted ladder its proof actually consumed. -/
theorem gDeep_defectVanishing_of_kills (HK : ∀ k, 2 ≤ k → GDeepKillAt h k)
    (hsep : GJoinSeparationAll h) : GJoinDefectVanishing h := by
  intro nu' j hsigma hx0 k hk a hal han hac _ hrel
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  have hzero : ∀ c, gDelta h c (sqRelWord (sqArbFrame h nu' j a)) = 0 :=
    fun c => gJoin_reading_zero c nu' j ⟨hal, han, hac⟩
  have hreach : levelMk (DSq h : Type) (k' + 2 + 2) (sqRelWord (sqArbFrame h nu' j a))
      ∈ gTowerReach h nu' (k' + 2) :=
    HK (k' + 2) (by omega) nu' hsigma hx0 _ hrel (gTower_frame_row_nuLam j hal)
      (gTower_frame_row_nu j hx0 han) hzero
  refine gJoin_reach_sep hx0 (hsep nu' (k' + 2) (by omega)) hreach
    (fun jj => ?_) (fun jj => ?_)
  · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)
  · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)

/-- The supply at every class, from the ladder plus the two wave-75 interfaces. -/
theorem gDeep_supply_of_kills (HK : ∀ k, 2 ≤ k → GDeepKillAt h k)
    (hsep : GJoinSeparationAll h) (HR : GTowerKnobRealizable h) :
    ∀ k, SqClassClearingSupply h k :=
  gJoin_supply_of_vanishing (gDeep_defectVanishing_of_kills HK hsep) HR

/-- ⭐⭐⭐ **The `h ≥ 1` residual, re-cut**: the kill ladder (rungs `2` and `3` proved, `k ≥ 4`
open), the separation bookkeeping, and the extraction interface. -/
theorem gDeep_markTransitivity_of_kills (HK : ∀ k, 2 ≤ k → GDeepKillAt h k)
    (hsep : GJoinSeparationAll h) (HR : GTowerKnobRealizable h) : SqLamMarkTransitivity h :=
  gJoin_markTransitivity_of_vanishing (gDeep_defectVanishing_of_kills HK hsep) HR

variable (h) in
/-- **The depth-3 vanishing**: the `k = 3` instance of `GJoinDefectVanishing`, the knob-form
consumed by the recursion's second step. -/
def GDeepVanishingThree : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
    ∀ a : Fin (sqRank h) → (DSq h : Type),
      (∀ i, nuLam h (a i) = 1) → (∀ i, nu' (a i) = 1) → (∀ i, chiSq h (a i) = 1) →
      SqModTwoIndep (sqArbFrame h nu' j a) →
      sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) 4 →
      levelMk (DSq h : Type) 5 (sqRelWord (sqArbFrame h nu' j a))
        ∈ Subgroup.closure (gTowerKnobSet h nu' 3)

/-- ⭐⭐ **The depth-3 vanishing holds, from depth-3 separation alone**: T1 plus T2 replace
the REFUTED `GTowerLayerReach h ν' 3` outright, exactly as wave 78 did at depth 2. -/
theorem gDeep_vanishingThree_of_sep
    (hsep : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      GJoinTowerSeparation h nu' 3) : GDeepVanishingThree h := by
  intro nu' j hsigma hx0 a hal han hac _ hrel
  have hzero : ∀ c, gDelta h c (sqRelWord (sqArbFrame h nu' j a)) = 0 :=
    fun c => gJoin_reading_zero c nu' j ⟨hal, han, hac⟩
  have hreach := gDeep_zero_reader_reach hsigma hx0 hrel (gTower_frame_row_nuLam j hal)
    (gTower_frame_row_nu j hx0 han) hzero
  refine gJoin_reach_sep (k := 1) hx0 (hsep nu') hreach (fun jj => ?_) (fun jj => ?_)
  · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)
  · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)

/-- **The class-4-to-5 clearing step**: wave 75's step at `k = 3`, with the depth-3 vanishing
in place of the refuted full-generation statement. -/
theorem gDeep_clear_step_three (HV : GDeepVanishingThree h) (HR : GTowerKnobRealizable h)
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    {a : Fin (sqRank h) → (DSq h : Type)} (hal : ∀ i, nuLam h (a i) = 1)
    (han : ∀ i, nu' (a i) = 1) (hac : ∀ i, chiSq h (a i) = 1)
    (hai : SqModTwoIndep (sqArbFrame h nu' j a))
    (hrel : sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) 4) :
    ∃ a' : Fin (sqRank h) → (DSq h : Type),
      (∀ i, nuLam h (a' i) = 1) ∧ (∀ i, nu' (a' i) = 1) ∧ (∀ i, chiSq h (a' i) = 1) ∧
        SqModTwoIndep (sqArbFrame h nu' j a') ∧
          sqRelWord (sqArbFrame h nu' j a') ∈ twoCentralSeries (DSq h : Type) 5 := by
  have hknob := HV nu' j hsigma hx0 a hal han hac hai hrel
  obtain ⟨d, hd, hdl, hdn, hrel'⟩ := HR nu' j hsigma hx0 3 (by omega) a hal han hai hrel hknob
  refine ⟨fun i => a i * d i, ?_, ?_, ?_, ?_, hrel'⟩
  · intro i
    rw [map_mul, hal i, hdl i, one_mul]
  · intro i
    rw [map_mul, han i, hdn i, one_mul]
  · intro i
    exact gJoin_chiSq_mul_correction (hac i) (by omega : 2 ≤ 3) (hd i) (hdl i)
  · rw [gTower_frame_mul]
    exact cfourId_modTwoIndep_mul hai
      (fun i => twoCentralSeries_antitone (G := (DSq h : Type)) (by omega : 2 ≤ 3) (hd i))

/-- ⭐⭐⭐ **The class-5 `χ`-supply from separation and extraction alone**: the committed
class-3 witness driven through the depth-2 and depth-3 absorptions.  No layer statement and
no per-class witness is consumed: both graded rungs are theorems. -/
theorem gDeep_chiSupply_five (hsep : GJoinSeparationAll h) (HR : GTowerKnobRealizable h) :
    GJoinChiSupply h 5 := by
  intro nu' j hsigma hx0
  obtain ⟨a, hal, han, hac, hai, hrel⟩ := gJoin_chiSupply_three (h := h) nu' j hsigma hx0
  obtain ⟨a', h1, h2, h3, h4, h5⟩ := gAbs_clear_step_two
    (gAbs_vanishingTwo_of_sep fun nu'' => hsep nu'' 2 (le_refl 2)) HR hsigma hx0 hal han hac
    hai hrel
  obtain ⟨a'', g1, g2, g3, g4, g5⟩ := gDeep_clear_step_three
    (gDeep_vanishingThree_of_sep fun nu'' => hsep nu'' 3 (by omega)) HR hsigma hx0 h1 h2 h3
    h4 h5
  exact ⟨a'', g1, g2, g3, g4, g5⟩

/-- ⭐⭐⭐ **The class-5 supply**: `SqClassClearingSupply h 5` from separation plus
extraction.  With wave 78's class 4, the per-class residual now starts at CLASS 6. -/
theorem gDeep_supply_five (hsep : GJoinSeparationAll h) (HR : GTowerKnobRealizable h) :
    SqClassClearingSupply h 5 :=
  gJoin_supply_of_chiSupply (gDeep_chiSupply_five hsep HR)

/-- The handle-free case carries no separation obligation at all. -/
theorem gDeep_separationAll_handleFree : GJoinSeparationAll 0 :=
  fun nu' k _ => gJoin_towerSeparation_handleFree nu' k

theorem gDeep_supply_five_handleFree (HR : GTowerKnobRealizable 0) :
    SqClassClearingSupply 0 5 :=
  gDeep_supply_five gDeep_separationAll_handleFree HR

end Reseed

/-! ## §9 Axiom pins -/

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
#print axioms GQ2.Dyadic.SqCore.gDeepCoker
#print axioms GQ2.Dyadic.SqCore.gDeepWide
#print axioms GQ2.Dyadic.SqCore.gDeepWideFull
#print axioms gDeep_reach_le_wide
#print axioms gDeep_wide_le_wideFull
#print axioms gDeep_wideFull_eq
#print axioms gDeep_B_sq_mem_four
#print axioms gDeep_C_sq_mem_four
#print axioms gDeep_coker_central
#print axioms gDeep_coker_normal
#print axioms gDeep_B_img_sq
#print axioms gDeep_C_img_sq
#print axioms gDeep_coker_form
#print axioms gDeep_sq_rowTrivial
#print axioms gDeep_defect_rowTrivial
#print axioms gDeep_pow_four_gammaTwo
#print axioms gDeep_family_pow
#print axioms gDeep_family_brPow
#print axioms gDeep_sqBr_mem_three
#print axioms gDeep_trBr_mem_three
#print axioms gDeep_bracket_wide
#print axioms gDeep_zLayer_le_wideFull
#print axioms gDeep_B_sq_nuLam
#print axioms gDeep_B_sq_nu
#print axioms gDeep_C_sq_nuLam
#print axioms gDeep_C_sq_nu
#print axioms gDeep_wideFull_realize
#print axioms gDeep_wide_cut
#print axioms gDeep_layer_wide
#print axioms gDeep_leftover_decomp
#print axioms gDeep_unit_mul_dvd
#print axioms gDeep_delta_sq
#print axioms gDeep_chiSq_B_sq
#print axioms gDeep_chiSq_C_sq
#print axioms gDeep_delta_B_sq_rowS
#print axioms gDeep_delta_B_sq_rowX
#print axioms gDeep_delta_C_sq_rowX
#print axioms gDeep_delta_C_sq_rowS
#print axioms gDeep_kill_mid
#print axioms gDeep_kill_last
#print axioms gDeep_zero_reader_reach
#print axioms gDeep_B_sq_notMem_reach
#print axioms gDeep_C_sq_notMem_reach
#print axioms GQ2.Dyadic.SqCore.GDeepKillAt
#print axioms gDeep_killAt_two
#print axioms gDeep_killAt_three
#print axioms gDeep_defectVanishing_of_kills
#print axioms gDeep_supply_of_kills
#print axioms gDeep_markTransitivity_of_kills
#print axioms GQ2.Dyadic.SqCore.GDeepVanishingThree
#print axioms gDeep_vanishingThree_of_sep
#print axioms gDeep_clear_step_three
#print axioms gDeep_chiSupply_five
#print axioms gDeep_supply_five
#print axioms gDeep_separationAll_handleFree
#print axioms gDeep_supply_five_handleFree

end AxiomPins

end SqCore

end Dyadic

end GQ2
