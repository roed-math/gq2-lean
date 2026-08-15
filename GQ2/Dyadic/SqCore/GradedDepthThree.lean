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
