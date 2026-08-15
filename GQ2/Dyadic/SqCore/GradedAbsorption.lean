/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedUniformJoin
import GQ2.Dyadic.SqCore.GradedBaseDecide

/-!
# W78-ABSORB: the leftover normal form and Labute's Theorem 5 absorption

Wave 77 refuted the depth-2 base (`GBaseResidual h`, `GJoinBase h`) at every `h`: the
images of `⁅x₁,σ⁆²` and `⁅x₁,x₀⁆²` are unreachable from the tower side.  Labute's own
proof survives this because his successive approximation never needs full layer
generation: at each level the leftover decomposes as a knob image times coker classes
with `𝔽₂`-coefficients, and in the character-pinned regime (his Theorem 5) those
coefficients are killed by the Δ-functional constraint rather than absorbed.

This file formalizes that mechanism.  Contents to be built in this lane:

* the leftover normal form at depth 2 (T1);
* the coefficient-killing constraint for the supply's actual defects (T2);
* the re-seeded clearing recursion (T3).
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute FoxH

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 The handle-corrected coefficient rows

Labute's Theorem 5 argument needs, for each coker class, a crossed homomorphism that reads
that class at the layer bit and reads every inventory generator one bit deeper.  The plain
`σ`- and `x₀`-rows fail this at `h ≥ 1`: the Eichler-cleared letters `U_j = w^{-ν'(u_j)}u_j`
carry a pivot factor, so a core row reads them as `-ν'(u_j)`, and their admissible towers
then pollute the layer bit.  The repair is Labute's own: correct the row on the handle slots
so that every cleared letter reads zero.  The correction needed on the slot of `u_j` is
`ν'(u_j) · Δ(w)`, so the corrected row is determined by its two core values and its own pivot
reading. -/

section Rows

variable {h : ℕ}

variable (h) in
/-- **The handle-corrected coefficient row**: core values `c₀, c₁` on the `σ`- and `x₀`-slots,
zero on the `x₁`-slot, and on each handle slot the `ν'`-value of its letter scaled by `P`.
When `P` is the row's own pivot reading, every Eichler-cleared letter reads zero
(`gAbs_delta_eichU`/`gAbs_delta_eichV` below). -/
noncomputable def gAbsRow (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (c₀ c₁ P : ℤ_[2]) : Fin (sqRank h) → ℤ_[2] :=
  fun i =>
    (if i = 0 then c₀ else 0) + (if i = 1 then c₁ else 0) +
      P * ((∑ j : Fin h,
              if i = sqHandleIdxU j then toAdd (nu' (sqGen h (sqHandleIdxU j))) else 0) +
            ∑ j : Fin h,
              if i = sqHandleIdxV j then toAdd (nu' (sqGen h (sqHandleIdxV j))) else 0)

variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {c₀ c₁ P : ℤ_[2]}

theorem gAbsRow_zero : gAbsRow h nu' c₀ c₁ P 0 = c₀ := by
  have h01 : (0 : Fin (sqRank h)) ≠ 1 := by
    rw [ne_eq, Fin.ext_iff, sqVal_zero, sqVal_one]; omega
  rw [gAbsRow, if_pos rfl, if_neg h01,
    Finset.sum_eq_zero fun j _ =>
      if_neg (Ne.symm (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_zero]; omega))),
    Finset.sum_eq_zero fun j _ =>
      if_neg (Ne.symm (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_zero]; omega)))]
  ring

theorem gAbsRow_one : gAbsRow h nu' c₀ c₁ P 1 = c₁ := by
  have h10 : (1 : Fin (sqRank h)) ≠ 0 := by
    rw [ne_eq, Fin.ext_iff, sqVal_zero, sqVal_one]; omega
  rw [gAbsRow, if_neg h10, if_pos rfl,
    Finset.sum_eq_zero fun j _ =>
      if_neg (Ne.symm (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_one]; omega))),
    Finset.sum_eq_zero fun j _ =>
      if_neg (Ne.symm (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_one]; omega)))]
  ring

theorem gAbsRow_two : gAbsRow h nu' c₀ c₁ P 2 = 0 := by
  have h20 : (2 : Fin (sqRank h)) ≠ 0 := by
    rw [ne_eq, Fin.ext_iff, sqVal_zero, sqVal_two]; omega
  have h21 : (2 : Fin (sqRank h)) ≠ 1 := by
    rw [ne_eq, Fin.ext_iff, sqVal_one, sqVal_two]; omega
  rw [gAbsRow, if_neg h20, if_neg h21,
    Finset.sum_eq_zero fun j _ =>
      if_neg (Ne.symm (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_two]; omega))),
    Finset.sum_eq_zero fun j _ =>
      if_neg (Ne.symm (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_two]; omega)))]
  ring

theorem gAbsRow_handleU (j : Fin h) :
    gAbsRow h nu' c₀ c₁ P (sqHandleIdxU j) = P * toAdd (nu' (sqGen h (sqHandleIdxU j))) := by
  have hU : (∑ j' : Fin h, if sqHandleIdxU j = sqHandleIdxU j'
      then toAdd (nu' (sqGen h (sqHandleIdxU j'))) else 0)
      = toAdd (nu' (sqGen h (sqHandleIdxU j))) := by
    rw [Fintype.sum_eq_single j fun j' hj' =>
      if_neg fun hc => hj' (sqHandleIdxU_injective hc.symm), if_pos rfl]
  have hV : (∑ j' : Fin h, if sqHandleIdxU j = sqHandleIdxV j'
      then toAdd (nu' (sqGen h (sqHandleIdxV j'))) else 0) = 0 :=
    Finset.sum_eq_zero fun j' _ => if_neg (sqHandleIdxU_ne_sqHandleIdxV j j')
  rw [gAbsRow, if_neg (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_zero]; omega)),
    if_neg (sqHandleIdxU_ne_of_val_lt j (by rw [sqVal_one]; omega)), hU, hV]
  ring

theorem gAbsRow_handleV (j : Fin h) :
    gAbsRow h nu' c₀ c₁ P (sqHandleIdxV j) = P * toAdd (nu' (sqGen h (sqHandleIdxV j))) := by
  have hU : (∑ j' : Fin h, if sqHandleIdxV j = sqHandleIdxU j'
      then toAdd (nu' (sqGen h (sqHandleIdxU j'))) else 0) = 0 :=
    Finset.sum_eq_zero fun j' _ => if_neg (Ne.symm (sqHandleIdxU_ne_sqHandleIdxV j' j))
  have hV : (∑ j' : Fin h, if sqHandleIdxV j = sqHandleIdxV j'
      then toAdd (nu' (sqGen h (sqHandleIdxV j'))) else 0)
      = toAdd (nu' (sqGen h (sqHandleIdxV j))) := by
    rw [Fintype.sum_eq_single j fun j' hj' =>
      if_neg fun hc => hj' (sqHandleIdxV_injective hc.symm), if_pos rfl]
  rw [gAbsRow, if_neg (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_zero]; omega)),
    if_neg (sqHandleIdxV_ne_of_val_lt j (by rw [sqVal_one]; omega)), hU, hV]
  ring

/-- The pivot reading of any row with trivial `x₀`-slot is its `σ`-slot value
(`gJoin_delta_pivot` with the `σ`-slot kept). -/
theorem gAbs_delta_pivot {c : Fin (sqRank h) → ℤ_[2]} (h1 : c 1 = 0) :
    gDelta h c (sqPivot h) = c 0 := by
  have hx0 : gDelta h c (dsqX0 h) = 0 := by rw [dsqX0, gDelta_gen, h1]
  have hzp : gDelta h c (zpowZtwo (isProP_DSq h) (dsqX0 h) sqPivotExp) = 0 :=
    gJoin_zpow_vanish hx0 _
  rw [sqPivot, sqMixPivotElem, gDelta_mul, gDelta_inv, hzp, mul_zero, neg_zero, mul_zero,
    add_zero, dsqSigma, gDelta_gen]

/-- **Two rows agreeing on the core slots read the pivot equally**: the difference of two
`gDelta`-functionals with the same twist is again a crossed homomorphism, its kernel is a
closed subgroup, and the pivot is a word in `σ` and `x₀` alone. -/
theorem gAbs_pivot_agree {c c' : Fin (sqRank h) → ℤ_[2]} (h0 : c 0 = c' 0)
    (h1 : c 1 = c' 1) : gDelta h c (sqPivot h) = gDelta h c' (sqPivot h) := by
  set K : Subgroup (DSq h : Type) :=
    { carrier := {x | gDelta h c x = gDelta h c' x}
      one_mem' := by simp only [Set.mem_setOf_eq, gDelta_one]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [gDelta_mul, gDelta_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [gDelta_inv, gDelta_inv, ha] } with hK
  have hKclosed : IsClosed (K : Set (DSq h : Type)) :=
    isClosed_eq (gDelta_continuous c) (gDelta_continuous c')
  have hsigma : dsqSigma h ∈ K := by
    show gDelta h c (dsqSigma h) = gDelta h c' (dsqSigma h)
    rw [dsqSigma, gDelta_gen, gDelta_gen, h0]
  have hx0 : dsqX0 h ∈ K := by
    show gDelta h c (dsqX0 h) = gDelta h c' (dsqX0 h)
    rw [dsqX0, gDelta_gen, gDelta_gen, h1]
  have hzp : zpowZtwo (isProP_DSq h) (dsqX0 h) sqPivotExp ∈ K := by
    have hle : (Subgroup.closure ({dsqX0 h} : Set (DSq h : Type))).topologicalClosure ≤ K :=
      Subgroup.topologicalClosure_minimal _
        ((Subgroup.closure_le _).2 (by rintro _ rfl; exact hx0)) hKclosed
    exact hle (zpowZtwo_mem_topologicalClosure (isProP_DSq h) (dsqX0 h) sqPivotExp)
  have hpiv : sqPivot h ∈ K := by
    rw [sqPivot, sqMixPivotElem]
    exact K.mul_mem hsigma (K.inv_mem hzp)
  exact hpiv

/-- **The cleared `u`-letter reads its own slot minus its `ν'`-value times the pivot
reading**, at every row: the general-`c` form of `gJoin_delta_eichU`. -/
theorem gAbs_delta_eichU (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    gDelta h c (sqEichU h nu' j)
      = c (sqHandleIdxU j)
        - toAdd (nu' (sqGen h (sqHandleIdxU j))) * gDelta h c (sqPivot h) := by
  rw [sqEichU, gDelta_mul, gDelta_inv, map_inv, gDelta_chiSq_zpow_pivot, inv_one,
    Units.val_one, one_mul, one_mul, gDelta_gen,
    gJoin_delta_zpow _ (chiSq_sqPivot h)]
  ring

/-- The cleared `v`-letter, same reading. -/
theorem gAbs_delta_eichV (c : Fin (sqRank h) → ℤ_[2])
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h) :
    gDelta h c (sqEichV h nu' j)
      = c (sqHandleIdxV j)
        - toAdd (nu' (sqGen h (sqHandleIdxV j))) * gDelta h c (sqPivot h) := by
  rw [sqEichV, gDelta_mul, gDelta_inv, gDelta_chiSq_zpow_pivot, inv_one, chiSq_handleV,
    Units.val_one, gDelta_gen, gJoin_delta_zpow _ (chiSq_sqPivot h)]
  ring

variable (h) in
/-- **The corrected `σ`-row**: reads `σ` as `1`, `x₀` and `x₁` as `0`, the pivot as `1`, and
every Eichler-cleared letter as `0`. -/
noncomputable def gAbsRowS (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    Fin (sqRank h) → ℤ_[2] :=
  gAbsRow h nu' 1 0 1

variable (h) in
/-- The pivot reading of the core `x₀`-row (an opaque `ℤ₂`-constant; only its role in the
correction matters). -/
noncomputable def gAbsPX (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    ℤ_[2] :=
  gDelta h (gAbsRow h nu' 0 1 0) (sqPivot h)

variable (h) in
/-- **The corrected `x₀`-row**: reads `x₀` as `1`, `σ` and `x₁` as `0`, and every
Eichler-cleared letter as `0`; its pivot reading is `gAbsPX`. -/
noncomputable def gAbsRowX (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    Fin (sqRank h) → ℤ_[2] :=
  gAbsRow h nu' 0 1 (gAbsPX h nu')

theorem gAbs_rowS_pivot : gDelta h (gAbsRowS h nu') (sqPivot h) = 1 := by
  rw [gAbsRowS, gAbs_delta_pivot (gAbsRow_one (h := h)), gAbsRow_zero]

theorem gAbs_rowX_pivot : gDelta h (gAbsRowX h nu') (sqPivot h) = gAbsPX h nu' := by
  rw [gAbsRowX, gAbsPX]
  exact gAbs_pivot_agree (by rw [gAbsRow_zero, gAbsRow_zero]) (by rw [gAbsRow_one, gAbsRow_one])

theorem gAbs_rowS_eichU (j : Fin h) : gDelta h (gAbsRowS h nu') (sqEichU h nu' j) = 0 := by
  rw [gAbs_delta_eichU, gAbs_rowS_pivot, gAbsRowS, gAbsRow_handleU]
  ring

theorem gAbs_rowS_eichV (j : Fin h) : gDelta h (gAbsRowS h nu') (sqEichV h nu' j) = 0 := by
  rw [gAbs_delta_eichV, gAbs_rowS_pivot, gAbsRowS, gAbsRow_handleV]
  ring

theorem gAbs_rowX_eichU (j : Fin h) : gDelta h (gAbsRowX h nu') (sqEichU h nu' j) = 0 := by
  rw [gAbs_delta_eichU, gAbs_rowX_pivot, gAbsRowX, gAbsRow_handleU]
  ring

theorem gAbs_rowX_eichV (j : Fin h) : gDelta h (gAbsRowX h nu') (sqEichV h nu' j) = 0 := by
  rw [gAbs_delta_eichV, gAbs_rowX_pivot, gAbsRowX, gAbsRow_handleV]
  ring

end Rows

/-! ## §2 The depth-2 reach lies in the layer kernel of both corrected rows

The knob half is wave 75's own `gJoin_knob_dvd`/`gJoin_bundle_dvd` at depth `2`.  The tower
half is new and is where the corrected rows earn their keep: the Eichler towers read exactly
zero because their letters do, and the `x̃₁`-tower reads `16`-divisibly at every row because
`χ(x̃₁) ≡ -1 (mod 8)` makes the norm sum at exponent `4` collapse. -/

section ReachKernel

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- `χ(x̃₁) ≡ -1 (mod 8)`: the cleared letter's orientation is the odd part of `Y`, and
`Y + X² = (Y + 1) + (X² - 1)` with both terms `8`-divisible. -/
theorem gAbs_chi_xOne_add_one :
    (2 : ℤ_[2]) ^ 3 ∣ ((chiSq h (gTowerXOne h) : ℤ_[2]ˣ) : ℤ_[2]) + 1 := by
  have hchi : chiSq h (gTowerXOne h) = YvalUnit * (rootXUnit ^ 2)⁻¹ := by
    rw [gTowerXOne, map_mul, map_inv, chiSq_x1,
      map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h), chiSq_x0,
      show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from by norm_num, zpowZtwo_natCast]
  obtain ⟨y, hy⟩ := gJoin_Yval_add_one
  obtain ⟨a, ha⟩ := gDelta_rootX_sub_one
  have hXsq : rootX ^ 2 - 1 = 2 ^ 3 * ((a : ℤ_[2]) * (2 * (a : ℤ_[2]) + 1)) := by
    linear_combination (rootX + 1 + 2 ^ 2 * (a : ℤ_[2])) * ha
  have hval : ((chiSq h (gTowerXOne h) : ℤ_[2]ˣ) : ℤ_[2])
      = Yval * (((rootXUnit ^ 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
    rw [hchi, Units.val_mul, val_YvalUnit]
  have hcanc : (((rootXUnit ^ 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (rootX ^ 2) = 1 := by
    have : (((rootXUnit ^ 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((rootXUnit ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rwa [Units.val_pow_eq_pow_val, val_rootXUnit] at this
  refine ⟨(((rootXUnit ^ 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (y + (a : ℤ_[2]) * (2 * (a : ℤ_[2]) + 1)), ?_⟩
  rw [hval]
  linear_combination (((rootXUnit ^ 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hy
    + (((rootXUnit ^ 2)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hXsq - hcanc

/-- The norm sum at exponent `4`, factored. -/
theorem gAbs_normSum_four (X : ℤ_[2]) : normSum X 4 = (1 + X) * (1 + X ^ 2) := by
  simp only [normSum, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- **The `x̃₁`-fourth-power reads `16`-divisibly**, at every row: the norm sum
`N₄(χ(x̃₁)) = (1 + χ)(1 + χ²)` has `v₂ ≥ 3 + 1`. -/
theorem gAbs_xOne_pow_four_dvd (c : Fin (sqRank h) → ℤ_[2]) :
    (2 : ℤ_[2]) ^ 4 ∣ gDelta h c (gTowerXOne h ^ 4) := by
  rw [gDelta_pow, gAbs_normSum_four]
  obtain ⟨y, hy⟩ := gAbs_chi_xOne_add_one (h := h)
  have hodd : (2 : ℤ_[2]) ∣ 1 + ((chiSq h (gTowerXOne h) : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 := by
    obtain ⟨t, ht⟩ := two_dvd_sub_of_isUnit (Units.isUnit (chiSq h (gTowerXOne h) ^ 2)) isUnit_one
    rw [Units.val_pow_eq_pow_val] at ht
    exact ⟨t + 1, by linear_combination ht⟩
  obtain ⟨s, hs⟩ := hodd
  refine ⟨y * s * gDelta h c (gTowerXOne h), ?_⟩
  linear_combination
    ((1 + ((chiSq h (gTowerXOne h) : ℤ_[2]ˣ) : ℤ_[2]) ^ 2) * gDelta h c (gTowerXOne h)) * hy
    + (2 ^ 3 * y * gDelta h c (gTowerXOne h)) * hs

/-- **The `x̃₁`-tower at depth `2` reads `8`-divisibly at every row** (in fact `16`-divisibly):
the `ℤ₂`-exponent statement, by density of `ℕ` from the fourth-power case. -/
theorem gAbs_xOne_tower_dvd (c : Fin (sqRank h) → ℤ_[2]) (a : ℤ_[2]) :
    (2 : ℤ_[2]) ^ 3 ∣
      gDelta h c (zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ 2 * a)) := by
  have hall : ∀ b : ℤ_[2], (2 : ℤ_[2]) ^ 4 ∣
      gDelta h c (zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ 2 * b)) := by
    intro b
    have hclosed : IsClosed {b : ℤ_[2] | (2 : ℤ_[2]) ^ 4 ∣
        gDelta h c (zpowZtwo (isProP_DSq h) (gTowerXOne h) (2 ^ 2 * b))} := by
      refine (gDelta_isClosed_dvd_set 4).preimage ?_
      exact (gDelta_continuous c).comp
        ((continuous_zpowZtwo (isProP_DSq h) (gTowerXOne h)).comp
          (continuous_const.mul continuous_id))
    refine PadicInt.denseRange_natCast.induction_on b hclosed ?_
    intro n
    have hcast : (2 : ℤ_[2]) ^ 2 * (n : ℤ_[2]) = ((4 * n : ℕ) : ℤ_[2]) := by push_cast; ring
    rw [hcast, zpowZtwo_natCast, pow_mul]
    obtain ⟨s, hs⟩ := gAbs_xOne_pow_four_dvd (h := h) c
    rw [gDelta_pow, hs]
    exact ⟨normSum ((chiSq h (gTowerXOne h ^ 4) : ℤ_[2]ˣ) : ℤ_[2]) n * s, by ring⟩
  exact (pow_dvd_pow (2 : ℤ_[2]) (by omega : 3 ≤ 4)).trans (hall a)

/-- ⭐⭐ **The depth-2 reach lies in the layer kernel of any row that kills the cleared
letters.**  Knobs and bundles are `8`-divisible by wave 75's invisibility bounds; the
Eichler towers read zero; the `x̃₁`-tower is `16`-divisible.  Both corrected rows qualify. -/
theorem gAbs_reach_le_layerDvd {c : Fin (sqRank h) → ℤ_[2]}
    (hU : ∀ j, gDelta h c (sqEichU h nu' j) = 0)
    (hV : ∀ j, gDelta h c (sqEichV h nu' j) = 0) :
    gTowerReach h nu' 2 ≤ gJoinLayerDvd h c 2 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z (hz | ⟨x, hx, a, rfl⟩)
  · rcases hz with ⟨t, q, ht, hq, rfl⟩ | ⟨t, ht, rfl⟩
    · exact gJoin_mem_layerDvd.2 (gJoin_knob_dvd (k := 0) ht hq c)
    · exact gJoin_mem_layerDvd.2 (gJoin_bundle_dvd (k := 0) ht c)
  · simp only [gTowerXLetters, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hx
    obtain (rfl | ⟨j, rfl⟩) | ⟨j, rfl⟩ := hx
    · exact gJoin_mem_layerDvd.2 (gAbs_xOne_tower_dvd c a)
    · refine gJoin_mem_layerDvd.2 ?_
      rw [gJoin_zpow_vanish (hU j)]
      exact dvd_zero _
    · refine gJoin_mem_layerDvd.2 ?_
      rw [gJoin_zpow_vanish (hV j)]
      exact dvd_zero _

theorem gAbs_reach_le_layerDvd_rowS :
    gTowerReach h nu' 2 ≤ gJoinLayerDvd h (gAbsRowS h nu') 2 :=
  gAbs_reach_le_layerDvd (fun j => gAbs_rowS_eichU j) (fun j => gAbs_rowS_eichV j)

theorem gAbs_reach_le_layerDvd_rowX :
    gTowerReach h nu' 2 ≤ gJoinLayerDvd h (gAbsRowX h nu') 2 :=
  gAbs_reach_le_layerDvd (fun j => gAbs_rowX_eichU j) (fun j => gAbs_rowX_eichV j)

end ReachKernel

/-! ## §3 The coker pair and its readings

The two classes wave 77 proved unreachable, as elements: the triple brackets
`B = ⁅⁅x₁,σ⁆,x₁⁆` and `C = ⁅⁅x₁,x₀⁆,x₁⁆` (in `commP` spelling).  Each is read `4·unit` by
its own corrected row and `0` by the other's.  Since the whole depth-2 reach reads
`8`-divisibly (§2), the layer bit of the two corrected rows separates the coker from the
reach: this is the exact constraint that kills the coker coefficients of any all-rows-zero
defect. -/

section Coker

variable {h : ℕ}

variable (h) in
/-- The `σ`-coker element `⁅⁅x₁,σ⁆,x₁⁆` (wave 77's `gDecide_sigma_not_mem` class). -/
noncomputable def gAbsB : (DSq h : Type) := commP (commP (dsqX1 h) (dsqSigma h)) (dsqX1 h)

variable (h) in
/-- The `x₀`-coker element `⁅⁅x₁,x₀⁆,x₁⁆` (wave 77's `gDecide_x0_not_mem` class). -/
noncomputable def gAbsC : (DSq h : Type) := commP (commP (dsqX1 h) (dsqX0 h)) (dsqX1 h)

theorem gAbs_B_mem_three : gAbsB h ∈ twoCentralSeries (DSq h : Type) 3 :=
  cfive_commP_mem_succ (cfour_commP_mem_two _ _) _

theorem gAbs_C_mem_three : gAbsC h ∈ twoCentralSeries (DSq h : Type) 3 :=
  cfive_commP_mem_succ (cfour_commP_mem_two _ _) _

theorem gAbs_chiSq_B : chiSq h (gAbsB h) = 1 := gDelta_chiSq_commP _ _

theorem gAbs_chiSq_C : chiSq h (gAbsC h) = 1 := gDelta_chiSq_commP _ _

/-- `Y - 1 = -2·unit`: the exact valuation of `χ(x₁) - 1`, from `Y = -X²` and
`v₂(X² + 1) = 1`. -/
theorem gAbs_Yval_sub_one : ∃ d : ℤ_[2]ˣ, Yval - 1 = -(2 * (d : ℤ_[2])) := by
  obtain ⟨d, hd⟩ := gDelta_rootX_sq_add_one
  exact ⟨d, by rw [Yval_eq]; linear_combination -hd⟩

/-- The reading of a triple bracket `⁅⁅x₁,g⁆,x₁⁆` at any row: the inner bracket is
`χ`-trivial, so the outer bracket contributes the single factor `χ(x₁)⁻¹ - 1`. -/
theorem gAbs_delta_triple (c : Fin (sqRank h) → ℤ_[2]) (g : (DSq h : Type)) :
    gDelta h c (commP (commP (dsqX1 h) g) (dsqX1 h))
      = ((((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) * gDelta h c (commP (dsqX1 h) g) := by
  rw [gDelta_commP, gDelta_chiSq_commP, chiSq_x1]
  simp only [inv_one, Units.val_one, one_mul, sub_self, mul_zero, zero_mul, add_zero]

/-- The inner `σ`-bracket reading, at a row with trivial `x₁`-slot. -/
theorem gAbs_delta_inner_sigma {c : Fin (sqRank h) → ℤ_[2]} (h2 : c 2 = 0) :
    gDelta h c (commP (dsqX1 h) (dsqSigma h))
      = (((SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - (((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))) * c 0 := by
  have hx1 : gDelta h c (dsqX1 h) = 0 := by rw [dsqX1, gDelta_gen, h2]
  have hs : gDelta h c (dsqSigma h) = c 0 := by rw [dsqSigma, gDelta_gen]
  rw [gDelta_commP, chiSq_x1, chiSq_sigma, hx1, hs]
  ring

/-- The inner `x₀`-bracket reading, at a row with trivial `x₁`-slot. -/
theorem gAbs_delta_inner_x0 {c : Fin (sqRank h) → ℤ_[2]} (h2 : c 2 = 0) :
    gDelta h c (commP (dsqX1 h) (dsqX0 h))
      = (((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - (((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))) * c 1 := by
  have hx1 : gDelta h c (dsqX1 h) = 0 := by rw [dsqX1, gDelta_gen, h2]
  have hx0 : gDelta h c (dsqX0 h) = c 1 := by rw [dsqX0, gDelta_gen]
  rw [gDelta_commP, chiSq_x1, chiSq_x0, hx1, hx0]
  ring

/-- `(Y⁻¹ - 1)·(1 - Y⁻¹) = -4·unit`: the square of the exact-valuation factor. -/
theorem gAbs_Yfactor_sq : ∃ u : ℤ_[2]ˣ,
    ((((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1) * (1 - (((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
      = 2 ^ 2 * (u : ℤ_[2]) := by
  obtain ⟨d, hd⟩ := gAbs_Yval_sub_one
  have hcanc : (((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * Yval = 1 := by
    rw [← val_YvalUnit, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨-((YvalUnit⁻¹ : ℤ_[2]ˣ) * (YvalUnit⁻¹ : ℤ_[2]ˣ) * d * d), ?_⟩
  have hYinv : (((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1
      = (((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (2 * (d : ℤ_[2])) := by
    linear_combination -(((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hd + hcanc
  simp only [Units.val_neg, Units.val_mul]
  linear_combination (-((((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1
    + (((YvalUnit)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (2 * (d : ℤ_[2])))) * hYinv

/-- ⭐ **The `σ`-coker class reads `4·unit` at the corrected `σ`-row.** -/
theorem gAbs_delta_B_rowS {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} :
    ∃ u : ℤ_[2]ˣ, gDelta h (gAbsRowS h nu') (gAbsB h) = 2 ^ 2 * (u : ℤ_[2]) := by
  obtain ⟨u, hu⟩ := gAbs_Yfactor_sq
  refine ⟨u * SvalUnit⁻¹, ?_⟩
  rw [gAbsB, gAbs_delta_triple, gAbsRowS, gAbs_delta_inner_sigma (gAbsRow_two (h := h)),
    gAbsRow_zero, Units.val_mul]
  linear_combination ((SvalUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hu

/-- The `σ`-coker class is invisible to the corrected `x₀`-row. -/
theorem gAbs_delta_B_rowX {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} :
    gDelta h (gAbsRowX h nu') (gAbsB h) = 0 := by
  rw [gAbsB, gAbs_delta_triple, gAbsRowX, gAbs_delta_inner_sigma (gAbsRow_two (h := h)),
    gAbsRow_zero]
  ring

/-- ⭐ **The `x₀`-coker class reads `4·unit` at the corrected `x₀`-row.** -/
theorem gAbs_delta_C_rowX {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} :
    ∃ u : ℤ_[2]ˣ, gDelta h (gAbsRowX h nu') (gAbsC h) = 2 ^ 2 * (u : ℤ_[2]) := by
  obtain ⟨u, hu⟩ := gAbs_Yfactor_sq
  refine ⟨u * rootXUnit⁻¹, ?_⟩
  rw [gAbsC, gAbs_delta_triple, gAbsRowX, gAbs_delta_inner_x0 (gAbsRow_two (h := h)),
    gAbsRow_one, Units.val_mul]
  linear_combination ((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hu

/-- The `x₀`-coker class is invisible to the corrected `σ`-row. -/
theorem gAbs_delta_C_rowS {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} :
    gDelta h (gAbsRowS h nu') (gAbsC h) = 0 := by
  rw [gAbsC, gAbs_delta_triple, gAbsRowS, gAbs_delta_inner_x0 (gAbsRow_two (h := h)),
    gAbsRow_one]
  ring

end Coker

/-! ## Axiom pins (§§1-3) -/

section AxiomPinsA

#print axioms GQ2.Dyadic.SqCore.gAbsRow
#print axioms gAbsRow_zero
#print axioms gAbsRow_one
#print axioms gAbsRow_two
#print axioms gAbsRow_handleU
#print axioms gAbsRow_handleV
#print axioms gAbs_delta_pivot
#print axioms gAbs_pivot_agree
#print axioms gAbs_delta_eichU
#print axioms gAbs_delta_eichV
#print axioms GQ2.Dyadic.SqCore.gAbsRowS
#print axioms GQ2.Dyadic.SqCore.gAbsPX
#print axioms GQ2.Dyadic.SqCore.gAbsRowX
#print axioms gAbs_rowS_pivot
#print axioms gAbs_rowX_pivot
#print axioms gAbs_rowS_eichU
#print axioms gAbs_rowS_eichV
#print axioms gAbs_rowX_eichU
#print axioms gAbs_rowX_eichV
#print axioms gAbs_chi_xOne_add_one
#print axioms gAbs_normSum_four
#print axioms gAbs_xOne_pow_four_dvd
#print axioms gAbs_xOne_tower_dvd
#print axioms gAbs_reach_le_layerDvd
#print axioms gAbs_reach_le_layerDvd_rowS
#print axioms gAbs_reach_le_layerDvd_rowX
#print axioms GQ2.Dyadic.SqCore.gAbsB
#print axioms GQ2.Dyadic.SqCore.gAbsC
#print axioms gAbs_B_mem_three
#print axioms gAbs_C_mem_three
#print axioms gAbs_chiSq_B
#print axioms gAbs_chiSq_C
#print axioms gAbs_Yval_sub_one
#print axioms gAbs_delta_triple
#print axioms gAbs_delta_inner_sigma
#print axioms gAbs_delta_inner_x0
#print axioms gAbs_Yfactor_sq
#print axioms gAbs_delta_B_rowS
#print axioms gAbs_delta_C_rowS
#print axioms gAbs_delta_C_rowX
#print axioms gAbs_delta_B_rowX

end AxiomPinsA

end SqCore

end Dyadic

end GQ2
