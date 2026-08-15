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

This file formalizes that mechanism.

* **T1** (`gAbs_layer_wide`, `gAbs_leftover_decomp`): the leftover normal form.  Adjoining
  the two refuted classes `B = [[x1,sigma],x1]` and `C = [[x1,x0],x1]` to the depth-2 reach
  absorbs the whole layer: every exactly row-trivial `γ₃`-element is a reach element times
  `B^{e₁}C^{e₂}` with `𝔽₂`-exponents.  Unconditional; wave 76's chain re-run against the
  widened reach, the handle instances reduced through the Eichler bracket squares.
* **T2** (`gAbs_zero_reader_reach`): the coefficient kill.  Two handle-corrected rows make
  the whole depth-2 reach read `8`-divisibly while `B` and `C` read `4·unit` each at its own
  row and `0` at the other's; a defect reads `0` at every row, so `e₁ = e₂ = 0`.  The
  refuted layer statement is recovered exactly on the all-rows-zero elements.
* **T3** (`gAbs_vanishingTwo_of_sep` through `gAbs_markTransitivity_of_baseThree`): the
  repaired class-3-to-4 step, the class-4 supply witness wave 77 costed the re-cut at
  (`gAbs_supply_four`), and the re-seeded recursion: the residual from the OPEN depth-3 base
  plus the two wave-75 interfaces, the refuted input replaced by an open one.
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

/-! ## §4 The widened reach, and the whole triple family lands in it

Wave 76 reduced the depth-2 base to the `x₁`-slot triple brackets `⁅⁅x₁, letter⁆, x₁⁆`; wave
77 refuted exactly the `σ`- and `x₀`-instances.  This section proves the unconditional
remainder: adjoining those two classes to the reach absorbs the whole family.  The handle
instances reduce to the two adjoined classes because the Eichler-cleared letters' bracket
squares reach unconditionally (the bundle at the correction `U²`, Labute's `w ∈ W ∩ F`
generator), and the pivot is a word in `σ` and `x₀`. -/

section Wide

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

variable (h) in
/-- **The coker span**: the subgroup of `Q₄` generated by the two wave-77 classes. -/
noncomputable def gAbsCoker : Subgroup (levelQuot (DSq h : Type) 4) :=
  Subgroup.closure
    {levelMk (DSq h : Type) 4 (gAbsB h), levelMk (DSq h : Type) 4 (gAbsC h)}

variable (h) in
/-- **The widened reach**: the depth-2 admissible reach with the coker adjoined. -/
noncomputable def gAbsWide
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    Subgroup (levelQuot (DSq h : Type) 4) :=
  gTowerReach h nu' 2 ⊔ gAbsCoker h

theorem gAbs_reach_le_wide : gTowerReach h nu' 2 ≤ gAbsWide h nu' := le_sup_left

/-- The coker is central: both generators are `γ₃`-images. -/
theorem gAbs_coker_central : gAbsCoker h ≤ Subgroup.center (levelQuot (DSq h : Type) 4) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact Subgroup.mem_center_iff.2 fun g => gTower_img_central (k := 2) gAbs_B_mem_three g
  · exact Subgroup.mem_center_iff.2 fun g => gTower_img_central (k := 2) gAbs_C_mem_three g

theorem gAbs_coker_normal : (gAbsCoker h).Normal := by
  constructor
  intro n hn g
  have hc : g * n = n * g := Subgroup.mem_center_iff.1 (gAbs_coker_central hn) g
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact hn

/-- The coker generators are involutions in `Q₄`: squares of `γ₃`-elements die at level 4. -/
theorem gAbs_B_img_sq : levelMk (DSq h : Type) 4 (gAbsB h) ^ 2 = 1 := by
  rw [← map_pow]
  exact (lim_mem_twoCentralSeries_iff_levelMk 4 _).mp
    (sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) gAbs_B_mem_three)

theorem gAbs_C_img_sq : levelMk (DSq h : Type) 4 (gAbsC h) ^ 2 = 1 := by
  rw [← map_pow]
  exact (lim_mem_twoCentralSeries_iff_levelMk 4 _).mp
    (sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) gAbs_C_mem_three)

/-- Combining `𝔽₂`-exponents of an involution. -/
theorem gAbs_pow_combine {Q : Type*} [Group Q] {x : Q} (hx : x ^ 2 = 1) :
    ∀ e f : ℕ, e ≤ 1 → f ≤ 1 → ∃ g, g ≤ 1 ∧ x ^ e * x ^ f = x ^ g := by
  intro e f he hf
  match e, he with
  | 0, _ => exact ⟨f, hf, by rw [pow_zero, one_mul]⟩
  | 1, _ =>
    match f, hf with
    | 0, _ => exact ⟨1, le_refl 1, by rw [pow_zero, mul_one]⟩
    | 1, _ => exact ⟨0, by omega, by rw [pow_one, pow_zero, ← pow_two, hx]⟩

/-- **Every coker element is `B^{e₁}·C^{e₂}` with `𝔽₂`-exponents**: the span of two central
commuting involutions. -/
theorem gAbs_coker_form {n : levelQuot (DSq h : Type) 4} (hn : n ∈ gAbsCoker h) :
    ∃ e₁ e₂ : ℕ, e₁ ≤ 1 ∧ e₂ ≤ 1 ∧
      n = levelMk (DSq h : Type) 4 (gAbsB h) ^ e₁ *
        levelMk (DSq h : Type) 4 (gAbsC h) ^ e₂ := by
  set Bc := levelMk (DSq h : Type) 4 (gAbsB h) with hBc
  set Cc := levelMk (DSq h : Type) 4 (gAbsC h) with hCc
  have hcommute : Commute Cc Bc := by
    show Cc * Bc = Bc * Cc
    exact Subgroup.mem_center_iff.1
      (gAbs_coker_central (Subgroup.subset_closure (Set.mem_insert _ _))) Cc
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hn
  · rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨1, 0, le_refl 1, by omega, by rw [pow_one, pow_zero, mul_one]⟩
    · exact ⟨0, 1, by omega, le_refl 1, by rw [pow_one, pow_zero, one_mul]⟩
  · exact ⟨0, 0, by omega, by omega, by rw [pow_zero, pow_zero, mul_one]⟩
  · rintro y z - - ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨f₁, f₂, hf₁, hf₂, rfl⟩
    obtain ⟨g₁, hg₁, hB⟩ := gAbs_pow_combine gAbs_B_img_sq e₁ f₁ he₁ hf₁
    obtain ⟨g₂, hg₂, hC⟩ := gAbs_pow_combine gAbs_C_img_sq e₂ f₂ he₂ hf₂
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
      | 1, _ => rw [pow_one, ← pow_two]; exact gAbs_B_img_sq
    have hCsq : Cc ^ e₂ * Cc ^ e₂ = 1 := by
      match e₂, he₂ with
      | 0, _ => rw [pow_zero, mul_one]
      | 1, _ => rw [pow_one, ← pow_two]; exact gAbs_C_img_sq
    calc Bc ^ e₁ * Cc ^ e₂ * (Bc ^ e₁ * Cc ^ e₂)
        = Bc ^ e₁ * (Cc ^ e₂ * Bc ^ e₁) * Cc ^ e₂ := by simp only [mul_assoc]
      _ = Bc ^ e₁ * (Bc ^ e₁ * Cc ^ e₂) * Cc ^ e₂ := by rw [hmid]
      _ = (Bc ^ e₁ * Bc ^ e₁) * (Cc ^ e₂ * Cc ^ e₂) := by simp only [mul_assoc]
      _ = 1 := by rw [hBsq, hCsq, one_mul]

/-- A closed subgroup of `DSq h` contains all `ℤ₂`-powers of its members. -/
theorem gAbs_zpow_mem_of_closed {K : Subgroup (DSq h : Type)}
    (hK : IsClosed (K : Set (DSq h : Type))) {x : (DSq h : Type)} (hx : x ∈ K) (A : ℤ_[2]) :
    zpowZtwo (isProP_DSq h) x A ∈ K := by
  have hle : (Subgroup.closure ({x} : Set (DSq h : Type))).topologicalClosure ≤ K :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.closure_le _).2 (by rintro _ rfl; exact hx)) hK
  exact hle (zpowZtwo_mem_topologicalClosure (isProP_DSq h) x A)

/-- The pivot lies in the far span. -/
theorem gAbs_pivot_far : sqPivot h ∈ gTowerFar h := by
  rw [sqPivot, sqMixPivotElem]
  exact Subgroup.mul_mem _ gBase_sigma_far (Subgroup.inv_mem _
    (gAbs_zpow_mem_of_closed (Subgroup.isClosed_topologicalClosure _) gBase_x0_far _))

/-- The Eichler-cleared letters lie in the far span. -/
theorem gAbs_eichU_far (j : Fin h) : sqEichU h nu' j ∈ gTowerFar h := by
  rw [sqEichU]
  exact Subgroup.mul_mem _
    (Subgroup.inv_mem _ (gAbs_zpow_mem_of_closed
      (Subgroup.isClosed_topologicalClosure _) gAbs_pivot_far _))
    (gBase_handleU_far j)

theorem gAbs_eichV_far (j : Fin h) : sqEichV h nu' j ∈ gTowerFar h := by
  rw [sqEichV]
  exact Subgroup.mul_mem _ (gBase_handleV_far j)
    (Subgroup.inv_mem _ (gAbs_zpow_mem_of_closed
      (Subgroup.isClosed_topologicalClosure _) gAbs_pivot_far _))

/-- The Eichler-cleared letters are `γ₁`-elements (a `zpowZtwo` bookkeeping step). -/
theorem gAbs_mem_one (x : (DSq h : Type)) : x ∈ twoCentralSeries (DSq h : Type) 1 := by
  have hz := gTower_zpow_dvd_mem (h := h) (le_refl 1) (a := 1)
    (by rw [Nat.sub_self, pow_zero]) x
  rwa [show (1 : ℤ_[2]) = ((1 : ℕ) : ℤ_[2]) from by norm_num, zpowZtwo_natCast, pow_one] at hz

/-- The square of an Eichler-cleared letter is an admissible depth-2 correction, at any
selected marking. -/
theorem gAbs_eichU_sq_adm (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (j : Fin h) :
    GTowerAdm h nu' 2 (sqEichU h nu' j ^ 2) := by
  have hl : nuLam h (sqEichU h nu' j) = 1 := by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_nuLam_sqEichU, toAdd_one]
  have hn : nu' (sqEichU h nu' j) = 1 := by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_nu_sqEichU hsigma hx0, toAdd_one]
  refine ⟨sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) (gAbs_mem_one _), ?_, ?_⟩
  · rw [map_pow, hl, one_pow]
  · rw [map_pow, hn, one_pow]

theorem gAbs_eichV_sq_adm (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (j : Fin h) :
    GTowerAdm h nu' 2 (sqEichV h nu' j ^ 2) := by
  have hl : nuLam h (sqEichV h nu' j) = 1 := by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_nuLam_sqEichV, toAdd_one]
  have hn : nu' (sqEichV h nu' j) = 1 := by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_nu_sqEichV hsigma hx0, toAdd_one]
  refine ⟨sq_mem_twoCentralSeries_succ (G := (DSq h : Type)) (gAbs_mem_one _), ?_, ?_⟩
  · rw [map_pow, hl, one_pow]
  · rw [map_pow, hn, one_pow]

/-- ⭐⭐ **The Eichler bracket squares reach unconditionally**: the bundle at the admissible
correction `U²` delivers `U⁴·⁅U², x₁⁆`; the fourth power is an admissible tower, the
square-in-slot identity splits the bracket, and the leftover triple is a far-span knob
because `U` itself lies in the far span.  This is wave 76 §4's `w ∈ W ∩ F` generator, in
Lean. -/
theorem gAbs_eich_bracketSq_mem {t : (DSq h : Type)} (hadm : GTowerAdm h nu' 2 (t ^ 2))
    (hfar : t ∈ gTowerFar h) (htow : levelMk (DSq h : Type) 4 (t ^ 4) ∈ gTowerReach h nu' 2) :
    (commP (levelMk (DSq h : Type) 4 t) (gBaseT h)) ^ 2 ∈ gTowerReach h nu' 2 := by
  set T := levelMk (DSq h : Type) 4 t with hT
  have hbundle : levelMk (DSq h : Type) 4 ((t ^ 2) ^ 2 * commP (t ^ 2) (dsqX1 h))
      ∈ gTowerReach h nu' 2 :=
    Subgroup.subset_closure (Or.inl (Or.inr ⟨t ^ 2, hadm, rfl⟩))
  have hknob : commP (commP T (gBaseT h)) T ∈ gTowerReach h nu' 2 := by
    have hk := gBase_knob_mem (nu' := nu') (a := t) (b := dsqX1 h) (q := t) hfar
    rwa [gBase_levelMk_triple] at hk
  have hcommsq : commP (T ^ 2) (gBaseT h) ∈ gTowerReach h nu' 2 := by
    have hfour : levelMk (DSq h : Type) 4 (commP (t ^ 2) (dsqX1 h))
        = (levelMk (DSq h : Type) 4 (t ^ 4))⁻¹ *
          levelMk (DSq h : Type) 4 ((t ^ 2) ^ 2 * commP (t ^ 2) (dsqX1 h)) := by
      rw [map_mul, show (t ^ 2) ^ 2 = t ^ 4 from by rw [← pow_mul], inv_mul_cancel_left]
    have hmem : levelMk (DSq h : Type) 4 (commP (t ^ 2) (dsqX1 h)) ∈ gTowerReach h nu' 2 := by
      rw [hfour]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htow) hbundle
    rwa [gBase_levelMk_commP, map_pow] at hmem
  have hsplit : (commP T (gBaseT h)) ^ 2
      = commP (T ^ 2) (gBaseT h) * (commP (commP T (gBaseT h)) T)⁻¹ := by
    rw [gThreeFour_commP_sq_left, mul_inv_cancel_right]
  rw [hsplit]
  exact Subgroup.mul_mem _ hcommsq (Subgroup.inv_mem _ hknob)

/-- The Eichler fourth powers are admissible towers. -/
theorem gAbs_eichU_four_mem (j : Fin h) :
    levelMk (DSq h : Type) 4 (sqEichU h nu' j ^ 4) ∈ gTowerReach h nu' 2 := by
  refine Subgroup.subset_closure (Or.inr ⟨sqEichU h nu' j, Or.inl (Or.inr ⟨j, rfl⟩), 1, ?_⟩)
  rw [mul_one, show ((2 : ℤ_[2]) ^ 2) = ((4 : ℕ) : ℤ_[2]) from by norm_num, zpowZtwo_natCast]

theorem gAbs_eichV_four_mem (j : Fin h) :
    levelMk (DSq h : Type) 4 (sqEichV h nu' j ^ 4) ∈ gTowerReach h nu' 2 := by
  refine Subgroup.subset_closure (Or.inr ⟨sqEichV h nu' j, Or.inr ⟨j, rfl⟩, 1, ?_⟩)
  rw [mul_one, show ((2 : ℤ_[2]) ^ 2) = ((4 : ℕ) : ℤ_[2]) from by norm_num, zpowZtwo_natCast]

/-- ⭐⭐ **The Eichler triple brackets reach unconditionally**, through the two spellings of
`gBase_residual_iff`. -/
theorem gAbs_eichU_triple_mem (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (j : Fin h) :
    commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (sqEichU h nu' j))) (gBaseT h)
      ∈ gTowerReach h nu' 2 := by
  refine (gBase_residual_iff _).2 ?_
  have hsq := gAbs_eich_bracketSq_mem (gAbs_eichU_sq_adm hsigma hx0 j) (gAbs_eichU_far j)
    (gAbs_eichU_four_mem j)
  rw [gBase_commP_swap (gBaseT h), inv_pow]
  exact Subgroup.inv_mem _ hsq

theorem gAbs_eichV_triple_mem (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (j : Fin h) :
    commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (sqEichV h nu' j))) (gBaseT h)
      ∈ gTowerReach h nu' 2 := by
  refine (gBase_residual_iff _).2 ?_
  have hsq := gAbs_eich_bracketSq_mem (gAbs_eichV_sq_adm hsigma hx0 j) (gAbs_eichV_far j)
    (gAbs_eichV_four_mem j)
  rw [gBase_commP_swap (gBaseT h), inv_pow]
  exact Subgroup.inv_mem _ hsq

variable (h nu') in
/-- The inner-slot test subgroup for the widened triple family. -/
noncomputable def gAbsTripleTest : Subgroup (DSq h : Type) where
  carrier := {q | commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 q)) (gBaseT h)
    ∈ gAbsWide h nu'}
  one_mem' := by
    show commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 1)) (gBaseT h) ∈ gAbsWide h nu'
    rw [map_one, cfour_comm_one, cfour_one_comm]
    exact Subgroup.one_mem _
  mul_mem' := fun {a b} ha hb => by
    show commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (a * b))) (gBaseT h)
      ∈ gAbsWide h nu'
    rw [map_mul, gBase_triple_mul_right]
    exact Subgroup.mul_mem _ hb ha
  inv_mem' := fun {a} ha => by
    show commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 a⁻¹)) (gBaseT h) ∈ gAbsWide h nu'
    rw [map_inv, gBase_triple_inv_right]
    exact Subgroup.inv_mem _ ha

theorem gAbs_tripleTest_closed :
    IsClosed ((gAbsTripleTest h nu' : Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
  haveI : DiscreteTopology (levelQuot (DSq h : Type) 4) := gTower_discrete 4
  have hset : ((gAbsTripleTest h nu' : Subgroup (DSq h : Type)) : Set (DSq h : Type)) =
      (fun q => commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 q)) (gBaseT h)) ⁻¹'
        (gAbsWide h nu' : Set (levelQuot (DSq h : Type) 4)) := rfl
  have hset2 : (fun q => commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 q)) (gBaseT h)) ⁻¹'
      (gAbsWide h nu' : Set (levelQuot (DSq h : Type) 4)) =
      levelMk (DSq h : Type) 4 ⁻¹'
        ((fun z => commP (commP (gBaseT h) z) (gBaseT h)) ⁻¹'
          (gAbsWide h nu' : Set (levelQuot (DSq h : Type) 4))) := rfl
  rw [hset, hset2]
  exact (isClosed_discrete _).preimage (continuous_levelMk (DSq h : Type) 4)

theorem gAbs_tripleTest_sigma : dsqSigma h ∈ gAbsTripleTest h nu' := by
  show commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (dsqSigma h))) (gBaseT h)
    ∈ gAbsWide h nu'
  have hB : commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (dsqSigma h))) (gBaseT h)
      = levelMk (DSq h : Type) 4 (gAbsB h) := (gBase_levelMk_triple _ _ _).symm
  rw [hB]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert _ _))

theorem gAbs_tripleTest_x0 : dsqX0 h ∈ gAbsTripleTest h nu' := by
  show commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (dsqX0 h))) (gBaseT h)
    ∈ gAbsWide h nu'
  have hC : commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (dsqX0 h))) (gBaseT h)
      = levelMk (DSq h : Type) 4 (gAbsC h) := (gBase_levelMk_triple _ _ _).symm
  rw [hC]
  exact Subgroup.mem_sup_right
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem gAbs_tripleTest_xOne : dsqX1 h ∈ gAbsTripleTest h nu' := by
  show commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (dsqX1 h))) (gBaseT h)
    ∈ gAbsWide h nu'
  rw [show levelMk (DSq h : Type) 4 (dsqX1 h) = gBaseT h from rfl, cfour_comm_self,
    cfour_one_comm]
  exact Subgroup.one_mem _

theorem gAbs_tripleTest_pivotZpow (A : ℤ_[2]) :
    zpowZtwo (isProP_DSq h) (sqPivot h) A ∈ gAbsTripleTest h nu' := by
  refine gAbs_zpow_mem_of_closed gAbs_tripleTest_closed ?_ A
  rw [sqPivot, sqMixPivotElem]
  exact Subgroup.mul_mem _ gAbs_tripleTest_sigma (Subgroup.inv_mem _
    (gAbs_zpow_mem_of_closed gAbs_tripleTest_closed gAbs_tripleTest_x0 _))

theorem gAbs_tripleTest_handleU (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (j : Fin h) :
    sqGen h (sqHandleIdxU j) ∈ gAbsTripleTest h nu' := by
  have hgen : sqGen h (sqHandleIdxU j)
      = zpowZtwo (isProP_DSq h) (sqPivot h) (toAdd (nu' (sqGen h (sqHandleIdxU j))))
        * sqEichU h nu' j := by
    rw [sqEichU, mul_inv_cancel_left]
  rw [hgen]
  refine Subgroup.mul_mem _ (gAbs_tripleTest_pivotZpow _) ?_
  show commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (sqEichU h nu' j))) (gBaseT h)
    ∈ gAbsWide h nu'
  exact Subgroup.mem_sup_left (gAbs_eichU_triple_mem hsigma hx0 j)

theorem gAbs_tripleTest_handleV (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (j : Fin h) :
    sqGen h (sqHandleIdxV j) ∈ gAbsTripleTest h nu' := by
  have hgen : sqGen h (sqHandleIdxV j)
      = sqEichV h nu' j
        * zpowZtwo (isProP_DSq h) (sqPivot h) (toAdd (nu' (sqGen h (sqHandleIdxV j)))) := by
    rw [sqEichV, inv_mul_cancel_right]
  rw [hgen]
  refine Subgroup.mul_mem _ ?_ (gAbs_tripleTest_pivotZpow _)
  show commP (commP (gBaseT h) (levelMk (DSq h : Type) 4 (sqEichV h nu' j))) (gBaseT h)
    ∈ gAbsWide h nu'
  exact Subgroup.mem_sup_left (gAbs_eichV_triple_mem hsigma hx0 j)

/-- ⭐⭐⭐ **The whole `x₁`-slot triple family lands in the widened reach**: wave 76's residual
`GBaseXOneTriple`, satisfied by `gAbsWide` unconditionally at every slot `c`. -/
theorem gAbs_triple_xOne_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (c : levelQuot (DSq h : Type) 4) :
    commP (commP (gBaseT h) c) (gBaseT h) ∈ gAbsWide h nu' := by
  obtain ⟨q, rfl⟩ := levelMk_surjective (DSq h : Type) 4 c
  have hsub : (Subgroup.closure (Set.range (sqGen h))).topologicalClosure
      ≤ gAbsTripleTest h nu' := by
    refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_)
      gAbs_tripleTest_closed
    rintro _ ⟨i, rfl⟩
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact gAbs_tripleTest_sigma
    · exact gAbs_tripleTest_x0
    · exact gAbs_tripleTest_xOne
    · exact gAbs_tripleTest_handleU hsigma hx0 j
    · exact gAbs_tripleTest_handleV hsigma hx0 j
  have hq : q ∈ (Subgroup.closure (Set.range (sqGen h))).topologicalClosure := by
    rw [dsq_topGen h]
    trivial
  exact hsub hq

end Wide

/-! ## §5 The wide chain: the full layer lands in the widened full reach

Wave 76's §§3-4 chain (`gBase_triple` through `gBase_layerReach_of_xOneTriple`) re-run with
the widened reach in place of the reach, and the unconditional §4 family in place of the
refuted hypothesis `GBaseXOneTriple`. -/

section WideChain

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- The `x₁`-outer triples at arbitrary inner pairs land in the widened reach. -/
theorem gAbs_triple_xOne_pair_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (p q : levelQuot (DSq h : Type) 4) :
    commP (commP p q) (gBaseT h) ∈ gAbsWide h nu' := by
  have hleft : p ∈ gBaseTripleLeft (DSq h : Type) (gAbsWide h nu') (gBaseT h) := by
    refine gBase_letters_mem (fun i => ?_) p
    intro q'
    refine gBase_letters_mem (K := gBaseTripleRight (DSq h : Type) (gAbsWide h nu')
      (levelMk (DSq h : Type) 4 (sqGen h i)) (gBaseT h)) (fun i' => ?_) q'
    show commP (commP (levelMk (DSq h : Type) 4 (sqGen h i))
      (levelMk (DSq h : Type) 4 (sqGen h i'))) (gBaseT h) ∈ gAbsWide h nu'
    by_cases hi : i = 2
    · subst hi
      exact gAbs_triple_xOne_wide hsigma hx0 _
    · by_cases hi' : i' = 2
      · subst hi'
        rw [gBase_commP_swap (levelMk (DSq h : Type) 4 (sqGen h i)),
          gThreeFour_ad_inv_left (cfour_commP_mem_lambdaTwo _ _)]
        exact gAbs_triple_xOne_wide hsigma hx0 _
      · exact Subgroup.mem_sup_left (gBase_jacobi_xOne (gTower_letters_mem_far i hi)
          (gTower_letters_mem_far i' hi'))
  exact hleft q

/-- A triple bracket of letters against the outer letter slot, packaged. -/
theorem gAbs_letter_triple_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (a b : (DSq h : Type)) (i : Fin (sqRank h)) :
    levelMk (DSq h : Type) 4 (commP (commP a b) (sqGen h i)) ∈ gAbsWide h nu' := by
  by_cases hi : i = 2
  · subst hi
    rw [gBase_levelMk_triple]
    exact gAbs_triple_xOne_pair_wide hsigma hx0 _ _
  · exact Subgroup.mem_sup_left (gBase_knob_mem (gTower_letters_mem_far i hi))

/-- ⭐⭐ **Every triple bracket lands in the widened reach.** -/
theorem gAbs_triple_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (p q r : levelQuot (DSq h : Type) 4) :
    commP (commP p q) r ∈ gAbsWide h nu' := by
  obtain ⟨a, rfl⟩ := levelMk_surjective (DSq h : Type) 4 p
  obtain ⟨b, rfl⟩ := levelMk_surjective (DSq h : Type) 4 q
  obtain ⟨g, rfl⟩ := levelMk_surjective (DSq h : Type) 4 r
  rw [← gBase_levelMk_triple]
  have hspan := gTower_commHom_span (h := h) (k := 2) (cfour_commP_mem_two a b) g
  refine Subgroup.closure_le (K := gAbsWide h nu') |>.2 ?_ hspan
  rintro _ ⟨i, rfl⟩
  exact gAbs_letter_triple_wide hsigma hx0 a b i

/-- ⭐⭐ **Every bracket square lands in the widened reach.** -/
theorem gAbs_bracketSq_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (p q : levelQuot (DSq h : Type) 4) :
    commP p q ^ 2 ∈ gAbsWide h nu' := by
  obtain ⟨a, rfl⟩ := levelMk_surjective (DSq h : Type) 4 p
  obtain ⟨b, rfl⟩ := levelMk_surjective (DSq h : Type) 4 q
  have hbundle := gBase_bundle_mem (nu' := nu') a b
  rw [map_mul, map_pow, gBase_levelMk_triple] at hbundle
  have hsplit : commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b) ^ 2 =
      (levelMk (DSq h : Type) 4 (commP a b) ^ 2 *
        commP (commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b))
          (levelMk (DSq h : Type) 4 (dsqX1 h))) *
      (commP (commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 b))
          (levelMk (DSq h : Type) 4 (dsqX1 h)))⁻¹ := by
    rw [mul_inv_cancel_right]
    simp only [commP, map_mul, map_inv]
  rw [hsplit]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbundle)
    (Subgroup.inv_mem _ (gAbs_triple_wide hsigma hx0 _ _ _))

variable (h nu') in
/-- The `Y`-elements whose bracket against `x₁` lands in the widened reach. -/
noncomputable def gAbsXOneTest : Subgroup (levelQuot (DSq h : Type) 4) where
  carrier := {y | y ∈ lambdaImage (DSq h : Type) 2 4 ∧
    commP y (gBaseT h) ∈ gAbsWide h nu'}
  one_mem' := ⟨Subgroup.one_mem _, by rw [cfour_one_comm]; exact Subgroup.one_mem _⟩
  mul_mem' := fun {_ _} hy hy' => ⟨Subgroup.mul_mem _ hy.1 hy'.1, by
    rw [gThreeFour_ad_left hy.1]; exact Subgroup.mul_mem _ hy.2 hy'.2⟩
  inv_mem' := fun {_} hy => ⟨Subgroup.inv_mem _ hy.1, by
    rw [gThreeFour_ad_inv_left hy.1]; exact hy.2⟩

/-- ⭐⭐ **The `x₁`-bracket of any `γ₂`-element lands in the widened reach.** -/
theorem gAbs_comm_xOne_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {v : (DSq h : Type)}
    (hv : v ∈ twoCentralSeries (DSq h : Type) 2) :
    levelMk (DSq h : Type) 4 (commP v (dsqX1 h)) ∈ gAbsWide h nu' := by
  haveI : DiscreteTopology (levelQuot (DSq h : Type) 4) := gTower_discrete 4
  have hpre : IsClosed ((Subgroup.comap (levelMk (DSq h : Type) 4) (gAbsXOneTest h nu') :
      Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    rw [Subgroup.coe_comap]
    exact (isClosed_discrete _).preimage (continuous_levelMk (DSq h : Type) 4)
  have hsub : twoCentralSeries (DSq h : Type) 2 ≤
      Subgroup.comap (levelMk (DSq h : Type) 4) (gAbsXOneTest h nu') := by
    rw [cfour_lambda_two, twoCentralSucc]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hpre
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, -, rfl⟩
      refine ⟨?_, ?_⟩
      · show levelMk (DSq h : Type) 4 (g ^ 2) ∈ lambdaImage (DSq h : Type) 2 4
        rw [map_pow]
        exact cfour_sq_mem_lambdaTwo _
      · show commP (levelMk (DSq h : Type) 4 (g ^ 2)) (gBaseT h) ∈ gAbsWide h nu'
        rw [map_pow, gThreeFour_commP_sq_left]
        exact Subgroup.mul_mem _ (gAbs_bracketSq_wide hsigma hx0 _ _)
          (gAbs_triple_wide hsigma hx0 _ _ _)
    · refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · show levelMk (DSq h : Type) 4 (a * b * a⁻¹ * b⁻¹) ∈ lambdaImage (DSq h : Type) 2 4
        rw [gThreeFour_levelMk_commutator]
        exact cfour_commP_mem_lambdaTwo _ _
      · show commP (levelMk (DSq h : Type) 4 (a * b * a⁻¹ * b⁻¹)) (gBaseT h)
          ∈ gAbsWide h nu'
        rw [gThreeFour_levelMk_commutator]
        exact gAbs_triple_wide hsigma hx0 _ _ _
  rw [gBase_levelMk_commP]
  exact (hsub hv).2

variable (h) in
/-- **The widened full reach**: the widened reach with the two complement towers. -/
noncomputable def gAbsWideFull
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    Subgroup (levelQuot (DSq h : Type) 4) :=
  gAbsWide h nu' ⊔ gTowerTowXW h 2

theorem gAbs_wide_le_wideFull : gAbsWide h nu' ≤ gAbsWideFull h nu' := le_sup_left

/-- The widened full reach is the full reach with the coker adjoined. -/
theorem gAbs_wideFull_eq :
    gAbsWideFull h nu' = gTowerFullReach h nu' 2 ⊔ gAbsCoker h := by
  rw [gAbsWideFull, gAbsWide, gTowerFullReach, sup_right_comm]

/-- The square of any `γ₂`-element lands in the widened full reach. -/
theorem gAbs_sq_gammaTwo_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {v : (DSq h : Type)}
    (hv : v ∈ twoCentralSeries (DSq h : Type) 2) :
    levelMk (DSq h : Type) 4 (v ^ 2) ∈ gAbsWideFull h nu' := by
  obtain ⟨d, hdmem, hdl, hdn, hdec⟩ := gTower_decomp nu' hsigma hx0 (by omega) hv
  set a := toAdd (nuLam h v) with ha
  set b := toAdd (nu' v) with hb
  have hda : (2 ^ (2 - 1) : ℤ_[2]) ∣ a := gTower_row_dvd (nuLam h) hv
  have hdb : (2 ^ (2 - 1) : ℤ_[2]) ∣ b := gTower_row_dvd nu' hv
  have hxa : zpowZtwo (isProP_DSq h) (dsqX0 h) a ∈ twoCentralSeries (DSq h : Type) 2 :=
    gTower_zpow_dvd_mem (by omega) hda _
  have hwb : zpowZtwo (isProP_DSq h) (sqPivot h) b ∈ twoCentralSeries (DSq h : Type) 2 :=
    gTower_zpow_dvd_mem (by omega) hdb _
  have htow : gTowerTower h a b ∈ twoCentralSeries (DSq h : Type) 2 :=
    Subgroup.mul_mem _ hxa hwb
  rw [hdec, gTower_sq_congr (le_refl 2) hdmem htow]
  refine Subgroup.mul_mem _ ?_ ?_
  · have hbundle : levelMk (DSq h : Type) 4 (d ^ 2 * commP d (dsqX1 h))
        ∈ gTowerReach h nu' 2 :=
      Subgroup.subset_closure (Or.inl (Or.inr ⟨d, ⟨hdmem, hdl, hdn⟩, rfl⟩))
    have hsplit : levelMk (DSq h : Type) 4 (d ^ 2)
        = levelMk (DSq h : Type) 4 (d ^ 2 * commP d (dsqX1 h)) *
          (levelMk (DSq h : Type) 4 (commP d (dsqX1 h)))⁻¹ := by
      rw [map_mul, mul_inv_cancel_right]
    rw [hsplit]
    exact gAbs_wide_le_wideFull (Subgroup.mul_mem _ (gAbs_reach_le_wide hbundle)
      (Subgroup.inv_mem _ (gAbs_comm_xOne_wide hsigma hx0 hdmem)))
  · rw [gTowerTower, gTower_sq_congr (le_refl 2) hxa hwb, gTower_zpow_sq, gTower_zpow_sq,
      ← map_mul]
    refine le_sup_right (α := Subgroup _) ?_
    refine Subgroup.subset_closure ⟨2 * a, 2 * b, ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hda
      exact ⟨c, by rw [hc]; ring⟩
    · obtain ⟨c, hc⟩ := hdb
      exact ⟨c, by rw [hc]; ring⟩
    · rw [gTowerTower]

/-- Every fourth power lands in the widened full reach. -/
theorem gAbs_pow_four_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (p : levelQuot (DSq h : Type) 4) :
    p ^ 4 ∈ gAbsWideFull h nu' := by
  obtain ⟨v, hv, hveq⟩ := cfour_sq_mem_lambdaTwo p
  have hfour : p ^ 4 = (p ^ 2) ^ 2 := by rw [← pow_mul]
  rw [hfour, ← hveq, ← map_pow]
  exact gAbs_sq_gammaTwo_wide hsigma hx0 hv

/-- ⭐⭐⭐ **The whole layer lands in the widened full reach**, unconditionally. -/
theorem gAbs_zLayer_le_wideFull (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    zLayer (DSq h : Type) 3 ≤ gAbsWideFull h nu' :=
  cfourCmp_zLayer_le_gens (gAbs_pow_four_wide hsigma hx0)
    (fun p q => gAbs_wide_le_wideFull (gAbs_bracketSq_wide hsigma hx0 p q))
    (fun p q r => gAbs_wide_le_wideFull (gAbs_triple_wide hsigma hx0 p q r))

end WideChain

/-! ## §6 The cut, the wide layer statement, and the leftover normal form (T1)

The realization of the widened full reach factors through wave 74's own
`gTower_fullReach_realize`: the coker is central, so its contribution moves into the
row-trivial part.  The cut is then verbatim wave 74's, and the result is the depth-2 layer
statement for the widened reach, with the two-class coker carrying explicit `𝔽₂`-exponents:
Labute's Theorem 5 leftover decomposition at level 2, in the campaign's vocabulary. -/

section Cut

open scoped Pointwise

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- The realization of the widened full reach: a row-trivial `γ₃`-element whose class lies in
the widened reach, times a two-tower image with `4`-divisible exponents. -/
theorem gAbs_wideFull_realize (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {z : levelQuot (DSq h : Type) 4}
    (hz : z ∈ gAbsWideFull h nu') :
    ∃ r A B, r ∈ twoCentralSeries (DSq h : Type) 3 ∧ nuLam h r = 1 ∧ nu' r = 1 ∧
      levelMk (DSq h : Type) 4 r ∈ gAbsWide h nu' ∧
        (2 ^ 2 : ℤ_[2]) ∣ A ∧ (2 ^ 2 : ℤ_[2]) ∣ B ∧
          z = levelMk (DSq h : Type) 4 r * levelMk (DSq h : Type) 4 (gTowerTower h A B) := by
  rw [gAbs_wideFull_eq] at hz
  haveI := gAbs_coker_normal (h := h)
  have hmem : z ∈ ((gTowerFullReach h nu' 2 : Subgroup (levelQuot (DSq h : Type) 4)) :
      Set (levelQuot (DSq h : Type) 4)) *
      ((gAbsCoker h : Subgroup (levelQuot (DSq h : Type) 4)) :
        Set (levelQuot (DSq h : Type) 4)) := by
    rw [← Subgroup.mul_normal]
    exact hz
  obtain ⟨f, hf, n, hn, heq⟩ := hmem
  obtain ⟨r, A, B, hrm, hrl, hrn, hrR, hA, hB, hfeq⟩ := gTower_fullReach_realize hsigma hx0 hf
  obtain ⟨e₁, e₂, he₁, he₂, hneq⟩ := gAbs_coker_form hn
  have hBl : nuLam h (gAbsB h) = 1 := gTower_row_commP _ _ _
  have hBn : nu' (gAbsB h) = 1 := gTower_row_commP _ _ _
  have hCl : nuLam h (gAbsC h) = 1 := gTower_row_commP _ _ _
  have hCn : nu' (gAbsC h) = 1 := gTower_row_commP _ _ _
  refine ⟨r * gAbsB h ^ e₁ * gAbsC h ^ e₂, A, B, ?_, ?_, ?_, ?_, hA, hB, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hrm
      (Subgroup.pow_mem _ gAbs_B_mem_three e₁)) (Subgroup.pow_mem _ gAbs_C_mem_three e₂)
  · rw [map_mul, map_mul, map_pow, map_pow, hrl, hBl, hCl, one_pow, one_pow, one_mul,
      one_mul]
  · rw [map_mul, map_mul, map_pow, map_pow, hrn, hBn, hCn, one_pow, one_pow, one_mul,
      one_mul]
  · have hBcMem : levelMk (DSq h : Type) 4 (gAbsB h) ∈ gAbsCoker h :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hCcMem : levelMk (DSq h : Type) 4 (gAbsC h) ∈ gAbsCoker h :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rw [map_mul, map_mul, map_pow, map_pow]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (gAbs_reach_le_wide hrR) ?_) ?_
    · exact Subgroup.mem_sup_right ((gAbsCoker h).pow_mem hBcMem e₁)
    · exact Subgroup.mem_sup_right ((gAbsCoker h).pow_mem hCcMem e₂)
  · have hcen : ∀ g : levelQuot (DSq h : Type) 4, g * n = n * g :=
      fun g => Subgroup.mem_center_iff.1 (gAbs_coker_central hn) g
    calc z = f * n := heq.symm
      _ = levelMk (DSq h : Type) 4 r * levelMk (DSq h : Type) 4 (gTowerTower h A B) * n := by
          rw [hfeq]
      _ = levelMk (DSq h : Type) 4 r *
          (levelMk (DSq h : Type) 4 (gTowerTower h A B) * n) := by rw [mul_assoc]
      _ = levelMk (DSq h : Type) 4 r *
          (n * levelMk (DSq h : Type) 4 (gTowerTower h A B)) := by rw [hcen]
      _ = levelMk (DSq h : Type) 4 r * n * levelMk (DSq h : Type) 4 (gTowerTower h A B) := by
          rw [mul_assoc]
      _ = levelMk (DSq h : Type) 4 (r * gAbsB h ^ e₁ * gAbsC h ^ e₂) *
          levelMk (DSq h : Type) 4 (gTowerTower h A B) := by
          rw [hneq, map_mul, map_mul, map_pow, map_pow]
          simp only [mul_assoc]

/-- ⭐⭐ **The cut for the widened reach**: an exactly row-trivial element whose class lies in
the widened full reach already lies in the widened reach.  Verbatim wave 74's `gTower_cut`
at depth `2`, over the widened realization. -/
theorem gAbs_wide_cut (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)} (hgl : nuLam h g = 1)
    (hgn : nu' g = 1)
    (hfull : levelMk (DSq h : Type) 4 g ∈ gAbsWideFull h nu') :
    levelMk (DSq h : Type) 4 g ∈ gAbsWide h nu' := by
  obtain ⟨r, A, B, hrmem, hrl, hrn, hrW, hA, hB, heq⟩ :=
    gAbs_wideFull_realize hsigma hx0 hfull
  have hAmem : zpowZtwo (isProP_DSq h) (dsqX0 h) A ∈ twoCentralSeries (DSq h : Type) 3 :=
    gTower_zpow_dvd_mem (by omega) (by simpa using hA) _
  have hBmem : zpowZtwo (isProP_DSq h) (sqPivot h) B ∈ twoCentralSeries (DSq h : Type) 3 :=
    gTower_zpow_dvd_mem (by omega) (by simpa using hB) _
  have htmem : gTowerTower h A B ∈ twoCentralSeries (DSq h : Type) 3 :=
    Subgroup.mul_mem _ hAmem hBmem
  set u := (r * gTowerTower h A B)⁻¹ * g with hu
  have humem : u ∈ twoCentralSeries (DSq h : Type) 4 := by
    rw [lim_mem_twoCentralSeries_iff_levelMk]
    show levelMk (DSq h : Type) 4 ((r * gTowerTower h A B)⁻¹ * g) = 1
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
  have hAdeep : (2 ^ 3 : ℤ_[2]) ∣ A := by
    have hud := gTower_row_dvd (nuLam h) humem
    rw [show (4 : ℕ) - 1 = 3 from rfl] at hud
    have hAeq : A = -toAdd (nuLam h u) := by
      have h0 := hrowA
      rw [hgl, toAdd_one] at h0
      exact eq_neg_of_add_eq_zero_left h0.symm
    rw [hAeq]
    exact hud.neg_right
  have hBdeep : (2 ^ 3 : ℤ_[2]) ∣ B := by
    have hud := gTower_row_dvd nu' humem
    rw [show (4 : ℕ) - 1 = 3 from rfl] at hud
    have hBeq : B = -toAdd (nu' u) := by
      have h0 := hrowB
      rw [hgn, toAdd_one] at h0
      exact eq_neg_of_add_eq_zero_left h0.symm
    rw [hBeq]
    exact hud.neg_right
  have htdeep : gTowerTower h A B ∈ twoCentralSeries (DSq h : Type) 4 :=
    gTower_tower_mem (by omega)
      (by rw [show (4 : ℕ) - 1 = 3 from rfl]; exact hAdeep)
      (by rw [show (4 : ℕ) - 1 = 3 from rfl]; exact hBdeep)
  have htimg : levelMk (DSq h : Type) 4 (gTowerTower h A B) = 1 :=
    (lim_mem_twoCentralSeries_iff_levelMk 4 _).mp htdeep
  rw [heq, htimg, mul_one]
  exact hrW

/-- ⭐⭐⭐ **The wide layer statement at depth 2**: every exactly row-trivial `γ₃`-element
reaches the widened span, unconditionally.  This is the refuted `GTowerLayerReach h ν' 2`
with the two-class coker adjoined: the exact unconditional content of the depth-2 base. -/
theorem gAbs_layer_wide (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)}
    (hg : g ∈ twoCentralSeries (DSq h : Type) 3) (hgl : nuLam h g = 1) (hgn : nu' g = 1) :
    levelMk (DSq h : Type) 4 g ∈ gAbsWide h nu' := by
  refine gAbs_wide_cut hsigma hx0 hgl hgn ?_
  exact gAbs_zLayer_le_wideFull hsigma hx0 ⟨g, hg, rfl⟩

/-- ⭐⭐⭐ **T1: the leftover normal form.**  Every exactly row-trivial `γ₃`-element is an
element whose class lies in the admissible depth-2 reach, times the two coker classes with
explicit `𝔽₂`-exponents.  Labute's Theorem 5 leftover decomposition at level 2. -/
theorem gAbs_leftover_decomp (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)}
    (hg : g ∈ twoCentralSeries (DSq h : Type) 3) (hgl : nuLam h g = 1) (hgn : nu' g = 1) :
    ∃ p e₁ e₂, p ∈ twoCentralSeries (DSq h : Type) 3 ∧
      levelMk (DSq h : Type) 4 p ∈ gTowerReach h nu' 2 ∧ e₁ ≤ 1 ∧ e₂ ≤ 1 ∧
        g = p * gAbsB h ^ e₁ * gAbsC h ^ e₂ := by
  have hw := gAbs_layer_wide hsigma hx0 hg hgl hgn
  haveI := gAbs_coker_normal (h := h)
  have hmem : levelMk (DSq h : Type) 4 g ∈
      ((gTowerReach h nu' 2 : Subgroup (levelQuot (DSq h : Type) 4)) :
        Set (levelQuot (DSq h : Type) 4)) *
      ((gAbsCoker h : Subgroup (levelQuot (DSq h : Type) 4)) :
        Set (levelQuot (DSq h : Type) 4)) := by
    rw [← Subgroup.mul_normal]
    exact hw
  obtain ⟨ρ, hρ, n, hn, heq⟩ := hmem
  obtain ⟨e₁, e₂, he₁, he₂, hneq⟩ := gAbs_coker_form hn
  refine ⟨g * (gAbsB h ^ e₁ * gAbsC h ^ e₂)⁻¹, e₁, e₂, ?_, ?_, he₁, he₂, by group⟩
  · exact Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ gAbs_B_mem_three e₁) (Subgroup.pow_mem _ gAbs_C_mem_three e₂)))
  · have himg : levelMk (DSq h : Type) 4 (g * (gAbsB h ^ e₁ * gAbsC h ^ e₂)⁻¹) = ρ := by
      rw [map_mul, map_inv, map_mul, map_pow, map_pow, ← hneq, ← heq, mul_inv_cancel_right]
    rw [himg]
    exact hρ

end Cut

/-! ## §7 T2: the coefficient kill

The defect of a `χ`-trivial admissible dressing reads zero at every row
(`gDeltaDefectVanishing`, proved in wave 74).  Against the normal form of §6 the two
corrected rows then read the two `𝔽₂`-coefficients directly: the reach part is
`8`-divisible (§2), each coker class reads `4·unit` at its own row (§3), so both exponents
vanish and the defect class lies in the admissible reach.  This is Labute's Theorem 5
constraint `0 = Δᵢ(ε_j) = aᵢπ^j`, at the two coordinates his printed argument does not
spell out. -/

section Kill

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- Units do not absorb powers of two. -/
theorem gAbs_unit_mul_dvd {w : ℤ_[2]ˣ} {t : ℤ_[2]}
    (hd : (2 : ℤ_[2]) ^ 3 ∣ (w : ℤ_[2]) * t) : (2 : ℤ_[2]) ^ 3 ∣ t := by
  obtain ⟨s, hs⟩ := hd
  have hcanc : ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (w : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * s, ?_⟩
  linear_combination ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hs - t * hcanc

/-- A `4·unit` value is not `8`-divisible. -/
theorem gAbs_four_unit_not_dvd {t : ℤ_[2]} {u : ℤ_[2]ˣ} (ht : t = 2 ^ 2 * (u : ℤ_[2])) :
    ¬ (2 : ℤ_[2]) ^ 3 ∣ t := by
  intro hdvd
  obtain ⟨s, hs⟩ := hdvd
  rw [ht] at hs
  refine gDelta_not_two_dvd_unit u ⟨s, ?_⟩
  have h4 : ((2 : ℤ_[2]) ^ 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine mul_left_cancel₀ h4 ?_
  linear_combination hs

/-- **The middle-exponent kill**: if the head reads `8`-divisibly, the middle base reads
`4·unit`, the tail base reads zero, and the whole product reads zero, the middle
`𝔽₂`-exponent vanishes. -/
theorem gAbs_kill_mid {p x y : (DSq h : Type)} {c : Fin (sqRank h) → ℤ_[2]} {e f : ℕ}
    (he : e ≤ 1) (h8p : (2 : ℤ_[2]) ^ 3 ∣ gDelta h c p)
    (hx4 : ∃ u : ℤ_[2]ˣ, gDelta h c x = 2 ^ 2 * (u : ℤ_[2]))
    (hy0 : gDelta h c y = 0) (hchiX : chiSq h x = 1) (hchiY : chiSq h y = 1)
    (hzero : gDelta h c (p * x ^ e * y ^ f) = 0) : e = 0 := by
  rw [gDelta_mul, gDelta_mul, gDelta_pow, gDelta_pow, hchiX, hchiY, hy0, mul_zero, mul_zero,
    add_zero, Units.val_one, normSum_one_base] at hzero
  match e, he with
  | 0, _ => rfl
  | 1, _ =>
    exfalso
    have h8 : (2 : ℤ_[2]) ^ 3 ∣ ((chiSq h p : ℤ_[2]ˣ) : ℤ_[2]) * gDelta h c x := by
      have hneg : ((chiSq h p : ℤ_[2]ˣ) : ℤ_[2]) * gDelta h c x = -gDelta h c p := by
        push_cast at hzero
        linear_combination hzero
      rw [hneg]
      exact h8p.neg_right
    obtain ⟨u, hu⟩ := hx4
    exact gAbs_four_unit_not_dvd hu (gAbs_unit_mul_dvd h8)

/-- **The tail-exponent kill**: same reading pattern with the roles of the two bases
swapped. -/
theorem gAbs_kill_last {p x y : (DSq h : Type)} {c : Fin (sqRank h) → ℤ_[2]} {e f : ℕ}
    (hf : f ≤ 1) (h8p : (2 : ℤ_[2]) ^ 3 ∣ gDelta h c p)
    (hx0 : gDelta h c x = 0)
    (hy4 : ∃ u : ℤ_[2]ˣ, gDelta h c y = 2 ^ 2 * (u : ℤ_[2]))
    (hchiX : chiSq h x = 1) (hchiY : chiSq h y = 1)
    (hzero : gDelta h c (p * x ^ e * y ^ f) = 0) : f = 0 := by
  rw [gDelta_mul, gDelta_mul, gDelta_pow, gDelta_pow, hchiX, hchiY, hx0, mul_zero, mul_zero,
    add_zero, Units.val_one, normSum_one_base, map_mul, map_pow, hchiX, one_pow, mul_one]
    at hzero
  match f, hf with
  | 0, _ => rfl
  | 1, _ =>
    exfalso
    have h8 : (2 : ℤ_[2]) ^ 3 ∣ ((chiSq h p : ℤ_[2]ˣ) : ℤ_[2]) * gDelta h c y := by
      have hneg : ((chiSq h p : ℤ_[2]ˣ) : ℤ_[2]) * gDelta h c y = -gDelta h c p := by
        push_cast at hzero
        linear_combination hzero
      rw [hneg]
      exact h8p.neg_right
    obtain ⟨u, hu⟩ := hy4
    exact gAbs_four_unit_not_dvd hu (gAbs_unit_mul_dvd h8)

/-- ⭐⭐⭐ **T2: the coefficient kill.**  An exactly row-trivial `γ₃`-element all of whose
functional readings vanish has zero coker coefficients: its class lies in the admissible
depth-2 reach.  The refuted layer statement is recovered for the all-rows-zero elements,
which is all Labute's Theorem 5 ever needs of it. -/
theorem gAbs_zero_reader_reach (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) {g : (DSq h : Type)}
    (hg : g ∈ twoCentralSeries (DSq h : Type) 3) (hgl : nuLam h g = 1) (hgn : nu' g = 1)
    (hzero : ∀ c : Fin (sqRank h) → ℤ_[2], gDelta h c g = 0) :
    levelMk (DSq h : Type) 4 g ∈ gTowerReach h nu' 2 := by
  obtain ⟨p, e₁, e₂, hpm, hpR, he₁, he₂, hgeq⟩ := gAbs_leftover_decomp hsigma hx0 hg hgl hgn
  have h8pS : (2 : ℤ_[2]) ^ 3 ∣ gDelta h (gAbsRowS h nu') p :=
    (gJoin_mem_layerDvd (c := gAbsRowS h nu') (k := 2) (x := p)).1
      (gAbs_reach_le_layerDvd_rowS hpR)
  have h8pX : (2 : ℤ_[2]) ^ 3 ∣ gDelta h (gAbsRowX h nu') p :=
    (gJoin_mem_layerDvd (c := gAbsRowX h nu') (k := 2) (x := p)).1
      (gAbs_reach_le_layerDvd_rowX hpR)
  have h0S := hzero (gAbsRowS h nu')
  rw [hgeq] at h0S
  have h0X := hzero (gAbsRowX h nu')
  rw [hgeq] at h0X
  have hBkill : e₁ = 0 :=
    gAbs_kill_mid he₁ h8pS gAbs_delta_B_rowS gAbs_delta_C_rowS gAbs_chiSq_B gAbs_chiSq_C h0S
  have hCkill : e₂ = 0 :=
    gAbs_kill_last he₂ h8pX gAbs_delta_B_rowX gAbs_delta_C_rowX gAbs_chiSq_B gAbs_chiSq_C h0X
  rw [hgeq, hBkill, hCkill, pow_zero, pow_zero, mul_one, mul_one]
  exact hpR

/-- ⭐⭐ **The wave-77 refutation, re-proved functionally**: the `σ`-coker class is outside
the depth-2 reach at every marking, because the reach reads `8`-divisibly at the corrected
`σ`-row while the class reads `4·unit`.  No finite witness group is needed, and no marking
selection: the corrected rows exist at every `ν'`.  (Wave 76's honesty marker "a functional
refutation is not available" computed the reading only at the `x₁`-row; the `σ`- and
`x₀`-rows see the classes at the layer bit.) -/
theorem gAbs_B_notMem_reach :
    levelMk (DSq h : Type) 4 (gAbsB h) ∉ gTowerReach h nu' 2 := by
  intro hmem
  obtain ⟨u, hu⟩ := gAbs_delta_B_rowS (h := h) (nu' := nu')
  exact gAbs_four_unit_not_dvd hu
    ((gJoin_mem_layerDvd (c := gAbsRowS h nu') (k := 2) (x := gAbsB h)).1
      (gAbs_reach_le_layerDvd_rowS hmem))

/-- The `x₀`-coker class is outside the depth-2 reach at every marking. -/
theorem gAbs_C_notMem_reach :
    levelMk (DSq h : Type) 4 (gAbsC h) ∉ gTowerReach h nu' 2 := by
  intro hmem
  obtain ⟨u, hu⟩ := gAbs_delta_C_rowX (h := h) (nu' := nu')
  exact gAbs_four_unit_not_dvd hu
    ((gJoin_mem_layerDvd (c := gAbsRowX h nu') (k := 2) (x := gAbsC h)).1
      (gAbs_reach_le_layerDvd_rowX hmem))

end Kill

/-! ## §8 T3: the repaired step and the re-seeded recursion

The `k = 2` instance of the defect-vanishing interface follows from T2 plus the depth-2
separation bookkeeping alone; with wave 74's extraction it yields the class-4 supply witness
that wave 77 identified as the missing seed.  The full interface then follows from the OPEN
depth-3 base (`GDecideBaseThree`, untouched by the `Q₁₆` refutation) plus separation, and
the committed recursion closes the residual from there. -/

section Reseed

variable {h : ℕ}

variable (h) in
/-- ⭐⭐⭐ **The repaired depth-2 vanishing**: the `k = 2` instance of
`GJoinDefectVanishing`, exactly the statement whose wave-75 derivation consumed the refuted
depth-2 base. -/
def GAbsVanishingTwo : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
    ∀ a : Fin (sqRank h) → (DSq h : Type),
      (∀ i, nuLam h (a i) = 1) → (∀ i, nu' (a i) = 1) → (∀ i, chiSq h (a i) = 1) →
      SqModTwoIndep (sqArbFrame h nu' j a) →
      sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) 3 →
      levelMk (DSq h : Type) 4 (sqRelWord (sqArbFrame h nu' j a))
        ∈ Subgroup.closure (gTowerKnobSet h nu' 2)

/-- ⭐⭐⭐ **The repaired vanishing holds, from depth-2 separation alone**: T1's normal form
plus T2's kill replace the refuted `GTowerLayerReach h ν' 2` outright. -/
theorem gAbs_vanishingTwo_of_sep
    (hsep : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      GJoinTowerSeparation h nu' 2) : GAbsVanishingTwo h := by
  intro nu' j hsigma hx0 a hal han hac hai hrel
  have hzero : ∀ c, gDelta h c (sqRelWord (sqArbFrame h nu' j a)) = 0 :=
    fun c => gJoin_reading_zero c nu' j ⟨hal, han, hac⟩
  have hreach := gAbs_zero_reader_reach hsigma hx0 hrel (gTower_frame_row_nuLam j hal)
    (gTower_frame_row_nu j hx0 han) hzero
  refine gJoin_reach_sep (k := 0) hx0 (hsep nu') hreach (fun jj => ?_) (fun jj => ?_)
  · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)
  · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)

/-- The handle-free case needs no input at all: the separation is vacuous at `h = 0`. -/
theorem gAbs_vanishingTwo_handleFree : GAbsVanishingTwo 0 :=
  gAbs_vanishingTwo_of_sep fun nu' => gJoin_towerSeparation_handleFree nu' 2

/-- ⭐⭐⭐ **The repaired class-3-to-4 clearing step**: wave 75's `gJoin_clear_step` at
`k = 2`, with the repaired vanishing in place of the refuted full-generation statement. -/
theorem gAbs_clear_step_two (HV : GAbsVanishingTwo h) (HR : GTowerKnobRealizable h)
    {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    {a : Fin (sqRank h) → (DSq h : Type)} (hal : ∀ i, nuLam h (a i) = 1)
    (han : ∀ i, nu' (a i) = 1) (hac : ∀ i, chiSq h (a i) = 1)
    (hai : SqModTwoIndep (sqArbFrame h nu' j a))
    (hrel : sqRelWord (sqArbFrame h nu' j a) ∈ twoCentralSeries (DSq h : Type) 3) :
    ∃ a' : Fin (sqRank h) → (DSq h : Type),
      (∀ i, nuLam h (a' i) = 1) ∧ (∀ i, nu' (a' i) = 1) ∧ (∀ i, chiSq h (a' i) = 1) ∧
        SqModTwoIndep (sqArbFrame h nu' j a') ∧
          sqRelWord (sqArbFrame h nu' j a') ∈ twoCentralSeries (DSq h : Type) 4 := by
  have hknob := HV nu' j hsigma hx0 a hal han hac hai hrel
  obtain ⟨d, hd, hdl, hdn, hrel'⟩ := HR nu' j hsigma hx0 2 (le_refl 2) a hal han hai hrel hknob
  refine ⟨fun i => a i * d i, ?_, ?_, ?_, ?_, hrel'⟩
  · intro i
    rw [map_mul, hal i, hdl i, one_mul]
  · intro i
    rw [map_mul, han i, hdn i, one_mul]
  · intro i
    exact gJoin_chiSq_mul_correction (hac i) (le_refl 2) (hd i) (hdl i)
  · rw [gTower_frame_mul]
    exact cfourId_modTwoIndep_mul hai
      (fun i => twoCentralSeries_antitone (G := (DSq h : Type)) (le_refl 2) (hd i))

/-- ⭐⭐⭐ **The class-4 supply witness**: exactly the seed wave 77 costed the depth-3 re-cut
at.  From the committed class-3 witness through the repaired step. -/
theorem gAbs_chiSupply_four (HV : GAbsVanishingTwo h) (HR : GTowerKnobRealizable h) :
    GJoinChiSupply h 4 := by
  intro nu' j hsigma hx0
  obtain ⟨a, hal, han, hac, hai, hrel⟩ := gJoin_chiSupply_three (h := h) nu' j hsigma hx0
  obtain ⟨a', h1, h2, h3, h4, h5⟩ := gAbs_clear_step_two HV HR hsigma hx0 hal han hac hai hrel
  exact ⟨a', h1, h2, h3, h4, h5⟩

theorem gAbs_supply_four (HV : GAbsVanishingTwo h) (HR : GTowerKnobRealizable h) :
    SqClassClearingSupply h 4 :=
  gJoin_supply_of_chiSupply (gAbs_chiSupply_four HV HR)

/-- ⭐⭐⭐ **The re-seeded vanishing interface**: `GJoinDefectVanishing h` from the OPEN
depth-3 base plus separation.  The `k = 2` instance is the absorption mechanism; the
`k ≥ 3` instances are the committed tower driven from depth 3. -/
theorem gAbs_defectVanishing_of_baseThree (H3 : GDecideBaseThree h)
    (hsep : GJoinSeparationAll h) : GJoinDefectVanishing h := by
  intro nu' j hsigma hx0 k hk a hal han hac hai hrel
  rcases eq_or_lt_of_le hk with rfl | hk3
  · exact gAbs_vanishingTwo_of_sep (fun nu'' => hsep nu'' 2 (le_refl 2)) nu' j hsigma hx0 a
      hal han hac hai hrel
  · have hlayer : GTowerLayerReach h nu' k :=
      gDecide_tower_of_baseThree H3 hsigma hx0 k (by omega)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have hzero : ∀ c, gDelta h c (sqRelWord (sqArbFrame h nu' j a)) = 0 :=
      fun c => gJoin_reading_zero c nu' j ⟨hal, han, hac⟩
    have hreach : levelMk (DSq h : Type) (k' + 2 + 2) (sqRelWord (sqArbFrame h nu' j a))
        ∈ gTowerReach h nu' (k' + 2) :=
      hlayer _ hrel (gTower_frame_row_nuLam j hal) (gTower_frame_row_nu j hx0 han)
    refine gJoin_reach_sep hx0 (hsep nu' (k' + 2) (by omega)) hreach
      (fun jj => ?_) (fun jj => ?_)
    · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)
    · exact gJoin_mem_layerDvd.2 (by rw [hzero]; exact dvd_zero _)

/-- ⭐⭐⭐ **The supply at every class, from the re-seeded route**: depth-3 base plus
separation plus extraction.  Wave 77's costing ("depth 3 alone does not restart the chain;
a class-four witness must be produced in addition") is discharged: the class-four seed now
comes from the absorption mechanism, at no cost beyond the separation already carried. -/
theorem gAbs_supply_of_baseThree (H3 : GDecideBaseThree h) (hsep : GJoinSeparationAll h)
    (HR : GTowerKnobRealizable h) : ∀ k, SqClassClearingSupply h k :=
  gJoin_supply_of_vanishing (gAbs_defectVanishing_of_baseThree H3 hsep) HR

/-- ⭐⭐⭐ **The `h ≥ 1` residual, from three named inputs**: the OPEN depth-3 base (in place
of the REFUTED depth-2 base), the separation bookkeeping, and the extraction interface.
Same three-input shape as wave 75's endpoint, with the refuted input replaced by an open
one. -/
theorem gAbs_markTransitivity_of_baseThree (H3 : GDecideBaseThree h)
    (hsep : GJoinSeparationAll h) (HR : GTowerKnobRealizable h) : SqLamMarkTransitivity h :=
  gJoin_markTransitivity_of_vanishing (gAbs_defectVanishing_of_baseThree H3 hsep) HR

end Reseed

/-! ## Axiom pins -/

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
#print axioms GQ2.Dyadic.SqCore.gAbsCoker
#print axioms GQ2.Dyadic.SqCore.gAbsWide
#print axioms gAbs_reach_le_wide
#print axioms gAbs_coker_central
#print axioms gAbs_coker_normal
#print axioms gAbs_B_img_sq
#print axioms gAbs_C_img_sq
#print axioms gAbs_pow_combine
#print axioms gAbs_coker_form
#print axioms gAbs_zpow_mem_of_closed
#print axioms gAbs_pivot_far
#print axioms gAbs_eichU_far
#print axioms gAbs_eichV_far
#print axioms gAbs_mem_one
#print axioms gAbs_eichU_sq_adm
#print axioms gAbs_eichV_sq_adm
#print axioms gAbs_eich_bracketSq_mem
#print axioms gAbs_eichU_four_mem
#print axioms gAbs_eichV_four_mem
#print axioms gAbs_eichU_triple_mem
#print axioms gAbs_eichV_triple_mem
#print axioms GQ2.Dyadic.SqCore.gAbsTripleTest
#print axioms gAbs_tripleTest_closed
#print axioms gAbs_tripleTest_sigma
#print axioms gAbs_tripleTest_x0
#print axioms gAbs_tripleTest_xOne
#print axioms gAbs_tripleTest_pivotZpow
#print axioms gAbs_tripleTest_handleU
#print axioms gAbs_tripleTest_handleV
#print axioms gAbs_triple_xOne_wide
#print axioms gAbs_triple_xOne_pair_wide
#print axioms gAbs_letter_triple_wide
#print axioms gAbs_triple_wide
#print axioms gAbs_bracketSq_wide
#print axioms GQ2.Dyadic.SqCore.gAbsXOneTest
#print axioms gAbs_comm_xOne_wide
#print axioms GQ2.Dyadic.SqCore.gAbsWideFull
#print axioms gAbs_wide_le_wideFull
#print axioms gAbs_wideFull_eq
#print axioms gAbs_sq_gammaTwo_wide
#print axioms gAbs_pow_four_wide
#print axioms gAbs_zLayer_le_wideFull
#print axioms gAbs_wideFull_realize
#print axioms gAbs_wide_cut
#print axioms gAbs_layer_wide
#print axioms gAbs_leftover_decomp
#print axioms gAbs_unit_mul_dvd
#print axioms gAbs_four_unit_not_dvd
#print axioms gAbs_kill_mid
#print axioms gAbs_kill_last
#print axioms gAbs_zero_reader_reach
#print axioms gAbs_B_notMem_reach
#print axioms gAbs_C_notMem_reach
#print axioms GQ2.Dyadic.SqCore.GAbsVanishingTwo
#print axioms gAbs_vanishingTwo_of_sep
#print axioms gAbs_vanishingTwo_handleFree
#print axioms gAbs_clear_step_two
#print axioms gAbs_chiSupply_four
#print axioms gAbs_supply_four
#print axioms gAbs_defectVanishing_of_baseThree
#print axioms gAbs_supply_of_baseThree
#print axioms gAbs_markTransitivity_of_baseThree

end AxiomPinsA

end SqCore

end Dyadic

end GQ2
