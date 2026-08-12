/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedClassFourDefect

/-!
# W73-KNOB: composing a handle correction with a core correction

Wave 72 left the class-four leftover of wave 68's frame at

```text
  sqRelWord (frame · cfourDefCorr) = cfourDefCore nu' j · ⁅y, A⁆
```

with `A = bridgeDress nu' j` and `y = ⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆`, and flagged that the tail
`⁅y, A⁆` is a knob **expression** and not yet a knob, the tree having no lemma that composes a
handle-slot correction with a core-slot correction.  This file supplies that lemma and cashes it.

Lane W73-KNOB.  New file; no edits to existing files.  Prefix `cfourCmp`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The composition lemma -/

section Compose

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐⭐⭐ **The five slots, corrected at once.**  Correcting the `σ`-, `x₀`- and `x₁`-slots by
`γ₂`-elements `c₀, c₁, c₂` and the two letters of the `j'`-th handle by `c_U, c_V`, all at the
same time, moves the class-four relator by the product of the five knobs of wave 70's inventory,
each read at the **undressed** frame.

This is the lemma wave 72's note asked for: `cfourId_dress_core` composes the three core slots,
and `cfourId_dress_handleU` / `cfourId_dress_handleV` move one handle slot with the core slots
held fixed, but nothing composed the two kinds.  The chaining is the argument
`cfourId_dress_core` already makes: every knob is a `Z`-element hence central, and the only cross
term is `commP c_U c_V`, which dies because `Y` is abelian in `Q₄`. -/
theorem cfourCmp_dress_all {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 4) (j' : Fin n)
    {c0 c1 c2 cU cV : levelQuot G 4} (hc0 : c0 ∈ lambdaImage G 2 4)
    (hc1 : c1 ∈ lambdaImage G 2 4) (hc2 : c2 ∈ lambdaImage G 2 4)
    (hcU : cU ∈ lambdaImage G 2 4) (hcV : cV ∈ lambdaImage G 2 4)
    (h0 : m' 0 = m 0 * c0) (h1 : m' 1 = m 1 * c1) (h2 : m' 2 = m 2 * c2)
    (hUj : m' (sqHandleIdxU j') = m (sqHandleIdxU j') * cU)
    (hVj : m' (sqHandleIdxV j') = m (sqHandleIdxV j') * cV)
    (hUne : ∀ i, i ≠ j' → m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hVne : ∀ i, i ≠ j' → m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m *
      (commP c0 (m 1) * commP (m 0) c1 * (c2 ^ 2 * commP c2 (m 2)) *
        (commP cU (m (sqHandleIdxV j')) * commP (m (sqHandleIdxU j')) cV)) := by
  classical
  obtain ⟨mA, hA0, hA1, hA2, hAU, hAV⟩ :
      ∃ mA : Fin (sqRank n) → levelQuot G 4,
        mA 0 = m 0 * c0 ∧ mA 1 = m 1 * c1 ∧ mA 2 = m 2 * c2 ∧
          (∀ i, mA (sqHandleIdxU i) = m (sqHandleIdxU i)) ∧
            (∀ i, mA (sqHandleIdxV i) = m (sqHandleIdxV i)) := by
    refine ⟨fun i => if (i : ℕ) = 0 then m 0 * c0 else if (i : ℕ) = 1 then m 1 * c1
      else if (i : ℕ) = 2 then m 2 * c2 else m i, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [sqVal_zero, if_pos]
    · simp only [sqVal_one]; norm_num
    · simp only [sqVal_two]; norm_num
    · intro i
      simp only [sqHandleIdxU_val]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · intro i
      simp only [sqHandleIdxV_val]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  obtain ⟨mB, hB0, hB1, hB2, hBUj, hBUne, hBV⟩ :
      ∃ mB : Fin (sqRank n) → levelQuot G 4,
        mB 0 = mA 0 ∧ mB 1 = mA 1 ∧ mB 2 = mA 2 ∧
          mB (sqHandleIdxU j') = mA (sqHandleIdxU j') * cU ∧
            (∀ i, i ≠ j' → mB (sqHandleIdxU i) = mA (sqHandleIdxU i)) ∧
              (∀ i, mB (sqHandleIdxV i) = mA (sqHandleIdxV i)) := by
    refine ⟨Function.update mA (sqHandleIdxU j') (mA (sqHandleIdxU j') * cU), ?_, ?_, ?_,
      Function.update_self _ _ _, ?_, ?_⟩
    · exact Function.update_of_ne (fun hc => by
        have := congrArg Fin.val hc
        rw [sqVal_zero, sqHandleIdxU_val] at this; omega) _ _
    · exact Function.update_of_ne (fun hc => by
        have := congrArg Fin.val hc
        rw [sqVal_one, sqHandleIdxU_val] at this; omega) _ _
    · exact Function.update_of_ne (fun hc => by
        have := congrArg Fin.val hc
        rw [sqVal_two, sqHandleIdxU_val] at this; omega) _ _
    · intro i hi
      refine Function.update_of_ne (fun hc => hi (Fin.val_injective ?_)) _ _
      have := congrArg Fin.val hc
      rw [sqHandleIdxU_val, sqHandleIdxU_val] at this
      omega
    · intro i
      refine Function.update_of_ne (fun hc => ?_) _ _
      have := congrArg Fin.val hc
      rw [sqHandleIdxV_val, sqHandleIdxU_val] at this
      omega
  have stepA := cfourId_dress_core m mA hc0 hc1 hc2 hA0 hA1 hA2 hAU hAV
  have stepB := cfourId_dress_handleU mA mB j' hcU hB0 hB1 hB2 hBUj hBUne hBV
  have stepC := cfourId_dress_handleV mB m' j' hcV (by rw [h0, ← hA0, ← hB0])
    (by rw [h1, ← hA1, ← hB1]) (by rw [h2, ← hA2, ← hB2])
    (by rw [hVj, ← hAV j', ← hBV j']) (fun i hi => by rw [hVne i hi, ← hAV i, ← hBV i])
    (fun i => by
      by_cases hi : i = j'
      · subst hi; rw [hUj, hBUj, hAU i]
      · rw [hUne i hi, hBUne i hi, hAU i])
  have hknobB : commP cU (mA (sqHandleIdxV j')) = commP cU (m (sqHandleIdxV j')) := by
    rw [hAV j']
  have hknobC : commP (mB (sqHandleIdxU j')) cV = commP (m (sqHandleIdxU j')) cV := by
    rw [hBUj, hAU j', cfourId_comm_dress_left _ _ hcU, cfour_commP_lambdaTwo hcU hcV, mul_one]
  rw [stepC, stepB, stepA, hknobB, hknobC]
  simp only [mul_assoc]

/-- ⭐⭐ **The two handle slots of one handle, corrected at once.**  The instance of
`cfourCmp_dress_all` with the three core slots left alone: the knob is
`⁅c_U, V_{j'}⁆ · ⁅U_{j'}, c_V⁆`, the two brackets of wave 70's handle inventory. -/
theorem cfourCmp_dress_handles {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 4) (j' : Fin n)
    {cU cV : levelQuot G 4} (hcU : cU ∈ lambdaImage G 2 4) (hcV : cV ∈ lambdaImage G 2 4)
    (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hUj : m' (sqHandleIdxU j') = m (sqHandleIdxU j') * cU)
    (hVj : m' (sqHandleIdxV j') = m (sqHandleIdxV j') * cV)
    (hUne : ∀ i, i ≠ j' → m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hVne : ∀ i, i ≠ j' → m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m *
      (commP cU (m (sqHandleIdxV j')) * commP (m (sqHandleIdxU j')) cV) := by
  have hstep := cfourCmp_dress_all m m' j' (Subgroup.one_mem _) (Subgroup.one_mem _)
    (Subgroup.one_mem _) hcU hcV (by rw [h0, mul_one]) (by rw [h1, mul_one])
    (by rw [h2, mul_one]) hUj hVj hUne hVne
  rw [hstep, cfour_one_comm, cfour_comm_one, one_pow, cfour_one_comm]
  simp only [one_mul, mul_one]

/-- Two copies of a `Z`-element bracketing a product annihilate. -/
theorem cfourCmp_z_pair {z : levelQuot G 4} (hz : z ∈ zLayer G 3) (p q : levelQuot G 4) :
    z * p * (q * z) = p * q := by
  rw [mul_assoc, cfourDef_z_push hz, cfourDef_z_push hz, cfourDef_z_sq hz, mul_one]

end Compose

/-! ## §2 The handle-pair correction as a tuple -/

section HandleCorr

variable {h : ℕ}

/-- **The handle-pair correction**: `a` on the `u_j`-slot, `b` on the `v_j`-slot, `1` on every
other slot of the frame. -/
noncomputable def cfourCmpHandleCorr (h : ℕ) (j : Fin h) (a b : (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) :=
  fun i => if i = sqHandleIdxU j then a else if i = sqHandleIdxV j then b else 1

variable (j : Fin h) (a b : (DSq h : Type))

@[simp] theorem cfourCmpHandleCorr_handleU :
    cfourCmpHandleCorr h j a b (sqHandleIdxU j) = a := by
  simp only [cfourCmpHandleCorr, if_pos]

@[simp] theorem cfourCmpHandleCorr_handleV :
    cfourCmpHandleCorr h j a b (sqHandleIdxV j) = b := by
  have hne : sqHandleIdxV j ≠ sqHandleIdxU j := fun hc => by
    have := congrArg Fin.val hc
    rw [sqHandleIdxV_val, sqHandleIdxU_val] at this
    omega
  simp only [cfourCmpHandleCorr, if_neg hne, if_pos]

theorem cfourCmpHandleCorr_handleU_ne {i : Fin h} (hi : i ≠ j) :
    cfourCmpHandleCorr h j a b (sqHandleIdxU i) = 1 := by
  have hU : sqHandleIdxU i ≠ sqHandleIdxU j := fun hc => hi (Fin.val_injective (by
    have := congrArg Fin.val hc
    rw [sqHandleIdxU_val, sqHandleIdxU_val] at this
    omega))
  have hV : sqHandleIdxU i ≠ sqHandleIdxV j := fun hc => by
    have := congrArg Fin.val hc
    rw [sqHandleIdxU_val, sqHandleIdxV_val] at this
    omega
  simp only [cfourCmpHandleCorr, if_neg hU, if_neg hV]

theorem cfourCmpHandleCorr_handleV_ne {i : Fin h} (hi : i ≠ j) :
    cfourCmpHandleCorr h j a b (sqHandleIdxV i) = 1 := by
  have hU : sqHandleIdxV i ≠ sqHandleIdxU j := fun hc => by
    have := congrArg Fin.val hc
    rw [sqHandleIdxV_val, sqHandleIdxU_val] at this
    omega
  have hV : sqHandleIdxV i ≠ sqHandleIdxV j := fun hc => hi (Fin.val_injective (by
    have := congrArg Fin.val hc
    rw [sqHandleIdxV_val, sqHandleIdxV_val] at this
    omega))
  simp only [cfourCmpHandleCorr, if_neg hU, if_neg hV]

@[simp] theorem cfourCmpHandleCorr_zero : cfourCmpHandleCorr h j a b 0 = 1 := by
  have hU : (0 : Fin (sqRank h)) ≠ sqHandleIdxU j := fun hc => by
    have := congrArg Fin.val hc
    rw [sqVal_zero, sqHandleIdxU_val] at this
    omega
  have hV : (0 : Fin (sqRank h)) ≠ sqHandleIdxV j := fun hc => by
    have := congrArg Fin.val hc
    rw [sqVal_zero, sqHandleIdxV_val] at this
    omega
  simp only [cfourCmpHandleCorr, if_neg hU, if_neg hV]

@[simp] theorem cfourCmpHandleCorr_one : cfourCmpHandleCorr h j a b 1 = 1 := by
  have hU : (1 : Fin (sqRank h)) ≠ sqHandleIdxU j := fun hc => by
    have := congrArg Fin.val hc
    rw [sqVal_one, sqHandleIdxU_val] at this
    omega
  have hV : (1 : Fin (sqRank h)) ≠ sqHandleIdxV j := fun hc => by
    have := congrArg Fin.val hc
    rw [sqVal_one, sqHandleIdxV_val] at this
    omega
  simp only [cfourCmpHandleCorr, if_neg hU, if_neg hV]

@[simp] theorem cfourCmpHandleCorr_two : cfourCmpHandleCorr h j a b 2 = 1 := by
  have hU : (2 : Fin (sqRank h)) ≠ sqHandleIdxU j := fun hc => by
    have := congrArg Fin.val hc
    rw [sqVal_two, sqHandleIdxU_val] at this
    omega
  have hV : (2 : Fin (sqRank h)) ≠ sqHandleIdxV j := fun hc => by
    have := congrArg Fin.val hc
    rw [sqVal_two, sqHandleIdxV_val] at this
    omega
  simp only [cfourCmpHandleCorr, if_neg hU, if_neg hV]

/-- **The handle-pair correction is admissible whenever its two entries are.** -/
theorem cfourCmpHandleCorr_admissible
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (ha : a ∈ twoCentralSeries (DSq h : Type) 2) (hal : nuLam h a = 1) (han : nu' a = 1)
    (hb : b ∈ twoCentralSeries (DSq h : Type) 2) (hbl : nuLam h b = 1) (hbn : nu' b = 1)
    (i : Fin (sqRank h)) :
    cfourCmpHandleCorr h j a b i ∈ twoCentralSeries (DSq h : Type) 2 ∧
      nuLam h (cfourCmpHandleCorr h j a b i) = 1 ∧ nu' (cfourCmpHandleCorr h j a b i) = 1 := by
  simp only [cfourCmpHandleCorr]
  split_ifs
  · exact ⟨ha, hal, han⟩
  · exact ⟨hb, hbl, hbn⟩
  · exact ⟨Subgroup.one_mem _, map_one _, map_one _⟩

/-- ⭐⭐ **The knob of a handle-pair correction, at an arbitrary frame.**  The instance of
`cfourCmp_dress_handles` the class-four application consumes: at any frame `F` the correction
`cfourCmpHandleCorr h j a b` moves the class-four relator by `⁅a, F(v_j)⁆ · ⁅F(u_j), b⁆`. -/
theorem cfourCmp_handle_knob (F : Fin (sqRank h) → (DSq h : Type))
    (ha : a ∈ twoCentralSeries (DSq h : Type) 2) (hb : b ∈ twoCentralSeries (DSq h : Type) 2) :
    sqRelWord (fun i => levelMk (DSq h : Type) 4 (F i * cfourCmpHandleCorr h j a b i))
      = sqRelWord (fun i => levelMk (DSq h : Type) 4 (F i)) *
        (commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 (F (sqHandleIdxV j))) *
          commP (levelMk (DSq h : Type) 4 (F (sqHandleIdxU j))) (levelMk (DSq h : Type) 4 b)) :=
  cfourCmp_dress_handles (fun i => levelMk (DSq h : Type) 4 (F i))
    (fun i => levelMk (DSq h : Type) 4 (F i * cfourCmpHandleCorr h j a b i)) j
    ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    (by simp only [cfourCmpHandleCorr_zero, mul_one])
    (by simp only [cfourCmpHandleCorr_one, mul_one])
    (by simp only [cfourCmpHandleCorr_two, mul_one])
    (by simp only [cfourCmpHandleCorr_handleU, map_mul])
    (by simp only [cfourCmpHandleCorr_handleV, map_mul])
    (fun i hi => by simp only [cfourCmpHandleCorr_handleU_ne j a b hi, mul_one])
    (fun i hi => by simp only [cfourCmpHandleCorr_handleV_ne j a b hi, mul_one])

end HandleCorr

/-! ## §3 The bracket against the dressing is a handle knob -/

section DressReach

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **A bracket against an even `ℤ₂`-power dies.** -/
theorem cfourCmp_comm_zpow_even {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) (g : (DSq h : Type)) {k : ℤ_[2]}
    (hk : (2 : ℤ_[2]) ∣ k) :
    commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) g k)) = 1 :=
  cfour_commP_lambdaTwo hy ⟨_, bridge_zpow_even g hk, rfl⟩

/-- **A bracket against an odd `ℤ₂`-power is the bracket against the base.** -/
theorem cfourCmp_comm_zpow_odd {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) (g : (DSq h : Type)) {k : ℤ_[2]}
    (hk : ¬ (2 : ℤ_[2]) ∣ k) :
    commP y (levelMk (DSq h : Type) 4 (zpowZtwo (isProP_DSq h) g k))
      = commP y (levelMk (DSq h : Type) 4 g) := by
  obtain ⟨u, hu, hug⟩ := bridge_zpow_odd_eq g hk
  rw [hug, map_mul, cfour_commP_right_hom hy, cfour_commP_lambdaTwo hy ⟨u, hu, rfl⟩, mul_one]

/-- **The bracket against the dressing, split into the two handle generators.**  The pivot factor
of `bridgeDress` has an even exponent, so it contributes nothing. -/
theorem cfourCmp_comm_dress_split {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) :
    commP y (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
      = commP y (levelMk (DSq h : Type) 4
            (zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxV j)) (bridgeRowU nu' j))) *
          commP y (levelMk (DSq h : Type) 4
            (zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxU j)) (bridgeRowV nu' j))) := by
  have hdvd : (2 : ℤ_[2]) ∣ -(2 * bridgeRowU nu' j * bridgeRowV nu' j) :=
    ⟨-(bridgeRowU nu' j * bridgeRowV nu' j), by ring⟩
  rw [bridgeDress, map_mul, map_mul, cfour_commP_right_hom hy,
    cfourCmp_comm_zpow_even hy _ hdvd, one_mul, cfour_commP_right_hom hy]

/-- **The bracket against the cleared `u`-letter.**  `U_j = w^{-ν'(u_j)}·u_j`. -/
theorem cfourCmp_comm_eichU {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) :
    commP y (levelMk (DSq h : Type) 4 (sqEichU h nu' j))
      = commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxU j))) *
          commP y (levelMk (DSq h : Type) 4
            (zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowU nu' j))) := by
  rw [sqEichU, map_mul, map_inv, cfour_commP_right_hom hy, cfourDef_comm_inv_right hy]
  rfl

/-- **The bracket against the cleared `v`-letter.**  `V_j = v_j·w^{-ν'(v_j)}`. -/
theorem cfourCmp_comm_eichV {y : levelQuot (DSq h : Type) 4}
    (hy : y ∈ lambdaImage (DSq h : Type) 2 4) :
    commP y (levelMk (DSq h : Type) 4 (sqEichV h nu' j))
      = commP y (levelMk (DSq h : Type) 4
            (zpowZtwo (isProP_DSq h) (sqPivot h) (bridgeRowV nu' j))) *
          commP y (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxV j))) := by
  rw [sqEichV, map_mul, map_inv, cfour_commP_right_hom hy, cfourDef_comm_inv_right hy]
  rfl

/-- ⭐⭐⭐ **The tail of wave 72 is a knob.**  For every admissible `γ₂`-correction `c`, the
bracket `⁅c, A⁆` against wave 68's dressing is *exactly* the knob of a handle-pair correction of
the `j`-th handle, both of whose entries are `1` or `c` and hence admissible.

The mechanism is a two-way parity count.  Modulo `γ₂` and modulo squares, which is all a bracket
with a `Y`-element in the near slot sees, `A = u_j^{ν'(v_j)}·v_j^{ν'(u_j)}·w^{even}` and the two
cleared letters are `U_j = u_j·w^{ν'(u_j)}`, `V_j = v_j·w^{ν'(v_j)}`.  So

```text
  ν'(v_j)·U_j + ν'(u_j)·V_j = ν'(v_j)·u_j + ν'(u_j)·v_j + 2·ν'(u_j)·ν'(v_j)·w = A ,
```

the two pivot contributions cancelling because their total exponent is even.  **The pivot is
therefore not needed**, which is why only the two handle slots appear here and the core slots stay
free.  Wave 72's `cfourDef_comm_dress_frame_mem` routed through the pivot and so had to spend the
`σ`- and `x₀`-slot knobs on `cfourDef_core_knob_pair`; that expenditure is avoidable. -/
theorem cfourCmp_dress_reach {c : (DSq h : Type)} (hc : c ∈ twoCentralSeries (DSq h : Type) 2)
    (hcl : nuLam h c = 1) (hcn : nu' c = 1) :
    ∃ a b : (DSq h : Type),
      (a ∈ twoCentralSeries (DSq h : Type) 2 ∧ nuLam h a = 1 ∧ nu' a = 1) ∧
        (b ∈ twoCentralSeries (DSq h : Type) 2 ∧ nuLam h b = 1 ∧ nu' b = 1) ∧
          commP (levelMk (DSq h : Type) 4 a) (levelMk (DSq h : Type) 4 (sqEichV h nu' j)) *
              commP (levelMk (DSq h : Type) 4 (sqEichU h nu' j)) (levelMk (DSq h : Type) 4 b)
            = commP (levelMk (DSq h : Type) 4 c)
                (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) := by
  have hy : levelMk (DSq h : Type) 4 c ∈ lambdaImage (DSq h : Type) 2 4 := ⟨c, hc, rfl⟩
  have hone : (1 : (DSq h : Type)) ∈ twoCentralSeries (DSq h : Type) 2 ∧
      nuLam h (1 : (DSq h : Type)) = 1 ∧ nu' (1 : (DSq h : Type)) = 1 :=
    ⟨Subgroup.one_mem _, map_one _, map_one _⟩
  have hsplit := cfourCmp_comm_dress_split nu' j hy
  have hU := cfourCmp_comm_eichU nu' j hy
  have hV := cfourCmp_comm_eichV nu' j hy
  have hswap := cfourDef_comm_swap hy (levelMk (DSq h : Type) 4 (sqEichU h nu' j))
  by_cases hu : (2 : ℤ_[2]) ∣ bridgeRowU nu' j <;> by_cases hv : (2 : ℤ_[2]) ∣ bridgeRowV nu' j
  · refine ⟨1, 1, hone, hone, ?_⟩
    rw [hsplit, cfourCmp_comm_zpow_even hy _ hu, cfourCmp_comm_zpow_even hy _ hv, one_mul,
      map_one, cfour_one_comm, cfour_comm_one, one_mul]
  · refine ⟨1, c, hone, ⟨hc, hcl, hcn⟩, ?_⟩
    rw [hsplit, cfourCmp_comm_zpow_even hy _ hu, cfourCmp_comm_zpow_odd hy _ hv,
      map_one, cfour_one_comm, one_mul, hswap, hU, cfourCmp_comm_zpow_even hy _ hu, mul_one,
      one_mul]
  · refine ⟨c, 1, ⟨hc, hcl, hcn⟩, hone, ?_⟩
    rw [hsplit, cfourCmp_comm_zpow_odd hy _ hu, cfourCmp_comm_zpow_even hy _ hv, mul_one,
      map_one, cfour_comm_one, mul_one, hV, cfourCmp_comm_zpow_even hy _ hv, one_mul]
  · refine ⟨c, c, ⟨hc, hcl, hcn⟩, ⟨hc, hcl, hcn⟩, ?_⟩
    rw [hsplit, cfourCmp_comm_zpow_odd hy _ hu, cfourCmp_comm_zpow_odd hy _ hv, hswap, hU, hV,
      cfourCmp_comm_zpow_odd hy _ hu, cfourCmp_comm_zpow_odd hy _ hv]
    exact cfourCmp_z_pair (cfour_commP_mem_zLayer_left hy _) _ _

end DressReach

/-! ## §4 The collapse: the leftover is the core defect alone -/

section Collapse

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **The `Y`-element of wave 72's tail**, upstairs: `y = ⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆`, the near
slot of the single bracket `cfourDef_leftover_reduce_merged` leaves behind. -/
noncomputable def cfourCmpTail : (DSq h : Type) :=
  commP (dsqSigma h) (bridgeDress nu' j) * commP (bridgeDress nu' j) (dsqX0 h) *
    commP (dsqX0 h) (dsqX1 h)

/-- The tail's near slot is an admissible correction: a product of three commutators. -/
theorem cfourCmpTail_admissible :
    cfourCmpTail nu' j ∈ twoCentralSeries (DSq h : Type) 2 ∧
      nuLam h (cfourCmpTail nu' j) = 1 ∧ nu' (cfourCmpTail nu' j) = 1 := by
  obtain ⟨hm1, hl1, hn1⟩ := cfourKnob_comm_admissible nu' (dsqSigma h) (bridgeDress nu' j)
  obtain ⟨hm2, hl2, hn2⟩ := cfourKnob_comm_admissible nu' (bridgeDress nu' j) (dsqX0 h)
  obtain ⟨hm3, hl3, hn3⟩ := cfourKnob_comm_admissible nu' (dsqX0 h) (dsqX1 h)
  obtain ⟨hm4, hl4, hn4⟩ := cfourKnob_mul_admissible nu' hm1 hm2 hl1 hl2 hn1 hn2
  exact cfourKnob_mul_admissible nu' hm4 hm3 hl4 hl3 hn4 hn3

/-- The tail's near slot, read in `Q₄`. -/
theorem cfourCmpTail_levelMk :
    levelMk (DSq h : Type) 4 (cfourCmpTail nu' j)
      = commP (levelMk (DSq h : Type) 4 (dsqSigma h))
              (levelMk (DSq h : Type) 4 (bridgeDress nu' j)) *
            commP (levelMk (DSq h : Type) 4 (bridgeDress nu' j))
              (levelMk (DSq h : Type) 4 (dsqX0 h)) *
          commP (levelMk (DSq h : Type) 4 (dsqX0 h)) (levelMk (DSq h : Type) 4 (dsqX1 h)) := by
  simp only [cfourCmpTail, map_mul, cfourKnob_levelMk_commP]

/-- ⭐⭐⭐ **The class-four leftover of wave 68's frame collapses to the core defect.**  One
admissible correction of wave 68's class-three witness (wave 72's `cfourDefCorr` on the `σ`- and
`x₁`-slots, followed by the wave-73 handle-pair correction of the `j`-th handle) turns the
class-four relator into

```text
  sqRelWord (wave 68's frame · that correction) = cfourDefCore nu' j
```

on the nose.  This is what wave 72's note asked a wave-73 lane to commit: with the composition
lemma `cfourCmp_dress_all` in hand, `cfourDef_leftover_reduce_merged`'s tail `⁅y, A⁆` is an actual
correction and not merely a knob expression, and the whole residue is `cfourDefCore`.

**Honesty marker.**  This is a statement about one route, `γ₂`-valued corrections of wave 68's
frame (wave 70's `CfourIdReachable`).  It says nothing about `SqClassClearingSupply h 4` beyond
what that route gives. -/
theorem cfourCmp_core_reduce (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    ∃ c : Fin (sqRank h) → (DSq h : Type),
      (∀ i, c i ∈ twoCentralSeries (DSq h : Type) 2) ∧ (∀ i, nuLam h (c i) = 1) ∧
        (∀ i, nu' (c i) = 1) ∧
          sqRelWord (fun i => levelMk (DSq h : Type) 4
              (sqArbFrame h nu' j (bridgeTuple nu' j) i * c i)) = cfourDefCore nu' j := by
  obtain ⟨hym, hyl, hyn⟩ := cfourCmpTail_admissible nu' j
  obtain ⟨a, b, ⟨ham, hal, han⟩, ⟨hbm, hbl, hbn⟩, hknob⟩ :=
    cfourCmp_dress_reach nu' j hym hyl hyn
  have hFU : sqArbFrame h nu' j (bridgeTuple nu' j) (sqHandleIdxU j) *
      cfourDefCorr nu' j (sqHandleIdxU j) = sqEichU h nu' j := by
    rw [bridge_frame_handleU, cfourDefCorr_handleU, mul_one, sqArbBase_handleU]
  have hFV : sqArbFrame h nu' j (bridgeTuple nu' j) (sqHandleIdxV j) *
      cfourDefCorr nu' j (sqHandleIdxV j) = sqEichV h nu' j := by
    rw [bridge_frame_handleV, cfourDefCorr_handleV, mul_one, sqArbBase_handleV]
  have hstep := cfourCmp_handle_knob j a b
    (fun i => sqArbFrame h nu' j (bridgeTuple nu' j) i * cfourDefCorr nu' j i) ham hbm
  rw [hFU, hFV, cfourDef_leftover_reduce_merged, ← cfourCmpTail_levelMk, hknob] at hstep
  refine ⟨fun i => cfourDefCorr nu' j i * cfourCmpHandleCorr h j a b i, ?_, ?_, ?_, ?_⟩
  · exact fun i => Subgroup.mul_mem _ (cfourDefCorr_admissible nu' j hsigma hx0 i).1
      (cfourCmpHandleCorr_admissible j a b nu' ham hal han hbm hbl hbn i).1
  · intro i
    rw [map_mul, (cfourDefCorr_admissible nu' j hsigma hx0 i).2.1,
      (cfourCmpHandleCorr_admissible j a b nu' ham hal han hbm hbl hbn i).2.1, one_mul]
  · intro i
    rw [map_mul, (cfourDefCorr_admissible nu' j hsigma hx0 i).2.2,
      (cfourCmpHandleCorr_admissible j a b nu' ham hal han hbm hbl hbn i).2.2, one_mul]
  · have hre : (fun i => levelMk (DSq h : Type) 4 (sqArbFrame h nu' j (bridgeTuple nu' j) i *
          (cfourDefCorr nu' j i * cfourCmpHandleCorr h j a b i)))
        = fun i => levelMk (DSq h : Type) 4 (sqArbFrame h nu' j (bridgeTuple nu' j) i *
          cfourDefCorr nu' j i * cfourCmpHandleCorr h j a b i) := by
      funext i
      rw [mul_assoc]
    rw [hre, hstep, mul_assoc,
      cfourDef_z_sq (cfour_commP_mem_zLayer_left ⟨_, hym, rfl⟩
        (levelMk (DSq h : Type) 4 (bridgeDress nu' j))), mul_one]

end Collapse

/-! ## §5 The residual after the collapse -/

section Residual

variable {h : ℕ}

/-- ⭐⭐ **The wave-73 residual**: from *any* admissible `γ₂`-valued correction of wave 68's frame
whose class-four relator is exactly the core defect, a further admissible correction kills it.
`cfourCmp_core_reduce` supplies such a correction unconditionally, so this Prop is the whole of
what is left of wave 70's `CfourIdReachable`.

**Honesty marker.**  This is a residual of the *route* (wave 70's `CfourIdReachable`, `γ₂`-valued
corrections of wave 68's frame), not of `SqClassClearingSupply h 4`.  A failure of this Prop would
not refute the supply. -/
def CfourCmpResidual (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∀ c : Fin (sqRank h) → (DSq h : Type),
        (∀ i, c i ∈ twoCentralSeries (DSq h : Type) 2) → (∀ i, nuLam h (c i) = 1) →
          (∀ i, nu' (c i) = 1) →
            sqRelWord (fun i => levelMk (DSq h : Type) 4
                (sqArbFrame h nu' j (bridgeTuple nu' j) i * c i)) = cfourDefCore nu' j →
              ∃ d : Fin (sqRank h) → (DSq h : Type),
                (∀ i, d i ∈ twoCentralSeries (DSq h : Type) 2) ∧ (∀ i, nuLam h (d i) = 1) ∧
                  (∀ i, nu' (d i) = 1) ∧
                    sqRelWord (fun i => levelMk (DSq h : Type) 4
                        (sqArbFrame h nu' j (bridgeTuple nu' j) i * c i * d i)) = 1

/-- ⭐⭐ **The residual discharges wave 70's reachability.**  Admissible corrections compose, and
`cfourCmp_core_reduce` supplies the intermediate one. -/
theorem cfourCmp_reachable_of_residual (H : CfourCmpResidual h) : CfourIdReachable h := by
  intro nu' j hs hx
  obtain ⟨c, hcm, hcl, hcn, hcrel⟩ := cfourCmp_core_reduce nu' j hs hx
  obtain ⟨d, hdm, hdl, hdn, hdrel⟩ := H nu' j hs hx c hcm hcl hcn hcrel
  refine ⟨fun i => c i * d i, fun i => Subgroup.mul_mem _ (hcm i) (hdm i), ?_, ?_, ?_⟩
  · intro i
    rw [map_mul, hcl i, hdl i, one_mul]
  · intro i
    rw [map_mul, hcn i, hdn i, one_mul]
  · simpa only [← mul_assoc] using hdrel

/-- ⭐⭐ **The residual discharges the class-four supply.** -/
theorem cfourCmp_supply_of_residual (H : CfourCmpResidual h) : SqClassClearingSupply h 4 :=
  cfourId_supply_of_reachable (cfourCmp_reachable_of_residual H)

/-- **The residual holds wherever the core defect vanishes**: take the trivial further
correction.  Nothing here says the core defect vanishes; §6 is about whether it is a knob. -/
theorem cfourCmp_residual_of_core_vanish
    (H : ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
      cfourDefCore nu' j = 1) : CfourCmpResidual h := by
  intro nu' j _ _ c _ _ _ hrel
  exact ⟨fun _ => 1, fun _ => Subgroup.one_mem _, fun _ => map_one _, fun _ => map_one _, by
    simpa only [mul_one, hrel] using H nu' j⟩

/-- **The class-four supply, from the vanishing of the core defect alone.**  The whole of the
class-four obligation along wave 70's route is now this single element of `Z = γ₃/γ₄`. -/
theorem cfourCmp_supply_of_core_vanish
    (H : ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
      cfourDefCore nu' j = 1) : SqClassClearingSupply h 4 :=
  cfourCmp_supply_of_residual (cfourCmp_residual_of_core_vanish H)

end Residual

/-! ## §6 The relations half of the graded decomposition, at class four -/

section Relations

variable {h : ℕ}

/-- **The test subgroup for `cfourCmp_zLayer_le_gens`**: those `Y`-elements whose square, and
whose bracket against every slot, lie in `S`.  It is a **subgroup** exactly because `Y` is abelian
at class four: `cfour_sq_mul_lambdaTwo` makes `y ↦ y²` additive on `Y` and
`cfourId_comm_dress_left` makes `y ↦ commP y q` additive, and both fail one class up, which is
why wave 72's class-five analogue needed six families where three suffice here. -/
def cfourCmpTest (S : Subgroup (levelQuot (DSq h : Type) 4)) :
    Subgroup (levelQuot (DSq h : Type) 4) where
  carrier := {y | y ∈ lambdaImage (DSq h : Type) 2 4 ∧ y ^ 2 ∈ S ∧
    ∀ q : levelQuot (DSq h : Type) 4, commP y q ∈ S}
  one_mem' := ⟨Subgroup.one_mem _, by rw [one_pow]; exact Subgroup.one_mem _,
    fun q => by rw [cfour_one_comm]; exact Subgroup.one_mem _⟩
  mul_mem' := fun {_ _} hy hy' => ⟨Subgroup.mul_mem _ hy.1 hy'.1,
    by rw [cfour_sq_mul_lambdaTwo hy.1 hy'.1]; exact Subgroup.mul_mem _ hy.2.1 hy'.2.1,
    fun q => by
      rw [cfourId_comm_dress_left _ _ hy'.1]
      exact Subgroup.mul_mem _ (hy.2.2 q) (hy'.2.2 q)⟩
  inv_mem' := fun {_} hy => ⟨Subgroup.inv_mem _ hy.1,
    by rw [inv_pow]; exact Subgroup.inv_mem _ hy.2.1,
    fun q => by rw [gThreeFour_ad_inv_left hy.1]; exact hy.2.2 q⟩

theorem cfourCmp_mem_test {S : Subgroup (levelQuot (DSq h : Type) 4)}
    {y : levelQuot (DSq h : Type) 4} :
    y ∈ cfourCmpTest S ↔ y ∈ lambdaImage (DSq h : Type) 2 4 ∧ y ^ 2 ∈ S ∧
      ∀ q : levelQuot (DSq h : Type) 4, commP y q ∈ S := Iff.rfl

/-- ⭐⭐⭐ **The relations half of the graded decomposition of `Z = γ₃/γ₄`, at `D_sq h`: three
families indexed by `Q₄` alone.**  A subgroup of `Q₄` containing

* every fourth power `p⁴`,
* every square of a bracket `⁅p, q⁆²`,
* every triple bracket `⁅⁅p, q⁆, r⁆`

contains the whole of `Z`.  This is what wave 70's `L₃(V)` spanning claim needed and never had,
and it is the class-four analogue of wave 72's `cfiveSpan_zLayer_le_gens`.  Sharper than that one:
three families instead of six, because `Y` is abelian at class four, so the two maps `y ↦ y²` and
`y ↦ commP y q` of `cfourId_zLayer_le` are homomorphisms on `Y` and each family need only be
checked on the generators of `Y`, namely the squares and brackets of `Q₄`.  On a square generator
the check is `gThreeFour_commP_sq_left`, which turns `commP (p²) q` into a bracket square and a
triple bracket, so no fourth family is needed for it.

The three families are exactly the three restricted summands of `γ₃/γ₄`: `V^{[4]}` from `p⁴`,
`(Λ²V)^{[2]}` from `⁅p, q⁆²`, and `L₃(V)` from the triple brackets. -/
theorem cfourCmp_zLayer_le_gens {S : Subgroup (levelQuot (DSq h : Type) 4)}
    (hpow : ∀ p : levelQuot (DSq h : Type) 4, p ^ 4 ∈ S)
    (hsq : ∀ p q : levelQuot (DSq h : Type) 4, commP p q ^ 2 ∈ S)
    (htriple : ∀ p q r : levelQuot (DSq h : Type) 4, commP (commP p q) r ∈ S) :
    zLayer (DSq h : Type) 3 ≤ S := by
  have hgenSq : ∀ p : levelQuot (DSq h : Type) 4, p ^ 2 ∈ cfourCmpTest S := by
    intro p
    refine ⟨cfour_sq_mem_lambdaTwo p, ?_, fun q => ?_⟩
    · have h4 : p ^ 4 = (p ^ 2) ^ 2 := by rw [← pow_mul]
      rw [← h4]
      exact hpow p
    · rw [gThreeFour_commP_sq_left]
      exact Subgroup.mul_mem _ (hsq p q) (htriple p q p)
  have hgenComm : ∀ p q : levelQuot (DSq h : Type) 4, commP p q ∈ cfourCmpTest S :=
    fun p q => ⟨cfour_commP_mem_lambdaTwo p q, hsq p q, fun r => htriple p q r⟩
  have hpre : IsClosed ((Subgroup.comap (levelMk (DSq h : Type) 4) (cfourCmpTest S) :
      Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    rw [Subgroup.coe_comap]
    exact (cfourId_isClosed _).preimage (continuous_levelMk (DSq h : Type) 4)
  have hsub : twoCentralSeries (DSq h : Type) 2 ≤
      Subgroup.comap (levelMk (DSq h : Type) 4) (cfourCmpTest S) := by
    rw [cfour_lambda_two, twoCentralSucc]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hpre
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, -, rfl⟩
      show levelMk (DSq h : Type) 4 (g ^ 2) ∈ cfourCmpTest S
      rw [map_pow]
      exact hgenSq _
    · refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [commutatorElement_def]
      show levelMk (DSq h : Type) 4 (a * b * a⁻¹ * b⁻¹) ∈ cfourCmpTest S
      rw [gThreeFour_levelMk_commutator]
      exact hgenComm _ _
  refine cfourId_zLayer_le (fun y hy => ?_) (fun y hy q => ?_)
  · obtain ⟨v, hv, rfl⟩ := hy
    exact (hsub hv).2.1
  · obtain ⟨v, hv, rfl⟩ := hy
    exact (hsub hv).2.2 q

/-- ⭐⭐⭐ **The sharp reduction of the class-four route.**  Suppose that at every selected
marking and handle, and for every admissible correction `c` whose class-four relator is the core
defect, there is a subgroup `S` of `Q₄` such that

* every element of `S` is the knob of some further admissible correction, and
* `S` contains the three families `p⁴`, `⁅p, q⁆²`, `⁅⁅p, q⁆, r⁆`.

Then `CfourCmpResidual h`, hence `SqClassClearingSupply h 4`.  The mechanism is
`cfourCmp_zLayer_le_gens`: those three families force `Z ≤ S`, and `cfourDefCore` lies in `Z`
(`cfourDef_core_mem_zLayer`), so it is a knob, and being an involution it kills itself.

**This is what a wave-74 lane has to decide, and it no longer mentions `cfourDefCore` at all.**
The question "is the core defect a knob" is replaced by the three uniform questions "are fourth
powers, bracket squares and triple brackets knobs".

**Honesty marker.**  A failure of this hypothesis is a statement about the knob subgroup of one
inventory along one route (wave 70's `CfourIdReachable`).  It is not a statement about
`SqClassClearingSupply h 4`, and it would not refute the residual. -/
theorem cfourCmp_residual_of_span
    (H : ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∀ c : Fin (sqRank h) → (DSq h : Type),
          (∀ i, c i ∈ twoCentralSeries (DSq h : Type) 2) → (∀ i, nuLam h (c i) = 1) →
            (∀ i, nu' (c i) = 1) →
              sqRelWord (fun i => levelMk (DSq h : Type) 4
                  (sqArbFrame h nu' j (bridgeTuple nu' j) i * c i)) = cfourDefCore nu' j →
                ∃ S : Subgroup (levelQuot (DSq h : Type) 4),
                  (∀ p : levelQuot (DSq h : Type) 4, p ^ 4 ∈ S) ∧
                    (∀ p q : levelQuot (DSq h : Type) 4, commP p q ^ 2 ∈ S) ∧
                      (∀ p q r : levelQuot (DSq h : Type) 4, commP (commP p q) r ∈ S) ∧
                        ∀ z ∈ S, ∃ d : Fin (sqRank h) → (DSq h : Type),
                          (∀ i, d i ∈ twoCentralSeries (DSq h : Type) 2) ∧
                            (∀ i, nuLam h (d i) = 1) ∧ (∀ i, nu' (d i) = 1) ∧
                              sqRelWord (fun i => levelMk (DSq h : Type) 4
                                  (sqArbFrame h nu' j (bridgeTuple nu' j) i * c i * d i))
                                = cfourDefCore nu' j * z) :
    CfourCmpResidual h := by
  intro nu' j hs hx c hcm hcl hcn hcrel
  obtain ⟨S, hpow, hsq, htriple, hreach⟩ := H nu' j hs hx c hcm hcl hcn hcrel
  obtain ⟨d, hdm, hdl, hdn, hdrel⟩ :=
    hreach _ (cfourCmp_zLayer_le_gens hpow hsq htriple (cfourDef_core_mem_zLayer nu' j))
  exact ⟨d, hdm, hdl, hdn, by
    rw [hdrel, cfourDef_z_sq (cfourDef_core_mem_zLayer nu' j)]⟩

/-- **The class-four supply, from the three families.**  `cfourCmp_residual_of_span` composed with
`cfourCmp_supply_of_residual`. -/
theorem cfourCmp_supply_of_span
    (H : ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∀ c : Fin (sqRank h) → (DSq h : Type),
          (∀ i, c i ∈ twoCentralSeries (DSq h : Type) 2) → (∀ i, nuLam h (c i) = 1) →
            (∀ i, nu' (c i) = 1) →
              sqRelWord (fun i => levelMk (DSq h : Type) 4
                  (sqArbFrame h nu' j (bridgeTuple nu' j) i * c i)) = cfourDefCore nu' j →
                ∃ S : Subgroup (levelQuot (DSq h : Type) 4),
                  (∀ p : levelQuot (DSq h : Type) 4, p ^ 4 ∈ S) ∧
                    (∀ p q : levelQuot (DSq h : Type) 4, commP p q ^ 2 ∈ S) ∧
                      (∀ p q r : levelQuot (DSq h : Type) 4, commP (commP p q) r ∈ S) ∧
                        ∀ z ∈ S, ∃ d : Fin (sqRank h) → (DSq h : Type),
                          (∀ i, d i ∈ twoCentralSeries (DSq h : Type) 2) ∧
                            (∀ i, nuLam h (d i) = 1) ∧ (∀ i, nu' (d i) = 1) ∧
                              sqRelWord (fun i => levelMk (DSq h : Type) 4
                                  (sqArbFrame h nu' j (bridgeTuple nu' j) i * c i * d i))
                                = cfourDefCore nu' j * z) :
    SqClassClearingSupply h 4 :=
  cfourCmp_supply_of_residual (cfourCmp_residual_of_span H)

end Relations

/-! ## §9 Axiom pins -/

section AxiomPins

#print axioms cfourCmp_dress_all
#print axioms cfourCmp_dress_handles
#print axioms cfourCmp_z_pair
#print axioms cfourCmpHandleCorr_handleU
#print axioms cfourCmpHandleCorr_handleV
#print axioms cfourCmpHandleCorr_handleU_ne
#print axioms cfourCmpHandleCorr_handleV_ne
#print axioms cfourCmpHandleCorr_zero
#print axioms cfourCmpHandleCorr_one
#print axioms cfourCmpHandleCorr_two
#print axioms cfourCmpHandleCorr_admissible
#print axioms cfourCmp_handle_knob
#print axioms cfourCmp_comm_zpow_even
#print axioms cfourCmp_comm_zpow_odd
#print axioms cfourCmp_comm_dress_split
#print axioms cfourCmp_comm_eichU
#print axioms cfourCmp_comm_eichV
#print axioms cfourCmp_dress_reach
#print axioms cfourCmpTail_admissible
#print axioms cfourCmpTail_levelMk
#print axioms cfourCmp_core_reduce
#print axioms cfourCmp_reachable_of_residual
#print axioms cfourCmp_supply_of_residual
#print axioms cfourCmp_residual_of_core_vanish
#print axioms cfourCmp_supply_of_core_vanish
#print axioms cfourCmpTest
#print axioms cfourCmp_mem_test
#print axioms cfourCmp_zLayer_le_gens
#print axioms cfourCmp_residual_of_span
#print axioms cfourCmp_supply_of_span

end AxiomPins

end SqCore

end Dyadic

end GQ2
