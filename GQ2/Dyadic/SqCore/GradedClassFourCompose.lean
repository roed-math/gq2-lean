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

end Compose

/-! ## §9 Axiom pins -/

section AxiomPins

#print axioms cfourCmp_dress_all
#print axioms cfourCmp_dress_handles

end AxiomPins

end SqCore

end Dyadic

end GQ2
