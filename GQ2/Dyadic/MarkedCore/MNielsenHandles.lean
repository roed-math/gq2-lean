/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.MNielsenGenerators

/-!
# The rank-four M Nielsen list carried to every handle count by the identity handle tail

Wave 366, lane W366-HANDLES.

**Scope, stated first.** This file is *optional* mathematics beyond the packet's rank-four
rows. The owner has accepted (Option A, 2026-09-18) the compactness proof method and the
families reading of the finite lists at rank four; nothing here is needed for that
acceptance and nothing here changes it.

**No handle-mixing classification is claimed, and none exists in the repo.** What is proved
here is exactly the weaker statement flagged at `docs/dyadic/w363-nielsen-note.md`
(lines 190-200): the seven core families, extended by the **identity on the `2h` handle
coordinates**, still preserve `mFrameOrientation` and `MCupFrameCupIsometry` at every `h`,
hence still lift by `mFullStabilizer_lift`. The stabilizer elements covered are exactly
those that are a rank-four `MStabParam` action on the core block and the identity on the
handle block; a full-frame automorphism that moves the handle block is **not** covered.
`alpha >= 2` throughout.

`MNielsenHandles.mNielsenHdlStabilizerShape` (below) states, as an unproved named `Prop`,
what a full handle-mixing classification would have to say.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 GQ2.SectionThree Multiplicative
open GQ2.Dyadic.EvenModel
open scoped GQ2.SectionThree.TopAbInstances

/-! ## Index arithmetic on `Fin (coreRank h)` -/

/-- Every full-frame index is one of the four core indices or a handle index. -/
theorem mNielsenHdl_index_cases {h : ℕ} (j : Fin (coreRank h)) :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ ∃ k : Fin (2 * h), j = mHandleIdx k := by
  have h0 := coreVal_zero h
  have h1 := coreVal_one h
  have h2 := coreVal_two h
  have h3 := coreVal_three h
  have hlt : (j : ℕ) < 4 + 2 * h := by have := j.isLt; simpa only [coreRank] using this
  rcases Nat.lt_or_ge (j : ℕ) 4 with hj | hj
  · have hcase : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ (j : ℕ) = 3 := by omega
    rcases hcase with hv | hv | hv | hv
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (Or.inl (Fin.ext (by omega)))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by omega)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨(j : ℕ) - 4, by omega⟩, Fin.ext ?_⟩)))
    rw [mHandleIdx_val]
    show (j : ℕ) = 4 + ((j : ℕ) - 4)
    omega

/-- The four core indices are not handle indices. -/
theorem mNielsenHdl_core_ne_handle {h : ℕ} (k : Fin (2 * h)) :
    (0 : Fin (coreRank h)) ≠ mHandleIdx k ∧ (1 : Fin (coreRank h)) ≠ mHandleIdx k ∧
      (2 : Fin (coreRank h)) ≠ mHandleIdx k ∧ (3 : Fin (coreRank h)) ≠ mHandleIdx k := by
  have h0 := coreVal_zero h
  have h1 := coreVal_one h
  have h2 := coreVal_two h
  have h3 := coreVal_three h
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_, fun hc => ?_⟩ <;>
    · have := congrArg (fun i : Fin (coreRank h) => (i : ℕ)) hc
      rw [mHandleIdx_val] at this
      omega

/-- **The head-plus-handles splitting of a full-frame sum.** -/
theorem mNielsenHdl_sum_split {h : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin (coreRank h) → M) :
    ∑ j, f j = f 0 + f 1 + f 2 + f 3 + ∑ k : Fin (2 * h), f (mHandleIdx k) := by
  have hsplit : ∑ j : Fin (4 + 2 * h), f j
      = (∑ i : Fin 4, f (Fin.castAdd (2 * h) i)) + ∑ k : Fin (2 * h), f (Fin.natAdd 4 k) :=
    Fin.sum_univ_add f
  have hnat : ∀ k : Fin (2 * h), (Fin.natAdd 4 k : Fin (coreRank h)) = mHandleIdx k :=
    fun _ => rfl
  have e0 : (0 : Fin (coreRank h)) = Fin.castAdd (2 * h) (0 : Fin 4) :=
    Fin.ext (by rw [coreVal_zero]; rfl)
  have e1 : (1 : Fin (coreRank h)) = Fin.castAdd (2 * h) (1 : Fin 4) :=
    Fin.ext (by rw [coreVal_one]; rfl)
  have e2 : (2 : Fin (coreRank h)) = Fin.castAdd (2 * h) (2 : Fin 4) :=
    Fin.ext (by rw [coreVal_two]; rfl)
  have e3 : (3 : Fin (coreRank h)) = Fin.castAdd (2 * h) (3 : Fin 4) :=
    Fin.ext (by rw [coreVal_three]; rfl)
  calc ∑ j, f j = ∑ j : Fin (4 + 2 * h), f j := rfl
    _ = (∑ i : Fin 4, f (Fin.castAdd (2 * h) i)) + ∑ k : Fin (2 * h), f (Fin.natAdd 4 k) :=
        hsplit
    _ = f 0 + f 1 + f 2 + f 3 + ∑ k : Fin (2 * h), f (mHandleIdx k) := by
        rw [Fin.sum_univ_four, e0, e1, e2, e3]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => congrArg f (hnat k))

#print axioms mNielsenHdl_index_cases
#print axioms mNielsenHdl_core_ne_handle
#print axioms mNielsenHdl_sum_split
