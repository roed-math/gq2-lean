import GQ2.Dyadic.MarkedCore.NPlaneRowRefinement
import GQ2.Dyadic.MarkedCore.NPlaneOrdinaryHead
import GQ2.Dyadic.MarkedCore.NPlaneFilteredSlack

/-!
# Relative refinement of an existing arbitrary-rank N correction

The head's extra ordinary digit follows from the actual improved relator
defect. Replacing that head in its filtered class and then using the actual
closed derivative kernel removes all ordinary rows simultaneously. This is
a refinement theorem, not an existence theorem for the initial correction.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

/-- Any existing orientation-preserving N correction at this depth can be
refined to have exactly zero ordinary rows, provided the current marking has
the specified unit diagonal. The improved error keeps the same literal target. -/
theorem exists_nPlane_relative_correction {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (n : ℕ) (y t : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (u : Fin (coreRank h) → ℤ_[2]ˣ)
    (hy : ∀ j v, toAdd (freeTwoCoordinate (coreRank h) j (y v)) =
      if j = v then (u v : ℤ_[2]) else 0)
    (target : FreeTwoRank (coreRank h))
    (hrow : ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]), f (nRelWord alpha y) = f target)
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2))
    (hchi : ∀ i, freeNOrientation alpha h (t i) = 1)
    (hdefect : nRelWord alpha (y*t) * target⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4)) :
    ∃ t' : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, t' i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      (∀ i, freeNOrientation alpha h (t' i) = 1) ∧
      (∀ i, ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]), f (t' i) = 1) ∧
      nRelWord alpha (y*t') * target⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4) := by
  classical
  obtain ⟨t0, ht0, hslack0, hzero0⟩ := exists_freeTwo_nHead_characterZero_same_class
    halpha y t target hrow (ht 0) hdefect
  let s := Function.update t 0 t0
  have hs : ∀ i, s i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2) := by
    intro i
    by_cases hi : i = 0
    · subst i; simpa [s] using ht0
    · simpa [s, hi] using ht i
  have hslack : ∀ i, (t i)⁻¹*s i ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+3) := by
    intro i
    by_cases hi : i = 0
    · subst i; simpa [s] using hslack0
    · simp [s, hi]
  have hshead : ∀ j, toAdd (freeTwoCoordinate (coreRank h) j (s 0)) = 0 := by
    intro j
    simp only [s, Function.update_self, hzero0, toAdd_one]
  have hschi : ∀ i, freeNOrientation alpha h (s i) = 1 := by
    intro i
    by_cases hi : i = 0
    · subst i
      apply (freeNOrientation_eq_one_iff halpha h (s 0)).mpr
      exact hshead 1
    · simpa [s, hi] using hchi i
  have hsdefect : nRelWord alpha (y*s) * target⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4) :=
    (nRelWord_correction_defect_mem_iff (by omega) (n+3) y t s target hslack).mpr hdefect
  obtain ⟨t', -, hcoords, ht', heq⟩ :=
    exists_nPlane_rowZero_same_kernelCoset halpha n y s u hy hs hshead hschi
  have hzero : ∀ i, ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
      (Multiplicative ℤ_[2]), f (t' i) = 1 := by
    intro i f
    apply toAdd.injective
    rw [freeTwo_character_coordinates]
    simp only [hcoords, toAdd_one, zero_mul, Finset.sum_const_zero]
  refine ⟨t', ht', ?_, hzero, ?_⟩
  · intro i
    apply (freeNOrientation_eq_one_iff halpha h (t' i)).mpr
    rw [hcoords, toAdd_one]
  · rw [← QuotientGroup.eq_one_iff] at hsdefect ⊢
    change levelMk (FreeTwoRank (coreRank h) : Type) (n+4) _ = 1 at hsdefect ⊢
    rw [map_mul, heq, ← map_mul]
    exact hsdefect

#print axioms exists_nPlane_relative_correction

end
end GQ2.Dyadic.MarkedCore
