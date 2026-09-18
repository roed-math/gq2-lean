import GQ2.Dyadic.MarkedCore.NBasisRowRefinement
import GQ2.Dyadic.MarkedCore.NPlaneOrdinaryHead
import GQ2.Dyadic.MarkedCore.NPlaneFilteredSlack

/-!
# Relative N correction at any current free basis

An already existing correction improving the actual N relator can be replaced
by one annihilated by every ordinary Z2 character. The current marking is an
arbitrary genuine free basis; no diagonal or separately invertible coordinate
matrix is assumed. Exact ordinary agreement with the target is retained as a
load-bearing premise for the extra head digit. The theorem refines a supplied
correction; it does not assert a starting basis or an initial depth-three
relator comparison.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

/-- Head cleanup and arbitrary-basis kernel interpolation preserve the literal
improved target-relative error while making every correction character zero.
Neither the input basis nor the input correction needs an orientation premise. -/
theorem exists_nBasis_full_relative_correction {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (n : ℕ) (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (t : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (target : FreeTwoRank (coreRank h))
    (hrow : ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]),
      f (nRelWord alpha (fun i => e (freeTwoRankGen (coreRank h) i))) = f target)
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2))
    (hdefect : nRelWord alpha ((fun i => e (freeTwoRankGen (coreRank h) i))*t) * target⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4)) :
    ∃ t' : Fin (coreRank h) → FreeTwoRank (coreRank h),
      (∀ i, t' i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      (∀ i, freeNOrientation alpha h (t' i) = 1) ∧
      (∀ i, ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]), f (t' i) = 1) ∧
      nRelWord alpha ((fun i => e (freeTwoRankGen (coreRank h) i))*t') * target⁻¹ ∈
        twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4) := by
  classical
  let y := fun i => e (freeTwoRankGen (coreRank h) i)
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
  have hsdefect : nRelWord alpha (y*s) * target⁻¹ ∈
      twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+4) :=
    (nRelWord_correction_defect_mem_iff (by omega) (n+3) y t s target hslack).mpr hdefect
  obtain ⟨t', -, hcoords, ht', heq⟩ :=
    exists_nBasis_allRows_same_kernelCoset halpha n e s hs hshead
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

#print axioms exists_nBasis_full_relative_correction

end
end GQ2.Dyadic.MarkedCore
