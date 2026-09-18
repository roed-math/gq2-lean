import GQ2.Dyadic.MarkedCore.ProTwoRowCorrection
import GQ2.Dyadic.MarkedCore.NPlaneCorrectionKernel
import GQ2.Dyadic.MarkedCore.NPlaneKernelDiagonal
import GQ2.Dyadic.MarkedCore.FreeProTwoFiniteProduct
import GQ2.Roe.Labute.AdditiveCharacters

/-!
# Exact finite-row refinement inside the actual N derivative kernel

This takes an existing correction, with its head rows already zero, and
removes every remaining ordinary coordinate inside the actual closed
derivative kernel. It preserves the actual relator at the current next
level. Existence of an unrestricted correction remains a separate premise.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

private def tupleRow (h : ℕ) (r : Fin (coreRank h) × Fin (coreRank h)) :
    ContinuousMonoidHom (Fin (coreRank h) → FreeTwoRank (coreRank h))
      (Multiplicative ℤ_[2]) where
  toFun t := freeTwoCoordinate (coreRank h) r.2 (t r.1)
  map_one' := map_one _
  map_mul' _ _ := map_mul _ _ _
  continuous_toFun := (freeTwoCoordinate (coreRank h) r.2).continuous_toFun.comp
    (continuous_apply r.1)

/-- All correction-coordinate rows are removed simultaneously. The zero
scales on the head and b-coordinate rows are justified by the explicit head
condition and exact orientation, respectively. Other divisibility follows
from the actual filtration depth, rather than being a new input. -/
theorem exists_nPlane_rowZero_same_kernelCoset {α h : ℕ} (hα : 2 ≤ α) (n : ℕ)
    (y t : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (u : Fin (coreRank h) → ℤ_[2]ˣ)
    (hy : ∀ j v, toAdd (freeTwoCoordinate (coreRank h) j (y v)) =
      if j = v then (u v : ℤ_[2]) else 0)
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2))
    (hhead : ∀ j, toAdd (freeTwoCoordinate (coreRank h) j (t 0)) = 0)
    (hchi : ∀ i, freeNOrientation α h (t i) = 1) :
    ∃ t' : Fin (coreRank h) → FreeTwoRank (coreRank h),
      t⁻¹*t' ∈ nPlaneCorrectionKernel (n+3) (by omega) y ∧
      (∀ i j, freeTwoCoordinate (coreRank h) j (t' i) = 1) ∧
      (∀ i, t' i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      levelMk (FreeTwoRank (coreRank h) : Type) (n+4) (nRelWord α (y*t')) =
        levelMk (FreeTwoRank (coreRank h) : Type) (n+4) (nRelWord α (y*t)) := by
  classical
  let good (r : Fin (coreRank h) × Fin (coreRank h)) : Prop := r.1 ≠ 0 ∧ r.2 ≠ 1
  let H := nPlaneCorrectionKernel (n+3) (by omega) y
  let w (r : Fin (coreRank h) × Fin (coreRank h)) :
      Fin (coreRank h) → FreeTwoRank (coreRank h) :=
    if good r then nPlaneKernelTuple n 0 1 r.1 r.2 y nPartner else 1
  let c (r : Fin (coreRank h) × Fin (coreRank h)) : ℤ_[2] :=
    if good r then 2^(n+1) * (u r.2 : ℤ_[2]) else 0
  have hw : ∀ r, w r ∈ H := by
    intro r
    dsimp only [w]
    split_ifs with hr
    · exact nPlaneKernelTuple_mem_correctionKernel n y r.1 r.2 hr.1 hr.2
    · exact H.one_mem
  have hd : ∀ r s, toAdd (tupleRow h r (w s)) = if r=s then c r else 0 := by
    intro r s
    by_cases hs : good s
    · rw [show w s = nPlaneKernelTuple n 0 1 s.1 s.2 y nPartner from if_pos hs]
      change toAdd (freeTwoCoordinate (coreRank h) r.2
        (nPlaneKernelTuple n 0 1 s.1 s.2 y nPartner r.1)) = _
      rw [nPlaneKernelTuple_coordinate_diagonal (coreRank h) n 0 1 s.1 s.2 y u hy]
      by_cases hrs : r = s
      · subst r
        simp [c, hs]
      · have hn : ¬ (r.1 = s.1 ∧ r.2 = s.2) := fun he => hrs (Prod.ext he.1 he.2)
        simp [hrs, hn]
    · rw [show w s = 1 from if_neg hs]
      change toAdd (freeTwoCoordinate (coreRank h) r.2 1) = _
      by_cases hrs : r = s
      · subst r
        simp [c, hs]
      · simp [hrs]
  have hc : ∀ r, c r ∣ toAdd (tupleRow h r t) := by
    intro r
    change c r ∣ toAdd (freeTwoCoordinate (coreRank h) r.2 (t r.1))
    by_cases hr : good r
    · dsimp only [c]
      rw [if_pos hr]
      obtain ⟨z, hz⟩ := twoCentralSeries_z2_character_dvd_succ
        (freeTwoCoordinate (coreRank h) r.2) (ht r.1)
      refine ⟨(↑((u r.2)⁻¹) : ℤ_[2])*z, ?_⟩
      rw [hz]
      calc
        (2 : ℤ_[2])^(n+1)*z = (2 : ℤ_[2])^(n+1)*
            ((u r.2 : ℤ_[2])*((↑((u r.2)⁻¹) : ℤ_[2])*z)) := by simp
        _ = (2 : ℤ_[2])^(n+1)*(u r.2 : ℤ_[2])*
            ((↑((u r.2)⁻¹) : ℤ_[2])*z) := by ring
    · have hz : toAdd (freeTwoCoordinate (coreRank h) r.2 (t r.1)) = 0 := by
        by_cases hi : r.1 = 0
        · rw [hi]; exact hhead r.2
        · have hv : r.2 = 1 := by
            by_contra hv
            exact hr ⟨hi, hv⟩
          rw [hv]
          exact (freeNOrientation_eq_one_iff hα h (t r.1)).mp (hchi r.1)
      rw [hz]
      exact dvd_zero _
  obtain ⟨t', hcoset, hzero⟩ := exists_closedSubgroup_rowZero_same_coset_fintype
    (isProTwo_freeN_tuple h)
    (tupleRow h) H (isClosed_nPlaneCorrectionKernel (n+3) (by omega) y) w hw c hd t hc
  have hcoord : ∀ i j, freeTwoCoordinate (coreRank h) j (t' i) = 1 :=
    fun i j => hzero (i,j)
  refine ⟨t', hcoset, hcoord, ?_, ?_⟩
  · intro i
    have hh := hcoset.1 i
    change (t i)⁻¹*t' i ∈ twoCentralSeries _ (n+3-1) at hh
    have he : t' i = t i*((t i)⁻¹*t' i) := by group
    rw [he]
    exact (twoCentralSeries _ (n+2)).mul_mem (ht i) (by simpa using hh)
  · have he := nRelWord_mul_correctionKernel (n+3) (by omega) α hα y t (t⁻¹*t')
      (fun i => by simpa using ht i) hcoset
    simpa only [mul_inv_cancel_left] using he

/-- The same refinement with the exact invariants needed by a future stage
iteration: one tuple is killed by every ordinary character and by chi. -/
theorem exists_nPlane_characterZero_refinement {α h : ℕ} (hα : 2 ≤ α) (n : ℕ)
    (y t : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (u : Fin (coreRank h) → ℤ_[2]ˣ)
    (hy : ∀ j v, toAdd (freeTwoCoordinate (coreRank h) j (y v)) =
      if j = v then (u v : ℤ_[2]) else 0)
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2))
    (hhead : ∀ j, toAdd (freeTwoCoordinate (coreRank h) j (t 0)) = 0)
    (hchi : ∀ i, freeNOrientation α h (t i) = 1) :
    ∃ t' : Fin (coreRank h) → FreeTwoRank (coreRank h),
      t⁻¹*t' ∈ nPlaneCorrectionKernel (n+3) (by omega) y ∧
      (∀ i j, freeTwoCoordinate (coreRank h) j (t' i) = 1) ∧
      (∀ i, t' i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      (∀ i, freeNOrientation α h (t' i) = 1) ∧
      (∀ i, ∀ f : ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type)
        (Multiplicative ℤ_[2]), f (t' i) = 1) ∧
      levelMk (FreeTwoRank (coreRank h) : Type) (n+4) (nRelWord α (y*t')) =
        levelMk (FreeTwoRank (coreRank h) : Type) (n+4) (nRelWord α (y*t)) := by
  obtain ⟨t', hcoset, hcoord, hdepth, hrel⟩ :=
    exists_nPlane_rowZero_same_kernelCoset hα n y t u hy ht hhead hchi
  refine ⟨t', hcoset, hcoord, hdepth, ?_, ?_, hrel⟩
  · intro i
    apply (freeNOrientation_eq_one_iff hα h (t' i)).mpr
    rw [hcoord, toAdd_one]
  · intro i f
    apply toAdd.injective
    rw [freeTwo_character_coordinates (coreRank h) f (t' i)]
    simp [hcoord]

#print axioms exists_nPlane_rowZero_same_kernelCoset
#print axioms exists_nPlane_characterZero_refinement

end
end GQ2.Dyadic.MarkedCore
