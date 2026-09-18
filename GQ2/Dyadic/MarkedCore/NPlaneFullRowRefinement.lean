import GQ2.Dyadic.MarkedCore.NPlaneKernelAllRows
import GQ2.Dyadic.MarkedCore.NPlaneRelativeRefinement

/-!
# Simultaneous removal of every ordinary N correction row

The actual closed derivative kernel contains independently weighted directions
for all non-head slots and all coordinates, including b. Compact pro-two row
interpolation removes them exactly, preserving the literal relator class.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

private def fullTupleRow (h : ℕ) (r : Fin (coreRank h) × Fin (coreRank h)) :
    ContinuousMonoidHom (Fin (coreRank h) → FreeTwoRank (coreRank h))
      (Multiplicative ℤ_[2]) where
  toFun t := freeTwoCoordinate (coreRank h) r.2 (t r.1)
  map_one' := map_one _
  map_mul' _ _ := map_mul _ _ _
  continuous_toFun := (freeTwoCoordinate (coreRank h) r.2).continuous_toFun.comp
    (continuous_apply r.1)

theorem exists_nPlane_allRows_same_kernelCoset {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (n : ℕ) (y t : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (u : Fin (coreRank h) → ℤ_[2]ˣ)
    (hy : ∀ j v, toAdd (freeTwoCoordinate (coreRank h) j (y v)) =
      if j = v then (u v : ℤ_[2]) else 0)
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2))
    (hhead : ∀ j, toAdd (freeTwoCoordinate (coreRank h) j (t 0)) = 0) :
    ∃ t' : Fin (coreRank h) → FreeTwoRank (coreRank h),
      t⁻¹*t' ∈ nPlaneCorrectionKernel (n+3) (by omega) y ∧
      (∀ i j, freeTwoCoordinate (coreRank h) j (t' i) = 1) ∧
      (∀ i, t' i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      levelMk (FreeTwoRank (coreRank h) : Type) (n+4) (nRelWord alpha (y*t')) =
        levelMk (FreeTwoRank (coreRank h) : Type) (n+4) (nRelWord alpha (y*t)) := by
  classical
  let H := nPlaneCorrectionKernel (n+3) (by omega) y
  let w (r : Fin (coreRank h) × Fin (coreRank h)) :
      Fin (coreRank h) → FreeTwoRank (coreRank h) :=
    if r.1 ≠ 0 then nPlaneKernelTuple n 0 1 r.1 r.2 y nPartner else 1
  let c (r : Fin (coreRank h) × Fin (coreRank h)) : ℤ_[2] :=
    if r.1 ≠ 0 then 2^(n+1) * (u r.2 : ℤ_[2]) else 0
  have hw : ∀ r, w r ∈ H := by
    intro r
    dsimp only [w]
    split_ifs with hr
    · exact nPlaneKernelTuple_mem_correctionKernel_all n y r.1 r.2 hr
    · exact H.one_mem
  have hd : ∀ r s, toAdd (fullTupleRow h r (w s)) = if r=s then c r else 0 := by
    intro r s
    by_cases hs : s.1 ≠ 0
    · rw [show w s = nPlaneKernelTuple n 0 1 s.1 s.2 y nPartner from if_pos hs]
      change toAdd (freeTwoCoordinate (coreRank h) r.2
        (nPlaneKernelTuple n 0 1 s.1 s.2 y nPartner r.1)) = _
      rw [nPlaneKernelTuple_coordinate_diagonal (coreRank h) n 0 1 s.1 s.2 y u hy]
      by_cases hrs : r = s
      · subst r; simp [c, hs]
      · have hn : ¬ (r.1 = s.1 ∧ r.2 = s.2) := fun he => hrs (Prod.ext he.1 he.2)
        simp [hrs, hn]
    · rw [show w s = 1 from if_neg hs]
      change toAdd (freeTwoCoordinate (coreRank h) r.2 1) = _
      by_cases hrs : r = s
      · subst r; simp [c, hs]
      · simp [hrs]
  have hc : ∀ r, c r ∣ toAdd (fullTupleRow h r t) := by
    intro r
    change c r ∣ toAdd (freeTwoCoordinate (coreRank h) r.2 (t r.1))
    by_cases hr : r.1 ≠ 0
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
    · have hi : r.1 = 0 := not_not.mp hr
      rw [hi, hhead]
      exact dvd_zero _
  obtain ⟨t', hcoset, hzero⟩ := exists_closedSubgroup_rowZero_same_coset_fintype
    (isProTwo_freeN_tuple h) (fullTupleRow h) H
    (isClosed_nPlaneCorrectionKernel (n+3) (by omega) y) w hw c hd t hc
  refine ⟨t', hcoset, fun i j => hzero (i,j), ?_, ?_⟩
  · intro i
    have hh := hcoset.1 i
    change (t i)⁻¹*t' i ∈ twoCentralSeries _ (n+3-1) at hh
    have he : t' i = t i*((t i)⁻¹*t' i) := by group
    rw [he]
    exact (twoCentralSeries _ (n+2)).mul_mem (ht i) (by simpa using hh)
  · have he := nRelWord_mul_correctionKernel (n+3) (by omega) alpha halpha y t (t⁻¹*t')
      (fun i => by simpa using ht i) hcoset
    simpa only [mul_inv_cancel_left] using he

#print axioms exists_nPlane_allRows_same_kernelCoset
end
end GQ2.Dyadic.MarkedCore
