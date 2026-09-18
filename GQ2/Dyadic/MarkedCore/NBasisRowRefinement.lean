import GQ2.Dyadic.MarkedCore.NPlaneFullRowRefinement

/-!
# Exact correction rows at an arbitrary current free basis

The inverse automorphism supplies the inverse of the current ordinary-coordinate
matrix. Finite ordered products of the actual derivative-kernel tuples, raised
to these inverse-coordinate exponents, give diagonal row witnesses. Thus the
row-clearing theorem needs an actual free basis, not a diagonal matrix or
separately supplied inverse. No initial-stage or derivative-image assertion is
made here.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

/-- The inverse-coordinate matrix identity, derived from the actual inverse
automorphism. Columns are generator images; the displayed scalar sum is the
`(j,k)` entry of A B, with the commuting factors written B first. -/
theorem freeTwo_basis_inverse_coordinates (N : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank N : Type) (FreeTwoRank N : Type))
    (j k : Fin N) :
    (∑ v, toAdd (freeTwoCoordinate N v (e.symm (freeTwoRankGen N k))) *
      toAdd (freeTwoCoordinate N j (e (freeTwoRankGen N v)))) =
      if j = k then 1 else 0 := by
  let f := (freeTwoCoordinate N j).comp (autHom e)
  have he := freeTwo_character_coordinates N f (e.symm (freeTwoRankGen N k))
  change toAdd (freeTwoCoordinate N j (e (e.symm (freeTwoRankGen N k)))) =
    ∑ v, toAdd (freeTwoCoordinate N v (e.symm (freeTwoRankGen N k))) *
      toAdd (freeTwoCoordinate N j (e (freeTwoRankGen N v))) at he
  rw [e.apply_symm_apply, freeTwoCoordinate_gen, toAdd_ofAdd] at he
  simpa only [eq_comm] using he.symm

def nBasisTupleRow (h : ℕ) (r : Fin (coreRank h) × Fin (coreRank h)) :
    ContinuousMonoidHom (Fin (coreRank h) → FreeTwoRank (coreRank h))
      (Multiplicative ℤ_[2]) where
  toFun t := freeTwoCoordinate (coreRank h) r.2 (t r.1)
  map_one' := map_one _
  map_mul' _ _ := map_mul _ _ _
  continuous_toFun := (freeTwoCoordinate (coreRank h) r.2).continuous_toFun.comp
    (continuous_apply r.1)

/-- A finite ordered product, not an infinite product or a commutative-group
construction. The coefficient is read from the genuine inverse basis. -/
def nBasisKernelWitness {h : ℕ} (n : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type)) (i k : Fin (coreRank h)) :
    Fin (coreRank h) → FreeTwoRank (coreRank h) :=
  (List.ofFn fun v => zpowZtwo (isProTwo_freeN_tuple h)
    (nPlaneKernelTuple n 0 1 i v (fun w => e (freeTwoRankGen (coreRank h) w)) nPartner)
    (toAdd (freeTwoCoordinate (coreRank h) v (e.symm (freeTwoRankGen (coreRank h) k))))).prod

private theorem basis_zpow_mem_closed {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (H : Subgroup P) (hH : IsClosed (H : Set P))
    (x : P) (hx : x ∈ H) (a : ℤ_[2]) : zpowZtwo hP x a ∈ H := by
  refine PadicInt.denseRange_natCast.induction_on a ?_ ?_
  · exact hH.preimage (continuous_zpowZtwo hP x)
  · intro k
    rw [zpowZtwo_natCast]
    exact H.pow_mem hx k

theorem nBasisKernelWitness_mem {h : ℕ} (n : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type)) (i k : Fin (coreRank h)) (hi : i ≠ 0) :
    nBasisKernelWitness n e i k ∈ nPlaneCorrectionKernel (n+3) (by omega)
      (fun w => e (freeTwoRankGen (coreRank h) w)) := by
  let H := nPlaneCorrectionKernel (n+3) (by omega)
    (fun w => e (freeTwoRankGen (coreRank h) w))
  apply H.list_prod_mem
  intro x hx
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hx
  exact basis_zpow_mem_closed (isProTwo_freeN_tuple h) H
    (isClosed_nPlaneCorrectionKernel (n+3) (by omega) _) _
    (nPlaneKernelTuple_mem_correctionKernel_all n _ i v hi) _

/-- Exact diagonal ordinary rows at an arbitrary current basis. This is where
the inverse-coordinate identity removes the former diagonal-unit hypothesis. -/
theorem nBasisKernelWitness_row {h : ℕ} (n : ℕ)
    (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type)) (i k j l : Fin (coreRank h)) :
    toAdd (nBasisTupleRow h (j,l) (nBasisKernelWitness n e i k)) =
      if j = i ∧ l = k then (2^(n+1) : ℤ_[2]) else 0 := by
  classical
  rw [nBasisKernelWitness, map_list_prod, List.map_ofFn, Fin.prod_ofFn, toAdd_prod]
  change (∑ v, toAdd (nBasisTupleRow h (j,l)
    (zpowZtwo (isProTwo_freeN_tuple h)
      (nPlaneKernelTuple n 0 1 i v (fun w => e (freeTwoRankGen (coreRank h) w)) nPartner)
      (toAdd (freeTwoCoordinate (coreRank h) v (e.symm (freeTwoRankGen (coreRank h) k))))))) = _
  simp_rw [toAdd_map_zpowZtwo]
  have hr (v : Fin (coreRank h)) :
      toAdd (nBasisTupleRow h (j,l)
        (nPlaneKernelTuple n 0 1 i v (fun w => e (freeTwoRankGen (coreRank h) w)) nPartner)) =
        if j = i then (2^(n+1) : ℤ_[2]) *
          toAdd (freeTwoCoordinate (coreRank h) l (e (freeTwoRankGen (coreRank h) v))) else 0 :=
    nPlaneKernelTuple_character (freeTwoCoordinate (coreRank h) l).toMonoidHom
      n 0 1 i v _ nPartner j
  simp_rw [hr]
  by_cases hji : j = i
  · simp only [hji, true_and]
    calc
      (∑ v, toAdd (freeTwoCoordinate (coreRank h) v (e.symm (freeTwoRankGen (coreRank h) k))) *
          ((2 : ℤ_[2])^(n+1) * toAdd (freeTwoCoordinate (coreRank h) l
            (e (freeTwoRankGen (coreRank h) v))))) =
          (2 : ℤ_[2])^(n+1) * ∑ v,
            toAdd (freeTwoCoordinate (coreRank h) v (e.symm (freeTwoRankGen (coreRank h) k))) *
              toAdd (freeTwoCoordinate (coreRank h) l (e (freeTwoRankGen (coreRank h) v))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by rw [freeTwo_basis_inverse_coordinates]; split_ifs <;> simp
  · simp [hji]

/-- Every depth-correction tuple whose head ordinary rows already vanish has
an exact all-row-zero representative in its actual derivative-kernel coset.
The current marking is any genuine free basis, with no matrix restriction. -/
theorem exists_nBasis_allRows_same_kernelCoset {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (n : ℕ) (e : ContinuousMulEquiv (FreeTwoRank (coreRank h) : Type)
      (FreeTwoRank (coreRank h) : Type))
    (t : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (ht : ∀ i, t i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2))
    (hhead : ∀ j, toAdd (freeTwoCoordinate (coreRank h) j (t 0)) = 0) :
    ∃ t' : Fin (coreRank h) → FreeTwoRank (coreRank h),
      t⁻¹*t' ∈ nPlaneCorrectionKernel (n+3) (by omega)
        (fun i => e (freeTwoRankGen (coreRank h) i)) ∧
      (∀ i j, freeTwoCoordinate (coreRank h) j (t' i) = 1) ∧
      (∀ i, t' i ∈ twoCentralSeries (FreeTwoRank (coreRank h) : Type) (n+2)) ∧
      levelMk (FreeTwoRank (coreRank h) : Type) (n+4)
          (nRelWord alpha ((fun i => e (freeTwoRankGen (coreRank h) i))*t')) =
        levelMk (FreeTwoRank (coreRank h) : Type) (n+4)
          (nRelWord alpha ((fun i => e (freeTwoRankGen (coreRank h) i))*t)) := by
  classical
  let y := fun i => e (freeTwoRankGen (coreRank h) i)
  let H := nPlaneCorrectionKernel (n+3) (by omega) y
  let w (r : Fin (coreRank h) × Fin (coreRank h)) :=
    if r.1 ≠ 0 then nBasisKernelWitness n e r.1 r.2 else 1
  let c (r : Fin (coreRank h) × Fin (coreRank h)) : ℤ_[2] :=
    if r.1 ≠ 0 then 2^(n+1) else 0
  have hw : ∀ r, w r ∈ H := by
    intro r
    dsimp only [w]
    split_ifs with hr
    · exact nBasisKernelWitness_mem n e r.1 r.2 hr
    · exact H.one_mem
  have hd : ∀ r s, toAdd (nBasisTupleRow h r (w s)) = if r=s then c r else 0 := by
    intro r s
    by_cases hs : s.1 ≠ 0
    · rw [show w s = nBasisKernelWitness n e s.1 s.2 from if_pos hs,
        show nBasisTupleRow h r = nBasisTupleRow h (r.1,r.2) from rfl,
        nBasisKernelWitness_row]
      by_cases hrs : r = s
      · subst r; simp [c, hs]
      · have hn : ¬ (r.1 = s.1 ∧ r.2 = s.2) := fun he => hrs (Prod.ext he.1 he.2)
        simp [hrs, hn]
    · rw [show w s = 1 from if_neg hs, map_one, toAdd_one]
      by_cases hrs : r = s
      · subst r; simp [c, hs]
      · simp [hrs]
  have hc : ∀ r, c r ∣ toAdd (nBasisTupleRow h r t) := by
    intro r
    change c r ∣ toAdd (freeTwoCoordinate (coreRank h) r.2 (t r.1))
    by_cases hr : r.1 ≠ 0
    · dsimp only [c]
      rw [if_pos hr]
      exact twoCentralSeries_z2_character_dvd_succ (freeTwoCoordinate (coreRank h) r.2) (ht r.1)
    · have hi : r.1 = 0 := not_not.mp hr
      rw [hi, hhead]
      exact dvd_zero _
  obtain ⟨t', hcoset, hzero⟩ := exists_closedSubgroup_rowZero_same_coset_fintype
    (isProTwo_freeN_tuple h) (nBasisTupleRow h) H
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

#print axioms freeTwo_basis_inverse_coordinates
#print axioms nBasisTupleRow
#print axioms nBasisKernelWitness
#print axioms nBasisKernelWitness_mem
#print axioms nBasisKernelWitness_row
#print axioms exists_nBasis_allRows_same_kernelCoset

end
end GQ2.Dyadic.MarkedCore
