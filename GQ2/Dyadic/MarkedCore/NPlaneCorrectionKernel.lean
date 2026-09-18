import GQ2.Dyadic.MarkedCore.NPlaneKernelTupleDerivative

/-!
# The closed actual N correction-kernel subgroup

This packages corrections of depth `k-1` with trivial actual N derivative.
Closedness is proved through the literal relator error, not through a
separation assumption on a quotient topology. Membership preserves a
next-level relator defect; it does not imply that any desired defect is
reachable.
-/

namespace GQ2.Dyadic.MarkedCore

open Roe.Labute

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem correction_project_mem {h k : ℕ} {t : Fin (coreRank h) → G}
    (ht : ∀ i, t i ∈ twoCentralSeries G (k - 1)) :
    ∀ i, levelMk G (k + 1) (t i) ∈ lambdaImage G (k - 1) (k + 1) :=
  fun i => ⟨t i, ht i, rfl⟩

private theorem correction_derivative_one {H : Type*} [Group H] {h : ℕ}
    (m : Fin (coreRank h) → H) : nFilteredDerivative m (1 : Fin (coreRank h) → H) = 1 := by
  simp [nFilteredDerivative, nFilteredCoreDerivative, nFilteredHandleDerivative, commP]

/-- The actual correction kernel, as a subgroup of the full tuple group.
Its carrier does not depend on alpha, since the N derivative is uniform for
all alpha at least two. -/
def nPlaneCorrectionKernel (k : ℕ) (hk : 3 ≤ k) {h : ℕ}
    (m : Fin (coreRank h) → G) : Subgroup (Fin (coreRank h) → G) where
  carrier := {t | (∀ i, t i ∈ twoCentralSeries G (k - 1)) ∧
    nFilteredDerivative (fun i => levelMk G (k + 1) (m i))
      (fun i => levelMk G (k + 1) (t i)) = 1}
  one_mem' := by
    constructor
    · intro i; exact (twoCentralSeries G (k - 1)).one_mem
    · simp only [Pi.one_apply, map_one]
      exact correction_derivative_one (h := h) (fun i => levelMk G (k + 1) (m i))
  mul_mem' := by
    intro t s ht hs
    constructor
    · intro i; exact (twoCentralSeries G (k - 1)).mul_mem (ht.1 i) (hs.1 i)
    · have he := nFilteredDerivative_mul k hk (fun i => levelMk G (k + 1) (m i))
        (fun i => levelMk G (k + 1) (t i)) (fun i => levelMk G (k + 1) (s i))
        (correction_project_mem ht.1) (correction_project_mem hs.1)
      simpa only [Pi.mul_apply, map_mul, ht.2, hs.2, one_mul] using he
  inv_mem' := by
    intro t ht
    have hi : ∀ i, (t i)⁻¹ ∈ twoCentralSeries G (k - 1) :=
      fun i => (twoCentralSeries G (k - 1)).inv_mem (ht.1 i)
    refine ⟨hi, ?_⟩
    have he := nFilteredDerivative_mul k hk (fun i => levelMk G (k + 1) (m i))
      (fun i => levelMk G (k + 1) (t i)) (fun i => levelMk G (k + 1) ((t i)⁻¹))
      (correction_project_mem ht.1) (correction_project_mem hi)
    have hleft : (fun i => levelMk G (k + 1) (t i) * levelMk G (k + 1) ((t i)⁻¹)) =
        (1 : Fin (coreRank h) → levelQuot G (k + 1)) := by
      funext i; simp
    rw [hleft, correction_derivative_one, ht.2, one_mul] at he
    exact he.symm

theorem mem_nPlaneCorrectionKernel (k : ℕ) (hk : 3 ≤ k) {h : ℕ}
    (m t : Fin (coreRank h) → G) :
    t ∈ nPlaneCorrectionKernel k hk m ↔
      (∀ i, t i ∈ twoCentralSeries G (k - 1)) ∧
        nFilteredDerivative (fun i => levelMk G (k + 1) (m i))
          (fun i => levelMk G (k + 1) (t i)) = 1 := Iff.rfl

/-- The previously constructed exact-row tuple belongs to this actual subgroup. -/
theorem nPlaneKernelTuple_mem_correctionKernel (n : ℕ) {h : ℕ}
    (m : Fin (coreRank h) → G) (i v : Fin (coreRank h)) (hi : i ≠ 0) (hv : v ≠ 1) :
    nPlaneKernelTuple n 0 1 i v m nPartner ∈ nPlaneCorrectionKernel (n + 3) (by omega) m := by
  constructor
  · intro j; simpa using nPlaneKernelTuple_mem n 0 1 i v m nPartner j
  · exact nPlaneKernelTuple_filteredDerivative n m i v hi hv

section ClosedAndRelator

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

private theorem correction_relator_shift (k : ℕ) (hk : 3 ≤ k)
    (alpha : ℕ) (halpha : 2 ≤ alpha) {h : ℕ} (m t : Fin (coreRank h) → G)
    (ht : ∀ i, t i ∈ twoCentralSeries G (k - 1)) :
    levelMk G (k + 1) (nRelWord alpha (m * t)) =
      levelMk G (k + 1) (nRelWord alpha m) *
        nFilteredDerivative (fun i => levelMk G (k + 1) (m i))
          (fun i => levelMk G (k + 1) (t i)) := by
  rw [map_nRelWord, map_nRelWord]
  simpa only [Pi.mul_apply, map_mul] using nFiltered_nRelWord k hk alpha halpha
    (fun i => levelMk G (k + 1) (m i)) (fun i => levelMk G (k + 1) (t i))
    (correction_project_mem ht)

/-- Membership is equivalently a literal next-level relator-error condition. -/
theorem mem_nPlaneCorrectionKernel_iff_error (k : ℕ) (hk : 3 ≤ k)
    (alpha : ℕ) (halpha : 2 ≤ alpha) {h : ℕ} (m t : Fin (coreRank h) → G) :
    t ∈ nPlaneCorrectionKernel k hk m ↔
      (∀ i, t i ∈ twoCentralSeries G (k - 1)) ∧
        (nRelWord alpha m)⁻¹ * nRelWord alpha (m * t) ∈ twoCentralSeries G (k + 1) := by
  rw [mem_nPlaneCorrectionKernel]
  apply and_congr_right
  intro ht
  rw [← QuotientGroup.eq_one_iff]
  change _ ↔ levelMk G (k + 1) _ = 1
  rw [map_mul, map_inv, correction_relator_shift k hk alpha halpha m t ht,
    inv_mul_cancel_left]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem correction_continuous_nRelWord (alpha : ℕ) {h : ℕ} :
    Continuous (fun m : Fin (coreRank h) → G => nRelWord alpha m) := by
  simp only [nRelWord]
  refine Continuous.mul ?_ ?_
  · simp only [nWord, commP]; fun_prop
  · simp only [handleWord]
    refine continuous_list_prod _ fun j _ => ?_
    simp only [commP]; fun_prop

/-- Closedness uses the alpha=2 representative of the common derivative,
so no arbitrary alpha parameter or quotient separation hypothesis is needed. -/
theorem isClosed_nPlaneCorrectionKernel (k : ℕ) (hk : 3 ≤ k) {h : ℕ}
    (m : Fin (coreRank h) → G) :
    IsClosed (nPlaneCorrectionKernel k hk m : Set (Fin (coreRank h) → G)) := by
  have he : (nPlaneCorrectionKernel k hk m : Set (Fin (coreRank h) → G)) =
      {t | ∀ i, t i ∈ twoCentralSeries G (k - 1)} ∩
        {t | (nRelWord 2 m)⁻¹ * nRelWord 2 (m * t) ∈ twoCentralSeries G (k + 1)} := by
    ext t
    exact mem_nPlaneCorrectionKernel_iff_error k hk 2 (by omega) m t
  rw [he]
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => (isClosed_twoCentralSeries G (k - 1)).preimage (continuous_apply i)
  · apply (isClosed_twoCentralSeries G (k + 1)).preimage
    exact continuous_const.mul
      ((correction_continuous_nRelWord 2).comp (continuous_const.mul continuous_id))

/-- Right multiplication by the closed kernel preserves the actual relator
value one level deeper, even when the first correction is not in the kernel. -/
theorem nRelWord_mul_correctionKernel (k : ℕ) (hk : 3 ≤ k)
    (alpha : ℕ) (halpha : 2 ≤ alpha) {h : ℕ} (m t z : Fin (coreRank h) → G)
    (ht : ∀ i, t i ∈ twoCentralSeries G (k - 1))
    (hz : z ∈ nPlaneCorrectionKernel k hk m) :
    levelMk G (k + 1) (nRelWord alpha (m * (t * z))) =
      levelMk G (k + 1) (nRelWord alpha (m * t)) := by
  have htz : ∀ i, (t * z) i ∈ twoCentralSeries G (k - 1) :=
    fun i => (twoCentralSeries G (k - 1)).mul_mem (ht i) (hz.1 i)
  rw [correction_relator_shift k hk alpha halpha m (t * z) htz,
    correction_relator_shift k hk alpha halpha m t ht]
  simp only [Pi.mul_apply, map_mul]
  rw [nFilteredDerivative_mul k hk _ _ _ (correction_project_mem ht)
    (correction_project_mem hz.1), hz.2, mul_one]

/-- In particular the same target-relator defect stays in the next filtration
subgroup; the target is arbitrary and is not required to vanish. -/
theorem nRelWord_defect_mul_correctionKernel_iff (k : ℕ) (hk : 3 ≤ k)
    (alpha : ℕ) (halpha : 2 ≤ alpha) {h : ℕ} (m t z : Fin (coreRank h) → G)
    (ht : ∀ i, t i ∈ twoCentralSeries G (k - 1))
    (hz : z ∈ nPlaneCorrectionKernel k hk m) (target : G) :
    nRelWord alpha (m * (t * z)) * target⁻¹ ∈ twoCentralSeries G (k + 1) ↔
      nRelWord alpha (m * t) * target⁻¹ ∈ twoCentralSeries G (k + 1) := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.eq_one_iff]
  change levelMk G (k + 1) _ = 1 ↔ levelMk G (k + 1) _ = 1
  rw [map_mul, map_mul, nRelWord_mul_correctionKernel k hk alpha halpha m t z ht hz]

end ClosedAndRelator

#print axioms nPlaneCorrectionKernel
#print axioms mem_nPlaneCorrectionKernel
#print axioms nPlaneKernelTuple_mem_correctionKernel
#print axioms mem_nPlaneCorrectionKernel_iff_error
#print axioms isClosed_nPlaneCorrectionKernel
#print axioms nRelWord_mul_correctionKernel
#print axioms nRelWord_defect_mul_correctionKernel_iff

end GQ2.Dyadic.MarkedCore
