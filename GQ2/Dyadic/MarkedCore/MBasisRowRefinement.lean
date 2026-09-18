import GQ2.Dyadic.MarkedCore.NBasisRowRefinement
import GQ2.Dyadic.Instances.StageAbstractionEvenRawSpan

/-!
# The closed derivative-kernel interpolation at the actual M word

The closed N correction-kernel subgroup `nPlaneCorrectionKernel` is defined by
the vanishing of the actual N derivative word `nFilteredDerivative`, and its
diagonal row witnesses `nBasisKernelWitness` are finite products of actual
free-group kernel tuples. Neither carries an N relator equation. This file
supplies the one adapter that makes both apply verbatim at the M word: for
`alpha >= 2`, `k >= 3` and corrections of depth `k-1`, the literal M relator
shift `(mRelWord alpha m)⁻¹ * mRelWord alpha (m*t)` in `Q_(k+1)` equals the
same derivative word. This is the composite of the two committed quotient-group
identities `evenRawStageShift_n` and `evenRawStageShift_m`; it is not a graded
analogy.

What transfers: kernel membership is equivalently a next-level M relator error
condition, right multiplication by the kernel preserves the M relator value one
level deeper, the arbitrary-basis row witnesses kill every ordinary row of a
depth correction at the M word. What does not transfer: no N relator
conclusion is asserted for the M word, the head row `t 0` is not killed here
(its cleanup is a separate coupled ordinary-row statement), and no correction
is constructed from a relator defect in this file.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative Roe.Labute

section Adapter
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The actual arbitrary-rank N derivative word is the shared even
crossed-derivation word, as elements of `Q_(k+1)`. -/
theorem mBasis_nFilteredDerivative_eq_evenRawDbarWord (k : ℕ) (hk : 3 ≤ k) {h : ℕ}
    (m t : Fin (coreRank h) → levelQuot G (k+1))
    (ht : ∀ i, t i ∈ lambdaImage G (k-1) (k+1)) :
    nFilteredDerivative m t = StageGeneric.evenRawDbarWord m t := by
  have h1 := nFiltered_nRelWord k hk 2 le_rfl m t ht
  have h2 := StageGeneric.evenRawStageShift_n (α := 2) le_rfl (by norm_num) h k hk m t ht
  change (nRelWord 2 m)⁻¹ * nRelWord 2 (fun i => m i * t i) = _ at h2
  rw [← h2, h1, inv_mul_cancel_left]

/-- **The M preservation adapter.** The literal M relator shift by a depth-`(k-1)`
correction is the N derivative word, so every statement about
`nPlaneCorrectionKernel` transfers to the M word without change. -/
theorem mBasis_mFiltered_mRelWord (k : ℕ) (hk : 3 ≤ k) (alpha : ℕ) (halpha : 2 ≤ alpha)
    {h : ℕ} (m t : Fin (coreRank h) → levelQuot G (k+1))
    (ht : ∀ i, t i ∈ lambdaImage G (k-1) (k+1)) :
    mRelWord alpha (fun i => m i * t i) = mRelWord alpha m * nFilteredDerivative m t := by
  have h2 := StageGeneric.evenRawStageShift_m halpha (by omega) h k hk m t ht
  change (mRelWord alpha m)⁻¹ * mRelWord alpha (fun i => m i * t i) = _ at h2
  rw [mBasis_nFilteredDerivative_eq_evenRawDbarWord k hk m t ht, ← h2, mul_inv_cancel_left]

/-- The M relator shift on the actual group, projected to `Q_(k+1)`. -/
theorem mBasis_relator_shift (k : ℕ) (hk : 3 ≤ k)
    (alpha : ℕ) (halpha : 2 ≤ alpha) {h : ℕ} (m t : Fin (coreRank h) → G)
    (ht : ∀ i, t i ∈ twoCentralSeries G (k - 1)) :
    levelMk G (k + 1) (mRelWord alpha (m * t)) =
      levelMk G (k + 1) (mRelWord alpha m) *
        nFilteredDerivative (fun i => levelMk G (k + 1) (m i))
          (fun i => levelMk G (k + 1) (t i)) := by
  rw [map_mRelWord, map_mRelWord]
  simpa only [Pi.mul_apply, map_mul] using mBasis_mFiltered_mRelWord k hk alpha halpha
    (fun i => levelMk G (k + 1) (m i)) (fun i => levelMk G (k + 1) (t i))
    (fun i => ⟨t i, ht i, rfl⟩)

/-- Membership in the closed N kernel is equivalently a literal next-level
M relator-error condition. -/
theorem mBasis_mem_nPlaneCorrectionKernel_iff_mError (k : ℕ) (hk : 3 ≤ k)
    (alpha : ℕ) (halpha : 2 ≤ alpha) {h : ℕ} (m t : Fin (coreRank h) → G) :
    t ∈ nPlaneCorrectionKernel k hk m ↔
      (∀ i, t i ∈ twoCentralSeries G (k - 1)) ∧
        (mRelWord alpha m)⁻¹ * mRelWord alpha (m * t) ∈ twoCentralSeries G (k + 1) := by
  rw [mem_nPlaneCorrectionKernel]
  apply and_congr_right
  intro ht
  rw [← QuotientGroup.eq_one_iff]
  change _ ↔ levelMk G (k + 1) _ = 1
  rw [map_mul, map_inv, mBasis_relator_shift k hk alpha halpha m t ht,
    inv_mul_cancel_left]

/-- Right multiplication by the closed kernel preserves the actual M relator
value one level deeper, even when the first correction is not in the kernel. -/
theorem mBasis_mRelWord_mul_correctionKernel (k : ℕ) (hk : 3 ≤ k)
    (alpha : ℕ) (halpha : 2 ≤ alpha) {h : ℕ} (m t z : Fin (coreRank h) → G)
    (ht : ∀ i, t i ∈ twoCentralSeries G (k - 1))
    (hz : z ∈ nPlaneCorrectionKernel k hk m) :
    levelMk G (k + 1) (mRelWord alpha (m * (t * z))) =
      levelMk G (k + 1) (mRelWord alpha (m * t)) := by
  have htz : ∀ i, (t * z) i ∈ twoCentralSeries G (k - 1) :=
    fun i => (twoCentralSeries G (k - 1)).mul_mem (ht i) (hz.1 i)
  have hproj : ∀ (s : Fin (coreRank h) → G), (∀ i, s i ∈ twoCentralSeries G (k - 1)) →
      ∀ i, levelMk G (k + 1) (s i) ∈ lambdaImage G (k - 1) (k + 1) :=
    fun s hs i => ⟨s i, hs i, rfl⟩
  rw [mBasis_relator_shift k hk alpha halpha m (t * z) htz,
    mBasis_relator_shift k hk alpha halpha m t ht]
  simp only [Pi.mul_apply, map_mul]
  rw [nFilteredDerivative_mul k hk (fun i => levelMk G (k + 1) (m i))
    (fun i => levelMk G (k + 1) (t i)) (fun i => levelMk G (k + 1) (z i))
    (hproj t ht) (hproj z hz.1), hz.2, mul_one]

/-- The same target-relative M defect stays in the next filtration subgroup;
the target is arbitrary and is not required to vanish. -/
theorem mBasis_mRelWord_defect_mul_correctionKernel_iff (k : ℕ) (hk : 3 ≤ k)
    (alpha : ℕ) (halpha : 2 ≤ alpha) {h : ℕ} (m t z : Fin (coreRank h) → G)
    (ht : ∀ i, t i ∈ twoCentralSeries G (k - 1))
    (hz : z ∈ nPlaneCorrectionKernel k hk m) (target : G) :
    mRelWord alpha (m * (t * z)) * target⁻¹ ∈ twoCentralSeries G (k + 1) ↔
      mRelWord alpha (m * t) * target⁻¹ ∈ twoCentralSeries G (k + 1) := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.eq_one_iff]
  change levelMk G (k + 1) _ = 1 ↔ levelMk G (k + 1) _ = 1
  rw [map_mul, map_mul, mBasis_mRelWord_mul_correctionKernel k hk alpha halpha m t z ht hz]

end Adapter

section Slack
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Top-layer slack is invisible in the actual M relator: replacing correction
representatives modulo `lambda_k` keeps the relator value modulo `lambda_(k+1)`.
This is the committed central-shift invariance of the M word datum. -/
theorem mBasis_mRelWord_correction_level_congr {alpha h : ℕ} (halpha : 1 ≤ alpha) (k : ℕ)
    (m t t' : Fin (coreRank h) → G)
    (hslack : ∀ i, (t i)⁻¹ * t' i ∈ twoCentralSeries G k) :
    levelMk G (k+1) (mRelWord alpha (fun i => m i * t' i)) =
      levelMk G (k+1) (mRelWord alpha (fun i => m i * t i)) := by
  rw [map_mRelWord, map_mRelWord]
  simp only [map_mul]
  have hz : ∀ i, levelMk G (k+1) ((t i)⁻¹ * t' i) ∈ zLayer G k :=
    fun i => ⟨(t i)⁻¹ * t' i, hslack i, rfl⟩
  have he := (StageGeneric.mStageWord alpha h halpha).zshift
    (fun i => levelMk G (k+1) ((t i)⁻¹ * t' i))
    (fun i => levelMk G (k+1) (m i) * levelMk G (k+1) (t i)) hz
  change mRelWord alpha (fun i => levelMk G (k+1) ((t i)⁻¹ * t' i) *
    (levelMk G (k+1) (m i) * levelMk G (k+1) (t i))) =
    mRelWord alpha (fun i => levelMk G (k+1) (m i) * levelMk G (k+1) (t i)) at he
  rw [← he]
  congr 1
  funext i
  rw [(zLayer_commute (hz i) _).eq, map_mul, map_inv]
  group

/-- The literal target-relative M defect membership is representative
independent modulo one level of slack. -/
theorem mBasis_mRelWord_correction_defect_mem_iff {alpha h : ℕ} (halpha : 1 ≤ alpha) (k : ℕ)
    (m t t' : Fin (coreRank h) → G) (target : G)
    (hslack : ∀ i, (t i)⁻¹ * t' i ∈ twoCentralSeries G k) :
    (mRelWord alpha (fun i => m i * t' i) * target⁻¹ ∈ twoCentralSeries G (k+1)) ↔
      (mRelWord alpha (fun i => m i * t i) * target⁻¹ ∈ twoCentralSeries G (k+1)) := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.eq_one_iff]
  change levelMk G (k+1) _ = 1 ↔ levelMk G (k+1) _ = 1
  rw [map_mul, map_mul, mBasis_mRelWord_correction_level_congr halpha k m t t' hslack]

end Slack

/-- **The closed derivative-kernel interpolation at the M word, arbitrary basis.**
Every depth-correction tuple whose head ordinary rows already vanish has an
exact all-row-zero representative in its actual derivative-kernel coset, and
the M relator value one level deeper is unchanged. The current marking is any
genuine free basis; no diagonal-matrix restriction and no N relator equation. -/
theorem exists_mBasis_allRows_same_kernelCoset {alpha h : ℕ} (halpha : 2 ≤ alpha)
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
          (mRelWord alpha ((fun i => e (freeTwoRankGen (coreRank h) i))*t')) =
        levelMk (FreeTwoRank (coreRank h) : Type) (n+4)
          (mRelWord alpha ((fun i => e (freeTwoRankGen (coreRank h) i))*t)) := by
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
  · have he := mBasis_mRelWord_mul_correctionKernel (n+3) (by omega) alpha halpha y t (t⁻¹*t')
      (fun i => by simpa using ht i) hcoset
    simpa only [mul_inv_cancel_left] using he

#print axioms mBasis_nFilteredDerivative_eq_evenRawDbarWord
#print axioms mBasis_mFiltered_mRelWord
#print axioms mBasis_relator_shift
#print axioms mBasis_mem_nPlaneCorrectionKernel_iff_mError
#print axioms mBasis_mRelWord_mul_correctionKernel
#print axioms mBasis_mRelWord_defect_mul_correctionKernel_iff
#print axioms mBasis_mRelWord_correction_level_congr
#print axioms mBasis_mRelWord_correction_defect_mem_iff
#print axioms exists_mBasis_allRows_same_kernelCoset

end
end GQ2.Dyadic.MarkedCore
