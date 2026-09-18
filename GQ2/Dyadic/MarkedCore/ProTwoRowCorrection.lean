import GQ2.Dyadic.MarkedCore.FreeProTwoCharacterCorrection

/-!
# Exact finite-row correction inside a closed pro-two subgroup

Diagonal row witnesses in a closed subgroup can be raised to arbitrary Z2
exponents to match all divisible row values simultaneously. No freeness,
normality of the subgroup, or identification of an abelianization is needed.
For a relative N stage, constructing the actual derivative-kernel subgroup
and verifying the diagonal witnesses remain separate obligations.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

private theorem rowCorrection_zpow_mem (hP : IsProP 2 P)
    (H : Subgroup P) (hH : IsClosed (H : Set P)) (x : P) (hx : x ∈ H)
    (a : ℤ_[2]) : zpowZtwo hP x a ∈ H := by
  refine PadicInt.denseRange_natCast.induction_on a ?_ ?_
  · exact hH.preimage (continuous_zpowZtwo hP x)
  · intro n
    rw [zpowZtwo_natCast]
    exact H.pow_mem hx n

/-- Simultaneous row interpolation by an element of the specified closed
subgroup. The diagonal scales need not be units or nonzero. -/
theorem exists_closedSubgroup_same_rows (hP : IsProP 2 P) (n : ℕ)
    (rows : Fin n → ContinuousMonoidHom P (Multiplicative ℤ_[2]))
    (H : Subgroup P) (hH : IsClosed (H : Set P))
    (w : Fin n → P) (hw : ∀ j, w j ∈ H) (c : Fin n → ℤ_[2])
    (hdiag : ∀ i j, toAdd (rows i (w j)) = if i=j then c i else 0)
    (x : P) (hrow : ∀ i, c i ∣ toAdd (rows i x)) :
    ∃ z : P, z ∈ H ∧ ∀ i, rows i z = rows i x := by
  choose a ha using hrow
  let z : P := (List.ofFn fun j => zpowZtwo hP (w j) (a j)).prod
  refine ⟨z, ?_, ?_⟩
  · apply H.list_prod_mem
    intro y hy
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    exact rowCorrection_zpow_mem hP H hH (w j) (hw j) (a j)
  · intro i
    apply toAdd.injective
    change toAdd (rows i ((List.ofFn fun j => zpowZtwo hP (w j) (a j)).prod)) = _
    rw [map_list_prod, List.map_ofFn, Fin.prod_ofFn, toAdd_prod]
    have he : (∑ j, toAdd (rows i (zpowZtwo hP (w j) (a j)))) =
        ∑ j, a j * toAdd (rows i (w j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact toAdd_map_zpowZtwo hP (rows i) (w j) (a j)
    change (∑ j, toAdd (rows i (zpowZtwo hP (w j) (a j)))) = _
    rw [he]
    simp only [hdiag, mul_ite, mul_zero]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
      exact (mul_comm _ _).trans (ha i).symm
    · intro j _ hji
      rw [if_neg (Ne.symm hji)]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))

/-- Exact zero-row representative in the same right H-coset, simultaneously
for every listed row. Normality of H is not required. -/
theorem exists_closedSubgroup_rowZero_same_coset (hP : IsProP 2 P) (n : ℕ)
    (rows : Fin n → ContinuousMonoidHom P (Multiplicative ℤ_[2]))
    (H : Subgroup P) (hH : IsClosed (H : Set P))
    (w : Fin n → P) (hw : ∀ j, w j ∈ H) (c : Fin n → ℤ_[2])
    (hdiag : ∀ i j, toAdd (rows i (w j)) = if i=j then c i else 0)
    (x : P) (hrow : ∀ i, c i ∣ toAdd (rows i x)) :
    ∃ x' : P, x⁻¹*x' ∈ H ∧ ∀ i, rows i x' = 1 := by
  obtain ⟨z, hz, hsame⟩ := exists_closedSubgroup_same_rows hP n rows H hH w hw c hdiag x hrow
  refine ⟨x*z⁻¹, ?_, ?_⟩
  · rw [inv_mul_cancel_left]
    exact H.inv_mem hz
  · intro i
    rw [map_mul, map_inv, hsame, mul_inv_cancel]

#print axioms exists_closedSubgroup_same_rows
#print axioms exists_closedSubgroup_rowZero_same_coset

section FiniteIndex
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The same interpolation for any finite row family, including product-indexed
tuple-coordinate rows. The enumeration is constructed, not an extra premise. -/
theorem exists_closedSubgroup_same_rows_fintype (hP : IsProP 2 P)
    (rows : I → ContinuousMonoidHom P (Multiplicative ℤ_[2]))
    (H : Subgroup P) (hH : IsClosed (H : Set P))
    (w : I → P) (hw : ∀ j, w j ∈ H) (c : I → ℤ_[2])
    (hdiag : ∀ i j, toAdd (rows i (w j)) = if i=j then c i else 0)
    (x : P) (hrow : ∀ i, c i ∣ toAdd (rows i x)) :
    ∃ z : P, z ∈ H ∧ ∀ i, rows i z = rows i x := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hd : ∀ i j, toAdd (rows (e.symm i) (w (e.symm j))) =
      if i=j then c (e.symm i) else 0 := by
    intro i j
    rw [hdiag]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  obtain ⟨z, hz, hsame⟩ := exists_closedSubgroup_same_rows hP (Fintype.card I)
    (fun i => rows (e.symm i)) H hH (fun i => w (e.symm i)) (fun i => hw (e.symm i))
    (fun i => c (e.symm i)) hd x (fun i => hrow (e.symm i))
  exact ⟨z, hz, fun i => by simpa only [e.symm_apply_apply] using hsame (e i)⟩

theorem exists_closedSubgroup_rowZero_same_coset_fintype (hP : IsProP 2 P)
    (rows : I → ContinuousMonoidHom P (Multiplicative ℤ_[2]))
    (H : Subgroup P) (hH : IsClosed (H : Set P))
    (w : I → P) (hw : ∀ j, w j ∈ H) (c : I → ℤ_[2])
    (hdiag : ∀ i j, toAdd (rows i (w j)) = if i=j then c i else 0)
    (x : P) (hrow : ∀ i, c i ∣ toAdd (rows i x)) :
    ∃ x' : P, x⁻¹*x' ∈ H ∧ ∀ i, rows i x' = 1 := by
  obtain ⟨z, hz, hsame⟩ := exists_closedSubgroup_same_rows_fintype hP rows H hH w hw c hdiag x hrow
  refine ⟨x*z⁻¹, ?_, ?_⟩
  · rw [inv_mul_cancel_left]
    exact H.inv_mem hz
  · intro i
    rw [map_mul, map_inv, hsame, mul_inv_cancel]

end FiniteIndex

#print axioms exists_closedSubgroup_same_rows_fintype
#print axioms exists_closedSubgroup_rowZero_same_coset_fintype

end
end GQ2.Dyadic.MarkedCore
