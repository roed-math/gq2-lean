import GQ2.Dyadic.MarkedCore.FreeProTwoCharacterCorrection
import GQ2.Dyadic.MarkedCore.FreeNOrientation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Integral matrices realized by actual free pro-two bases

The column `A j i` is the ordinary coordinate `j` of the image of generator `i`.
The free endomorphism sends each generator to the ordered coordinate word of
its column. A right inverse for `A` makes this endomorphism surjective in every
index-two quotient; the pro-two Frattini criterion and profinite Hopficity then
make it an actual continuous automorphism.

The endomorphism associated to an inverse matrix is NOT asserted to be the
nonabelian inverse automorphism. Only its ordinary coordinates are used.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative

theorem freeTwoCoordinateWord_coordinate (n : ℕ) (a : Fin n → ℤ_[2]) (j : Fin n) :
    toAdd (freeTwoCoordinate n j (freeTwoCoordinateWord n a)) = a j := by
  rw [freeTwoCoordinateWord_character]
  simp [freeTwoCoordinate_gen]

theorem freeTwoCoordinateWord_single (n : ℕ) (i : Fin n) (z : ℤ_[2]) :
    freeTwoCoordinateWord n (fun j => if j = i then z else 0) =
      zpowZtwo (isProP_presPro2 1) (freeTwoRankGen n i) z := by
  rw [freeTwoCoordinateWord, List.ofFn_eq_map,
    List.prod_map_eq_pow_single i _ (fun j hji _ => by
      rw [if_neg hji, zpowZtwo_zero_exp]), List.count_finRange, pow_one, if_pos rfl]

theorem freeTwoCoordinateWord_basis (n : ℕ) (i : Fin n) :
    freeTwoCoordinateWord n (fun j => if j = i then 1 else 0) = freeTwoRankGen n i := by
  rw [freeTwoCoordinateWord_single, zpowZtwo_one_exp]

/-- Exact coordinates detect equality after every commutative pro-two map. -/
theorem freeTwo_commutative_eq_of_coordinates
    {Q : Type} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hQ : IsProP 2 Q) (n : ℕ) (x y : FreeTwoRank n)
    (hxy : ∀ j, toAdd (freeTwoCoordinate n j x) = toAdd (freeTwoCoordinate n j y))
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) Q) : f x = f y := by
  rw [freeTwo_commutative_hom_coordinates hQ n f x,
    freeTwo_commutative_hom_coordinates hQ n f y]
  exact Finset.prod_congr rfl (fun j _ => congrArg _ (hxy j))

def freeTwoMatrixHom (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ_[2]) :
    ContinuousMonoidHom (FreeTwoRank n : Type) (FreeTwoRank n : Type) :=
  presLiftHom 1 (isProP_presPro2 1)
    (fun i => freeTwoCoordinateWord n (fun j => A j i)) (map_one _)

theorem freeTwoMatrixHom_gen (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ_[2]) (i : Fin n) :
    freeTwoMatrixHom n A (freeTwoRankGen n i) =
      freeTwoCoordinateWord n (fun j => A j i) := presLiftHom_gen _ _ _ _ _

theorem freeTwoMatrixHom_coordinate_gen (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ_[2]) (j i : Fin n) :
    toAdd (freeTwoCoordinate n j (freeTwoMatrixHom n A (freeTwoRankGen n i))) = A j i := by
  rw [freeTwoMatrixHom_gen, freeTwoCoordinateWord_coordinate]

theorem freeTwoMatrixHom_coordinate (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ_[2]) (x : FreeTwoRank n) (j : Fin n) :
    toAdd (freeTwoCoordinate n j (freeTwoMatrixHom n A x)) =
      ∑ i, A j i * toAdd (freeTwoCoordinate n i x) := by
  have he := freeTwo_character_coordinates n
    ((freeTwoCoordinate n j).comp (freeTwoMatrixHom n A)) x
  change toAdd (freeTwoCoordinate n j (freeTwoMatrixHom n A x)) = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  change toAdd (freeTwoCoordinate n i x) *
    toAdd (freeTwoCoordinate n j (freeTwoMatrixHom n A (freeTwoRankGen n i))) = _
  rw [freeTwoMatrixHom_coordinate_gen, mul_comm]

theorem freeTwoMatrixHom_comp_coordinate_gen (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ_[2]) (j i : Fin n) :
    toAdd (freeTwoCoordinate n j
      (freeTwoMatrixHom n A (freeTwoMatrixHom n B (freeTwoRankGen n i)))) = (A * B) j i := by
  rw [freeTwoMatrixHom_coordinate]
  simp only [freeTwoMatrixHom_coordinate_gen, Matrix.mul_apply]

theorem freeTwoMatrixHom_surjective_of_rightInverse (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ_[2]) (hAB : A * B = 1) :
    Function.Surjective (freeTwoMatrixHom n A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_index_p_quotient_surjective (isProP_presPro2 1) _ ?_
  intro M hM
  letI : Finite ((FreeTwoRank n : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hc : Nat.card ((FreeTwoRank n : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  haveI : IsCyclic ((FreeTwoRank n : Type) ⧸ M.toSubgroup) := isCyclic_of_prime_card hc
  letI : CommGroup ((FreeTwoRank n : Type) ⧸ M.toSubgroup) := IsCyclic.commGroup
  let q : ContinuousMonoidHom (FreeTwoRank n : Type)
      ((FreeTwoRank n : Type) ⧸ M.toSubgroup) :=
    ⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩
  have hQ : IsProP 2 ((FreeTwoRank n : Type) ⧸ M.toSubgroup) :=
    isProP_of_isPGroup ((isProP_presPro2 1) M)
  have he : (q.comp (freeTwoMatrixHom n A)).comp (freeTwoMatrixHom n B) = q := by
    apply presPro2_hom_ext
    intro i
    apply freeTwo_commutative_eq_of_coordinates hQ n _ _ ?_ q
    intro j
    change toAdd (freeTwoCoordinate n j
      (freeTwoMatrixHom n A (freeTwoMatrixHom n B (freeTwoRankGen n i)))) =
      toAdd (freeTwoCoordinate n j (freeTwoRankGen n i))
    rw [freeTwoMatrixHom_comp_coordinate_gen, hAB, freeTwoCoordinate_gen]
    simp [Matrix.one_apply, eq_comm]
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M.toSubgroup z
  refine ⟨freeTwoMatrixHom n B x, ?_⟩
  exact congrArg (fun f : ContinuousMonoidHom _ _ => f x) he

private theorem matrixBasis_topGen (n : ℕ) :
    ∃ s : Finset (FreeTwoRank n : Type),
      (Subgroup.closure (s : Set (FreeTwoRank n : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (freeTwoRankGen n), ?_⟩
  have hs : (↑(Finset.univ.image (freeTwoRankGen n)) : Set (FreeTwoRank n : Type)) =
      Set.range (freeTwoRankGen n) := by simp
  rw [hs]
  exact presPro2_topGen _

def freeTwoMatrixEquivOfRightInverse (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ_[2]) (hAB : A * B = 1) :
    ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type) :=
  continuousMulEquivOfBijective (freeTwoMatrixHom n A)
    ⟨profinite_hopfian (matrixBasis_topGen n) _
        (freeTwoMatrixHom_surjective_of_rightInverse n A B hAB),
      freeTwoMatrixHom_surjective_of_rightInverse n A B hAB⟩

theorem freeTwoMatrixEquivOfRightInverse_gen (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ_[2]) (hAB : A * B = 1) (i : Fin n) :
    freeTwoMatrixEquivOfRightInverse n A B hAB (freeTwoRankGen n i) =
      freeTwoCoordinateWord n (fun j => A j i) := freeTwoMatrixHom_gen n A i

theorem freeTwoMatrixEquivOfRightInverse_coordinate_gen (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ_[2]) (hAB : A * B = 1) (j i : Fin n) :
    toAdd (freeTwoCoordinate n j
      (freeTwoMatrixEquivOfRightInverse n A B hAB (freeTwoRankGen n i))) = A j i :=
  freeTwoMatrixHom_coordinate_gen n A j i

theorem freeTwoMatrixEquivOfRightInverse_coordinate (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ_[2]) (hAB : A * B = 1)
    (x : FreeTwoRank n) (j : Fin n) :
    toAdd (freeTwoCoordinate n j (freeTwoMatrixEquivOfRightInverse n A B hAB x)) =
      ∑ i, A j i * toAdd (freeTwoCoordinate n i x) := freeTwoMatrixHom_coordinate n A x j

/-- An identity column fixes the actual generator, not just its coordinates. -/
theorem freeTwoMatrixEquivOfRightInverse_gen_of_column (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ_[2]) (hAB : A * B = 1) (i : Fin n)
    (hi : ∀ j, A j i = if j = i then 1 else 0) :
    freeTwoMatrixEquivOfRightInverse n A B hAB (freeTwoRankGen n i) = freeTwoRankGen n i := by
  rw [freeTwoMatrixEquivOfRightInverse_gen]
  simpa only [hi] using freeTwoCoordinateWord_basis n i

/-- An identity row preserves that ordinary character on every group element. -/
theorem freeTwoMatrixEquivOfRightInverse_coordinate_of_row (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ_[2]) (hAB : A * B = 1) (j : Fin n)
    (hj : ∀ i, A j i = if i = j then 1 else 0) (x : FreeTwoRank n) :
    toAdd (freeTwoCoordinate n j (freeTwoMatrixEquivOfRightInverse n A B hAB x)) =
      toAdd (freeTwoCoordinate n j x) := by
  rw [freeTwoMatrixEquivOfRightInverse_coordinate]
  simp [hj]

/-- In the N application the exact b-row is the complete orientation condition;
no alpha bound or assumption about the relator is needed for this adapter. -/
theorem freeNOrientation_matrixEquiv (α h : ℕ)
    (A B : Matrix (Fin (coreRank h)) (Fin (coreRank h)) ℤ_[2]) (hAB : A * B = 1)
    (hb : ∀ i, A 1 i = if i = 1 then 1 else 0) (x : FreeTwoRank (coreRank h)) :
    freeNOrientation α h (freeTwoMatrixEquivOfRightInverse (coreRank h) A B hAB x) =
      freeNOrientation α h x := by
  rw [freeNOrientation_coordinate, freeNOrientation_coordinate,
    freeTwoMatrixEquivOfRightInverse_coordinate_of_row (coreRank h) A B hAB 1 hb x]

/-- Every invertible integral matrix is realized by an actual free pro-two
automorphism, with its prescribed columns exactly (not merely modulo two). -/
theorem exists_freeTwoMatrixBasis_of_rightInverse (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ_[2]) (hAB : A * B = 1) :
    ∃ e : ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type),
      (∀ i, e (freeTwoRankGen n i) = freeTwoCoordinateWord n (fun j => A j i)) ∧
      ∀ j i, toAdd (freeTwoCoordinate n j (e (freeTwoRankGen n i))) = A j i :=
  ⟨freeTwoMatrixEquivOfRightInverse n A B hAB,
    freeTwoMatrixEquivOfRightInverse_gen n A B hAB,
    freeTwoMatrixEquivOfRightInverse_coordinate_gen n A B hAB⟩

theorem exists_freeTwoMatrixBasis_of_isUnit_det (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ_[2]) (hA : IsUnit A.det) :
    ∃ e : ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type),
      (∀ i, e (freeTwoRankGen n i) = freeTwoCoordinateWord n (fun j => A j i)) ∧
      ∀ j i, toAdd (freeTwoCoordinate n j (e (freeTwoRankGen n i))) = A j i :=
  exists_freeTwoMatrixBasis_of_rightInverse n A A⁻¹ (Matrix.mul_nonsing_inv A hA)

#print axioms freeTwoCoordinateWord_coordinate
#print axioms freeTwoCoordinateWord_single
#print axioms freeTwoCoordinateWord_basis
#print axioms freeTwo_commutative_eq_of_coordinates
#print axioms freeTwoMatrixHom
#print axioms freeTwoMatrixHom_gen
#print axioms freeTwoMatrixHom_coordinate_gen
#print axioms freeTwoMatrixHom_coordinate
#print axioms freeTwoMatrixHom_comp_coordinate_gen
#print axioms freeTwoMatrixHom_surjective_of_rightInverse
#print axioms freeTwoMatrixEquivOfRightInverse
#print axioms freeTwoMatrixEquivOfRightInverse_gen
#print axioms freeTwoMatrixEquivOfRightInverse_coordinate_gen
#print axioms freeTwoMatrixEquivOfRightInverse_coordinate
#print axioms freeTwoMatrixEquivOfRightInverse_gen_of_column
#print axioms freeTwoMatrixEquivOfRightInverse_coordinate_of_row
#print axioms freeNOrientation_matrixEquiv
#print axioms exists_freeTwoMatrixBasis_of_rightInverse
#print axioms exists_freeTwoMatrixBasis_of_isUnit_det

end
end GQ2.Dyadic.MarkedCore
