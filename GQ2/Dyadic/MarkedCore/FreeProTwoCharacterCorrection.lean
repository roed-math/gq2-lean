import GQ2.Dyadic.MarkedCore.FreeProTwoCommutatorShear
import GQ2.Roe.Labute.TwoCentralTower

/-!
# Exact removal of divisible ordinary-character rows

This is the exact group-level representative correction used after a graded row
has vanished. Divisibility and the closed-subgroup power hypotheses are explicit;
no restricted graded-image theorem or N-boundary lift is asserted.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative

def freeTwoCoordinate (n : ℕ) (j : Fin n) :
    ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]) :=
  presLiftHom 1 PropOneOne.isProP_two_multPadicInt
    (fun i => ofAdd (if i=j then (1 : ℤ_[2]) else 0)) (map_one _)

theorem freeTwoCoordinate_gen (n : ℕ) (j i : Fin n) :
    freeTwoCoordinate n j (freeTwoRankGen n i) =
      ofAdd (if i=j then (1 : ℤ_[2]) else 0) := presLiftHom_gen _ _ _ _ _

private def characterFromCoordinates (n : ℕ)
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2])) :
    ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]) where
  toFun x := ofAdd (∑ j, toAdd (freeTwoCoordinate n j x) * toAdd (f (freeTwoRankGen n j)))
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, toAdd_mul, add_mul, Finset.sum_add_distrib, ofAdd_add]
  continuous_toFun := continuous_ofAdd.comp (continuous_finsetSum _ fun j _ =>
    (continuous_toAdd.comp (freeTwoCoordinate n j).continuous_toFun).mul continuous_const)

/-- Every ordinary character is the exact linear combination of coordinate
characters given by its generator values. No abelianization isomorphism is a
premise of this result. -/
theorem freeTwo_character_coordinates (n : ℕ)
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]))
    (x : FreeTwoRank n) :
    toAdd (f x) = ∑ j, toAdd (freeTwoCoordinate n j x) * toAdd (f (freeTwoRankGen n j)) := by
  have he : f = characterFromCoordinates n f := by
    apply presPro2_hom_ext
    intro i
    change f (freeTwoRankGen n i) = ofAdd (∑ j,
      toAdd (freeTwoCoordinate n j (freeTwoRankGen n i)) * toAdd (f (freeTwoRankGen n j)))
    simp [freeTwoCoordinate_gen]
  exact congrArg (fun g : ContinuousMonoidHom _ _ => toAdd (g x)) he

def freeTwoCoordinateWord (n : ℕ) (a : Fin n → ℤ_[2]) : FreeTwoRank n :=
  (List.ofFn fun i => zpowZtwo (isProP_presPro2 1) (freeTwoRankGen n i) (a i)).prod

theorem freeTwoCoordinateWord_character (n : ℕ) (a : Fin n → ℤ_[2])
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2])) :
    toAdd (f (freeTwoCoordinateWord n a)) = ∑ i, a i * toAdd (f (freeTwoRankGen n i)) := by
  rw [freeTwoCoordinateWord, map_list_prod, List.map_ofFn, Fin.prod_ofFn]
  rw [toAdd_prod]
  apply Finset.sum_congr rfl
  intro i _
  exact toAdd_map_zpowZtwo (isProP_presPro2 1) f (freeTwoRankGen n i) (a i)

private theorem zpow_mem_closed {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (H : Subgroup P) (hH : IsClosed (H : Set P))
    (x : P) (hx : x ∈ H) (a : ℤ_[2]) : zpowZtwo hP x a ∈ H := by
  refine PadicInt.denseRange_natCast.induction_on a ?_ ?_
  · exact hH.preimage (continuous_zpowZtwo hP x)
  · intro k
    rw [zpowZtwo_natCast]
    exact H.pow_mem hx k

theorem freeTwoCoordinateWord_mem (n d : ℕ) (a : Fin n → ℤ_[2])
    (H : Subgroup (FreeTwoRank n : Type)) (hH : IsClosed (H : Set (FreeTwoRank n : Type)))
    (hpow : ∀ i, (freeTwoRankGen n i)^d ∈ H) (ha : ∀ i, (d : ℤ_[2]) ∣ a i) :
    freeTwoCoordinateWord n a ∈ H := by
  apply H.list_prod_mem
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  obtain ⟨t, ht⟩ := ha i
  have he : zpowZtwo (isProP_presPro2 1) (freeTwoRankGen n i) (a i) =
      zpowZtwo (isProP_presPro2 1) ((freeTwoRankGen n i)^d) t := by
    rw [← zpowZtwo_natCast (isProP_presPro2 1) (freeTwoRankGen n i) d,
      zpowZtwo_zpowZtwo, ht]
  rw [he]
  exact zpow_mem_closed (isProP_presPro2 1) H hH _ (hpow i) t

/-- Exact common-character-kernel representative in the same right H-coset.
Normality of H is not needed. In a filtration application, take d=2^m and H
the next closed filtration term; the theorem does not assume that application. -/
theorem exists_freeTwo_characterZero_same_coset (n d : ℕ) (x : FreeTwoRank n)
    (H : Subgroup (FreeTwoRank n : Type)) (hH : IsClosed (H : Set (FreeTwoRank n : Type)))
    (hpow : ∀ i, (freeTwoRankGen n i)^d ∈ H)
    (hx : ∀ i, (d : ℤ_[2]) ∣ toAdd (freeTwoCoordinate n i x)) :
    ∃ x' : FreeTwoRank n, x⁻¹*x' ∈ H ∧
      ∀ f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]), f x' = 1 := by
  let a : Fin n → ℤ_[2] := fun i => toAdd (freeTwoCoordinate n i x)
  refine ⟨x * (freeTwoCoordinateWord n a)⁻¹, ?_, ?_⟩
  · rw [inv_mul_cancel_left]
    exact H.inv_mem (freeTwoCoordinateWord_mem n d a H hH hpow hx)
  · intro f
    change toAdd (f (x * (freeTwoCoordinateWord n a)⁻¹)) = 0
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [freeTwoCoordinateWord_character, freeTwo_character_coordinates n f x]
    exact add_neg_cancel _

/-- Concrete filtration specialization, still with the necessary extra
divisibility premise stated. It turns a zero ordinary graded row into an exact
common-character-kernel representative of the same two-central class. -/
theorem exists_freeTwo_characterZero_same_twoCentralClass (n m : ℕ) (x : FreeTwoRank n)
    (hx : x ∈ Roe.Labute.twoCentralSeries (FreeTwoRank n : Type) m)
    (hrow : ∀ i, (2^m : ℤ_[2]) ∣ toAdd (freeTwoCoordinate n i x)) :
    ∃ x' : FreeTwoRank n,
      x' ∈ Roe.Labute.twoCentralSeries (FreeTwoRank n : Type) m ∧
      x⁻¹*x' ∈ Roe.Labute.twoCentralSeries (FreeTwoRank n : Type) (m+1) ∧
      ∀ f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]), f x' = 1 := by
  obtain ⟨x', hdiff, hchar⟩ := exists_freeTwo_characterZero_same_coset n (2^m) x
    (Roe.Labute.twoCentralSeries (FreeTwoRank n : Type) (m+1))
    (Roe.Labute.isClosed_twoCentralSeries _ _) (fun i =>
      Roe.Labute.pow_two_pow_mem_twoCentralSeries_succ (FreeTwoRank n : Type)
        (freeTwoRankGen n i) m)
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hrow)
  refine ⟨x', ?_, hdiff, hchar⟩
  have he : x' = x*(x⁻¹*x') := by group
  rw [he]
  exact (Roe.Labute.twoCentralSeries (FreeTwoRank n : Type) m).mul_mem hx
    (Roe.Labute.twoCentralSeries_antitone (G := (FreeTwoRank n : Type)) (Nat.le_succ m) hdiff)

section CommutativeTargets
variable {Q : Type} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]

private def commHomFromCoordinates (hQ : IsProP 2 Q) (n : ℕ)
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) Q) :
    ContinuousMonoidHom (FreeTwoRank n : Type) Q where
  toFun x := ∏ i, zpowZtwo hQ (f (freeTwoRankGen n i)) (toAdd (freeTwoCoordinate n i x))
  map_one' := by simp [zpowZtwo_zero_exp]
  map_mul' x y := by
    simp only [map_mul, toAdd_mul, zpowZtwo_add, Finset.prod_mul_distrib]
  continuous_toFun := continuous_finsetProd _ fun i _ =>
    (continuous_zpowZtwo hQ _).comp
      (continuous_toAdd.comp (freeTwoCoordinate n i).continuous_toFun)

/-- The coordinate formula also holds for all commutative pro-two targets,
including the orientation-unit target. -/
theorem freeTwo_commutative_hom_coordinates (hQ : IsProP 2 Q) (n : ℕ)
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) Q) (x : FreeTwoRank n) :
    f x = ∏ i, zpowZtwo hQ (f (freeTwoRankGen n i)) (toAdd (freeTwoCoordinate n i x)) := by
  have he : f = commHomFromCoordinates hQ n f := by
    apply presPro2_hom_ext
    intro i
    change f (freeTwoRankGen n i) = ∏ j,
      zpowZtwo hQ (f (freeTwoRankGen n j))
        (toAdd (freeTwoCoordinate n j (freeTwoRankGen n i)))
    simp only [freeTwoCoordinate_gen, toAdd_ofAdd]
    rw [Finset.prod_eq_single i (fun j _ hji => by
      rw [if_neg (Ne.symm hji), zpowZtwo_zero_exp])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [if_pos rfl, zpowZtwo_one_exp]
  exact congrArg (fun g : ContinuousMonoidHom _ _ => g x) he

/-- Killing every ordinary Z2 character also kills every continuous map into a
commutative pro-two target. Thus exact row corrections preserve such characters
without presuming an abelianization identification. -/
theorem freeTwo_characterZero_commutative (hQ : IsProP 2 Q) (n : ℕ) (x : FreeTwoRank n)
    (hx : ∀ f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]), f x = 1)
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) Q) : f x = 1 := by
  rw [freeTwo_commutative_hom_coordinates hQ n f x]
  apply Finset.prod_eq_one
  intro i _
  rw [hx (freeTwoCoordinate n i), toAdd_one, zpowZtwo_zero_exp]

end CommutativeTargets

#print axioms freeTwoCoordinate
#print axioms freeTwoCoordinate_gen
#print axioms freeTwo_character_coordinates
#print axioms freeTwoCoordinateWord
#print axioms freeTwoCoordinateWord_character
#print axioms freeTwoCoordinateWord_mem
#print axioms exists_freeTwo_characterZero_same_coset
#print axioms exists_freeTwo_characterZero_same_twoCentralClass
#print axioms freeTwo_commutative_hom_coordinates
#print axioms freeTwo_characterZero_commutative

end
end GQ2.Dyadic.MarkedCore

