import GQ2.Dyadic.MarkedCore.FreeProTwoCharacterCorrection

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative SectionThree

theorem freeTwo_commutative_expTwo_eq_of_coordinate_modTwo
    {Q : Type} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hQ : IsProP 2 Q) (hsq : ∀ q : Q, q ^ 2 = 1) (n : ℕ)
    (x y : FreeTwoRank n)
    (hxy : ∀ i, PadicInt.toZModPow 1 (toAdd (freeTwoCoordinate n i x)) =
      PadicInt.toZModPow 1 (toAdd (freeTwoCoordinate n i y)))
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) Q) : f x = f y := by
  rw [freeTwo_commutative_hom_coordinates hQ n f x,
    freeTwo_commutative_hom_coordinates hQ n f y]
  apply Finset.prod_congr rfl
  intro i _
  rw [zpowZtwo_of_sq_eq_one hQ _ (hsq _) _,
    zpowZtwo_of_sq_eq_one hQ _ (hsq _) _, hxy i]

theorem freeTwo_modTwo_character_eq_of_coordinate_modTwo (n : ℕ)
    (x y : FreeTwoRank n)
    (hxy : ∀ i, PadicInt.toZModPow 1 (toAdd (freeTwoCoordinate n i x)) =
      PadicInt.toZModPow 1 (toAdd (freeTwoCoordinate n i y)))
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative (ZMod 2))) :
    f x = f y :=
  freeTwo_commutative_expTwo_eq_of_coordinate_modTwo isProP_two_multZMod2
    (by decide) n x y hxy f

theorem freeTwo_modTwo_character_eq_of_coordinate_even_difference (n : ℕ)
    (x y : FreeTwoRank n)
    (hxy : ∀ i, (2 : ℤ_[2]) ∣
      toAdd (freeTwoCoordinate n i x) - toAdd (freeTwoCoordinate n i y))
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative (ZMod 2))) :
    f x = f y := by
  apply freeTwo_modTwo_character_eq_of_coordinate_modTwo n x y _ f
  intro i
  apply sub_eq_zero.mp
  rw [← map_sub]
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one]
  exact hxy i

#print axioms freeTwo_commutative_expTwo_eq_of_coordinate_modTwo
#print axioms freeTwo_modTwo_character_eq_of_coordinate_modTwo
#print axioms freeTwo_modTwo_character_eq_of_coordinate_even_difference
end
end GQ2.Dyadic.MarkedCore
