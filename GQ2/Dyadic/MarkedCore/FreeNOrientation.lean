import GQ2.Dyadic.MarkedCore.FreeProTwoUnitPower

/-!
# The ordinary b-coordinate of the free N orientation

The canonical orientation of the free group sends index 1 to nUnit and
every other marked generator to one. At alpha at least two, its kernel is
exactly the kernel of the ordinary index-1 coordinate, integrally. This uses
the already proved injectivity of powering by nUnit, not a logarithm axiom.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 Multiplicative

def freeNOrientation (α h : ℕ) :
    ContinuousMonoidHom (FreeTwoRank (coreRank h) : Type) ℤ_[2]ˣ :=
  presLiftHom 1 isProP_two_unitsPadicInt
    (fun i => if i = 1 then nUnit α else 1) (map_one _)

theorem freeNOrientation_gen (α h : ℕ) (i : Fin (coreRank h)) :
    freeNOrientation α h (freeTwoRankGen (coreRank h) i) =
      if i = 1 then nUnit α else 1 := presLiftHom_gen _ _ _ _ _

theorem freeNOrientation_coordinate (α h : ℕ) (x : FreeTwoRank (coreRank h)) :
    freeNOrientation α h x = zpowZtwo isProP_two_unitsPadicInt (nUnit α)
      (toAdd (freeTwoCoordinate (coreRank h) 1 x)) := by
  rw [freeTwo_commutative_hom_coordinates isProP_two_unitsPadicInt (coreRank h)
    (freeNOrientation α h) x]
  simp only [freeNOrientation_gen]
  rw [Finset.prod_eq_single (1 : Fin (coreRank h)) (fun i _ hi => by
    rw [if_neg hi, zpowZtwo_one_base])
    (fun hi => absurd (Finset.mem_univ 1) hi), if_pos rfl]

/-- The b-coordinate vanishes exactly, not merely modulo two. -/
theorem freeNOrientation_eq_one_iff {α : ℕ} (hα : 2 ≤ α) (h : ℕ)
    (x : FreeTwoRank (coreRank h)) :
    freeNOrientation α h x = 1 ↔
      toAdd (freeTwoCoordinate (coreRank h) 1 x) = 0 := by
  rw [freeNOrientation_coordinate]
  constructor
  · intro hx
    apply nUnit_zpowZtwo_injective hα
    rw [hx, zpowZtwo_zero_exp]
  · intro hx
    rw [hx, zpowZtwo_zero_exp]

theorem freeNOrientation_ker {α : ℕ} (hα : 2 ≤ α) (h : ℕ) :
    (freeNOrientation α h).ker = (freeTwoCoordinate (coreRank h) 1).ker := by
  ext x
  change freeNOrientation α h x = 1 ↔ freeTwoCoordinate (coreRank h) 1 x = 1
  rw [freeNOrientation_eq_one_iff hα]
  exact ⟨fun hx => toAdd.injective (by simpa using hx), fun hx => by rw [hx, toAdd_one]⟩

/-- The initial power substitution also preserves the canonical orientation
provided that the selected generator is not b (index 1). -/
theorem freeNOrientation_unitPowerEquiv (α h : ℕ) (c : Fin (coreRank h))
    (hc : c ≠ 1) (κ : ℤ_[2]ˣ) (x : FreeTwoRank (coreRank h)) :
    freeNOrientation α h (freeTwoUnitPowerEquiv (coreRank h) c κ x) =
      freeNOrientation α h x := by
  have he : (freeNOrientation α h).comp (freeTwoUnitPowerHom (coreRank h) c κ) =
      freeNOrientation α h := by
    apply presPro2_hom_ext
    intro i
    change freeNOrientation α h (freeTwoUnitPowerHom (coreRank h) c κ
      (freeTwoRankGen (coreRank h) i)) = freeNOrientation α h (freeTwoRankGen (coreRank h) i)
    rw [freeTwoUnitPowerHom_gen, freeTwoUnitPowerMark]
    split_ifs with hi
    · subst i
      rw [map_zpowZtwo (isProP_presPro2 1) isProP_two_unitsPadicInt,
        freeNOrientation_gen, if_neg hc, zpowZtwo_one_base]
    · rfl
  exact congrArg (fun f : ContinuousMonoidHom _ _ => f x) he

theorem freeNOrientation_initialError (α h : ℕ) (c : Fin (coreRank h))
    (hc : c ≠ 0) (κ : ℤ_[2]ˣ) :
    freeNOrientation α h (nInitialUnitPowerError α h c κ) = 1 :=
  nInitialUnitPowerError_commutative α h c hc κ (freeNOrientation α h).toMonoidHom

#print axioms freeNOrientation
#print axioms freeNOrientation_gen
#print axioms freeNOrientation_coordinate
#print axioms freeNOrientation_eq_one_iff
#print axioms freeNOrientation_ker
#print axioms freeNOrientation_unitPowerEquiv
#print axioms freeNOrientation_initialError

end
end GQ2.Dyadic.MarkedCore
